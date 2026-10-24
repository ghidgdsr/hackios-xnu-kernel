/*
 * XNU loader: a UEFI application that plays the role of iBoot for an
 * open-source arm64 XNU kernel on non-Apple hardware.
 *
 *   - finds the "XNUP" payload in RAM (placed there by the boot shim on the
 *     phone, by `-device loader` under QEMU) and the Mach-O kernel inside it
 *   - picks a block of free RAM to be XNU's [physBase, physBase + memSize)
 *   - copies the Mach-O segments there, builds an Apple-format device tree
 *     and a boot_args structure behind the kernel
 *   - exits boot services, turns the MMU off and jumps to the kernel entry
 */
#include "efi.h"
#include "identity.h"         /* who iOS shall think we are: from the iPhone's own device tree (mkidentity.py) */
#include "font5x12.h"         /* the framebuffer console's font, for logs the EFI console cannot show */

/* ------------------------------------------------------------------------ */
/* Fixed conventions shared with the boot shim, the packer and the kernel   */

/* Where the boot shim copies the XNUP container; a device whose memory map places it elsewhere
 * (malachite: above 4 GiB) passes -DPAYLOAD_BASE=... at build time. */
#ifndef PAYLOAD_BASE
#define PAYLOAD_BASE        0xF0000000ULL
#endif
#define PAYLOAD_MAGIC       0x50554E58u /* "XNUP" */

struct payload_header { uint32_t magic; uint32_t size; };
struct payload_entry { char name[16]; uint32_t size; uint32_t reserved; };

#define KERNEL_VIRT_BASE    0xFFFFFFF004000000ULL /* boot_args.virtBase */
#define KERNEL_LINK_OFFSET  0x03000000ULL         /* kernel text sits 48 MB above the base */
#define BASE_ALIGN          0x02000000ULL         /* 32 MB: L2 block size with 16K pages */
#define MAX_MEM_SIZE        0x180000000ULL        /* 6 GB; the kernel's bootstrap page tables cover 8 */
/*
 * A root image too big for the payload area is placed here, at a fixed
 * offset inside the kernel's memory window, once; it then survives any
 * number of kernel runs (nothing writes to it: the root is read-only).
 */
#define RESIDENT_RD_OFFSET  0x08000000ULL
#define RESIDENT_RD_RESERVE 0x30000000ULL         /* RAM that must remain for the kernel itself */
#define PAGE_SIZE_MAX       0x4000ULL

#define LOG_PARTITION       u"logdump"
#define CHECKPOINT_SELFTEST 999
#define PANIC_LOG_SIZE      0x80000u
#define NVRAM_BANK_SIZE     0x2000u
#define PANIC_LOG_BASE      (PAYLOAD_BASE + PAYLOAD_MAX_SIZE - 0x100000ULL)
#define PAYLOAD_MAX_SIZE    0x04000000ULL         /* RAM reserved for the payload in the UEFI memory map */
/* Bring-up: a mailbox the firmware reads after this loader returns (see XnuLoader.c). */
#define LOG_MBOX_BASE       (PAYLOAD_BASE + PAYLOAD_MAX_SIZE - 0x80000ULL)
#define LOG_MBOX_MAGIC      0x474F4C58u           /* "XLOG" */
#define LOG_MBOX_SIZE       0x7F000u
#define LOG_MBOX_FLAG_OFF   0x7F800u              /* u32: 1 = the log below is a fault log */

/* ------------------------------------------------------------------------ */
/* XNU structures (pexpert/pexpert/arm64/boot.h, mach-o/loader.h)           */

struct boot_video {
	uint64_t v_baseAddr, v_display, v_rowBytes, v_width, v_height, v_depth;
};

#define BOOT_LINE_LENGTH 608

struct boot_args {
	uint16_t revision;
	uint16_t version;
	uint64_t virtBase;
	uint64_t physBase;
	uint64_t memSize;
	uint64_t topOfKernelData;
	struct boot_video video;
	uint32_t machineType;
	uint64_t deviceTreeP;
	uint32_t deviceTreeLength;
	char commandLine[BOOT_LINE_LENGTH];
	uint64_t bootFlags;
	uint64_t memSizeActual;
};

#define MH_MAGIC_64      0xFEEDFACFu
#define LC_SEGMENT_64    0x19
#define LC_UNIXTHREAD    0x5

struct mach_header_64 { uint32_t magic, cputype, cpusubtype, filetype, ncmds, sizeofcmds, flags, reserved; };
struct load_command { uint32_t cmd, cmdsize; };
struct segment_command_64 {
	uint32_t cmd, cmdsize; char segname[16];
	uint64_t vmaddr, vmsize, fileoff, filesize;
	uint32_t maxprot, initprot, nsects, flags;
};

/* ------------------------------------------------------------------------ */
/* Globals and small helpers                                                */

static efi_system_table *ST;
static efi_boot_services *BS;
static efi_handle IMAGE;

static char log_buf[32768];
static uint32_t log_len;

void *
memset(void *dst, int c, size_t n)
{
	uint8_t *d = dst;
	while (n--) {
		*d++ = (uint8_t)c;
	}
	return dst;
}

int
memcmp(const void *a, const void *b, size_t n)
{
	const uint8_t *x = a, *y = b;

	for (; n > 0; n--, x++, y++) {
		if (*x != *y) {
			return *x < *y ? -1 : 1;
		}
	}
	return 0;
}

void *
memcpy(void *dst, const void *src, size_t n)
{
	uint8_t *d = dst;
	const uint8_t *s = src;

	/*
	 * Word at a time when possible: USB transfer buffers are uncached, where
	 * a byte loop costs one bus access per byte (6 MB/s instead of 30+).
	 */
	if ((((uintptr_t)d | (uintptr_t)s) & 7) == 0) {
		uint64_t *dw = (uint64_t *)d;
		const uint64_t *sw = (const uint64_t *)s;

		for (; n >= 32; n -= 32, dw += 4, sw += 4) {
			uint64_t a = sw[0], b = sw[1], c = sw[2], e = sw[3];
			dw[0] = a;
			dw[1] = b;
			dw[2] = c;
			dw[3] = e;
		}
		for (; n >= 8; n -= 8) {
			*dw++ = *sw++;
		}
		d = (uint8_t *)dw;
		s = (const uint8_t *)sw;
	}
	while (n--) {
		*d++ = *s++;
	}
	return dst;
}

static size_t
str_len(const char *s)
{
	size_t n = 0;
	while (s[n]) {
		n++;
	}
	return n;
}

static int
str_eq(const char *a, const char *b)
{
	while (*a && *a == *b) {
		a++, b++;
	}
	return *a == *b;
}

/*
 * Set once the loader takes commands over USB: its log travels that way, and
 * the screen is left to the kernel (and to "oem screenshot").
 */
static int screen_quiet;

static void
put_char(char c)
{
	char16 w[3] = { 0, 0, 0 };

	if (log_len < sizeof(log_buf) - 1) {
		log_buf[log_len++] = c;
	}
	if (ST->con_out != NULL && !screen_quiet) {
		if (c == '\n') {
			w[0] = '\r', w[1] = '\n';
		} else {
			w[0] = (char16)c;
		}
		ST->con_out->output_string(ST->con_out, w);
	}
}

/* printf subset: %s %x %d (64-bit values), %% */
static void
print(const char *fmt, ...)
{
	__builtin_va_list ap;
	__builtin_va_start(ap, fmt);
	for (; *fmt; fmt++) {
		if (*fmt != '%') {
			put_char(*fmt);
			continue;
		}
		fmt++;
		if (*fmt == 's') {
			const char *s = __builtin_va_arg(ap, const char *);
			while (*s) {
				put_char(*s++);
			}
		} else if (*fmt == 'x' || *fmt == 'd') {
			uint64_t v = __builtin_va_arg(ap, uint64_t);
			unsigned base = (*fmt == 'x') ? 16 : 10;
			char tmp[24];
			int i = 0;
			do {
				tmp[i++] = "0123456789abcdef"[v % base];
				v /= base;
			} while (v);
			while (i) {
				put_char(tmp[--i]);
			}
		} else {
			put_char(*fmt);
		}
	}
	__builtin_va_end(ap);
}

#define READ_SYSREG(name) ({ uint64_t _v; __asm__ volatile ("mrs %0, " #name : "=r" (_v)); _v; })

/*
 * Write back and drop cached copies of a range. Required for memory the
 * kernel will touch with the MMU (and so the data cache) off: its early code
 * builds page tables that way, and a stale cached copy of those pages would
 * be what the table walker sees once caches are turned on again.
 */
static void
flush_dcache(uint64_t start, uint64_t end)
{
	uint64_t line = 4ULL << ((READ_SYSREG(CTR_EL0) >> 16) & 0xF);
	for (uint64_t p = start & ~(line - 1); p < end; p += line) {
		__asm__ volatile ("dc civac, %0" : : "r" (p));
	}
	__asm__ volatile ("dsb sy");
}

static void
clean_dcache(uint64_t start, uint64_t end)
{
	uint64_t line = 4ULL << ((READ_SYSREG(CTR_EL0) >> 16) & 0xF);
	for (uint64_t p = start & ~(line - 1); p < end; p += line) {
		__asm__ volatile ("dc cvac, %0" : : "r" (p));
	}
	__asm__ volatile ("dsb sy");
}

/* ------------------------------------------------------------------------ */
/* Log persistence: raw write to a GPT partition (phone only)               */

static efi_block_io *
find_log_partition(void)
{
	static const efi_guid part_guid = EFI_PARTITION_INFO_GUID;
	static const efi_guid blk_guid = EFI_BLOCK_IO_GUID;
	static const char16 want[] = LOG_PARTITION;
	efi_handle *handles;
	uint64_t count;

	if (EFI_ERROR(BS->locate_handle_buffer(ByProtocol, &part_guid, NULL, &count, &handles))) {
		return NULL;
	}
	for (uint64_t i = 0; i < count; i++) {
		efi_partition_info *info;
		efi_block_io *bio;
		int match = 1;

		if (EFI_ERROR(BS->handle_protocol(handles[i], &part_guid, (void **)&info)) || info->type != 2) {
			continue;
		}
		for (unsigned k = 0; k < sizeof(want) / sizeof(want[0]); k++) {
			if (info->name[k] != want[k]) {
				match = 0;
				break;
			}
		}
		if (match && !EFI_ERROR(BS->handle_protocol(handles[i], &blk_guid, (void **)&bio))) {
			return bio;
		}
	}
	return NULL;
}

/*
 * The "staged" buffer holds the loader log followed by the kernel log of the
 * last run. It is what gets written to the log partition and what the host
 * fetches over USB (fastboot get_staged).
 */
static char out_buf[2 * 1024 * 1024];
/* the storage's reads for the kernel land here (block_poll); also where the log is read back */
#define BLOCK_BUFFER_SIZE  (4u << 20)
static uint8_t block_buffer[BLOCK_BUFFER_SIZE] __attribute__((aligned(0x2000)));
static const char *staged_data = out_buf;   /* what "upload" sends: normally the log in out_buf */
static uint64_t staged_len;

static void
compose_logs(const char *klog, uint64_t klog_len)
{
	static const char sep[] = "\n== KERNEL LOG ==\n", end[] = "\n== END OF LOG ==\n";
	uint64_t n = log_len;

	staged_data = out_buf;
	memset(out_buf, 0, sizeof(out_buf));
	memcpy(out_buf, log_buf, log_len);
	if (klog != NULL) {
		if (klog_len > sizeof(out_buf) - n - 8192) {
			klog_len = sizeof(out_buf) - n - 8192;
		}
		memcpy(out_buf + n, sep, sizeof(sep) - 1);
		n += sizeof(sep) - 1;
		memcpy(out_buf + n, klog, klog_len);
		n += klog_len;
		memcpy(out_buf + n, end, sizeof(end) - 1);
		n += sizeof(end) - 1;
	}
	staged_len = n;
}

static int hc_list_is_uefis(void);
static int hc_log_skips;                /* logs not written this run (said twice at most) */
static void hc_print_state(const char *when);
static void hc_take_back(const char *when);

static void
write_logs(const char *klog, uint64_t klog_len)
{
	efi_block_io *bio = find_log_partition();

	compose_logs(klog, klog_len);
	if (bio == NULL) {
		/* No log partition (QEMU): echo the returned kernel log on the console instead. */
		if (klog != NULL) {
			print("\n== KERNEL LOG ==\n");
			for (uint64_t i = 0; i < klog_len; i++) {
				put_char(klog[i]);
			}
			print("\n== END OF LOG ==\n");
		}
		return;
	}
	uint64_t bs = bio->media->block_size;
	uint64_t len = (staged_len + 1 + bs - 1) / bs * bs;
	efi_status ws, rs = 0;
	int same = 0;

	/* only through UEFI's own transfer list (see hc_take_back) */
	if (!hc_list_is_uefis()) {
		if (hc_log_skips++ < 2) {
			hc_print_state("log not written");
			print("log: NOT WRITTEN to logdump: UEFI's transfer list is not the one in the controller\n");
		}
		compose_logs(klog, klog_len);
		return;
	}
	ws = bio->write_blocks(bio, bio->media->media_id, 0, len, out_buf);

	if (!EFI_ERROR(ws)) {
		bio->flush_blocks(bio);
		/*
		 * And read back: that the log is in the partition is what a run of the kernel's own UFS
		 * driver must leave possible (the controller is shared with this one). The line goes into
		 * the copy the host fetches over USB, not into the partition, which already has the rest.
		 */
		if (len <= sizeof(block_buffer)) {
			rs = bio->read_blocks(bio, bio->media->media_id, 0, len, block_buffer);
			same = !EFI_ERROR(rs) && memcmp(block_buffer, out_buf, len) == 0;
		}
	}
	print("log: %d bytes written to logdump (%x), read back %s (%x)\n", len, ws,
	    EFI_ERROR(ws) ? "not tried" : same ? "the same" : "DIFFERENT", rs);
	compose_logs(klog, klog_len);
}

static void
flush_log(void)
{
	write_logs(NULL, 0);
}

/* ------------------------------------------------------------------------ */
/* Apple device tree writer                                                 */
/*                                                                          */
/* node := u32 nProperties, u32 nChildren, props[], children[]              */
/* prop := char name[32], u32 length, value padded to 4 bytes               */

struct dt_writer {
	uint8_t *base, *cur;
	uint32_t *counts[16]; /* [depth] -> {nProperties, nChildren} of the open node */
	int depth;
};

static void
dt_prop(struct dt_writer *w, const char *name, const void *data, uint32_t len)
{
	memset(w->cur, 0, 32);
	memcpy(w->cur, name, str_len(name));
	*(uint32_t *)(w->cur + 32) = len;
	memset(w->cur + 36, 0, (len + 3) & ~3u);
	memcpy(w->cur + 36, data, len);
	w->cur += 36 + ((len + 3) & ~3u);
	w->counts[w->depth - 1][0]++;
}

static void
dt_prop_str(struct dt_writer *w, const char *name, const char *value)
{
	dt_prop(w, name, value, (uint32_t)str_len(value) + 1);
}

static void
dt_prop_u32(struct dt_writer *w, const char *name, uint32_t value)
{
	dt_prop(w, name, &value, sizeof(value));
}

static void
dt_prop_u64(struct dt_writer *w, const char *name, uint64_t value)
{
	dt_prop(w, name, &value, sizeof(value));
}

/* Seconds since 1970 by the firmware's real-time clock, or 0 when it has none or it is not set. */
static uint64_t
firmware_epoch(void)
{
	static const uint16_t before_month[12] = { 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334 };
	struct efi_time t;
	uint64_t days;

	if (ST->rt == NULL || ST->rt->get_time == NULL || EFI_ERROR(ST->rt->get_time(&t, NULL)) ||
	    t.year < 2024 || t.year > 2099 || t.month < 1 || t.month > 12) {
		return 0;
	}
	days = (uint64_t)(t.year - 1970) * 365 + (t.year - 1969) / 4 + before_month[t.month - 1] + (t.day - 1);
	if (t.month > 2 && t.year % 4 == 0) {
		days++;
	}
	uint64_t secs = days * 86400 + (uint64_t)t.hour * 3600 + (uint64_t)t.minute * 60 + t.second;
	if (t.timezone != 0x7FF) {
		secs += (int64_t)t.timezone * 60;       /* local time = UTC - timezone */
	}
	return secs;
}

/* A string in a field of fixed size, the rest zeros. */
static void
dt_prop_padded(struct dt_writer *w, const char *name, const char *value, uint32_t size)
{
	uint8_t field[64];

	memset(field, 0, sizeof(field));
	memcpy(field, value, str_len(value));
	dt_prop(w, name, field, size);
}

/*
 * Properties copied from the iPhone's device tree (identity.h), but one: the iPhone X's display is a
 * wide-gamut one ("artwork-display-gamut" P3), and with it iOS takes the screen for one that shows
 * extended colour (MobileGestalt's HasExtendedColorDisplay): WebKit then draws a page's tiles into
 * surfaces of ten bits a colour ('w30r', 'b3a8'), which neither the kernel's surfaces nor the window
 * server's renderer here do (eight bits, BGRA), and every page comes out black. Here the screen is
 * what the framebuffer is: sRGB.
 */
static int gamut_p3;    /* boot-arg gamut=p3 (a test): the iPhone's own "P3" left in place */

static void
dt_identity(struct dt_writer *w, const struct identity_prop *props, uint32_t count, const unsigned char *data)
{
	for (uint32_t i = 0; i < count; i++) {
		if (str_eq(props[i].name, "artwork-display-gamut") && !gamut_p3) {
			dt_prop(w, props[i].name, "sRGB", 5);
			continue;
		}
		dt_prop(w, props[i].name, data + props[i].offset, props[i].length);
	}
}

/* One property of those copied from the iPhone's device tree, by name. */
static void
dt_identity_one(struct dt_writer *w, const struct identity_prop *props, uint32_t count, const unsigned char *data, const char *name)
{
	for (uint32_t i = 0; i < count; i++) {
		if (str_eq(props[i].name, name)) {
			dt_prop(w, props[i].name, data + props[i].offset, props[i].length);
		}
	}
}

static void
dt_begin(struct dt_writer *w, const char *name)
{
	if (w->depth > 0) {
		w->counts[w->depth - 1][1]++;
	}
	w->counts[w->depth++] = (uint32_t *)w->cur;
	memset(w->cur, 0, 8);
	w->cur += 8;
	dt_prop_str(w, "name", name);
}

static void
dt_end(struct dt_writer *w)
{
	w->depth--;
}

/* ------------------------------------------------------------------------ */
/* Platform description                                                     */

/*
 * The phone has no UART, and the kernel's serial driver is the only way its kprintf reaches
 * this loader's log (pexpert/arm/pe_kprintf.c: serial_putc_crlf -> loader_log_putc). So the
 * device tree points uart0 at a page in the loader's reserved payload area instead: the kernel
 * maps it uncached and treats it as a PL011, and since the page is zeroed and nothing writes
 * its FR word, the transmit-ready bit (FR & 0x20) always reads clear. The characters it
 * "sends" land at DRAM the kernel does not otherwise use. The page is past the XNUP payload
 * (about 20 MB) and well below the panic log and mailbox at the end of the reserved area.
 */
#define MALACHITE_FAKE_UART (PAYLOAD_BASE + 0x03000000ULL)

struct platform {
	const char *name;
	uint64_t io_base, io_size;       /* one window covering the SoC peripherals */
	uint64_t gic_dist, gic_redist;   /* GICv3 */
	uint64_t uart;                   /* PL011, 0 if none */
	int psci_hvc;                    /* the firmware's power interface is called with HVC, not SMC */
	int log_other_cpu;               /* keep notes in the log partition while a kernel starts on another core */
	int cores;                       /* at most this many processor cores, numbered from 0 ... */
	int core_shift;                  /* ... in this bit of MPIDR: the phone numbers them in the second affinity field */
	uint32_t timeout_scale;          /* a kernel on several cores gets this much longer to wait for a lock, 0: as it is */
	uint32_t small_cores;            /* a bit for each of the slower cores, by number: "small-core" in the device tree */
	uint64_t fb_base;                /* the framebuffer the firmware reports (GOP): it tells this device apart */
};

static const struct platform platform_qemu_virt = {
	.name = "qemu-virt", .io_base = 0x08000000, .io_size = 0x08000000,
	.gic_dist = 0x08000000, .gic_redist = 0x080A0000, .uart = 0x09000000, .psci_hvc = 1,
	.cores = 8, .core_shift = 0,
	/*
	 * QEMU's emulated cores stop each other all the time (every flush of a page from all the
	 * TLBs is a rendezvous of all its CPU threads), and the kernel's patience with a spin lock
	 * is that of real hardware: an eighth of a second by a 24 MHz clock, a twentieth here.
	 */
	.timeout_scale = 20,
};

static const struct platform platform_redwood = {
	/* io_base must be non-zero: XNU treats a zero SoC base as "no SoC" and skips clock setup. */
	.name = "redwood", .io_base = 0x00400000, .io_size = 0x3FC00000,
	.gic_dist = 0x17A00000, .gic_redist = 0x17A60000, .uart = 0, .log_other_cpu = 1,
	.cores = 8, .core_shift = 8,
	/*
	 * Cores 0-3 are Cortex-A55s (1.8 GHz at most), 4-7 Cortex-A78s (2.4 GHz): a big one is about
	 * 2.5 times as fast. The kernel uses the small ones only when the big ones are all busy
	 * (XNU's machine_routines.c, ml_choose_slow_core_partners()).
	 */
	.small_cores = 0x0f,
	.fb_base = 0xE1000000,
};

static const struct platform platform_malachite = {
	/* POCO X7 / Redmi Note 14 Pro 5G, MT6878 (Dimensity 7300): GICv3, PSCI over SMC.
	 * The peripheral window follows redwood's: MTK's GIC (0x0C000000), pinctrl (0x10005000)
	 * and watchdog (0x1C00A000) all fall inside 0x00400000..0x40000000. */
	.name = "malachite", .io_base = 0x00400000, .io_size = 0x3FC00000,
	.gic_dist = 0x0C000000, .gic_redist = 0x0C040000, .uart = MALACHITE_FAKE_UART, .log_other_cpu = 1,
	.cores = 8, .core_shift = 8,       /* cpu@N reg = 0xN00: MPIDR's second affinity field */
	.small_cores = 0x0f,               /* cpu0-3: Cortex-A55 (capacity-dmips-mhz 267), cpu4-7: A78 */
	.fb_base = 0xFD91F000,             /* LK's scanout buffer, top of the first 4 GiB; it can move
	                                    * with the RAM size, so efi_main also matches by range */
};

/*
 * The devices the loader knows, told apart by the framebuffer base their UEFI reports. A port to another
 * device adds its description here (common/new-device.sh writes a starting point, docs/PORTING.md says
 * where each value comes from); a display that matches none is QEMU's ramfb.
 */
static const struct platform *const platforms[] = {
	&platform_redwood,
	&platform_malachite,
};

/* ------------------------------------------------------------------------ */

static void
reboot(void)
{
	hc_take_back("before the reset");
	flush_log();
	ST->rt->reset_system(0 /* EfiResetCold */, 0, 0, NULL);
	for (;;) {
	}
}

/*
 * Return-from-kernel support.
 *
 * Boot services are never exited: UEFI stays resident outside XNU's memory
 * window. loader_save_ctx() records the UEFI execution environment and
 * returns 0. When the kernel is done it jumps to loader_return_stub (mapped
 * 1:1 or with the MMU off) with x0 = PA of its log, x1 = length, x2 = reason
 * (0 = orderly, 1 = early exception, then x3..x7 = ESR, ELR, FAR, LR, SP).
 * The stub switches the MMU off, reinstates the saved environment and makes
 * loader_save_ctx() return a second time, with 1.
 *
 * The EL1 physical timer (CNTP_*) is deliberately left alone: the Qualcomm
 * hypervisor traps it. The CTX_CNTP_* slots are unused.
 */
enum {
	CTX_TTBR0, CTX_TCR, CTX_MAIR, CTX_SCTLR, CTX_VBAR, CTX_CPACR, CTX_SP, CTX_SPSEL, CTX_DAIF,
	CTX_CNTV_CTL, CTX_CNTV_CVAL, CTX_CNTP_CTL, CTX_CNTP_CVAL, CTX_CNTKCTL,
	CTX_X18, CTX_X19, /* ... x30 */
	CTX_LOG_PA = CTX_X19 + 12, CTX_LOG_LEN, CTX_REASON, CTX_ESR, CTX_ELR, CTX_FAR, CTX_LR, CTX_KSP,
	CTX_TPIDR_EL1, CTX_TPIDR_EL0, CTX_TPIDRRO_EL0, CTX_SP_EL0, CTX_CONTEXTIDR, CTX_MDSCR, CTX_FPCR, CTX_FPSR,
	CTX_ICC_PMR, CTX_ICC_IGRPEN1, CTX_ICC_BPR1, CTX_COUNT
};
uint64_t loader_ctx[CTX_COUNT];
int loader_save_ctx(void);
void loader_return_stub(void);

__asm__ (
        ".text\n"
        ".balign 64\n"
        ".globl loader_save_ctx\n"
        "loader_save_ctx:\n"
        "  adrp x10, loader_ctx\n"
        "  add  x10, x10, :lo12:loader_ctx\n"
        "  mrs x9, ttbr0_el1\n   str x9, [x10, #0]\n"
        "  mrs x9, tcr_el1\n     str x9, [x10, #8]\n"
        "  mrs x9, mair_el1\n    str x9, [x10, #16]\n"
        "  mrs x9, sctlr_el1\n   str x9, [x10, #24]\n"
        "  mrs x9, vbar_el1\n    str x9, [x10, #32]\n"
        "  mrs x9, cpacr_el1\n   str x9, [x10, #40]\n"
        "  mov x9, sp\n          str x9, [x10, #48]\n"
        "  mrs x9, spsel\n       str x9, [x10, #56]\n"
        "  mrs x9, daif\n        str x9, [x10, #64]\n"
        "  mrs x9, cntv_ctl_el0\n  str x9, [x10, #72]\n"
        "  mrs x9, cntv_cval_el0\n str x9, [x10, #80]\n"
        "  mrs x9, cntkctl_el1\n   str x9, [x10, #104]\n"
        /* Qualcomm's UEFI has its own thread scheduler and keeps its current-thread
         * pointer in TPIDR_EL1; the kernel overwrites it, so it must come back intact. */
        "  mrs x9, tpidr_el1\n     str x9, [x10, #280]\n"
        "  mrs x9, tpidr_el0\n     str x9, [x10, #288]\n"
        "  mrs x9, tpidrro_el0\n   str x9, [x10, #296]\n"
        "  mrs x9, contextidr_el1\n str x9, [x10, #312]\n"
        "  mrs x9, mdscr_el1\n     str x9, [x10, #320]\n"
        "  mrs x9, s3_3_c4_c4_0\n          str x9, [x10, #328]\n"
        "  mrs x9, s3_3_c4_c4_1\n          str x9, [x10, #336]\n"
        /* GICv3 CPU interface: the kernel reprograms it for its own interrupts */
        "  mrs x9, icc_pmr_el1\n     str x9, [x10, #344]\n"
        "  mrs x9, icc_igrpen1_el1\n str x9, [x10, #352]\n"
        "  mrs x9, icc_bpr1_el1\n    str x9, [x10, #360]\n"
        "  mrs x9, spsel\n"
        "  cbz x9, 1f\n"                  /* SP_EL0 is only accessible while running on SP_EL1 */
        "  mrs x9, sp_el0\n        str x9, [x10, #304]\n"
        "1:\n"
        "  str x18, [x10, #112]\n"
        "  stp x19, x20, [x10, #120]\n"
        "  stp x21, x22, [x10, #136]\n"
        "  stp x23, x24, [x10, #152]\n"
        "  stp x25, x26, [x10, #168]\n"
        "  stp x27, x28, [x10, #184]\n"
        "  stp x29, x30, [x10, #200]\n"
        "  mov x0, #0\n"
        "  ret\n"
        ".balign 64\n"
        ".globl loader_return_stub\n"
        "loader_return_stub:\n"
        "  msr daifset, #0xf\n"
        /* PSTATE bits the kernel may have left set. PAN in particular is fatal:
         * UEFI maps its memory as EL0-accessible, so with PAN every data access
         * (including the exception handler's own stack push) faults. */
        "  .inst 0xd500409f\n"          /* msr PAN, #0 */
        "  .inst 0xd500407f\n"          /* msr UAO, #0 */
        "  mrs x9, sctlr_el1\n"
        "  bic x9, x9, #0x1\n"
        "  bic x9, x9, #0x4\n"
        "  bic x9, x9, #0x1000\n"
        "  msr sctlr_el1, x9\n"
        "  isb\n"
        "  adrp x10, loader_ctx\n"
        "  add  x10, x10, :lo12:loader_ctx\n"
        "  ldr x9, [x10, #0]\n   msr ttbr0_el1, x9\n"
        "  ldr x9, [x10, #8]\n   msr tcr_el1, x9\n"
        "  ldr x9, [x10, #16]\n  msr mair_el1, x9\n"
        "  ldr x9, [x10, #32]\n  msr vbar_el1, x9\n"
        "  ldr x9, [x10, #40]\n  msr cpacr_el1, x9\n"
        "  isb\n"
        "  tlbi vmalle1\n"
        "  dsb sy\n"
        "  ic iallu\n"
        "  isb\n"
        "  ldr x9, [x10, #24]\n  msr sctlr_el1, x9\n"
        "  isb\n"
        "  ldr x9, [x10, #56]\n"
        "  cbz x9, 1f\n"
        "  msr spsel, #1\n"
        "  ldr x9, [x10, #304]\n msr sp_el0, x9\n"
        "  b 2f\n"
        "1:\n"
        "  msr spsel, #0\n"
        "2:\n"
        "  ldr x9, [x10, #48]\n  mov sp, x9\n"
        "  ldr x9, [x10, #280]\n msr tpidr_el1, x9\n"
        "  ldr x9, [x10, #288]\n msr tpidr_el0, x9\n"
        "  ldr x9, [x10, #296]\n msr tpidrro_el0, x9\n"
        "  ldr x9, [x10, #312]\n msr contextidr_el1, x9\n"
        "  ldr x9, [x10, #320]\n msr mdscr_el1, x9\n"
        "  ldr x9, [x10, #344]\n msr icc_pmr_el1, x9\n"
        "  ldr x9, [x10, #360]\n msr icc_bpr1_el1, x9\n"
        "  ldr x9, [x10, #352]\n msr icc_igrpen1_el1, x9\n"
        "  ldr x9, [x10, #328]\n msr s3_3_c4_c4_0, x9\n"
        "  ldr x9, [x10, #336]\n msr s3_3_c4_c4_1, x9\n"
        "  ldr x9, [x10, #104]\n msr cntkctl_el1, x9\n"
        "  ldr x9, [x10, #80]\n  msr cntv_cval_el0, x9\n"
        "  ldr x9, [x10, #72]\n  msr cntv_ctl_el0, x9\n"
        "  ldr x18, [x10, #112]\n"
        "  ldp x19, x20, [x10, #120]\n"
        "  ldp x21, x22, [x10, #136]\n"
        "  ldp x23, x24, [x10, #152]\n"
        "  ldp x25, x26, [x10, #168]\n"
        "  ldp x27, x28, [x10, #184]\n"
        "  ldp x29, x30, [x10, #200]\n"
        "  stp x0, x1, [x10, #216]\n"   /* kernel log PA and length, stored with caches on */
        "  stp x2, x3, [x10, #232]\n"   /* reason, ESR */
        "  stp x4, x5, [x10, #248]\n"   /* ELR, FAR */
        "  stp x6, x7, [x10, #264]\n"   /* LR, SP */
        "  ldr x9, [x10, #64]\n  msr daif, x9\n"
        "  mov x0, #1\n"
        "  ret\n"
        );

__attribute__((noreturn)) static void
jump_to_kernel(uint64_t entry, uint64_t boot_args_pa)
{
	__asm__ volatile (
                "msr daifset, #0xf\n"
                /* Last thing before the MMU goes off: write this stack back to RAM
                 * (dirty cache lines do not survive, and we come back to this frame). */
                "mov x2, sp\n"
                "sub x2, x2, #0x400\n"
                "bic x2, x2, #63\n"
                "add x3, x2, #0x4000\n"
                "1: dc cvac, x2\n"
                "add x2, x2, #64\n"
                "cmp x2, x3\n"
                "b.lo 1b\n"
                "dsb sy\n"
                "mrs x2, sctlr_el1\n"
                "bic x2, x2, #0x1\n"    /* M: MMU off */
                "bic x2, x2, #0x4\n"    /* C: data cache off */
                "bic x2, x2, #0x1000\n" /* I: instruction cache off */
                "msr sctlr_el1, x2\n"
                "isb\n"
                "ic iallu\n"
                "dsb sy\n"
                "isb\n"
                "mov x0, %1\n"
                "br %0\n"
                : : "r" (entry), "r" (boot_args_pa) : "x0", "x2", "x3");
	__builtin_unreachable();
}

/* ------------------------------------------------------------------------ */
/* The kernel on another core.                                               */
/*                                                                          */
/* The firmware runs on core 0, one of the four small ones (Cortex-A55); the */
/* kernel uses a single core, and it had better be a big one (the A78s are   */
/* about 2.5 times as fast). With "bootcpu=N" among the kernel's arguments   */
/* the loader does not jump into the kernel itself: it has the firmware      */
/* (PSCI) start core N at other_cpu_entry, which enters the kernel exactly   */
/* as core 0 would have, and waits. UEFI stays resident and lives on core 0, */
/* so the kernel's way back is different too: other_cpu_return_stub, on core */
/* N, leaves what the kernel returned where core 0 looks for it, wakes core  */
/* 0 and switches its own core off.                                         */

#define PSCI_CPU_OFF       0x84000002u
#define PSCI_CPU_ON        0xC4000003u
#define PSCI_AFFINITY_INFO 0xC4000004u      /* (MPIDR, 0): 0 = that core is on, 1 = off, 2 = being started */
#define PSCI_NOT_SUPPORTED (-1)

/* each alone in a cache line: one core reads them with its caches off */
static struct {
	uint64_t entry, boot_args;
} other_cpu_start __attribute__((aligned(64)));
volatile uint64_t other_cpu_stage __attribute__((aligned(64)));  /* 1: that core has reached other_cpu_entry */
volatile uint64_t other_cpu_done __attribute__((aligned(64)));   /* 1: the kernel is back (other_cpu_return_stub) */
uint64_t other_cpu_el __attribute__((aligned(64)));              /* CurrentEL that core started at */
uint64_t psci_by_hvc __attribute__((aligned(64)));
void other_cpu_entry(void);
void other_cpu_return_stub(void);

__asm__ (
        ".text\n"
        ".balign 64\n"
        ".globl other_cpu_entry\n"
        "other_cpu_entry:\n"                    /* MMU and caches are off; the entry and its arguments are in other_cpu_start */
        "  msr daifset, #0xf\n"
        "  mrs x12, CurrentEL\n"                 /* remember which EL the firmware started this core at */
        "  adrp x13, other_cpu_el\n"
        "  add  x13, x13, :lo12:other_cpu_el\n"
        "  str x12, [x13]\n"
        /*
         * PSCI CPU_ON can enter a secondary core at EL2 on this SoC. This code
         * (and the kernel's early boot) is written for EL1, where the boot core
         * runs under the firmware; on EL2 every cpacr_el1/sctlr_el1 access traps
         * to EL2 and lands in other_cpu_fault (reason 1, no log). Set up a
         * plain EL1&0 regime and drop to EL1 first.
         */
        "  cmp x12, #0x8\n"
        "  b.ne 1f\n"
        "  mov x11, #0x80000000\n"               /* HCR_EL2: RW=1 (AArch64 EL1), no traps */
        "  msr hcr_el2, x11\n"
        "  msr cptr_el2, xzr\n"                  /* no FP/SIMD traps from EL1 */
        "  isb\n"
        "  adrp x9, other_cpu_entry_el1\n"
        "  add  x9, x9, :lo12:other_cpu_entry_el1\n"
        "  msr elr_el2, x9\n"
        "  mov x9, #0x3c5\n"                     /* SPSR: EL1h, DAIF masked */
        "  msr spsr_el2, x9\n"
        "  eret\n"
        "1:\n"
        "other_cpu_entry_el1:\n"
        /* until the kernel has vectors of its own, an exception must not go nowhere */
        "  adrp x9, other_cpu_vectors\n"
        "  add  x9, x9, :lo12:other_cpu_vectors\n"
        "  msr vbar_el1, x9\n"
        /* what the firmware had set up on the core the kernel used to start on, the kernel may take
         * for granted: floating point allowed (CPACR), the fixed bits of SCTLR */
        "  adrp x10, loader_ctx\n"
        "  add  x10, x10, :lo12:loader_ctx\n"
        "  ldr x9, [x10, #40]\n"
        "  msr cpacr_el1, x9\n"
        "  ldr x9, [x10, #24]\n"
        "  bic x9, x9, #0x1\n"
        "  bic x9, x9, #0x4\n"
        "  bic x9, x9, #0x1000\n"
        "  msr sctlr_el1, x9\n"
        "  isb\n"
        "  adrp x9, other_cpu_stage\n"
        "  add  x9, x9, :lo12:other_cpu_stage\n"
        "  mov x10, #1\n"
        "  str x10, [x9]\n"
        /* the kernel entry and its boot_args, from this loader's own memory: the
         * firmware's context register is not relied on (it read back as zero) */
        "  adrp x10, other_cpu_start\n"
        "  add  x10, x10, :lo12:other_cpu_start\n"
        "  ldp x9, x11, [x10]\n"
        "  mov x0, x11\n"
        "  br x9\n"
        "other_cpu_fault:\n"                    /* as an early exception in the kernel: reason 1 */
        "  mrs x3, esr_el1\n"
        "  mrs x4, elr_el1\n"
        "  mrs x5, far_el1\n"
        "  mov x6, x30\n"
        "  mov x7, sp\n"
        "  mov x0, #0\n"
        "  mov x1, #0\n"
        "  mov x2, #1\n"
        "  b other_cpu_return_stub\n"
        ".balign 0x800\n"
        "other_cpu_vectors:\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        "  b other_cpu_fault\n  .balign 0x80\n  b other_cpu_fault\n  .balign 0x80\n"
        ".balign 64\n"
        ".globl other_cpu_return_stub\n"
        "other_cpu_return_stub:\n"              /* x0..x7 as for loader_return_stub */
        "  msr daifset, #0xf\n"
        "  .inst 0xd500409f\n"                  /* msr PAN, #0 */
        "  .inst 0xd500407f\n"                  /* msr UAO, #0 */
        "  mrs x9, sctlr_el1\n"
        "  bic x9, x9, #0x1\n"
        "  bic x9, x9, #0x4\n"
        "  bic x9, x9, #0x1000\n"
        "  msr sctlr_el1, x9\n"
        "  isb\n"
        "  adrp x10, loader_ctx\n"
        "  add  x10, x10, :lo12:loader_ctx\n"
        "  stp x0, x1, [x10, #216]\n"           /* kernel log PA and length */
        "  stp x2, x3, [x10, #232]\n"           /* reason, ESR */
        "  stp x4, x5, [x10, #248]\n"           /* ELR, FAR */
        "  stp x6, x7, [x10, #264]\n"           /* LR, SP */
        "  adrp x10, other_cpu_done\n"
        "  add  x10, x10, :lo12:other_cpu_done\n"
        "  mov x9, #1\n"
        "  str x9, [x10]\n"
        "  dsb sy\n"
        "  sev\n"
        "  adrp x10, psci_by_hvc\n"
        "  add  x10, x10, :lo12:psci_by_hvc\n"
        "  ldr x9, [x10]\n"
        "  mov x0, #0x0002\n"                   /* PSCI CPU_OFF: does not return */
        "  movk x0, #0x8400, lsl #16\n"
        "  cbnz x9, 2f\n"
        "  smc #0\n"
        "1: wfi\n"
        "  b 1b\n"
        "2: hvc #0\n"
        "  b 1b\n"
        );

/*
 * The log monitor: a core the kernel never learns about (it runs with cpus=1)
 * adopts the UEFI page tables and cache settings handed to it in monitor_args
 * -- so its reads of the kernel's log are cache-coherent with the kernel's
 * writes -- and then sits in monitor_main drawing that log.
 */
__asm__ (
        ".text\n"
        ".balign 64\n"
        ".globl monitor_entry\n"
        "monitor_entry:\n"                      /* caches and MMU off */
        "  msr daifset, #0xf\n"
        "  mrs x9, CurrentEL\n"
        "  cmp x9, #0x8\n"
        "  b.ne 1f\n"
        "  mov x11, #0x80000000\n"              /* HCR_EL2: RW=1, no traps */
        "  msr hcr_el2, x11\n"
        "  msr cptr_el2, xzr\n"
        "  isb\n"
        "  adrp x9, monitor_entry_el1\n"
        "  add  x9, x9, :lo12:monitor_entry_el1\n"
        "  msr elr_el2, x9\n"
        "  mov x9, #0x3c5\n"                    /* SPSR: EL1h, DAIF masked */
        "  msr spsr_el2, x9\n"
        "  eret\n"
        "1:\n"
        "monitor_entry_el1:\n"
        "  adrp x10, monitor_args\n"
        "  add  x10, x10, :lo12:monitor_args\n"
        "  ldr x9, [x10, #16]\n"                /* ttbr0 */
        "  msr ttbr0_el1, x9\n"
        "  ldr x9, [x10, #24]\n"                /* tcr */
        "  msr tcr_el1, x9\n"
        "  ldr x9, [x10, #32]\n"                /* mair */
        "  msr mair_el1, x9\n"
        "  dsb sy\n"
        "  isb\n"
        "  tlbi vmalle1\n"
        "  dsb sy\n"
        "  isb\n"
        "  ldr x9, [x10, #40]\n"                /* sctlr: UEFI's, MMU and caches on */
        "  msr sctlr_el1, x9\n"
        "  isb\n"
        "  adrp x9, monitor_stack\n"
        "  add  x9, x9, :lo12:monitor_stack\n"
        "  add  x9, x9, #16384\n"
        "  mov  sp, x9\n"
        "  bl monitor_main\n"
        "2: wfi\n"
        "  b 2b\n"
        );

static uint64_t smc_call(uint64_t id, uint64_t a1, uint64_t a2, uint64_t *r1, uint64_t *r2);
static uint64_t smc_x3;
static const struct platform *PLAT;
static void clean_dcache(uint64_t start, uint64_t end);
static void flush_dcache(uint64_t start, uint64_t end);

/* What the kernel shows a watching loader (struct loader_live in XNU's loader_return.c). */
struct kernel_live {
	uint64_t magic;                 /* "XNULIVE!" */
	uint64_t heartbeat;             /* goes up every 10 seconds while the kernel is alive */
	uint64_t log, log_len, log_ring_at, log_wrapped;        /* the kernel's virtual addresses: add the slide */
	uint64_t log_head, log_ring;    /* the log: this much from the start of the boot, then a ring this big */
	uint64_t recording;             /* (a virtual address too) { physical address, bytes } of a screen recording */
	uint64_t stop;                  /* ours to write: the host wants the run to end ("oem stop") */
	uint64_t magic2;                /* "XNULIVE2": the kernel is new enough to have what follows */
	uint64_t sound;                 /* (a virtual address too) the same for a recording of the sound */
};

/*
 * Battery state shared with XNU.  Qualcomm's charger firmware remains a UEFI
 * boot-service client on core 0 while XNU runs on another core.  The loader is
 * therefore the one safe place to call it; XNU only reads this cache.
 */
#define LOADER_BATTERY_MAGIC            0x2154544142574452ULL /* "RDWBATT!" */
#define LOADER_BATTERY_VERSION          1
#define LOADER_BATTERY_VALID            (1u << 0)
#define LOADER_BATTERY_PRESENT          (1u << 1)
#define LOADER_BATTERY_CHARGER_PRESENT  (1u << 2)
#define LOADER_BATTERY_VOLTAGE_VALID    (1u << 3)
#define LOADER_BATTERY_CHARGING         (1u << 4)
#define LOADER_BATTERY_SOC_ESTIMATED    (1u << 5)

struct loader_battery {
	uint64_t magic;
	uint32_t version, size;
	volatile uint32_t sequence;
	uint32_t flags;
	int32_t soc_percent;
	int32_t voltage_mv;
	int32_t current_ma;
	int32_t temperature_c;
	uint32_t charger_action;
	uint32_t polls;
	uint32_t failures;
	uint32_t reserved;
};

/*
 * Layout returned by QcomChargerDxeLA's GetChargingAction, word offsets confirmed by dumping the
 * raw buffer on this phone: [2] state of charge, [3] charge current (signed mA), [4] battery
 * voltage (mV), [5] temperature (C). `rest` is oversized on purpose so a firmware that writes
 * more than the fields we name cannot smash the stack.
 */
struct qcom_battery_status {
	uint32_t status0, status1;
	int32_t state_of_charge;
	int32_t charge_current_ma;
	int32_t battery_voltage_mv;
	int32_t battery_temperature_c;
	uint32_t rest[26];
};

static struct loader_battery charger_shared __attribute__((aligned(0x2000))) = {
	.magic = LOADER_BATTERY_MAGIC,
	.version = LOADER_BATTERY_VERSION,
	.size = sizeof(struct loader_battery),
	.soc_percent = -1,
	.voltage_mv = -1,
	.current_ma = 0,
	.temperature_c = -273,
	.charger_action = 0xffffffffu,
};
static efi_charger_ex *CHARGER_EX;
static efi_qcom_charger *QCOM_CHARGER;
static int charger_enabled;

/* The screen recording the last kernel left in memory, if it made one ("oem recording" stages it). */
static const char *recording_data;
static uint64_t recording_len;
/* ... and the recording of the sound ("oem sound"). */
static const char *sound_data;
static uint64_t sound_len;
#define KERNEL_LIVE_MAGIC2      0x324556494c554e58ULL
#define KERNEL_LIVE_MAGIC       0x214556494c554e58ULL
#define OTHER_CPU_NOT_STARTED   1000    /* run_on_other_cpu(): the firmware said yes but the core never arrived */
#define OTHER_CPU_HUNG          1001    /* ... the kernel stopped giving signs of life */
#define START_SECONDS           5
#define SILENCE_SECONDS         50
#define NOTE_SECONDS            24      /* how long the kernel's progress is written down as it happens */

static void wdt_pet(void);
static int wdt_armed;

/*
 * While a kernel runs on another core and this one watches it: where it shows its signs of life,
 * for the commands that the host sends meanwhile (usb_poll_command).
 */
static const struct kernel_live *running_live;
static uint64_t running_slide;
static void usb_poll_command(void);
static void stage_paint(uint32_t argb);
static void stage_corner(uint32_t argb, int right, int bottom, unsigned px);
static void fb_render_log(const char *log, uint64_t len, uint32_t fg);
static void monitor_footer(uint64_t new_bytes, unsigned hidden);
static void monitor_ustacks(uint64_t slide);
static unsigned fb_reserve_rows;       /* rows the monitor keeps for its footer */

/*
 * The kernel's log, live. loader_return.c keeps every kprintf character
 * (pexpert/arm/pe_kprintf.c) and everything user space writes to /dev/console
 * (bsd/dev/arm/km.c) in loader_log -- a linear first part and a ring -- and
 * loader_live publishes where it and its state are. Reading that from this
 * core and drawing it needs no return and no cooperation from the kernel.
 *
 * The screen shows whole lines and leaves the persona noise out: this port has
 * no persona subsystem, the kernel answers ESRCH to everything that asks about
 * one, and launchd and usermanagerd ask on every spawn and every sync. The
 * full log is still in loader_log; only the panel would otherwise be filled
 * with "no such process" and lose the line that says where the boot really is.
 */
#define LOG_TAIL_SIZE 32768u

static char log_tail[LOG_TAIL_SIZE];
static char log_clean[LOG_TAIL_SIZE];  /* the last 32 KB of lines worth showing, as a ring */
static char log_line[512];
static uint32_t log_clean_at, log_clean_len;
static unsigned log_hidden;            /* noise lines left out, last pass */
/* A sign of life that survives the log wrapping: characters the monitor has seen arrive. */
static uint64_t log_new_bytes;
static uint32_t log_last_pos;
static int log_last_wrapped = -1;      /* -1: no look yet; else whether the ring had wrapped */

static int
log_find(const char *s, const char *needle)
{
	for (; *s != 0; s++) {
		const char *a = s, *b = needle;

		while (*b != 0 && *a == *b) {
			a++;
			b++;
		}
		if (*b == 0) {
			return 1;
		}
	}
	return 0;
}

static int
log_noise(const char *line)
{
	static const char *const patterns[] = {
		"kpersona_find_by_type() failed",
		"Unable to find persona with type",
		"persona info for pid",
		"look up persona for pid",
		"info for kernel persona",
		"persona array OK:",
		"denied attempt to escape CPU monitor",
	};

	for (unsigned i = 0; i < sizeof(patterns) / sizeof(patterns[0]); i++) {
		if (log_find(line, patterns[i])) {
			return 1;
		}
	}
	return 0;
}

static void
log_clean_putc(char c)
{
	log_clean[log_clean_at] = c;
	if (++log_clean_at == LOG_TAIL_SIZE) {
		log_clean_at = 0;
	}
	if (log_clean_len < LOG_TAIL_SIZE) {
		log_clean_len++;
	}
}

static void
render_kernel_log(const struct kernel_live *live, uint64_t slide)
{
	const char *log = (const char *)(uintptr_t)(live->log + slide);
	uint32_t len = *(volatile uint32_t *)(live->log_len + slide);
	uint32_t ring_at = *(volatile uint32_t *)(live->log_ring_at + slide);
	uint32_t head = (uint32_t)live->log_head, ring = (uint32_t)live->log_ring;
	int wrapped = *(volatile uint8_t *)(live->log_wrapped + slide);
	const char *seg[3];
	uint32_t segn[3];
	int ns = 0;
	uint32_t line_len = 0, show, start, first;
	unsigned hidden = 0;

	if (ring_at > ring) {
		ring_at = ring;
	}
	if (!wrapped) {
		if (len > head + ring) {
			len = head + ring;
		}
		seg[0] = log;
		segn[0] = len;
		ns = 1;
	} else {
		seg[0] = log;
		segn[0] = head;
		seg[1] = log + head + ring_at;
		segn[1] = ring - ring_at;
		seg[2] = log + head;
		segn[2] = ring_at;
		ns = 3;
	}
	/*
	 * How much has arrived since the last look. The log's length stops moving once its ring
	 * wraps, so follow the ring pointer instead; a delta may then be short only if a whole
	 * ring went by between two looks (a megabyte in two seconds), which does not happen.
	 */
	if (!wrapped) {
		if (log_last_wrapped == 0 && len >= log_last_pos) {
			log_new_bytes += len - log_last_pos;
		}
		log_last_pos = len;
		log_last_wrapped = 0;
	} else if (log_last_wrapped == 1) {
		log_new_bytes += (ring_at + ring - log_last_pos) % ring;
		log_last_pos = ring_at;
	} else {
		log_last_pos = ring_at;
		log_last_wrapped = 1;
	}
	/* whole lines, oldest to newest: leave the noise out, keep the last 32 KB */
	log_clean_at = 0;
	log_clean_len = 0;
	for (int i = 0; i < ns; i++) {
		for (uint32_t j = 0; j < segn[i]; j++) {
			char c = seg[i][j];

			if (c == '\r') {
				continue;
			}
			if (c != '\n') {
				if (line_len < sizeof(log_line) - 1) {
					log_line[line_len++] = c;
				}
				continue;
			}
			log_line[line_len] = 0;
			if (line_len != 0 && log_noise(log_line)) {
				hidden++;
			} else {
				for (uint32_t k = 0; k < line_len; k++) {
					log_clean_putc(log_line[k]);
				}
				log_clean_putc('\n');
			}
			line_len = 0;
		}
	}
	/* a line still being written has no '\n' yet: it is the newest text there is */
	if (line_len != 0) {
		log_line[line_len] = 0;
		if (!log_noise(log_line)) {
			for (uint32_t k = 0; k < line_len; k++) {
				log_clean_putc(log_line[k]);
			}
		}
	}
	log_hidden = hidden;

	show = log_clean_len;
	if (show == 0) {
		stage_paint(0xFF000000u);
		return;
	}
	start = (log_clean_at + LOG_TAIL_SIZE - show) % LOG_TAIL_SIZE;
	first = LOG_TAIL_SIZE - start;
	if (first > show) {
		first = show;
	}
	memcpy(log_tail, log_clean + start, first);
	memcpy(log_tail + first, log_clean, show - first);
	fb_render_log(log_tail, show, 0xFF00FF00u);
}

/* ------------------------------------------------------------------------ */
/* A log monitor on a core the kernel does not use                         */
/*                                                                          */
/* The kernel runs on the boot core with cpus=1; this loader starts another */
/* core with PSCI and leaves it drawing the kernel's log from loader_log.   */
/* It is given the UEFI regime (page tables, cache settings) so that what   */
/* it reads is cache-coherent with the kernel's writes, and it never asks   */
/* the kernel for anything -- no return, no heartbeat.                      */

#define MONITOR_MPIDR 0x700ULL                 /* a big core; the kernel is told it has one CPU */

struct monitor_args {
	uint64_t live, slide;                  /* where loader_live is, and the kernel's slide */
	uint64_t ttbr0, tcr, mair, sctlr;      /* the UEFI regime, for that core to adopt */
	/* appended below what monitor_entry reads by offset: where the log can be kept */
	uint64_t slot_bio;                     /* userdata's Block I/O, 0 when there is none */
	uint64_t slot_first, slot_blocks;      /* its first LBA and size, in media blocks */
	uint64_t slot_block_size;
	uint64_t ustacks_probe;                /* ustacks_probe=1: show the kernel's sampler globals */
};

/*
 * A copy of the log that outlives the run, in the free part of userdata.
 *
 * The firmware on this phone has no USB stack, so the loader cannot hand the log to the host
 * while the kernel hangs. What it can do is put it on the storage it drives itself: two slots
 * in userdata, four gigabytes in, well past the 2.4 GB system image at the partition's start.
 * The monitor core rewrites the newest one every few seconds; a "showprev=1" run reads the
 * newest valid one back and draws it (and the region can be read with mtkclient as well).
 *
 * A slot is one block of header and then the last bytes of loader_log in order. The two slots
 * are written alternately, so a write cut short by a reset leaves the other one intact; the
 * header carries a sequence number and a CRC of the text, which is how the reader picks.
 */
#define LOG_SLOT_OFFSET     (0x100000000ULL)    /* 4 GiB into userdata */
#define LOG_SLOT_SIZE       (2u << 20)          /* per slot */
#define LOG_SLOT_HEADER     4096u               /* text starts at this offset (one block) */
#define LOG_SLOT_MAGIC      0x5653474F4C554E58ULL /* "XNULOGSV" */

struct log_slot_header {
	uint64_t magic;
	uint32_t version;
	uint32_t length;                        /* bytes of text */
	uint64_t total;                         /* loader_log bytes at the time */
	uint64_t seq;
	uint64_t uptime_ms;
	uint32_t crc;                           /* of the text */
	uint32_t reserved;
};

static uint8_t log_slot_buf[LOG_SLOT_SIZE] __attribute__((aligned(0x1000)));
static uint64_t log_slot_seq;                   /* the last sequence number written */
static int log_slot_state;                      /* 0 not tried, 1 written, else the error's low bits */
static uint32_t log_slot_total;                 /* loader_log bytes at the last write */
static void save_log_slot(const struct kernel_live *live, uint64_t slide);

struct monitor_args monitor_args;
uint8_t monitor_stack[16384] __attribute__((aligned(16)));
void monitor_entry(void);
void monitor_main(void);

void
monitor_main(void)
{
	const struct kernel_live *live = (const struct kernel_live *)(uintptr_t)monitor_args.live;
	uint64_t freq = READ_SYSREG(CNTFRQ_EL0);
	uint64_t last_save = 0;

	for (;;) {
		uint64_t started, now;

		if (live != NULL) {
			now = READ_SYSREG(CNTVCT_EL0);
			fb_reserve_rows = monitor_args.ustacks_probe != 0 ? 2 : 1;
			render_kernel_log(live, monitor_args.slide);
			/*
			 * The log is put on the storage as it stands every ten seconds: the last slot
			 * written before a hang is what a "showprev=1" run (or mtkclient) gets back.
			 */
			if (monitor_args.slot_bio != 0 && now - last_save >= 10 * freq) {
				last_save = now;
				save_log_slot(live, monitor_args.slide);
			}
			monitor_footer(log_new_bytes, log_hidden);
			if (monitor_args.ustacks_probe != 0) {
				monitor_ustacks(monitor_args.slide);
			}
		}
		started = READ_SYSREG(CNTVCT_EL0);
		while (READ_SYSREG(CNTVCT_EL0) - started < 2 * freq) {
		}
	}
}

static uint64_t
seconds_since(uint64_t then)
{
	return (READ_SYSREG(CNTVCT_EL0) - then) / READ_SYSREG(CNTFRQ_EL0);
}

/* Reverse a stretch of memory in place. */
static void
reverse(char *p, uint64_t n)
{
	for (uint64_t i = 0; i < n / 2; i++) {
		char c = p[i];

		p[i] = p[n - 1 - i];
		p[n - 1 - i] = c;
	}
}

/*
 * The log of a kernel that did not come back to hand it over: put its two parts in order
 * (the ring's oldest character first) and say where it is and how long.
 */
static void
log_of_hung_kernel(const struct kernel_live *live, uint64_t slide)
{
	char *log = (char *)(live->log + slide);
	uint32_t len, ring_at;

	loader_ctx[CTX_LOG_PA] = loader_ctx[CTX_LOG_LEN] = 0;
	len = *(volatile uint32_t *)(live->log_len + slide);
	ring_at = *(volatile uint32_t *)(live->log_ring_at + slide);
	if (*(volatile uint8_t *)(live->log_wrapped + slide) && ring_at < live->log_ring) {
		/* rotate the ring left by ring_at: three reversals */
		reverse(log + live->log_head, ring_at);
		reverse(log + live->log_head + ring_at, live->log_ring - ring_at);
		reverse(log + live->log_head, live->log_ring);
		len = (uint32_t)(live->log_head + live->log_ring);
	}
	if (len <= live->log_head + live->log_ring) {
		loader_ctx[CTX_LOG_PA] = (uint64_t)(uintptr_t)log;
		loader_ctx[CTX_LOG_LEN] = len;
	}
}

/*
 * The log of a kernel that is alive and is merely being asked how it is doing ("oem log" during
 * a run): a copy in the right order after the loader's own log, with nothing moved under the
 * kernel's feet.
 */
static void
compose_live_log(const struct kernel_live *live, uint64_t slide)
{
	static const char sep[] = "\n== KERNEL LOG (the kernel is still running) ==\n";
	const char *log = (const char *)(live->log + slide);
	uint32_t len = *(volatile uint32_t *)(live->log_len + slide);
	uint32_t ring_at = *(volatile uint32_t *)(live->log_ring_at + slide);
	int wrapped = *(volatile uint8_t *)(live->log_wrapped + slide);
	uint64_t n, room = sizeof(out_buf) - 8192;

	compose_logs(NULL, 0);
	n = staged_len;
#define PUT(from, size) do { \
	uint64_t take = (size); \
	if (n + take > room) { \
	        take = room - n; \
	} \
	memcpy(out_buf + n, (from), take); \
	n += take; \
} while (0)
	PUT(sep, sizeof(sep) - 1);
	if (!wrapped || ring_at >= live->log_ring) {
		PUT(log, len <= live->log_head + live->log_ring ? len : live->log_head + live->log_ring);
	} else {
		PUT(log, live->log_head);
		PUT(log + live->log_head + ring_at, live->log_ring - ring_at);
		PUT(log + live->log_head, ring_at);
	}
#undef PUT
	staged_len = n;
}

static void print(const char *fmt, ...);
static void flush_log(void);
static void put_char(char c);

/* A voltage-only fallback is deliberately conservative; the real QG SOC wins whenever available. */
static int
soc_from_voltage(uint32_t mv)
{
	if (mv <= 3300) return 0;
	if (mv < 3700) return (int)((mv - 3300) * 10 / 400);
	if (mv < 3900) return 10 + (int)((mv - 3700) * 40 / 200);
	if (mv < 4200) return 50 + (int)((mv - 3900) * 40 / 300);
	if (mv < 4400) return 90 + (int)((mv - 4200) * 10 / 200);
	return 100;
}

/* Read-only status query.  No TakeAction call and no charger-limit writes are made here. */
static void
charger_poll(void)
{
	struct qcom_battery_status status;
	uint32_t action = 0xffffffffu, flags = 0, voltage = 0;
	uint8_t present = 0, plugged = 0;
	efi_status s;
	int have_soc = 0, have_voltage = 0;

	if (!charger_enabled) {
		return;
	}
	memset(&status, 0, sizeof(status));

	charger_shared.sequence++;
	__asm__ volatile ("dmb ish" ::: "memory");
	if (CHARGER_EX != NULL) {
		s = CHARGER_EX->get_battery_presence(&present);
		if (!EFI_ERROR(s) && present) flags |= LOADER_BATTERY_PRESENT;
		s = CHARGER_EX->get_charger_presence(&plugged);
		if (!EFI_ERROR(s) && plugged) flags |= LOADER_BATTERY_CHARGER_PRESENT;
		s = CHARGER_EX->get_battery_voltage(&voltage);
		if (!EFI_ERROR(s) && voltage >= 2500 && voltage <= 5000) {
			have_voltage = 1;
			flags |= LOADER_BATTERY_VOLTAGE_VALID;
			charger_shared.voltage_mv = (int32_t)voltage;
		}
	}
	if (QCOM_CHARGER != NULL) {
		s = QCOM_CHARGER->get_charging_action(&action, &status, 0);
		if (!EFI_ERROR(s)) {
			charger_shared.charger_action = action;
			if (status.battery_voltage_mv >= 2500 && status.battery_voltage_mv <= 5000) {
				charger_shared.voltage_mv = status.battery_voltage_mv;
				have_voltage = 1;
				flags |= LOADER_BATTERY_VOLTAGE_VALID;
			}
			/*
			 * GetChargingAction returns the firmware's state of charge in word [2] of its
			 * output (confirmed by dumping the raw buffer on this device). We use it as-is
			 * EXCEPT when the fuel gauge is clearly not ready yet: right after initialize()
			 * it can report a near-empty SOC while the cell voltage says otherwise, which is
			 * where the old "shows 1% on a half-full battery" came from. A Li-ion cell above
			 * ~3.6 V is never under 5%, so in that case we distrust the gauge and fall back to
			 * the voltage estimate below until it settles.
			 */
			if (status.state_of_charge >= 0 && status.state_of_charge <= 100) {
				int vmv = have_voltage ? charger_shared.voltage_mv : 0;
				if (status.state_of_charge < 5 && vmv > 3600) {
					/* fuel gauge not settled; leave it to the voltage fallback */
				} else {
					charger_shared.soc_percent = status.state_of_charge;
					have_soc = 1;
					flags |= LOADER_BATTERY_VALID;
				}
			}
			charger_shared.current_ma = status.charge_current_ma;
			charger_shared.temperature_c = status.battery_temperature_c;
		}
	}
	if (!have_soc && have_voltage) {
		charger_shared.soc_percent = soc_from_voltage((uint32_t)charger_shared.voltage_mv);
		flags |= LOADER_BATTERY_VALID | LOADER_BATTERY_SOC_ESTIMATED;
	}
	if (plugged && charger_shared.soc_percent < 100) {
		flags |= LOADER_BATTERY_CHARGING;
	}
	charger_shared.flags = flags;
	charger_shared.polls++;
	if (!(flags & LOADER_BATTERY_VALID)) charger_shared.failures++;
	__asm__ volatile ("dmb ish" ::: "memory");
	charger_shared.sequence++;
	clean_dcache((uint64_t)(uintptr_t)&charger_shared,
	    (uint64_t)(uintptr_t)&charger_shared + sizeof(charger_shared));
}

/* ------------------------------------------------------------------------ */
/* UFS survey (ufs=1): what the phone's storage holds, read only            */

/*
 * The phone's storage as Qualcomm's own UFS driver in this UEFI sees it (UFSDxe): every raw
 * logical unit, every GPT partition with its name, place and size, and for the partitions there
 * are reference images of -- firmware-update/ in the ROM's fw.zip -- an FNV-1a hash of exactly
 * as many bytes as the image has, which tools/ufs-survey.py computes from the images on the host.
 * Where the two agree, reading through this driver gives the bytes that are on the flash, and that
 * is the ground a block device for the kernel is to stand on.
 *
 * Only read_blocks is ever called here: nothing is written, flushed or reset. It runs before the
 * kernel is started, with UEFI's boot services whole and interrupts on.
 */
static const struct {
	const char *name;
	uint64_t bytes;
} ufs_references[] = {
	{ "bluetooth", 503808 }, { "abl", 208896 }, { "aop", 208896 }, { "xbl", 3706880 },
	{ "tz", 3710976 }, { "hyp", 3653632 }, { "dsp", 67108864 }, { "modem", 214265856 },
};

static uint8_t ufs_buffer[1024 * 1024] __attribute__((aligned(4096)));

static uint64_t
ufs_fnv(uint64_t h, const uint8_t *p, uint64_t n)
{
	for (uint64_t i = 0; i < n; i++) {
		h = (h ^ p[i]) * 0x100000001b3ULL;
	}
	return h;
}

/* the partition's name in ASCII (GPT names are UTF-16; these are all plain letters) */
static void
ufs_name(const efi_partition_info *info, char *out, unsigned size)
{
	unsigned i = 0;

	for (; i + 1 < size && i < 36 && info->name[i] != 0; i++) {
		out[i] = info->name[i] < 0x80 ? (char)info->name[i] : '?';
	}
	out[i] = 0;
}

/* "bluetooth_a" and "bluetooth_b" are both "bluetooth": the image is the same for either slot */
static int
ufs_reference_of(const char *name)
{
	for (unsigned r = 0; r < sizeof(ufs_references) / sizeof(ufs_references[0]); r++) {
		const char *a = ufs_references[r].name, *b = name;

		while (*a && *a == *b) {
			a++;
			b++;
		}
		if (*a == 0 && (*b == 0 || ((b[0] == '_') && (b[1] == 'a' || b[1] == 'b') && b[2] == 0))) {
			return (int)r;
		}
	}
	return -1;
}

static void
ufs_hash_partition(efi_block_io *bio, const char *name, uint64_t bytes)
{
	uint64_t bs = bio->media->block_size, h = 0xcbf29ce484222325ULL, done = 0, started = READ_SYSREG(CNTVCT_EL0);
	uint64_t chunk = sizeof(ufs_buffer) / bs * bs, lba = 0;

	if (bs == 0 || bs > sizeof(ufs_buffer) || (bio->media->last_block + 1) * bs < bytes) {
		print("ufs: %s: %d bytes asked for, the partition is smaller\n", name, bytes);
		return;
	}
	while (done < bytes) {
		uint64_t want = bytes - done < chunk ? (bytes - done + bs - 1) / bs * bs : chunk;
		efi_status s = bio->read_blocks(bio, bio->media->media_id, lba, want, ufs_buffer);

		if (EFI_ERROR(s)) {
			print("ufs: %s: reading at block %d: error %x\n", name, lba, (uint64_t)s);
			return;
		}
		if (done == 0) {
			print("ufs: %s: begins", name);
			for (int k = 0; k < 16; k++) {
				print(" %x", (uint64_t)ufs_buffer[k]);
			}
			print("\n");
		}
		h = ufs_fnv(h, ufs_buffer, bytes - done < want ? bytes - done : want);
		done += bytes - done < want ? bytes - done : want;
		lba += want / bs;
		if (wdt_armed) {
			wdt_pet();
		}
	}
	print("ufs: %s: fnv %x over %d bytes, %d ms\n", name, h, bytes,
	    (READ_SYSREG(CNTVCT_EL0) - started) * 1000 / READ_SYSREG(CNTFRQ_EL0));
}

/* CRC-32 as GPT uses it (IEEE 802.3, reflected, 0xedb88320) */
static uint32_t
ufs_crc32(const uint8_t *p, uint64_t n)
{
	uint32_t c = 0xffffffffu;

	for (uint64_t i = 0; i < n; i++) {
		c ^= p[i];
		for (int k = 0; k < 8; k++) {
			c = (c >> 1) ^ (0xedb88320u & (0u - (c & 1)));
		}
	}
	return ~c;
}

/*
 * A unit's GPT checks itself: its header carries a CRC-32 of the header and one of the table of
 * partitions. Whatever firmware is on the phone, the bytes read are the bytes on the flash only if
 * both come out right -- the one check here that does not depend on having the same images.
 */
/*
 * Android's dynamic partitions live inside "super" as liblp extents. Read the
 * metadata (read only), print each logical partition, and find the largest
 * unallocated hole: that is the one place a volume of this port's own can go
 * without moving any of Android's partitions.
 *
 * Layout (liblp/metadata_format.h): geometry at offset 4096, magic 0x616c4467,
 * metadata_max_size at 40, metadata_slot_count at 44; a slot's metadata is at
 * 3*4096 + slot*max_size. Header magic 0x414c5030, header_size at 8,
 * tables_size at 44; the table descriptors start at 80 (partitions), 92
 * (extents), 104 (groups), 116 (block devices), 12 bytes each. Partition
 * entry: name[36], attributes, first_extent_index, num_extents. Extent entry:
 * num_sectors u64, target_type u32, target_data u64, target_source u32; the
 * LINEAR extents of source 0 are the sectors used inside super.
 */
static void
ufs_analyze_super(efi_block_io *bio, uint64_t first_lba, uint64_t last_lba)
{
	uint64_t bs = bio->media->block_size;
	uint64_t sectors = (last_lba - first_lba + 1) * bs / 512;
	uint64_t head = (8192 + bs - 1) / bs * bs;   /* through the geometry at 4096 */
	const uint8_t *geometry;
	uint32_t max_size, slots;
	uint64_t want, read;

	if (bs == 0 || bs > sizeof(ufs_buffer) || head > sizeof(ufs_buffer) ||
	    EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, first_lba, head, ufs_buffer))) {
		print("ufs: super: its start could not be read\n");
		return;
	}
	geometry = ufs_buffer + 4096;
	if (*(const uint32_t *)geometry != 0x616c4467) {
		print("ufs: super: no liblp geometry (magic %x)\n", (uint64_t)*(const uint32_t *)geometry);
		return;
	}
	max_size = *(const uint32_t *)(geometry + 40);
	slots = *(const uint32_t *)(geometry + 44);
	if (max_size == 0 || slots == 0 || slots > 4) {
		print("ufs: super: max_size %x slots %d\n", (uint64_t)max_size, (uint64_t)slots);
		return;
	}
	want = 3 * 4096 + (uint64_t)slots * max_size;
	read = (want + bs - 1) / bs * bs;
	if (read > sizeof(ufs_buffer) ||
	    EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, first_lba, read, ufs_buffer))) {
		print("ufs: super: %d KB of metadata could not be read\n", want >> 10);
		return;
	}

	for (uint32_t slot = 0; slot < slots; slot++) {
		const uint8_t *hdr = ufs_buffer + 3 * 4096 + (uint64_t)slot * max_size;
		const uint8_t *tables;
		uint32_t header_size, tables_size, po, pn, pe, eo, en, ee;
		static struct { uint64_t start, len; } ex[96];
		unsigned nex = 0, i, j;
		uint64_t cursor = 0, covered = 0, best = 0, best_start = 0, best_end = 0;

		if (*(const uint32_t *)hdr != 0x414c5030) {
			print("ufs: super slot %d: no metadata header\n", (uint64_t)slot);
			continue;
		}
		header_size = *(const uint32_t *)(hdr + 8);
		tables_size = *(const uint32_t *)(hdr + 44);
		if (header_size < 128 || header_size + (uint64_t)tables_size > max_size) {
			print("ufs: super slot %d: header %x tables %x max %x\n", (uint64_t)slot,
			    (uint64_t)header_size, (uint64_t)tables_size, (uint64_t)max_size);
			continue;
		}
		tables = hdr + header_size;
		po = *(const uint32_t *)(hdr + 80);
		pn = *(const uint32_t *)(hdr + 84);
		pe = *(const uint32_t *)(hdr + 88);
		eo = *(const uint32_t *)(hdr + 92);
		en = *(const uint32_t *)(hdr + 96);
		ee = *(const uint32_t *)(hdr + 100);
		if (pe < 52 || ee < 24 || (uint64_t)po + (uint64_t)pn * pe > tables_size ||
		    (uint64_t)eo + (uint64_t)en * ee > tables_size) {
			print("ufs: super slot %d: tables p %x/%x/%x e %x/%x/%x, size %x\n", (uint64_t)slot,
			    (uint64_t)po, (uint64_t)pn, (uint64_t)pe, (uint64_t)eo, (uint64_t)en, (uint64_t)ee,
			    (uint64_t)tables_size);
			continue;
		}

		for (i = 0; i < pn; i++) {
			const uint8_t *p = tables + po + (uint64_t)i * pe;
			char name[37];
			uint64_t mb = 0;
			uint32_t fe = *(const uint32_t *)(p + 40);
			uint32_t np = *(const uint32_t *)(p + 44);

			memcpy(name, p, 36);
			name[36] = 0;
			for (j = 0; j < np && (uint64_t)(fe + j) < en; j++) {
				const uint8_t *e = tables + eo + (uint64_t)(fe + j) * ee;
				uint64_t ns = *(const uint64_t *)(e + 0);
				uint32_t tt = *(const uint32_t *)(e + 8);
				uint64_t td = *(const uint64_t *)(e + 12);
				uint32_t ts = *(const uint32_t *)(e + 20);

				mb += ns;
				if (tt == 0 && ts == 0 && nex < 96) {
					ex[nex].start = td;
					ex[nex].len = ns;
					nex++;
				}
			}
			if (slot == 0) {
				print("ufs: super p%d %s: %d MB\n", (uint64_t)i, name, (mb * 512) >> 20);
			}
		}

		for (i = 1; i < nex; i++) {
			for (j = i; j > 0 && ex[j].start < ex[j - 1].start; j--) {
				typeof(ex[0]) t = ex[j];

				ex[j] = ex[j - 1];
				ex[j - 1] = t;
			}
		}
		for (i = 0; i < nex; i++) {
			uint64_t s = ex[i].start, l = ex[i].len;

			if (s > cursor) {
				uint64_t bytes = (s - cursor) * 512;

				if (bytes > best) {
					best = bytes;
					best_start = cursor;
					best_end = s - 1;
				}
			}
			if (s + l > cursor) {
				covered += s + l - cursor;
				cursor = s + l;
			}
		}
		if (sectors > cursor) {
			uint64_t bytes = (sectors - cursor) * 512;

			if (bytes > best) {
				best = bytes;
				best_start = cursor;
				best_end = sectors - 1;
			}
		}
		if (covered > sectors) {
			covered = sectors;
		}
		print("ufs: super slot %d: %d parts, %d MB used, %d MB free, largest lba %x..%x (%d MB)\n",
		    (uint64_t)slot, (uint64_t)pn, (covered * 512) >> 20,
		    ((sectors - covered) * 512) >> 20, best_start, best_end, best >> 20);
	}
}

static void
ufs_check_gpt(efi_block_io *bio, uint64_t unit)
{
	uint64_t bs = bio->media->block_size, entries_lba, count, size, bytes, read;
	uint64_t super_first = 0, super_last = 0;
	uint32_t header_size, header_crc, entries_crc, got_header, got_entries;
	int have_super = 0;
	uint8_t header[512];

	if (bs < 512 || bs > sizeof(ufs_buffer) ||
	    EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, 1, bs, ufs_buffer))) {
		print("ufs: unit %d: the GPT header could not be read\n", unit);
		return;
	}
	if (ufs_buffer[0] != 'E' || ufs_buffer[1] != 'F' || ufs_buffer[2] != 'I' || ufs_buffer[3] != ' ' ||
	    ufs_buffer[4] != 'P' || ufs_buffer[5] != 'A' || ufs_buffer[6] != 'R' || ufs_buffer[7] != 'T') {
		print("ufs: unit %d: no GPT header in block 1\n", unit);
		return;
	}
	memcpy(header, ufs_buffer, sizeof(header));
	header_size = *(uint32_t *)(header + 12);
	header_crc = *(uint32_t *)(header + 16);
	entries_lba = *(uint64_t *)(header + 72);
	count = *(uint32_t *)(header + 80);
	size = *(uint32_t *)(header + 84);
	entries_crc = *(uint32_t *)(header + 88);
	if (header_size < 92 || header_size > sizeof(header)) {
		print("ufs: unit %d: GPT header size %d\n", unit, (uint64_t)header_size);
		return;
	}
	*(uint32_t *)(header + 16) = 0;
	got_header = ufs_crc32(header, header_size);
	bytes = count * size;
	if (bytes == 0 || bytes > sizeof(ufs_buffer)) {
		print("ufs: unit %d: GPT header crc %s, a table of %d bytes not checked\n", unit,
		    got_header == header_crc ? "right" : "WRONG", bytes);
		return;
	}
	read = (bytes + bs - 1) / bs * bs;
	if (EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, entries_lba, read, ufs_buffer))) {
		print("ufs: unit %d: the GPT table could not be read\n", unit);
		return;
	}
	got_entries = ufs_crc32(ufs_buffer, bytes);
	print("ufs: unit %d: GPT header crc %s (%x), table of %d entries crc %s (%x)\n", unit,
	    got_header == header_crc ? "right" : "WRONG", (uint64_t)got_header, count,
	    got_entries == entries_crc ? "right" : "WRONG", (uint64_t)got_entries);

	/*
	 * The partitions themselves, in table order: GPT entry is 128 bytes,
	 * the type GUID is all zero for an unused entry, and the name is
	 * UTF-16LE at offset 56 (36 code units).
	 */
	if (size < 128) {
		print("ufs: unit %d: entry size %d, not listed\n", unit, (uint64_t)size);
		return;
	}

	{
		/*
		 * The list itself has to fit the panel: two partitions per line,
		 * index, name and size, and the large ones once more with their
		 * exact LBA range. A gap between two used partitions is what a
		 * volume of the port's own could occupy without moving anything.
		 */
		static struct {
			uint64_t first, last;
			uint32_t index;
			char name[25];
		} parts[128];
		uint32_t n = 0;

		for (uint32_t e = 0; e < count && n < 128; e++) {
			const uint8_t *ent = ufs_buffer + (uint64_t)e * size;
			int used = 0, k;

			for (k = 0; k < 16; k++) {
				used |= ent[k];
			}
			if (used == 0) {
				continue;
			}
			parts[n].index = e;
			parts[n].first = *(const uint64_t *)(ent + 32);
			parts[n].last = *(const uint64_t *)(ent + 40);
			for (k = 0; k < 24; k++) {
				uint16_t c = (uint16_t)ent[56 + 2 * k] | ((uint16_t)ent[56 + 2 * k + 1] << 8);

				if (c == 0) {
					break;
				}
				parts[n].name[k] = c < 0x80 ? (char)c : '?';
			}
			parts[n].name[k] = 0;
			if (str_eq(parts[n].name, "super")) {
				super_first = parts[n].first;
				super_last = parts[n].last;
				have_super = 1;
			}
			n++;
		}

		/* table order is LBA order on this device, but sort to be sure */
		for (uint32_t i = 1; i < n; i++) {
			for (uint32_t j = i; j > 0 && parts[j].first < parts[j - 1].first; j--) {
				typeof(parts[0]) t = parts[j];

				parts[j] = parts[j - 1];
				parts[j - 1] = t;
			}
		}

		for (uint32_t i = 0; i < n; i += 2) {
			print("ufs: p%d %s %dM", (uint64_t)parts[i].index, parts[i].name,
			    (parts[i].last - parts[i].first + 1) * bs >> 20);
			if (i + 1 < n) {
				print(" | p%d %s %dM", (uint64_t)parts[i + 1].index, parts[i + 1].name,
				    (parts[i + 1].last - parts[i + 1].first + 1) * bs >> 20);
			}
			print("\n");
		}

		for (uint32_t i = 0; i < n; i++) {
			uint64_t mb = (parts[i].last - parts[i].first + 1) * bs >> 20;

			if (mb >= 1024) {
				print("ufs: big p%d %s: lba %x..%x, %d MB\n", (uint64_t)parts[i].index,
				    parts[i].name, parts[i].first, parts[i].last, mb);
			}
		}

		{
			uint64_t first_usable = *(const uint64_t *)(header + 40);
			uint64_t last_usable = *(const uint64_t *)(header + 48);
			uint64_t prev_end = first_usable;
			uint64_t best_start = 0, best_end = 0, best = 0;

			for (uint32_t i = 0; i < n; i++) {
				if (parts[i].first > prev_end) {
					uint64_t bytes = (parts[i].first - prev_end) * bs;

					if (bytes > best) {
						best = bytes;
						best_start = prev_end;
						best_end = parts[i].first - 1;
					}
				}
				if (parts[i].last + 1 > prev_end) {
					prev_end = parts[i].last + 1;
				}
			}
			if (last_usable + 1 > prev_end) {
				uint64_t bytes = (last_usable + 1 - prev_end) * bs;

				if (bytes > best) {
					best = bytes;
					best_start = prev_end;
					best_end = last_usable;
				}
			}
			print("ufs: largest gap: lba %x..%x, %d MB\n", best_start, best_end, best >> 20);
		}

		if (have_super) {
			ufs_analyze_super (bio, super_first, super_last);
		}
	}
}

/*
 * The block device and LBA range of a GPT partition, by name: the system
 * image is flashed at the start of "userdata" (the partition this port gives
 * up), and run_kernel() reads it from there through the same BlockIo the
 * survey uses. Read only.
 */
static efi_block_io *
ufs_find_partition(const char *name, uint64_t *first_lba, uint64_t *blocks)
{
	static const efi_guid blk_guid = EFI_BLOCK_IO_GUID;
	efi_handle *handles;
	uint64_t count;

	if (EFI_ERROR(BS->locate_handle_buffer(ByProtocol, &blk_guid, NULL, &count, &handles))) {
		return NULL;
	}
	for (uint64_t i = 0; i < count; i++) {
		efi_block_io *bio;
		uint64_t bs, entries_lba, n, esz, bytes, read;
		uint32_t hsize;
		static uint8_t hdr[4096];

		if (EFI_ERROR(BS->handle_protocol(handles[i], &blk_guid, (void **)&bio)) || bio->media->logical ||
		    bio->media->block_size < 512 || bio->media->block_size > sizeof(hdr) ||
		    bio->media->last_block < 2) {
			continue;
		}
		bs = bio->media->block_size;
		if (EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, 1, bs, hdr)) ||
		    memcmp(hdr, "EFI PART", 8) != 0) {
			continue;
		}
		hsize = *(uint32_t *)(hdr + 12);
		entries_lba = *(uint64_t *)(hdr + 72);
		n = *(uint32_t *)(hdr + 80);
		esz = *(uint32_t *)(hdr + 84);
		bytes = n * esz;
		if (hsize < 92 || hsize > bs || esz < 128 || bytes == 0 || bytes > sizeof(ufs_buffer)) {
			continue;
		}
		read = (bytes + bs - 1) / bs * bs;
		if (EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, entries_lba, read, ufs_buffer))) {
			continue;
		}
		for (uint64_t e = 0; e < n; e++) {
			const uint8_t *ent = ufs_buffer + e * esz;
			char pname[37];
			int used = 0, k;

			for (k = 0; k < 16; k++) {
				used |= ent[k];
			}
			if (used == 0) {
				continue;
			}
			for (k = 0; k < 36; k++) {
				uint16_t c = (uint16_t)ent[56 + 2 * k] | ((uint16_t)ent[56 + 2 * k + 1] << 8);

				if (c == 0) {
					break;
				}
				pname[k] = c < 0x80 ? (char)c : '?';
			}
			pname[k] = 0;
			if (str_eq(pname, name)) {
				*first_lba = *(const uint64_t *)(ent + 32);
				*blocks = *(const uint64_t *)(ent + 40) - *first_lba + 1;
				return bio;
			}
		}
	}
	return NULL;
}

/* one line per 32 bytes: "ufs: PART WHAT +OFFSET: hex" */
static void
ufs_dump_of(const char *part, const char *what, const uint8_t *p, uint64_t n)
{
	for (uint64_t at = 0; at < n; at += 32) {
		char line[72];
		unsigned k = 0;

		for (uint64_t i = at; i < n && i < at + 32; i++) {
			line[k++] = "0123456789abcdef"[p[i] >> 4];
			line[k++] = "0123456789abcdef"[p[i] & 15];
		}
		line[k] = 0;
		print("ufs: %s %s +%x: %s\n", part, what, at, line);
	}
}

static void
ufs_dump(const char *what, const uint8_t *p, uint64_t n)
{
	ufs_dump_of("super", what, p, n);
}

/*
 * The start of userdata: where an f2fs (or ext4) of Android's would have its superblock, at 1024
 * and, for f2fs, its copy at 4096 + 1024. Plain text there says the filesystem itself lies on the
 * flash as it is; anything else says it lies under an encryption of the whole partition
 * (Android's metadata encryption, dm-default-key), and only Android can see into it.
 */
static void
ufs_dump_userdata(efi_block_io *bio)
{
	uint64_t bs = bio->media->block_size, want = 8192;

	if (bs == 0 || want % bs || EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, 0, want, ufs_buffer))) {
		print("ufs: userdata: its start could not be read\n");
		return;
	}
	ufs_dump_of("userdata", "sb", ufs_buffer + 1024, 1024);
	ufs_dump_of("userdata", "sb2", ufs_buffer + 4096 + 1024, 64);
}

/*
 * Android's own system (system, vendor, product, ...) is not in GPT partitions but in logical ones
 * inside "super", which liblp's metadata at its start describes: a geometry at 4096 (and its copy
 * at 8192), then its metadata slots from 12288 on -- each a header and its tables of partitions,
 * extents, groups and block devices. Printed raw for tools/ufs-super.py, which checks their SHA-256 sums and
 * says where in super nothing lies: a place a volume of this port's own could have without
 * anything of Android's being moved.
 */
static void
ufs_dump_super(efi_block_io *bio)
{
	uint64_t bs = bio->media->block_size, want = 256 * 1024;
	const uint8_t *geometry = ufs_buffer + 4096;
	uint32_t max_size, slots;

	if (bs == 0 || want % bs || (bio->media->last_block + 1) * bs < want ||
	    EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, 0, want, ufs_buffer))) {
		print("ufs: super: its start could not be read\n");
		return;
	}
	if (*(const uint32_t *)geometry != 0x616c4467) {
		print("ufs: super: no liblp geometry (magic %x)\n", (uint64_t)*(const uint32_t *)geometry);
		return;
	}
	ufs_dump("geometry", geometry, 52);
	max_size = *(const uint32_t *)(geometry + 40);
	slots = *(const uint32_t *)(geometry + 44);
	/* a slot per A/B slot: the first describes super as slot _a sees it, the second as _b does */
	for (uint32_t slot = 0; slot < slots && slot < 2; slot++) {
		const uint8_t *header = ufs_buffer + 3 * 4096 + (uint64_t)slot * max_size;
		uint32_t header_size, tables_size;
		char what[8] = "header0", tables[8] = "tables0";

		if (3 * 4096 + (uint64_t)(slot + 1) * max_size > want || *(const uint32_t *)header != 0x414c5030) {
			print("ufs: super: slot %d: no metadata header within the first %d KB\n", (uint64_t)slot, want >> 10);
			continue;
		}
		header_size = *(const uint32_t *)(header + 8);
		tables_size = *(const uint32_t *)(header + 44);
		if (header_size < 128 || header_size > 256 || tables_size > max_size - header_size || tables_size > 16384) {
			print("ufs: super: slot %d: header of %d bytes, tables of %d: not dumped\n", (uint64_t)slot,
			    (uint64_t)header_size, (uint64_t)tables_size);
			continue;
		}
		what[6] = tables[6] = (char)('0' + slot);
		ufs_dump(what, header, header_size);
		ufs_dump(tables, header + header_size, tables_size);
	}
}

static void
ufs_survey(void)
{
	static const efi_guid part_guid = EFI_PARTITION_INFO_GUID;
	static const efi_guid blk_guid = EFI_BLOCK_IO_GUID;
	efi_handle *handles;
	uint64_t count, units = 0, partitions = 0;

	/*
	 * What the UEFI storage stack left behind, before any block device is looked at:
	 * the controller's registers as the last driver wrote them, and which of the UFS
	 * drivers made it. A survey that finds no BlockIo otherwise says nothing about why.
	 * The addresses are UFSHCI: CAP, VER, IS, IE, HCS, HCE, UECPA.
	 */
	{
		volatile uint32_t *hci = (volatile uint32_t *)(uintptr_t)0x112B0000;
		static const efi_guid hc_guid = { 0xebc01af5, 0x7a9, 0x489e,
			{ 0xb7, 0xce, 0xdc, 0x08, 0x9e, 0x45, 0x9b, 0x2f } };
		static const efi_guid cfg_guid = { 0xb81bfab0, 0x0eb3, 0x4cf9,
			{ 0x84, 0x65, 0x7f, 0xa9, 0x86, 0x36, 0x16, 0x64 } };
		static const efi_guid scsi_guid = { 0x143b7632, 0xb81b, 0x4cb7,
			{ 0xab, 0xd3, 0xb6, 0x25, 0xa5, 0xb9, 0xbf, 0xfe } };
		void *iface;

		print("ufs: hci CAP=%x VER=%x IS=%x IE=%x HCS=%x HCE=%x UECPA=%x\n",
		    (uint64_t)hci[0x00 / 4], (uint64_t)hci[0x08 / 4], (uint64_t)hci[0x20 / 4],
		    (uint64_t)hci[0x24 / 4], (uint64_t)hci[0x30 / 4], (uint64_t)hci[0x34 / 4],
		    (uint64_t)hci[0x38 / 4]);
		print("ufs: protocols: hc %s, device config %s, scsi pass-thru %s\n",
		    !EFI_ERROR(BS->locate_protocol(&hc_guid, NULL, &iface)) ? "yes" : "no",
		    !EFI_ERROR(BS->locate_protocol(&cfg_guid, NULL, &iface)) ? "yes" : "no",
		    !EFI_ERROR(BS->locate_protocol(&scsi_guid, NULL, &iface)) ? "yes" : "no");
	}

	/* the raw logical units: the block devices that are not partitions of another */
	if (!EFI_ERROR(BS->locate_handle_buffer(ByProtocol, &blk_guid, NULL, &count, &handles))) {
		for (uint64_t i = 0; i < count; i++) {
			efi_block_io *bio;

			if (EFI_ERROR(BS->handle_protocol(handles[i], &blk_guid, (void **)&bio)) || bio->media->logical) {
				continue;
			}
			print("ufs: unit %d: media %d, %d blocks of %d (%d MB), %s, align %d\n", units++,
			    (uint64_t)bio->media->media_id, bio->media->last_block + 1, (uint64_t)bio->media->block_size,
			    (bio->media->last_block + 1) * bio->media->block_size >> 20,
			    bio->media->read_only ? "read only" : "writable", (uint64_t)bio->media->io_align);
			ufs_check_gpt(bio, units - 1);
		}
	}
	/* the GPT partitions, with the hash of those there are images of */
	if (EFI_ERROR(BS->locate_handle_buffer(ByProtocol, &part_guid, NULL, &count, &handles))) {
		print("ufs: no partition information in this UEFI\n");
		return;
	}
	for (uint64_t i = 0; i < count; i++) {
		efi_partition_info *info;
		efi_block_io *bio;
		char name[40];
		int r;

		if (EFI_ERROR(BS->handle_protocol(handles[i], &part_guid, (void **)&info)) || info->type != 2 ||
		    EFI_ERROR(BS->handle_protocol(handles[i], &blk_guid, (void **)&bio))) {
			continue;
		}
		ufs_name(info, name, sizeof(name));
		partitions++;
		print("ufs: part %s: lba %d..%d, %d KB\n", name, info->start_lba, info->end_lba,
		    (bio->media->last_block + 1) * bio->media->block_size >> 10);
		if ((r = ufs_reference_of(name)) >= 0) {
			ufs_hash_partition(bio, name, ufs_references[r].bytes);
		}
		if (name[0] == 's' && name[1] == 'u' && name[2] == 'p' && name[3] == 'e' && name[4] == 'r' && name[5] == 0) {
			ufs_dump_super(bio);
		}
		if (name[0] == 'u' && name[1] == 's' && name[2] == 'e' && name[3] == 'r' && name[4] == 'd' &&
		    name[5] == 'a' && name[6] == 't' && name[7] == 'a' && name[8] == 0) {
			ufs_dump_userdata(bio);
		}
	}
	print("ufs: %d raw units, %d partitions\n", units, partitions);
}

/* ------------------------------------------------------------------------ */
/* UFS block service (ufs=2): the kernel reads the phone's storage through  */
/* this loader, and this loader through Qualcomm's own UFS driver           */

/*
 * The kernel has no driver for the phone's storage, and does not need one: UEFI never exits here,
 * Qualcomm's UFS driver (UFSDxe) has the controller, its PHY, clocks and power up and stays
 * resident, and this loader already serves the kernel from core 0 while the kernel runs on another
 * (the battery). So the kernel asks for blocks through a page both can see, and core 0 reads them
 * with that driver's ReadBlocks into a buffer both can see. The kernel's side is
 * bsd/dev/redwood_ufs.c; it gets the page's address as ufs_shared_pa= on its command line.
 *
 * Reads, and -- with ufs_write=1 on the command line -- writes into one partition and nowhere
 * else: the port's own darwin, proved by its GPT entry (name, both GUIDs, first and last LBA, its
 * logical unit), and in it only past everything the build writes from the computer, so that no
 * answer to the kernel can reach Android's partitions, the iOS volume or the cryptexes. The
 * refusals are here, in the kernel (bsd/dev/redwood_ufs.c) and in UEFI's own driver, which gives
 * out a partition's BlockIo and bounds it: a request has to pass all three.
 *
 * Each side writes its own cache lines only: the kernel the request, core 0 the answer (and the
 * table, once, before the kernel starts). A line one side cleans out of its cache therefore never
 * carries a stale copy of what the other side wrote into it. Into the data buffer core 0 writes
 * only what it has read back after a write of its own, so after the controller's DMA there is
 * nothing of its own in its cache to write back over the data; the kernel, which fills the buffer
 * for a write, cleans its own lines of it before it asks.
 */
#define BLOCK_MAGIC        0x4b434f4c42574452ULL       /* "RDWBLOCK" */
#define BLOCK_VERSION      3
#define BLOCK_MAX_PARTS    160
#define BLOCK_MAX_UNITS    16
#define BLOCK_PART_UNIT    1u                          /* the entry is a whole logical unit, not a partition */
#define BLOCK_OP_READ      0u
#define BLOCK_OP_WRITE     1u

/*
 * The one partition a write may reach, and from which of its blocks. darwin is the port's own
 * 20 GiB at the end of logical unit 0 (README, "The port's partition"); what the build puts there
 * from the computer (tools/darwin-write.py) is the iOS volume at its start and the two cryptexes
 * behind it, and nothing of this port reads or writes the rest -- so the data of iOS lives there
 * and a write is refused before that block. The identity is the whole of darwin-write.py's: the
 * same partition, named the same, of the same size, in the same place, on logical unit 0.
 */
#define BLOCK_WRITE_FIRST  2042368ULL                  /* darwin's blocks of 4096: past both cryptexes */
#define BLOCK_DARWIN_FIRST 25374720ULL                 /* its first and last LBA of unit 0, as the GPT has them */
#define BLOCK_DARWIN_LAST  30617594ULL
#define BLOCK_DARWIN_TYPE  { 0x7c3457ef, 0x0000, 0x11aa, { 0xaa, 0x11, 0x00, 0x30, 0x65, 0x43, 0xec, 0xac } }
#define BLOCK_DARWIN_UNIQ  { 0xfd6854ad, 0x24aa, 0x4fc3, { 0x94, 0xfe, 0x29, 0x01, 0x16, 0x85, 0x8d, 0x68 } }

/*
 * The partitions first, then the logical units they are on (BLOCK_PART_UNIT, named unit0, unit1,
 * ... in the order UEFI lists them). Each partition says which of those it is on and where it
 * begins there, so that a reader of the units themselves -- the kernel's own UFS driver -- finds
 * it; a unit says its logical unit number if its device path does.
 */
struct loader_block_part {
	char name[36];
	uint32_t block_size;
	uint64_t blocks;
	uint64_t start_lba;            /* where it begins on its unit, in the unit's blocks (0 for a unit) */
	uint16_t unit;                 /* the unit it is on, its number among the units; 0xffff: not known */
	uint8_t lun;                   /* a unit's logical unit number as its device path says; 0xff: it does not */
	uint8_t flags;                 /* BLOCK_PART_UNIT */
	uint32_t reserved;
};

struct loader_block {
	/* written by the loader, once, before the kernel starts */
	uint64_t magic;
	uint32_t version, size;
	uint32_t parts, buffer_size;
	uint64_t buffer_pa;
	/*
	 * Which partition takes writes this run, as its index among part[] plus one (0: none), and
	 * from which of its blocks. They are here, in what was padding before ask, so that the page
	 * stays the size and the version it was: one phone is shared between working copies, and a
	 * kernel built before writes existed must go on reading through a loader built after them,
	 * and the other way about -- a kernel that does not know these fields leaves ask.op zero,
	 * which is a read, and a loader that does not know them leaves these zero, which is no write.
	 */
	uint32_t write_part_plus_one;
	uint32_t write_reserved;
	uint64_t write_first;
	/* written by the kernel: what it wants, then request is advanced */
	struct {
		volatile uint32_t request;
		uint32_t part;
		uint64_t lba, count;           /* in the partition's own blocks */
		uint32_t op;                   /* BLOCK_OP_READ, BLOCK_OP_WRITE */
		uint32_t reserved;
	} ask __attribute__((aligned(128)));
	/* written by the loader: answered becomes request when the data is in the buffer */
	struct {
		volatile uint32_t answered;
		uint32_t reserved;
		int64_t status;                /* the EFI status of the read, 0 when it went well */
		uint64_t served, failed, bytes, ticks;
	} answer __attribute__((aligned(128)));
	struct loader_block_part part[BLOCK_MAX_PARTS] __attribute__((aligned(128)));
	/*
	 * Written by the loader before the kernel starts, with ufs_native= on the command line: where
	 * the kernel may put a transfer request list of its own into the UFS host controller for the
	 * run (hc_area, below), and UEFI's, which the loader puts back. hc_pa 0: it may not.
	 */
	struct {
		uint64_t hc_pa;                /* the controller's registers */
		uint64_t area_pa;              /* the list (1 KB, at the start) and command descriptors */
		uint32_t area_size, ucd_offset, ucd_size, slots;
		uint32_t uefi_utrlba, uefi_utrlbau;
	} native __attribute__((aligned(128)));
	/* written by the loader during a run: it takes the controller back (a hung kernel); send nothing more */
	struct {
		volatile uint32_t take_back;
	} loader_native __attribute__((aligned(128)));
	/* written by the kernel: its list is in the controller (for the loader's log) */
	struct {
		volatile uint32_t list_in;
		uint32_t switched_in, switched_out;
		volatile uint32_t cnr_at_switch;       /* UTRLCNR when the kernel's list went in */
	} kernel_native __attribute__((aligned(128)));
};

_Static_assert(__builtin_offsetof(struct loader_block, ask) == 128,
    "the page must stay the size it was: the fields before ask have to fit in what was padding");

/* (8 KB is as far as this target aligns; the kernel maps whole 16 KB pages around both) */
static struct loader_block block_shared __attribute__((aligned(0x2000)));
static void block_io2_probe(efi_handle h, efi_block_io *bio);
static int block_probe_requested;       /* ufs_probe=1: block_io2_probe() at block_start() */
static efi_block_io *block_bios[BLOCK_MAX_PARTS];
static int block_enabled;
static int block_write_requested;       /* ufs_write=1 on the command line */
static int block_write_part = -1;       /* the only partition a write may reach; -1: none, writes refused */
static uint64_t block_writes, block_writes_refused, block_write_bytes;

/* the bytes of a device path before its end node */
static uint64_t
device_path_bytes(const efi_device_path *dp)
{
	const uint8_t *p = (const uint8_t *)dp;
	uint64_t n = 0;

	for (int nodes = 0; nodes < 64; nodes++) {
		uint64_t len = p[n + 2] | (uint64_t)p[n + 3] << 8;

		if (p[n] == 0x7f || len < 4) {
			break;
		}
		n += len;
	}
	return n;
}

/*
 * A unit's device path, a node at a time ("ufs: unit N: path TYPE.SUBTYPE[data] ..."), and its
 * logical unit number if a UFS node (messaging, subtype 0x19: target, then LUN) says it.
 */
static uint8_t
device_path_print(uint64_t unit, const efi_device_path *dp)
{
	const uint8_t *p = (const uint8_t *)dp;
	uint64_t n = 0, total = device_path_bytes(dp);
	uint8_t lun = 0xff;

	print("ufs: unit %d: path", unit);
	while (n < total) {
		uint64_t len = p[n + 2] | (uint64_t)p[n + 3] << 8;

		print(" %x.%x[", (uint64_t)p[n], (uint64_t)p[n + 1]);
		for (uint64_t i = 4; i < len && i < 4 + 24; i++) {
			print("%s%x", (uint64_t)p[n + i] < 16 ? "0" : "", (uint64_t)p[n + i]);
		}
		print("%s]", len > 4 + 24 ? "..." : "");
		if (p[n] == 3 && p[n + 1] == 0x19 && len >= 6) {
			lun = p[n + 5];
		}
		n += len;
	}
	print(lun == 0xff ? "\n" : " (LUN %d)\n", (uint64_t)lun);
	return lun;
}

/*
 * The UFS host controller, for the kernel's own driver (ufs_native= on the command line; without it
 * this loader never touches the controller's registers). The kernel may, for the length of a run,
 * stop the controller's transfer request list, point it at a list of its own in hc_area (memory of
 * this loader, so that putting UEFI's back never depends on the kernel's memory), and start it
 * again; UEFI's list is one slot and its command descriptor, with no room for another request.
 * This loader keeps UEFI's list address (UTRLBA/UTRLBAU) from before the first run and checks it,
 * and puts it back if need be, on every way back from a run (hc_take_back) before anything here
 * touches the storage; it reads for the kernel (block_poll) and writes the log (write_logs) only
 * while UEFI's list is the one in the controller.
 */
#define HC_PA              0x1d84000ULL        /* ufshc@1d84000, "ufs_mem", in this phone's Android device tree */
#define HC_CAP             0x00
#define HC_VER             0x08
#define HC_IS              0x20
#define HC_IE              0x24
#define HC_HCS             0x30
#define HC_HCE             0x34
#define HC_UTRLBA          0x50
#define HC_UTRLBAU         0x54
#define HC_UTRLDBR         0x58
#define HC_UTRLCLR         0x5c
#define HC_UTRLRSR         0x60
#define HC_UTRLCNR         0x64
#define HC_UTMRLDBR        0x78
#define HC_SLOTS           32
#define HC_UCD_OFFSET      0x1000
#define HC_UCD_SIZE        0x800
#define HC_AREA_SIZE       (HC_UCD_OFFSET + HC_SLOTS * HC_UCD_SIZE)

static uint8_t hc_area[HC_AREA_SIZE] __attribute__((aligned(0x2000)));
static int hc_requested;                /* ufs_native= on the command line */
static int hc_known;                    /* UEFI's list address is kept here: check it, put it back */
static uint32_t hc_uefi_lo, hc_uefi_hi;
static int hc_refused_reads;

static inline uint32_t
hc_rd(uint32_t off)
{
	return *(volatile uint32_t *)(uintptr_t)(HC_PA + off);
}

static inline void
hc_wr(uint32_t off, uint32_t v)
{
	__asm__ volatile ("dsb sy" ::: "memory");
	*(volatile uint32_t *)(uintptr_t)(HC_PA + off) = v;
	__asm__ volatile ("dsb sy" ::: "memory");
}

static uint64_t
hc_ms_since(uint64_t then)
{
	return (READ_SYSREG(CNTVCT_EL0) - then) * 1000 / READ_SYSREG(CNTFRQ_EL0);
}

/* UEFI's list in, and running: what UEFI's driver needs to read or write */
static int
hc_list_is_uefis(void)
{
	return !hc_known || (hc_rd(HC_UTRLBA) == hc_uefi_lo && hc_rd(HC_UTRLBAU) == hc_uefi_hi &&
	       (hc_rd(HC_UTRLRSR) & 1) != 0);
}

static void
hc_print_state(const char *when)
{
	print("ufs: %s: list %x:%x (UEFI's %x:%x), run %x, doorbell %x, HCS %x, IS %x, IE %x, completion %x, "
	    "task doorbell %x\n", when, (uint64_t)hc_rd(HC_UTRLBAU), (uint64_t)hc_rd(HC_UTRLBA), (uint64_t)hc_uefi_hi,
	    (uint64_t)hc_uefi_lo, (uint64_t)hc_rd(HC_UTRLRSR), (uint64_t)hc_rd(HC_UTRLDBR), (uint64_t)hc_rd(HC_HCS),
	    (uint64_t)hc_rd(HC_IS), (uint64_t)hc_rd(HC_IE), (uint64_t)hc_rd(HC_UTRLCNR), (uint64_t)hc_rd(HC_UTMRLDBR));
}

/*
 * Whatever the kernel left: UEFI's list back in the controller. The kernel is told to send nothing
 * more (it looks before every doorbell, with interrupts off), given 50 ms, then what is in flight
 * is waited for (1 s), cleared if it does not finish (UTRLCLR: every slot of that list is the
 * kernel's), the list stopped, UEFI's address written back, the list started, all read back.
 */
static void
hc_take_back(const char *when)
{
	uint32_t lo, hi, rsr, db;
	uint64_t t;

	if (!hc_known) {
		return;
	}
	lo = hc_rd(HC_UTRLBA);
	hi = hc_rd(HC_UTRLBAU);
	rsr = hc_rd(HC_UTRLRSR);
	db = hc_rd(HC_UTRLDBR);
	if (lo == hc_uefi_lo && hi == hc_uefi_hi && (rsr & 1)) {
		print("ufs: %s: UEFI's transfer list is in the controller (%x), running, doorbell %x\n", when, (uint64_t)lo,
		    (uint64_t)db);
		return;
	}
	print("ufs: %s: the controller has list %x:%x (run %x, doorbell %x), not UEFI's %x:%x: taking it back\n", when,
	    (uint64_t)hi, (uint64_t)lo, (uint64_t)rsr, (uint64_t)db, (uint64_t)hc_uefi_hi, (uint64_t)hc_uefi_lo);
	block_shared.loader_native.take_back = 1;
	clean_dcache((uint64_t)(uintptr_t)&block_shared.loader_native,
	    (uint64_t)(uintptr_t)&block_shared.loader_native + sizeof(block_shared.loader_native));
	for (t = READ_SYSREG(CNTVCT_EL0); hc_ms_since(t) < 50;) {
	}
	for (t = READ_SYSREG(CNTVCT_EL0); (db = hc_rd(HC_UTRLDBR)) != 0 && hc_ms_since(t) < 1000;) {
	}
	if (db != 0) {
		print("ufs: %s: doorbell %x still set after 1 s\n", when, (uint64_t)db);
		if (hc_rd(HC_UTRLBA) != hc_uefi_lo || hc_rd(HC_UTRLBAU) != hc_uefi_hi) {
			print("ufs: %s: clearing the kernel's slots (UTRLCLR)\n", when);
			hc_wr(HC_UTRLCLR, 0);
			for (t = READ_SYSREG(CNTVCT_EL0); (db = hc_rd(HC_UTRLDBR)) != 0 && hc_ms_since(t) < 1000;) {
			}
			print("ufs: %s: doorbell %x after the clear\n", when, (uint64_t)db);
		}
	}
	/* the completion notifications the kernel's requests left (it says what there was when its list went in) */
	flush_dcache((uint64_t)(uintptr_t)&block_shared.kernel_native,
	    (uint64_t)(uintptr_t)&block_shared.kernel_native + sizeof(block_shared.kernel_native));
	if (block_shared.kernel_native.switched_in != 0) {
		uint32_t cnr = hc_rd(HC_UTRLCNR), ours = cnr & ~block_shared.kernel_native.cnr_at_switch;

		if (ours != 0) {
			hc_wr(HC_UTRLCNR, ours);
		}
		print("ufs: %s: completion %x, at the kernel's switch %x: cleared %x, now %x\n", when, (uint64_t)cnr,
		    (uint64_t)block_shared.kernel_native.cnr_at_switch, (uint64_t)ours, (uint64_t)hc_rd(HC_UTRLCNR));
	}
	hc_wr(HC_UTRLRSR, 0);
	for (t = READ_SYSREG(CNTVCT_EL0); (hc_rd(HC_UTRLRSR) & 1) && hc_ms_since(t) < 100;) {
	}
	hc_wr(HC_UTRLBA, hc_uefi_lo);
	hc_wr(HC_UTRLBAU, hc_uefi_hi);
	hc_wr(HC_UTRLRSR, 1);
	for (t = READ_SYSREG(CNTVCT_EL0); hc_ms_since(t) < 50;) {
	}
	hc_print_state(when);
	print("ufs: %s: UEFI's list %s\n", when, hc_list_is_uefis() ? "put back" : "NOT PUT BACK: the storage is not used");
}

/*
 * Before a run (ufs_native=): what the controller looks like, and UEFI's list address kept -- the
 * first time; later it must be the same (or this loader's own area, which is then taken back).
 */
static int
hc_init(void)
{
	uint32_t lo, hi, area = (uint32_t)(uintptr_t)hc_area;

	if (!hc_requested) {
		return 0;
	}
	lo = hc_rd(HC_UTRLBA);
	hi = hc_rd(HC_UTRLBAU);
	print("ufs: controller at %x: CAP %x, VER %x, HCE %x, HCS %x, IS %x, IE %x, list %x:%x, run %x, doorbell %x\n",
	    HC_PA, (uint64_t)hc_rd(HC_CAP), (uint64_t)hc_rd(HC_VER), (uint64_t)hc_rd(HC_HCE), (uint64_t)hc_rd(HC_HCS),
	    (uint64_t)hc_rd(HC_IS), (uint64_t)hc_rd(HC_IE), (uint64_t)hi, (uint64_t)lo, (uint64_t)hc_rd(HC_UTRLRSR),
	    (uint64_t)hc_rd(HC_UTRLDBR));
	if (!hc_known) {
		if (hi == 0 && lo == area) {
			print("ufs: the controller has this loader's own area for its list before any run: left alone\n");
			return 0;
		}
		hc_uefi_lo = lo;
		hc_uefi_hi = hi;
		hc_known = 1;
		print("ufs: UEFI's transfer list is at %x:%x; it is put back after every run\n", (uint64_t)hi, (uint64_t)lo);
	} else if (lo != hc_uefi_lo || hi != hc_uefi_hi) {
		if (hi == 0 && lo == area) {
			hc_take_back("before the run");
		} else {
			print("ufs: UEFI's list moved from %x:%x to %x:%x: that is UEFI's now\n", (uint64_t)hc_uefi_hi,
			    (uint64_t)hc_uefi_lo, (uint64_t)hi, (uint64_t)lo);
			hc_uefi_lo = lo;
			hc_uefi_hi = hi;
		}
	}
	return hc_list_is_uefis();
}

/*
 * The firmware's configuration tables, by GUID (an ACPI or device tree table among them would say
 * where the storage controller is).
 */
static void
block_tables(void)
{
	for (uint64_t i = 0; ST->tables != NULL && i < ST->nr_tables && i < 32; i++) {
		const efi_guid *g = &ST->tables[i].guid;

		print("ufs: firmware table %d: %x-%x-%x-%x%x-%x%x%x%x%x%x at %x\n", i, (uint64_t)g->a, (uint64_t)g->b,
		    (uint64_t)g->c, (uint64_t)g->d[0], (uint64_t)g->d[1], (uint64_t)g->d[2], (uint64_t)g->d[3],
		    (uint64_t)g->d[4], (uint64_t)g->d[5], (uint64_t)g->d[6], (uint64_t)g->d[7],
		    (uint64_t)(uintptr_t)ST->tables[i].table);
	}
}

/*
 * Is this partition the one a write may reach? Everything about it has to be what it was when the
 * port was set up; one field out of place and nothing is written this run. The name UEFI reports
 * is already in bp->name (ufs_name), in ASCII.
 */
static int
block_is_darwin(const efi_partition_info *info, const efi_block_io *bio, const struct loader_block_part *bp)
{
	static const efi_guid type = BLOCK_DARWIN_TYPE, uniq = BLOCK_DARWIN_UNIQ;
	static const char name[] = "darwin";
	const char *why = NULL;

	for (unsigned i = 0; i < sizeof(name); i++) {
		if (bp->name[i] != name[i]) {
			return 0;               /* another partition: nothing to say about it */
		}
	}
	if (memcmp(&info->type_guid, &type, sizeof(type)) != 0) {
		why = "its type GUID is not the one it had";
	} else if (memcmp(&info->unique_guid, &uniq, sizeof(uniq)) != 0) {
		why = "its unique GUID is not the one it had";
	} else if (info->start_lba != BLOCK_DARWIN_FIRST || info->end_lba != BLOCK_DARWIN_LAST) {
		why = "it does not begin and end where it did";
	} else if (bp->unit != 0) {
		/* the first unit UEFI lists: this firmware's device paths say no logical unit number
		 * (device_path_print finds no 3.19 node), so bp->lun is 0xff for every unit */
		why = "it is not on the first logical unit";
	} else if (bp->block_size != 4096 || bp->blocks != BLOCK_DARWIN_LAST - BLOCK_DARWIN_FIRST + 1) {
		why = "its blocks are not what they were";
	} else if (bio->media->read_only) {
		why = "UEFI gives it out read only";
	}
	if (why != NULL) {
		print("ufs: darwin: no write will be served: %s\n", why);
		return 0;
	}
	print("ufs: darwin (LBA %d..%d of unit 0): its blocks from %d on may be written this run\n",
	    info->start_lba, info->end_lba, BLOCK_WRITE_FIRST);
	return 1;
}

static void
block_start(void)
{
	static const efi_guid part_guid = EFI_PARTITION_INFO_GUID;
	static const efi_guid blk_guid = EFI_BLOCK_IO_GUID;
	efi_handle *handles;
	uint64_t count;

	static const efi_guid dp_guid = EFI_DEVICE_PATH_GUID;
	static struct {
		efi_block_io *bio;
		const efi_device_path *path;
		uint64_t path_bytes;
		uint8_t lun;
	} units[BLOCK_MAX_UNITS];
	uint64_t nunits = 0;

	memset(&block_shared, 0, sizeof(block_shared));
	block_tables();
	/* the logical units: the block devices that are not partitions of another */
	if (!EFI_ERROR(BS->locate_handle_buffer(ByProtocol, &blk_guid, NULL, &count, &handles))) {
		for (uint64_t i = 0; i < count && nunits < BLOCK_MAX_UNITS; i++) {
			efi_block_io *bio;
			efi_device_path *dp;

			if (EFI_ERROR(BS->handle_protocol(handles[i], &blk_guid, (void **)&bio)) || bio->media->logical ||
			    bio->media->block_size == 0 || bio->media->block_size > BLOCK_BUFFER_SIZE ||
			    EFI_ERROR(BS->handle_protocol(handles[i], &dp_guid, (void **)&dp))) {
				continue;
			}
			units[nunits].bio = bio;
			units[nunits].path = dp;
			units[nunits].path_bytes = device_path_bytes(dp);
			units[nunits].lun = device_path_print(nunits, dp);
			nunits++;
		}
	}
	if (EFI_ERROR(BS->locate_handle_buffer(ByProtocol, &part_guid, NULL, &count, &handles))) {
		print("ufs: no partition information: the block service is off\n");
		return;
	}
	for (uint64_t i = 0; i < count && block_shared.parts + nunits < BLOCK_MAX_PARTS; i++) {
		struct loader_block_part *bp = &block_shared.part[block_shared.parts];
		efi_partition_info *info;
		efi_block_io *bio;
		efi_device_path *dp;

		if (EFI_ERROR(BS->handle_protocol(handles[i], &part_guid, (void **)&info)) || info->type != 2 ||
		    EFI_ERROR(BS->handle_protocol(handles[i], &blk_guid, (void **)&bio)) ||
		    bio->media->block_size == 0 || bio->media->block_size > BLOCK_BUFFER_SIZE) {
			continue;
		}
		ufs_name(info, bp->name, sizeof(bp->name));
		bp->block_size = bio->media->block_size;
		bp->blocks = bio->media->last_block + 1;
		bp->start_lba = info->start_lba;
		bp->unit = 0xffff;
		bp->lun = 0xff;
		/* its unit: the one whose device path its own begins with */
		if (!EFI_ERROR(BS->handle_protocol(handles[i], &dp_guid, (void **)&dp))) {
			uint64_t bytes = device_path_bytes(dp);

			for (uint64_t u = 0; u < nunits; u++) {
				if (units[u].path_bytes < bytes &&
				    memcmp(units[u].path, dp, units[u].path_bytes) == 0) {
					bp->unit = (uint16_t)u;
					bp->lun = units[u].lun;
				}
			}
		}
		if (block_write_requested && block_is_darwin(info, bio, bp)) {
			block_write_part = (int)block_shared.parts;
		}
		block_bios[block_shared.parts++] = bio;
		if (block_probe_requested && bp->name[0] == 'd' && bp->name[1] == 'a' && bp->name[2] == 'r' &&
		    bp->name[3] == 'w' && bp->name[4] == 'i' && bp->name[5] == 'n' && bp->name[6] == 0) {
			block_io2_probe(handles[i], bio);
		}
	}
	for (uint64_t u = 0; u < nunits; u++) {
		struct loader_block_part *bp = &block_shared.part[block_shared.parts];
		char *n = bp->name;

		n[0] = 'u', n[1] = 'n', n[2] = 'i', n[3] = 't';
		n[4] = (char)('0' + u / 10 % 10), n[5] = (char)('0' + u % 10), n[6] = 0;
		if (u < 10) {
			n[4] = n[5], n[5] = 0;
		}
		bp->block_size = units[u].bio->media->block_size;
		bp->blocks = units[u].bio->media->last_block + 1;
		bp->unit = (uint16_t)u;
		bp->lun = units[u].lun;
		bp->flags = BLOCK_PART_UNIT;
		block_bios[block_shared.parts++] = units[u].bio;
	}
	/* the kernel's own transfer list: this loader's area, if the controller is as UEFI keeps it */
	if (hc_known && hc_list_is_uefis() && hc_rd(HC_UTRLDBR) == 0 && (hc_rd(HC_HCE) & 1)) {
		memset(hc_area, 0, sizeof(hc_area));
		flush_dcache((uint64_t)(uintptr_t)hc_area, (uint64_t)(uintptr_t)hc_area + sizeof(hc_area));
		block_shared.native.hc_pa = HC_PA;
		block_shared.native.area_pa = (uint64_t)(uintptr_t)hc_area;
		block_shared.native.area_size = sizeof(hc_area);
		block_shared.native.ucd_offset = HC_UCD_OFFSET;
		block_shared.native.ucd_size = HC_UCD_SIZE;
		block_shared.native.slots = HC_SLOTS;
		block_shared.native.uefi_utrlba = hc_uefi_lo;
		block_shared.native.uefi_utrlbau = hc_uefi_hi;
		print("ufs: the kernel may put its own transfer list in, at %x (this loader's), for the run\n",
		    (uint64_t)(uintptr_t)hc_area);
	} else if (hc_requested) {
		print("ufs: the kernel's own transfer list is not offered: the controller is not as UEFI keeps it\n");
	}
	hc_refused_reads = 0;
	hc_log_skips = 0;
	/* per run, like the two above: this loader stays resident across runs, and a tally carried
	 * over from the run before is read as this one's */
	block_writes = block_writes_refused = block_write_bytes = 0;
	if (block_write_part >= 0) {
		block_shared.write_part_plus_one = (uint32_t)block_write_part + 1;
		block_shared.write_first = BLOCK_WRITE_FIRST;
	}
	block_shared.magic = BLOCK_MAGIC;
	block_shared.version = BLOCK_VERSION;
	block_shared.size = sizeof(block_shared);
	block_shared.buffer_size = BLOCK_BUFFER_SIZE;
	block_shared.buffer_pa = (uint64_t)(uintptr_t)block_buffer;
	clean_dcache((uint64_t)(uintptr_t)&block_shared, (uint64_t)(uintptr_t)&block_shared + sizeof(block_shared));
	block_enabled = 1;
	print("ufs: block service: %d partitions and %d units, page %x, buffer %x of %d KB\n",
	    (uint64_t)block_shared.parts - nunits, nunits, (uint64_t)(uintptr_t)&block_shared, block_shared.buffer_pa,
	    (uint64_t)(BLOCK_BUFFER_SIZE >> 10));
}

/*
 * Whether the storage could have more than one request in flight (ufs_probe=1): Block I/O 2
 * on the partitions, and whether its reads come back before they are done.  Eight 4 KB
 * reads at places 64 MB apart in "darwin", one after another through Block I/O and then all
 * eight at once through Block I/O 2, each into its own part of the buffer.  Before the kernel
 * runs (the UEFI timer still ticks), and only to say what there is.
 *
 * What it says on this phone: Block I/O 2 is there and the calls come back at once (eight in
 * 160 us, none done), but the eight are done only after 61.5 ms, against 1.0 ms one at a time
 * through Block I/O -- Qualcomm's driver finishes them from the UEFI timer, which besides does
 * not tick on core 0 while the kernel runs.  So one request at a time, synchronously.
 */
static void
block_io2_probe(efi_handle h, efi_block_io *bio)
{
	static const efi_guid blk2_guid = EFI_BLOCK_IO2_GUID;
	efi_status (EFIAPI *create_event)(uint32_t, uint64_t, void *, void *, void **) =
	    (efi_status (EFIAPI *)(uint32_t, uint64_t, void *, void *, void **))BS->create_event;
	efi_status (EFIAPI *check_event)(void *) = (efi_status (EFIAPI *)(void *))BS->check_event;
	static efi_block_io2_token tokens[8];
	efi_block_io2 *bio2 = NULL;
	uint64_t bs = bio->media->block_size, t0, t_sync, t_issue = 0, t_all, freq = READ_SYSREG(CNTFRQ_EL0);
	uint64_t returned_done = 0, pending, polls = 0;
	efi_status s;

	if (EFI_ERROR(BS->handle_protocol(h, &blk2_guid, (void **)&bio2)) || bio2 == NULL) {
		print("ufs: darwin: no Block I/O 2: one request at a time it is\n");
		return;
	}
	t0 = READ_SYSREG(CNTVCT_EL0);
	for (int i = 0; i < 8; i++) {
		s = bio->read_blocks(bio, bio->media->media_id, (uint64_t)i * (64ULL << 20) / bs + 7, bs,
		    block_buffer + i * 65536);
		if (EFI_ERROR(s)) {
			print("ufs: probe: Block I/O read failed %x\n", s);
			return;
		}
	}
	t_sync = READ_SYSREG(CNTVCT_EL0) - t0;
	for (int i = 0; i < 8; i++) {
		tokens[i].transaction_status = 0;
		if (EFI_ERROR(create_event(0, 8 /* TPL_CALLBACK */, NULL, NULL, &tokens[i].event))) {
			print("ufs: probe: no event\n");
			return;
		}
	}
	t0 = READ_SYSREG(CNTVCT_EL0);
	for (int i = 0; i < 8; i++) {
		/* other places than the synchronous reads, so that nothing the storage kept is read again */
		s = bio2->read_blocks_ex(bio2, bio2->media->media_id, (uint64_t)i * (64ULL << 20) / bs + 1031,
		    &tokens[i], bs, block_buffer + 1048576 + i * 65536);
		if (EFI_ERROR(s)) {
			print("ufs: probe: ReadBlocksEx %d failed %x\n", (uint64_t)i, s);
			return;
		}
		if (check_event(tokens[i].event) == 0) {
			returned_done++;        /* already signalled when the call came back */
		}
	}
	t_issue = READ_SYSREG(CNTVCT_EL0) - t0;
	pending = 8 - returned_done;
	while (pending > 0 && polls < 50000000) {
		pending = 0;
		for (int i = 0; i < 8; i++) {
			if (tokens[i].event != NULL && check_event(tokens[i].event) != 0) {
				pending++;
			} else if (tokens[i].event != NULL) {
				BS->close_event(tokens[i].event);
				tokens[i].event = NULL;
			}
		}
		polls++;
	}
	t_all = READ_SYSREG(CNTVCT_EL0) - t0;
	print("ufs: darwin: Block I/O 2 there. 8 random 4 KB reads: one at a time %d us; at once: the calls came back "
	    "after %d us (%d of them done by then), all done after %d us, %d still pending\n",
	    t_sync * 1000000 / freq, t_issue * 1000000 / freq, returned_done, t_all * 1000000 / freq, pending);
}

/* one request, if there is one: called from core 0's watch loop while the kernel runs */
static void
block_poll(void)
{
	uint64_t ask = (uint64_t)(uintptr_t)&block_shared.ask;
	uint32_t request, part, op;
	uint64_t lba, count, bytes, started;
	efi_status s = 0x8000000000000002ULL;     /* EFI_INVALID_PARAMETER: a request out of bounds */

	/* the kernel writes the request into memory past this core's cache: look at memory */
	flush_dcache(ask, ask + sizeof(block_shared.ask));
	request = block_shared.ask.request;
	if (request == block_shared.answer.answered) {
		return;
	}
	part = block_shared.ask.part;
	lba = block_shared.ask.lba;
	count = block_shared.ask.count;
	op = block_shared.ask.op;
	started = READ_SYSREG(CNTVCT_EL0);
	bytes = 0;
	if (part < block_shared.parts && count != 0 && count <= BLOCK_BUFFER_SIZE / block_shared.part[part].block_size &&
	    lba < block_shared.part[part].blocks && count <= block_shared.part[part].blocks - lba) {
		efi_block_io *bio = block_bios[part];

		bytes = count * block_shared.part[part].block_size;
		if (!hc_list_is_uefis()) {
			/* the kernel's own list is in: UEFI's driver must not ring now (the kernel should not ask) */
			if (hc_refused_reads++ < 4) {
				print("ufs: a read asked for while the kernel's own transfer list is in the controller: refused\n");
			}
			s = 0x800000000000000FULL;      /* EFI_ACCESS_DENIED */
			bytes = 0;
		} else if (op == BLOCK_OP_WRITE) {
			if (block_write_part < 0 || part != (uint32_t)block_write_part || lba < BLOCK_WRITE_FIRST) {
				/* not darwin, or not past what the build writes from the computer: never */
				if (block_writes_refused++ < 8) {
					print("ufs: a write of %d blocks from %d of %s: REFUSED\n", count, lba,
					    block_shared.part[part].name);
				}
				s = 0x800000000000000FULL;      /* EFI_ACCESS_DENIED */
				bytes = 0;
			} else {
				/*
				 * The kernel filled the buffer and cleaned its lines of it; drop whatever this
				 * core holds, write, and read back -- the answer says the blocks hold what the
				 * kernel gave, or the write is no good. The read back overwrites the buffer,
				 * which the kernel does not need: it has the data.
				 */
				uint32_t want;

				flush_dcache((uint64_t)(uintptr_t)block_buffer,
				    (uint64_t)(uintptr_t)block_buffer + bytes);
				want = ufs_crc32(block_buffer, bytes);
				s = bio->write_blocks(bio, bio->media->media_id, lba, bytes, block_buffer);
				if (!EFI_ERROR(s)) {
					bio->flush_blocks(bio);
					s = bio->read_blocks(bio, bio->media->media_id, lba, bytes, block_buffer);
					flush_dcache((uint64_t)(uintptr_t)block_buffer,
					    (uint64_t)(uintptr_t)block_buffer + bytes);
					if (!EFI_ERROR(s) && ufs_crc32(block_buffer, bytes) != want) {
						print("ufs: %d blocks from %d of darwin read back DIFFERENT\n",
						    count, lba);
						s = 0x800000000000000AULL;      /* EFI_VOLUME_CORRUPTED */
					}
				}
				if (!EFI_ERROR(s)) {
					block_writes++;
					block_write_bytes += bytes;
				}
			}
		} else if (op == BLOCK_OP_READ) {
			s = bio->read_blocks(bio, bio->media->media_id, lba, bytes, block_buffer);
			/* what the controller wrote is in memory; drop whatever this core held of the buffer */
			flush_dcache((uint64_t)(uintptr_t)block_buffer, (uint64_t)(uintptr_t)block_buffer + bytes);
		} else {
			bytes = 0;              /* an operation this loader does not know: nothing is touched */
		}
	}
	block_shared.answer.status = (int64_t)s;
	block_shared.answer.ticks += READ_SYSREG(CNTVCT_EL0) - started;
	if (EFI_ERROR(s)) {
		block_shared.answer.failed++;
	} else {
		block_shared.answer.served++;
		block_shared.answer.bytes += bytes;
	}
	__asm__ volatile ("dmb sy");
	block_shared.answer.answered = request;
	clean_dcache((uint64_t)(uintptr_t)&block_shared.answer,
	    (uint64_t)(uintptr_t)&block_shared.answer + sizeof(block_shared.answer));
}

static void
charger_start(void)
{
	static const efi_guid charger_ex_guid = QCOM_CHARGER_EX_GUID;
	static const efi_guid qcom_charger_guid = QCOM_CHARGER_GUID;
	efi_status ex_status, qcom_status, init_status = 0;

	if (charger_enabled || PLAT != &platform_redwood) {
		return;
	}
	ex_status = BS->locate_protocol(&charger_ex_guid, NULL, (void **)&CHARGER_EX);
	qcom_status = BS->locate_protocol(&qcom_charger_guid, NULL, (void **)&QCOM_CHARGER);
	if (!EFI_ERROR(qcom_status) && QCOM_CHARGER != NULL) {
		/* Re-open the driver's status path after QcomChargerApp handed off to the OS. */
		init_status = QCOM_CHARGER->initialize(1);
	}
	charger_enabled = (!EFI_ERROR(ex_status) && CHARGER_EX != NULL) ||
	    (!EFI_ERROR(qcom_status) && QCOM_CHARGER != NULL);
	print("battery: ChargerEx=%x QcomCharger=%x init=%x shared=%x\n", ex_status, qcom_status, init_status,
	    (uint64_t)(uintptr_t)&charger_shared);
	charger_poll();
	print("battery: flags=%x SOC=%d%% V=%d mV I=%d mA T=%d C action=%d\n", (uint64_t)charger_shared.flags,
	    (uint64_t)(int64_t)charger_shared.soc_percent, (uint64_t)(int64_t)charger_shared.voltage_mv,
	    (uint64_t)(int64_t)charger_shared.current_ma, (uint64_t)(int64_t)charger_shared.temperature_c,
	    (uint64_t)charger_shared.charger_action);
}

/* For the record: how much the kernel on the other core has logged so far, and the end of it. */
static void
note_kernel_progress(const struct kernel_live *live, uint64_t slide, uint64_t seconds)
{
	const char *log;
	uint32_t len, from;

	if (live == NULL) {
		print("%d s\n", seconds);
		return;
	}
	log = (const char *)(live->log + slide);
	/* its first words are written with the caches off: look at memory */
	flush_dcache(live->log_len + slide, live->log_len + slide + 4);
	len = *(volatile uint32_t *)(live->log_len + slide);
	if (len > live->log_head + live->log_ring) {
		len = 0;
	}
	from = len > 240 ? len - 240 : 0;
	flush_dcache((uint64_t)(uintptr_t)log + from, (uint64_t)(uintptr_t)log + len);
	print("%d s: the kernel has logged %d bytes, heartbeat %d; the last of it:\n", seconds, (uint64_t)len, live->heartbeat);
	for (uint32_t i = from; i < len; i++) {
		put_char(log[i] >= 0x20 && log[i] < 0x7f ? log[i] : log[i] == '\n' ? '\n' : '.');
	}
	print("\n");
}

/* A call of the firmware's power interface, the way this platform makes them. */
static int64_t
psci_call(uint64_t function, uint64_t a1, uint64_t a2, uint64_t a3)
{
	int64_t status;

	if (PLAT->psci_hvc) {
		register uint64_t x0 __asm__("x0") = function;
		register uint64_t x1 __asm__("x1") = a1;
		register uint64_t x2 __asm__("x2") = a2;
		register uint64_t x3 __asm__("x3") = a3;

		__asm__ volatile ("hvc #0" : "+r" (x0), "+r" (x1), "+r" (x2), "+r" (x3)
                        : : "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17");
		status = (int64_t)x0;
	} else {
		smc_x3 = a3;
		status = (int64_t)smc_call(function, a1, a2, NULL, NULL);
		smc_x3 = 0;
	}
	return status;
}

/*
 * Copy the last `cap` characters of loader_log, in order, into dst. The layout is the one
 * loader_return.c keeps: a linear first part and then a ring; once the ring has wrapped the
 * linear part is the oldest and the ring holds the newest 1 MB, oldest first from ring_at.
 */
static uint32_t
copy_log_stream(char *dst, uint32_t cap, const char *log, uint32_t len, uint32_t ring_at,
    uint32_t head, uint32_t ring, int wrapped)
{
	const char *seg[3];
	uint32_t segn[3];
	int ns = 0;
	uint32_t total = 0, skip, out = 0;

	if (ring_at > ring) {
		ring_at = ring;
	}
	if (!wrapped) {
		if (len > head + ring) {
			len = head + ring;
		}
		seg[0] = log;
		segn[0] = len;
		ns = 1;
	} else {
		seg[0] = log;
		segn[0] = head;
		seg[1] = log + head + ring_at;
		segn[1] = ring - ring_at;
		seg[2] = log + head;
		segn[2] = ring_at;
		ns = 3;
	}
	for (int i = 0; i < ns; i++) {
		total += segn[i];
	}
	skip = total > cap ? total - cap : 0;
	for (int i = 0; i < ns && out < cap; i++) {
		uint32_t n = segn[i];
		const char *p;

		if (skip >= n) {
			skip -= n;
			continue;
		}
		p = seg[i] + skip;
		n -= skip;
		skip = 0;
		if (n > cap - out) {
			n = cap - out;
		}
		memcpy(dst + out, p, n);
		out += n;
	}
	return out;
}

/*
 * Write the log into the next slot of userdata (see LOG_SLOT_*). Called on the monitor core
 * while the kernel runs on another: the storage is this loader's (the kernel has no driver
 * for this controller), and the firmware's Block I/O polls, so it needs no interrupts here.
 */
static void
save_log_slot(const struct kernel_live *live, uint64_t slide)
{
	efi_block_io *bio = (efi_block_io *)(uintptr_t)monitor_args.slot_bio;
	uint32_t bs = (uint32_t)monitor_args.slot_block_size;
	struct log_slot_header *h = (struct log_slot_header *)log_slot_buf;
	const char *log = (const char *)(uintptr_t)(live->log + slide);
	uint32_t len, ring_at, n, text_off;
	uint64_t slot, lba, freq = READ_SYSREG(CNTFRQ_EL0), blocks;
	efi_status s;
	int wrapped;

	if (bio == NULL || bs == 0 || bs > LOG_SLOT_HEADER) {
		log_slot_state = -1;
		return;
	}
	text_off = (LOG_SLOT_HEADER + bs - 1) / bs * bs;
	blocks = LOG_SLOT_SIZE / bs;
	len = *(volatile uint32_t *)(live->log_len + slide);
	ring_at = *(volatile uint32_t *)(live->log_ring_at + slide);
	wrapped = *(volatile uint8_t *)(live->log_wrapped + slide);
	n = copy_log_stream((char *)log_slot_buf + text_off, LOG_SLOT_SIZE - text_off, log, len, ring_at,
	    (uint32_t)live->log_head, (uint32_t)live->log_ring, wrapped);

	if (!hc_list_is_uefis()) {
		log_slot_state = -2;            /* the kernel's own transfer list is in the controller */
		return;
	}
	log_slot_seq++;
	memset(h, 0, sizeof(*h));
	h->magic = LOG_SLOT_MAGIC;
	h->version = 1;
	h->length = n;
	h->total = wrapped ? (uint64_t)(live->log_head + live->log_ring) : len;
	h->seq = log_slot_seq;
	if (freq >= 1000) {
		h->uptime_ms = READ_SYSREG(CNTVCT_EL0) / (freq / 1000);
	}
	h->crc = ufs_crc32((const uint8_t *)log_slot_buf + text_off, n);
	clean_dcache((uint64_t)(uintptr_t)log_slot_buf, (uint64_t)(uintptr_t)log_slot_buf + LOG_SLOT_SIZE);
	slot = log_slot_seq & 1;
	lba = monitor_args.slot_first + LOG_SLOT_OFFSET / bs + slot * blocks;
	s = bio->write_blocks(bio, bio->media->media_id, lba, LOG_SLOT_SIZE, log_slot_buf);
	if (!EFI_ERROR(s)) {
		bio->flush_blocks(bio);
		log_slot_state = 1;
	} else {
		log_slot_state = (int)(s & 0x7f);
	}
	log_slot_total = n;
}

/* Start the log monitor on its own core (see monitor_main above). */
extern char __ImageBase;

static void
monitor_start(const struct kernel_live *live, uint64_t slide, uint64_t probe)
{
	uint8_t *base = (uint8_t *)(uintptr_t)&__ImageBase;
	uint32_t pe_off, image_size;
	int64_t status;

	if (live == NULL) {
		print("monitor: the kernel has no loader_live; not started\n");
		return;
	}
	monitor_args.live = (uint64_t)(uintptr_t)live;
	monitor_args.slide = slide;
	monitor_args.ustacks_probe = probe;
	monitor_args.ttbr0 = READ_SYSREG(TTBR0_EL1);
	monitor_args.tcr = READ_SYSREG(TCR_EL1);
	monitor_args.mair = READ_SYSREG(MAIR_EL1);
	monitor_args.sctlr = READ_SYSREG(SCTLR_EL1);
	/* where the log can be kept: the free part of userdata (see LOG_SLOT_*) */
	{
		uint64_t first = 0, blocks = 0;
		efi_block_io *bio = ufs_find_partition("userdata", &first, &blocks);

		if (bio != NULL) {
			uint64_t bs = bio->media->block_size;
			uint64_t slot_blocks = bs != 0 ? LOG_SLOT_SIZE / bs : 0;

			if (bs != 0 && bs <= LOG_SLOT_HEADER && LOG_SLOT_SIZE % bs == 0 &&
			    LOG_SLOT_OFFSET / bs + 2 * slot_blocks <= blocks) {
				monitor_args.slot_bio = (uint64_t)(uintptr_t)bio;
				monitor_args.slot_first = first;
				monitor_args.slot_blocks = blocks;
				monitor_args.slot_block_size = bs;
				print("monitor: the log is saved %d MB into userdata\n", (uint64_t)(LOG_SLOT_OFFSET >> 20));
			} else {
				print("monitor: userdata has no room for the log slots\n");
			}
		}
	}
	pe_off = *(uint32_t *)(base + 0x3c);
	image_size = *(uint32_t *)(base + pe_off + 0x50);
	if (image_size == 0 || image_size > 0x1000000) {
		image_size = 0x800000;
	}
	/* that core starts with caches off: what it reads has to be in memory */
	clean_dcache((uint64_t)(uintptr_t)base, (uint64_t)(uintptr_t)base + image_size);
	clean_dcache((uint64_t)(uintptr_t)&monitor_args, (uint64_t)(uintptr_t)&monitor_args + sizeof(monitor_args));
	clean_dcache((uint64_t)(uintptr_t)monitor_stack, (uint64_t)(uintptr_t)monitor_stack + sizeof(monitor_stack));
	status = psci_call(PSCI_CPU_ON, MONITOR_MPIDR, (uint64_t)(uintptr_t)&monitor_entry, 0);
	print("monitor: core %x for the log, PSCI %d\n", MONITOR_MPIDR, (uint64_t)status);
}

/*
 * Run the kernel on the core with that MPIDR and wait until it is back. Returns 0 when it has
 * been and gone (the caller goes on as after loader_return_stub), a negative number if the
 * firmware refused to start the core, OTHER_CPU_NOT_STARTED, or OTHER_CPU_HUNG: then the kernel
 * is still sitting on that core, but what it logged is there to be read (loader_ctx, as after a
 * return). `live` is where the kernel shows its signs of life, if it has such a place;
 * `budget` is how many seconds it has said it will run.
 */
static int64_t
run_on_other_cpu(uint64_t mpidr, uint64_t entry, uint64_t boot_args_pa, const struct kernel_live *live, uint64_t slide,
    uint64_t budget)
{
	uint64_t daif = 0, group1 = 0, started, last_pet, last_battery, last_beat_at, last_beat = 0, noted = 0;
	uint64_t last_render = 0;
	uint32_t last_len = 0;
	int quiet = 0;
	int64_t status;
	int arrived = 0, watching_only = 0;

	running_live = live;
	running_slide = slide;
	other_cpu_start.entry = entry;
	other_cpu_start.boot_args = boot_args_pa;
	other_cpu_stage = 0;
	other_cpu_done = 0;
	psci_by_hvc = PLAT->psci_hvc;
	/* that core starts with its caches off: all it reads must be in memory, not in this core's cache */
	clean_dcache((uint64_t)(uintptr_t)&other_cpu_start, (uint64_t)(uintptr_t)&other_cpu_start + sizeof(other_cpu_start));
	clean_dcache((uint64_t)(uintptr_t)&other_cpu_stage, (uint64_t)(uintptr_t)&other_cpu_stage + 8);
	clean_dcache((uint64_t)(uintptr_t)&other_cpu_done, (uint64_t)(uintptr_t)&other_cpu_done + 8);
	clean_dcache((uint64_t)(uintptr_t)&psci_by_hvc, (uint64_t)(uintptr_t)&psci_by_hvc + 8);
	clean_dcache((uint64_t)(uintptr_t)&other_cpu_entry, (uint64_t)(uintptr_t)&other_cpu_entry + 0x1000);
	clean_dcache((uint64_t)(uintptr_t)loader_ctx, (uint64_t)(uintptr_t)loader_ctx + sizeof(loader_ctx));

	/* the last argument arrives in that core's x0 */
	status = psci_call(PSCI_CPU_ON, mpidr, (uint64_t)(uintptr_t)&other_cpu_entry, (uint64_t)(uintptr_t)&other_cpu_start);

	started = last_pet = last_battery = last_beat_at = READ_SYSREG(CNTVCT_EL0);
	print("core %x: the firmware answers %d to the request to start it\n", mpidr, (uint64_t)status);
	if (PLAT->log_other_cpu) {
		flush_log();
	}
	while (status == 0) {
		/*
		 * The first seconds are the ones in which a new arrangement goes wrong, and a machine
		 * that resets takes this loader's memory with it: where there is storage for the log,
		 * what the kernel is seen to do goes there as it happens. That needs UEFI's services,
		 * so until NOTE_SECONDS are over this core keeps its interrupts.
		 */
		if (!watching_only && seconds_since(started) >= noted + 2) {
			noted = seconds_since(started);
			if (PLAT->log_other_cpu) {
				if (!arrived) {
					print("%d s: the core has not arrived\n", noted);
				} else {
					note_kernel_progress(live, slide, noted);
				}
				flush_log();
			}
		}
		/*
		 * After that this core only watches: no interrupts (the kernel reprograms the interrupt
		 * controller's shared half; UEFI's handlers had better not run on top of that for long).
		 */
		if (!watching_only && seconds_since(started) >= NOTE_SECONDS) {
			watching_only = 1;
			daif = READ_SYSREG(DAIF);
			__asm__ volatile ("msr daifset, #0xf");
			group1 = READ_SYSREG(S3_0_C12_C12_7);          /* ICC_IGRPEN1_EL1 */
			__asm__ volatile ("msr S3_0_C12_C12_7, %0\nisb" : : "r" ((uint64_t)0));
		}
		/* both are written by a core with its caches off: look at memory, not at our copy */
		flush_dcache((uint64_t)(uintptr_t)&other_cpu_done, (uint64_t)(uintptr_t)&other_cpu_done + 8);
		if (other_cpu_done) {
			/* what the kernel returned, written the same way */
			flush_dcache((uint64_t)(uintptr_t)&loader_ctx[CTX_LOG_PA], (uint64_t)(uintptr_t)&loader_ctx[CTX_KSP + 1]);
			break;
		}
		if (!arrived) {
			flush_dcache((uint64_t)(uintptr_t)&other_cpu_stage, (uint64_t)(uintptr_t)&other_cpu_stage + 8);
			arrived = other_cpu_stage != 0;
			if (!arrived && seconds_since(started) >= START_SECONDS) {
				status = OTHER_CPU_NOT_STARTED;
			}
		}
		/*
		 * The watchdog is this core's to feed for as long as the kernel is expected to run:
		 * the kernel does it too, but whether that counts from another core is not known.
		 * After that a kernel that neither returns nor hangs visibly meets the watchdog.
		 */
		if (wdt_armed && seconds_since(last_pet) >= 5 && seconds_since(started) < budget + 60) {
			wdt_pet();
			last_pet = READ_SYSREG(CNTVCT_EL0);
		}
		/* Qualcomm's UEFI charger stack owns the PMIC/GLINK side; keep XNU's cache live. */
		if (charger_enabled && seconds_since(last_battery) >= 5 && hc_list_is_uefis()) {
			/* (not while the kernel's own transfer list is in: Qualcomm's DXEs are not to touch the storage) */
			charger_poll();
			last_battery = READ_SYSREG(CNTVCT_EL0);
		}
		if (arrived && live != NULL) {
			uint32_t llen = *(volatile uint32_t *)(live->log_len + slide);

			if (live->heartbeat != last_beat) {
				last_beat = live->heartbeat;
				last_beat_at = READ_SYSREG(CNTVCT_EL0);
#ifdef MALACHITE_STAGES
				/*
				 * A small square in the top-right corner changes colour with
				 * every heartbeat. The screen itself is the kernel's log.
				 */
				{
					static const uint32_t beat[4] = {
						0xFF0000FFu, 0xFF00FFFFu, 0xFFFFFF00u, 0xFFFF00FFu
					};

					stage_corner(beat[last_beat & 3], 1, 0, 40);
				}
#endif
			}
			/*
			 * The heartbeat is only fed when the loader armed the watchdog
			 * (a Qualcomm thing; not on this port), so the log growing is the
			 * sign of life that matters here: a kernel printing through the
			 * boot is alive even with loader_live.heartbeat stuck at zero.
			 */
			if (llen != last_len) {
				last_len = llen;
				last_beat_at = READ_SYSREG(CNTVCT_EL0);
				quiet = 0;
			} else if (seconds_since(last_beat_at) >= SILENCE_SECONDS) {
				/*
				 * Nothing printed for a while. That is not the same as dead (a
				 * system waiting on a service is quiet), so just mark it in the
				 * corner and keep watching: the marker goes away by itself when
				 * the log grows again.
				 */
				quiet = 1;
			}
			/*
			 * Put the tail of loader_log on the panel every two seconds: the
			 * boot log (and user space's /dev/console output) is visible while
			 * the kernel runs, without any help from it.
			 */
			if (seconds_since(last_render) >= 2) {
				last_render = READ_SYSREG(CNTVCT_EL0);
				render_kernel_log(live, slide);
				if (quiet) {
					stage_corner(0xFFFF0000u, 1, 1, 60);
				}
			}
		}
		if (block_enabled) {
			block_poll();
		}
		usb_poll_command();
		if (block_enabled) {
			/*
			 * The pause is spent looking at the kernel's mailbox: with one look a pass, a
			 * request waited 60-75 us on average before this core noticed it, more than a
			 * 4 KB ReadBlocks takes (27 us). Same length of pause as below.
			 */
			for (int k = 0; k < 64; k++) {
				block_poll();
				for (volatile int i = 0; i < 300; i++) {
				}
			}
		} else {
			for (volatile int i = 0; i < 20000; i++) {
			}
		}
	}
	running_live = NULL;

	if (watching_only) {
		__asm__ volatile ("msr S3_0_C12_C12_7, %0\nisb" : : "r" (group1));
		__asm__ volatile ("msr daif, %0" : : "r" (daif));
	}
	return status;
}

/* ------------------------------------------------------------------------ */
/* Hypervisor watchdog (Qualcomm "Haven" virtual watchdog, SMC interface as  */
/* used by Linux drivers/virt/haven/hh_virt_wdt.c). Armed for the whole stay */
/* in the loader and the kernel: any hang ends in a reset without a human.   */

#define VIRT_WDT_CONTROL   0x86000005u
#define VIRT_WDT_STATUS    0x86000006u
#define VIRT_WDT_PET       0x86000007u
#define VIRT_WDT_SET_TIME  0x86000008u
#define WDT_BITE_MS        30000u

static const struct platform *PLAT;
static int wdt_armed;

static uint64_t smc_x3;             /* the fourth argument register, for the one call that has one */

static uint64_t
smc_call(uint64_t id, uint64_t a1, uint64_t a2, uint64_t *r1, uint64_t *r2)
{
	register uint64_t x0 __asm__("x0") = id;
	register uint64_t x1 __asm__("x1") = a1;
	register uint64_t x2 __asm__("x2") = a2;
	register uint64_t x3 __asm__("x3") = smc_x3;

	__asm__ volatile ("smc #0" : "+r" (x0), "+r" (x1), "+r" (x2), "+r" (x3)
                : : "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17");
	if (r1 != NULL) {
		*r1 = x1;
	}
	if (r2 != NULL) {
		*r2 = x2;
	}
	return x0;
}

static void
wdt_pet(void)
{
	if (wdt_armed) {
		smc_call(VIRT_WDT_PET, 0, 0, NULL, NULL);
	}
}

/* Change the time to the bite, and start counting again. The hypervisor takes 16 bits of milliseconds. */
static void
wdt_set_ms(uint64_t ms)
{
	if (ms > 65000) {
		ms = 65000;
	}
	if (wdt_armed) {
		smc_call(VIRT_WDT_SET_TIME, ms, ms, NULL, NULL);
		smc_call(VIRT_WDT_PET, 0, 0, NULL, NULL);
	}
}

static void
wdt_arm(void)
{
	uint64_t ctl = 0, since = 0;

	if (PLAT != &platform_redwood) {
		return; /* SMC is not routed anywhere useful on QEMU virt */
	}
	uint64_t st = smc_call(VIRT_WDT_STATUS, 0, 0, &ctl, &since);
	uint64_t r_time = smc_call(VIRT_WDT_SET_TIME, WDT_BITE_MS, WDT_BITE_MS, NULL, NULL);
	uint64_t r_ctl = smc_call(VIRT_WDT_CONTROL, 3, 0, NULL, NULL);
	uint64_t r_pet = smc_call(VIRT_WDT_PET, 0, 0, NULL, NULL);
	print("watchdog: status ret=%x ctl=%x since_pet=%x; set_time=%x enable=%x pet=%x\n", st, ctl, since, r_time,
	    r_ctl, r_pet);
	wdt_armed = (r_pet == 0);
}

/* ------------------------------------------------------------------------ */
/* UEFI exception hook: put the fault into the log instead of on the screen  */

extern char __ImageBase;

static void publish_log(void);   /* defined with the payload below */

static void EFIAPI
exception_handler(int64_t type, uint64_t *ctx)
{
	print("\nUEFI EXCEPTION type=%d elr=%x esr=%x far=%x lr=%x sp=%x spsr=%x\n", (uint64_t)type, ctx[EXC_CTX_ELR],
	    ctx[EXC_CTX_ESR], ctx[EXC_CTX_FAR], ctx[EXC_CTX_LR], ctx[EXC_CTX_SP], ctx[EXC_CTX_SPSR]);
	print("loader image base %x (elr offset %x)\n", (uint64_t)(uintptr_t)&__ImageBase,
	    ctx[EXC_CTX_ELR] - (uint64_t)(uintptr_t)&__ImageBase);
	flush_log();
	/* Leave the log for the firmware of the next boot to print (DDR survives a PSCI
	 * reset), with a flag the firmware checks before starting anything. The cache is
	 * cleaned explicitly: dirty lines do not survive the reset on this hardware. */
	publish_log();
	*(volatile uint32_t *)(uintptr_t)(LOG_MBOX_BASE + LOG_MBOX_FLAG_OFF) = 1;
	flush_dcache(LOG_MBOX_BASE, LOG_MBOX_BASE + 0x80000);
	ST->rt->reset_system(0 /* EfiResetCold */, 0, 0, NULL);
	for (;;) {
	}
}

static void
install_exception_hook(void)
{
	static const efi_guid cpu_guid = EFI_CPU_ARCH_GUID;
	efi_cpu_arch *cpu;

	if (EFI_ERROR(BS->locate_protocol(&cpu_guid, NULL, (void **)&cpu))) {
		return;
	}
	for (int64_t type = 0; type <= 3; type += 3) { /* synchronous, SError */
		cpu->register_interrupt_handler(cpu, type, NULL);
		efi_status s = cpu->register_interrupt_handler(cpu, type, exception_handler);
		if (EFI_ERROR(s)) {
			print("exception hook %d: status %x\n", (uint64_t)type, s);
		}
	}
}

/* ------------------------------------------------------------------------ */
/* Payload                                                                  */

struct payload_info {
	const uint8_t *kernel;
	const uint8_t *ramdisk;
	uint32_t ramdisk_size;
	const char *cmdline;
	uint64_t checkpoint;
	uint64_t forced_base;
	uint64_t resident_rd;           /* size of a root image the host put at the resident address */
	int usb_mode;
	int hold;                       /* bring-up aid: stay on the log screen instead of resetting */
	int nokernel;                   /* bring-up aid: stop after the payload is read, never enter the kernel */
	int ret;                        /* bring-up aid: after the kernel path, return to the firmware */
};

static uint64_t
parse_number(const char *c, unsigned base)
{
	uint64_t v = 0;
	for (; *c; c++) {
		uint64_t d = (*c >= '0' && *c <= '9') ? (uint64_t)(*c - '0') : (*c >= 'a' && *c <= 'f') ? (uint64_t)(*c - 'a' + 10) : 16;
		if (d >= base) {
			break;
		}
		v = v * base + d;
	}
	return v;
}

static int
parse_payload(struct payload_info *pi, int verbose)
{
	struct payload_header *ph = (struct payload_header *)PAYLOAD_BASE;

	memset(pi, 0, sizeof(*pi));
	pi->cmdline = "";
	if (ph->magic != PAYLOAD_MAGIC) {
		print("no payload at %x (magic %x)\n", PAYLOAD_BASE, (uint64_t)ph->magic);
		return 0;
	}
	const uint8_t *p = (const uint8_t *)(ph + 1), *pend = p + ph->size;
	while (p + sizeof(struct payload_entry) <= pend) {
		const struct payload_entry *e = (const struct payload_entry *)p;
		const char *text = (const char *)(p + sizeof(*e));
		if (e->name[0] == 0) {
			break;
		}
		if (verbose) {
			print("payload entry '%s' size %x\n", e->name, (uint64_t)e->size);
		}
		if (str_eq(e->name, "ramdisk")) {
			pi->ramdisk = p + sizeof(*e);             /* becomes /dev/md0, the root device */
			pi->ramdisk_size = e->size;
		} else if (str_eq(e->name, "kernel")) {
			pi->kernel = p + sizeof(*e);
		} else if (str_eq(e->name, "cmdline")) {
			pi->cmdline = text;
		} else if (str_eq(e->name, "physbase")) {
			pi->forced_base = parse_number(text, 16); /* testing aid; must be free RAM */
		} else if (str_eq(e->name, "rdres")) {
			pi->resident_rd = parse_number(text, 16); /* e.g. loaded there by QEMU; see RESIDENT_RD_OFFSET */
		} else if (str_eq(e->name, "checkpoint")) {
			pi->checkpoint = parse_number(text, 10);  /* where the kernel should stop and come back */
		} else if (str_eq(e->name, "usb")) {
			pi->usb_mode = 1;                         /* stay in the loader and take commands over USB */
		} else if (str_eq(e->name, "hold")) {
			pi->hold = 1;                             /* bring-up: keep the log on screen, no reset */
		} else if (str_eq(e->name, "nokernel")) {
			pi->nokernel = 1;                         /* bring-up: stop after the payload is read */
		} else if (str_eq(e->name, "ret")) {
			pi->ret = 1;                              /* bring-up: return to the firmware after the run */
		}
		p += sizeof(*e) + ((e->size + 15) & ~15u);
	}
	return 1;
}

/* ------------------------------------------------------------------------ */
/* NVRAM image                                                              */
/*                                                                          */
/* iBoot hands the kernel a copy of the NVRAM contents in CHRP format       */
/* (iokit/Kernel/IONVRAMCHRPHandler.cpp). There is no NVRAM here, so build  */
/* an image with a valid header and one empty "common" partition.           */

static void
nvram_chrp_header(uint8_t *h, uint8_t sig, uint32_t bytes, const char *name)
{
	uint16_t blocks = (uint16_t)(bytes / 16), sum;

	memset(h, 0, 16);
	h[0] = sig;
	h[2] = (uint8_t)blocks;
	h[3] = (uint8_t)(blocks >> 8);
	memcpy(h + 4, name, str_len(name));
	/* checksum over signature, length and name, folded to 8 bits */
	sum = h[0];
	for (int i = 2; i < 16; i++) {
		sum += h[i];
	}
	while (sum > 0xff) {
		sum = (sum & 0xff) + (sum >> 8);
	}
	h[1] = (uint8_t)sum;
}

static void
build_nvram_image(uint8_t *image)
{
	uint32_t lo = 1, hi = 0, generation = 1;

	memset(image, 0, NVRAM_BANK_SIZE);
	nvram_chrp_header(image, 0x5a, 0x20, "nvram");                           /* Apple header: 32 bytes */
	nvram_chrp_header(image + 0x20, 0x70, NVRAM_BANK_SIZE - 0x20, "common"); /* the rest: common partition */
	memcpy(image + 20, &generation, 4);
	/* Adler-32 over everything after the checksum field itself */
	for (uint32_t i = 20; i < NVRAM_BANK_SIZE; i++) {
		lo = (lo + image[i]) % 65521;
		hi = (hi + lo) % 65521;
	}
	uint32_t adler = (hi << 16) | lo;
	memcpy(image + 16, &adler, 4);
}

/* ------------------------------------------------------------------------ */
/* Running the kernel                                                       */

static efi_gop *GOP;
/* The display handed to the kernel: the firmware's, or one we set up ourselves (QEMU). base 0 = none. */
static struct {
	uint64_t base;
	uint32_t width, height, stride;
} SCREEN;
static uint64_t win_base, win_size; /* XNU's physical memory window, claimed once */
static uint64_t resident_rd_size;   /* root image kept at win_base + RESIDENT_RD_OFFSET, 0 if none */
static char last_result[64] = "idle";

/*
 * Bring-up on a device with no USB link: the UEFI's text console may be missing
 * or unreadable, so the last stage reached is painted on the whole panel, the
 * way the UEFI port's SEC does it. Words are 0xAARRGGBB as the panel scans them
 * out (0xFFFF0000 is red).
 */
#define STAGE_BLUE     0xFF0000FFu      /* loader started, platform chosen */
#define STAGE_RED      0xFFFF0000u      /* no payload, or the kernel failed to start */
#define STAGE_CYAN     0xFF00FFFFu      /* payload read */
#define STAGE_MAGENTA  0xFFFF00FFu      /* entering the kernel (self test) */
#define STAGE_GREEN    0xFF00FF00u      /* run_kernel returned */
#define STAGE_YELLOW   0xFFFFFF00u      /* physical window claimed */
#define STAGE_LIME     0xFF80FF00u      /* kernel segments copied */
#define STAGE_ORANGE   0xFFFF8000u      /* kernel and ramdisk loaded */
#define STAGE_WHITE    0xFFFFFFFFu      /* about to jump to the kernel / return stub */

#ifdef MALACHITE_STAGES
static void
stage_paint(uint32_t argb)
{
	if (SCREEN.base == 0 || SCREEN.stride == 0 || SCREEN.height == 0) {
		return;
	}
	volatile uint32_t *p = (volatile uint32_t *)(uintptr_t)SCREEN.base;
	uint64_t n = (uint64_t)(SCREEN.stride / 4) * SCREEN.height;
	for (uint64_t i = 0; i < n; i++) {
		p[i] = argb;
	}
}

/* A square marker in a corner: a colour that survives whatever the kernel draws. */
static void
stage_corner(uint32_t argb, int right, int bottom, unsigned px)
{
	volatile uint32_t *p;
	uint64_t words, x0, y0;

	if (SCREEN.base == 0 || SCREEN.stride == 0 || SCREEN.height == 0) {
		return;
	}
	p = (volatile uint32_t *)(uintptr_t)SCREEN.base;
	words = SCREEN.stride / 4;
	x0 = right && words > px ? words - px : 0;
	y0 = bottom && SCREEN.height > px ? SCREEN.height - px : 0;
	for (uint64_t y = y0; y < y0 + px && y < SCREEN.height; y++) {
		for (uint64_t x = x0; x < x0 + px && x < words; x++) {
			p[y * words + x] = argb;
		}
	}
}
#else
#define stage_paint(c) do { } while (0)
#define stage_corner(c, r, b, p) do { } while (0)
#endif

/* ------------------------------------------------------------------------ */
/* A framebuffer text console of our own                                    */
/*                                                                          */
/* The EFI text console has no output device on this port, and the kernel   */
/* has no video console of its own: the only way to read a kernel log on a  */
/* panel is to draw it here. The glyphs are the 5x12 set the UEFI console   */
/* uses on this panel (crisp, known to read well there), doubled to 12x24   */
/* pixel cells. The text area starts below the camera cutout and is inset   */
/* from the rounded corners, which would otherwise cut the first and last   */
/* columns of the top lines.                                                */

#define FB_TEXT_SCALE  2
#define FB_CELL_W      (6 * FB_TEXT_SCALE)     /* 5 pixels + one of spacing */
#define FB_CELL_H      (12 * FB_TEXT_SCALE)
#define FB_X0          28                      /* clear of the rounded sides */
#define FB_Y0          120                     /* clear of the camera cutout */

static void
fb_char(uint64_t x, uint64_t y, char c, uint32_t fg)
{
	unsigned long long glyph;
	volatile uint32_t *p;
	uint64_t words, gx, gy;

	if (SCREEN.base == 0 || SCREEN.stride == 0 || SCREEN.height == 0) {
		return;
	}
	if (c < 32 || c > 126) {
		c = '?';
	}
	glyph = font5x12[(unsigned char)c - 32];
	p = (volatile uint32_t *)(uintptr_t)SCREEN.base;
	words = SCREEN.stride / 4;
	gx = x + FB_X0;
	gy = y + FB_Y0;
	for (unsigned row = 0; row < 12; row++) {
		uint32_t bits = (row < 6) ? (uint32_t)(glyph >> 32) >> (5 * row) :
		    (uint32_t)glyph >> (5 * (row - 6));

		for (unsigned col = 0; col < 5; col++) {
			uint64_t px, py;

			if ((bits & (1u << col)) == 0) {
				continue;
			}
			px = gx + (uint64_t)col * FB_TEXT_SCALE;
			py = gy + (uint64_t)row * FB_TEXT_SCALE;
			for (unsigned sy = 0; sy < FB_TEXT_SCALE; sy++) {
				for (unsigned sx = 0; sx < FB_TEXT_SCALE; sx++) {
					uint64_t ax = px + sx, ay = py + sy;

					if (ax < SCREEN.width && ay < SCREEN.height && ax < words) {
						p[ay * words + ax] = fg;
					}
				}
			}
		}
	}
}

/*
 * Draw the tail of a log (which ends with the interesting part: a panic) in
 * green on black. Everything after the last full line that fits is shown.
 */
static void
fb_render_log(const char *log, uint64_t len, uint32_t fg)
{
	uint64_t cols, rows, cap, start = 0, col = 0, row = 0;

	if (SCREEN.base == 0 || SCREEN.stride == 0 || SCREEN.height == 0) {
		return;
	}
	stage_paint(0xFF000000u);       /* black */
	cols = (SCREEN.width > 2 * FB_X0) ? (SCREEN.width - 2 * FB_X0) / FB_CELL_W : 0;
	rows = (SCREEN.height > FB_Y0 + FB_CELL_H) ? (SCREEN.height - FB_Y0 - 8) / FB_CELL_H : 0;
	rows = (rows > fb_reserve_rows) ? rows - fb_reserve_rows : 0;
	cap = cols * rows;
	if (cols == 0 || rows == 0) {
		return;
	}
	if (log == NULL || len == 0) {
		static const char none[] = "no log yet";
		for (uint64_t i = 0; none[i] && i / cols < rows; i++) {
			fb_char((i % cols) * FB_CELL_W, (i / cols) * FB_CELL_H, none[i], fg);
		}
		return;
	}
	if (len > (2u << 20)) {
		len = 2u << 20;
	}
	if (len > cap) {
		start = len - cap;
		/* begin at a line, not in its middle */
		while (start < len && log[start] != '\n') {
			start++;
		}
		if (start < len) {
			start++;
		}
	}
	for (uint64_t i = start; i < len && row < rows; i++) {
		char c = log[i];

		if (c == '\r') {
			continue;
		}
		if (c == '\n') {
			col = 0;
			row++;
			continue;
		}
		if (c == '\t') {
			col = (col + 4) & ~(uint64_t)3;
		} else if ((unsigned char)c < 32 || c == 127) {
			continue;       /* NULs and other control bytes: nothing to draw */
		} else {
			fb_char(col * FB_CELL_W, row * FB_CELL_H, c, fg);
			col++;
		}
		if (col >= cols) {
			col = 0;
			row++;
		}
	}
}

/* A line of our console: clear `lines` rows and draw the text in them. */
static void
fb_status_clear(unsigned lines)
{
	volatile uint32_t *p;
	uint64_t words, ymax;

	if (SCREEN.base == 0 || SCREEN.stride == 0 || SCREEN.height == 0) {
		return;
	}
	p = (volatile uint32_t *)(uintptr_t)SCREEN.base;
	words = SCREEN.stride / 4;
	ymax = (uint64_t)FB_Y0 + (uint64_t)lines * FB_CELL_H;
	for (uint64_t y = 0; y < ymax && y < SCREEN.height; y++) {
		for (uint64_t x = 0; x < words; x++) {
			p[y * words + x] = 0xFF000000u;
		}
	}
}

static unsigned
fb_u64(char *out, uint64_t v)
{
	char tmp[24];
	unsigned n = 0;

	do {
		tmp[n++] = (char)('0' + (v % 10));
		v /= 10;
	} while (v);
	for (unsigned i = 0; i < n; i++) {
		out[i] = tmp[n - 1 - i];
	}
	return n;
}

static void
fb_line(unsigned line, const char *s, uint32_t fg)
{
	for (unsigned i = 0; s[i]; i++) {
		fb_char((uint64_t)i * FB_CELL_W, (uint64_t)line * FB_CELL_H, s[i], fg);
	}
}

static unsigned
fb_hex(char *out, uint64_t v)
{
	static const char hex[] = "0123456789abcdef";
	char tmp[16];
	unsigned n = 0;

	do {
		tmp[n++] = hex[v & 15];
		v >>= 4;
	} while (v);
	out[0] = '0';
	out[1] = 'x';
	for (unsigned i = 0; i < n; i++) {
		out[2 + i] = tmp[n - 1 - i];
	}
	return 2 + n;
}

static void
fb_row_clear(uint64_t line)
{
	volatile uint32_t *p;
	uint64_t words, y0, ymax;

	if (SCREEN.base == 0 || SCREEN.stride == 0 || SCREEN.height == 0) {
		return;
	}
	p = (volatile uint32_t *)(uintptr_t)SCREEN.base;
	words = SCREEN.stride / 4;
	y0 = FB_Y0 + line * FB_CELL_H;
	ymax = y0 + FB_CELL_H;
	if (ymax > SCREEN.height) {
		ymax = SCREEN.height;
	}
	for (uint64_t y = y0; y < ymax; y++) {
		for (uint64_t x = 0; x < words; x++) {
			p[y * words + x] = 0xFF000000u;
		}
	}
}

/*
 * The monitor's bottom line: characters that have arrived since it started (a count that only
 * goes up, even after the log's ring has wrapped), and how many noise lines the retained log
 * holds now -- that second number falls as old lines are overwritten, which is not a fault.
 */
static void
monitor_footer(uint64_t new_bytes, unsigned hidden)
{
	static const char lead[] = "console +";
	static const char mid[] = " KiB since start, noise now: ";
	char buf[96];
	unsigned n = 0;
	uint64_t rows;

	for (unsigned i = 0; lead[i] != 0; i++) {
		buf[n++] = lead[i];
	}
	n += fb_u64(buf + n, new_bytes >> 10);
	for (unsigned i = 0; mid[i] != 0; i++) {
		buf[n++] = mid[i];
	}
	n += fb_u64(buf + n, hidden);
	if (log_slot_state == 1) {
		static const char tail[] = ", saved #";

		for (unsigned i = 0; tail[i] != 0; i++) {
			buf[n++] = tail[i];
		}
		n += fb_u64(buf + n, log_slot_seq);
	} else if (log_slot_state != 0) {
		static const char bad[] = ", save failed";

		for (unsigned i = 0; bad[i] != 0; i++) {
			buf[n++] = bad[i];
		}
	}
	buf[n] = 0;

	rows = (SCREEN.height > FB_Y0 + FB_CELL_H) ? (SCREEN.height - FB_Y0 - 8) / FB_CELL_H : 0;
	if (rows == 0) {
		return;
	}
	fb_row_clear(rows - 1);
	fb_line((unsigned)(rows - 1), buf, 0xFF9A9A9Au);
}

/*
 * The second bottom line with ustacks_probe=1: the kernel's own sampler state, read where it
 * lives (the addresses are the kernel's symbol table's, unslid; the monitor's slide makes them
 * readable on its core too). "call" is the thread call ustacks_init allocated -- 0 means the boot
 * argument was not taken; "cnt" is ustacks_count as it stands, and it falls by one for every fire,
 * so a value that never moves while call is set is a thread call that never ran. A cnt that falls
 * while the log has no "ustacks:" lines is a fire that found no process of that name.
 *
 * The addresses belong to prebuilt/mach.development.bcm2837, the kernel these images carry; a
 * rebuilt one moves them, and this line would then only be showing whatever happened to be there.
 */
#define USTACKS_NAME_VA    0xfffffff007e7e000ULL
#define USTACKS_CALL_VA    0xfffffff007e7e020ULL
#define USTACKS_COUNT_VA   0xfffffff007e7e068ULL
#define USTACKS_EVERY_VA   0xfffffff007e7e06cULL
#define USTACKS_THREADS_VA 0xfffffff007af5268ULL
#define USTACKS_TNAME_VA   0xfffffff007e8a780ULL

static void
monitor_ustacks(uint64_t slide)
{
	char buf[192];
	static const char lead[] = "ustacks call=";
	unsigned n = 0;
	uint64_t call = *(volatile uint64_t *)(uintptr_t)(USTACKS_CALL_VA + slide);
	uint32_t count = *(volatile uint32_t *)(uintptr_t)(USTACKS_COUNT_VA + slide);
	uint32_t every = *(volatile uint32_t *)(uintptr_t)(USTACKS_EVERY_VA + slide);
	uint32_t threads = *(volatile uint32_t *)(uintptr_t)(USTACKS_THREADS_VA + slide);
	const char *name = (const char *)(uintptr_t)(USTACKS_NAME_VA + slide);
	const char *tname = (const char *)(uintptr_t)(USTACKS_TNAME_VA + slide);
	uint64_t rows;

#define PUT_LIT(s) do { \
	for (unsigned i_ = 0; (s)[i_] != 0 && n < sizeof(buf) - 1; i_++) { \
		buf[n++] = (s)[i_]; \
	} \
} while (0)
#define PUT_TEXT(s) do { \
	for (unsigned i_ = 0; i_ < 31 && (s)[i_] != 0 && n < sizeof(buf) - 1; i_++) { \
		char ch_ = (s)[i_]; \
		buf[n++] = (ch_ >= 32 && ch_ < 127) ? ch_ : '.'; \
	} \
} while (0)

	PUT_LIT(lead);
	n += fb_hex(buf + n, call);
	PUT_LIT(" name=");
	PUT_TEXT(name);
	PUT_LIT(" cnt=");
	n += fb_u64(buf + n, count);
	PUT_LIT(" ev=");
	n += fb_u64(buf + n, every);
	PUT_LIT(" thr=");
	n += fb_u64(buf + n, threads);
	PUT_LIT(" tn=");
	PUT_TEXT(tname);
	buf[n] = 0;
#undef PUT_TEXT
#undef PUT_LIT

	rows = (SCREEN.height > FB_Y0 + FB_CELL_H) ? (SCREEN.height - FB_Y0 - 8) / FB_CELL_H : 0;
	if (rows < 2) {
		return;
	}
	fb_row_clear(rows - 2);
	fb_line((unsigned)(rows - 2), buf, 0xFFB0B0FFu);
}

/*
 * What power mode the UFS link ended up in: a UIC DME_GET for PA_PWR_MODE.
 * EDK2's UfsPassThru only performs link startup, never a PA_PWR_MODE change
 * to a high-speed gear; the value here says whether the link is still on a
 * PWM gear (low nibble 1..3) or an HS one (4..7), and how many lanes.
 * Bits: [3:0] mode, [5:4] gear, [7:6] lanes.
 */
static uint64_t
ufs_dme_get(uint32_t attr)
{
	volatile uint32_t *h = (volatile uint32_t *)(uintptr_t)0x112B0000;
	uint64_t deadline, now;
	uint32_t is;

	is = h[0x20 / 4];
	if (is & 0x400u) {              /* IS.UCCS: clear a stale completion */
		h[0x20 / 4] = is;
	}
	h[0x94 / 4] = attr << 16;      /* UIC_ARG_MIB: MIB id in the high half */
	h[0x98 / 4] = 0;
	h[0x9c / 4] = 0;
	deadline = READ_SYSREG(CNTVCT_EL0) + READ_SYSREG(CNTFRQ_EL0);
	while ((h[0x30 / 4] & 0x1u) == 0) {     /* HCS.UCRDY */
		if (READ_SYSREG(CNTVCT_EL0) > deadline) {
			return 0x1000000;
		}
	}
	h[0x90 / 4] = 0x01;             /* UIC DME_GET */
	deadline = READ_SYSREG(CNTVCT_EL0) + READ_SYSREG(CNTFRQ_EL0);
	while ((h[0x20 / 4] & 0x400u) == 0) {   /* IS.UCCS */
		if (READ_SYSREG(CNTVCT_EL0) > deadline) {
			return 0x2000000;
		}
	}
	if ((h[0x98 / 4] & 0xffu) != 0) {       /* command result */
		return 0x3000000u | (h[0x98 / 4] & 0xffu);
	}
	now = h[0x9c / 4];             /* value */
	return now;
}

static uint64_t
ufs_dme_set(uint32_t attr, uint32_t value)
{
	volatile uint32_t *h = (volatile uint32_t *)(uintptr_t)0x112B0000;
	uint64_t deadline;
	uint32_t is;

	is = h[0x20 / 4];
	if (is & 0x400u) {
		h[0x20 / 4] = is;
	}
	h[0x94 / 4] = attr << 16;
	h[0x98 / 4] = 0;
	h[0x9c / 4] = value;
	deadline = READ_SYSREG(CNTVCT_EL0) + READ_SYSREG(CNTFRQ_EL0);
	while ((h[0x30 / 4] & 0x1u) == 0) {
		if (READ_SYSREG(CNTVCT_EL0) > deadline) {
			return 0x1000000;
		}
	}
	h[0x90 / 4] = 0x02;             /* UIC DME_SET */
	deadline = READ_SYSREG(CNTVCT_EL0) + READ_SYSREG(CNTFRQ_EL0);
	while ((h[0x20 / 4] & 0x400u) == 0) {
		if (READ_SYSREG(CNTVCT_EL0) > deadline) {
			return 0x2000000;
		}
	}
	if ((h[0x98 / 4] & 0xffu) != 0) {
		return 0x3000000u | (h[0x98 / 4] & 0xffu);
	}
	return 0;
}

/*
 * Move the link from the PWM gear the EDK2 driver leaves it in to an HS one
 * (the sequence is the one a UEFI UFS stack for phones uses): set both gears,
 * the active lanes, termination and the HS series, then PA_PWRMODE with FAST
 * (HS) TX and RX; the controller's HCS.UPMCRS reports whether it took. Tries
 * the device's highest gear first and walks down. Returns 1 and the gear when
 * one worked, 0 when the link stays in PWM.
 */
static int
ufs_hs_switch(uint64_t *gear_out, uint64_t *lanes_out)
{
	volatile uint32_t *h = (volatile uint32_t *)(uintptr_t)0x112B0000;
	uint64_t maxgear = ufs_dme_get(0x1587);        /* PA_MaxRxHSGear */
	uint64_t lanes = ufs_dme_get(0x1560);          /* PA_ActiveTxDataLanes */

	if (maxgear < 1 || maxgear > 4) {
		maxgear = 4;
	}
	if (lanes < 1 || lanes > 2) {
		lanes = 2;
	}
	for (uint64_t g = maxgear; g >= 1; g--) {
		if (ufs_dme_set(0x1583, (uint32_t)g) != 0 ||   /* PA_RxGear */
		    ufs_dme_set(0x1568, (uint32_t)g) != 0 ||   /* PA_TxGear */
		    ufs_dme_set(0x1580, (uint32_t)lanes) != 0 || /* PA_ActiveRxLanes */
		    ufs_dme_set(0x1560, (uint32_t)lanes) != 0 || /* PA_ActiveTxLanes */
		    ufs_dme_set(0x1584, 1) != 0 ||             /* PA_RxTermination */
		    ufs_dme_set(0x1569, 1) != 0 ||             /* PA_TxTermination */
		    ufs_dme_set(0x156A, 2) != 0) {             /* PA_HSSeries: rate B */
			continue;
		}
		if (ufs_dme_set(0x1571, 0x11) != 0) {          /* PA_PWRMODE: HS, TX+RX FAST */
			continue;
		}
		if (((h[0x30 / 4] >> 8) & 7u) == 1u) {         /* HCS.UPMCRS == PWR_LOCAL */
			*gear_out = g;
			*lanes_out = lanes;
			return 1;
		}
		/* not taken: back to the PWM defaults before the next gear */
		ufs_dme_set(0x1571, 0x22);
	}
	return 0;
}

static uint64_t sysimg_pwr;
static uint64_t sysimg_gear;
static uint64_t sysimg_lanes;

/* The UFS read's progress, on the panel: MB read, seconds, and the mode. */
static void
sysimg_status(uint64_t done, uint64_t want, uint64_t started, uint64_t lba, int bounce,
    uint64_t dma_ms, uint64_t copy_ms)
{
	char buf[96];
	unsigned n = 0;
	const char *s;
	uint64_t secs = (READ_SYSREG(CNTVCT_EL0) - started) / READ_SYSREG(CNTFRQ_EL0);
	uint64_t mbs = secs ? (done >> 20) / secs : 0;

	s = "sysimg ";
	while (*s) buf[n++] = *s++;
	n += fb_u64(buf + n, done >> 20);
	buf[n++] = '/';
	n += fb_u64(buf + n, want >> 20);
	s = " MB  ";
	while (*s) buf[n++] = *s++;
	n += fb_u64(buf + n, mbs);
	s = " MB/s pwr ";
	while (*s) buf[n++] = *s++;
	n += fb_hex(buf + n, sysimg_pwr);
	buf[n] = 0;
	fb_status_clear(2);
	fb_line(0, buf, 0xFF00FF00u);

	n = 0;
	if (sysimg_gear != 0) {
		s = "HS G";
		while (*s) buf[n++] = *s++;
		buf[n++] = (char)('0' + (sysimg_gear % 10));
		s = " L";
		while (*s) buf[n++] = *s++;
		buf[n++] = (char)('0' + (sysimg_lanes % 10));
	} else {
		s = "HS FAIL";
		while (*s) buf[n++] = *s++;
	}
	s = bounce ? " bounce dma " : " direct dma ";
	while (*s) buf[n++] = *s++;
	n += fb_u64(buf + n, dma_ms);
	s = " ms copy ";
	while (*s) buf[n++] = *s++;
	n += fb_u64(buf + n, copy_ms);
	s = " ms";
	while (*s) buf[n++] = *s++;
	buf[n] = 0;
	fb_line(1, buf, 0xFF00FF00u);
}

static void
set_result(const char *what, uint64_t a, uint64_t b)
{
	uint32_t saved = log_len;
	uint32_t start = log_len;
	print("%s %d %x", what, a, b);
	uint32_t n = log_len - start;
	if (n > sizeof(last_result) - 1) {
		n = sizeof(last_result) - 1;
	}
	memcpy(last_result, log_buf + start, n);
	last_result[n] = 0;
	log_len = saved;
}

/* Every range of the firmware's memory map of 1 MB or more, and the total of each type. */
static void
print_memory_map(void)
{
	static uint8_t map_buf[65536];
	uint64_t map_size = sizeof(map_buf), map_key, desc_size, totals[16];
	uint32_t desc_ver;

	if (EFI_ERROR(BS->get_memory_map(&map_size, map_buf, &map_key, &desc_size, &desc_ver))) {
		print("GetMemoryMap failed\n");
		return;
	}
	memset(totals, 0, sizeof(totals));
	print("memory map (type 7 = free, 1/2 = loader, 3/4 = boot services, 5/6 = runtime, 0 = reserved):\n");
	for (uint64_t off = 0; off < map_size; off += desc_size) {
		efi_memory_descriptor *d = (efi_memory_descriptor *)(map_buf + off);

		if (d->type < 16) {
			totals[d->type] += d->pages << 12;
		}
		if (d->pages >= 256) {
			print("  %x - %x  type %d  %d MB\n", d->phys_start, d->phys_start + (d->pages << 12), (uint64_t)d->type,
			    d->pages >> 8);
		}
	}
	for (int t = 0; t < 16; t++) {
		if (totals[t] != 0) {
			print("  total of type %d: %d MB\n", (uint64_t)t, totals[t] >> 20);
		}
	}
}

static int
choose_window(const struct payload_info *pi)
{
	static uint8_t map_buf[65536];
	uint64_t map_size = sizeof(map_buf), map_key, desc_size;
	uint32_t desc_ver;
	uint64_t best_base = 0, best_size = 0;
	uint64_t pay_lo = PAYLOAD_BASE, pay_hi = PAYLOAD_BASE + PAYLOAD_MAX_SIZE;

	if (win_size != 0) {
		return 1;
	}
	if (EFI_ERROR(BS->get_memory_map(&map_size, map_buf, &map_key, &desc_size, &desc_ver))) {
		print("GetMemoryMap failed\n");
		return 0;
	}
	for (uint64_t off = 0; off < map_size; off += desc_size) {
		efi_memory_descriptor *d = (efi_memory_descriptor *)(map_buf + off);
		if (d->type != EfiConventionalMemory) {
			continue;
		}
		uint64_t lo = d->phys_start, hi = d->phys_start + (d->pages << 12);
		/* the payload sits in RAM that UEFI may consider free: stay clear of it */
		if (lo < pay_hi && hi > pay_lo) {
			if (pay_lo - lo > hi - pay_hi && pay_lo > lo) {
				hi = pay_lo;
			} else {
				lo = pay_hi;
			}
		}
		lo = (lo + BASE_ALIGN - 1) & ~(BASE_ALIGN - 1);
		hi &= ~(BASE_ALIGN - 1);
		if (hi > lo && hi - lo > best_size) {
			best_base = lo;
			best_size = hi - lo;
		}
	}
	print("largest free block %x size %x\n", best_base, best_size);
	if (pi->forced_base != 0) {
		best_base = pi->forced_base;
		best_size = MAX_MEM_SIZE;
	}
	if (best_size > MAX_MEM_SIZE) {
		best_size = MAX_MEM_SIZE;
	}
	/* UEFI stays alive while the kernel runs, so the kernel must own all of its window. */
	uint64_t claim = best_base;
	efi_status s = BS->allocate_pages(AllocateAddress, EfiLoaderData, best_size >> 12, &claim);
	print("phys window %x size %x, claim status %x\n", best_base, best_size, s);
	if (EFI_ERROR(s)) {
		return 0;
	}
	win_base = best_base;
	win_size = best_size;
	return 1;
}

/*
 * Paging for the saved log. Page starts are byte offsets into prev_text; a page is exactly
 * what fills `rows` rows of `cols` columns, with the rules fb_render_log draws by, so the
 * pages tile the text without gaps and every press moves one screenful.
 */
#define PREV_MAX_PAGES 4096
static const char *prev_text;
static uint32_t prev_len;
static uint32_t prev_page[PREV_MAX_PAGES];
static uint32_t prev_pages;

static uint32_t
prev_page_extent(uint32_t start, uint32_t cols, uint32_t rows)
{
	uint32_t col = 0, row = 0, i = start;

	while (i < prev_len) {
		char c = prev_text[i];

		if (c == '\r') {
			i++;
			continue;
		}
		if (c == '\n') {
			col = 0;
			row++;
			i++;
		} else if (c == '\t') {
			col = (col + 4) & ~3u;
			i++;
		} else if ((unsigned char)c < 32 || c == 127) {
			i++;
			continue;
		} else {
			col++;
			i++;
		}
		if (col >= cols) {
			col = 0;
			row++;
		}
		if (row >= rows) {
			break;
		}
	}
	return i;
}

static void
prev_render(uint32_t start, uint32_t end, uint32_t cols, uint32_t rows, uint32_t fg)
{
	uint32_t col = 0, row = 0;

	stage_paint(0xFF000000u);
	for (uint32_t i = start; i < end && row < rows; i++) {
		char c = prev_text[i];

		if (c == '\r') {
			continue;
		}
		if (c == '\n') {
			col = 0;
			row++;
			continue;
		}
		if (c == '\t') {
			col = (col + 4) & ~3u;
		} else if ((unsigned char)c < 32 || c == 127) {
			continue;
		} else {
			fb_char((uint64_t)col * FB_CELL_W, (uint64_t)row * FB_CELL_H, c, fg);
			col++;
		}
		if (col >= cols) {
			col = 0;
			row++;
		}
	}
}

static void
prev_compute_pages(uint32_t cols, uint32_t rows)
{
	uint32_t at = 0;

	prev_pages = 0;
	while (at < prev_len) {
		uint32_t next;

		if (prev_pages == PREV_MAX_PAGES) {
			/* keep the newest pages: drop the older half and go on */
			memcpy(prev_page, prev_page + PREV_MAX_PAGES / 2,
			    (PREV_MAX_PAGES / 2) * sizeof(prev_page[0]));
			prev_pages = PREV_MAX_PAGES / 2;
		}
		prev_page[prev_pages++] = at;
		next = prev_page_extent(at, cols, rows);
		if (next <= at) {
			break;
		}
		at = next;
	}
}

/*
 * A copy of the saved log with only the lines that say "ustacks:". The rest of a boot log is a
 * wall of launchd and lsd chatter; this is the same viewer with the thread snapshots only.
 */
static int
line_has_ustacks(const char *p, uint32_t n)
{
	static const char want[] = "ustacks:";

	for (uint32_t i = 0; i + 8 <= n; i++) {
		uint32_t k = 0;

		while (k < 8 && p[i + k] == want[k]) {
			k++;
		}
		if (k == 8) {
			return 1;
		}
	}
	return 0;
}

static uint32_t
filter_ustacks(const char *src, uint32_t len, char *dst, uint32_t cap)
{
	uint32_t line = 0, out = 0;

	while (line < len && out < cap) {
		uint32_t end = line, n;

		while (end < len && src[end] != '\n') {
			end++;
		}
		if (line_has_ustacks(src + line, end - line)) {
			n = end - line;
			if (n > cap - out) {
				n = cap - out;
			}
			memcpy(dst + out, src + line, n);
			out += n;
			if (out < cap) {
				dst[out++] = '\n';
			}
		}
		line = end + 1;
	}
	return out;
}

/*
 * showprev=1 / showprev=ustacks: draw the newest log the monitor core saved in userdata, then
 * stay there. Both slots are looked at; a slot counts when its header is intact and the CRC of
 * its text matches, and the one with the higher sequence number wins. With ust_only only the
 * "ustacks:" lines are shown. The volume key pages: a short press (SCAN_UP) back, a press held
 * past 700 ms (Enter) forward.
 */
static void
show_previous_log(int ust_only)
{
	static const char none[] = "no saved log in userdata";
	static const char bad[] = "the saved slots are corrupt";
	uint64_t first = 0, blocks = 0;
	efi_block_io *bio = ufs_find_partition("userdata", &first, &blocks);
	uint64_t bs, slot_blocks, best_seq = 0;
	uint32_t text_off;
	int best = -1;

	if (bio == NULL) {
		fb_render_log(none, sizeof(none) - 1, 0xFFFF0000u);
		return;
	}
	bs = bio->media->block_size;
	if (bs == 0 || bs > LOG_SLOT_HEADER) {
		fb_render_log(bad, sizeof(bad) - 1, 0xFFFF0000u);
		return;
	}
	text_off = (LOG_SLOT_HEADER + bs - 1) / bs * bs;
	slot_blocks = LOG_SLOT_SIZE / bs;
	for (int slot = 0; slot < 2; slot++) {
		uint64_t lba = first + LOG_SLOT_OFFSET / bs + (uint64_t)slot * slot_blocks;
		struct log_slot_header *h;

		if (EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, lba, bs, log_slot_buf))) {
			continue;
		}
		flush_dcache((uint64_t)(uintptr_t)log_slot_buf, (uint64_t)(uintptr_t)log_slot_buf + bs);
		h = (struct log_slot_header *)log_slot_buf;
		if (h->magic != LOG_SLOT_MAGIC || h->version != 1 || h->length > LOG_SLOT_SIZE - text_off) {
			continue;
		}
		if (best < 0 || h->seq > best_seq) {
			best = slot;
			best_seq = h->seq;
		}
	}
	if (best < 0) {
		fb_render_log(none, sizeof(none) - 1, 0xFFFF0000u);
		return;
	}
	for (int tries = 0; tries < 2; tries++) {
		uint64_t lba = first + LOG_SLOT_OFFSET / bs + (uint64_t)best * slot_blocks;
		struct log_slot_header *h;

		if (!EFI_ERROR(bio->read_blocks(bio, bio->media->media_id, lba, LOG_SLOT_SIZE, log_slot_buf))) {
			flush_dcache((uint64_t)(uintptr_t)log_slot_buf, (uint64_t)(uintptr_t)log_slot_buf + LOG_SLOT_SIZE);
			h = (struct log_slot_header *)log_slot_buf;
			if (h->magic == LOG_SLOT_MAGIC && h->version == 1 &&
			    h->length <= LOG_SLOT_SIZE - text_off &&
			    ufs_crc32((const uint8_t *)log_slot_buf + text_off, h->length) == h->crc) {
				efi_simple_text_input *in[8];
				unsigned nin = 0;
				uint64_t cols, rows_all, rows;
				uint64_t freq = READ_SYSREG(CNTFRQ_EL0);
				uint32_t page;
				char foot[128];

				if (h->length == 0) {
					static const char empty[] = "the saved log is empty";

					fb_render_log(empty, sizeof(empty) - 1, 0xFFFF0000u);
					return;
				}
				if (ust_only) {
					uint32_t n = filter_ustacks((const char *)log_slot_buf + text_off, h->length,
					    out_buf, sizeof(out_buf));

					if (n == 0) {
						static const char noun[] = "no ustacks lines in the saved log";

						fb_render_log(noun, sizeof(noun) - 1, 0xFFFF0000u);
						return;
					}
					prev_text = out_buf;
					prev_len = n;
				} else {
					prev_text = (const char *)log_slot_buf + text_off;
					prev_len = h->length;
				}
				cols = (SCREEN.width > 2 * FB_X0) ? (SCREEN.width - 2 * FB_X0) / FB_CELL_W : 0;
				rows_all = (SCREEN.height > FB_Y0 + FB_CELL_H) ? (SCREEN.height - FB_Y0 - 8) / FB_CELL_H : 0;
				if (cols == 0 || rows_all < 2) {
					fb_render_log(prev_text, prev_len, 0xFF00FF00u);
					return;
				}
				rows = rows_all - 1;            /* the last row is the footer */
				prev_compute_pages((uint32_t)cols, (uint32_t)rows);
				page = prev_pages - 1;
				/*
				 * The key may already have left the keypad's own queue: the firmware's console
				 * splitter reads it first (the Boot Manager's menu listens for that same SCAN_UP).
				 * So read the console input the firmware itself uses, and every SimpleTextIn
				 * instance besides, and take a key from whichever has one.
				 */
				if (ST->con_in != NULL) {
					in[nin++] = (efi_simple_text_input *)ST->con_in;
				}
				{
					efi_guid in_guid = EFI_SIMPLE_TEXT_INPUT_GUID;
					efi_handle *handles = NULL;
					uint64_t count = 0;

					if (!EFI_ERROR(BS->locate_handle_buffer(ByProtocol, &in_guid, NULL, &count, &handles))) {
						for (uint64_t i = 0; i < count && nin < 8; i++) {
							efi_simple_text_input *p = NULL;
							int dup = 0;

							if (EFI_ERROR(BS->handle_protocol(handles[i], &in_guid, (void **)&p)) || p == NULL) {
								continue;
							}
							for (unsigned k = 0; k < nin; k++) {
								if (in[k] == p) {
									dup = 1;
								}
							}
							if (!dup) {
								in[nin++] = p;
							}
						}
					}
				}
				for (;;) {
					uint32_t end = (page + 1 < prev_pages) ? prev_page[page + 1] : prev_len;
					unsigned n = 0;
					static const char p1[] = "page ";
					static const char p2[] = "  short press: older, long press: newer  saved at ";
					static const char p3[] = " s, seq ";

					for (unsigned i = 0; p1[i] != 0; i++) {
						foot[n++] = p1[i];
					}
					n += fb_u64(foot + n, page + 1);
					foot[n++] = '/';
					n += fb_u64(foot + n, prev_pages);
					for (unsigned i = 0; p2[i] != 0; i++) {
						foot[n++] = p2[i];
					}
					n += fb_u64(foot + n, h->uptime_ms / 1000);
					for (unsigned i = 0; p3[i] != 0; i++) {
						foot[n++] = p3[i];
					}
					n += fb_u64(foot + n, h->seq);
					foot[n] = 0;
					prev_render(prev_page[page], end, (uint32_t)cols, (uint32_t)rows, 0xFF00FF00u);
					fb_row_clear(rows_all - 1);
					fb_line((unsigned)(rows_all - 1), foot, 0xFF9A9A9Au);
					if (nin == 0) {
						return;         /* no key input: leave the newest page up */
					}
					{
						uint8_t key = 0;
						uint64_t began = READ_SYSREG(CNTVCT_EL0);

						/*
						 * Wait for a key, but come back every half second to redraw: the
						 * firmware prints its own "volume up pressed/released" lines to the
						 * framebuffer and those would sit on top of the page.
						 */
						while (key == 0) {
							for (unsigned i = 0; i < nin && key == 0; i++) {
								efi_input_key k;

								if (!EFI_ERROR(in[i]->read_key_stroke(in[i], &k))) {
									if (k.scan_code == SCAN_UP) {
										key = 1;
									} else if (k.unicode_char == 0x0D) {
										key = 2;
									}
								}
							}
							if (key != 0 || READ_SYSREG(CNTVCT_EL0) - began >= freq / 2) {
								break;
							}
							BS->stall(20000);
						}
						if (key == 1 && page > 0) {
							page--;
						} else if (key == 2 && page + 1 < prev_pages) {
							page++;
						}
					}
				}
			}
		}
		best ^= 1;                      /* the other slot, once */
	}
	fb_render_log(bad, sizeof(bad) - 1, 0xFFFF0000u);
}

/*
 * Load and run the kernel from the payload. Returns when the kernel comes
 * back (panic, checkpoint, early exception); the combined log is staged and
 * written to the log partition. Returns 0 if the kernel could not be started.
 */
static int starts_with(const char *s, const char *prefix);

static int
run_kernel(int have_checkpoint, uint64_t checkpoint)
{
	static uint8_t map_buf[65536];
	uint64_t map_size, map_key, desc_size;
	uint32_t desc_ver;
	struct payload_info pi;

	if (!parse_payload(&pi, 1) || pi.kernel == NULL) {
		print("no kernel in payload\n");
		return 0;
	}
	if (!have_checkpoint) {
		checkpoint = pi.checkpoint;
	}
	const uint8_t *kernel = pi.kernel;
	const struct mach_header_64 *mh = (const struct mach_header_64 *)kernel;
	if (mh->magic != MH_MAGIC_64) {
		print("kernel is not a 64-bit Mach-O\n");
		return 0;
	}

	/* --- kernel extent -------------------------------------------------- */
	uint64_t vm_lo = ~0ULL, vm_hi = 0, entry_va = 0;
	const struct load_command *lc = (const struct load_command *)(mh + 1);
	for (uint32_t i = 0; i < mh->ncmds; i++, lc = (const void *)((const uint8_t *)lc + lc->cmdsize)) {
		if (lc->cmd == LC_SEGMENT_64) {
			const struct segment_command_64 *sg = (const void *)lc;
			if (sg->vmsize == 0) {
				continue;
			}
			if (sg->vmaddr < vm_lo) {
				vm_lo = sg->vmaddr;
			}
			if (sg->vmaddr + sg->vmsize > vm_hi) {
				vm_hi = sg->vmaddr + sg->vmsize;
			}
		} else if (lc->cmd == LC_UNIXTHREAD) {
			/* cmd, cmdsize, flavor, count, x0..x28, fp, lr, sp, pc */
			entry_va = ((const uint64_t *)((const uint8_t *)lc + 16))[32];
		}
	}
	print("kernel va %x..%x entry %x\n", vm_lo, vm_hi, entry_va);
	if (vm_lo < KERNEL_VIRT_BASE + KERNEL_LINK_OFFSET || entry_va == 0) {
		print("unexpected kernel layout\n");
		return 0;
	}
	if (!choose_window(&pi)) {
		return 0;
	}
	stage_paint(STAGE_YELLOW);

#ifdef MALACHITE_STAGES
	/* Probe the claimed window before trusting it with the kernel: a fault here
	 * means the firmware mapped the descriptive region but not the memory. */
	{
		volatile uint64_t *probe = (volatile uint64_t *)(uintptr_t)(win_base + 0x1000000);
		*probe = 0xA5A5A5A5A5A5A5A5ULL;
		if (*probe == 0xA5A5A5A5A5A5A5A5ULL) {
			stage_paint(STAGE_LIME);
		}
	}
#endif

	uint64_t phys_base = win_base;
	uint64_t slide = phys_base - KERNEL_VIRT_BASE; /* pa = va + slide */
	uint64_t kern_lo = vm_lo + slide, kern_hi = (vm_hi + slide + PAGE_SIZE_MAX - 1) & ~(PAGE_SIZE_MAX - 1);
	/* The ramdisk must sit inside the kernel's static mapping, i.e. below topOfKernelData. */
	uint64_t rd_pa = kern_hi;
	uint64_t rd_size = (pi.ramdisk_size + PAGE_SIZE_MAX - 1) & ~(PAGE_SIZE_MAX - 1);
	int rd_resident = 0;
	/* A resident image next to a payload ramdisk: two disks (which is which is decided where the device tree is written). */
	uint64_t rd1_pa = 0, rd1_size = 0;

	if (pi.resident_rd != 0) {
		resident_rd_size = pi.resident_rd;
	}
	if (resident_rd_size != 0) {
		uint64_t res_pa = phys_base + RESIDENT_RD_OFFSET;
		uint64_t res_size = (resident_rd_size + PAGE_SIZE_MAX - 1) & ~(PAGE_SIZE_MAX - 1);

		if (kern_hi + rd_size > res_pa) {
			print("kernel and ramdisk overlap the resident image\n");
			return 0;
		}
		if (rd_size == 0) {
			rd_pa = res_pa;
			rd_size = res_size;
			rd_resident = 1;
		} else {
			rd1_pa = res_pa;
			rd1_size = res_size;
		}
	}
	/* everything up to topOfKernelData is the kernel's static region: it must cover both images */
	uint64_t dt_pa = rd1_size != 0 ? rd1_pa + rd1_size : rd_pa + rd_size;
	uint64_t dt_max = 0x10000;
	uint64_t ba_pa = dt_pa + dt_max;
	uint64_t top = ba_pa + PAGE_SIZE_MAX;

	if (win_size < top - phys_base + 0x4000000ULL) {
		print("not enough contiguous RAM\n");
		return 0;
	}

	/* --- load segments -------------------------------------------------- */
	lc = (const struct load_command *)(mh + 1);
	for (uint32_t i = 0; i < mh->ncmds; i++, lc = (const void *)((const uint8_t *)lc + lc->cmdsize)) {
		const struct segment_command_64 *sg = (const void *)lc;
		if (lc->cmd != LC_SEGMENT_64 || sg->vmsize == 0) {
			continue;
		}
		memset((void *)(sg->vmaddr + slide), 0, sg->vmsize);
		memcpy((void *)(sg->vmaddr + slide), kernel + sg->fileoff, sg->filesize);
	}
	print("kernel loaded at pa %x..%x\n", kern_lo, kern_hi);
	stage_paint(STAGE_ORANGE);
	if (rd_resident) {
		print("resident ramdisk at pa %x size %x\n", rd_pa, rd_size);
	} else if (rd_size != 0) {
		memset((void *)rd_pa, 0, rd_size);
		memcpy((void *)rd_pa, pi.ramdisk, pi.ramdisk_size);
		print("ramdisk at pa %x size %x\n", rd_pa, rd_size);
	}
	if (rd1_size != 0) {
		print("resident image at pa %x size %x: it is the root (md0), the payload ramdisk is md1\n", rd1_pa, rd1_size);
	}

	/* "bootcpu=N" among the kernel's arguments: run it on core N (see run_on_other_cpu) */
	uint64_t this_mpidr = READ_SYSREG(MPIDR_EL1) & 0xFFFFFF, kernel_mpidr = this_mpidr;
	/* "cpus=N" or "cpumask=M" there too: the kernel may have more cores than the one it starts on */
	int more_cores = 0, battery_requested = 0, ufs_requested = 0, memmap_requested = 0, sysimg_requested = 0;
	int sysimg_test = 0;
	int sysimg_bounce = 0;
	int monitor_requested = 0;
	int kret_hold = 0;
	int showprev_mode = 0;         /* showprev=1: the saved log; showprev=ustacks: its ustacks lines */
	int ustacks_probe = 0;         /* ustacks_probe=1: the monitor shows ustacks_*'s state too */
	/* "torch=N" (not 0) there too: the phone's flashlight is the kernel's (bsd/dev/redwood_torch.c) */
	int torch_requested = 0;
	/* "cam=5" there too: the phone's wide camera is iOS's (bsd/dev/redwood_camera.c) */
	int camera_requested = 0;
	/* (the loader stays for run after run: what the last run's arguments said must not hold for this one) */
	gamut_p3 = 0;
	/* a run that does not ask for writes does not get them, whatever an earlier run of this
	 * loader asked for (the loader stays resident across runs) */
	block_write_requested = 0;
	block_write_part = -1;
	for (const char *c = pi.cmdline; *c; c++) {
		if (starts_with(c, "bootcpu=") && (c == pi.cmdline || c[-1] == ' ') && c[8] >= '0' && c[8] <= '7') {
			kernel_mpidr = (uint64_t)(c[8] - '0') << PLAT->core_shift;
		}
		more_cores |= (starts_with(c, "cpus=") || starts_with(c, "cpumask=")) && (c == pi.cmdline || c[-1] == ' ');
		battery_requested |= starts_with(c, "battery=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[9] == 0 || c[9] == ' ');
		torch_requested |= starts_with(c, "torch=") && (c == pi.cmdline || c[-1] == ' ') && c[6] >= '1' && c[6] <= '9';
		camera_requested |= starts_with(c, "cam=5") && (c == pi.cmdline || c[-1] == ' ') && (c[5] == 0 || c[5] == ' ');
		gamut_p3 |= starts_with(c, "gamut=p3") && (c == pi.cmdline || c[-1] == ' ');
		if (starts_with(c, "ufs=") && (c == pi.cmdline || c[-1] == ' ') && c[4] >= '1' && c[4] <= '2' &&
		    (c[5] == 0 || c[5] == ' ')) {
			ufs_requested = c[4] - '0';
		}
		memmap_requested |= starts_with(c, "memmap=1") && (c == pi.cmdline || c[-1] == ' ');
		sysimg_requested |= starts_with(c, "sysimg=ufs") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[10] == 0 || c[10] == ' ');
		sysimg_test |= starts_with(c, "sysimg_test=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[13] == 0 || c[13] == ' ');
		sysimg_bounce |= starts_with(c, "sysimg_bounce=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[15] == 0 || c[15] == ' ');
		kret_hold |= starts_with(c, "kret_hold=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[11] == 0 || c[11] == ' ');
		monitor_requested |= starts_with(c, "monitor=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[9] == 0 || c[9] == ' ');
		ustacks_probe |= starts_with(c, "ustacks_probe=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[15] == 0 || c[15] == ' ');
		block_probe_requested |= starts_with(c, "ufs_probe=1") && (c == pi.cmdline || c[-1] == ' ');
		block_write_requested |= starts_with(c, "ufs_write=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[11] == 0 || c[11] == ' ');
		hc_requested |= starts_with(c, "ufs_native=") && (c == pi.cmdline || c[-1] == ' ') && c[11] >= '1' &&
		    c[11] <= '9';
		if (starts_with(c, "showprev=ustacks") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[16] == 0 || c[16] == ' ')) {
			showprev_mode = 2;
		} else if (starts_with(c, "showprev=1") && (c == pi.cmdline || c[-1] == ' ') &&
		    (c[10] == 0 || c[10] == ' ')) {
			showprev_mode = 1;
		}
	}
	if (showprev_mode != 0) {
		show_previous_log(showprev_mode == 2);
		for (;;) {
			__asm__ volatile("wfi");
		}
	}
#ifdef MALACHITE_PARSE_HALT
	/* Bring-up: what did the payload actually say? White screen; a red square
	 * top-left if kret_hold was parsed, a blue one top-right if sysimg=ufs
	 * was. Then stop, so a photo answers it in seconds. */
	stage_paint(STAGE_WHITE);
	if (kret_hold) {
		stage_corner(STAGE_RED, 0, 0, 300);
	}
	if (sysimg_requested) {
		stage_corner(STAGE_BLUE, 1, 0, 300);
	}
	for (;;) {
		__asm__ volatile("wfi");
	}
#endif
	if (sysimg_requested) {
		uint64_t dest = phys_base + RESIDENT_RD_OFFSET;
		uint64_t want = resident_rd_size;
		uint64_t first = 0, blocks = 0, done = 0;
		uint64_t started = READ_SYSREG(CNTVCT_EL0);
		efi_block_io *bio = ufs_find_partition("userdata", &first, &blocks);

		/* The panel is this read's progress meter: black, with the megabytes
		 * done and how they were read. A stalled read leaves its last number
		 * on screen, which says where it stopped. */
		/*
		 * The EDK2 driver never leaves the PWM gear: try an HS one here,
		 * before any of the big reads, and show which one took.
		 */
		sysimg_gear = 0;
		sysimg_lanes = 0;
		(void)ufs_hs_switch(&sysimg_gear, &sysimg_lanes);
		sysimg_pwr = ufs_dme_get(0x1571);       /* PA_PWRMODE, after the switch */
		stage_paint(0xFF000000u);
		sysimg_status(0, want, started, first, sysimg_bounce, 0, 0);
		if (bio == NULL || want == 0) {
			print("sysimg: userdata %s, resident size %x\n", bio == NULL ? "not found" : "found",
			    want);
			fb_line(2, "userdata not found", 0xFFFF0000u);
			for (;;) {
				__asm__ volatile("wfi");
			}
		}
		if (blocks * bio->media->block_size < want) {
			print("sysimg: userdata %x blocks, image needs %x blocks\n", blocks,
			    (want + bio->media->block_size - 1) / bio->media->block_size);
			fb_line(2, "userdata too small", 0xFFFF0000u);
			for (;;) {
				__asm__ volatile("wfi");
			}
		}
		/*
		 * sysimg_test=1 (bring-up): read one megabyte twice, once into the
		 * loader's own low buffer and once into the high address the kernel
		 * window uses, and compare. Blue says they match and the full read
		 * starts; red says the controller did not put the bytes where it was
		 * told. Magenta after the full image means all of it came back; the
		 * loader then stops there (no kernel, no log handoff), so the colour
		 * is what a photo shows.
		 */
		if (sysimg_test) {
			uint64_t probe = 0x100000;

			if (probe > want) {
				probe = want;
			}
			if (probe & (bio->media->block_size - 1)) {
				probe = (probe + bio->media->block_size - 1) & ~(bio->media->block_size - 1);
			}
			efi_status s1 = bio->read_blocks(bio, bio->media->media_id, first, probe, ufs_buffer);
			efi_status s2 = bio->read_blocks(bio, bio->media->media_id, first, probe,
			    (void *)(uintptr_t)dest);
			if (EFI_ERROR(s1) || EFI_ERROR(s2) || memcmp(ufs_buffer, (const void *)(uintptr_t)dest, probe) != 0) {
				print("sysimg: high read test failed: %x %x, first %x %x %x %x / %x %x %x %x\n",
				    (uint64_t)s1, (uint64_t)s2,
				    (uint64_t)ufs_buffer[0], (uint64_t)ufs_buffer[1], (uint64_t)ufs_buffer[2],
				    (uint64_t)ufs_buffer[3], (uint64_t)((const uint8_t *)(uintptr_t)dest)[0],
				    (uint64_t)((const uint8_t *)(uintptr_t)dest)[1],
				    (uint64_t)((const uint8_t *)(uintptr_t)dest)[2],
				    (uint64_t)((const uint8_t *)(uintptr_t)dest)[3]);
				stage_paint(STAGE_RED);
				for (;;) {
					__asm__ volatile("wfi");
				}
			}
			stage_paint(STAGE_BLUE);
			print("sysimg: high read test passed\n");
		}
		print("sysimg: %d MB from userdata lba %x to pa %x\n", want >> 20, first, dest);
		{
			uint64_t last_show = started;
			uint64_t dma_ms = 0, copy_ms = 0;

			while (done < want) {
				uint64_t chunk = want - done;
				uint64_t t0, t1, t2;
				efi_status s;

				if (chunk > 0x400000) {
					chunk = 0x400000;
				}
				if (chunk & (bio->media->block_size - 1)) {
					chunk = (chunk + bio->media->block_size - 1) & ~(bio->media->block_size - 1);
				}
				t0 = READ_SYSREG(CNTVCT_EL0);
				if (sysimg_bounce) {
					s = bio->read_blocks(bio, bio->media->media_id,
					    first + done / bio->media->block_size, chunk, block_buffer);
					t1 = READ_SYSREG(CNTVCT_EL0);
					if (!EFI_ERROR(s)) {
						memcpy((void *)(uintptr_t)(dest + done), block_buffer, chunk);
					}
					t2 = READ_SYSREG(CNTVCT_EL0);
				} else {
					s = bio->read_blocks(bio, bio->media->media_id,
					    first + done / bio->media->block_size, chunk,
					    (void *)(uintptr_t)(dest + done));
					t1 = t2 = READ_SYSREG(CNTVCT_EL0);
				}
				dma_ms = (t1 - t0) * 1000 / READ_SYSREG(CNTFRQ_EL0);
				copy_ms = (t2 - t1) * 1000 / READ_SYSREG(CNTFRQ_EL0);
				if (EFI_ERROR(s)) {
					print("sysimg: read at %d MB failed: %x\n", done >> 20, (uint64_t)s);
					sysimg_status(done, want, started, first + done / bio->media->block_size,
					    sysimg_bounce, dma_ms, copy_ms);
					fb_line(2, "READ FAILED", 0xFFFF0000u);
					for (;;) {
						__asm__ volatile("wfi");
					}
				}
				done += chunk;
				if (done % (512ULL << 20) == 0 && done < want) {
					print("sysimg: %d MB\n", done >> 20);
				}
				if (seconds_since(last_show) >= 1) {
					last_show = READ_SYSREG(CNTVCT_EL0);
					sysimg_status(done, want, started,
					    first + done / bio->media->block_size, sysimg_bounce, dma_ms,
					    copy_ms);
				}
				if (wdt_armed) {
					wdt_pet();
				}
			}
			sysimg_status(done, want, started, first + want / bio->media->block_size,
			    sysimg_bounce, dma_ms, copy_ms);
		}
		{
			const uint8_t *head = (const uint8_t *)(uintptr_t)dest;
			int apfs = head[0x20] == 'N' && head[0x21] == 'X' && head[0x22] == 'S' &&
			    head[0x23] == 'B';

			print("sysimg: done in %d ms, head %x %x %x %x %x %x %x %x, at 20: %x %x %x %x\n",
			    (READ_SYSREG(CNTVCT_EL0) - started) * 1000 / READ_SYSREG(CNTFRQ_EL0),
			    (uint64_t)head[0], (uint64_t)head[1], (uint64_t)head[2], (uint64_t)head[3],
			    (uint64_t)head[4], (uint64_t)head[5], (uint64_t)head[6], (uint64_t)head[7],
			    (uint64_t)head[0x20], (uint64_t)head[0x21], (uint64_t)head[0x22],
			    (uint64_t)head[0x23]);
			fb_line(2, apfs ? "APFS NXSB ok" : "APFS magic BAD",
			    apfs ? 0xFF00FF00u : 0xFFFF0000u);
		}
		if (sysimg_test) {
			for (;;) {
				__asm__ volatile("wfi");
			}
		}
	}
	if (battery_requested) {
		charger_start();
	}
	if (ufs_requested >= 2) {
		hc_init();              /* (ufs_native=: UEFI's transfer list kept, before anything reads) */
	}
	if (memmap_requested) {
		print_memory_map();
	}
	if (ufs_requested >= 1) {
		ufs_survey();
	}
	if (ufs_requested >= 2) {
		block_start();
	}
	if (checkpoint == CHECKPOINT_SELFTEST) {
		kernel_mpidr = this_mpidr;
	}

	/* where the kernel will show its signs of life, and how long it has said it will run */
	const struct kernel_live *kernel_live = NULL;
	uint64_t kernel_budget = 0;
	for (uint64_t *q = (uint64_t *)kern_lo; q < (uint64_t *)kern_hi; q++) {
		if (*q == KERNEL_LIVE_MAGIC) {
			kernel_live = (const struct kernel_live *)q;
			break;
		}
	}
	for (const char *c = pi.cmdline; *c; c++) {
		if (starts_with(c, "loader_return_after=")) {
			for (c += 20; *c >= '0' && *c <= '9'; c++) {
				kernel_budget = kernel_budget * 10 + (uint64_t)(*c - '0');
			}
			break;
		}
	}

	/* Give the kernel the address of our return stub and the checkpoint to stop at. */
	for (uint64_t *q = (uint64_t *)kern_lo; q < (uint64_t *)kern_hi; q++) {
		if (*q == 0x545352444C554E58ULL /* "XNULDRST" */) {
			q[1] = kernel_mpidr != this_mpidr ? (uint64_t)(uintptr_t)&other_cpu_return_stub :
			    (uint64_t)(uintptr_t)&loader_return_stub;
			q[2] = checkpoint;
			q[3] = slide;
			print("return slot patched at %x, checkpoint %d\n", (uint64_t)(uintptr_t)q, checkpoint);
			break;
		}
	}

	/* --- boot_args ------------------------------------------------------ */
	struct boot_args *ba = (struct boot_args *)ba_pa;
	memset(ba, 0, sizeof(*ba));
	ba->revision = 2;
	ba->version = 2;
	ba->virtBase = KERNEL_VIRT_BASE;
	ba->physBase = phys_base;
	ba->memSize = win_size;
	ba->memSizeActual = win_size;
	ba->topOfKernelData = top;
	/* any display the firmware has set up: the phone's panel, or QEMU's ramfb */
	if (SCREEN.base != 0) {
		/*
		 * v_display is how iBoot says "graphics mode": the kernel then keeps
		 * its text off the screen. A verbose boot (-v) wants the text.
		 */
		int verbose = 0;
		for (const char *c = pi.cmdline; *c; c++) {
			verbose |= starts_with(c, "-v") && (c[2] == ' ' || c[2] == 0) && (c == pi.cmdline || c[-1] == ' ');
		}
		ba->video.v_baseAddr = SCREEN.base;
		ba->video.v_display = verbose ? 0 : 1;
		ba->video.v_rowBytes = SCREEN.stride;
		ba->video.v_width = SCREEN.width;
		ba->video.v_height = SCREEN.height;
		ba->video.v_depth = 32;
	}
	/*
	 * No "-v" by default: on the phone the verbose console is a text
	 * framebuffer that scrolls 10 MB per line and slows boot to a crawl.
	 * The log comes back through the loader instead. Add -v via the
	 * payload's cmdline entry to watch the boot on screen.
	 */
	/*
	 * serial=3 sends the console to the UART. Where there is none it would
	 * only silence the screen; and a "serial=" in the payload's own
	 * arguments must win, which means ours must not come first.
	 */
	int own_serial = 0;
	for (const char *c = pi.cmdline; *c; c++) {
		own_serial |= starts_with(c, "serial=");
	}
	const char *base_cmdline = (PLAT->uart != 0 && !own_serial) ? "debug=0x8 serial=3 " : "debug=0x8 ";
	uint32_t n = 0;
	for (const char *c = base_cmdline; *c && n < BOOT_LINE_LENGTH - 1; c++) {
		ba->commandLine[n++] = *c;
	}
	/* one processor unless the payload asks for more (of two "cpus=" the kernel takes the first) */
	if (!more_cores) {
		for (const char *c = "cpus=1 "; *c && n < BOOT_LINE_LENGTH - 1; c++) {
			ba->commandLine[n++] = *c;
		}
	}
	/* the root is the first RAM disk unless the payload says otherwise */
	int own_root = 0;
	for (const char *c = pi.cmdline; *c; c++) {
		own_root |= starts_with(c, "rd=") && (c == pi.cmdline || c[-1] == ' ');
	}
	if (rd_size != 0 && !own_root) {
		for (const char *c = "rd=md0 "; *c && n < BOOT_LINE_LENGTH - 1; c++) {
			ba->commandLine[n++] = *c;
		}
	}
	if (wdt_armed) {
		for (const char *c = "hv_wdt_pet=1 "; *c && n < BOOT_LINE_LENGTH - 1; c++) {
			ba->commandLine[n++] = *c;
		}
	}
	if (block_enabled) {
		static const char prefix[] = "ufs_shared_pa=0x";
		static const char hex[] = "0123456789abcdef";
		uint64_t address = (uint64_t)(uintptr_t)&block_shared;

		for (const char *c = prefix; *c && n < BOOT_LINE_LENGTH - 1; c++) {
			ba->commandLine[n++] = *c;
		}
		for (int shift = 60; shift >= 0 && n < BOOT_LINE_LENGTH - 1; shift -= 4) {
			ba->commandLine[n++] = hex[(address >> shift) & 0xf];
		}
		if (n < BOOT_LINE_LENGTH - 1) ba->commandLine[n++] = ' ';
	}
	if (battery_requested) {
		static const char prefix[] = "battery_shared_pa=0x";
		static const char hex[] = "0123456789abcdef";
		uint64_t address = (uint64_t)(uintptr_t)&charger_shared;

		for (const char *c = prefix; *c && n < BOOT_LINE_LENGTH - 1; c++) {
			ba->commandLine[n++] = *c;
		}
		for (int shift = 60; shift >= 0 && n < BOOT_LINE_LENGTH - 1; shift -= 4) {
			ba->commandLine[n++] = hex[(address >> shift) & 0xf];
		}
		if (n < BOOT_LINE_LENGTH - 1) ba->commandLine[n++] = ' ';
	}
	for (const char *c = pi.cmdline; *c && n < BOOT_LINE_LENGTH - 1; c++) {
		ba->commandLine[n++] = *c;
	}

	/* --- device tree ---------------------------------------------------- */
	const struct platform *plat = PLAT;
	struct dt_writer w = { .base = (uint8_t *)dt_pa, .cur = (uint8_t *)dt_pa, .depth = 0 };
	uint64_t cntfrq = READ_SYSREG(CNTFRQ_EL0);
	uint64_t ranges[3] = { 0, plat->io_base, plat->io_size };
	uint64_t reg2[2];
	uint8_t seed[64];

	for (unsigned i = 0; i < sizeof(seed); i++) {
		seed[i] = (uint8_t)(READ_SYSREG(CNTVCT_EL0) >> (i & 7)) ^ (uint8_t)(i * 37);
	}

	dt_begin(&w, "device-tree");
	/*
	 * The identity is the iPhone's (model, compatible, target-type ...): iOS user space looks
	 * its device up by these, and its files -- the dyld shared cache to begin with -- are
	 * those of that phone. XNU itself does not care; the hardware is described further down.
	 */
	dt_identity(&w, identity_root, sizeof(identity_root) / sizeof(identity_root[0]), identity_root_data);
	dt_prop_str(&w, "platform-name", "t8015");
	/* what iBoot takes from the factory configuration of a real phone; fixed size fields */
	dt_prop_padded(&w, "serial-number", "RDW00POCOX5P", 32);
	dt_prop_padded(&w, "mlb-serial-number", "RDW00POCOX5PMLB00", 32);
	dt_prop_padded(&w, "model-number", "MQAC2", 32);
	dt_prop_padded(&w, "region-info", "LL/A", 32);
	dt_prop_padded(&w, "regulatory-model-number", "A1865", 32);
	dt_prop_u32(&w, "#address-cells", 2);
	dt_prop_u32(&w, "#size-cells", 2);

	dt_begin(&w, "chosen");
	dt_prop(&w, "random-seed", seed, sizeof(seed));
	dt_prop_u64(&w, "dram-base", phys_base);
	dt_prop_u64(&w, "dram-size", win_size);
	dt_prop_u32(&w, "debug-enabled", 1);
	/* what MobileGestalt answers "main screen scale" from: 3 device pixels per point */
	dt_prop_u32(&w, "display-scale", 3);
	dt_prop_u32(&w, "display-rotation", 0);
	/* how the kernel is to ask the firmware for more cores (PSCI) */
	dt_prop_str(&w, "psci-method", plat->psci_hvc ? "hvc" : "smc");
	/* the time now, by the firmware's clock (the kernel has no real-time clock driver) */
	uint64_t epoch = firmware_epoch();
	if (epoch != 0) {
		dt_prop_u64(&w, "boot-epoch", epoch);
	}
	/*
	 * More of what iBoot reports about the phone. MobileGestalt builds the device identifier
	 * (UDID) from the serial number, the chip ID and the two addresses; when one is missing it
	 * asks its helper for the factory data, is refused and waits forever (and lsd with it).
	 */
	static const uint8_t wifi_address[6] = { 0x02, 0x52, 0x44, 0x57, 0x00, 0x01 };
	static const uint8_t bluetooth_address[6] = { 0x02, 0x52, 0x44, 0x57, 0x00, 0x02 };
	static const uint8_t manifest_hash[48] = { 0x72, 0x65, 0x64, 0x77, 0x6f, 0x6f, 0x64 };
	static const uint8_t no_behavior[16];
	dt_prop_u64(&w, "unique-chip-id", 0x000052445730001ULL);
	dt_prop_u32(&w, "chip-id", 0x8015);
	dt_prop_u32(&w, "board-id", 0x06);
	dt_prop(&w, "mac-address-wifi0", wifi_address, sizeof(wifi_address));
	dt_prop(&w, "mac-address-bluetooth0", bluetooth_address, sizeof(bluetooth_address));
	dt_prop(&w, "boot-manifest-hash", manifest_hash, sizeof(manifest_hash));
	dt_prop(&w, "software-behavior", no_behavior, sizeof(no_behavior));
	dt_prop_str(&w, "firmware-version", "iBoot-8422.100.650");
	dt_prop_u32(&w, "certificate-production-status", 1);
	dt_prop_u32(&w, "certificate-security-mode", 1);
	dt_prop_u32(&w, "effective-production-status-ap", 1);
	dt_prop_u32(&w, "effective-security-mode-ap", 1);
	dt_prop_u32(&w, "secure-boot", 1);
	dt_prop_u32(&w, "production-cert", 1);
	dt_prop_u32(&w, "development-cert", 0);
	dt_prop_u32(&w, "embedded-panic-log-size", PANIC_LOG_SIZE);
	/* An empty but well-formed NVRAM image: IOKit refuses to start without it. */
	static uint8_t nvram_image[NVRAM_BANK_SIZE];
	build_nvram_image(nvram_image);
	dt_prop_u32(&w, "nvram-bank-size", NVRAM_BANK_SIZE);
	dt_prop_u32(&w, "nvram-bank-count", 1);
	dt_prop_u32(&w, "nvram-current-bank", 0);
	dt_prop(&w, "nvram-proxy-data", nvram_image, sizeof(nvram_image));
	dt_begin(&w, "memory-map");
	/*
	 * "RAMDisk" becomes /dev/md0, the root (the kernel and launchd treat
	 * only md0 as a RAM disk boot); "RAMDisk1" becomes /dev/md1. With both
	 * images present the big resident one is the root and the payload's
	 * small one is the second disk.
	 */
	if (rd_size != 0 || rd1_size != 0) {
		uint64_t first[2] = { rd1_size != 0 ? rd1_pa : rd_pa, rd1_size != 0 ? rd1_size : rd_size };
		dt_prop(&w, "RAMDisk", first, sizeof(first));
	}
	if (rd_size != 0 && rd1_size != 0) {
		uint64_t second[2] = { rd_pa, rd_size };
		dt_prop(&w, "RAMDisk1", second, sizeof(second));
	}
	dt_end(&w);
	if (more_cores && plat->timeout_scale != 0) {
		/* multiplies every "machine timeout" of the kernel (machine_timeout_init_with_suffix()) */
		dt_begin(&w, "machine-timeouts");
		dt_prop_u32(&w, "global-scale", plat->timeout_scale);
		dt_end(&w);
	}
	dt_end(&w);

	/*
	 * What iBoot's device tree tells the kernel to do unless told otherwise. The compressor: an
	 * embedded kernel left to itself keeps it for the freezer alone, and with nothing being
	 * compressed the memory is gone twice as fast (2 = VM_PAGER_COMPRESSOR_NO_SWAP, as on a phone).
	 */
	dt_begin(&w, "defaults");
	dt_prop_u32(&w, "kern.vm_compressor", 2);
	dt_end(&w);

	/* the product: screen class, artwork scale, name ... as on the real phone */
	dt_begin(&w, "product");
	dt_identity(&w, identity_product, sizeof(identity_product) / sizeof(identity_product[0]), identity_product_data);
	/*
	 * and its haptics: "closed-loop" (MobileGestalt's DeviceSupportsClosedLoopHaptics) makes iOS play
	 * its vibrations and feedbacks as waveforms on the "Actuator" audio device (the audio plug-in
	 * hands them to the kernel's motor driver); without it iOS looks for an IOKit vibration motor
	 * that the iPhone X does not have, and nothing vibrates.
	 */
	dt_begin(&w, "haptics");
	dt_identity(&w, identity_haptics, sizeof(identity_haptics) / sizeof(identity_haptics[0]), identity_haptics_data);
	dt_end(&w);
	/*
	 * and of its camera what is here: with torch=N the flash (MobileGestalt's camera-flash; without
	 * it Control Center has no flashlight); with cam=5 the node itself, for a camera there is (with it
	 * MobileGestalt's video-camera). The rest of the iPhone's camera is not here, nor said to be.
	 */
	if (torch_requested || camera_requested) {
		dt_begin(&w, "camera");
		if (torch_requested) {
			dt_identity_one(&w, identity_camera, sizeof(identity_camera) / sizeof(identity_camera[0]), identity_camera_data, "flash");
		}
		dt_end(&w);
	}
	dt_end(&w);

	/* IOKit publishes its NVRAM object on this node; without it IOKit asserts. */
	dt_begin(&w, "options");
	dt_end(&w);

	/* Panic log region: RAM outside XNU's window (tail of the payload reservation). */
	uint64_t pram_reg[2] = { PANIC_LOG_BASE, PANIC_LOG_SIZE };
	memset((void *)PANIC_LOG_BASE, 0, PANIC_LOG_SIZE);
	dt_begin(&w, "pram");
	dt_prop(&w, "reg", pram_reg, sizeof(pram_reg));
	dt_end(&w);

	/*
	 * The processors. The first is the one the kernel starts on. With "cpus=N" in its
	 * arguments the kernel takes that one and the next N-1 of this list and starts them
	 * itself (PSCI CPU_ON); "cpumask=M" picks by position, bit 0 being the first. So the
	 * order matters: after the boot core come those whose numbers are nearest to its own
	 * (on the phone, where the kernel boots on the biggest core, 7: the other big ones
	 * 6, 5, 4, then the small ones 3, 2, 1). Only cores that are off are listed: the one
	 * this loader stays on while it watches is not the kernel's, nor any the firmware runs.
	 */
	uint64_t cpu_mpidr[8] = { kernel_mpidr };
	int cpu_count = 1, boot_core = (int)(kernel_mpidr >> plat->core_shift);

	if (more_cores) {
		for (int distance = 1; distance < plat->cores; distance++) {
			for (int side = 0; side < 2; side++) {
				int core = side == 0 ? boot_core + distance : boot_core - distance;
				uint64_t mpidr = (uint64_t)core << plat->core_shift;
				int64_t state;

				if (core < 0 || core >= plat->cores || mpidr == this_mpidr) {
					continue;
				}
				state = psci_call(PSCI_AFFINITY_INFO, mpidr, 0, 0);
				if (state == 1 || state == PSCI_NOT_SUPPORTED) {
					cpu_mpidr[cpu_count++] = mpidr;
				} else if (state >= 0) {
					print("core %x is not off (the firmware says %d): not the kernel's to take\n", mpidr, (uint64_t)state);
				}
			}
		}
		print("cores for the kernel, in the order it takes them:");
		for (int i = 0; i < cpu_count; i++) {
			print(" %x", cpu_mpidr[i]);
		}
		print("\n");
	}

	dt_begin(&w, "cpus");
	for (int i = 0; i < cpu_count; i++) {
		char name[5] = { 'c', 'p', 'u', (char)('0' + i), 0 };

		dt_begin(&w, name);
		dt_prop_str(&w, "device_type", "cpu");
		dt_prop_str(&w, "state", i == 0 ? "running" : "waiting");
		dt_prop_u32(&w, "reg", (uint32_t)cpu_mpidr[i]);
		dt_prop_u32(&w, "cpu-id", (uint32_t)i);
		dt_prop_u64(&w, "timebase-frequency", cntfrq);
		dt_prop_u64(&w, "fixed-frequency", cntfrq);
		dt_prop_u64(&w, "clock-frequency", 1800000000ULL);
		dt_prop_u64(&w, "bus-frequency", 100000000ULL);
		dt_prop_u64(&w, "memory-frequency", 100000000ULL);
		dt_prop_u64(&w, "peripheral-frequency", 24000000ULL);
		if (plat->small_cores & (1u << ((cpu_mpidr[i] >> plat->core_shift) & 31))) {
			dt_prop_u32(&w, "small-core", 1);
		}
		dt_end(&w);
	}
	dt_end(&w);

	dt_begin(&w, "arm-io");
	dt_prop_str(&w, "device_type", plat->name);
	dt_prop(&w, "ranges", ranges, sizeof(ranges));
	dt_prop_u32(&w, "#address-cells", 2);
	dt_prop_u32(&w, "#size-cells", 2);
	/*
	 * With cam=5, where MobileGestalt looks for the cameras (IODeviceTree:/arm-io/isp, its still-camera and
	 * rear-facing-camera, by which SpringBoard shows Camera.app): the iPhone's ISP node, of its
	 * properties only the camera at the back. Neither a compatible nor a device_type: no driver matches it.
	 */
	if (camera_requested) {
		dt_begin(&w, "isp");
		dt_prop_u32(&w, "camera-rear", 1);
		dt_end(&w);
	}
	dt_begin(&w, "gic");
	dt_prop_str(&w, "device_type", "interrupt-controller");
	dt_prop_str(&w, "compatible", "arm,gic-v3");
	uint64_t gic_reg[4] = { plat->gic_dist - plat->io_base, 0x10000, plat->gic_redist - plat->io_base, 0x100000 };
	dt_prop(&w, "reg", gic_reg, sizeof(gic_reg));
	dt_end(&w);
	if (plat->uart != 0) {
		dt_begin(&w, "uart0");
		dt_prop_str(&w, "device_type", "uart");
		dt_prop_str(&w, "compatible", "arm,pl011");
		reg2[0] = plat->uart - plat->io_base;
		reg2[1] = 0x1000;
		dt_prop(&w, "reg", reg2, sizeof(reg2));
		dt_prop_u32(&w, "boot-console", 1);
		dt_end(&w);
	}
	dt_end(&w);

	dt_end(&w);

	uint32_t dt_len = (uint32_t)(w.cur - w.base);
	ba->deviceTreeP = dt_pa - slide;
	ba->deviceTreeLength = dt_len;
	print("device tree %x len %x, boot_args %x, top %x\n", dt_pa, (uint64_t)dt_len, ba_pa, top);
	print("cmdline: %s\n", ba->commandLine);
	if (kernel_mpidr != this_mpidr) {
		print("the kernel will run on core %x (this is core %x)\n", kernel_mpidr, this_mpidr);
	}
	/*
	 * The page the device tree offers as uart0 (MALACHITE_FAKE_UART): zero it and write it
	 * back to memory, since the kernel maps it uncached. Its FR word then reads clear, so
	 * the serial driver never waits for a transmit-ready bit that nothing would set.
	 * Magenta on the panel after a failed boot means it stopped in here; the monitor paints
	 * over it when the loader got through.
	 */
	stage_paint(STAGE_MAGENTA);
	if (plat->uart == MALACHITE_FAKE_UART) {
		volatile uint64_t *page = (volatile uint64_t *)(uintptr_t)MALACHITE_FAKE_UART;

		for (unsigned i = 0; i < 0x1000 / sizeof(*page); i++) {
			page[i] = 0;
		}
		flush_dcache(MALACHITE_FAKE_UART, MALACHITE_FAKE_UART + 0x1000);
	}
	stage_paint(STAGE_CYAN);
	/*
	 * monitor=1: leave a core behind drawing the kernel's own log from
	 * loader_log while the kernel runs on this one. It needs no return, no
	 * heartbeat and no cooperation, which is the only way to see a boot that
	 * never comes back (the system image boot is one).
	 */
	if (monitor_requested && kernel_mpidr == this_mpidr) {
		monitor_start(kernel_live, slide, ustacks_probe);
	}
	print("jumping to %x\n", entry_va + slide);
	stage_paint(STAGE_WHITE);
	stage_corner(STAGE_BLUE, 0, 0, 200);   /* still there = the kernel drew nothing */
	flush_log();
	/* From here on the kernel feeds the watchdog (boot-arg hv_wdt_pet, see loader_return.c in XNU). */
	wdt_set_ms(60000);

	/* --- hand off (UEFI is left resident, see loader_save_ctx) ------------ */
	if (loader_save_ctx() == 0) {
		/*
		 * On real hardware (under the Qualcomm hypervisor) dirty data-cache
		 * lines do not survive the MMU-off round trip. UEFI stays resident,
		 * so everything it owns must be written back to RAM first: clean
		 * every allocated region in the memory map, then this stack again.
		 */
		map_size = sizeof(map_buf);
		if (!EFI_ERROR(BS->get_memory_map(&map_size, map_buf, &map_key, &desc_size, &desc_ver))) {
			for (uint64_t off = 0; off < map_size; off += desc_size) {
				efi_memory_descriptor *d = (efi_memory_descriptor *)(map_buf + off);
				/* loader/boot-services/runtime code and data, ACPI tables; XNU's own window is handled below */
				if (d->phys_start >= win_base && d->phys_start < win_base + win_size) {
					continue;
				}
				if ((d->type >= 1 && d->type <= 6) || d->type == 9 || d->type == 10) {
					clean_dcache(d->phys_start, d->phys_start + (d->pages << 12));
				}
			}
		}
		uint64_t sp_now = (uint64_t)(uintptr_t)__builtin_frame_address(0);
		/* Stay below the top of the UEFI stack: one page past it may be unmapped
		 * (malachite's RAM hole), and a clean of an unmapped line is a fault. */
		clean_dcache(sp_now - 0x2000, sp_now + 0x200);
		flush_dcache(phys_base, top);
		if (checkpoint == CHECKPOINT_SELFTEST) {
			/* Do not enter the kernel at all: exercise only the return path. */
			jump_to_kernel((uint64_t)(uintptr_t)&loader_return_stub, 0);
		}
		if (kernel_mpidr != this_mpidr) {
			int64_t status = run_on_other_cpu(kernel_mpidr, entry_va + slide, ba_pa, kernel_live, slide, kernel_budget);

			wdt_set_ms(WDT_BITE_MS);
			if (status != 0) {
				/* a kernel that hung may have left its own transfer list in the controller */
				hc_take_back(status == OTHER_CPU_HUNG ? "the kernel hung" : "the kernel did not start");
			}
			if (status == OTHER_CPU_HUNG) {
				/*
				 * Bring-up: the kernel stopped showing signs of life. What it
				 * said last is the only thing that explains why, so draw that
				 * (the log the loader collected on the way out) and mark the
				 * state with a red square in a corner, without painting over
				 * the text.
				 */
				uint64_t n = loader_ctx[CTX_LOG_LEN];

				print("THE KERNEL HUNG on core %x: no sign of life for %d seconds; its log follows\n", kernel_mpidr,
				    (uint64_t)SILENCE_SECONDS);
				set_result("hung", n, 0);
				fb_render_log((const char *)(uintptr_t)loader_ctx[CTX_LOG_PA], n, 0xFF00FF00u);
				stage_corner(STAGE_RED, 1, 1, 200);
				for (;;) {
					__asm__ volatile("wfi");
				}
			} else if (status != 0) {
				/* the kernel was told it would be on that core (return path, device tree): no second try */
				stage_paint(STAGE_YELLOW);
				stage_corner(0xFF000000u, 1, status == OTHER_CPU_NOT_STARTED ? 1 : 0, 200);
				if (status == OTHER_CPU_NOT_STARTED) {
					print("core %x was started but never arrived\n", kernel_mpidr);
				} else {
					print("core %x did not start: PSCI error %d\n", kernel_mpidr, (uint64_t)-status);
				}
				set_result("no-such-core", (uint64_t)(status < 0 ? -status : status), 0);
				for (;;) {
					__asm__ volatile("wfi");
				}
			}
		} else {
			jump_to_kernel(entry_va + slide, ba_pa);
		}
	}

	/* --- the kernel came back ------------------------------------------- */
	if (kret_hold) {
		/*
		 * Bring-up: the kernel came back, and its log is where the return
		 * stub left it. Draw the tail of it on the panel ourselves -- the EFI
		 * console cannot show it, and the publish path to the firmware has
		 * been unreliable -- then stop. The red square says it did return.
		 * The two lines written on top are the return record itself: an
		 * empty log is otherwise indistinguishable from a broken one.
		 */
		char buf[96];
		unsigned n = 0;
		const char *s;

		fb_render_log((const char *)(uintptr_t)loader_ctx[CTX_LOG_PA],
		    loader_ctx[CTX_LOG_LEN], 0xFF00FF00u);
		s = "ret reason=";
		while (*s) buf[n++] = *s++;
		n += fb_u64(buf + n, loader_ctx[CTX_REASON]);
		s = " esr=";
		while (*s) buf[n++] = *s++;
		n += fb_hex(buf + n, loader_ctx[CTX_ESR]);
		s = " elr=";
		while (*s) buf[n++] = *s++;
		n += fb_hex(buf + n, loader_ctx[CTX_ELR]);
		buf[n] = 0;
		fb_line(0, buf, 0xFFFFFFFFu);

		n = 0;
		s = "far=";
		while (*s) buf[n++] = *s++;
		n += fb_hex(buf + n, loader_ctx[CTX_FAR]);
		s = " log=";
		while (*s) buf[n++] = *s++;
		n += fb_u64(buf + n, loader_ctx[CTX_LOG_LEN]);
		s = " bytes at ";
		while (*s) buf[n++] = *s++;
		n += fb_hex(buf + n, loader_ctx[CTX_LOG_PA]);
		s = " el=";
		while (*s) buf[n++] = *s++;
		n += fb_hex(buf + n, other_cpu_el);
		buf[n] = 0;
		fb_line(1, buf, 0xFFFFFFFFu);

		stage_corner(STAGE_RED, 1, 1, 100);
		for (;;) {
			__asm__ volatile("wfi");
		}
	}
	wdt_set_ms(WDT_BITE_MS);
	hc_take_back("the kernel came back");   /* before anything here touches the storage */
	if (hc_known) {
		flush_dcache((uint64_t)(uintptr_t)&block_shared.kernel_native,
		    (uint64_t)(uintptr_t)&block_shared.kernel_native + sizeof(block_shared.kernel_native));
		print("ufs: the kernel put its own list in %d times and took it out %d times\n",
		    (uint64_t)block_shared.kernel_native.switched_in, (uint64_t)block_shared.kernel_native.switched_out);
	}
	if (block_write_requested) {
		print("ufs: %d writes into darwin, %d bytes, read back the same; %d refused\n", block_writes,
		    block_write_bytes, block_writes_refused);
	}
	/* ... and its other cores should all be off again: the next kernel cannot start one that is not */
	for (int i = 1; i < cpu_count; i++) {
		int64_t state = psci_call(PSCI_AFFINITY_INFO, cpu_mpidr[i], 0, 0);

		if (state != 1 && state != PSCI_NOT_SUPPORTED) {
			print("THE KERNEL LEFT CORE %x RUNNING (the firmware says %d): restart before running another\n", cpu_mpidr[i],
			    (uint64_t)state);
		}
	}
	recording_data = NULL;
	recording_len = 0;
	if (kernel_live != NULL && kernel_live->recording != 0 && checkpoint != CHECKPOINT_SELFTEST) {
		const uint64_t *recording = (const uint64_t *)(kernel_live->recording + slide);

		if (recording[0] != 0 && recording[1] > 24 && recording[1] <= (1ULL << 30)) {
			recording_data = (const char *)recording[0];
			recording_len = recording[1];
			print("the kernel left a screen recording: %d bytes at %x\n", recording_len, recording[0]);
		}
	}
	sound_data = NULL;
	sound_len = 0;
	if (kernel_live != NULL && kernel_live->magic2 == KERNEL_LIVE_MAGIC2 && kernel_live->sound != 0 &&
	    checkpoint != CHECKPOINT_SELFTEST) {
		const uint64_t *sound = (const uint64_t *)(kernel_live->sound + slide);

		if (sound[0] != 0 && sound[1] > 24 && sound[1] <= (1ULL << 30)) {
			sound_data = (const char *)sound[0];
			sound_len = sound[1];
			print("the kernel left a sound recording: %d bytes at %x\n", sound_len, sound[0]);
		}
	}
	const char *klog = (const char *)loader_ctx[CTX_LOG_PA];
	uint64_t klog_len = loader_ctx[CTX_LOG_LEN];
	uint64_t reason = loader_ctx[CTX_REASON];
	if (checkpoint == CHECKPOINT_SELFTEST) {
		print("return-path self test passed\n");
		set_result("selftest-ok", 0, 0);
		klog = NULL;
		klog_len = 0;
	} else {
		print("kernel returned: log at %x, %d bytes\n", (uint64_t)(uintptr_t)klog, klog_len);
		if (reason == 2) {
			print("STOPPED AT CHECKPOINT %d\n", loader_ctx[CTX_ESR]);
			set_result("checkpoint", loader_ctx[CTX_ESR], 0);
		} else if (reason == 1) {
			print("EARLY KERNEL EXCEPTION: esr=%x elr=%x far=%x lr=%x sp=%x\n", loader_ctx[CTX_ESR], loader_ctx[CTX_ELR],
			    loader_ctx[CTX_FAR], loader_ctx[CTX_LR], loader_ctx[CTX_KSP]);
			print("  (pa-va slide %x: subtract it from physical addresses to symbolicate)\n", slide);
			set_result("early-exception", 0, loader_ctx[CTX_ELR]);
			klog_len = klog_len > (1u << 20) ? 0 : klog_len;
		} else {
			set_result("returned", klog_len, 0);
		}
	}
	write_logs(klog, klog_len);
	return 1;
}

/* ------------------------------------------------------------------------ */
/* USB command channel: a small fastboot-protocol server.                    */
/*                                                                          */
/* Host side (stock `fastboot` tool):                                        */
/*   fastboot stage payload.bin    download a new "XNUP" payload            */
/*   fastboot oem run [N]          run its kernel (optionally stop at N)    */
/*   fastboot getvar result        blocks until the kernel is back          */
/*   fastboot get_staged log.txt   fetch loader + kernel log                */
/*   fastboot oem hang             stop petting the watchdog (test)         */
/*   fastboot reboot               cold reset                               */

#define USB_EP_OUT   0x01
#define USB_EP_IN    0x81
#define USB_CHUNK    (1024 * 1024)

static usb_device_protocol *USB;
static int download_to_ramdisk;     /* set by "oem ramdisk" for the one download that follows */
static uint8_t *usb_rx_buf, *usb_tx_buf;
static int usb_connected;

static const uint8_t usb_dev_desc[18] = { 18, 1, 0x10, 0x02, 0, 0, 0, 64, 0xd1, 0x18, 0x0d, 0xd0, 0x00, 0x01, 1, 2, 3, 1 };
static const uint8_t usb_ss_dev_desc[18] = { 18, 1, 0x00, 0x03, 0, 0, 0, 9, 0xd1, 0x18, 0x0d, 0xd0, 0x00, 0x01, 1, 2, 3, 1 };
static const uint8_t usb_cfg_desc[32] = {
	9, 2, 32, 0, 1, 1, 0, 0x80, 0x50,
	9, 4, 0, 0, 2, 0xff, 0x42, 0x03, 4,   /* fastboot interface */
	7, 5, USB_EP_IN, 2, 0x00, 0x02, 0,
	7, 5, USB_EP_OUT, 2, 0x00, 0x02, 0,
};
static const uint8_t usb_ss_cfg_desc[44] = {
	9, 2, 44, 0, 1, 1, 0, 0x80, 0x10,
	9, 4, 0, 0, 2, 0xff, 0x42, 0x03, 4,
	7, 5, USB_EP_IN, 2, 0x00, 0x04, 0,   6, 0x30, 4, 0, 0, 0,
	7, 5, USB_EP_OUT, 2, 0x00, 0x04, 0,  6, 0x30, 4, 0, 0, 0,
};
static const uint8_t usb_qualifier[10] = { 10, 6, 0x00, 0x02, 0xff, 0xff, 0xff, 64, 1, 0 };
static const uint8_t usb_bos[42] = {
	5, 0x0f, 42, 0, 3,
	7, 0x10, 0x02, 0x06, 0, 0, 0,
	10, 0x10, 0x03, 0x00, 0x0e, 0x00, 0x01, 0x07, 0x65, 0x00,
	20, 0x10, 0x0a, 0x00, 0x01, 0, 0, 0, 0x00, 0x11, 0, 0, 0x30, 0x40, 0x0a, 0x00, 0xb0, 0x40, 0x0a, 0x00,
};
static const uint8_t usb_str0[4] = { 4, 3, 0x09, 0x04 };
static const uint8_t usb_str_mfr[8] = { 8, 3, 'X', 0, 'N', 0, 'U', 0 };
static const uint8_t usb_str_prod[20] = { 20, 3, 'x', 0, 'n', 0, 'u', 0, 'l', 0, 'o', 0, 'a', 0, 'd', 0, 'e', 0, 'r', 0 };
static const uint8_t usb_str_serial[20] = { 20, 3, 'x', 0, 'n', 0, 'u', 0, 'l', 0, 'o', 0, 'a', 0, 'd', 0, 'e', 0, 'r', 0 };
static const uint8_t usb_str_iface[18] = { 18, 3, 'f', 0, 'a', 0, 's', 0, 't', 0, 'b', 0, 'o', 0, 'o', 0, 't', 0 };

static void EFIAPI
usb_dummy_notify(void *event, void *ctx)
{
}

static int
usb_start(void)
{
	static const efi_guid usb_guid = QCOM_USB_DEVICE_GUID;
	static const efi_guid init_guid = QCOM_USB_INIT_EVENT_GUID;
	static const void *cfg = usb_cfg_desc, *ss_cfg = usb_ss_cfg_desc;
	static const void *strings[5] = { usb_str0, usb_str_mfr, usb_str_prod, usb_str_serial, usb_str_iface };
	static usb_device_descriptor_set set;
	void *event;

	/* Ask the platform to bring the controller up in peripheral mode (as the stock fastboot does). */
	if (!EFI_ERROR(BS->create_event_ex(0x200 /* EVT_NOTIFY_SIGNAL */, 8 /* TPL_CALLBACK */, usb_dummy_notify, NULL,
	    &init_guid, &event))) {
		BS->signal_event(event);
		BS->close_event(event);
	}
	if (EFI_ERROR(BS->locate_protocol(&usb_guid, NULL, (void **)&USB))) {
		print("usb: device protocol not found\n");
		return 0;
	}
	set.device_descriptor = usb_dev_desc;
	set.descriptors = &cfg;
	set.ss_device_descriptor = usb_ss_dev_desc;
	set.ss_descriptors = &ss_cfg;
	set.device_qualifier = usb_qualifier;
	set.bos = usb_bos;
	set.string_count = 5;
	set.strings = strings;
	efi_status s = USB->start_ex(&set);
	if (EFI_ERROR(s)) {
		print("usb: start failed %x\n", s);
		return 0;
	}
	if (EFI_ERROR(USB->allocate_transfer_buffer(USB_CHUNK, (void **)&usb_rx_buf)) ||
	    EFI_ERROR(USB->allocate_transfer_buffer(USB_CHUNK, (void **)&usb_tx_buf))) {
		print("usb: no transfer buffers\n");
		return 0;
	}
	print("usb: started\n");
	return 1;
}

/*
 * Pump controller events until a transfer on `endpoint` finishes.
 * Returns the byte count, or -1 if the transfer was cancelled or the cable
 * state changed. Keeps the watchdog fed while idle.
 */
static int64_t
usb_wait(uint8_t endpoint)
{
	/* static: a long transfer is many short waits, and the watchdog must be fed across them */
	static uint64_t last_pet;
	uint64_t freq = READ_SYSREG(CNTFRQ_EL0), began = READ_SYSREG(CNTVCT_EL0);

	for (;;) {
		uint32_t msg = UsbDeviceEventNoEvent;
		uint64_t size = 0;
		usb_device_event_data data;

		USB->handle_event(&msg, &size, &data);
		if (msg == UsbDeviceEventDeviceStateChange) {
			usb_connected = (data.device_state == UsbDeviceStateConnected);
			return -1;
		}
		/* with a kernel running, a host that went away must not keep this core from watching it */
		if (running_live != NULL && READ_SYSREG(CNTVCT_EL0) - began > 3 * freq) {
			return -1;
		}
		if (msg == UsbDeviceEventTransferNotification && data.transfer.endpoint_index == endpoint) {
			return data.transfer.status == UsbDeviceTransferStatusCompleteOK ? (int64_t)data.transfer.bytes_completed : -1;
		}
		if (READ_SYSREG(CNTVCT_EL0) - last_pet > freq) {
			last_pet = READ_SYSREG(CNTVCT_EL0);
			wdt_pet();
		}
	}
}

static int usb_rx_queued;       /* usb_poll_command() has left the receive for the next command with the controller */

static int64_t
usb_rx(uint8_t *buf, uint64_t len)
{
	if (usb_rx_queued) {
		usb_rx_queued = 0;      /* (every command is received the same way, into the same buffer) */
	} else if (EFI_ERROR(USB->send(USB_EP_OUT, len, buf))) {
		return -1;
	}
	return usb_wait(USB_EP_OUT);
}

static int64_t
usb_tx(const uint8_t *data, uint64_t len)
{
	if (data != usb_tx_buf) {
		memcpy(usb_tx_buf, data, len);
	}
	if (EFI_ERROR(USB->send(USB_EP_IN, len, usb_tx_buf))) {
		return -1;
	}
	return usb_wait(USB_EP_IN);
}

static void
fb_reply(const char *code, const char *text)
{
	uint32_t n = 0;
	for (; *code; code++) {
		usb_tx_buf[n++] = (uint8_t)*code;
	}
	for (; *text && n < 63; text++) {
		usb_tx_buf[n++] = (uint8_t)*text;
	}
	usb_tx(usb_tx_buf, n);
}

static void
fb_reply_data(uint64_t len)
{
	char msg[13] = "DATA00000000";
	for (int i = 0; i < 8; i++) {
		msg[4 + i] = "0123456789abcdef"[(len >> (28 - 4 * i)) & 0xf];
	}
	usb_tx((const uint8_t *)msg, 12);
}

static int
starts_with(const char *s, const char *prefix)
{
	while (*prefix) {
		if (*s++ != *prefix++) {
			return 0;
		}
	}
	return 1;
}

/*
 * One command from the host. While a kernel runs on another core (running_live) only what does
 * not disturb it: questions, the screen, the log so far, and "oem stop".
 */
static void
fb_command(char *cmd)
{
	int busy = running_live != NULL;

	{
		if (busy && (starts_with(cmd, "oem ramdisk") || starts_with(cmd, "download:") || starts_with(cmd, "oem run") ||
		    starts_with(cmd, "oem selftest") || starts_with(cmd, "oem hang") || starts_with(cmd, "oem recording") ||
		    starts_with(cmd, "oem sound") || starts_with(cmd, "oem clearscreen") || starts_with(cmd, "oem memmap"))) {
			fb_reply("FAIL", "a kernel is running (oem stop ends it)");
		} else if (starts_with(cmd, "oem stop")) {
			/* the kernel looks at this once a second and comes back as it does when its time is up */
			if (busy) {
				((struct kernel_live *)(uintptr_t)running_live)->stop = 1;
			}
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "getvar:")) {
			const char *var = cmd + 7;
			if (str_eq(var, "product")) {
				fb_reply("OKAY", "xnuloader");
			} else if (str_eq(var, "version")) {
				fb_reply("OKAY", "0.5");
			} else if (str_eq(var, "max-download-size")) {
				fb_reply("OKAY", download_to_ramdisk ? "0xffffffff" : "0x03f00000");
			} else if (str_eq(var, "result")) {
				fb_reply("OKAY", last_result);
			} else if (str_eq(var, "screen") && SCREEN.base != 0) {
				/* width height bytes-per-row */
				uint32_t mark = log_len;
				print("%d %d %d", (uint64_t)SCREEN.width, (uint64_t)SCREEN.height, (uint64_t)SCREEN.stride);
				log_buf[log_len] = 0;
				fb_reply("OKAY", log_buf + mark);
				log_len = mark;
			} else {
				fb_reply("OKAY", "");
			}
		} else if (starts_with(cmd, "oem ramdisk")) {
			/* "oem ramdisk": the next download is a root image for the resident area; "oem ramdisk none" drops it */
			struct payload_info pi;

			if (starts_with(cmd, "oem ramdisk none")) {
				resident_rd_size = 0;
				fb_reply("OKAY", "");
				return;
			}
			parse_payload(&pi, 0);
			log_len = 0;
			if (!choose_window(&pi) || win_size <= RESIDENT_RD_OFFSET + RESIDENT_RD_RESERVE) {
				fb_reply("FAIL", "no memory window");
				return;
			}
			download_to_ramdisk = 1;
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "download:")) {
			uint64_t total = parse_number(cmd + 9, 16), got = 0;
			uint64_t limit = PAYLOAD_MAX_SIZE - 0x100000;
			uint8_t *dest = (uint8_t *)PAYLOAD_BASE;
			int to_ramdisk = download_to_ramdisk;

			download_to_ramdisk = 0;
			if (to_ramdisk) {
				limit = win_size - RESIDENT_RD_OFFSET - RESIDENT_RD_RESERVE;
				dest = (uint8_t *)(win_base + RESIDENT_RD_OFFSET);
				resident_rd_size = 0;
			}
			if (total == 0 || total > limit) {
				fb_reply("FAIL", "bad size");
				return;
			}
			fb_reply_data(total);
			while (got < total) {
				uint64_t want = total - got > USB_CHUNK ? USB_CHUNK : total - got;
				int64_t r = usb_rx(usb_rx_buf, want);
				if (r <= 0) {
					break;
				}
				memcpy(dest + got, usb_rx_buf, (size_t)r);
				got += (uint64_t)r;
			}
			if (got == total) {
				if (to_ramdisk) {
					resident_rd_size = total;
				}
				fb_reply("OKAY", "");
			} else {
				fb_reply("FAIL", "short download");
			}
		} else if (starts_with(cmd, "upload")) {
			uint64_t sent = 0;
			fb_reply_data(staged_len);
			while (sent < staged_len) {
				uint64_t chunk = staged_len - sent > USB_CHUNK ? USB_CHUNK : staged_len - sent;
				if (usb_tx((const uint8_t *)staged_data + sent, chunk) < 0) {
					break;
				}
				sent += chunk;
			}
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "oem screenshot")) {
			/* stage the raw framebuffer; "getvar screen" gives its geometry */
			if (SCREEN.base == 0) {
				fb_reply("FAIL", "no display");
				return;
			}
			staged_data = (const char *)(uintptr_t)SCREEN.base;
			staged_len = (uint64_t)SCREEN.stride * SCREEN.height;
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "oem recording")) {
			/* stage what the kernel's display driver recorded (boot-arg rec_secs) */
			if (recording_data == NULL) {
				fb_reply("FAIL", "no recording");
				return;
			}
			staged_data = recording_data;
			staged_len = recording_len;
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "oem sound")) {
			/* stage what the kernel recorded of the sound (boot-arg rec_sound) */
			if (sound_data == NULL) {
				fb_reply("FAIL", "no sound recording");
				return;
			}
			staged_data = sound_data;
			staged_len = sound_len;
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "oem clearscreen")) {
			if (SCREEN.base != 0) {
				memset((void *)(uintptr_t)SCREEN.base, 0, (size_t)SCREEN.stride * SCREEN.height);
			}
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "oem run") || starts_with(cmd, "oem selftest")) {
			int selftest = starts_with(cmd, "oem selftest");
			const char *arg = cmd + 7;
			while (*arg == ' ') {
				arg++;
			}
			int have_cp = selftest || (*arg >= '0' && *arg <= '9');
			uint64_t cp = selftest ? CHECKPOINT_SELFTEST : parse_number(arg, 10);

			set_result("running", cp, 0);
			fb_reply("OKAY", "");
			log_len = 0;
			print("== XNULOADER run (usb) ==\n");
			if (!run_kernel(have_cp, cp)) {
				set_result("not-started", 0, 0);
				compose_logs(NULL, 0);
			}
		} else if (starts_with(cmd, "oem hang")) {
			fb_reply("OKAY", "watchdog test: not petting any more");
			for (;;) {
			}
		} else if (starts_with(cmd, "oem memmap")) {
			/* the firmware's memory map into the log (then "oem log" and fetch it) */
			print_memory_map();
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "oem log")) {
			if (busy) {
				compose_live_log(running_live, running_slide);
			} else {
				compose_logs(NULL, 0);
			}
			fb_reply("OKAY", "");
		} else if (starts_with(cmd, "reboot") || starts_with(cmd, "oem reboot")) {
			fb_reply("OKAY", "");
			BS->stall(200000);
			ST->rt->reset_system(0 /* EfiResetCold */, 0, 0, NULL);
		} else {
			fb_reply("FAIL", "unknown command");
		}
	}
}

/*
 * A kernel is running on another core and this one watches it: see whether the host has said
 * something meanwhile, without waiting for it to. This is how a run can be asked to end, and
 * the screen and the log be had while it lasts.
 */
static void
usb_poll_command(void)
{
	uint32_t msg = UsbDeviceEventNoEvent;
	uint64_t size = 0, n;
	usb_device_event_data data;
	char cmd[128];

	if (USB == NULL) {
		return;         /* this run was not started over USB */
	}
	if (!usb_rx_queued && usb_connected && !EFI_ERROR(USB->send(USB_EP_OUT, 511, usb_rx_buf))) {
		usb_rx_queued = 1;
	}
	USB->handle_event(&msg, &size, &data);
	if (msg == UsbDeviceEventDeviceStateChange) {
		usb_connected = (data.device_state == UsbDeviceStateConnected);
		usb_rx_queued = 0;
		return;
	}
	if (msg != UsbDeviceEventTransferNotification || data.transfer.endpoint_index != USB_EP_OUT) {
		return;
	}
	usb_rx_queued = 0;
	if (data.transfer.status != UsbDeviceTransferStatusCompleteOK || data.transfer.bytes_completed == 0) {
		return;
	}
	n = data.transfer.bytes_completed < sizeof(cmd) - 1 ? data.transfer.bytes_completed : sizeof(cmd) - 1;
	memcpy(cmd, usb_rx_buf, (size_t)n);
	cmd[n] = 0;
	fb_command(cmd);
}

static void
usb_command_loop(void)
{
	screen_quiet = 1;
	for (;;) {
		char cmd[128];
		int64_t n;

		if (!usb_connected) {
			usb_wait(0xff); /* returns on the next cable state change */
			continue;
		}
		n = usb_rx(usb_rx_buf, 511);
		if (n <= 0) {
			continue;
		}
		if (n > (int64_t)sizeof(cmd) - 1) {
			n = sizeof(cmd) - 1;
		}
		memcpy(cmd, usb_rx_buf, (size_t)n);
		cmd[n] = 0;
		fb_command(cmd);
	}
}

/* ------------------------------------------------------------------------ */

/*
 * QEMU's "ramfb" display shows whatever guest memory it is told to, in any size; the firmware
 * only offers a few small landscape modes of it. So we point it at memory of our own with the
 * shape of the iPhone's screen, through the fw_cfg file "etc/ramfb" (the firmware's own mode
 * is simply replaced). In QEMU the display is then exactly what iOS expects; on the real phone
 * the kernel's display driver scales that picture to the panel.
 */
#define PHONE_WIDTH     1125            /* the screen of the iPhone X, whose identity we carry */
#define PHONE_HEIGHT    2436
/* HACKIOS_RAMFB_HEIGHT: QEMU's ramfb refuses a mode taller than 2048 (bochs-vbe's
 * VBE_DISPI_MAX_YRES), so the panel is asked for 2048 rows and the kernel scales the
 * 1125x2436 display into it -- the same thing it does on a real phone. */
#define RAMFB_HEIGHT    2048
#define FW_CFG_BASE     0x09020000ULL   /* QEMU virt: data at +0, selector at +8, DMA address at +16 */
#define FW_CFG_FILE_DIR 0x19
#define FW_CFG_DMA_SELECT 0x08
#define FW_CFG_DMA_WRITE  0x10

static uint32_t
be32(uint32_t v)
{
	return __builtin_bswap32(v);
}

static void
fw_cfg_read(void *buf, uint32_t len)
{
	for (uint32_t i = 0; i < len; i++) {
		((uint8_t *)buf)[i] = *(volatile uint8_t *)FW_CFG_BASE;
	}
}

static void
ramfb_phone_screen(void)
{
	static volatile struct {
		uint64_t addr;
		uint32_t fourcc, flags, width, height, stride;
	} __attribute__((packed)) cfg;
	/* the device writes the control word back: it must be read from memory after the request,
	 * not from a register the compiler kept its own copy in */
	static volatile struct {
		uint32_t control, length;
		uint64_t address;
	} dma;
	struct {
		uint32_t size;
		uint16_t select, reserved;
		char name[56];
	} file;
	uint32_t count, select = 0;
	uint64_t fb = 0, bytes = (uint64_t)PHONE_WIDTH * 4 * RAMFB_HEIGHT;

	*(volatile uint16_t *)(FW_CFG_BASE + 8) = __builtin_bswap16(FW_CFG_FILE_DIR);
	fw_cfg_read(&count, sizeof(count));
	count = be32(count);
	for (uint32_t i = 0; i < count && i < 256 && select == 0; i++) {
		fw_cfg_read(&file, sizeof(file));
		if (str_eq(file.name, "etc/ramfb")) {
			select = __builtin_bswap16(file.select);
		}
	}
	if (select == 0 || EFI_ERROR(BS->allocate_pages(AllocateAnyPages, EfiLoaderData, (bytes + 0xFFF) >> 12, &fb))) {
		return;
	}
	memset((void *)(uintptr_t)fb, 0, (size_t)bytes);
	cfg.addr = __builtin_bswap64(fb);
	cfg.fourcc = be32(0x34325258);          /* 'XR24': blue, green, red, unused */
	cfg.flags = 0;
	cfg.width = be32(PHONE_WIDTH);
	cfg.height = be32(RAMFB_HEIGHT);
	cfg.stride = be32(PHONE_WIDTH * 4);
	dma.control = be32(select << 16 | FW_CFG_DMA_SELECT | FW_CFG_DMA_WRITE);
	dma.length = be32(sizeof(cfg));
	dma.address = __builtin_bswap64((uint64_t)(uintptr_t)&cfg);
	*(volatile uint64_t *)(FW_CFG_BASE + 16) = __builtin_bswap64((uint64_t)(uintptr_t)&dma);
	if (dma.control != 0) {
		/* HACKIOS: this is the value we wrote ourselves; nothing writes back into it, so it
		 * says nothing about whether the request worked. QEMU's ramfb refuses a mode taller
		 * than 2048 (VBE_DISPI_MAX_YRES), and the mode it takes is the one in the panel. */
		print("ramfb: control %x after the request (the mode is taken as it stands)\n",
		    (uint64_t)be32(dma.control));
	}
	SCREEN.base = fb;
	SCREEN.width = PHONE_WIDTH;
	SCREEN.height = RAMFB_HEIGHT;
	SCREEN.stride = PHONE_WIDTH * 4;
}

/* Hand this loader's log to the firmware (see XnuLoader.c): the EFI console has no
 * output device on the malachite port yet, the firmware's DEBUG console does. */
static void
publish_log(void)
{
	volatile uint32_t *mbox = (volatile uint32_t *)(uintptr_t)LOG_MBOX_BASE;
	uint32_t n = log_len < LOG_MBOX_SIZE ? log_len : LOG_MBOX_SIZE;

	mbox[0] = LOG_MBOX_MAGIC;
	mbox[1] = n;
	memcpy((void *)(uintptr_t)(LOG_MBOX_BASE + 8), log_buf, n);
	((volatile char *)(uintptr_t)(LOG_MBOX_BASE + 8))[n] = 0;
}

efi_status EFIAPI
efi_main(efi_handle image, efi_system_table *st)
{
	static const efi_guid gop_guid = EFI_GOP_GUID;
	struct payload_info pi;

#ifdef MALACHITE_ENTRY_PAINT
	/* First instruction of the loader: no EFI call has been made yet. Magenta here means
	 * the firmware really transferred control; anything later is a hang after this point. */
	{
		volatile uint32_t *px = (volatile uint32_t *)(uintptr_t)0xFD91F000;
		for (uint64_t i = 0; i < (uint64_t)1248 * 2712; i++) {
			px[i] = 0xFFFF00FFu;
		}
	}
#endif

	ST = st;
	BS = st->bs;
	IMAGE = image;

#ifdef MALACHITE_QUIET
	/* Bring-up: the EFI console's output path faults on this port; log only. */
	screen_quiet = 1;
#endif
	BS->set_watchdog_timer(0, 0, 0, NULL);
	print("== XNULOADER v3 ==\n");
	print("CurrentEL=%x MIDR=%x MMFR0=%x CNTFRQ=%d image=%x\n", READ_SYSREG(CurrentEL) >> 2, READ_SYSREG(MIDR_EL1),
	    READ_SYSREG(ID_AA64MMFR0_EL1), READ_SYSREG(CNTFRQ_EL0), (uint64_t)(uintptr_t)&__ImageBase);

	PLAT = &platform_qemu_virt;
	if (EFI_ERROR(BS->locate_protocol(&gop_guid, NULL, (void **)&GOP)) || GOP->mode == NULL ||
	    GOP->mode->info == NULL || GOP->mode->fb_base == 0) {
		GOP = NULL;                     /* no display (QEMU without -device ramfb) */
	} else {
		SCREEN.base = GOP->mode->fb_base;
		SCREEN.width = GOP->mode->info->width;
		SCREEN.height = GOP->mode->info->height;
		SCREEN.stride = GOP->mode->info->pixels_per_scanline * 4;
		for (unsigned i = 0; i < sizeof(platforms) / sizeof(platforms[0]); i++)
			if (platforms[i]->fb_base == SCREEN.base)
				PLAT = platforms[i];
		/*
		 * malachite's LK places the scanout buffer at the top of the first 4 GiB and the
		 * exact address depends on the RAM size; keep it away from the QEMU ramfb path
		 * (fw_cfg does not exist on a phone).
		 */
		if (PLAT == &platform_qemu_virt && SCREEN.base >= 0xF0000000ULL && SCREEN.base < 0x100000000ULL)
			PLAT = &platform_malachite;
		if (PLAT == &platform_qemu_virt)
			ramfb_phone_screen();
		print("display %d x %d at %x\n", (uint64_t)SCREEN.width, (uint64_t)SCREEN.height, SCREEN.base);
	}
	print("platform %s\n", PLAT->name);
	stage_paint(STAGE_BLUE);

	install_exception_hook();
	wdt_arm();

	int have_payload = parse_payload(&pi, 0);
	stage_paint(have_payload ? STAGE_CYAN : STAGE_RED);
	if (have_payload && pi.nokernel) {
		/* Bring-up: show what the payload holds, hand the log to the firmware and return.
		 * The EFI console has no output device on this port yet; the firmware's own
		 * DEBUG console does (FrameBufferSerialPortLib), so it prints this for us. */
		parse_payload(&pi, 1);
		print("nokernel: payload read; not entering the kernel\n");
		print("display %d x %d, stride %d, platform %s\n", (uint64_t)SCREEN.width, (uint64_t)SCREEN.height,
		    (uint64_t)SCREEN.stride, PLAT->name);
		/* Green on the visible part of the panel: the loader got this far. The console
		 * cursor lives at the end of the whole reserved region, far past this fill. */
		if (SCREEN.base != 0 && SCREEN.stride != 0 && SCREEN.height != 0) {
			volatile uint32_t *px = (volatile uint32_t *)(uintptr_t)SCREEN.base;
			uint64_t count = (uint64_t)(SCREEN.stride / 4) * SCREEN.height;
			for (uint64_t i = 0; i < count; i++) {
				px[i] = 0xFF00FF00u;
			}
		}
		publish_log();
		return 0;
	}
	if (have_payload && pi.usb_mode && usb_start()) {
		flush_log();
		usb_command_loop();
	}

	/* One-shot mode: run the kernel that came with the image, then reset. */
	if (have_payload) {
		stage_paint(STAGE_MAGENTA);
		int ran = run_kernel(0, 0);

		/* Cyan only when the kernel really ran and came back; every way to
		 * fail before the jump leaves red, and a green panel is then the
		 * kernel's own (it never returned), so a photo tells them apart. */
		stage_paint(ran ? STAGE_CYAN : STAGE_RED);
		if (pi.ret) {
			/* Bring-up: hand the log to the firmware to print (XnuLoader.c). */
			publish_log();
			return 0;
		}
		if (pi.hold) {
			/* A device with no USB link yet: leave the log where it can be photographed. */
			print("holding (payload hold=1): power-cycle to leave\n");
			for (;;) {
				__asm__ volatile("wfi");
			}
		}
	}
	reboot();
	return 0;
}
