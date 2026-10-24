# malachite: the POCO X7 (MT6878)

The first MediaTek port in this tree: the Xiaomi POCO X7 / Redmi Note 14 Pro 5G
(`malachite`), with the MediaTek MT6878 (Dimensity 7300-Ultra). It boots iOS 16.5
userland — launchd and lsd run, the boot then stalls in lsd — and it is where the
loader's log monitor and saved-log facilities were worked out.

## The device

| Item | Value |
| --- | --- |
| SoC | MediaTek MT6878 (Dimensity 7300-Ultra): 4x Cortex-A55 + 4x Cortex-A78 |
| Cores | 8; MPIDR numbers them in the second affinity field (`cpu@N reg = <0xN00>`) |
| GIC | GICv3, distributor `0x0C000000`, redistributor `0x0C040000` |
| PSCI | over SMC |
| RAM | 12 GiB |
| Framebuffer | LK's scanout buffer at `0xFD91F000`, stride 1248 |
| Display | 1220x2712, top 120 px and the rounded sides are not safe for text |
| Bootloader | MediaTek LK, unlocked; `fastboot flash boot_a` works, some vendor commands wedge it |
| UART | none |

The platform entry is `platform_malachite` in `xnuloader/loader.c`. XNU must run on
core 0 (a core started by PSCI is left at EL2 and userland self-tests fail there).

## Boot chain

```
LK -> boot.img (BootShim + UEFI firmware volume + XNUP payload)
   -> UEFI (uefi-sheng, malachite platform)
   -> BootManagerLib/XnuLoader.c: start loader.efi from the XNUP payload
   -> xnuloader: load the kernel, build the device tree and boot_args, jump
   -> XNU: iOS 16.5 userland from the 2.4 GB system image on userdata (md0)
```

The UEFI side lives in the [uefi-sheng](https://github.com/UniXNU/uefi-sheng)
port (`Platforms/Xiaomi/malachitePkg`, `Silicon/MediaTek/MT6878Pkg`), on a fork.
The system image is written to the `userdata` partition; the loader reads it as
`md0` (`sysimg=ufs`) and the payload ramdisk is `md1`.

## Seeing a boot without a UART

There is no serial port on the phone, and a boot that stops leaves nothing behind
by itself. Three facilities, all requested from the payload's cmdline:

- **A fake PL011.** `platform_malachite.uart` points at a zeroed page at
  `PAYLOAD_BASE + 0x03000000`. The kernel's `serial_init()` succeeds, its TX
  status bit always reads ready, and every `kprintf` character goes through
  `loader_log_putc()` before being written into that page. This is the path the
  early `bsd_init` and `memory:`/`apfs:` lines take.
- **`monitor=1`.** The loader starts core 7 with PSCI before jumping, hands it the
  UEFI MMU/cache regime, and that core draws the kernel's `loader_log` to the
  panel every two seconds. It needs no cooperation from the kernel and survives a
  boot that never returns.
- **Saved log slots.** The monitor copies the live log into one of two 2 MiB slots
  4 GiB into `userdata` every 10 seconds, with a magic, a sequence number and a
  CRC. A later `showprev=1` run draws the newest valid slot; `showprev=ustacks`
  draws only its `ustacks:` lines. This is how the log is read back from a phone
  that cannot be photographed and whose fastboot cannot read partitions.

`ustacks_probe=1` adds a second monitor footer line with the kernel's own
`ustacks_*` state (the thread call pointer, the parsed name and filter, and the
count that falls with every sample), for when the sampling daemon stays silent.

## Build and flash

The loader is built as a freestanding UEFI application:

```sh
cd xnuloader
clang --target=aarch64-unknown-windows -ffreestanding -fno-builtin \
  -fno-stack-protector -fshort-wchar -mgeneral-regs-only -O1 \
  -Wall -Wextra -Wno-unused-parameter \
  -DPAYLOAD_BASE=0x100000000ULL -DMALACHITE_STAGES -DMALACHITE_QUIET \
  -c loader.c -o loader-malachite.obj
lld-link /subsystem:efi_application /entry:efi_main /nodefaultlib \
  /base:0xA1000000 /out:loader-malachite.efi loader-malachite.obj
```

A payload carries the loader, the kernel and the ramdisk, and the cmdline:

```sh
python3 mkpayload.py -o payload.bin \
  loader.efi=loader-malachite.efi \
  kernel=../prebuilt/mach.development.bcm2837 \
  ramdisk=../userland/root.apfs \
  --rdres 948c0000 \
  --cmdline "rd=md0 sysimg=ufs sysimg_bounce=1 monitor=1 kret_hold=1 \
-enable_kprintf_spam serial=0"
```

The boot image is the malachite UEFI image with the payload appended (the packer
in the uefi-sheng port), flashed to `boot_a`:

```sh
fastboot flash boot_a hackios-malachite.img
fastboot --set-active=a
fastboot reboot
```

## State

| Component | State |
| --- | --- |
| UEFI | boots, Boot Manager menu |
| XNU | boots on core 0 |
| iOS userland | launchd and lsd run; stalls in lsd about 83 s in |
| UFS | root works (system image as `md0`) |
| Display | loader text only (LK framebuffer) |
| GPU / touch / USB / Wi-Fi / audio | not implemented |

The stall is under investigation; `ustacks` sampling and the saved-log viewer
exist for it. Two kinds of log noise are expected and not the cause: persona
lookups return ESRCH because there is no persona subsystem, and MCM refuses to
set a Data Protection class because there is no AKS/SEP.

The MediaTek BROM is locked down (SLA/DAA, no public DA for MT6878), so the
`userdata` slots cannot be read back with mtkclient; the viewer is the way in.
