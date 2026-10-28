# PhysicalPlaneFlux — independent root audit

PASS, 2026-10-27. Complete source and mathematical scope reviewed independently of the author. Fresh pinned Lean 4.19.0 source compilation completed with exit 0. Source SHA256: `E80FC66C2967355A028E906E8CEEBB1EA1CBC5D0F9F9BE8B1ACE5FD14A934EBD`.

Audit log: `lean/logs/PhysicalPlaneFlux-root-audit.log`, SHA256 `7E40465D31B8C7C0F42C66BF6A4AD1F54EAA60CC1BA0616BB9746B51F8C5B727`. Exit receipt: `lean/logs/PhysicalPlaneFlux-root-audit.exit.log` = 0. All 6 selected reports use only `propext`, `Classical.choice`, and `Quot.sound`; no warnings, errors or proof placeholders. This re-elaborated the source against existing dependency objects, not a clean dependency rebuild.

The physical passage is one half of the real complex-flux integral; bypass is the integral of one half the absolute real flux. Whole-plane integrability makes the real-part interchange and bypass comparison valid. Applying the raw counted theorem at twice both thresholds yields the physical thresholds without changing input or output power. The generic adapter assumes integrability; the concrete companion proves it.
