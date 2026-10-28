# PhysicalPlaneFlux — author review, 2026-10-27

Author final PASS: pinned Lean 4.19.0, EXIT0, no warnings, six reports using only `propext`, `Classical.choice`, `Quot.sound`. Independent review is pending root verification.

- Source: `lean/PhysicalPlaneFlux.lean`, 66 lines; SHA256 `E80FC66C2967355A028E906E8CEEBB1EA1CBC5D0F9F9BE8B1ACE5FD14A934EBD`.
- Final log: `lean/logs/PhysicalPlaneFlux-final.log`; SHA256 `7E40465D31B8C7C0F42C66BF6A4AD1F54EAA60CC1BA0616BB9746B51F8C5B727`.
- Exit receipt: `lean/logs/PhysicalPlaneFlux-final.exit.log`, value 0. Generated object exists.
- Complete source/log/object/receipt evidence: `reviews/physical_counted_normalization_author_2026_10_27.json`.

The definitions are physical passage `(Re ∫_D F)/2` and physical absolute bypass `∫_(Dᶜ) |Re F|/2`. Whole-plane integrability of the complex flux implies integrability of both real-valued flux functions. The passage equals the section integral of `Re F/2`; the absolute real bypass is at most half the raw complex-norm bypass, by `|Re F| ≤ ‖F‖` and monotonicity of integrals of integrable functions.

`counted_of_double` converts a raw `IsCounted` statement at `(2η,2δ)` to the physical statement at `(η,δ)`, retaining the same subspace and scattering map. Its explicit integrability input is essential for bypass monotonicity. The concrete endpoint supplies this input from actual field estimates in the companion modules; this generic lemma does not itself construct a device.

No frozen source, shared configuration, registry, manuscript, or Git state was edited. Source scan and final-newline checks pass.
