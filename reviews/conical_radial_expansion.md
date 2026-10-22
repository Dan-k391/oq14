# ConicalRadialExpansion — author verification

Source SHA256: `C71F4E696CF0E244C855DE11DDBC856F97A40583E5E93EA89598B0CE43BAB796`.
Pinned Lean 4.19 target/object EXIT0, no warnings, both standard-only dependency reports. Final log `lean/ConicalRadialExpansion.final2.log`, SHA256 `30B6A96947A17F20CB2DBCB0483984041EB514BE5C87009AEFA93CBC3ABFFB67`. Object 546408 bytes.

The actual Euler first-order system is transformed by f=rU to a genuine scalar second-order system. The actual powers r^(nu+1), r^(-nu) have proved derivatives and nonzero constant Wronskian; the existing proved ODE variation theorem gives the complete two-power expansion. Subtracting the actual particular solution then yields the exact forced expansion U=c r^nu+b r^(-nu-1)+p. No solution expansion or constant coefficient is assumed. This supplies the genuine ODE classification; its input forced system must still be derived for the actual Maxwell cone projections. Root independent complete-source/compiler audit requested.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 2 reports use only standard foundations. Final source SHA256 `c71f4e696cf0e244c855de11ddbc856f97a40583e5e93ea89598b0ce43bab796`. Independent log `lean/logs/ConicalRadialExpansion-root-audit.log`, SHA256 `30b6a96947a17f20cb2dbcb0483984041eb514be5c87009aefa93cbc3abffb67`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
