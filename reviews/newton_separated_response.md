# Actual continuous Newton representative on a source-free strip

Frozen source: lean/NewtonSeparatedResponse.lean.
SHA256: CD9CBC0AAEC5C1BE82CB77B3D39E3F6FB65840C34FA8BE2C530E0CB789EA4EF0.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all fourteen reports standard-only. Log: lean/logs/NewtonSeparatedResponse-final.log.
Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

For actual compactly supported integrable source coordinates with absolute
height at least positive d wherever nonzero, the open strip abs(x_2)<d/2 is
genuinely separated from the source. The actual weak Newton Hessian pairing
is converted to an ordinary cutoff convolution on strip-supported tests.
The actual L2 Newton operator therefore agrees AE on this open strip with
the literal ordinary Hessian response, using the genuine test annihilator.

The ordinary integral is actually continuous on the strip: the derived
static kernel bound and fixed positive separation give an actual integrable
uniform dominator. Its plane values are exactly the literal whole-plane
integral fields used in StaticPlaneSource. A packaged continuous representative
and uniqueness of continuous representatives on the open strip are proved.

No spatial identity, continuity conclusion, or trace is an input. The proof
does not restrict a 3D AE statement to a null plane. It constructs a genuine
continuous representative on a 3D neighborhood, whose plane values are
well-defined independently of arbitrary L2 representatives. Finite-stack
Green identification and full dynamic Maxwell flux remain separate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 14 reports use only standard foundations. Final source SHA256 `cd9cbc0aaec5c1be82cb77b3d39e3f6fb65840c34fa8be2c530e0cb789ea4ef0`. Independent log `lean/logs/NewtonSeparatedResponse-root-audit.log`, SHA256 `0b375c127c53bf78740be638fa17fea1f32c998577269fe0d137410b949a6484`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
