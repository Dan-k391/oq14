# Exact pointwise plane dipole of an actual uniformly polarized ball

Frozen source: lean/StaticBallPlaneDipole.lean.
SHA256: 468B4F028994DFD60C94E7C5567F72BC1DA14CFE9E858219B2E28B111FFBC5AA.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/StaticBallPlaneDipole-final.log.
Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

An actual positive-radius uniformly polarized ball, whose center absolute
height is at least d+R for positive d, supplies genuine compact support and
a source gap. The literal Newton response is continuous on the actual open
strip around the plane, and the existing Newton operator identifies it AE.
The previously derived exact exterior dipole identity also holds AE on this
strip. Both sides are actually continuous there, so equality holds pointwise
throughout the strip and hence at every point of the measurement plane.

The resulting plane profile is exactly the static Hessian kernel evaluated
at the center displacement and multiplied by the actual volume-polarization
moment. No pointwise trace, source response, or point-dipole conclusion is
assumed. The proof uses uniqueness of continuous representatives on an open
3D neighborhood, never a restriction of an arbitrary 3D AE identity to the plane.
Physical finite-stack Green identification and dynamic flux are separate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `468b4f028994dfd60c94e7c5567f72bc1da14cfe9e858219b2e28b111ffbc5aa`. Independent log `lean/logs/StaticBallPlaneDipole-root-audit.log`, SHA256 `0f2434991a8c0410f50b4fce89ca331df745933a982831404e8082bc8193c102`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
