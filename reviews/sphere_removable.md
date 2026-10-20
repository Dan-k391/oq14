# SphereRemovable independent scope and self-audit

`lean/SphereRemovable.lean` proves actual integration by parts across one sphere in Euclidean three-space. Its eleven exports compile with only `propext`, `Classical.choice`, and `Quot.sound`.

The proof uses a coordinate splitting that preserves volume. Each line meets the sphere at no more than two points, established from the exact norm-square formula. A continuous compactly supported line function, differentiable off a countable set with integrable actual derivative, has zero integrated derivative by the existing continuous off-countable fundamental theorem of calculus. Fubini gives the three-dimensional identity. The sphere has measure zero by the proved Haar sphere theorem.

The weak partial theorem requires continuity of the scalar field, genuine off-sphere differentiability and the formula for its genuine derivative, and local integrability of that derivative. These are explicit analytic hypotheses, not an assumed weak law. In the gradient theorem, the supplied vector field must equal that actual derivative off the sphere. Applying the weak partial identity to first derivatives of a compact C2 test and using Schwarz symmetry proves zero distributional curl even if the gradient has a normal jump.

The final continuous-vector theorem derives the actual curl pairing from componentwise scalar identities. It does not assume an interface trace theorem or assert that a discontinuous electric field is continuous.

Self-audit: the line compact support argument uses the exact norm bound; the off-countable FTC uses continuity at every exceptional point; the almost-everywhere replacements are justified by zero sphere measure; all integral sums are backed by integrability. The compact C2 requirement for the weak-gradient argument is explicit. Instantiating these analytic hypotheses for the actual assembled spherical mode is separate work.

Verification command, from `D:\oq14\lean`:

```powershell
& '..\.tools\lean\lean-4.19.0-windows\bin\lake.exe' env lean SphereRemovable.lean
```
