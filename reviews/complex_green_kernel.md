# Physical scalar Green kernel at complex frequency

Source: `lean/ComplexGreenKernel.lean`.

SHA256: `F10A621E145DFAB398FF5F35330F6A4F8A1C40E82BF739EBDAE1D1BFDB066E56`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0). All fifteen theorem exports have matching axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent full-source audit passed. The source is frozen at the hash above.

The scalar kernel is literally exp(i k |x|)/(4 pi |x|) for complex k. The radial first and second derivative formulas are proved with actual real derivatives, then composed with the Euclidean norm. The coordinate gradient and Hessian are actual real spatial derivatives away from zero. Taking the Hessian trace proves the actual spatial Helmholtz equation for every complex k. Spatial smoothness away from zero is also proved.

Six exact restriction identities identify the radial kernel, its first two radial derivatives, scalar kernel, gradient and Hessian at real k with the existing real-frequency objects. No frequency analyticity or distributional source conclusion is asserted here.
