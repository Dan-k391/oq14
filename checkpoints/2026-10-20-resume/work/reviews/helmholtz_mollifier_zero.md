# Actual local zero inherited by shrinking mollifiers

Source: `lean/HelmholtzMollifierZero.lean`.

SHA256: `959220D15F21ABC074E8C26C14C74648F98AC97787562D4BE3179F0BAE3F7B18`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All five exported theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent complete-source mathematical audit passed at this exact hash. The source is frozen; root's independent compiler recheck is pending.

If the actual complex function is zero almost everywhere in a ball, any actual compact-kernel convolution is pointwise zero wherever the reflected topological kernel support lies inside that ball. The finite-radius support estimate is the proved geometric containment from the genuine local regularization module. Outside that reflected support the kernel itself is zero, and inside it the function is AE zero, so the literal convolution integrand vanishes almost everywhere. No integrability premise is required for this exact zero-integrand result.

For the actual normalized complex bump, its actual outer radius supplies the support bound and hence exact zero throughout the reduced ball. The genuine shrinking-radius limit makes the same convolution sequence identically zero eventually throughout any fixed strict inner ball. Finally an arbitrary neighborhood on which the function is AE zero contains an actual positive-radius ball. Restricting AE zero to that ball gives a fixed smaller positive-radius ball of eventual pointwise zero, and therefore an eventual actual zero germ at the original center.

The theorems have no PDE, regularity, representation, completeness, or unique-continuation premise. They supply only genuine inheritance of local zero, to be combined later with separately proved smooth PDE uniqueness and the actual AE convolution limit.
