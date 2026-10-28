# ModalDipoleOrigin — author verification

Author PASS, 2026-10-27. Frozen source `lean/ModalDipoleOrigin.lean` SHA256 `A944E56CFDD8EF20B5B9BA243F174034098AC332177DBA52FF8C8BAFA4876885`. Pinned Lean 4.19.0 final object run exited 0, with no errors or warnings. All 16 selected declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

Final log: `lean/logs/ModalDipoleOrigin-final.log`, SHA256 `9D5E62A2D7419CF819CA9CD3CA95B6EE0D05E4999D4B4FDD128D5E43B61AC6BC`. Exit receipt: `lean/logs/ModalDipoleOrigin-final.exit.log` = 0. Importable object: `lean/.lake/build/lib/lean/ModalDipoleOrigin.olean` (549248 bytes). The preceding full check `lean/logs/ModalDipoleOrigin-check5.log` also exited 0. Root independent audit pending.

## Actual determinant and normalization

The existing genuine entire `ModalOrigin.profile`, denoted g, satisfies psi_1(w)=w² g(w), psiD_1(w)=2w g(w)+w² g'(w), and g(0)=1/3. The new definition is

`D(n,z) = exp(I*z) * [n^3*(I+z-I*z^2)*g(n*z) + (z+I)*(2*n*g(n*z)+n^2*z*g'(n*z))]`.

`regularized_eq` cancels the actual outgoing xi_1/xiD_1 poles using `p_one` and `pD_one`, giving D(n,z)=`ModalAlgebra.tmDet 1 n z` whenever n and z are nonzero. The exponential factor is retained exactly. `regularized_zero` proves D(n,0)=I*n*(n²+2)/3. No equality with the totalized finite Hankel formula at z=0 is asserted.

The extension is jointly continuous for complex (n,z), and entire in z for every complex n (`regularized_continuous`, `regularized_differentiable`, `regularized_analyticAt`). The actual Wronskian proves tmDet_1(1,z)=I away from zero, hence `regularized_one` gives D(1,z)=I for every z, including zero.

## Uniform zero exclusion

`uniform_origin_nonzero`, `uniform_tmDet_nonzero`, and `uniform_real_tmDet_nonzero` exclude zeros uniformly as both n→1 and z→0. Their only local input is the nonzero removable value I and joint continuity.

`compact_regularized_nonzero` strengthens this: for each compact K⊂ℂ there exists δ>0 such that every complex n with ‖n−1‖<δ has D(n,z)≠0 for all z∈K. The proof applies the genuine compactness neighborhood lemma to joint continuity and D(1,z)=I. `compact_tmDet_nonzero` transfers this to the actual matching determinant for nonzero n,z. `bounded_real_tmDet_nonzero` specializes it to every closed frequency disk and real n≥1.

Finally `zero_frequencies_escape` works over an arbitrary source filter: if real n tends to 1, eventually n≥1, and z is eventually a nonzero actual degree-one determinant zero, then ‖z‖ tends to infinity. This closes the bounded-frequency branch of the degeneration argument, including any approach to the frequency origin. It does not assume a ratio lower bound.

## Scope

This does not construct polynomial root branches, establish nonidentity on unbounded algebraic branches, select an index avoiding all angular coincidences, identify the volume-operator kernel, or establish a full Maxwell resolvent residue. Those remain separate mathematical obligations. The frozen sources imported here were not edited.
