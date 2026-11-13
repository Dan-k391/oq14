# Independent review: six reduced-pencil and Schur-pole extensions

Reviewed exact sources/hashes:
- Packet06LeftPreconditioner: 80a41110971871b21ebe086cd4646683fccd486393628daecc84ad7c3fc18730
- Packet06ReducedPencil: d582aa6173bf4e560da1a7f424d4f932baf51fb4abbe7b1f3cbf841485fd80d7
- Packet06SphereReduced: 6fb7a70c29fdd722a16c999fbba068fc6d5c9cd872efc265d02e15cd0667c1d7
- Packet06SphereReducedSchur: 010f95ca127462105a359f0b511cd3a8c43185ca994d1e33b3f308938135aac3
- Packet06SchurInverse: 174047048271d64f1d96d2a2cd75b951c9ef583f55ea8b650f749406bbecb3cb
- Packet06SchurPole: 22651cc0310679fe2ed1d751907b6c1ca7d5d3ec15a3fd64b516d0cc37e05794

The left preconditioning is by the actual invertible static block: its kernel, transformed range annihilator and derivative pairing are preserved with the correct order B⁻¹A and φ∘B. The material reduced pencil satisfies the actual factorization, transfers invertibility to the weighted volume block, and establishes locally uniform coefficient convergence under the explicit common bound, a.e. coefficient convergence, and common support assumptions. Its analyticity result is for nonnegative enclosing radius.

The spherical sector pencil is shown to agree with the actual full pencil on sector inputs; its simple scalar crossing assumes n>1, algebraicity of the complexified n over Q, nonzero z, and an actual l=1 TM determinant zero. The resulting rank-one repair is invertible and the scalar derivative is nonzero. The inverse formula requires repair invertibility and nonzero scalar. The meromorphic expansion is an abstract Banach-operator theorem under analytic A, invertible repair, zero scalar and nonzero scalar derivative: its residue is nonzero rank one with the stated left/right normalization and a punctured-neighborhood analytic remainder.

These theorems do not themselves establish a perturbed physical resonance for each rounded material, a sphere-pole expansion on the entire unconstrained volume space, physical residues for all angular sectors, or uniform separation/packing. No placeholders or custom axioms occur in these six sources. Separate-object build logs and the frozen-hash manifest provide the compiler/axiom evidence; cached upstream project and external dependency objects remain outside the six-source independent rebuild.
