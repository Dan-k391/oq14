# Compact spatial derivatives of actual regular solid waves

Source: `lean/SolidSpatialBounds.lean`.
SHA256: `8B2F6E9AC563E40F67D79AEFED5F0B1ABB64CD6A73BCFAEF3AB6726A6403DA7A`.

Author final target and importable object compiler exit 0, no warnings. Object 284608 bytes. Twelve selected dependency reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/SolidSpatialBounds-final.log`. Forbidden-token source scan passed.

The actual complex Taylor derivatives of F_l restrict to its real Taylor derivatives with equal operator norms. This transfers the genuine all-order radial series estimate. The spatial squared argument is the actual smooth quadratic x -> q^2 norm(x)^2.

For an actual smooth spatial function f, jetSup(f,j,b) is the supremum of the actual j-th Frechet derivative norm on the closed ball; jetNorm(f,N,b) is their finite sum for j=0,...,N. Compactness and continuity prove these bounds are finite, nonnegative, and dominate actual derivatives; no derivative-bound premise is introduced. Define D=1+jetNorm(squaredArgument q,N,b), which depends only on q,N,b and satisfies D>=1.

For b>=0 and norm(x)<=b the actual regular factor obeys

    norm(D^j [F_l(q^2 norm(.)^2)](x)) <= j! A_l exp(norm(q^2)b^2/2) D^j, j<=N.

The genuine higher chain rule gives this estimate. The actual higher product rule then gives

    norm(D^N wave_l,q,p(x)) <= 2^N N! A_l exp(norm(q^2)b^2/2) D^N jetNorm(complexEvaluate p,N,b).

This bound is global on compact balls including the origin and applies to the literal solid scalar waves. Homogeneity and harmonicity are needed for the separate actual Helmholtz theorem, not for this derivative estimate. The harmonic polynomial normalization is retained as its literal compact jet norm. This file does not claim a degree-uniform bound for unit spherical harmonic bases, spatial addition formulas, or spatial dyadic series convergence. Those require an additional actual angular-normalization argument.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 12 reports use only standard foundations. Final source SHA256 `8b2f6e9ac563e40f67d79aefed5f0b1abb64cd6a73bcfaef3ab6726a6403da7a`. Independent log `lean/logs/SolidSpatialBounds-root-audit.log`, SHA256 `98d72ffc9db71f61f46a3389be84dab649135b3d89f822724e19511561b24e8e`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
