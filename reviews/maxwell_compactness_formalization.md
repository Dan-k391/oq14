# Full local weak Maxwell compactness

`lean/WeakPoynting/MaxwellCompactness.lean` is frozen at SHA-256
`4c375b8e526332f958ac10d1897095a73cf9fd5c2fa0de6a9751671ea138da18`.
All eleven selected exports directly compile without warnings and use only
`propext`, `Classical.choice`, and `Quot.sound`. Complete output and combined
source hashes are in `maxwell-compactness-verification.txt` and
`maxwell-compactness-provenance.json`.

The final local precompactness and subsequence theorems apply to actual
regional weak Maxwell fields with:

- one fixed nonzero real frequency and permeability one;
- one fixed real scalar permittivity with positive lower and finite upper
  bounds almost everywhere;
- a common regional L2 bound on the electric and magnetic fields.

For every compact interior set, one common open neighborhood and one common
interior cutoff are constructed. The paired global L2 cutoff
representatives agree almost everywhere with the original electric and
magnetic fields on that neighborhood. Their paired L2 range has compact
closure; every sequence therefore has a strictly increasing subsequence
converging strongly in the actual L2 product norm.

Electric compactness is proved from magnetic compactness, rather than
assuming electric H1 regularity across a discontinuous coefficient.
The actual weak Maxwell equations are closed under subtraction for the
same coefficient. The established electric cutoff norm estimate controls
the difference of two electric cutoffs by the difference of two outer
magnetic cutoffs. Finite covers transfer compactness, and the product
compactness theorem gives the paired result.

The coordinator independently reviewed the full mathematical chain and
reported no defect. The scope does not include boundary compactness,
global L2 scattering fields, derivative convergence, or compactness
uniform over a varying family of coefficients.
