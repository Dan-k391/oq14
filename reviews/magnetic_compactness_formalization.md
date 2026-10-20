# Interior magnetic compactness for actual weak Maxwell fields

`lean/WeakPoynting/MagneticCompactness.lean` is frozen at SHA-256
`043f8eb89640e4f0bdeb517c5ed3f0d51de57f6c643458426f8fa79ce12e7961`.
All six selected exports directly compile without warnings using only
`propext`, `Classical.choice`, and `Quot.sound`. Full output, combined source
hashes, and scope are recorded in `magnetic-compactness-verification.txt`
and `magnetic-compactness-provenance.json`.

The theorem `maxwell_cutoff_precompact` applies to actual regional H(curl)
Maxwell fields at a fixed nonzero real frequency, with permeability one
and a real scalar permittivity bounded in absolute value almost everywhere.
The family has a common regional L2 bound on its electric and magnetic
fields. No field differentiability or global L2 condition is imposed.

For any fixed compact C2 interior cutoff, its extended magnetic fields have
compact closure in the actual whole-space L2 vector space. The proof
derives uniform cutoff and support bounds from the cutoff itself, obtains
all nine actual weak derivatives and their uniform energy bound from the
previous Maxwell div–curl construction, and embeds each component in the
concrete weak H1 compactness theorem.

`maxwell_magnetic_local_precompact` constructs one cutoff and one open
neighborhood for an arbitrary compact interior set, uniformly for the
whole family. The resulting precompact global L2 representatives agree
almost everywhere with the original magnetic fields on that neighborhood.
`maxwell_magnetic_local_subsequence` then gives a strictly increasing
subsequence converging strongly in the genuine L2 norm of those representatives.

The result concerns interior magnetic compactness. It does not yet assert
electric compactness, boundary compactness, convergence of the magnetic
derivatives, or existence of a scattering solution. No positive lower
bound on permittivity is needed for this magnetic result.

The coordinator's independent full source review passed.
