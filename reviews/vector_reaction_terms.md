# Actual normalized vector reaction terms

`lean/VectorReactionTerms.lean`: seven author-final reports, exit0, no
warnings, standard foundations only. Independent audit pending.

The two branches are the actual toroidal Debye field and its actual curl,
at unit frequency, evaluated in the constructed normalized scalar harmonic
representatives. Their joint two-point products have genuine arbitrary
finite Frechet derivative envelopes. The normalization weight is
1/(l*(l+1)), bounded between zero and one, and zero at degree zero.
The actual term is -(gamma+I) times that weight and the vector dyad.
The previously established physical radial majorant gives a summable
degree envelope for every chosen finite derivative order, including both
spatial origins. The control radius uses degreeScale(N+2,b).

This specifies and bounds actual vector terms. Identification with the
full layered point-source dyadic Green tensor remains separate.

Source SHA256 `c1b9854eb1ffc9934ccdc6eaa23cbe8ac84173d242db3d8fc2ed2ec7441ecb20`.
Final log `lean/logs/VectorReactionTerms-final.log`, SHA256
`8bf61b45596f4534901762877298f6401624b78009481854b544154f3a7aa5a2`.
