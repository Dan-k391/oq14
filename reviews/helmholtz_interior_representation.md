# Actual Helmholtz interior reproducing kernel

`lean/HelmholtzInteriorRepresentation.lean` has six author-final reports,
compiler exit 0, no warnings, standard foundations only, and a compiled
object. Independent review has been requested.

The proof starts with the actual compact Green representation. Reflection
and weak differentiation transfer every solution derivative from the
cutoff source to the actual Green kernel. The resulting integral kernel
is phi(x-y) times the cutoff Laplacian minus twice the contraction of the
Green gradient with the cutoff gradient. All products and translations
have derived integrability; neither a representation nor a derivative
estimate is an input premise.

This module proves the representation for a global smooth representative
that solves Helmholtz on the cutoff support. Localization, uniform bounds,
and the passage from convergent mode sums to smooth Maxwell fields remain
separate steps.

Evidence: `lean/logs/HelmholtzInteriorRepresentation-final.log` and its
zero exit receipt.

## Author compilation receipt (October 23)

Source SHA256 `79812a25ad989688ab88f7553bf1827d87ae7ee553e684ca9cbaf3cd223f2111`. Compiler/object PASS, exit 0, no warnings. Evidence `lean/logs/HelmholtzInteriorRepresentation-final.log`, SHA256 `82fc60b9ffdafd81f2f2402e71a903e12045d7dc5a06d712985d5d4f48cff48f`. Selected reports use only standard foundations. Source frozen for independent review.

These local analytic results do not by themselves complete the physical channel, fixed-input hotspot, or modal constructions.
