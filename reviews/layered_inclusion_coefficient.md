# Literal layered-inclusion susceptibility

Source: `lean/LayeredInclusionCoefficient.lean`.

SHA256: `32C08D37AA02CDDF2B94DEE9318D122FB1E4CABEA4472692B022E706B4DFBD53`.

Author final compiler exit 0; importable object 335048 bytes. All 18 selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output: `lean/logs/layered-inclusion-coefficient-check.log`.

The actual susceptibility is the finite sum of the prescribed cell contrasts times indicators of the literal layered-inclusion cells. Its pullback through the genuine coordinate measurable equivalence is packaged as `StaticCoefficient.Coefficient`.

Actual cell-index uniqueness and pairwise disjointness are proved from radial inequalities, strict core containment and strict inclusion separation. These give exact pointwise contrast values on every open cell and the actual common bound M, without a factor depending on the number of cells. Measurability and nonnegativity are proved from the finite indicators. Points on uncovered interfaces receive zero susceptibility.

The constructor explicitly assumes nonnegative contrasts, a nonnegative common bound M and each contrast at most M. Exterior contrast zero gives genuine pointwise support inside the closed ball at the outermost radial cut. Dielectric values on the literal cells are derived as 1 plus their assigned contrasts and hence are positive. Cavity contrast may be zero or any nonnegative prescribed value.

No coefficient agreement, support, partition, connectivity, or Maxwell uniqueness conclusion is supplied as an assumption. Actual scattering for this constructed coefficient is supplied separately in `LayeredDeviceScattering.lean`.

Status: author compiler PASS; ready for root independent full-source audit and compiler. Source held unchanged pending audit.

## Independent root verification on resumption

Full source reviewed; pinned compiler EXIT0. All 18 reports use standard foundations. Exact source SHA256 `32c08d37aa02cddf2b94dee9318d122fb1e4cabea4472692b022e706b4dfbd53`. Independent log: `lean/logs/LayeredInclusionCoefficient-independent-root.log`. The assumptions retain the stated scope and do not close the complete device construction.
