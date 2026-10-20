# CapSturmEndpointTest — author verification

Source SHA256: `51908019F5F8FADDD3F41F0B9CA3E6E089024159BE606851342D9B08CD70A7FE`.
Pinned Lean 4.19 target and object emission: exit 0, no warnings, both selected dependency reports standard-only. Log `lean/CapSturmEndpointTest.final.log`, SHA256 `433E04F787D430E01CFD57DFC3DE460C7ECBE3FA1EE62FFF8281B82D230212C2`.

The actual cap weak identity is generalized to a continuous test on [-1,1] with an actual interior derivative in L1. The proof uses genuine interval integration by parts on each of the three intervals; the previously proved actual value/flux relations cancel the two interface terms, and the actual endpoint factors vanish at the poles. This allows actual spherical-coordinate tests, which need not have bounded endpoint derivatives. No weak equation is supplied as a premise.

Parent independent complete-source/compiler audit requested. Frozen precursor CapSturmLiouville is unchanged.
