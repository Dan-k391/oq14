# Complex linearity of the material L2 source densities

Author final pinned compiler/object PASS: 2 reports (add, smul), each standard-only [propext, Classical.choice, Quot.sound]; exit 0, no warnings, no errors. Frozen source: lean/MaterialSourceLinear.lean, SHA256 ec05a8419e0d1062a69d0480ee2292d68d8d3d2d880ae512c16477f03f662da4. Final log: lean/logs/MaterialSourceLinear-final.log, SHA256 ad07d1e9f517b0678e8e3e6188a4ad598fc8ec0d1ee18437265a42444f826f79 (exit file lean/logs/MaterialSourceLinear-final.exit.log, value 0). Root independent audit pending. Frozen source.

Proved: for a static coefficient c and L2 vector fields u, v, the actual density representative `DynamicVolume.source c w j y = sqrt(c(coordinateMap y)) * w(coordinateMap y) j` satisfies `source c (u+v) j =ᵐ source c u j + source c v j` and `source c (z•u) j =ᵐ z * source c u j` almost everywhere on physical space, from the a.e. descriptions of L2 addition and scaling pulled back along the measure-preserving coordinate map.

Not proved: the identities are almost-everywhere only, not pointwise (the representatives are not pointwise linear), so downstream integrals against the density are linear but any support or gap statement must be established for the actual representative separately. No admissibility, integrability, field or flux claim is made.
