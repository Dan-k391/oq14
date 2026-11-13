# Complex response weak source identity author review

PASS. `lean/logs/complex_response_real_weak_author_final.log` is the full compiler log; `lean/logs/complex_response_real_weak_author_final.exit.log` records exit 0. Source SHA256 0FEECECB00E2C00F6D3F66F6360329562B4E53538C96F5077CF2C7D27AD612D7; log SHA256 AD665DF026FA426B0174DCF824D831BDD4B5F085844B8FC9B05FBA8BA4EBFE59; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

For every source input and every compact smooth test supported in the observation/material ball, proves the actual localized response satisfies the complex-frequency weak curl-curl source equation. The proof derives its real-frequency counterpart from FieldResponse.electric_maxwell_source and uses analyticity of actual response test pairings and the identity theorem. It does not yet derive homogeneous sphere Helmholtz, interface matching, or kernel classification. Reported axioms are propext, Classical.choice, and Quot.sound.

