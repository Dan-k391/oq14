# ModalVolumeData — independent audit

PASS, 2026-10-28. I inspected the full frozen source and relevant imported coordinate, compact-extension, square-root multiplier, and regular-mode identities. Source `lean/ModalVolumeData.lean` SHA256 `8CC8F3463A1B812DE56856612557FDEAD43A8A0AD44AE3C98C13EF5871B8A637`.

Fresh pinned Lean 4.19.0 compilation: `lean/logs/ModalVolumeData-terra-audit.log`, SHA256 `A6EE7115B12975062E8469B644CD981353E87CD42F5E2D8C55099182376FD513`; receipt `lean/logs/ModalVolumeData-terra-audit.exit.log` records exit 0. The complete log has eleven axiom reports, no errors or warnings, and only `propext`, `Classical.choice`, `Quot.sound`. Source scan found no forbidden declarations or placeholders.

The construction zero-extends each continuous core component, inserts it into the physical vector L² space and applies the bounded actual square-root coefficient multiplier. For real n > 1 the incident and numerator coordinates are almost everywhere √χ centerE(k) and √χ (I/n) centerE(nk), with χ = n² − 1 inside the open unit ball and zero outside the closed ball. Their vector-valued analyticity holds for every complex k, including zero. The numerator source identity gives χ (I/n) centerE(nk).

For k ≠ 0, nonzero numerator follows from continuity on the open ball and the explicitly nonzero third component at the center; no determinant condition is assumed. The source does not prove a driven volume identity, outgoing representation, volume-kernel membership, or volume-resolvent residue. These remain separate obligations.
