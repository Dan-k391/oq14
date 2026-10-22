# ConicalAnnularSource — author verification

Source SHA256: `115A25DEC94DC0C9F23E65C04227E96C26F5AF59FC7B269C04775DDD00FD9AD1`.
Pinned Lean 4.19 target/object EXIT0, no warnings, all fifteen standard-only dependency reports. Final log `lean/ConicalAnnularSource.final.log`, SHA256 `267488974E58D4395BC949A861A2582B08CF9921119544A44D8B6F260F7DB725`. Object 307632 bytes.

An actual smooth radial bump chi defines the finite material epsilon_global (actual conical epsilon inside its outer closed ball and 1 outside), the localized gradient/curl fields, and literal F=epsilon_global cutElectric-cutCurl. The actual bump derivatives vanish in the inner ball and outside the outer closed ball; F vanishes there pointwise. Its topological support lies in the actual closed annulus and is compact. Bounded measurable coefficient multiplication and actual local L2 of U,E prove global coordinate L2 of cutElectric, cutCurl and F. No compact support, integrability or annular vanishing is assumed. The weak equations for these localized fields were already proved in the imported cutoff modules. Root independent complete-source/compiler audit requested.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 15 reports use only standard foundations. Final source SHA256 `115a25dec94dc0c9f23e65c04227e96c26f5af59fc7b269c04775ddd00fd9ad1`. Independent log `lean/logs/ConicalAnnularSource-root-audit.log`, SHA256 `267488974e58d4395bc949a861a2582b08cf9921119544a44d8b6f260f7db725`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
