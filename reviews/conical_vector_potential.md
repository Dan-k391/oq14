# ConicalVectorPotential — author verification

Source SHA256: `F4BE5279606F3C552310EBA2081398BFC15D1C0BB43920CF6DF044A7DFD6B618`.
Pinned Lean 4.19 target/object EXIT0, no warnings, all six standard-only dependency reports. Final log `lean/ConicalVectorPotential.final.log`, SHA256 `8B9F927FA139537FA5EAF286A0A29450A5342561CFB0B21CEF654306545E142C`. Object 573112 bytes.

The literal real vector potential is A=-x cross D/(nu+1), with D=epsilon E. Testing actual Gauss against x_i psi gives the coordinate Gauss moment. The actual weak Euler moment and explicit coordinate algebra prove curl(x cross D)=-(nu+1)D distributionally, hence curl A=D on every genuine compact C1 test. All individual integrals are proved integrable. No interface differentiability, weak vector-potential identity, or vanishing origin source is assumed. The cyclic real cross-product definition is displayed explicitly. Root independent complete-source/compiler audit requested.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `f4be5279606f3c552310eba2081398bfc15d1c0bb43920cf6df044a7dfd6b618`. Independent log `lean/logs/ConicalVectorPotential-root-audit.log`, SHA256 `8b9f927fa139537fa5eaf286a0a29450a5342561cfb0b21cef654306545e142c`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
