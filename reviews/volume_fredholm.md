# Actual preconditioned volume kernel and range

Source: `lean/VolumeFredholm.lean`.

SHA256: `4AF79FF8A1465B51CF9FC4F8C68BE937DD2141064537BAB273BBCE5DCF695E72`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0). All seven theorem exports have matching axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Root independently reviewed the source before this final compilation. The source is frozen at the hash above.

The compact part is the actual dynamic weighted remainder composed on the left with the proved static volume inverse. Literal multiplication identities factor the actual dynamic volume block through identity minus this compact operator. Invertibility of the static block identifies the kernels. The kernel is finite dimensional, the range is closed, and the kernel's orthogonal complement has a genuine norm bound. The static inverse norm bound one transfers the preconditioned estimate to the actual volume block.

The only support premise is compact support of the actual material coefficient in a finite closed ball. These results impose no contrast or volume smallness and do not establish homogeneous PDE uniqueness.
