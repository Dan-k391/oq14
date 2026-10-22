# Actual density-integrated coherent Herglotz tails

Frozen source: lean/SourceHerglotzTail.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/SourceHerglotzTail-final.log.
Independent audit pending.

The actual source cross-column identities and their genuine integrability
allow the point mixed Maxwell/Herglotz bounds to be integrated against the
literal volume density. Both E_volume cross conjugate K_point and J_point
cross conjugate H_volume have normal-flux tails bounded by
pointTailConstant*sourceMass/r^3. The magnetic density is actually
conjugated; its norm is the original source norm. No source-to-field
representation or tail conclusion is assumed.

Actual plane continuity supplies measurability; the genuine 2D inverse-cube
integration gives tail integrability and tail L1 mass bounded by
pointTailConstant*sourceMass*diskConstant/T. Source support and positive
separation from the plane are actual geometric premises, and the incident
point lies in the same fixed enclosing ball. Constants do not depend on
the source-plane gap. Whole-plane coherent error and physical finite-stack
Green identification remain further work.
SHA256: C221BE9A303B56AB6273A64CDBB565938E71FCFC9E449059E0C230C92166D319

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `c221be9a303b56ab6273a64cdbb565938e71fcfc9e449059e0c230c92166d319`. Independent log `lean/logs/SourceHerglotzTail-root-audit.log`, SHA256 `6d5032b172438c0746d8edde89ea3a11844a2edb841dbedbca802c20807adf99`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
