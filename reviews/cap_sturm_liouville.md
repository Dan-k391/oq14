# Cap Sturm--Liouville profile

Author verification for `lean/CapSturmLiouville.lean`.

- Source SHA256: `FBC4DB08D9FB30F81CF1826C0F353158885A9CF185DBF1171245502BB7422557`.
- Pinned Lean 4.19.0 final compilation and object emission passed with exit 0 and no warnings; object 1043896 bytes.
- All thirty dependency reports use only `propext`, `Classical.choice`, `Quot.sound`.
- Exact log `lean/CapSturmLiouville.final.log`, SHA256 `F6E214F6031F44FB0BCC14AE261512B1B8998A0FEAD41FDBAB6E89502AFFCE7F`.

The actual odd piecewise profile uses the matched actual Legendre solutions on `[-1,-t]`, `[-t,t]`, and `[t,1]`. The two interface values are proved to match, which gives continuity on the entire closed interval. The profile is odd and nonzero at the positive pole. The defined slope is identified with the actual derivative away from the two interfaces, hence almost everywhere on the open interval.

The weak identity is proved by literal integration by parts on all three intervals. The actual Legendre equation gives the derivative of `(1-z^2)*f'`; the endpoint terms at the two poles vanish because of `1-z^2`. The interface terms cancel using the determinant root's actual weighted flux identity and evenness of the inner derivative. The actual step coefficient and global profile/slope agree with these regional integrands almost everywhere; their integrability and the global interval integral are established by actual adjacent-interval splitting.

For positive contrast, the weighted squared norm is strictly positive: the profile is continuous and positive at the pole, and the step coefficient is at least one. Dividing by its actual positive square root gives weighted norm exactly one and preserves the literal weak identity. The final existence theorem obtains its root from the proved intermediate value construction, so no weak equation or eigenpair is assumed.

Independent root full-source and compiler audits requested. Source held stable. Scope: a normalized actual one-dimensional transmission profile and its interval weak equation. This source does not establish a weak eigenfunction or H1 membership on the actual sphere; that geometric lifting remains separate.

## Independent root verification on resumption

Full source reviewed; pinned compiler EXIT0. All 30 reports use standard foundations. Exact source SHA256 `fbc4db08d9fb30f81cf1826c0f353158885a9cf185dbf1171245502bb7422557`. Independent log: `lean/logs/CapSturmLiouville-independent-root.log`. The assumptions retain the stated scope and do not close the complete device construction.
