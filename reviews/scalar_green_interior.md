# Actual regular Green moment selection

Source: `lean/ScalarGreenInterior.lean`.
SHA256: `705CBF782A607C7F5C38CFFCFCE4977184DAC55EED1B111F553E83E4E6FD6724`.

Author target plus importable object compiler exit 0, no warnings. Object 146960 bytes. Eight selected reports standard-only. Log: `lean/logs/ScalarGreenInterior-final.log`. Forbidden-token scan passed.

The actual derivative state U+F/r is algebraically identified everywhere, including r=0, with U+r UD, where U and UD are the literal Green spherical moment and first Frechet derivative moment. The previously proved actual origin continuity gives continuity of both actual Riccati state components, and r U vanishes at zero. On the genuine source-free annulus 0<r<norm(y), actual spherical differentiation and the actual scalar Helmholtz equation give the flux derivatives and thus the actual Riccati ODE. Applying the actual Wronskian endpoint selection proves each literal interior Green coefficient is a multiple of the actual entire origin_l(k r)/r. No origin regularity, expansion, PDE or coefficient-selection conclusion is supplied as a premise. Frequency k is explicitly nonzero and source y explicitly nonzero. The remaining source-radius matching determines the actual multiple.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 8 reports use only standard foundations. Final source SHA256 `705cbf782a607c7f5c38cffcfce4977184dac55eed1b111f553e83e4e6fd6724`. Independent log `lean/logs/ScalarGreenInterior-root-audit.log`, SHA256 `7cdb31b4ae028d0130d38ee4833935b27312924ef1d3ec8aaa84b970f58d8464`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
