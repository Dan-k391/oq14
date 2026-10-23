# HarmonicVectorDecomposition author review

Frozen source SHA256: `9D76DBC326E0F96C1F410C81AF2949ADF8A1BD83A529957C10E20C0BC21297C8`.

Author complete-source mathematical review PASS. Pinned final target and importable object compile exit 0, all 9 standard-only dependency reports and no warnings, in `lean/logs/HarmonicVectorDecomposition-final.log`. Forbidden-source scan clean. Root independent audit pending.

For an actual componentwise harmonic vector polynomial Q of homogeneous degree n+1, this constructs three literal scalar harmonic polynomials: div Q of degree n, radialDot(curl Q) of degree n+1, and (2n+3) radialDot Q minus radiusSq div Q of degree n+2. It proves their harmonicity and the exact scaled vector identity. The positive scale is (n+1)(n+2)(2n+3). Euler, polynomial partial commutation, curl-curl and the genuine radial Laplacian product rule supply the proof; no decomposition premise is supplied.

The toroidal convention is grad P cross x. The positive middle-sector sign agrees with the degree-one example Q=(-y,x,0). The lower-sector sign agrees with Q=x and with Q=x*z-radiusSq*e_z/3. The identity currently covers positive homogeneous vector degree only. The degree-zero vector case, sphere restriction span, actual normalized vector harmonic completeness, and physical dyadic/source normalization remain future work.

Checkpoint: no active author compiler sessions. Next proof step after resume is the explicit degree-zero vector case, followed by actual harmonic polynomial representative span and sphere restriction completeness. No new completeness source has been started.
