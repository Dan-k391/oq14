# Growing-support radial construction and optical-flux audit

Owned files: `manuscript/sections/channel_global.tex` and this review. No Git operations.

## Concrete global progress

`cg:simultaneous-gain` constructs a finite positive scalar radial dielectric which gives simultaneous gain comparable to q^M to every prescribed partial wave of one electric inversion parity, and reciprocal gain q^(-M) to the opposite parity. It includes both polarizations and all azimuthal indices up to an arbitrary prescribed finite L. The support grows explicitly; the material bound stays fixed.

The stack has M low/high quarter-wave pairs with epsilon=n²+2/x², n=1 or q, x=k0*r. Its inner radius x0 is a multiple of pi. Explicit sufficient requirements are x0>=8*K_L*q^(2M), x0²>=32*[L(L+1)+2]*d_M*q^(4M+4), and the fixed material-bound radius. K_L is the finite Hankel polynomial coefficient sum, d_M=M*pi*(1+1/q)/2.

The exact TE reference transfer is (-1)^M diag(q^(-M),q^M), while TM gives (-1)^M diag(q^M,q^(-M)). Actual generator errors are bounded by [L(L+1)+2]/x0². Conjugating by reference propagation and applying Volterra/Gronwall retains its amplification, giving endpoint error <=q^M*(exp(beta)-1), beta<=q^(-2M)/32. Bessel phase errors at x0 are <=q^(-2M)/8. The final actual state differs from its ideal coordinate state by <=q^(-M)/4. Wronskian extraction then gives the explicit incoming-coefficient bounds.

`cg:resource-counteraudit` uses N odd axisymmetric TE modes. It is an actual N-dimensional physical input space with full unitary scattering, zero normal Poynting density on the entire plane for every coherent input, and a local electric energy lower bound diverging as q^(2M) uniformly over its unit sphere. This strengthens the one-channel resource obstruction to arbitrary rank. It is not a channel counterexample because its signed passage is zero.

## Actual passage bound for the prescribed band

`cg:vacuum-trace` derives a nuclear norm estimate for the physically normalized regular vacuum section-flux operator: ||Q_D^0||_1 <= 2*k0²*A/pi. Its positive trace is <=k0²*A/pi for a centered symmetric D, since inversion parity conjugates Q to -Q. The proof computes the Hilbert--Schmidt norms of the physical electric and magnetic Herglotz restriction maps, then factors the flux operator.

`cg:stack-count` observes that core gains are exactly G=(q^M P_-+q^(-M)P_+)B with ||B||<=8*sqrt(2)/3. The signed section flux has only cross-parity blocks, so Q_device=B*Q_vacuum*B exactly: the real large and small factors cancel. A counted subspace inside the prescribed band therefore has dimension <=128*k0²*A/(9*pi*eta*tau), independent of mirror period count, support radius, input-band size, and local energy. No bypass assumption is needed for this restricted bound.

The estimate does not cover partial waves above the prescribed band L, even though the physical device admits them. It is a complete global exclusion for the proposed finite-band common-stack construction, not unrestricted OQ14 closure.

## Verification and remaining route

Full analytical derivations are in LaTeX, including physical power factors, all-vector parity, the weighted transfer error, and trace-class factorization. Independent root and hotspots-agent adversarial reviews passed: both checked the physical Herglotz constants, quarter-wave products, weighted Duhamel amplification, exterior Wronskian extraction, and parity cancellation. The hotspots reviewer also checked pointwise zero plane flux for coherent odd axisymmetric TE inputs and the energy constant 16*Z0/25. Two text-formatting errors were corrected after review. Parent owns integrated compilation and any Lean formalization. The current mathematical section is frozen after these checks.

The next possible escape is angular-selective interior phase engineering which amplifies both required parities. Local radial gain/phase control is already proved, but its radius does not establish the large global shifts or the whole-plane bypass estimate needed here. No such step is assumed.
