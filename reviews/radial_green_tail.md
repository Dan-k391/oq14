# Actual radial source Green function and distant common-stack limit

Owned review only. Existing sources are frozen. This derivation uses actual scalar-positive Maxwell layers. It does not assume that incoming gain bounds a source response.

## Fixed-gain common stack

Fix q>1 with q²<epsilon_plus, an integer M>=1, and A=q^M. Starting at dimensionless radius R=2*pi*n, use M high-low quarter pairs: index q for length pi/(2q), then index one for length pi/2. Let

\[
 d_A=\frac{M\pi}{2}(1+q^{-1}),\qquad X=R+d_A.
\]

The core and exterior are vacuum. The two reference transfers are

\[
 U_{\rm TE}^0=(-1)^M\operatorname{diag}(A,A^{-1}),\qquad
 U_{\rm TM}^0=(-1)^M\operatorname{diag}(A^{-1},A).
\]

For each fixed angular order l the actual transfers converge to these matrices as R tends to infinity. At this stage A and M are fixed. The order of quantifiers matters: radius is chosen after the desired gain and transducer size.

## PROVED: exact coefficient of the actual radial source Green function

Write nu=l(l+1), psi_l(x)=x*j_l(x), chi_l(x)=x*y_l(x), and

\[
 F_l(x)=
 \begin{pmatrix}\psi_l&\chi_l\\\psi_l'&\chi_l'\end{pmatrix},
 \qquad \det F_l=1.
\]

For either polarization use its physical continuous radial state: (u,u') for TE and (u,epsilon^-1*u') for TM. In the vacuum core and exterior these conventions agree. Let U_l be the actual transfer from R to X and set

\[
 M_l=F_l(X)^{-1}U_lF_l(R)
       =\begin{pmatrix}a&b\\c&d\end{pmatrix}.
\]

All these matrices are real and have determinant one. Normalize the exterior outgoing radial solution to xi_l^+=psi_l+i*chi_l. Its core continuation is z_l=alpha_l*psi_l+beta_l*chi_l, where

\[
 \binom{\alpha_l}{\beta_l}
       =M_l^{-1}\binom1i
       =\binom{d-ib}{-c+ia}.
\]

Since a²+c²>0, beta_l is nonzero. Define the source reaction coefficient gamma_l=alpha_l/beta_l. Then

\[
 \gamma_l=\frac{-cd-ab-i}{a^2+c^2},\qquad
 \operatorname{Im}\gamma_l=-\frac1{a^2+c^2},\qquad
 |\gamma_l|\leq\|M_l\|^2.
\]

The norm bound follows from |alpha_l|<=||M_l|| and |beta_l|=|M_l*e1|>=||M_l||^-1. The incoming coefficient of the origin-normalized regular solution is (a+i*c)/2; hence its physical core gain satisfies

\[
 |g_l|^2=-\operatorname{Im}\gamma_l,\qquad
 |1/\beta_l|=|g_l|.
\]

The real part of gamma_l is not determined by the incoming gain. This is why gain alone is insufficient for a Green estimate.

For the reduced radial operator with derivative jump +1, the core Green function is

\[
 g_l(x,y)=\psi_l(x_<)\chi_l(x_>)
                    +\gamma_l\psi_l(x)\psi_l(y).
\]

For free outgoing vacuum gamma_l=-i. Both polarizations have the same core formula; the TM source jump uses its weighted derivative, which equals the ordinary derivative in the vacuum core.

## PROVED: uniform low-order source bound for a fixed stack

Fix 0<c0<1 and consider nu<=c0²R². For xi_l^+ on x>=R the quantity

\[
 {\cal E}(x)=|\xi_l^{+\prime}|^2+
              (1-\nu/x^2)|\xi_l^+|^2
\]

satisfies E'(x)=2*nu*x^-3*|xi_l^+|²>=0 and E(infinity)=2. Thus

\[
 \|F_l(R)\|,\|F_l(R)^{-1}\|,
 \|F_l(X)\|,\|F_l(X)^{-1}\|
       \leq\frac2{\sqrt{1-c0^2}}.
\]

The inverse bound equals the forward norm because the real 2-by-2 determinant is one. On the stack the TE generator has norm at most q²+c0²+1, and the TM generator at most q²+c0²+1 as well. Therefore, with C0=q²+c0²+1,

\[
 \|U_l\|\leq e^{C0 d_A},\qquad
 |\gamma_l|
 \leq\frac{16}{(1-c0^2)^2}e^{2C0 d_A}
       =:B_A .
\]

This bound is uniform in l and R in the stated range. B_A is finite and polynomial in A for fixed q. It is a source-coefficient bound, not merely an incoming-gain estimate.

## PROVED: source tails at orders comparable to the remote radius

The finite Hankel polynomial has coefficients

\[
 \xi_l^+(x)=(-i)^{l+1}e^{ix}
       \sum_{s=0}^l i^s\frac{(l+s)!}{s!(l-s)!2^s}x^{-s}.
\]

Let a_l=(2l-1)!!. Reversing this finite sum gives

\[
 |\xi_l^+(x)|\leq a_lx^{-l}e^x,\qquad
 |\xi_l^{+\prime}(x)|\leq(1+l/x)a_lx^{-l}e^x.
\]

Indeed the ratio of the coefficient of x^(-(l-t)) to a_l is

\[
 \frac{2^t}{t!}\prod_{j=0}^{t-1}\frac{l-j}{2l-j}
       \leq\frac1{t!}.
\]

For large R, X<=2R. If c0²R²<nu<=q²X², then l<=2qR and the bounds above give

\[
 \|F_l(R)\|,\|F_l(R)^{-1}\|,
 \|F_l(X)\|,\|F_l(X)^{-1}\|
 \leq C_F e^{h_qR},
\]

where one may take C_F=4(1+2q) and h_q=2+2q*log(4q). Both actual generators have norm at most 4q² in this range, so

\[
 |\gamma_l|\leq C_F^4
       \exp(4h_qR+8q^2d_A).
\]

For every fixed core radius r0 and sufficiently large l,

\[
 |\psi_l(r0)|\leq\frac{r0^{l+1}}{(2l+1)!!}.
\]

Thus the products gamma_l*psi_l(r0)², including any fixed polynomial weight in l, have a total tail tending to zero in the range c0*R+O(1)<=l<=2qR. The negative exponent -2*l*log(l/(e*r0)) dominates the displayed O(R)+O(d_A) exponent. Fixed spatial derivatives and vector spherical-harmonic multiplicities contribute only polynomial weights.

## PROVED: arbitrarily high orders are controlled by the centrifugal barrier

First, the exact identity

\[
 |\xi_l^+(x)|^2=
 \sum_{s=0}^l
  \frac{(l+s)!}{(l-s)!}\frac{\binom{2s}s}{4^s}x^{-2s}
\]

has nonnegative coefficients. To verify it without an asymptotic claim, insert the even polynomial |xi|² into f'''+4*(1-nu/x²)*f'+4*nu*x^-3*f=0. Starting with its constant coefficient one, the recurrence is

\[
 c_{s+1}=\frac{(2s+1)[\nu-s(s+1)]}{2(s+1)}c_s,
\]

which gives the displayed coefficients and terminates at s=l. Consequently

\[
 \operatorname{Re}\frac{\xi_l^{+\prime}(x)}{\xi_l^+(x)}
 =\tfrac12\partial_x\log|\xi_l^+(x)|^2\leq0.
\]

Assume now nu>q²X². In every stack layer the TE equation has positive barrier nu/x²-epsilon. If z is its outgoing continuation,

\[
 \partial_x\operatorname{Re}(z'\overline z)
       =|z'|^2+(\nu/x^2-\varepsilon)|z|^2>0.
\]

The value at X is nonpositive, so the value at every smaller stack radius is nonpositive. For TM the continuous state p=epsilon^-1*z' gives

\[
 \partial_x\operatorname{Re}(p\overline z)
       =\varepsilon|p|^2+
           (\nu/(\varepsilon x^2)-1)|z|^2>0,
\]

with the same conclusion. Nonzero outgoing Wronskian excludes a zero of z. At the inner vacuum boundary the load h=z'(R)/z(R) therefore obeys Re h<=0 for either polarization.

The regular solution psi is positive and increasing at R. Set

\[
 \gamma_*=\frac{1+\sqrt{1+4(\nu-R^2)}}2.
\]

The Riccati comparison gives R*psi'(R)/psi(R)>=gamma_*. Solving the load equation for the source coefficient gives

\[
 \gamma_l=\frac{\chi_l'(R)-h\chi_l(R)}
                      {h\psi_l(R)-\psi_l'(R)},\qquad
 |\gamma_l|\leq
       \frac{|\chi_l'(R)|}{\psi_l'(R)}
       +\frac{|\chi_l(R)|}{\psi_l(R)}.
\]

The denominator bounds used here follow from Re h<=0:
|h*psi-psi'|²>=|h|²*psi²+psi'².

A useful explicit lower bound for psi is

\[
 \psi_l(R)\geq\frac{R^{l+1}}{(2l+1)!!}
     \exp\left[-\frac{R^2}{2(l+\gamma_*+2)}\right].
\]

To prove it put f=psi/x^(l+1). Then (x^(2l+2)*f')'=-x^(2l+2)*f. The Riccati lower bound implies f(t)/f(x)<=(x/t)^(l+1-gamma_*) for 0<t<x<=R. Integration yields -f'(x)/f(x)<=x/(l+gamma_*+2), proving the bound.

Let theta_q=sqrt(1-q^-2)>0. Then gamma_*>=theta_q*l and R/l<=2/q. Combining the preceding bounds gives

\[
 |\gamma_l|\psi_l(r0)^2
 \leq C_q
       \exp\left[\left(1+\frac1{q(1+\theta_q)}\right)R\right]
       \frac{r0^{2l+2}}{(2l+1)R^{2l+1}},
\]

where C_q=1+(1+2/q)/theta_q is sufficient. This estimate holds for r0<R and nu>q²X². Since such l are at least qR+O(1), its sum, including any fixed polynomial weight, tends to zero as R grows. The estimate is independent of the number of interfaces and holds for both polarizations.

## PROVED: compact smooth convergence of the actual source reaction kernel

For fixed A, every fixed l has actual transfer converging to its common-stack reference. At R=2*pi*n the regular state tends to (sin(-l*pi/2),cos(-l*pi/2)); the irregular state is its independent quarter-turn. The outgoing state at X has a common nonzero factor exp(iX)*(-i)^(l+1), which cancels in alpha/beta. No exterior phase padding is required. Direct substitution gives

\[
 \gamma_l^{\rm TE}\to
 \begin{cases}-iA^2&l\ {\rm even},\\-iA^{-2}&l\ {\rm odd},\end{cases}
 \qquad
 \gamma_l^{\rm TM}\to
 \begin{cases}-iA^{-2}&l\ {\rm even},\\-iA^2&l\ {\rm odd}.\end{cases}
\]

The low-order uniform bound and the two high-order tails justify termwise convergence of the reaction Green series, with every fixed number of derivatives, on each fixed compact core product B_r0 times B_r0. TE regular vector waves are j_l(kr)*X_lm and TM waves are their curl divided by k. Their derivatives and multiplicity add only fixed polynomial factors to the factorial bounds above. Finite low orders present no difficulty at the origin.

To state the limiting electric polarization operator precisely, let K0=(k²I+grad div)*Phi_k be the free outgoing electric volume kernel. Its imaginary part is the smooth radiation kernel

\[
 {\cal R}(x,y)=\operatorname{Im}K_0(x-y)
   =\frac{k^3}{16\pi^2}
       \int_{S^2}(I-dd^T)e^{ikd\cdot(x-y)}\,dS(d).
\]

Let R_+,R_- be its projections onto electric fields even and odd under x -> -x. Their kernels are [R(x-y)+R(x+y)]/2 and [R(x-y)-R(x+y)]/2. Then the actual background source kernel satisfies, locally with all derivatives,

\[
 K_R-K_0\longrightarrow
 i\left[(A^2-1){\cal R}_+
              +(A^{-2}-1){\cal R}_-\right].
\]

The normalization can be checked directly: the free electric dyadic multipole expansion has coefficients i*k³ on M_regular*M_outgoing and N_regular*N_outgoing. Replacing the outgoing radial wave by its core continuation and dividing by the actual Wronskian replaces the regular-regular coefficient by -k³*gamma_l. Hence the reaction coefficient is -k³*(gamma_l+i), which gives the displayed limit. The regular-wave completeness identity is Im K0=k³*sum(M*Mbar+N*Nbar), also obtained by expanding the spherical Herglotz integral above.

For A>=1 every fixed derivative of order s of the limiting reaction kernel is bounded by (A²-1)*k^(3+s)/(4*pi) in operator norm. Indeed its expression in R(x-y),R(x+y) has nonnegative scalar coefficients adding to A²-1, and each derivative of the integral kernel is bounded by k^(3+s)/(4*pi).

On the odd-electric-inversion source sector the reaction is i*(A^-2-1)*R_-, uniformly bounded independently of A. On the C2-even source sector this is precisely the opposite-wall sector; the even-electric-inversion sector is electric-wall. These are source-response bounds, not merely incident-channel suppression.

## PROVED: weighted state bounds through the stack and the exterior

All constants in this subsection may depend on fixed A, q, k, and a fixed source ball B_S. They are uniform in R tending to infinity. Physical radii are restored by x=k*r; this changes only those constants. We take S>=1 and enlarge it slightly beyond the dimensionless source support. Compact L2 polarizations have regular electric and magnetic multipole moments f_lm satisfying, for all sufficiently large l,

\[
 |f_{lm}|\leq C\|P\|_2(l+1)^b\psi_l(S)
 \leq C'\|P\|_2(l+1)^b
              \frac{S^{l+1}}{(2l+1)!!}.
\]

Here b is a fixed integer (b=4 is more than sufficient); the final factorial bound holds for every l after enlarging C'. The intermediate bound involving psi_l(S) is only used for large l, when psi_l(S)>0; it is not asserted at a possible low-order zero. The estimate follows by integrating the regular vector waves against P and using Cauchy--Schwarz. Their scalar factors are j_l, (x*j_l)'/x, and sqrt(nu)*j_l/x. On a fixed ball the power series gives the displayed factorial estimate, while its lower bound at the slightly enlarged S lets the estimate be expressed using psi_l(S). Angular sup norms, multiplicities, and any fixed number of angular derivatives add only fixed powers of l. In particular every weighted sum below is valid for arbitrary fixed polynomial weights. This avoids imposing spatial smoothness on P.

For a source moment f_lm the outgoing radial factor outside the source is, up to fixed physical normalization, f_lm*w_l, where

\[
 w_l=\chi_l+\gamma_l\psi_l
\]

in the core. Its actual continuation across the layers is used, not its vacuum continuation. In the barrier range nu>q²X² let h=p(R)/w(R), with p=u' for TE and p=epsilon^-1*u' for TM. The exact Wronskian gives the cancellation

\[
 w_l(R)=\frac1{h\psi_l(R)-\psi_l'(R)},\qquad
 p_l(R)=\frac{h}{h\psi_l(R)-\psi_l'(R)}.
\]

Consequently

\[
 |w_l(R)|\leq\psi_l'(R)^{-1},\qquad
 |p_l(R)|\leq\psi_l(R)^{-1}.
\]

Throughout the barrier stack the equations are u'=epsilon*p, p'=V*u for TM, where V=nu/(epsilon*x²)-1>0. For TE they are u'=p, p'=V*u with V=nu/x²-epsilon>0. We already proved Re(p*conj(u))<=0 there. Hence

\[
 (|u|^2)'=2\epsilon\operatorname{Re}(p\overline u)\leq0,\qquad
 (|p|^2)'=2V\operatorname{Re}(u\overline p)\leq0
\]

for TM, and the same with epsilon=1 in the first equation for TE. Both state components are continuous at interfaces. Therefore both magnitudes are nonincreasing outward through every layer, regardless of the number of layers.

The lower bound for psi_l(R) and psi_l'(R)>=gamma_*psi_l(R)/R now imply, uniformly for R<=x<=X,

\[
 |f_{lm}|\bigl(|u_l(x)|+|p_l(x)|\bigr)
 \leq C\|P\|_2(l+1)^b
              e^{C_qR}(S/R)^{l+1}.
\]

This is summable with every fixed polynomial weight and is smaller than every inverse power of R after summing the barrier orders l>=qR+O(1). In particular no estimate of the form exp(C*l²/R²) has been used.

For low orders nu<=c0²R², the uniform F, gamma, and partial-transfer bounds above give

\[
 |f_{lm}|\bigl(|u_l(x)|+|p_l(x)|\bigr)
        \leq C_A |f_{lm}|,\qquad R\leq x\leq X .
\]

For the middle orders c0²R²<nu<=q²X² the corresponding bound is exp(C_A R)*|f_lm|. Since l>=c0 R+O(1), its weighted sum tends to zero like exp(-c R log R). Thus the sum of the magnitudes of all physical radial states, with any fixed polynomial angular weight, is bounded uniformly in R throughout the annulus.

The same bound holds for every x>=X in the vacuum exterior. To see this without invoking a far-field expansion nonuniform in angular order, use the exact outgoing solution xi_l. Its positive amplitude-square polynomial proves that |xi_l(x)| is nonincreasing for all x>0, with limit one. Also

\[
 (|\xi_l'|^2)'=2(\nu/x^2-1)
                    \operatorname{Re}(\xi_l\overline{\xi_l'}).
\]

The last real part is nonpositive. Therefore |xi_l'| decreases up to sqrt(nu), then increases to one. It follows for x>=X that

\[
 |\xi_l(x)|\leq|\xi_l(X)|,\qquad
 |\xi_l'(x)|\leq\max\{|\xi_l'(X)|,1\}
             \leq\max\{|\xi_l'(X)|,|\xi_l(X)|\}.
\]

Multiplication by the actual exterior outgoing coefficient preserves the preceding state bounds. This proves the assertion even for orders whose centrifugal turning point lies far beyond X.

For Maxwell vector waves a tangential field component is a constant times u/r or p/r, and a radial component is a constant times sqrt(nu)*u/r² (with a bounded factor epsilon^-1 where needed). The vector spherical harmonics and their derivatives have polynomial angular-order bounds. Therefore the weighted-state estimates imply

\[
 |E_t|+|H_t|\leq C_{A,S}\|P\|_2/r,\qquad
 |E_r|+|H_r|\leq C_{A,S}\|P\|_2/r^2,
 \quad R/k\leq r<\infty.
\]

Here t and r mean tangential and radial relative to spheres, not to the section plane. The bounds are piecewise through the layers; interface circles have plane measure zero. A fixed finite-band incident field and its background scattering field satisfy the same estimates, with the source norm replaced by the bounded incident coefficients. The constants may depend on A and that fixed finite band.

At z=0, the spherical radial direction lies in the section plane. The cross product of two sphere-tangential vectors is radial, so contributes zero to the normal plane flux. Thus only radial--tangential products contribute, giving

\[
 |S_z(r,\phi,0)|\leq C/r^3.
\]

It follows that the absolute flux across the annular portion of the plane is O(d_A/R²), and that across its exterior is O(1/R). The same conclusions hold for sums of the source-generated and fixed finite-band background fields. This is a bound on absolute flux; signed conservation is not being substituted for it.

## PROVED: uniform growing-core tails and whole-plane flux convergence

Fix A, a compact source region K separated by a positive distance from z=0, and a fixed finite-band incident family. Let P_R be polarizations supported in K with P_R -> P in L2. Assume the background incident fields, after one common phase adjustment, converge on compact sets to the common-stack limiting fields. Let E_R,H_R be their sum with the actual radial-background source response to P_R. Define E_infinity,H_infinity with the limiting source kernel proved above and the corresponding limiting illumination. Then

\[
 \left\|\frac12\operatorname{Re}
       (E_R\times\overline H_R)\cdot\widehat z
 -\frac12\operatorname{Re}
       (E_\infty\times\overline H_\infty)\cdot\widehat z
 \right\|_{L^1(\mathbb R^2)}\longrightarrow0.
\]

Here the fields are actual source responses in the respective background; the assertion does not yet say that P_R comes from a dielectric perturbation. That identification is supplied by the inverse-stability corollary below.

Proof. Compact plane convergence follows from the positive source-plane separation, the local C-infinity reaction-kernel convergence, and P_R -> P in L2. It remains to control the growing vacuum core.

Separate its reaction series into low orders nu<=c0²R² and the remaining orders. The low-order coefficients (gamma_l+i)*f_lm have a uniform factorial bound. They therefore define tangential Herglotz densities uniformly bounded in every fixed smooth angular norm, even though the cutoff depends on R. Their Maxwell fields have sphere-tangential components O(1/r) and radial components O(1/r²), uniformly in R. One elementary proof writes the Herglotz integral in polar coordinates about the observation direction: integration by parts in t=cos(theta) gives O(1/r); for the radial component the endpoint amplitudes vanish by transversality, so a second integration gives O(1/r²). The azimuthally averaged smooth amplitude has bounded derivatives at both endpoints; this follows by its local even Taylor expansion in sin(theta). Uniform C4 angular control suffices. The corresponding magnetic density is d cross the electric density divided by Z0, so the same proof applies.

The free outgoing source response has the same tangential/radial bounds outside twice the source ball, directly by differentiating its compact-source integral. The fixed finite-band background has them as well. Their combined absolute plane-flux tail beyond any B>2S/k is O(1/B), uniformly in R.

The remaining reaction fields are uniformly negligible throughout B<=r<=R/k. For middle orders, |gamma_l|<=exp(CR), the source moments have factorial decay with l>=cR, and the regular observation factors on r<=R/k and their first derivatives are at most polynomial in l and R. For example the integral representation of j_l gives |j_l|<=1 and |j_l'|<=1; radial factors involving 1/r are bounded since r>=B. Thus the weighted field sum is exp(-c R log R).

For the barrier orders, combine the earlier bound for gamma_l itself with the upper bounds psi_l(S)<=S^(l+1)/(2l+1)!! and psi_l(x)<=x^(l+1)/(2l+1)!! at x<=R. This gives

\[
 |\gamma_l|\psi_l(S)\psi_l(x)
 \leq C_q e^{C_q'R}\frac{R}{2l+1}(S/R)^{l+1},
                  \qquad 0<x\leq R .
\]

Equivalent bounds for first radial derivatives follow from
0<x*psi_l'(x)/psi_l(x)<=l+1 in the pre-turning interval. On r>=B the additional inverse-radius factors are harmless. Angular derivatives add polynomial factors. Summing again gives exp(-c R log R). The addition of the free regular coefficient i in gamma+i is smaller. Consequently the entire high-order reaction field, and the magnetic field obtained by its curl, are o(R^-m) for every fixed m on B<=r<=R/k. Their self-flux and their cross-flux with the bounded low-order fields have integral o(1), despite the O(R²) area.

Combining the growing-core tail with the proved annulus/exterior estimate yields

\[
 \limsup_{R\to\infty}\int_{r>B}|S_{z,R}|\,dA\leq C/B.
\]

The limiting free-plus-Herglotz field has the same O(1/B) tail. Compact convergence, then B tending to infinity, proves the L1 statement. Every estimate is uniform for bounded L2 source norms. It is also uniform for a finite-dimensional incident/source family converging in operator norm, by applying the linear field estimates and the quadratic flux inequality. Thus the assertion covers every coherent vector in a fixed finite-dimensional input space, rather than only a chosen basis.

## PROVED: passing from source response to actual dielectric perturbations

Let chi be a bounded fixed real contrast supported in K, still separated from the plane, and let the limiting volume equation

\[
 P=\chi(E_\infty^{\rm inc}+K_\infty P)
\]

have a bounded inverse on L2(K). The singular free-volume operator is identical for all R; only its smooth reaction kernel varies. The compact smooth convergence above therefore gives

\[
 \|\chi(K_R-K_\infty)\|_{L^2(K)\to L^2(K)}\to0 .
\]

The elementary inverse perturbation identity shows that the actual finite-R equations are invertible for sufficiently large R, and their solutions P_R converge in L2(K) to P, uniformly on any fixed finite-dimensional input family. The preceding whole-plane theorem applies. All finite-R fields now are actual scattering fields of the radial layers plus the dielectric perturbation, with their original physical incident normalization.

For a sequence of particle sizes a tending to zero and gains B_a tending to infinity, this result is used separately at each fixed a and B_a. One first proves invertibility and the desired plane-flux estimate in the explicit limiting kernel, and only then chooses a sufficiently large finite R(a). No estimate uniform in a is required for this last radial-radius choice. If the desired gains must be realized by a common quarter-wave stack with a fixed index q, use B=q^M and choose a_M=t*sqrt(lambda)/q^M; the small-a limit is unchanged along this sequence.

## Review scope and audit status

Root and hotspots independently audited both the local source coefficient/compact-kernel proof and the complete whole-plane extension; both reported no substantive defect. Root explicitly checked the Wronskian w/p bounds, both-component outward monotonicity, exterior derivative-modulus turning-point bound, weighted radial/tangential conversion, uniform Herglotz endpoint cancellation, middle/barrier growing-core tails, and inverse stability. Hotspots identified the possible low-order zero of psi_l(S); the moment statement was clarified to use that positive factor only for sufficiently large l, while the factorial statement covers all l. The full proof is promoted to manuscript/sections/radial_green_limit.tex, with the final physical theorem labelled rg:physical-limit.

Channels independently reviewed manuscript/sections/channel_transducers.tex and channel_transducer_limit.tex. The Debye jet map, symmetrized scalar two-jet duality, exact finite-band interpolation, physical incoming Gram balancing, positive static inverse, O(a) reaction perturbation, source residual norms, normal-dipole first moment, planar Hilbert--Schmidt exponents, and every compact/tail cross product check. The source-kernel normalization agrees exactly on the C2-invariant sector.

Channels independently reviewed manuscript/sections/channel_unrestricted.tex. The fixed parameters, discrete gain B_M=q^M and size a_M=t*sqrt(lambda)/B_M, radius-after-size diagonal choice, full unitary S as selected output, all-coherent inequalities, positive vacuum gap for every finite device, and scalar-positive finite geometry check. The conclusion is exactly the permitted regime delta>eta>0, tau in (0,1), with full S selected; no conclusion for delta<=eta or a prescribed receiving hemisphere is asserted.

## Lean coverage added after the analytic proof

The separate source lean/RadialGreen.lean compiles under the pinned Lean 4.19.0 and mathlib environment. It exports 24 theorems, each with an explicit #print axioms command. Every report lists exactly the standard foundations propext, Classical.choice, and Quot.sound; there is no sorryAx, custom axiom, or assumed Maxwell Green-limit conclusion.

The formalized statements are the actual complex outgoing continuation of a real determinant-one transfer, nonvanishing beta, its squared modulus and positive denominator, exact real/imaginary gamma formula and strictly negative imaginary part, equality of the physical gain squared and minus imaginary gamma, vacuum-source Wronskian/load cancellations, and the exact load-denominator squared-modulus lower bound. In addition, the file proves complex radial ODE derivative identities for the load and both squared state magnitudes, then derives monotone load and antitone state magnitudes on a closed barrier interval from the actual ODEs and a nonpositive outgoing endpoint load. It also derives zero derivatives of the complex radial Wronskian and real fundamental-matrix determinant directly from their first-order ODEs.

The complete partial-wave Green convergence, spherical expansions and whole-device counterexample are analytic manuscript proofs, not claimed to be formalized by these 24 declarations. The interval theorem is a classical single-interval result; the finite-layer manuscript uses state continuity to concatenate it across interfaces.
