# Whole-plane L1 continuity of actual compact-source Maxwell flux

Author: continuation_review_sol. Date: 2026-10-20.

Source: `lean/MaxwellPlaneL1.lean`.
SHA256: `0E91CB48B1C83951096D4CFCF1C34C43DCDFC77917734DDCD299142B33896D61`.

The complete source passed pinned Lean 4.19 targeted compilation and
importable object emission with exit 0. All eight selected dependency
reports use only `propext`, `Classical.choice`, and `Quot.sound`.
Independent source and compiler review is requested before registration.

Fix real frequency k, a nonnegative common source radius R, and a positive
common distance d from the plane. Sources are the actual componentwise L1
functions satisfying the support and gap conditions of PlaneSourceKernel.
The flux is the literal complex normal cross product of the ordinary
dyadic electric response and conjugated ordinary magnetic response, on
the actual Euclidean two-dimensional plane.

The actual compact-product kernel bound from PlaneSourceKernel supplies
uniform electric and magnetic component bounds on a fixed disk. A cutoff
radius T=max(2R,2)+1 then permits the already proved inverse-cube transverse
radiation estimate on its complement. These are combined into one actual
nonnegative integrable envelope, independent of the two source functions.
Its disk part is bounded and compactly supported; its outer part is the
genuine integrable inverse-cube profile. The common constant therefore
depends only on k,R,d, not on individual source values.

Integrating this proved envelope gives actual whole-plane bilinear
integrability and a bound C*mass(rho)*mass(sigma), where mass is the actual
sum of component L1 norms. It does not assume an operator bound or a flux
integrability premise. Actual source subtraction, already justified by
integrable kernel products, gives the difference estimate

`L1(flux(rho,sigma)-flux(rho',sigma')) <= C*(mass(rho-rho')*mass(sigma)
  + mass(rho')*mass(sigma-sigma'))`.

The source triangle bound controls varying source masses. Consequently
source convergence in the actual L1 component mass forces convergence
of the actual bilinear flux in L1 on the complete plane. The proof works
over an arbitrary index filter. Taking the real part and dividing by two
proves genuine integrability and L1 convergence of the physical
time-averaged normal-power density, including its absolute error.

Precise scope: compact outgoing source responses with one fixed support
ball and one fixed positive plane gap. The constants may deteriorate as
the gap tends to zero or the source ball grows. The theorem does not assert
uniformity over varying remote radial stacks, actual source polarization
convergence, the incoming part of reaction/incident waves, or the complete
channel construction. Those require their own proved inputs. Within the
stated class, actual source L1 convergence is the premise; the resulting
whole-plane flux L1 convergence is fully derived.

No standalone custom axiom/constant declarations or proof-hole tokens
occur in the source. The frozen tail and polar-integration dependencies
were not modified.

## Independent root verification on resumption

Full source reviewed and pinned Lean compiler returned exit0. All 8 selected reports use only the standard foundations. Source SHA256 `0e91cb48b1c83951096d4cfcf1c34c43dcdfc77917734ddcd299142b33896d61`. Independent log: `lean/logs/MaxwellPlaneL1-independent-root.log`. Actual definitions and hypotheses were checked; this result does not close the outstanding full Maxwell/OQ14 constructions.
