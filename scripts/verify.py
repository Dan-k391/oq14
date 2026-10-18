"""Deterministic finite-dimensional and exact-formula diagnostics, NOT a Maxwell simulation."""
from pathlib import Path
import csv, hashlib, json, math, platform, subprocess
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'output'
OUT.mkdir(exist_ok=True)

def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()

def norm(a): return float(np.linalg.norm(a,2))

def pair(J,gamma,delta=0.,loss=0.):
    rate=gamma+loss
    den=(rate-1j*delta)**2+J**2
    x=np.sqrt(2*gamma)*(rate-1j*delta)/den
    y=-1j*np.sqrt(2*gamma)*J/den
    t=np.sqrt(2*gamma)*y
    r=-1+np.sqrt(2*gamma)*x
    return x,y,t,r

def bisection(f,left,right,n=100):
    fl=f(left)
    assert fl*f(right)<0
    for _ in range(n):
        mid=(left+right)/2
        if f(mid)*fl>0: left=mid; fl=f(left)
        else: right=mid
    return (left+right)/2

checks=[]
rows=[]
rng=np.random.default_rng(140014)
tau=.9
rho=.01
for N in (2,4,8):
    js=10.**(-np.arange(1,N+1,dtype=float))
    I=np.eye(N); zero=np.zeros_like(I)
    B0=np.block([[I,1j*I],[1j*I,I]])
    G=np.diag(np.sqrt(np.concatenate([js,js])))
    EL=np.vstack([I,zero]); ER=np.vstack([zero,I])
    X=np.linalg.solve(G@B0@G,np.sqrt(2)*G@EL)
    T=np.sqrt(2)*ER.T@G@X
    R=-I+np.sqrt(2)*EL.T@G@X
    energy=X.conj().T@X
    XL=X[:N,:]; XR=X[N:,:]
    B=XL.conj().T@np.diag(js)@XR
    current=1j*(B-B.conj().T)
    assert norm(T+1j*I)<1e-12 and norm(R)<1e-12
    assert norm(energy-np.diag(1/js))/max(1/js)<1e-12
    assert norm(current-I)<1e-12
    H=rng.normal(size=(2*N,2*N)); H=(H+H.T)/2; H/=norm(H)
    F=1j*rho*H
    perturbed=np.linalg.inv(B0+F)
    S=-np.eye(2*N)+2*perturbed
    Tp=2*ER.T@perturbed@EL
    err=norm(Tp+1j*I); bound=rho/(1-rho/np.sqrt(2))
    assert err<=bound+1e-13 and bound<1-np.sqrt(tau)
    assert norm(S.conj().T@S-np.eye(2*N))<1e-12
    row={'N':N,'weakest_J':float(min(js)),
         'minimum_transmission_singular_value':float(min(np.linalg.svd(T,compute_uv=False))),
         'power_balance_residual':norm(T.conj().T@T+R.conj().T@R-I),
         'model_current_gram_residual':norm(current-I),
         'max_model_internal_energy':float(max(np.linalg.eigvalsh(energy))),
         'weakest_pair_FWHM':float(2*np.sqrt(2)*min(js)),
         'detuning':0.,'perturbation_weighted_norm':rho,
         'perturbed_T_error':err,'error_bound':float(bound),
         'perturbed_min_power':float(min(np.linalg.svd(Tp,compute_uv=False))**2),
         'full_model_unitarity_residual':norm(S.conj().T@S-np.eye(2*N)),
         'physical_section_flux_gram':None,'physical_absolute_bypass':None,
         'Maxwell_model_reduction_error':None}
    rows.append(row)
checks.append({'name':'N=2,4,8 pair networks and weighted passive reciprocal perturbations','passed':True})

max_pair_balance=0.
for J in (1.,1e-4,1e-8):
    for scale in (.2,1.,3.):
        for detune in (-3.,-.3,0.,.3,3.):
            x,y,t,r=pair(J,scale*J,detune*J)
            max_pair_balance=max(max_pair_balance,abs(abs(t)**2+abs(r)**2-1))
            assert abs(abs(t)**2+abs(r)**2-1)<2e-14
    for detune in (0.,.3,math.sqrt(2),3.):
        _,_,t,_=pair(J,J,detune*J)
        assert abs(abs(t)**2-1/(1+detune**4/4))<2e-14
checks.append({'name':'exact pair line shape and lossless balance','passed':True,'max_residual':max_pair_balance})

# Checkerboard angular monodromy: full turn has a periodic eigenvector.
corner=[]
for eps in (1.1,2.,4.,12.):
    b=1/eps; alpha=4/math.pi*math.atan(math.sqrt(b)); t=alpha*math.pi/2
    def transfer(a): return np.array([[math.cos(t),math.sin(t)/a],[-a*math.sin(t),math.cos(t)]])
    half=transfer(b)@transfer(1.)
    _,_,vh=np.linalg.svd(half+np.eye(2)); v=vh[-1]
    residual=norm(((half@half-np.eye(2))@v).reshape(2,1))
    assert 0<alpha<1 and abs(np.trace(half)+2)<1e-13 and residual<1e-12
    corner.append({'eps_plus':eps,'alpha':alpha,'periodicity_residual':residual})
checks.append({'name':'corner exponent and angular transfer relation','passed':True})

# Analytic forced projection for F=1: p=-k^2 r^2/(4-alpha^2).
for alpha in (.1,.5,.9):
    for radius in (.01,.2,1.):
        p=-(radius**alpha*radius**(2-alpha)/(2-alpha)-radius**(-alpha)*radius**(2+alpha)/(2+alpha))/(2*alpha)
        exact=-radius**2/(4-alpha**2)
        assert abs(p-exact)<1e-14
checks.append({'name':'finite-frequency radial projection sign and factors','passed':True})

# Exact compensated TE l=1 Bragg profile, dimensionless k0=omega=mu0=1.
def jhat(x): return math.sin(x)/x-math.cos(x)
def djhat(x): return math.cos(x)/x-math.sin(x)/x**2+math.sin(x)
x0=bisection(djhat,2.,3.); q=2.; ain=math.sqrt(2.)
bragg=[]
for M in (0,2,4,8):
    radius=x0+M*math.pi/2*(1+1/q)
    hp=-np.exp(1j*radius)*(1j-1/radius-1j/radius**2)
    hm=np.conj(hp)
    bout=-ain*hm/hp
    C=2j*ain/hp*((-q)**M)/jhat(x0)
    transfer_low=np.array([[0.,1.],[-1.,0.]])
    transfer_high=np.array([[0.,1/q],[-q,0.]])
    v=np.linalg.matrix_power(transfer_high@transfer_low,M)@np.array([C*jhat(x0),0.])
    assert abs(v[0]-2j*ain/hp)<1e-11
    assert abs(abs(bout/ain)-1)<1e-14
    bragg.append({'pairs':M,'radius':float(radius),'core_amplitude_squared':float(abs(C)**2),
                  'core_amplitude_squared_over_q2M':float(abs(C)**2/q**(2*M)),
                  'reflection_power':float(abs(bout/ain)**2),'eps_upper_used':float(q*q+2/x0**2)})
checks.append({'name':'exact radial Bragg transfer and incoming-power identity','passed':True})

# Quadrature refinement is of explicit LOCAL fields, not a mesh-refined device.
flux_refinement=[]
L=W=1.; ms=np.array([1,2,3,4,5,6,7,8]); kap=np.sqrt((math.pi*ms)**2-1.)
amps=np.sqrt(2/kap)
for points in (33,65,129):
    xx=np.linspace(0,L,points)
    sins=np.sin(np.outer(xx,math.pi*ms))
    f=amps*(1+1j); fp=kap*amps*(-1+1j)
    E=sins*f; H=sins*(1j*fp)
    matrices=np.empty((points,8,8),dtype=complex)
    for p in range(points):
        raw=-np.outer(np.conj(H[p]),E[p])
        matrices[p]=(raw+raw.conj().T)/4
    Q=np.trapezoid(matrices,xx,axis=0)
    error=norm(Q-np.eye(8))
    assert error<1e-12
    flux_refinement.append({'quadrature_points':points,'gram_error':error})
checks.append({'name':'local evanescent coherent flux Gram under quadrature refinement','passed':True})

# Basic inference failures: exact matrices, including coherent bypass.
Q=np.array([[1.,2.],[2.,1.]])
assert min(np.linalg.eigvalsh(Q))==-1.
F=np.array([[0.,1.],[1.,0.]]); v=np.array([1.,1.])/math.sqrt(2)
assert abs(v@F@v-1)<1e-14 and np.all(np.diag(F)==0)
checks.append({'name':'positive diagonals and zero signed bypass do not imply coherent constraints','passed':True})

result={'kind':'diagnostics, not continuum certification','seed':140014,
        'source_commit':git('rev-parse','HEAD'),'dirty_worktree':bool(git('status','--porcelain')),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'python':platform.python_version(),'numpy':np.__version__,
        'checks':checks,'pair_networks':rows,'corner_exponents':corner,'bragg':bragg,
        'local_flux_quadrature':flux_refinement,
        'limitations':['No physical N-channel family was synthesized.',
        'Physical section Gram, bypass, finite-device and model-reduction errors are unavailable, not zero.',
        'No full hotspot scattering discretization or formal theorem prover was run.',
        'Floating-point identities corroborate handwritten proofs and are not certified error bounds.']}
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
with (OUT/'model-diagnostics.csv').open('w',newline='',encoding='utf-8') as f:
    writer=csv.DictWriter(f,fieldnames=rows[0]); writer.writeheader(); writer.writerows(rows)
print(json.dumps({'passed':len(checks),'source_commit':result['source_commit'],'dirty':result['dirty_worktree'],
                  'N':[r['N'] for r in rows], 'max_pair_balance_residual':max_pair_balance},indent=2))
