import numpy as np, json
from scipy.optimize import minimize
rng=np.random.default_rng(3)
def openax(d):
    P=np.diag(np.linspace(-1,1,d)).astype(complex); A=np.eye(d,k=1)+np.eye(d,k=-1)
    return (A/(2*np.cos(np.pi/(d+1)))).astype(complex),P
def closed3():
    return ((np.ones((3,3))-np.eye(3))/2).astype(complex),np.diag([-1.,0,1]).astype(complex)
def st(psi,T,P):
    psi=psi/np.linalg.norm(psi)
    cT=T@psi-np.vdot(psi,T@psi).real*psi; cP=P@psi-np.vdot(psi,P@psi).real*psi
    g=np.vdot(cT,cP); VT=np.linalg.norm(cT)**2; VP=np.linalg.norm(cP)**2
    return VT,VP,g.real,-2*g.imag
def Fmin(T,P,v,c,tries=12):
    d=T.shape[0]; best=np.inf
    for _ in range(tries):
        def f(x):
            VT,VP,cov,t=st(x[:d]+1j*x[d:],T,P)
            if abs(t)<1e-9: return 1e6
            F=(VT*VP-cov**2)/(t*t/4)   # = det Sigma / |det Omega| of the 2x2 block
            return F+1e4*(abs(t)/c-v)**2
        r=minimize(f,rng.normal(size=2*d),method="Nelder-Mead",options=dict(maxiter=8000,xatol=1e-10,fatol=1e-12))
        best=min(best,r.fun)
    return best
out={}
vs=np.round(np.linspace(0.02,1,50),3)
for name,(T,P) in {"closed3":closed3(),"open3":openax(3),"open4":openax(4)}.items():
    K=1j*(T@P-P@T); c=max(np.linalg.eigvalsh(K))
    out[name]={"c":c,"v":vs.tolist(),"F":[round(float(Fmin(T,P,v,c)),6) for v in vs]}
    print(name,"c=",round(c,5),"F(1)=",out[name]["F"][-1],"F(0.5)=",out[name]["F"][24],flush=True)
json.dump(out,open("band.json","w"))
import numpy as np, json
from scipy.optimize import minimize
rng=np.random.default_rng(5)
T=((np.ones((3,3))-np.eye(3))/2).astype(complex); P=np.diag([-1.,0,1]).astype(complex)
K=1j*(T@P-P@T); w,V=np.linalg.eigh(K); c=w[-1]; cstate=V[:,-1]
def st(psi):
    psi=psi/np.linalg.norm(psi)
    cT=T@psi-np.vdot(psi,T@psi).real*psi; cP=P@psi-np.vdot(psi,P@psi).real*psi
    g=np.vdot(cT,cP); return np.linalg.norm(cT)**2,np.linalg.norm(cP)**2,g.real,-2*g.imag,psi
vs=np.round(np.linspace(0.02,1,99),4); rows=[]
for v in vs:
    best=None
    for _ in range(16):
        def f(x):
            VT,VP,cov,t,_=st(x[:3]+1j*x[3:])
            if abs(t)<1e-9: return 1e6
            return (VT*VP-cov**2)/(t*t/4)+1e5*(abs(t)/c-v)**2
        r=minimize(f,rng.normal(size=6),method="Nelder-Mead",options=dict(maxiter=10000,xatol=1e-11,fatol=1e-13))
        if best is None or r.fun<best.fun: best=r
    psi=best.x[:3]+1j*best.x[3:]
    if v==1.0: psi=cstate
    VT,VP,cov,t,psi=st(psi)
    psi=psi*np.exp(-1j*np.angle(psi[1])) if abs(psi[1])>1e-9 else psi
    rows.append([float(v)]+[round(float(z),7) for p in psi for z in (p.real,p.imag)])
VT,VP,cov,t,_=st(cstate)
print("c-state F=",(VT*VP-cov**2)/(t*t/4), "v grid ok", len(rows))
json.dump({"c":float(c),"rows":rows},open("fiber.json","w"))
