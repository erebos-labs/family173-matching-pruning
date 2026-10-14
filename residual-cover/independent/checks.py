"""Audit-owned literal supports/minimum-cover oracle and non-removable checks."""
from pathlib import Path
import copy,functools,itertools,json,random,sys
ROOT=Path(__file__).resolve().parents[1];PKG=ROOT
sys.path.insert(0,str(PKG/'src'))
import convert as c,verify as v

def ck(x,msg):
    if not x:raise RuntimeError(msg)
def subsets(S):
    a=sorted(S)
    for mask in range(1<<len(a)):yield {x for k,x in enumerate(a) if mask>>k&1}
@functools.lru_cache(maxsize=200000)
def mincover(L,R,E):
    if len(L)>len(R):return mincover(R,L,frozenset((b,a) for a,b in E))
    best=None
    for U in subsets(L):
        K=frozenset(U|{b for a,b in E if a not in U})
        if best is None or len(K)<len(best):best=K
    return best
def oracle(G):return mincover(*map(frozenset,G))
def size(G):return len(oracle(G))
def restriction(G,U):return G[0]&U,G[1],{(a,b) for a,b in G[2] if a in U}
def cert(G,q):
    M=[(tuple(a),tuple(b)) for a,b in q['matching']];K=set(map(tuple,q['cover']))
    ck(all(e in G[2] for e in M),'literal nonedge')
    ck(len({a for a,b in M})==len(M)==len({b for a,b in M}),'duplicate endpoint')
    ck(len(K)==len(q['cover']) and K<=G[0]|G[1] and all(a in K or b in K for a,b in G[2]),'literal cover')
    ck(len(K)==len(M),'certificate cardinalities')
    return dict(M)

def literal(data):
    n=data['n'];X=list(itertools.product(range(n),repeat=2))
    E=set(map(tuple,data['arrows']));R=set(map(tuple,data['R']));C=set(map(tuple,data['C']))
    conflict=lambda r,z:(r[0],z[0]) in E and (z[1],r[1]) in E
    Z={z for z in X if any(r[1]==z[1] and t[0]==z[0] and conflict(r,t) for r in R for t in C)}
    H={h for h in X if any(r[0]==h[0] and t[1]==h[1] and conflict(r,t) for r in R for t in C)}
    ts=lambda tag,p:{(tag,*x) for x in p}
    RR,CC,HH,ZL,ZR=ts('R',R),ts('C',C),ts('H',H),ts('ZL',Z),ts('ZR',Z)
    LE={(a,b) for a in RR for b in ZR if a[2]==b[2] and (a[1],b[1]) in E}
    NE={(a,b) for a in ZL for b in CC if a[1]==b[1] and (b[2],a[2]) in E}
    BE={(a,b) for a in RR for b in HH if a[1]==b[1] and (b[2],a[2]) in E}
    AE={(a,b) for a in HH for b in CC if a[2]==b[2] and (a[1],b[1]) in E}
    CE={(a,b) for a in RR for b in CC if (a[1],b[1]) in E and (b[2],a[2]) in E}
    return E,Z,H,dict(L=(RR,ZR,LE),N=(ZL,CC,NE),B=(RR,HH,BE),A=(HH,CC,AE),Gamma=(RR|ZL,CC|ZR,CE|LE|NE))

def selected(P,I,E,order):
    out=set();prefix=set();last=0
    for i in order:
        if i not in I:continue
        prefix.add(i)
        g=({('P',p) for p in P},{('I',x) for x in prefix},
           {(('P',p),('I',x)) for p in P for x in prefix if (p,x) in E})
        now=size(g);ck(now in (last,last+1),'oracle increment')
        if now>last:out.add(i)
        last=now
    return out

systems=inclusions=0
for mask in range(512):
    pp=list(itertools.product(range(3),repeat=2));E={e for k,e in enumerate(pp) if mask>>k&1}
    ss=list(subsets({0,1,2}))
    for order in [(0,1,2),(2,1,0)]:
        cache={}
        for P,I in itertools.product(ss,repeat=2):
            expected=selected(P,I,E,order);chosen,proof=c.selector(P,I,E,order)
            ck(chosen==expected,'selector/oracle mismatch')
            verified=v.selection(P,I,E,order,{'coordinate':0,**proof},0,3)
            ck(verified==expected,'certified selector mismatch')
            cache[frozenset(P),frozenset(I)]=expected;systems+=1
        for P,I,J in itertools.product(ss,repeat=3):
            S=cache[frozenset(P),frozenset(I)]
            if P<=J:ck(S<=cache[frozenset(J),frozenset(I)],'left monotonicity');inclusions+=1
            if J<=I:ck(S&J<=cache[frozenset(P),frozenset(J)],'right restriction');inclusions+=1
print(json.dumps(dict(event='independent_selectors',status='PASS',supports=512,orders=2,
 systems=systems,inclusions=inclusions),sort_keys=True),flush=True)

rng=random.Random(173105941);inputs=requests=nontrivial=nonminimum=strictW=seedtests=0
def exercise(data):
    global inputs,requests,nontrivial,nonminimum,strictW,seedtests
    E,Z,H,G=literal(data)
    ck(c.supports(data)[-1]==G and v.rebuild(data)[-1]==G,'literal supports disagree')
    lcert,LM,_=c.solve(G['L']);cert(G['L'],lcert);ck(len(LM)==size(G['L']),'L optimum oracle')
    # A fresh arbitrary legal, possibly nonmaximum Gamma seed.
    edges=sorted(G['Gamma'][2]);rng.shuffle(edges);seed={};used=set()
    for a,b in edges:
        if a not in seed and b not in used and rng.random()<0.35:seed[a]=b;used.add(b)
    account=c.normalized_accounting(G,seed)
    rebuilt=v.rebuild(data);v.verify_accounting(data,rebuilt,account);seedtests+=1
    for name in ['L','N','B','A','Gamma']:
        M=cert(G[name],account['certificates'][name])
        if name!='Gamma' or data['n']<=2:ck(len(M)==size(G[name]),'graph optimum oracle '+name)
    extracted=cert_matching={tuple(a):tuple(b) for a,b in account['extracted']}
    ck(all(e in G['B'][2] for e in extracted.items()) and len(set(extracted.values()))==len(extracted),'extraction illegal')
    ck(len(extracted)>=max(0,len(seed)-len(Z)),'arbitrary seed extraction bound')
    keys=sorted(LM);Ws={frozenset(keys),frozenset(keys[:len(keys)//2]),frozenset(keys[::2])}
    orders={tuple(range(data['n'])),tuple(reversed(range(data['n'])))}
    if data['n']>=3:
        oo=list(range(data['n']));rng.shuffle(oo);orders.add(tuple(oo))
    for WW in Ws:
        W=set(WW);BG=restriction(G['B'],W);best=set(oracle(BG))
        covers={frozenset(best),frozenset(W),frozenset(G['B'][1])}
        extras=(BG[0]|BG[1])-best
        if extras:covers.add(frozenset(best|{min(extras)}))
        for KB,order in itertools.product(covers,orders):
            KB=set(KB);ck(all(a in KB or b in KB for a,b in BG[2]),'oracle KB')
            req={'W':[list(u[1:]) for u in sorted(W)],
                 'alpha':c.encode_matching({u:LM[u] for u in W}),
                 'KB':[list(x) for x in sorted(KB)],'order':list(order)}
            out=c.convert(data,req);v.verify_conversion(data,req,out)
            KN=set(map(tuple,out['KN']))
            ck(KN<=G['N'][0]|G['N'][1] and all(a in KN or b in KN for a,b in G['N'][2]),'literal N coverage')
            ck(len(KN)<=len(Z)-len(W)+len(KB),'cover budget')
            if out['branch']=='ordered-selector':
                remain=W-KB;V=KB&G['B'][1];Q=set();D=set()
                for j in range(data['n']):
                    P={p for _,p,jj in remain if jj==j};I={i for i,jj in Z if jj==j}
                    Q|={('ZL',i,j) for i in selected(P,I,E,order)}
                for s in range(data['n']):
                    P={p for _,p,ss in V if ss==s};I={i for i,ss in map(tuple,data['C']) if ss==s}
                    D|={('C',i,s) for i in selected(P,I,E,order)}
                ck(KN==(G['N'][0]-Q)|D and len(Q)==len(remain) and len(D)<=len(V),'independent KN construction')
                ck(all(b in D for a,b in G['N'][2] if a in Q),'closure/neighbor containment')
            requests+=1;nontrivial+=len(KB)<len(W);nonminimum+=len(KB)>len(best);strictW+=W<G['L'][0]
    inputs+=1

for n in range(3):
    pp=list(itertools.product(range(n),repeat=2));ss=[[list(e) for e in S] for S in subsets(pp)]
    for E,R,C in itertools.product(ss,repeat=3):exercise(dict(n=n,arrows=E,R=R,C=C))
for k in range(240):
    n=3+k%3;pp=list(itertools.product(range(n),repeat=2));prob=(0.2,0.5,0.8)[k//3%3]
    exercise(dict(n=n,arrows=[list(e) for e in pp if rng.random()<prob],
                  R=[list(x) for x in rng.sample(pp,rng.randrange(7))],
                  C=[list(x) for x in rng.sample(pp,rng.randrange(7))]))
print(json.dumps(dict(event='independent_conversion',status='PASS',inputs=inputs,
 exhaustive_small_inputs=4105,fresh_larger_inputs=240,requests=requests,nontrivial=nontrivial,
 nonminimum_covers=nonminimum,strict_W_requests=strictW,arbitrary_seed_extractions=seedtests),sort_keys=True),flush=True)

base=v.load(PKG/'fixtures/repeated-H-positive.json');mutants=[]
def add(name,f):
    q=copy.deepcopy(base);f(q);mutants.append((name,q))
add('valid_order_changed_without_reproof',lambda q:q['request'].__setitem__('order',[1,0]))
add('missing_selector_prefix',lambda q:q['conversion']['selectors_Z'][0]['prefix_certificates'].pop())
add('wrong_selector_coordinate',lambda q:q['conversion']['selectors_Z'][0].__setitem__('coordinate',1))
add('missing_accounting_cover',lambda q:q['accounting']['certificates']['Gamma']['cover'].pop())
add('wrong_output_branch',lambda q:q['conversion'].__setitem__('branch','all-Z'))
for name,q in mutants:
    try:v.verify_record(q)
    except ValueError:continue
    else:raise RuntimeError('accepted corruption '+name)
print(json.dumps(dict(event='extra_corruptions',status='PASS',rejected=[x[0] for x in mutants]),sort_keys=True),flush=True)
