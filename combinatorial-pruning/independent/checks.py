"""Audit-owned minimum-cover oracle, fresh cases and adversarial controls."""
from pathlib import Path
import copy,functools,itertools,json,random,sys
ROOT=Path(__file__).resolve().parents[1]
PKG=ROOT
sys.path.insert(0,str(PKG/'src'))
import producer,verify
def ck(v,s):
    if not v:raise RuntimeError(s)
def powers(S):
    a=list(S)
    for m in range(1<<len(a)):yield {x for k,x in enumerate(a) if m>>k&1}
@functools.lru_cache(maxsize=100000)
def optimum(L,R,E):
    if len(L)>len(R):return optimum(R,L,frozenset((v,u) for u,v in E))
    return min(len(S)+len({v for u,v in E if u not in S}) for S in powers(L))
def size(g):return optimum(*map(frozenset,g))
def remove(g,x):return (g[0]-{x},g[1]-{x},{(u,v) for u,v in g[2] if u!=x and v!=x})
def exposed(g,side):return {x for x in g[side] if size(remove(g,x))==size(g)}
def literal(data):
    n=data['n'];X=list(itertools.product(range(n),repeat=2))
    E=set(map(tuple,data['arrows']));R=set(map(tuple,data['R']));C=set(map(tuple,data['C']))
    conflict=lambda r,c:(r[0],c[0]) in E and (c[1],r[1]) in E
    Z={z for z in X if any(r[1]==z[1] and c[0]==z[0] and conflict(r,c) for r in R for c in C)}
    H={h for h in X if any(r[0]==h[0] and c[1]==h[1] and conflict(r,c) for r in R for c in C)}
    t=lambda name,pp:{(name,*p) for p in pp}
    L=t('R',R);N=t('C',C);HL=t('H',H);ZL=t('ZL',Z);ZR=t('ZR',Z)
    ge={(('R',*r),('C',*c)) for r in R for c in C if conflict(r,c)}
    le={(('R',*r),('ZR',*z)) for r in R for z in Z if r[1]==z[1] and (r[0],z[0]) in E}
    ne={(('ZL',*z),('C',*c)) for z in Z for c in C if z[0]==c[0] and (c[1],z[1]) in E}
    be={(('R',*r),('H',*h)) for r in R for h in H if r[0]==h[0] and (h[1],r[1]) in E}
    ae={(('H',*h),('C',*c)) for h in H for c in C if h[1]==c[1] and (h[0],c[0]) in E}
    return dict(Gamma=(L|ZL,N|ZR,ge|le|ne),L=(L,ZR,le),N=(ZL,N,ne),B=(L,HL,be),A=(HL,N,ae)),Z,H
def case(data):
    G,Z,H=literal(data);provided,Zp,Hp=verify.reconstruct(data)
    ck((G,Z,H)==(provided,Zp,Hp),'literal support mismatch')
    rec=producer.make_record(data);v=verify.verify_record(rec,pruning=True)
    for name,g in G.items():ck(v[name]==size(g),'cover optimum '+name)
    EB,EN,ENC=exposed(G['B'],0),exposed(G['N'],0),exposed(G['N'],1)
    for r,z in G['L'][2]:
        if r in EB:ck(('ZL',z[1],z[2]) in EN,'exposure transfer')
    ck(not any(r in EB and c in ENC for r,c in G['Gamma'][2] if r[0]=='R' and c[0]=='C'),'conflicting exposed endpoints')
    M={tuple(r):tuple(c) for r,c in rec['certificates']['Gamma']['matching']}
    T={r for r,c in M.items() if r[0]=='R' and c[0]=='C'}
    ck(not T&EB,'mandatory core')
    Bminus=(G['B'][0]-T,G['B'][1],{(r,h) for r,h in G['B'][2] if r not in T})
    ck(size(G['B'])==len(T)+size(Bminus),'core deletion identity')
    ck(v['pruning_optimum']==size(G['Gamma'])-len(Z),'objective')
    return int(bool(T))

count=cores=0
for n in range(3):
    pairs=list(itertools.product(range(n),repeat=2));ss=[[list(x) for x in S] for S in powers(pairs)]
    for E,R,C in itertools.product(ss,repeat=3):
        cores+=case(dict(n=n,arrows=E,R=R,C=C));count+=1
rng=random.Random(1739942)
for k in range(80):
    n=3+k%2;pp=list(itertools.product(range(n),repeat=2))
    data=dict(n=n,arrows=[list(x) for x in pp if rng.random()<0.55],
              R=[list(x) for x in rng.sample(pp,rng.randrange(5))],
              C=[list(x) for x in rng.sample(pp,rng.randrange(5))])
    cores+=case(data)
print(json.dumps(dict(event='independent_pair_geometry',status='PASS',exhaustive_inputs=count,
 fresh_seeded_inputs=80,graph_optima=5*(count+80),records_with_core=cores),sort_keys=True))

# Check the general elementary matching claims on all 3-by-3 bipartite supports.
L,R=set(range(3)),set(range(10,13));edges=list(itertools.product(L,R))
identity_tests=deletion_tests=addition_tests=0
for E in powers(edges):
    g=(L,R,E);el,er=exposed(g,0),exposed(g,1)
    ck(not any(u in el and v in er for u,v in E),'opposite exposure adjacency')
    for x in el:
        for y in R:
            ck(x in exposed(remove(g,y),0),'opposite-side deletion exposure');deletion_tests+=1
        for neighbors in powers(R):
            gg=(L|{3},R,E|{(3,v) for v in neighbors})
            ck(x in exposed(gg,0),'own-side addition exposure');addition_tests+=1
    mandatory=L-el
    for T in powers(mandatory):
        gg=(L-T,R,{(u,v) for u,v in E if u not in T})
        ck(size(g)==len(T)+size(gg),'arbitrary mandatory subset identity');identity_tests+=1
print(json.dumps(dict(event='generic_matching_facts',status='PASS',supports=512,
 mandatory_subset_identity_tests=identity_tests,right_deletion_tests=deletion_tests,
 left_addition_tests=addition_tests),sort_keys=True))

records={p.stem:json.loads(p.read_text()) for p in (PKG/'fixtures').glob('*.json')}
with_trace=next(r for r in records.values() if r['normalization_trace'])
with_core=next(r for r in records.values() if r['core_extension']['selected'])
with_path=next(r for r in records.values() if r['core_extension']['paths'])
mutants=[]
def add(name,r,f):
    q=copy.deepcopy(r);f(q);mutants.append((name,q))
add('missing_exposure_deletion',with_core,lambda q:q['exposure_deletions']['B_left'].pop())
add('duplicate_exposure_deletion',with_core,lambda q:q['exposure_deletions']['B_left'].append(q['exposure_deletions']['B_left'][0]))
add('missing_selected_core',with_core,lambda q:q['core_extension']['selected'].pop())
add('nonmaximum_normalization_start',with_core,lambda q:q['normalization_start'].pop())
add('omitted_normalization_trace',with_trace,lambda q:q.__setitem__('normalization_trace',[]))
add('wrong_normalization_side',with_trace,lambda q:q['normalization_trace'][0].__setitem__('side','B'))
add('duplicate_path_vertex',with_path,lambda q:q['core_extension']['paths'][0].append(q['core_extension']['paths'][0][0]))
add('omitted_extension_trace',with_path,lambda q:q['core_extension'].__setitem__('paths',[]))
rejected=[]
for name,q in mutants:
    try:verify.verify_record(q)
    except (ValueError,TypeError,KeyError,IndexError,AttributeError) as e:rejected.append(dict(name=name,reason=str(e)))
    else:raise RuntimeError('accepted corruption '+name)
invalid=[]
for name,patch in [('negative_n',{'n':-1}),('bool_n',{'n':True}),('duplicate_input',{'R':[[0,0],[0,0]]}),('bool_pair',{'R':[[False,0]]}),('out_of_domain',{'R':[[9,0]]})]:
    q=copy.deepcopy(records['one-loop-all-tags']);q['instance'].update(patch)
    try:verify.verify_record(q)
    except (ValueError,TypeError,KeyError,IndexError,AttributeError):invalid.append(name)
    else:raise RuntimeError('accepted invalid input '+name)
print(json.dumps(dict(event='additional_corruptions',status='PASS',rejected=rejected,
 invalid_inputs_rejected=invalid),sort_keys=True))
# Hardened edition rejects numerically equivalent Boolean/float aliases.
g,_,_=literal(records['one-loop-all-tags']['instance'])
base=records['one-loop-all-tags']['certificates']['Gamma']
leniency=[]
for name,value in [('boolean_coordinate',False),('float_coordinate',0.0)]:
    q=copy.deepcopy(base);q['matching'][0][0][1]=value
    try:verify.check_certificate(g['Gamma'],q)
    except (ValueError,TypeError,KeyError):outcome='rejected'
    else:raise RuntimeError('accepted malformed certificate coordinate '+name)
    leniency.append(dict(case=name,outcome=outcome))
print(json.dumps(dict(event='hardened_certificate_formats',probes=leniency),sort_keys=True))
