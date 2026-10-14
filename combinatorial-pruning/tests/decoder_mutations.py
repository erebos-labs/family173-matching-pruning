"""Regressions for exact certificate coordinate and schema decoding."""
import copy,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
import verify

def check(value,message):
    if not value:raise RuntimeError(message)

records={p.stem:json.loads(p.read_text()) for p in (ROOT/'fixtures').glob('*.json')}
loop=records['one-loop-all-tags']
trace=next(r for r in records.values() if r['normalization_trace'])
extension=next(r for r in records.values() if r['core_extension']['paths'])
selected=next(r for r in records.values() if r['core_extension']['selected'])
mutations=[]

def alias(vertex,kind):
    for pos in (1,2):
        if kind=='float' or vertex[pos] in (0,1):
            vertex[pos]=float(vertex[pos]) if kind=='float' else bool(vertex[pos])
            return
    raise RuntimeError('No Boolean-equivalent test coordinate')

def add(label,record,vertices,kind):
    q=copy.deepcopy(record)
    values=vertices(q)
    v=next((v for v in values if kind=='float' or any(x in (0,1) for x in v[1:])),None)
    check(v is not None,'No alias candidate '+label)
    alias(v,kind);mutations.append((label+'_'+kind,q,'certificate coordinates must be exact integers'))

locations=[
 ('graph_matching_left',loop,lambda q:[e[0] for e in q['certificates']['Gamma']['matching']]),
 ('graph_matching_right',loop,lambda q:[e[1] for e in q['certificates']['Gamma']['matching']]),
 ('graph_cover',loop,lambda q:q['certificates']['Gamma']['cover']),
 ('normalization_start',loop,lambda q:[v for e in q['normalization_start'] for v in e]),
 ('exposure_removed',loop,lambda q:[e['removed'] for e in q['exposure_deletions']['B_left']]),
 ('deletion_matching',records['opposite-arrows'],lambda q:[v for e in q['exposure_deletions']['N_left'] for pair in e['certificate']['matching'] for v in pair]),
 ('normalization_removed',trace,lambda q:[v for e in q['normalization_trace'] for v in e['removed']]),
 ('normalization_path',trace,lambda q:[v for e in q['normalization_trace'] for v in e['path']]),
 ('extension_path',extension,lambda q:[v for path in q['core_extension']['paths'] for v in path]),
 ('extension_final_matching',extension,lambda q:[v for e in q['core_extension']['final']['matching'] for v in e]),
 ('extension_selected',selected,lambda q:[v for e in q['core_extension']['selected'] for v in e])]
for kind in ['bool','float']:
    for label,record,get in locations:add(label,record,get,kind)
for value in [True,1.0]:
    q=copy.deepcopy(loop);q['schema']=value;mutations.append(('schema_'+type(value).__name__,q,'unknown schema'))
q=copy.deepcopy(loop);q['certificates']['Gamma']['matching'][0][0][0]=True
mutations.append(('nonstring_tag',q,'invalid certificate vertex tag'))
q=copy.deepcopy(loop);q['certificates']['Gamma']['matching'][0][0].pop()
mutations.append(('short_vertex',q,'certificate vertex must have three fields'))
# Deleting N-left Z leaves a remaining covered edge in opposite-arrows; exercise
# deletion-cover decoding separately from the deletion-matching control.
for kind in ['bool','float']:
    add('deletion_cover',records['opposite-arrows'],
        lambda q:[v for item in q['exposure_deletions']['B_left'] for v in item['certificate']['cover']],kind)

for label,q,expected in mutations:
    try:verify.verify_record(q)
    except ValueError as e:
        check(expected in str(e),'Unexpected rejection for '+label+': '+str(e))
    else:raise RuntimeError('Malformed certificate accepted: '+label)
valid=0
for r in records.values():
    verify.verify_record(r,pruning=True);valid+=1
print(json.dumps({'event':'decoder_mutations','status':'PASS','rejected':len(mutations),
                  'valid_integer_fixture_records':valid,'cases':[label for label,_,_ in mutations]},sort_keys=True))
