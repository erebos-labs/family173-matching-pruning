"""Reject integer-alias coordinate corruptions throughout certificates and paths."""
from copy import deepcopy
from pathlib import Path
import tempfile
import verify as v


def leaves(obj, path=()):
    if type(obj) is dict:
        for key, val in obj.items():
            yield from leaves(val, path + (key,))
    elif type(obj) is list:
        for index, val in enumerate(obj):
            yield from leaves(val, path + (index,))
    elif type(obj) is int:
        yield path, obj


def replace(obj, path, value):
    cur = obj
    for key in path[:-1]:
        cur = cur[key]
    cur[path[-1]] = value


def rejected(record):
    try:
        v.verify_record(record)
    except ValueError:
        return
    raise AssertionError('corrupted record accepted')


def main():
    root = Path(__file__).resolve().parents[1]
    bools = floats = other = 0
    for name in ('mixed-cover-positive', 'inherited-sharp-core'):
        original = v.load(root / 'fixtures' / (name + '.json'))
        v.verify_record(original)
        entries = list(leaves(original))
        for path, number in entries:
            bad = deepcopy(original); replace(bad, path, float(number)); rejected(bad); floats += 1
            if number in (0, 1):
                bad = deepcopy(original); replace(bad, path, bool(number)); rejected(bad); bools += 1
        print('PASS alias mutations at every integer leaf:', name, len(entries), 'integer positions')
    record = v.load(root / 'fixtures/repeated-H-positive.json')
    mutations = []
    bad = deepcopy(record); bad['request']['KB'].append(bad['request']['KB'][0]); mutations.append(bad)
    bad = deepcopy(record); bad['request']['alpha'][1] = deepcopy(bad['request']['alpha'][0]); mutations.append(bad)
    bad = deepcopy(record); bad['conversion']['KN'].pop(); mutations.append(bad)
    bad = deepcopy(record); bad['request']['order'] = [0, 0]; mutations.append(bad)
    bad = deepcopy(record); bad['conversion']['selectors_Z'][0]['selected'].pop(); mutations.append(bad)
    bad = deepcopy(record); bad['conversion']['selectors_Z'][0]['prefix_certificates'][-1]['cover'].pop(); mutations.append(bad)
    bad = deepcopy(record); bad['request']['KB'][0][0] = 'R'; mutations.append(bad)
    bad = deepcopy(record); bad['request']['W'][0][0] = -1; mutations.append(bad)
    bad = deepcopy(record); bad['request']['W'][0][0] = record['instance']['n']; mutations.append(bad)
    bad = deepcopy(record); bad['request']['alpha'][0][0].append(0); mutations.append(bad)
    bad = deepcopy(record); bad['extra_unchecked_field'] = 1; mutations.append(bad)
    for bad in mutations:
        rejected(bad); other += 1
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / 'bad.json'
        for text in ('{"n":1,"n":2}', '{"x":NaN}', '{"x":Infinity}', '{"x":-Infinity}'):
            path.write_text(text)
            try:
                v.load(path)
            except ValueError:
                other += 1
            else:
                raise AssertionError('non-strict JSON accepted')
    print('PASS rejected', floats, 'float aliases,', bools, 'bool aliases, and', other, 'other corruptions.')
    print('These tests are parser diagnostics, not a security or formal-verification claim.')


if __name__ == '__main__':
    main()
