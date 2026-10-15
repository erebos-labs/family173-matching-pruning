"""Bounded offline source-closure replay; never imports a package's cached outputs."""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT / 'project'
PIN = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0', PYTHONDONTWRITEBYTECODE='1')
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output', type=Path, required=True, help='new output directory OUTSIDE the source checkout')
ap.add_argument('--lean-bin', type=Path, help='directory containing the pinned lean executable')
ap.add_argument('--fetch', action='store_true', help='fetch exact pinned dependency sources if missing; no binary caches')
args = ap.parse_args()
if not __debug__: ap.error('run without -O; source-closure integrity assertions must remain active')
FRESH = args.output.resolve()
if FRESH.exists(): ap.error('output already exists; preserve previous receipts and use a new directory')
if FRESH.is_relative_to(ROOT.parent): ap.error('output must be outside the release source tree')
lean = args.lean_bin / 'lean' if args.lean_bin else Path(shutil.which('lean') or '/missing/lean')
TOOL = lean.resolve().parent.parent
FRESH.mkdir(parents=True)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(root, *args):
    cp = subprocess.run(['git', '-C', str(root), *args], env=ENV, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if cp.returncode:
        raise RuntimeError(cp.stderr)
    return cp.stdout.strip()

def imports(path):
    # Preserve newlines while removing nested Lean comments and quoted strings.
    text = path.read_text(); out = []; i = 0; depth = 0; string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\': out.extend('  '); i += 2
            elif text[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i); j = len(text) if j < 0 else j
            out.extend(' ' * (j-i)); i = j
        elif text[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(text[i]); i += 1
    result = []
    for line in ''.join(out).splitlines():
        match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+?)\s*$', line)
        if match:
            for module in match[1].split():
                if not re.fullmatch(r"[A-Za-z_][\w.']*", module):
                    raise ValueError(f'unparsed import in {path}: {module}')
                result.append(module)
    return result

def main():
    manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
    packages = [('mathlib', '.deps/mathlib', PIN, 'https://github.com/leanprover-community/mathlib4')] + [
        (p['name'], '.lake/packages/' + p['name'], p['rev'], p['url'])
        for p in manifest['packages'] if p['type'] == 'git']
    pins = []; index = {}; duplicates = set()
    for name, relative, pin, url in packages:
        target = PROJECT / relative
        if not target.exists():
            if not args.fetch: raise RuntimeError('Missing source: '+relative+'; use --fetch or provide clean exact pinned Git sources')
            target.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['git','init','--quiet',str(target)],check=True,env=ENV)
            subprocess.run(['git','-C',str(target),'remote','add','origin',url],check=True,env=ENV)
            subprocess.run(['git','-C',str(target),'fetch','--depth','1','origin',pin],check=True,env=ENV)
            git(target,'checkout','--quiet','--detach',pin)
        if git(target,'rev-parse','HEAD') != pin: raise RuntimeError('Dependency pin mismatch: '+relative)
        if git(target,'status','--porcelain','--untracked-files=no'): raise RuntimeError('Dirty dependency: '+relative)
        pins.append({'package': name, 'revision': pin, 'source_root': str(target),
                     'git_source_clean': True, 'url':url})
        for rel in git(target, 'ls-files', '*.lean').splitlines():
            if rel.startswith(('.lake/', '.git/')) or rel == 'lakefile.lean': continue
            module = rel[:-5].replace('/', '.')
            if module in index: duplicates.add(module)
            else: index[module] = (name, target, target / rel)
    project_sources = [*PROJECT.glob('*.lean'), *(PROJECT/'Family173').rglob('*.lean'),
                       *(PROJECT/'OAI').rglob('*.lean')]
    project_sources = [p for p in project_sources if p.name != 'lakefile.lean']
    for path in project_sources:
        module = path.relative_to(PROJECT).as_posix()[:-5].replace('/', '.')
        assert module not in index
        index[module] = ('project', PROJECT, path)
    needed = set(); builtin = set(); dependencies = {}
    def visit(module):
        if module in needed or module in builtin: return
        if module.split('.')[0] in {'Init', 'Lean', 'Std', 'Lake'}:
            assert (TOOL/'lib/lean'/(module.replace('.', '/')+'.olean')).exists(), module
            builtin.add(module); return
        assert module in index and module not in duplicates, ('unresolved/ambiguous source', module)
        needed.add(module); dependencies[module] = set(imports(index[module][2]))
        for dep in dependencies[module]: visit(dep)
    for path in project_sources:
        visit(path.relative_to(PROJECT).as_posix()[:-5].replace('/', '.'))
    version = subprocess.check_output([str(TOOL/'bin/lean'), '--version'], text=True).strip()
    assert 'version 4.34.1,' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version
    assert (PROJECT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
    sources = {m: {'module': m, 'package': index[m][0], 'source': str(index[m][2]),
                   'sha256': digest(index[m][2]), 'imports': sorted(dependencies[m])}
               for m in sorted(needed)}
    plan = {'compiler': version, 'toolchain': str(TOOL), 'compiler_sha256': digest(TOOL/'bin/lean'),
            'pins': pins, 'modules': len(needed), 'local_modules': len(project_sources),
            'external_modules': sum(index[m][0] != 'project' for m in needed),
            'trusted_compiler_distribution_modules': sorted(builtin), 'sources': sources,
            'cache_policy': 'Only fresh central output on LEAN_PATH; no cached project or package outputs.',
            'semantic_options_mathlib': ['pp.unicode.fun=true', 'autoImplicit=false', 'maxSynthPendingDepth=3'],
            'limits': 'Pinned compiler distribution is trusted, not bootstrapped. Needed source closure only; not all Mathlib.'}
    plan_file = FRESH/'BUILD_PLAN.json'
    if plan_file.exists(): assert json.loads(plan_file.read_text()) == plan
    else: plan_file.write_text(json.dumps(plan, indent=2)+'\n')
    print(json.dumps({k: plan[k] for k in ['compiler', 'modules', 'local_modules', 'external_modules', 'cache_policy']}), flush=True)
    out = FRESH/'lib/lean'; out.mkdir(parents=True)
    logs = FRESH/'module-logs'; logs.mkdir()
    assert not any(out.iterdir())
    env = dict(ENV, PATH=str(TOOL/'bin')+os.pathsep+os.environ['PATH'],
               LEAN_PATH=str(out), LEAN_SRC_PATH='', MATHLIB_NO_CACHE_ON_UPDATE='1')
    started = time.monotonic(); done = set(); pending = set(needed); records = []; terminal = None
    def build(module):
        package, cwd, source = index[module]
        obj = out/(module.replace('.', '/')+'.olean'); obj.parent.mkdir(parents=True, exist_ok=True)
        opts = ['-Dpp.unicode.fun=true', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3'] if package == 'mathlib' else (['-DautoImplicit=false'] if package == 'project' else [])
        cmd = [str(TOOL/'bin/lean'), '-t', '0', '-j', '1', *opts, '-o', str(obj), str(source.relative_to(cwd))]
        log = logs/(module+'.log'); start = time.monotonic()
        with log.open('w') as stream:
            try: code = subprocess.run(cmd, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=900).returncode
            except subprocess.TimeoutExpired: code = 'TIMEOUT'
        return {'module': module, 'package': package, 'command': cmd, 'cwd': str(cwd),
                'exit_code': code, 'seconds': round(time.monotonic()-start, 3),
                'source_sha256': sources[module]['sha256'], 'log': str(log),
                'log_sha256': digest(log), 'object': str(obj),
                'object_sha256': digest(obj) if code == 0 else None}
    def save(status):
        r = {'status': status, 'planned': len(needed), 'completed': len(done),
             'local_completed': sum(index[m][0] == 'project' for m in done),
             'external_completed': sum(index[m][0] != 'project' for m in done),
             'initial_compiled_artifacts': 0, 'cached_package_outputs_used': False,
             'LEAN_PATH': str(out), 'seconds': round(time.monotonic()-started, 3),
             'records': records, 'sources_unchanged': all(digest(index[m][2]) == sources[m]['sha256'] for m in needed)}
        (FRESH/'BUILD_RESULT.json').write_text(json.dumps(r, indent=2)+'\n')
    running = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        while pending or running:
            if not terminal and shutil.disk_usage(ROOT).free < 4*1024**3: terminal = 'STOP_DISK_RESERVE'
            if not terminal and time.monotonic()-started > 7200: terminal = 'STOP_TWO_HOUR_BUDGET'
            if not terminal:
                for module in sorted(pending):
                    if len(running) >= 4: break
                    if (dependencies[module] & needed) <= done:
                        pending.remove(module); running[executor.submit(build, module)] = module
            if not running:
                if pending and not terminal: terminal = 'UNRESOLVED_DEPENDENCY_GRAPH'
                break
            finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                module = running.pop(future); record = future.result(); records.append(record)
                if record['exit_code'] == 0: done.add(module)
                else: terminal = 'FAILED_SOURCE_BUILD'
                if len(records) % 25 == 0 or record['exit_code'] != 0:
                    save(terminal or 'RUNNING'); print(len(done), '/', len(needed), module, record['exit_code'], flush=True)
    status = 'PASS' if len(done) == len(needed) and terminal is None else terminal or 'INCOMPLETE'
    save(status); print('FINAL', status, len(done), '/', len(needed), flush=True)
    if status != 'PASS': raise SystemExit(1)
    allowed={'propext','Classical.choice','Quot.sound'}
    def reports(text):
        parsed=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
        parsed += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
        for name, raw in parsed:
            if not {a.strip() for a in raw.split(',') if a.strip()} <= allowed:
                raise RuntimeError('unexpected axiom: '+name)
        return parsed
    expected=json.loads((ROOT/'EXPECTED_AXIOM_REPORTS.json').read_text())
    counts={}
    for module,names in expected.items():
        entries=reports((logs/(module+'.log')).read_text())
        if len(entries)!=len(names) or {n for n,_ in entries}!=set(names):
            raise RuntimeError('missing/duplicate/unexpected axiom reports: '+module)
        counts[module]=len(entries)
    scoped=[p for p in project_sources]
    forbidden={str(p.relative_to(PROJECT)):re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',p.read_text()) for p in scoped}
    if any(forbidden.values()): raise RuntimeError('forbidden proof-source token')
    audit=ROOT/'LocalSemanticAudit.lean';auditlog=FRESH/'LocalSemanticAudit.log'
    cmd=[str(TOOL/'bin/lean'),'-t','0','-DautoImplicit=false','-o',str(FRESH/'LocalSemanticAudit.olean'),audit.name]
    q=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,text=True)
    auditlog.write_text(q.stdout+q.stderr)
    audit_reports=reports(auditlog.read_text())
    expected_semantics={'LocalFinalAudit.literalObjective_exact','LocalFinalAudit.actual_minimum_semantics','LocalFinalAudit.every_positive_size','LocalFinalAudit.real_counterexample_nonvacuous'}
    if q.returncode or len(audit_reports)!=4 or {n for n,_ in audit_reports}!=expected_semantics: raise RuntimeError('semantic acceptance failed')
    result={'status':'PASS','build_modules':len(done),'local_modules':len(project_sources),'external_modules':sum(index[m][0]!='project' for m in done),'axiom_report_counts':counts,'semantic_reports':4,'allowed_axioms':sorted(allowed),'source_token_scan':'PASS','cache_policy':plan['cache_policy'],'limits':plan['limits']}
    (FRESH/'ACCEPTANCE.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__ == '__main__': main()
