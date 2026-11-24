#!/usr/bin/env python3
"""Recheck these research notes using the repository's pinned Lean/Mathlib.
Run from lean/: python3 research-notes/2026-11-24/verify.py
No native-backed decision tactic is used. Generated audit files are temporary.
"""
import hashlib,json,os,re,signal,subprocess,tempfile,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
THEOREMS={
 'Incidence':['incidence_count','common_line_unique','no_incidence_rectangle','line_intersection_at_most_one','rectangle_is_star','rectangle_edge_count_le_cost','rectangle_cover_cost'],
 'PlaneCircuit64':['candidate_monotone','candidate_size','one_positive','positive_pairs'],
 'Matching':['matching_cover_lower_bound','diagonal_cover_lower_bound'],
 'Plane13':['line_card','distinct_intersection','complement_admissible'],
 'Plane21':['diagonal','cover_lower_bound','edge_count','cover_cost','pair_unique','left_endpoints','left_cover_exact'],
}
results=[]
for module,names in THEOREMS.items():
    src=HERE/(module+'.lean'); text=src.read_text()
    assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b',text)
    audit=text+'\n'+'\n'.join('#print axioms PEqualNPResearch.'+module+'.'+n for n in names)+'\n'
    with tempfile.NamedTemporaryFile(mode='w',suffix='.lean',prefix='ResearchAudit',dir=Path.cwd(),delete=False) as f:
        f.write(audit); temp=Path(f.name)
    start=time.monotonic()
    p=subprocess.Popen(['/home/hermesops/.elan/bin/lake','env','lean',str(temp)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
    try:
        out,_=p.communicate(timeout=420)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGTERM)
        try: out,_=p.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGKILL);out,_=p.communicate()
        raise RuntimeError('Lean audit timeout: '+module+'\n'+out)
    finally: temp.unlink(missing_ok=True)
    (HERE/(module+'.audit.log')).write_text(out)
    print(out,flush=True)
    assert p.returncode==0,(module,p.returncode)
    assert len(out.splitlines())==len(names),out
    for name in names:
        line=next(l for l in out.splitlines() if "'PEqualNPResearch."+module+'.'+name+"'" in l)
        if 'does not depend on any axioms' in line: continue
        match=re.search(r'depends on axioms: \[([^]]*)\]',line)
        assert match,line
        assert set(x.strip() for x in match.group(1).split(','))<=ALLOWED,line
    results.append({'module':module,'theorems':len(names),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'axioms_allowed':True})
(HERE/'verification.json').write_text(json.dumps({'lean':'4.36.0','mathlib':'fc4f59e577feb1a4956671bc04ac18aaaf8cd842','results':results},indent=2)+'\n')
print('CHECKED:',sum(r['theorems'] for r in results),'auxiliary statements; no complete desk task proved.',flush=True)
