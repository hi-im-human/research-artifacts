"""System review of commit-57. Review-only tests; no production implementation changes.

Run: GLAB_ENGINE=/path/to/engine PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python -m pytest -q this_file
Fixtures use actual registered Stage 2/3 checks. A reconstructed re-check bundle is
built here, not copied from the worker's archived Windows run.
"""
import copy
import json
import os
import sys
from pathlib import Path

import pytest

ENGINE = Path(os.environ['GLAB_ENGINE']).resolve()
sys.path.insert(0, str(ENGINE))
from glab.core.registry import ActionSpec, StateDraft
from glab.core.runfile import Run
from glab.two_rim.source import normalize_source
from glab.two_rim.material import build_material
from probes.stage4a.specimens import (prepare, SQUARE, E11, E11_DELTA,
                                      Prepared, maintained_registry, _summary)
from probes.stage4a.ideal import load_subject, enclose
from probes.stage4a.firewall import ideal_certificate
from probes.stage4a.classify import to_json, classify_seam
from probes.stage4a import recheck_mpmath as rc


@pytest.fixture(scope='module')
def e11():
    return prepare(E11)


@pytest.fixture(scope='module')
def square():
    return prepare(SQUARE, seams=['E0'])


def make_bundle(prepared, seams=('E9',)):
    m = prepared.run.get(prepared.material)['payload']
    bundle = {'delta': E11_DELTA, 'bits':128,
              'vertices': {v['id']:v['xyz'] for v in m['vertices']},
              'faces': [{k:f[k] for k in ('id','entry','exit','boundary','plane')} for f in m['faces']],
              'hinges': {e['id']:[e['lower'],e['upper']] for e in m['hinges']}, 'seams':{}}
    for seam in seams:
        s = load_subject(prepared, seam, E11_DELTA)
        enc = enclose(s.model, 128)
        cl = classify_seam(s.model, schedule=(128,))
        bundle['seams'][seam] = {'subject_id':s.id, 'chain':s.model.chain,
            'rings':s.model.rings, 'boxes':to_json(enc['boxes']), 'rows':to_json(cl['rows'])}
    return bundle


@pytest.fixture(scope='module')
def bundle(e11):
    return make_bundle(e11)


def run_recheck(bundle, tmp_path):
    inp,out = tmp_path/'input.json',tmp_path/'output.json'
    inp.write_text(json.dumps(bundle),encoding='ascii')
    return rc.main(str(inp),str(out))


def test_control_valid_square_is_source_linked(square):
    c = ideal_certificate(load_subject(square,'E0','1/4'))
    assert c['source_linked'] and c['seam_verdict'] == 'pass'


def test_control_e9_contains_known_overlap(e11):
    c = ideal_certificate(load_subject(e11,'E9',E11_DELTA))
    assert c['seam_verdict'] == 'fail' and c['classification']['pairs'] == 55
    assert any(set(r['pair']) == {'F10','F7'} and r['outcome'] == 'fail'
               for r in c['classification']['rows'])


def test_control_genuine_recheck_bundle_passes(bundle,tmp_path):
    r = run_recheck(bundle,tmp_path)
    assert r['failures'] == 0
    assert r['coordinates_contained'] == r['coordinates_checked'] == 88
    assert r['theorem_s_confirmed'] == 10
    assert r['axis_confirmed'] == 41 and r['witness_confirmed'] == 4


@pytest.mark.parametrize('delta',['-1','0','1/2','1','2'])
def test_A01_out_of_domain_delta_cannot_receive_ideal_verdict(square,delta):
    try:
        s = load_subject(square,'E0',delta)
        c = ideal_certificate(s,schedule=(64,))
    except (ValueError,TypeError,ArithmeticError):
        return  # Explicit refusal is acceptable, not a mathematical failure verdict.
    assert c['seam_verdict'] not in ('pass','fail'), c['seam_verdict']


def test_A02_model_for_safe_seam_cannot_certify_unsafe_spec(e11):
    s = load_subject(e11,'E9',E11_DELTA)
    original_id = s.id
    try:
        s.model = load_subject(e11,'E4',E11_DELTA).model
        c = ideal_certificate(s)
    except (AttributeError,ValueError,TypeError,ArithmeticError):
        return
    # Rebuilding from immutable source inputs would also be acceptable.
    assert not (c['subject']['id'] == original_id and c['source_linked']
                and c['seam_verdict'] == 'pass'), c['subject']


def wrong_source_prepared():
    reg=maintained_registry()
    reg.register_action(ActionSpec('review.wrong_material',1,'two_rim.source',{},'review-height-four',
        lambda st,p,se: StateDraft('two_rim.material',
            build_material(normalize_source(**dict(SQUARE,height='4'))),'exact')))
    run=Run(reg)
    source=run.apply('two_rim.source.normalize',1,SQUARE)['output']
    material=run.apply('review.wrong_material',1,{},source)['output']
    cut=run.apply('two_rim.cut.open',1,{'seam':'E0'},material)['output']
    pre={'source':_summary(run,run.check('two_rim.check.source',2,source,{})),
         'material':_summary(run,run.check('two_rim.check.material',2,material,{})),
         'cut:E0':_summary(run,run.check('two_rim.check.cut',1,cut,{}))}
    return Prepared(run,source,material,{'E0':cut},pre)


def test_control_wrong_source_with_full_evidence_is_refused():
    p=wrong_source_prepared()
    c=ideal_certificate(load_subject(p,'E0','1/4'))
    assert not c['source_linked'] and c['seam_verdict']=='not_source_linked'


def test_A02_dropping_failed_prerequisite_does_not_make_it_pass():
    p=wrong_source_prepared()
    assert any(r['claim']=='two_rim.material.matches_parent_source' and r['outcome']=='fail'
               for r in p.prerequisites['material'])
    p.prerequisites['material']=[r for r in p.prerequisites['material']
        if r['claim']!='two_rim.material.matches_parent_source']
    c=ideal_certificate(load_subject(p,'E0','1/4'))
    assert not (c['source_linked'] and c['seam_verdict']=='pass')


def test_A03_zero_axis_cannot_replace_overlap_witness(bundle,tmp_path):
    b=copy.deepcopy(bundle)
    for row in b['seams']['E9']['rows']:
        if row.get('method')=='interior_witness':
            row.update(method='separating_axis',outcome='pass',certificate={
                'method':'separating_axis','axis':['0','0'],'order':'P_below_Q',
                'axis_gap':'0','euclidean_gap_lower_bound':'0'})
    r=run_recheck(b,tmp_path)
    assert r['failures'] > 0


def test_A03_missing_all_pair_rows_is_not_a_completed_recheck(bundle,tmp_path):
    b=copy.deepcopy(bundle)
    b['seams']['E9']['rows']=[]
    r=run_recheck(b,tmp_path)
    assert r['failures'] > 0


def test_A03_truncated_vertex_lists_are_not_complete_box_coverage(bundle,tmp_path):
    b=copy.deepcopy(bundle)
    for f in b['seams']['E9']['boxes']:
        b['seams']['E9']['boxes'][f]=b['seams']['E9']['boxes'][f][:3]
    # Preserve only exact-neighbor rows so malformed interval polygons are not indexed
    # by an incidental witness failure. The box-coverage check must catch the truncation.
    b['seams']['E9']['rows']=[r for r in b['seams']['E9']['rows'] if r['method']=='shared_hinge_exact']
    r=run_recheck(b,tmp_path)
    assert r['failures'] > 0


def test_A03_outcome_must_match_verified_certificate_method(bundle,tmp_path):
    b=copy.deepcopy(bundle)
    for row in b['seams']['E9']['rows']:
        if row.get('method')=='interior_witness':
            row['outcome']='pass'
    r=run_recheck(b,tmp_path)
    assert r['failures'] > 0
