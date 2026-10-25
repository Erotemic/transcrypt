"""Local interactive storyboard: one HTML file and no running server.

Shows editable scene beats, who knows what, packets and source references.
The diagrams are generated from the same plans as the Manim animations.
"""
from __future__ import annotations

import base64
import json
from pathlib import Path
from typing import Mapping

from tvis.catalog import load_catalog
from tvis.svg_preview import render_svg


def build_gallery(target: Path, *, theme: str = 'dark',
                  videos: Mapping[str, str] | None = None) -> Path:
    deck, scenes = load_catalog()
    videos = videos or {}
    payload = []
    for scene in scenes:
        diagram = scene.diagram()
        beats = []
        for i, beat in enumerate(diagram.beats):
            drawing = render_svg(diagram, beat=i, theme=theme).encode('utf-8')
            beats.append({
                'id': beat.key,
                'caption': beat.caption,
                'status': beat.status,
                'packet': beat.packet_label,
                'packetKind': beat.packet_kind if beat.packet else '',
                'processing': ({'node': beat.processing.node,
                                'input': beat.processing.before,
                                'inputKind': beat.processing.before_kind,
                                'output': beat.processing.after,
                                'outputKind': beat.processing.after_kind}
                               if beat.processing else None),
                'knowledge': [
                    {'party': diagram.node_map()[k.owner].title, 'items': list(k.items)}
                    for k in beat.knowledge
                ],
                'image': 'data:image/svg+xml;base64,' + base64.b64encode(drawing).decode('ascii'),
            })
        payload.append({
            'id': scene.id, 'title': diagram.title,
            'video': videos.get(scene.id, ''),
            'status': scene.status, 'claim': scene.claim,
            'operations': [
                {'node': node.key, 'title': node.title, 'tier': node.evidence.level,
                 'basis': node.evidence.basis, 'note': node.evidence.note}
                for node in diagram.nodes if node.evidence is not None
            ],
            'narration': scene.narration,
            'sources': list(scene.sources),
            'optionalSources': list(scene.optional_sources),
            'proofAnchors': list(scene.proof_anchors),
            'editPlan': scene.plan.replace('.', '/') + '.py',
            'editManim': scene.file,
            'beats': beats,
        })
    encoded = json.dumps({'title': deck['title'], 'scenes': payload}, ensure_ascii=True)
    # A data script does not execute source prose; protect the HTML end tag in
    # case a scene description contains it.
    encoded = encoded.replace('<', '\\u003c')
    template = '''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Transcrypt v3 | bytes and proof boundaries</title>
<style>
:root{color-scheme:dark;font-family:system-ui,-apple-system,"DejaVu Sans",sans-serif;background:#0b1422;color:#eff6fb}
*{box-sizing:border-box} body{max-width:1500px;margin:0 auto;padding:18px 22px 40px}
h1{font-size:26px;font-weight:650;margin:6px 0 6px} p{margin:4px 0 12px;color:#b1c0cd;font-size:15px}
.controls{display:flex;gap:12px;align-items:center;flex-wrap:wrap;margin:16px 0 14px}
select,button,input{accent-color:#64c9f2;color:#eff6fb;background:#172c3f;border:1px solid #3c6479;border-radius:9px;font-size:16px;padding:8px 12px}
button{cursor:pointer}button:hover{background:#28516c}input[type=range]{padding:0;width:250px;max-width:35vw}
#image{display:block;width:100%;height:auto;box-shadow:0 7px 35px #0009;border-radius:7px;background:#0b1422}
#video{display:none;width:100%;max-height:76vh;aspect-ratio:16/9;background:#0b1422;border-radius:8px}
#mode-switch{display:flex;gap:8px;margin:8px 0}
#mode-switch[hidden],#video[hidden]{display:none!important}
#video[src]{display:block}
#image[hidden]{display:none}
.foot{display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-top:16px}
.panel{background:#152638;border:1px solid #28465b;border-radius:12px;padding:16px}
.panel strong{color:#6fe0b7}.panel span{color:#d2e3f0}.panel p{line-height:1.5}.operation-items{display:grid;grid-template-columns:repeat(auto-fit,minmax(245px,1fr));gap:8px;margin:9px 0 0}.operation{border-left:4px solid #b1c0cd;padding:9px 12px;background:#132132;border-radius:7px}.operation strong{display:block;color:#eff6fb;font-size:14px}.operation small{display:block;font-size:12px;color:#b1c0cd}.operation .tier{font-size:12px;letter-spacing:.03em;color:#f4c474}.operation[data-tier=source-proof],.operation[data-tier=conditional-proof]{border-left-color:#78dba9}.operation[data-tier=model-proof]{border-left-color:#af9ef7}.operation[data-tier=tested]{border-left-color:#6fe0b7}.operation[data-tier=trusted-crypto],.operation[data-tier=trusted-platform]{border-left-color:#f4c474}.operation[data-tier=planned]{border-left-color:#ff947d}.operation.active{outline:2px solid #eff6fb}.inventory{grid-column:1 / -1}.inventory-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;margin-top:8px}.inventory-grid h3{font-size:14px;margin:4px 0;color:#74ceec}.inventory-grid ul{margin-top:4px}@media(max-width:850px){.inventory-grid{grid-template-columns:1fr}}
code{color:#f4c474;overflow-wrap:anywhere} ul{padding-left:21px;margin:9px 0;color:#b1c0cd}
@media(max-width:780px){.foot{grid-template-columns:1fr}.controls{gap:7px}.panel{padding:12px}}
</style>
</head>
<body>
<h1>Transcrypt v3: plaintext, ciphertext, and proof</h1>
<p>Select a scene and a step. The diagrams come from editable Python plans and are shared with the Manim animation.</p>
<div class="controls">
<label for="scene">Scene</label><select id="scene"></select>
<button id="previous" type="button" aria-label="Previous beat">Prev</button>
<label for="beat">Beat</label><input id="beat" type="range" min="0" max="0" value="0">
<button id="next" type="button" aria-label="Next beat">Next</button>
<strong id="number" aria-live="polite"></strong>
</div>
<div id="mode-switch" hidden>
  <button type="button" id="motion">Play animation</button>
  <button type="button" id="still">Step through diagrams</button>
</div>
<video id="video" controls preload="metadata" playsinline hidden aria-label="Rendered Manim scene"></video>
<img id="image" alt="Editable protocol diagram">

<div class="foot">
  <div class="panel"><strong id="status"></strong><p id="claim"></p><strong>Explanation</strong><p id="narration"></p></div>
  <div class="panel"><strong>Edit</strong><p id="editpaths"></p><strong>Source files</strong><ul id="sources"></ul></div>
  <div class="panel inventory"><strong>Operation-by-operation evidence</strong><p>The badge applies to this operation only. The source or assumption is shown beneath it.</p><div id="operations" class="operation-items"></div></div>
  <div class="panel inventory"><strong>What each component holds at this step</strong><div id="inventory" class="inventory-grid"></div></div>
</div>
<script type="application/json" id="story-data">__PAYLOAD__</script>
<script>
const data = JSON.parse(document.getElementById('story-data').textContent);
const scenes = data.scenes;
const sceneSelect = document.getElementById('scene');
const beatRange = document.getElementById('beat');
const player = document.getElementById('video');
const image = document.getElementById('image');
const modeSwitch = document.getElementById('mode-switch');
let showMotion = true;
function setMode(){
  const s = scenes.find(x=>x.id===sceneSelect.value)||scenes[0];
  const isVideo = Boolean(s.video) && showMotion;
  player.hidden = !isVideo;
  image.hidden = isVideo;
  document.getElementById('beat').disabled = isVideo;
  document.getElementById('previous').disabled = isVideo;
  document.getElementById('next').disabled = isVideo;
}
document.getElementById('motion').addEventListener('click',()=>{showMotion=true;setMode();});
document.getElementById('still').addEventListener('click',()=>{showMotion=false;player.pause();setMode();});
for(const s of scenes){const o=document.createElement('option');o.value=s.id;o.textContent=s.id+' — '+s.title;sceneSelect.append(o);}
function show(){
  const s = scenes.find(x=>x.id===sceneSelect.value)||scenes[0];
  const j = Math.min(Math.max(Number(beatRange.value),0),s.beats.length-1);
  const b=s.beats[j];
  document.getElementById('number').textContent=b.id+'  ('+(j+1)+'/'+s.beats.length+')';
  const operations=document.getElementById('operations');operations.replaceChildren();
  const opLabels={'source-proof':'LEAN: SOURCE PROOF','conditional-proof':'LEAN: IF REALIZES',
    'model-proof':'LEAN: MODEL ONLY','tested':'TESTED: NO PROOF','trusted-crypto':'TRUSTED: CRYPTO',
    'trusted-platform':'TRUSTED: GIT / OS','implemented':'IN CODE: NO PROOF','planned':'DESIGN GOAL'};
  for(const op of s.operations){
    const el=document.createElement('div');el.className='operation'+(b.processing?.node===op.node?' active':'');
    el.dataset.tier=op.tier;
    const title=document.createElement('strong');title.textContent=op.title;
    const tier=document.createElement('span');tier.className='tier';tier.textContent=opLabels[op.tier];
    const detail=document.createElement('small');detail.textContent=op.basis+' — '+op.note;
    el.append(title,tier,detail);operations.append(el);
  }
  image.src=b.image;
  document.getElementById('image').alt=s.title+' — '+b.caption;
  document.getElementById('status').textContent=b.status.toUpperCase();
  document.getElementById('claim').textContent=s.claim;
  document.getElementById('narration').textContent=s.narration+'\\nCurrent beat: '+b.caption+
    (b.processing?'\\nProcessing '+b.processing.node+': '+b.processing.inputKind+' ('+b.processing.input+
    ') → '+b.processing.outputKind+' ('+b.processing.output+')':'');
  const ul=document.getElementById('sources');ul.replaceChildren();
  for(const f of s.sources.concat(s.optionalSources.map(x=>x+' (optional source)')).concat(s.proofAnchors.map(x=>'Lean theorem: '+x))){
    const li=document.createElement('li');const code=document.createElement('code');code.textContent=f;li.append(code);ul.append(li);
  }
  document.getElementById('editpaths').textContent=s.editPlan+' | '+s.editManim;
  const inventory=document.getElementById('inventory');inventory.replaceChildren();
  if(!b.knowledge.length){const p=document.createElement('p');p.textContent='See the diagram for this step.';inventory.append(p);}
  for(const owner of b.knowledge){
    const section=document.createElement('section');const heading=document.createElement('h3');heading.textContent=owner.party;
    const list=document.createElement('ul');
    for(const value of owner.items){const item=document.createElement('li');item.textContent=value;list.append(item);}
    section.append(heading,list);inventory.append(section);
  }
}
function selectedChanged(){
  const s=scenes.find(x=>x.id===sceneSelect.value);
  beatRange.max=s.beats.length-1;beatRange.value=0;
  player.pause();
  player.removeAttribute('src');
  player.load();
  if(s.video){player.src=s.video;player.load();}
  modeSwitch.hidden=!s.video;
  setMode();show();
}
sceneSelect.addEventListener('change',selectedChanged);
beatRange.addEventListener('input',show);
document.getElementById('previous').addEventListener('click',()=>{beatRange.value=Math.max(0,Number(beatRange.value)-1);show();});
document.getElementById('next').addEventListener('click',()=>{beatRange.value=Math.min(Number(beatRange.max),Number(beatRange.value)+1);show();});
document.addEventListener('keydown',event=>{if(event.target.matches('input,select,textarea'))return;if(event.key==='ArrowRight'){document.getElementById('next').click();}if(event.key==='ArrowLeft'){document.getElementById('previous').click();}});
sceneSelect.value=scenes[0].id;selectedChanged();
</script>
</body></html>
'''
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(template.replace('__PAYLOAD__', encoded), encoding='utf-8')
    return target
