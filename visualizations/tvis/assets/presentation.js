"use strict";
// Offline, keyboard-driven presentation. The HTML may contain base64 videos,
// but clip sources are attached only when needed to avoid eager media decoding.
const slides = Array.from(document.querySelectorAll('.slide'));
const videoMap = JSON.parse(document.getElementById('video-data').textContent);
const notesMap = JSON.parse(document.getElementById('notes-data').textContent);
let slideIndex = 0;
function activate(index, updateLocation = true) {
  slideIndex = Math.max(0,Math.min(index,slides.length-1));
  slides.forEach((slide,i) => {
    const visible = i===slideIndex;
    slide.hidden = !visible;
    for (const clip of slide.querySelectorAll('video')) {
      if (!visible) { clip.pause(); clip.removeAttribute('src'); clip.load(); }
      else if (videoMap[clip.dataset.scene] && clip.getAttribute('src')!==videoMap[clip.dataset.scene]) {
        clip.src=videoMap[clip.dataset.scene]; clip.load();
      }
    }
  });
  const s=slides[slideIndex];
  document.getElementById('counter').textContent=(slideIndex+1)+' / '+slides.length;
  document.getElementById('progress-bar').style.width=((slideIndex+1)/slides.length*100)+'%';
  const note=notesMap[s.dataset.slideId];
  document.getElementById('notes-title').textContent=s.querySelector('h2').textContent;
  document.getElementById('notes-text').textContent=note.narration;
  document.getElementById('notes-sources').textContent='Lean anchors: '+note.proofs.join(', ')+'\nSources: '+note.sources.join('; ');
  if(updateLocation) history.replaceState(null,'','#slide-'+s.dataset.slideId);
}
function navigate(delta){activate(slideIndex+delta);}
document.getElementById('prev').addEventListener('click',()=>navigate(-1));
document.getElementById('next').addEventListener('click',()=>navigate(+1));
document.getElementById('notes-button').addEventListener('click',()=>{
  const panel=document.getElementById('notes-panel'); panel.hidden=!panel.hidden;
});
document.getElementById('fullscreen').addEventListener('click',()=>{
  if(document.fullscreenElement){document.exitFullscreen();}
  else{document.documentElement.requestFullscreen?.();}
});
document.addEventListener('keydown',event=>{
  if(event.altKey||event.ctrlKey||event.metaKey||event.target.closest('button,input,textarea,select'))return;
  if(['ArrowRight','PageDown'].includes(event.key)){event.preventDefault();navigate(1);}
  else if(['ArrowLeft','PageUp'].includes(event.key)){event.preventDefault();navigate(-1);}
  else if(event.key==='Home'){event.preventDefault();activate(0);}
  else if(event.key==='End'){event.preventDefault();activate(slides.length-1);}
  else if(event.key.toLowerCase()==='n'){document.getElementById('notes-button').click();}
  else if(event.key.toLowerCase()==='f'){document.getElementById('fullscreen').click();}
  else if(event.code==='Space'){
    const video=slides[slideIndex].querySelector('video');
    if(video){event.preventDefault();if(video.paused){video.play().catch(()=>{});}else{video.pause();}}
  }
});
window.addEventListener('hashchange',()=>{
  const i=slides.findIndex(s=>'#'+s.id===location.hash);
  if(i>=0&&i!==slideIndex)activate(i,false);
});
const initial=slides.findIndex(s=>'#'+s.id===location.hash);
activate(initial>=0?initial:0,false);
