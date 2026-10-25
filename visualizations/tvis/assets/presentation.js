"use strict";
// DKPS-style one-beat-at-a-time presentation: each click plays one saved
// Manim section, then stays on its final frame until the next click.
// If no section movies exist, the same controls step through plan-derived SVGs.
const slides = Array.from(document.querySelectorAll('.slide'));
const stepMap = JSON.parse(document.getElementById('step-data').textContent);
const clipMap = JSON.parse(document.getElementById('video-data').textContent);
const notesMap = JSON.parse(document.getElementById('notes-data').textContent);
let slideIndex = 0;
let beatIndex = 0;
let playbackVersion = 0;

function stopVideo(slide) {
  if (!slide) return;
  const video = slide.querySelector('.scene-video');
  const image = slide.querySelector('.diagram-picture');
  if (!video) return;
  video.pause();
  video.onplaying = null;
  video.onerror = null;
  video.removeAttribute('src');
  video.load();
  video.hidden = true;
  if (image) image.hidden = false;
}

function renderBeat(slide, beat, animate, previousPoster = null) {
  const image = slide.querySelector('.diagram-picture');
  const video = slide.querySelector('.scene-video');
  const clip = clipMap[slide.dataset.scene]?.[beat.name];
  const willAnimate = animate && !!clip && slide.dataset.media === 'video' && !!video;
  if (image) {
    // Hold the *previous* completed state while loading the next clip.
    image.src = willAnimate && previousPoster ? previousPoster : beat.poster;
    image.alt = `${slide.querySelector('h2').textContent}: ${beat.name}`;
    image.hidden = false;
  }
  const badge = slide.querySelector('[data-role="beat-number"]');
  const caption = slide.querySelector('[data-role="beat-caption"]');
  const tier = slide.querySelector('[data-role="beat-tier"]');
  if (badge) badge.textContent = `${beatIndex + 1}/${stepMap[slide.dataset.slideId].length}`;
  if (caption) {
    caption.textContent = beat.flow ? `${beat.caption} · ${beat.flow}` : beat.caption;
    caption.title = caption.textContent;
  }
  if (tier) {
    tier.textContent = beat.evidence;
    tier.className = 'beat-tier' + (beat.tier ? ' tier-' + beat.tier : '');
  }
  for (const card of slide.querySelectorAll('[data-op-node]')) {
    card.classList.toggle('active-operation', card.dataset.opNode === beat.active);
  }
  // Section clips are only played on deliberate forward motion or replay;
  // stepping backward shows the exact completed SVG state immediately.
  if (!willAnimate) return;
  const version = playbackVersion;
  video.poster = beat.poster;
  video.src = clip;
  video.hidden = true; // Keep the SVG visible until the first frame is ready.
  video.onplaying = () => {
    if (version === playbackVersion) {
      video.hidden = false;
      if (image) image.hidden = true;
    }
  };
  video.onerror = () => {
    if (version === playbackVersion) {
      video.hidden = true;
      if (image) { image.src = beat.poster; image.hidden = false; }
    }
  };
  video.load();
  const promise = video.play();
  if (promise && typeof promise.catch === 'function') {
    promise.catch(() => {
      if (version === playbackVersion) {
        video.hidden = true;
        if (image) { image.src = beat.poster; image.hidden = false; }
      }
    });
  }
  // Deliberately no 'ended' handler: the final frame remains visible, and
  // the next section will not play until another click / keypress.
}

function show(index, step = 0, {animate = true, updateLocation = true} = {}) {
  const previous = slides[slideIndex];
  const wasSameSlide = index === slideIndex;
  const previousPoster = wasSameSlide
    ? stepMap[previous.dataset.slideId][beatIndex].poster : null;
  playbackVersion += 1;
  stopVideo(previous);
  slideIndex = Math.max(0, Math.min(index, slides.length - 1));
  const slide = slides[slideIndex];
  beatIndex = Math.max(0, Math.min(step, stepMap[slide.dataset.slideId].length - 1));
  slides.forEach((s, i) => { s.hidden = i !== slideIndex; });
  stopVideo(slide);
  const beats = stepMap[slide.dataset.slideId];
  renderBeat(slide, beats[beatIndex], animate, previousPoster);
  document.getElementById('counter').textContent =
    `SLIDE ${slideIndex + 1}/${slides.length} · BEAT ${beatIndex + 1}/${beats.length}`;
  const stepsDone = slides.slice(0, slideIndex)
    .reduce((n, s) => n + stepMap[s.dataset.slideId].length, 0) + beatIndex + 1;
  const total = slides.reduce((n, s) => n + stepMap[s.dataset.slideId].length, 0);
  document.getElementById('progress-bar').style.width = (stepsDone / total * 100) + '%';
  const note = notesMap[slide.dataset.slideId];
  document.getElementById('notes-title').textContent = slide.querySelector('h2').textContent;
  document.getElementById('notes-text').textContent = note.narration;
  document.getElementById('notes-sources').textContent =
    'Lean anchors: ' + note.proofs.join(', ') + '\nSources: ' + note.sources.join('; ');
  if (updateLocation) {
    const suffix = beatIndex ? '~' + encodeURIComponent(beats[beatIndex].name) : '';
    history.replaceState(null, '', '#slide-' + encodeURIComponent(slide.dataset.slideId) + suffix);
  }
}

function navigate(delta) {
  const current = slides[slideIndex];
  const number = stepMap[current.dataset.slideId].length;
  const next = beatIndex + delta;
  if (next >= 0 && next < number) {
    show(slideIndex, next, {animate: delta > 0});
  } else if (delta > 0 && slideIndex < slides.length - 1) {
    show(slideIndex + 1, 0);
  } else if (delta < 0 && slideIndex > 0) {
    const previous = stepMap[slides[slideIndex - 1].dataset.slideId];
    show(slideIndex - 1, previous.length - 1, {animate: false});
  }
}

function navigateSlide(delta) {
  const target = Math.max(0, Math.min(slideIndex + delta, slides.length - 1));
  if (target !== slideIndex) show(target, 0, {animate: delta > 0});
}

document.getElementById('prev').addEventListener('click', () => navigate(-1));
document.getElementById('next').addEventListener('click', () => navigate(+1));
document.getElementById('prev-slide').addEventListener('click', () => navigateSlide(-1));
document.getElementById('next-slide').addEventListener('click', () => navigateSlide(+1));
document.getElementById('notes-button').addEventListener('click', () => {
  const panel = document.getElementById('notes-panel');
  panel.hidden = !panel.hidden;
});
document.getElementById('fullscreen').addEventListener('click', () => {
  if (document.fullscreenElement) document.exitFullscreen();
  else document.documentElement.requestFullscreen?.();
});
// A click on the slide itself advances to the next beat without finding play.
document.getElementById('presentation').addEventListener('click', event => {
  if (!event.target.closest('.slide') ||
      event.target.closest('button,a,summary,input,textarea,select')) return;
  navigate(+1);
});
document.addEventListener('keydown', event => {
  if (event.altKey || event.ctrlKey || event.metaKey ||
      event.target.closest('input,textarea,select,[contenteditable="true"]')) return;
  // A clicked button retains focus: let arrows keep working there, but
  // preserve native Space-to-activate on focused buttons (avoid double steps).
  if (event.code === 'Space' && event.target.closest('button')) return;
  if (['ArrowRight', 'PageDown'].includes(event.key) || event.code === 'Space') {
    event.preventDefault();
    if (event.shiftKey) navigateSlide(+1); else navigate(+1);
  } else if (['ArrowLeft', 'PageUp'].includes(event.key)) {
    event.preventDefault();
    if (event.shiftKey) navigateSlide(-1); else navigate(-1);
  } else if (event.key === 'Home') {
    event.preventDefault(); show(0, 0, {animate: false});
  } else if (event.key === 'End') {
    event.preventDefault();
    const last = slides.length - 1;
    show(last, stepMap[slides[last].dataset.slideId].length - 1, {animate: false});
  } else if (event.key.toLowerCase() === 'r') {
    event.preventDefault(); show(slideIndex, beatIndex);
  } else if (event.key.toLowerCase() === 'n') {
    document.getElementById('notes-button').click();
  } else if (event.key.toLowerCase() === 'f') {
    document.getElementById('fullscreen').click();
  }
});
function hashTarget() {
  if (!location.hash.startsWith('#slide-')) return null;
  const [slug, beatName] = location.hash.slice(7).split('~', 2);
  const name = decodeURIComponent(slug);
  const index = slides.findIndex(s => s.dataset.slideId === name);
  if (index < 0) return null;
  const steps = stepMap[slides[index].dataset.slideId];
  const step = beatName ? steps.findIndex(s => s.name === decodeURIComponent(beatName)) : 0;
  return [index, Math.max(0, step)];
}
window.addEventListener('hashchange', () => {
  const location = hashTarget();
  if (location) show(location[0], location[1], {animate: false, updateLocation: false});
});
const initial = hashTarget();
if (initial) show(initial[0], initial[1], {animate: false, updateLocation: false});
else show(0, 0, {animate: true, updateLocation: false});
