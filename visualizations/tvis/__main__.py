"""Fast local Manim authoring: ``python -m tvis --help``.

No Manim dependency is imported until an individual scene is rendered.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import importlib.util
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import time

from tvis.catalog import VIS_ROOT, get_scene, load_catalog, validate_catalog
from tvis.svg_preview import write_preview
from tvis.gallery import build_gallery
from tvis.slide_deck import load_slides


BUILD = VIS_ROOT / '.build'


def render_command(scene_id: str, *, quality: str = 'l', still: bool = False,
                   theme: str = 'dark', speed: float = 1.0,
                   animation: str | None = None, open_result: bool = False,
                   no_cache: bool = False, save_sections: bool = False) -> tuple[list[str], dict[str, str]]:
    """Return command data; no shell interpolation and no ambient Manim import."""
    scene = get_scene(scene_id)
    if quality not in {'l', 'm', 'h', 'p'}:
        raise ValueError('quality must be l/m/h/p')
    if theme not in {'dark', 'light'}:
        raise ValueError('theme must be dark/light')
    if not 0.1 <= speed <= 10:
        raise ValueError('speed must be in [0.1, 10]')
    if animation is not None:
        parts = animation.split(',')
        if not 1 <= len(parts) <= 2 or any(not p.isdecimal() for p in parts):
            raise ValueError('--animation must be N or N,M (zero-based Manim play indices)')
        if len(parts) == 2 and int(parts[1]) < int(parts[0]):
            raise ValueError('--animation end cannot precede start')
    cmd = [sys.executable, '-m', 'manim', '-q'+quality,
           '--media_dir', str(BUILD / 'media'),
           '-o', scene_id, scene.file, scene.class_name]
    if save_sections:
        if still or animation is not None:
            raise ValueError('--save_sections requires a complete video render')
        cmd.insert(3, '--save_sections')
    if no_cache:
        cmd.insert(3, '--disable_caching')
    if still:
        cmd.insert(3, '-s')
    if open_result:
        cmd.insert(3, '-p')
    if animation is not None:
        cmd[3:3] = ['-n', animation]
    env = os.environ.copy()
    env['TVIS_THEME'] = theme
    env['TVIS_SPEED'] = str(speed)
    return cmd, env


def _render(args, *, scene_id: str | None = None, save_sections: bool = False) -> int:
    scene_id = scene_id or args.scene
    cmd, env = render_command(scene_id, quality=args.quality, still=args.still,
                              theme=args.theme, speed=args.speed,
                              animation=args.animation, open_result=args.open_result,
                              no_cache=getattr(args, 'no_cache', False), save_sections=save_sections)
    print('$ '+shlex.join(cmd), flush=True)
    if args.dry_run:
        return 0
    if importlib.util.find_spec('manim') is None:
        print('Manim is not installed in this Python environment. From visualizations/: '
              'uv sync --extra manim --extra test', file=sys.stderr)
        return 2
    return subprocess.run(cmd, cwd=VIS_ROOT, env=env, check=False).returncode


def _render_and_publish(args) -> int:
    """Render one complete scene, or reuse its current clip, for HTML playback."""
    if args.still or args.animation is not None:
        raise ValueError('--publish requires a full video; use render without --publish for still/partial clips')
    from tvis.presentation import publish_scene, find_manim_video

    def render_one(scene_id: str) -> Path:
        result = _render(args, scene_id=scene_id, save_sections=True)
        if result:
            raise RuntimeError(f'failed to render {scene_id} (exit code {result})')
        return find_manim_video(scene_id, args.quality)

    if args.dry_run:
        return _render(args, save_sections=True)
    target, changed = publish_scene(
        args.scene, quality=args.quality, theme=args.theme, speed=args.speed,
        force=args.force or args.open_result, render_scene=render_one)
    print(('Updated' if changed else 'Reused') + f' video: {target}', flush=True)
    return 0


def _all(args) -> int:
    """Refresh only changed Manim clips and the browser presentation."""
    from tvis.presentation import build_presentation, find_manim_video

    if args.still or args.animation is not None:
        raise ValueError('all builds videos; --still/--animation apply to render only')
    if args.dry_run:
        _, scenes = load_catalog()
        for scene in scenes:
            _render(args, scene_id=scene.id, save_sections=True)
        return 0

    def render_scene(scene_id: str) -> Path:
        returncode = _render(args, scene_id=scene_id, save_sections=True)
        if returncode:
            raise RuntimeError(f'failed to render {scene_id} (exit code {returncode})')
        return find_manim_video(scene_id, args.quality)

    output, changed = build_presentation(
        quality=args.quality, theme=args.theme, speed=args.speed,
        force=getattr(args, 'force', False), render_scene=render_scene,
        formats=getattr(args, 'format', 'both'),
        embed_videos=getattr(args, 'embed_videos', False))
    print(f'Updated {len(changed)} scene videos; {len(load_catalog()[1])-len(changed)} reused.', flush=True)
    print(f'Presentation: {output}', flush=True)
    from tvis.presentation import PRESENTATION
    if (PRESENTATION/'presentation.pdf').is_file() and args.format in {'pdf','both'}:
        print(f"PDF presentation: {PRESENTATION / 'presentation.pdf'}", flush=True)
    if args.open_result:
        import webbrowser
        webbrowser.open(output.as_uri())
    return 0


def _preview(scene_id: str, beat: str = 'last', theme: str = 'dark') -> Path:
    plan = get_scene(scene_id).diagram()
    selected: str | int = int(beat) if beat.isdecimal() else beat
    target = BUILD / 'previews' / f'{scene_id}-{beat}-{theme}.svg'
    write_preview(plan, target, beat=selected, theme=theme)
    print(target, flush=True)
    return target


def _snapshot() -> tuple[tuple[str, int, int], ...]:
    """Watch only authored source and storyboard, never generated Manim media."""
    files = [* (VIS_ROOT / 'tvis').rglob('*.py'),
             * (VIS_ROOT / 'storyboards').glob('*.toml'),
             * (VIS_ROOT / 'tvis/assets').glob('presentation.*'),
             * (VIS_ROOT / 'tvis/assets/icons').glob('*.svg')]
    return tuple(sorted((str(path), path.stat().st_mtime_ns, path.stat().st_size)
                        for path in files if path.is_file()))


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description='Transcrypt v3 data flow, proof boundaries and presentations')
    commands = parser.add_subparsers(dest='action', required=True)
    commands.add_parser('list', help='print every scene and its editable plan source')
    story = commands.add_parser('storyboard', help='show claims, speaker notes and source references')
    story.add_argument('--json', action='store_true', help='machine-readable metadata')
    commands.add_parser('check', help='validate scene plans, identifiers, and referenced source paths (no Manim)')
    gallery = commands.add_parser('gallery', help='build a single-file interactive storyboard, no Manim')
    gallery.add_argument('--theme', choices=['dark','light'], default='dark')
    presentation=commands.add_parser('present',help='export full HTML/PDF slides, reusing videos when available; no Manim required')
    presentation.add_argument('--theme',choices=['dark','light'],default='dark')
    presentation.add_argument('--format',choices=['html','pdf','both'],default='both')
    presentation.add_argument('--embed-videos',action='store_true',help='also output standalone embedded.html with base64 MP4s')
    subset = presentation.add_mutually_exclusive_group()
    subset.add_argument('--scene', help='only slides for this scene ID')
    subset.add_argument('--scenes', nargs='+', metavar='ID', help='only slides for these scene IDs')
    subset.add_argument('--slide', help='only the named slide ID')
    subset.add_argument('--slides', nargs='+', metavar='ID', help='only these slide IDs')
    preview = commands.add_parser('preview', help='instant SVG preview of any beat (no Manim)')
    preview.add_argument('scene', help='scene ID or all')
    preview.add_argument('--beat', default='last', help='zero-based number, named beat, or last')
    preview.add_argument('--theme', choices=['dark','light'], default='dark')
    for name in ('render', 'deck', 'watch', 'all'):
        cmd = commands.add_parser(name, help={
            'render':'render one Manim scene',
            'deck':'legacy: render each scene separately (no HTML)',
            'watch':'refresh previews, a scene, or all changed clips after edits',
            'all':'render changed Manim clips and build an HTML presentation',
        }[name])
        if name not in ('deck', 'all'):
            cmd.add_argument('scene', help='scene ID or all for watch')
        cmd.add_argument('--quality', choices=['l','m','h','p'], default='l')
        cmd.add_argument('--theme', choices=['dark','light'], default='dark')
        cmd.add_argument('--speed', type=float, default=1.0, help='animation playback speed')
        cmd.add_argument('--still', action='store_true', help='render last frame, no video')
        cmd.add_argument('--animation', help='Manim play indices: N or N,M')
        cmd.add_argument('--open', dest='open_result', action='store_true', help='Manim -p (open local viewer)')
        cmd.add_argument('--dry-run', action='store_true', help='print command without rendering')
        cmd.add_argument('--no-cache', action='store_true', help='disable Manim partial-movie caching')
        if name == 'render':
            cmd.add_argument('--publish', action='store_true',
                             help='stage one full scene in the HTML deck and reuse if unchanged')
        if name in ('render', 'all'):
            cmd.add_argument('--force', action='store_true', help='render even if the staged clip is current')
        if name == 'all':
            cmd.add_argument('--format', choices=['html','pdf','both'], default='both', help='slide presentation export formats')
            cmd.add_argument('--embed-videos', action='store_true', help='also generate fully self-contained embedded.html')
        if name == 'watch':
            cmd.add_argument('--mode', choices=['preview','render','gallery','all'], default='preview')
            cmd.add_argument('--beat', default='last')
            cmd.add_argument('--interval', type=float, default=0.7)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        if args.action == 'list':
            _, scenes = load_catalog()
            for scene in scenes:
                print(f'{scene.id:<12} {scene.status:<26} {scene.file:<37} {scene.plan}')
            return 0
        if args.action == 'storyboard':
            deck, scenes = load_catalog()
            if args.json:
                print(json.dumps({'deck': deck, 'scenes':[asdict(s) for s in scenes]}, indent=2))
            else:
                print(f'{deck["title"]}  [{deck["name"]}]\n')
                for number, scene in enumerate(scenes, 1):
                    print(f'{number}. {scene.id} [{scene.status}]\n'
                          f'   FLOW: {scene.claim}\n'
                          f'   NOTES: {scene.narration}\n'
                          f'   SOURCES: {", ".join(scene.sources)}')
                    if scene.proof_anchors:
                        print(f'   LEAN REFS: {", ".join(scene.proof_anchors)}')
                    print()
            return 0
        if args.action == 'check':
            scenes = validate_catalog()
            slides = load_slides()
            print(f'{len(scenes)} scene plans and {len(slides.slides)} presentation slides valid')
            return 0
        if args.action == 'preview':
            _, scenes = load_catalog()
            if args.scene == 'all':
                for scene in scenes:
                    _preview(scene.id, beat=args.beat, theme=args.theme)
            else:
                _preview(args.scene, beat=args.beat, theme=args.theme)
            return 0
        if args.action == 'gallery':
            print(build_gallery(BUILD / 'storyboard.html', theme=args.theme))
            return 0
        if args.action == 'present':
            from tvis.presentation import export_presentation
            scene_ids = (args.scene,) if args.scene else tuple(args.scenes or ())
            slide_ids = (args.slide,) if args.slide else tuple(args.slides or ())
            paths=export_presentation(theme=args.theme,formats=args.format,
                                      embed_videos=args.embed_videos,
                                      scene_ids=scene_ids, slide_ids=slide_ids)
            for kind,path in paths.items():
                print(f'{kind}: {path}')
            return 0
        if args.action == 'render':
            return _render_and_publish(args) if args.publish else _render(args)
        if args.action == 'all':
            return _all(args)
        if args.action == 'deck':
            _, scenes = load_catalog()
            for scene in scenes:
                outcome = _render(args, scene_id=scene.id)
                if outcome:
                    return outcome
            return 0
        if args.action == 'watch':
            if args.interval < 0.2:
                raise ValueError('watch interval must be >= 0.2 seconds')
            if args.scene != 'all':
                get_scene(args.scene)  # refuse typo before entering the long-running loop
            elif args.mode == 'render':
                raise ValueError('watch all in Manim mode uses --mode all, not --mode render')
            print(f'Watching {args.scene}; Ctrl-C to stop.', flush=True)
            previous = None
            try:
                while True:
                    current = _snapshot()
                    if current != previous:
                        previous = current
                        if args.mode in ('preview', 'gallery'):
                            # Separate process ensures edited Python plans are reimported.
                            command = [sys.executable, '-m', 'tvis', args.mode]
                            if args.mode == 'preview':
                                command += [args.scene, '--beat', args.beat]
                            command += ['--theme', args.theme]
                            subprocess.run(command, cwd=VIS_ROOT, check=False)
                        elif args.mode == 'all':
                            command=[sys.executable, '-m', 'tvis', 'all',
                                     '--quality', args.quality, '--theme', args.theme,
                                     '--speed', str(args.speed)]
                            subprocess.run(command, cwd=VIS_ROOT, check=False)
                        else:
                            _render(args)
                    time.sleep(args.interval)
            except KeyboardInterrupt:
                print('\nStopped watching.')
                return 0
        return 2
    except (ValueError, FileNotFoundError, ImportError, RuntimeError) as error:
        print(f'tvis: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
