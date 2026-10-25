"""Static 16:9 PDF companion for the heterogeneous HTML/Manim slide deck.

PDF media playback is not portable. Video slides use an actual plan-derived
key beat as their static poster and link to the corresponding HTML slide. The
PDF never embeds a fake screenshot or labels an external premise as proved.
"""
from __future__ import annotations

from functools import lru_cache
import io
from pathlib import Path

from tvis.diagram import EVIDENCE_LABELS, EVIDENCE_ROLES
from tvis.palette import palette
from tvis.slide_deck import Slide, SlideDeck
from tvis.svg_preview import render_svg

PAGE_W, PAGE_H = 960, 540  # 16:9 points


def _fonts():
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    regular = Path('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf')
    bold = Path('/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf')
    if regular.is_file() and bold.is_file():
        if 'TVis-Regular' not in pdfmetrics.getRegisteredFontNames():
            pdfmetrics.registerFont(TTFont('TVis-Regular', str(regular)))
            pdfmetrics.registerFont(TTFont('TVis-Bold', str(bold)))
        return ('TVis-Regular', 'TVis-Bold')
    return ('Helvetica', 'Helvetica-Bold')


def _color(hexcolor):
    from reportlab.lib.colors import HexColor
    return HexColor(hexcolor)


def _fitline(text: str, font: str, size: float, width: float) -> str:
    from reportlab.pdfbase.pdfmetrics import stringWidth
    if stringWidth(text, font, size) <= width:
        return text
    while text and stringWidth(text + '…', font, size) > width:
        text = text[:-1]
    return text + '…'


def _lines(text: str, font: str, size: float, width: float) -> list[str]:
    from reportlab.pdfbase.pdfmetrics import stringWidth
    result = []
    row = ''
    for word in text.split():
        candidate = (row + ' ' + word).strip()
        if row and stringWidth(candidate, font, size) > width:
            result.append(row)
            row = word
        else:
            row = candidate
    if row:
        result.append(row)
    return result


def _paragraph(c, text, x, top, width, *, font, size, ink, leading=None,
               max_lines=99):
    leading = leading or size * 1.35
    c.setFont(font, size)
    c.setFillColor(_color(ink))
    for line in _lines(text, font, size, width)[:max_lines]:
        c.drawString(x, top, _fitline(line, font, size, width))
        top -= leading
    return top


def _pill(c, text: str, x: float, y: float, *, font: str, color: str,
          bg: str, max_w: float, size: int = 10):
    from reportlab.pdfbase.pdfmetrics import stringWidth
    label = _fitline(text, font, size, max_w - 18)
    width = min(max_w, stringWidth(label, font, size) + 20)
    c.setFillColor(_color(bg)); c.roundRect(x, y, width, 23, 7, stroke=0, fill=1)
    c.setFillColor(_color(color)); c.setFont(font, size); c.drawString(x + 10, y + 7, label)
    return width


@lru_cache(maxsize=32)
def _poster_png(scene_id: str, beat: str, theme: str) -> bytes:
    try:
        import cairosvg
    except ImportError as ex:
        raise RuntimeError('PDF export requires optional presentation dependencies: '
                           'uv sync --extra presentation') from ex
    from tvis.catalog import get_scene
    diagram = get_scene(scene_id).diagram()
    return cairosvg.svg2png(bytestring=render_svg(diagram, beat=beat, theme=theme).encode('utf-8'),
                           output_width=1440, output_height=810)


def _visual(c, slide: Slide, rect, theme: str, colors: dict):
    from reportlab.lib.utils import ImageReader
    x, y, w, h = rect
    # Container is physically separate from the diagram's own SVG background.
    c.setStrokeColor(_color(colors['neutral'])); c.setLineWidth(.4)
    c.roundRect(x, y, w, h, 7, stroke=1, fill=0)
    aspect = 16/9
    rw = min(w, h * aspect)
    rh = rw / aspect
    dx, dy = x + (w-rw)/2, y+(h-rh)/2
    png = _poster_png(slide.scene.id, slide.beat, theme)
    c.drawImage(ImageReader(io.BytesIO(png)), dx, dy, width=rw, height=rh)


def _operations(c, slide: Slide, box, colors: dict, fonts, *, columns: int = 2,
                max_items: int = 6, item_height: float = 68.0):
    x, top, width = box
    regular, bold = fonts
    nodes = [node for node in slide.diagram.nodes if node.evidence]
    gap = 11
    w = (width - gap * (columns - 1)) / columns
    for i, node in enumerate(nodes[:max_items]):
        col, row = i % columns, i // columns
        left = x + col * (w + gap)
        y = top - row * (item_height + 8) - item_height
        tier_color = colors[EVIDENCE_ROLES[node.evidence.level]]
        c.setFillColor(_color(colors['surface'])); c.roundRect(left, y, w, item_height, 7, stroke=0, fill=1)
        c.setFillColor(_color(tier_color)); c.roundRect(left, y, 5, item_height, 2, stroke=0, fill=1)
        c.setFillColor(_color(colors['foreground'])); c.setFont(bold, 11)
        c.drawString(left + 15, y + item_height - 17,
                     _fitline(node.title, bold, 11, w-24))
        c.setFillColor(_color(tier_color)); c.setFont(bold, 9)
        c.drawString(left+15, y+item_height-32,
                     _fitline(EVIDENCE_LABELS[node.evidence.level], bold, 9, w-24))
        c.setFillColor(_color(colors['muted'])); c.setFont(regular, 9)
        desc = node.evidence.basis + ' · ' + node.evidence.note
        for j,line in enumerate(_lines(desc, regular, 9, w-24)[:2]):
            c.drawString(left+15, y+item_height-45-j*11, _fitline(line,regular,9,w-24))
    return top - ((min(len(nodes),max_items)+columns-1)//columns)*(item_height+8)


def _title(c, slide: Slide, colors: dict, fonts, *, x=40, top=500, maxwidth=875):
    regular, bold = fonts
    c.setFillColor(_color(colors['guest'])); c.setFont(bold, 10)
    c.drawString(x, top, _fitline(slide.kicker, bold,10,maxwidth))
    top -= 33
    title_size=30 if len(slide.title) < 57 else 27
    top=_paragraph(c, slide.title, x, top, maxwidth, font=bold, size=title_size,
                   ink=colors['foreground'], leading=34, max_lines=2) - 3
    top=_paragraph(c,slide.subtitle,x,top,maxwidth,font=regular,size=12.4,
                   ink=colors['muted'],leading=17,max_lines=2)
    return top


def _bullet_list(c, points, x, top, width, colors, fonts, *, size=12, gap=9,
                 limit=5, min_bottom=70):
    regular, bold = fonts
    for point in points[:limit]:
        if top < min_bottom:
            break
        c.setFillColor(_color(colors['guest'])); c.circle(x+3,top+3,2.6,stroke=0,fill=1)
        top = _paragraph(c,point,x+13,top,width-15,font=regular,size=size,
                         ink=colors['foreground'],leading=size*1.39,max_lines=3) - gap
    return top


def _page(c, slide: Slide, number: int, total: int, theme: str, video_present: bool,
          colors: dict, fonts, html_name: str):
    regular, bold = fonts
    c.setFillColor(_color(colors['background'])); c.rect(0,0,PAGE_W,PAGE_H,fill=1,stroke=0)
    c.setStrokeColor(_color(colors['surface_soft'])); c.setLineWidth(1.0)
    c.line(38,39,PAGE_W-38,39)
    c.setFont(regular,9.2); c.setFillColor(_color(colors['muted']))
    c.drawString(40,22,f'Scene: {slide.scene.id}  /  Evidence applies per operation')
    c.drawRightString(PAGE_W-40,22,f'{number:02d} / {total:02d}')
    if video_present and slide.media=='video':
        _pill(c,'VIDEO: OPEN COMPANION HTML',612,10,font=bold,
              color=colors['guest'],bg=colors['surface_soft'],max_w=260,size=9)
        # Local relative URL works when the PDF and index.html are hosted in
        # the same directory. Some file:// PDF viewers block local URI opens.
        c.linkURL(f'{html_name}#slide-{slide.id}',(606,9,879,35),relative=0)
    if slide.layout=='cover':
        c.setFillColor(_color(colors['guest'])); c.setFont(bold, 12)
        c.drawString(49,458,slide.kicker)
        y=_paragraph(c,slide.title,49,386,410,font=bold,size=44,
                     ink=colors['foreground'],leading=53,max_lines=3)-16
        y=_paragraph(c,slide.subtitle,49,y,412,font=regular,size=14,
                     ink=colors['muted'],leading=21,max_lines=5)
        _bullet_list(c,slide.points,49,y-23,410,colors,fonts,size=12,limit=3)
        _visual(c,slide,(487,129,424,244),theme,colors)
        return
    if slide.layout=='statement':
        c.setFillColor(_color(colors['guest'])); c.setFont(bold, 11)
        c.drawString(72,469,slide.kicker)
        y=_paragraph(c,slide.title,72,399,828,font=bold,size=41,
                     ink=colors['foreground'],leading=49,max_lines=2)-15
        y=_paragraph(c,slide.subtitle,72,y,793,font=regular,size=18,
                     ink=colors['muted'],leading=26,max_lines=3)-25
        _bullet_list(c,slide.points,79,y,745,colors,fonts,size=16,gap=16,limit=4)
        return
    end_header=_title(c,slide,colors,fonts)
    if slide.layout=='cinema':
        _visual(c,slide,(63,92,834,307),theme,colors)
        _bullet_list(c,slide.points,72,75,820,colors,fonts,size=10.2,gap=1,limit=2,min_bottom=45)
    elif slide.layout=='split':
        _visual(c,slide,(41,90,576,307),theme,colors)
        x=640
        y=_bullet_list(c,slide.points,x,388,277,colors,fonts,size=11.5,gap=9,limit=4,min_bottom=210)
        c.setFillColor(_color(colors['guest']));c.setFont(bold,10)
        c.drawString(x,min(y,225),'OPERATION EVIDENCE')
        _operations(c,slide,(x,min(y,225)-12,277),colors,fonts,columns=1,max_items=2,item_height=62)
    elif slide.layout=='diagram':
        _visual(c,slide,(55,77,850,326),theme,colors)
        c.setFont(regular,10.1);c.setFillColor(_color(colors['muted']))
        c.drawCentredString(PAGE_W/2,58,_fitline('   /   '.join(slide.points),regular,10.1,864))
    elif slide.layout=='evidence':
        _operations(c,slide,(42,401,600),colors,fonts,columns=2,max_items=6,item_height=73)
        _bullet_list(c,slide.points,674,386,239,colors,fonts,size=12.6,gap=16,limit=4)
    else:
        raise ValueError(f'unknown slide layout: {slide.layout}')


def render_pdf(deck: SlideDeck, target: Path, *, theme: str='dark',
               video_scenes: set[str] | None=None, html_name: str='index.html') -> Path:
    """Generate a paged, static PDF from same evidence plans and slide layout."""
    try:
        from reportlab.pdfgen.canvas import Canvas
    except ImportError as ex:
        raise RuntimeError('PDF export requires uv sync --extra presentation') from ex
    colors=palette(theme)
    fonts=_fonts()
    target.parent.mkdir(parents=True,exist_ok=True)
    c=Canvas(str(target),pagesize=(PAGE_W,PAGE_H),pageCompression=1)
    c.setTitle(deck.title)
    c.setAuthor('Transcrypt visualizations')
    c.setSubject('Static presentation companion; videos play in adjacent HTML')
    for i,slide in enumerate(deck.slides,1):
        _page(c,slide,i,len(deck.slides),theme,slide.scene.id in (video_scenes or set()),colors,fonts,html_name)
        c.showPage()
    c.save()
    return target
