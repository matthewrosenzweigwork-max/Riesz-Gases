#!/usr/bin/env python3
"""Idempotent manuscript navigation overlay; never changes mathematics or source code."""
from pathlib import Path
import argparse,json,re,os
from lxml import html as H, etree as E
HERE=Path(__file__).resolve().parent
FEATURES={'M-3':('The-sharp-sub-Coulomb-commutator','§3 · The sharp sub-Coulomb commutator'),'M-6':('Mesoscopic-observations-and-screening','§6 · Mesoscopic observations and screening'),'S-S2':('Whole-space-fluctuations','§S2 · Whole-space fluctuations'),'S-S3':('Whole-space-fluctuations','§S3 · Preparation and stationary transfer'),'S-S5':('Whole-space-fluctuations','§S5 · Weighted paths and field estimates'),'S-S11':('Relaxation-on-moving-windows','§S11 · Relaxation on moving windows')}
CSS='''\n/* Manuscript navigation: no independent reader numbering. */
.hrs-manuscript-nav{font-size:1rem;line-height:1.5;max-width:100%;padding:.5rem}.hrs-manuscript-nav ul{list-style:none;padding-left:.65rem}.hrs-manuscript-nav li{margin:.4rem 0}.hrs-manuscript-nav a{overflow-wrap:anywhere}.hrs-manuscript-nav h2,.hrs-manuscript-nav h3{font-size:1.1rem;margin:1rem 0 .3rem}.hrs-manuscript-nav a:focus-visible{outline:3px solid #165e91;outline-offset:3px}.hrs-reader-context{display:flex;flex-wrap:wrap;gap:.7rem;padding:.6rem}.hrs-reader-context a{overflow-wrap:anywhere}#toc .hrs-manuscript-nav{max-height:65vh;overflow:auto}#toc table td.num:empty{display:none}\n'''
def run(tree):
 tree=Path(tree).resolve();reader=tree/'reader'; sections=json.loads((HERE/'manuscript-navigation.json').read_text())
 for f in [reader/'index.html',*reader.glob('*/index.html')]:
  if f.parent.name in ['source','native-docs','notices']:continue
  d=H.fromstring(f.read_text())
  if d.xpath('//style[@id="hrs-manuscript-navigation-style"]'):continue
  base=d.xpath('//base/@href'); root=(f.parent/(base[0] if base else '.')).resolve()
  def href(target):return os.path.relpath(target,root)
  def destination(s):
   c=tree/'coverage/sections'/(s['id']+'.html')
   return href(c) if c.exists() else href(reader/'Browse-the-paper-and-supplement/index.html')+'#section-'+s['id'].replace('.','___')
  def navigation():
   n=E.Element('div',attrib={'class':'hrs-manuscript-nav'})
   for group,label in [('M','Main manuscript'),('S','Supplement')]:
    E.SubElement(n,'h3').text=label;ul=E.SubElement(n,'ul')
    for s in sections:
     if s['doc']!=group:continue
     li=E.SubElement(ul,'li');a=E.SubElement(li,'a',href=destination(s));a.text='§'+s['id'][2:]+' · '+s['title']
     if s['id'] in FEATURES:
      slug,title=FEATURES[s['id']];a=E.SubElement(li,'a',href=href(reader/slug/'index.html'));a.text=' — '+title.split(' · ',1)[1]
   ul=E.SubElement(n,'ul')
   for label,target in [('Paper index',reader/'Browse-the-paper-and-supplement/index.html'),('Evidence',reader/'Evidence-and-selected-direct-proof-calls/index.html'),('Search',reader/'search/index.html'),('Third-party notices',reader/'notices/index.html')]:
    E.SubElement(E.SubElement(ul,'li'),'a',href=href(target)).text=label
   return n
  # Remove only renderer-generated heading prefixes. Paper/S labels follow them.
  for e in d.xpath('//h1|//h2|//h3|//h4|//h5|//h6'):
   if e.text:e.text=re.sub(r'^(\s*)\d+(?:\.\d+)*\.\s*',r'\1',e.text)
  for e in d.xpath('//*[contains(concat(" ",normalize-space(@class)," ")," number ")]|//td[@class="num"]'):
   e.text=''
  for book in d.xpath('//*[@class="split-toc book"]'):
   for e in list(book):
    if e.tag=='table' or e.get('class')=='hrs-manuscript-nav':book.remove(e)
   book.append(navigation())
  # Blueprint display ordinals are reader positions, not mathematical result labels.
  # Keep their spans and anchors for existing references, suppress only positional numbers.
  for e in d.xpath('//span[contains(concat(" ",normalize-space(@class)," ")," bp_label ")]'):
   if re.fullmatch(r'\d+(?:\.\d+){2,}',(e.text or '').strip()):e.text=''
  # Preserve the old table-of-contents and all local section anchors.
  if f==reader/'index.html':
   for toc in d.xpath('//ol[@class="section-toc"]'):
    toc.tag='div';toc.set('class','hrs-manuscript-nav');toc.clear();toc.set('class','hrs-manuscript-nav');toc.append(navigation())
   for e in d.xpath('//div[@class="titlepage"]/p'):
    if len(e)==1 and e[0].tag=='a':e.getparent().remove(e)
  for e in d.xpath('//nav[@aria-label="Whole-space chapter" or @aria-label="Relaxation on moving windows"]'):
   for ident in e.xpath('.//@id'):d.find('body').insert(0,E.Element('span',id=ident))
   e.getparent().remove(e)
  # No invented previous/next numerical sequence: return to the actual manuscript section.
  slug=f.parent.name; relevant=next((key for key,(s,_) in FEATURES.items() if s==slug),None)
  for n in d.xpath('//nav[@class="prev-next-buttons"]'):
   n.clear();n.set('class','prev-next-buttons');n.set('aria-label','Manuscript navigation')
   E.SubElement(n,'a',href=href(reader/'index.html')).text='Reader home'
   if relevant:E.SubElement(n,'a',href=destination(next(s for s in sections if s['id']==relevant))).text='Return to §'+relevant[2:]
   E.SubElement(n,'a',href=href(reader/'Browse-the-paper-and-supplement/index.html')).text='Paper index'
  if not d.xpath('//*[@id="hrs-manuscript-context"]'):
   n=E.Element('nav',id='hrs-manuscript-context',attrib={'class':'hrs-reader-context','aria-label':'Manuscript context'})
   E.SubElement(n,'a',href=href(reader/'index.html')).text='Reader home'
   if relevant:E.SubElement(n,'a',href=destination(next(s for s in sections if s['id']==relevant))).text='Supplement §'+relevant[2:] if relevant.startswith('S-') else 'Main manuscript §'+relevant[2:]
   E.SubElement(n,'a',href=href(reader/'Browse-the-paper-and-supplement/index.html')).text='Main manuscript and supplement'
   d.find('body').insert(0,n)
  # Links to actual features from paper-index section headings.
  for key,(slug,title) in FEATURES.items():
   ident='section-'+key;found=d.xpath('//*[@id=$id]',id=ident)
   if found and not d.xpath('//*[@id=$id]',id='reader-feature-'+key):
    n=E.Element('p',id='reader-feature-'+key);E.SubElement(n,'a',href=href(reader/slug/'index.html')).text=title;found[0].addnext(n)
  for h in d.xpath('//h1'):
   text=(h.text or '').strip()
   if text in ['The sharp sub-Coulomb commutator','Mesoscopic observations and screening']:h.text=('§3 · ' if text.startswith('The sharp') else '§6 · ')+text
   elif text=='Whole-space fluctuations':h.text='§§S2–S5 · Whole-space fluctuations'
   elif text=='Relaxation on moving windows':h.text='§S11 · Relaxation on moving windows'
  if not d.xpath('//style[@id="hrs-manuscript-navigation-style"]'):E.SubElement(d.find('head'),'style',id='hrs-manuscript-navigation-style').text=CSS
  f.write_text('<!DOCTYPE html>\n'+E.tostring(d,encoding='unicode',method='html'))
 for key,(slug,title) in FEATURES.items():
  f=tree/'coverage/sections'/(key+'.html')
  if not f.exists():continue
  d=H.fromstring(f.read_text())
  if not d.xpath('//*[@id="hrs-reader-feature"]'):
   p=E.Element('p',id='hrs-reader-feature');E.SubElement(p,'a',href='../../reader/'+slug+'/index.html').text='Read '+title
   d.xpath('//h1')[0].addnext(p)
  f.write_text('<!DOCTYPE html>\n'+E.tostring(d,encoding='unicode',method='html'))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--tree',required=True);run(p.parse_args().tree)
