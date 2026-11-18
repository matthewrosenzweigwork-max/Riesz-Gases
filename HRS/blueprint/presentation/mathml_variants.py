"""Preserve author-selected MathML styles in native MathML Core renderers.
Only explicitly styled single ASCII letters/digits are transformed. TeX is untouched.
"""
import unicodedata as U
VARIANTS={'sans-serif':'SANS-SERIF','bold-sans-serif':'SANS-SERIF BOLD','sans-serif-italic':'SANS-SERIF ITALIC','sans-serif-bold-italic':'SANS-SERIF BOLD ITALIC','double-struck':'DOUBLE-STRUCK','script':'SCRIPT','bold-script':'BOLD SCRIPT','fraktur':'FRAKTUR','bold-fraktur':'BOLD FRAKTUR','monospace':'MONOSPACE','bold':'BOLD','italic':'ITALIC','bold-italic':'BOLD ITALIC'}
HOLES={'SCRIPT':dict(zip('BEFHILMR ego'.replace(' ',''),'ℬℰℱℋℐℒℳℛℯℊℴ')),'FRAKTUR':dict(zip('CHIRZ','ℭℌℑℜℨ')),'DOUBLE-STRUCK':dict(zip('CHNPQRZ','ℂℍℕℙℚℝℤ')),'ITALIC':{'h':'ℎ'}}
def styled(c,v):
 name=VARIANTS[v]
 if c in HOLES.get(name,{}):return HOLES[name][c]
 if 'A'<=c<='Z':tail='CAPITAL '+c
 elif 'a'<=c<='z':tail='SMALL '+c.upper()
 elif c.isascii() and c.isdigit():tail='DIGIT '+['ZERO','ONE','TWO','THREE','FOUR','FIVE','SIX','SEVEN','EIGHT','NINE'][int(c)]
 else:return None
 try:return U.lookup('MATHEMATICAL '+name+' '+tail)
 except KeyError:return None

def normalize(soup):
 changes=[];unresolved=[]
 for e in soup.select('math [mathvariant]'):
  variant=e.get('mathvariant')
  if variant not in VARIANTS:continue
  text=e.get_text()
  if e.name not in ('mi','mn') or len(text)!=1 or len(list(e.children))!=1:
   unresolved.append({'tag':e.name,'variant':variant,'text':text});continue
  new=styled(text,variant)
  if new is None:
   unresolved.append({'tag':e.name,'variant':variant,'text':text});continue
  e.string=new;e['mathvariant']='normal'
  changes.append({'old':text,'variant':variant,'new':new,'unicode_name':U.name(new)})
 return changes,unresolved
