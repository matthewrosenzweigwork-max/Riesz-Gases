"""Present manuscript labels in Verso search without renumbering native records."""
from pathlib import Path

def replace_once(text,before,after):
    if after in text:  # An already transformed static tree is also valid.
        assert before not in text
        return text
    assert text.count(before)==1, f"Unexpected Verso search template for {before!r}"
    return text.replace(before,after)

def apply_search_labels(reader_dir):
    root=Path(reader_dir)/'-verso-search'
    p=root/'search-box.js'
    s=p.read_text()
    # Verso's full-text headers include its generated chapter ordinal even
    # where the author's own heading already contains the manuscript number.
    # Remove exactly one ordinal from the header, never from any mathematical text.
    s=replace_once(s, 'let headerHl = highlightTextResult(doc.header, term, { contextLength: headerContext });',
        r'''// Modified for the HRS reader: suppress the generated Verso ordinal;
    // keep the authored manuscript title, search target, highlighted terms and context.
    const paperHeader = doc.header.replace(/^\d+(?:\.\d+)*\.\s+/, "");
    let headerHl = highlightTextResult(paperHeader, term, { contextLength: headerContext });''')
    s=replace_once(s,'headerHl.append(document.createTextNode(doc.header));','headerHl.append(document.createTextNode(paperHeader));')
    p.write_text(s)
    p=root/'domain-mappers.js';s=p.read_text()
    # Semantic section records separate the authored title from the generated
    # sectionNum; use only the former in a section's search key and visible label.
    s=replace_once(s,"searchKey: `${value[0].data.sectionNum ?? ''} ${value[0].data.title}`,",
        '// Modified for the HRS reader: only manuscript titles supply public numbering.\n            searchKey: value[0].data.title,')
    p.write_text(s)

    # Post-release D.6 removal: old native snapshots remain historical inputs.
    # Filter the neutral legacy resolver alias before either search UI renders it.
    p=root/'search-box.js';s=p.read_text()
    s=replace_once(s, '    return candidates;', '''    // HRS current-source removal: retain legacy anchors, do not advertise removed content.
    return candidates.filter(candidate => {
        const address = candidate.kind === "semantic" ? candidate.searchable.address : candidate.textMatch.ref;
        return !/#sample-6(?:$|[?&])/.test(address);
    });''')
    p.write_text(s)
