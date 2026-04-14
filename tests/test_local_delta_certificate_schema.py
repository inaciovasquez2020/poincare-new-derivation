from pathlib import Path

def test_local_delta_certificate_schema_lock():
    text = Path('docs/math/LOCAL_DELTA_CERTIFICATE_SCHEMA.md').read_text(encoding='utf-8')
    assert 'Delta Certificate Schema' in text
    assert '\\Delta_{\\mathcal N}\\Phi' in text
    assert 'Status: Open.' in text
