import importlib.util
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location('markdown_links', Path(__file__).resolve().parents[1] / 'scripts/check-markdown-links.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class LinkChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'target.md').write_text('# A heading\n# A heading\n<a id="custom"></a>\nSetext heading\n==============\n')
        (self.root / 'file (one).txt').write_text('ok')

    def check(self, body):
        source = self.root / 'source.md'
        source.write_text(body)
        return checker.check(self.root, [source])

    def test_links_and_anchors(self):
        self.assertEqual([], self.check('''[one](target.md#a-heading)
[two](target.md#a-heading-1) [custom](target.md#custom)
[setext](target.md#setext-heading) [file](<file (one).txt>)
[ref][ID] [collapsed][] ![image][id] [id]
[id]: target.md#a-heading
[collapsed]: target.md#custom
[web](https://example.invalid/no-check) [source](target.md?plain=1#a-heading)
'''))

    def test_missing_paths_anchors_and_references_fail(self):
        errors = self.check('[bad](missing.md)\n[bad](target.md#missing)\n[bad][missing]\n')
        self.assertEqual(3, len(errors))
        self.assertIn('missing path', errors[0][2])
        self.assertIn('missing anchor', errors[1][2])
        self.assertIn('undefined reference', errors[2][2])

    def test_nested_label_is_checked(self):
        self.assertEqual(1, len(self.check('[a [nested] label](missing.md)')))

    def test_shortcut_and_indented_list_link_are_checked(self):
        errors = self.check('    [x](missing.md)\n[bad]\n[bad]: missing.md\n')
        self.assertEqual(2, len(errors))

    def test_comments_and_code_are_not_links(self):
        self.assertEqual([], self.check('''<!-- [no](missing.md) -->
`[no](missing.md)`
```markdown
[no](missing.md)
```
~~~
[no](missing.md)
~~~
'''))

    def test_html_and_escaped_destinations(self):
        self.assertEqual([], self.check('<a href="target.md#custom">ok</a>\n[ok](file%20%28one%29.txt)\n'))
        self.assertEqual(1, len(self.check('<a href="target.md#missing">broken</a>')))


if __name__ == '__main__':
    unittest.main()
