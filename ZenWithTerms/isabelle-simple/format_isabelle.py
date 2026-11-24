#!/usr/bin/env python3
"""Whitespace-only layout of Isabelle theory files.

Re-lays out the following constructs, aligning on rendered columns (an Isabelle symbol such as
\\<lparr> counts as one column). Everything except the last item is inside double-quoted terms.

  * Record brackets \\<lparr> ... \\<rparr> with several fields (updates `:=` or constructions `=`):
    \\<lparr> ends the line on which the record starts, one field per line follows, indented two
    columns from that line, with the field names padded so that the operators line up, and
    \\<rparr> is on a line of its own at the indentation of the first line.

  * `let ... in ...`: the bindings are aligned after `let`, and `in` is on its own line directly
    below `let`.

  * A function application with many arguments (at least MIN_APP_ARGS, if it is wider than
    MIN_APP_WIDTH on one line, or a shorter one that is too long for the line): the function on the first line, then one argument per line, aligned,
    APP_INDENT columns in from the start of the function. Quantifier and lambda binder lists are
    not arguments.
      - If the application is the left-hand side of an equation, the `=` goes on a line of its own,
        aligned with the start of the left-hand side.
      - If it is the right-hand side, `lhs = f a b c` is first tried with the `=` moved to a line
        of its own, aligned with the start of the left-hand side, so that the right-hand side can
        stay on one line.

  * A chain of conjunctions or disjunctions that is too long for the line, or that the author has
    already broken: each operator starts its line, at the column of the first operand, with its
    operand following it. A bracketed operand starts a new, deeper level, which shows the nesting.
    Operands of the weaker operator (disjunction) are laid out first; a conjunction inside one is
    laid out on its own if it is long. The first operand of an unbracketed chain is not indented,
    so the operators of a chain nested there line up with those of the outer chain.

  * In a proof, a `from`/`with`/`using` list of facts that is followed on the same line by `have`,
    `show`, `obtain`, `hence` or `thus`, where that keyword would start beyond FACT_BREAK_COL: the
    keyword moves to a line of its own, at the same indentation.

Everything else, including the author's own line breaks, is kept as written. The tool never
changes anything but whitespace: the sequence of non-whitespace tokens of each file is compared
before and after, and a file that would differ is left untouched and reported. Text blocks (text,
section, ...) are not touched. Running the tool twice changes nothing.

Usage:  format_isabelle.py [--check] [FILE.thy ...]     (default: every .thy next to this script)
        --check  change nothing; exit with status 1 if any file would change
"""
import re, sys, pathlib

MAX_WIDTH = 100        # a record that fits within this many columns, and has few fields, stays on one line
MIN_VERTICAL_FIELDS = 3  # records with at least this many fields are always laid out one per line
FACT_BREAK_COL = 50      # `from facts have ...` breaks before `have` if `have` would start beyond this column
APP_INDENT = 4           # columns by which the arguments of a broken application are indented from the function
MIN_APP_ARGS = 6         # an application with at least this many arguments is laid out one argument per line ...
MIN_APP_WIDTH = 100       # ... if, on a single line, it would be wider than this; a short one stays on one line
SKIP_COMMANDS = ("theory", "begin", "end", "text", "section", "subsection", "subsubsection",
                 "txt", "chapter", "(*")

KEYWORDS = {'if', 'then', 'else', 'let', 'in', 'of', 'case', 'where', 'and', 'for', 'is', 'fix',
            'assumes', 'shows', 'obtains', 'from', 'using', 'by', 'proof', 'qed', 'next'}
# Tokens that end a chain of conjunctions or disjunctions because they bind more weakly.
LOWER = {'\\<longrightarrow>', '\\<longleftrightarrow>', '\\<Longrightarrow>', 'if', 'then', 'else', 'case',
         'of', '|', ',', ':='}
BINDERS = {'\\<forall>', '\\<exists>', '\\<lambda>', '\\<And>'}
ATOM = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_'.?]*$")

TOKEN = re.compile(r'\\<\^?[A-Za-z]+>|:=|[A-Za-z0-9_\'.?]+|\s+|.', re.S)
LP, RP = '\\<lparr>', '\\<rparr>'
OPEN, CLOSE = {'(': ')', '[': ']', '{': '}'}, {')', ']', '}'}


def vw(text):
    """Rendered width: an Isabelle symbol is one column."""
    return len(re.sub(r'\\<\^?[A-Za-z]+>', 'X', text))


class Tok:
    def __init__(self, text, col):
        self.text, self.col = text, col       # col: rendered column in the original text
    def is_ws(self): return self.text.isspace()


class Group:                                   # a bracketed group; also used for \<lparr> ... \<rparr>
    def __init__(self, open_tok, items, close_tok):
        self.open, self.items, self.close = open_tok, items, close_tok


class Let:
    def __init__(self, let_tok, bindings, body):
        self.let, self.bindings, self.body = let_tok, bindings, body


def tokenize(text):
    toks, col = [], 0
    for m in TOKEN.finditer(text):
        t = m.group(0)
        toks.append(Tok(t, col))
        nl = t.rfind('\n')
        col = vw(t[nl + 1:]) if nl >= 0 else col + vw(t)
    return toks


def parse(toks):
    pos = [0]

    def seq(stop):
        items = []
        while pos[0] < len(toks):
            t = toks[pos[0]]
            if t.text in stop:
                return items
            pos[0] += 1
            if t.text in OPEN or t.text == LP:
                closer = RP if t.text == LP else OPEN[t.text]
                inner = seq({closer})
                close = toks[pos[0]] if pos[0] < len(toks) else None
                pos[0] += 1
                items.append(Group(t, inner, close))
            elif t.text == 'let':
                items.append(let_rest(t, stop))
            else:
                items.append(t)
        return items

    def let_rest(let_tok, stop):
        bindings, cur = [], []
        while pos[0] < len(toks):
            t = toks[pos[0]]
            if t.text == 'in':
                pos[0] += 1
                bindings.append(cur)
                return Let(let_tok, bindings, seq(stop))
            if t.text == ';':
                pos[0] += 1
                bindings.append(cur)
                cur = []
                continue
            if t.text in stop:
                break
            pos[0] += 1
            if t.text in OPEN or t.text == LP:
                closer = RP if t.text == LP else OPEN[t.text]
                inner = seq({closer})
                close = toks[pos[0]] if pos[0] < len(toks) else None
                pos[0] += 1
                cur.append(Group(t, inner, close))
            elif t.text == 'let':
                cur.append(let_rest(t, stop | {';', 'in'}))
            else:
                cur.append(t)
        raise ValueError('let without in')

    items = seq(set())
    return items


def flat(items):
    """Single-line text: whitespace runs collapse to one space, no leading or trailing space."""
    out = []
    for it in items:
        if isinstance(it, Tok):
            out.append(' ' if it.is_ws() else it.text)
        elif isinstance(it, Group):
            out.append(it.open.text + flat_inner(it.items) + (it.close.text if it.close else ''))
        else:
            out.append('let ' + '; '.join(flat(b) for b in it.bindings) + ' in ' + flat(it.body))
    return re.sub(r' +', ' ', ''.join(out)).strip()


def flat_inner(items):
    return flat(items) if items else ''


def first_col(items):
    for it in items:
        if isinstance(it, Tok):
            if not it.is_ws():
                return it.col
        elif isinstance(it, Group):
            return it.open.col
        else:
            return it.let.col
    return 0


def split_fields(items):
    """Split the items of a record on top-level commas into (name, op, value-items) triples."""
    fields, cur = [], []
    for it in items:
        if isinstance(it, Tok) and it.text == ',':
            fields.append(cur)
            cur = []
        else:
            cur.append(it)
    fields.append(cur)
    result = []
    for f in fields:
        k = next((i for i, it in enumerate(f) if isinstance(it, Tok) and it.text in (':=', '=')), None)
        if k is None:
            return None
        result.append((flat(f[:k]), f[k].text, f[k + 1:]))
    return result


class Printer:
    def __init__(self, first_indent=0):
        self.out = []
        self.first_indent = first_indent   # indentation of the source line on which the term starts
        self.breaks = 0                    # number of applications laid out one argument per line

    def line_indent(self):
        text = self.text()
        if '\n' not in text:
            return self.first_indent
        line = text[text.rfind('\n') + 1:]
        return len(line) - len(line.lstrip(' '))

    def text(self):
        return ''.join(self.out)

    def col(self):
        s = self.text()
        return vw(s[s.rfind('\n') + 1:])

    def put(self, s):
        self.out.append(s)

    def region(self, items):
        """Emit items; original newlines inside are kept, re-indented by the move of the region."""
        items = list(items)
        while items and isinstance(items[0], Tok) and items[0].is_ws():
            items.pop(0)
        while items and isinstance(items[-1], Tok) and items[-1].is_ws():
            items.pop()
        if not items:
            return
        shift = self.col() - first_col(items)
        self.emit(items, shift)

    def emit(self, items, shift):
        """Emit items, laying out long chains of conjunctions or disjunctions."""
        b = next((k for k, it in enumerate(items) if isinstance(it, Tok) and it.text in BINDERS), None)
        if b is not None:
            dot = next((k for k in range(b + 1, len(items))
                        if isinstance(items[k], Tok) and items[k].text.endswith('.')), None)
            if dot is not None:               # the body of a binder is a level of its own
                self.emit_level(items[:b], shift)
                for it in items[b:dot + 1]:
                    self.item(it, shift)
                self.emit(items[dot + 1:], shift)
                return
        self.emit_level(items, shift)

    def emit_level(self, items, shift):
        segment = []
        for it in items:
            if isinstance(it, Tok) and it.text in LOWER:
                self.emit_segment(segment, shift)
                self.item(it, shift)
                segment = []
            else:
                segment.append(it)
        self.emit_segment(segment, shift)

    def emit_segment(self, items, shift):
        lead = 0
        while lead < len(items) and isinstance(items[lead], Tok) and items[lead].is_ws():
            lead += 1
        end = len(items)
        while end > lead and isinstance(items[end - 1], Tok) and items[end - 1].is_ws():
            end -= 1
        for it in items[:lead]:
            self.item(it, shift)
        core = items[lead:end]
        operator = None
        for candidate in ('\\<or>', '\\<and>'):
            if any(isinstance(it, Tok) and it.text == candidate for it in core):
                operator = candidate
                break
        operands = []
        if operator:
            current = []
            for it in core:
                if isinstance(it, Tok) and it.text == operator:
                    operands.append(current)
                    current = []
                else:
                    current.append(it)
            operands.append(current)
        newline = any(isinstance(it, Tok) and it.is_ws() and '\n' in it.text for it in core)
        if operator and len(operands) >= 2 and (newline or self.col() + vw(flat(core)) > MAX_WIDTH):
            column = self.col()
            for k, operand in enumerate(operands):
                if k:
                    self.put('\n' + ' ' * column + operator + ' ')
                self.region(operand)
        else:
            self.emit_apps(core, shift)
        for it in items[end:]:
            self.item(it, shift)

    def emit_apps(self, items, shift):
        i = 0
        scope_col = None                   # column at which this sequence of items starts
        while i < len(items):
            it = items[i]
            if isinstance(it, Tok) and it.is_ws():
                self.item(it, shift)
                i += 1
                continue
            if isinstance(it, Tok) and it.text == '=' and scope_col is not None:
                moved = self.equals_before_rhs(items, i, scope_col)
                if moved is not None:
                    i = moved
                    continue
            if scope_col is None:
                scope_col = self.col()
            before = self.breaks
            run = application(items, i)
            if run is None:
                self.item(it, shift)
                end = i + 1
            else:
                end, clusters = run
                span = items[i:end]
                args = len(clusters) - 1
                width = vw(flat(span))
                if (args >= MIN_APP_ARGS and width > MIN_APP_WIDTH) or \
                        (args >= 3 and self.col() + width > MAX_WIDTH):
                    base = self.col()
                    self.breaks += 1
                    self.emit(clusters[0], shift)
                    for cluster in clusters[1:]:
                        self.put('\n' + ' ' * (base + APP_INDENT))
                        self.region(cluster)
                elif args >= 3:                    # fits on the line: one line, whatever it was before
                    for k, cluster in enumerate(clusters):
                        if k:
                            self.put(' ')
                        for sub in cluster:
                            self.item(sub, shift)
                else:
                    for sub in span:
                        self.item(sub, shift)
            i = end
            if self.breaks > before:
                i = self.equals_on_own_line(items, i, scope_col, shift)

    def equals_before_rhs(self, items, i, scope_col):
        """For `lhs = f a b c` whose right-hand side is too long to follow the `=` but fits on a
        line of its own: put `= f a b c` on a new line at the start of the left-hand side."""
        j = i + 1
        while j < len(items) and isinstance(items[j], Tok) and items[j].is_ws():
            j += 1
        run = application(items, j) if j < len(items) else None
        if run is None:
            return None
        end, clusters = run
        args = len(clusters) - 1
        text = self.text().rstrip()
        line = text[text.rfind('\n') + 1:]
        width = vw(flat(items[j:end]))
        if not (args >= 3 and (args < MIN_APP_ARGS or width <= MIN_APP_WIDTH) and vw(line) + 3 + width > MAX_WIDTH
                and scope_col + 2 + width <= MAX_WIDTH):
            return None
        self.out = [text + '\n' + ' ' * scope_col + '= ']
        return j

    def equals_on_own_line(self, items, i, scope_col, shift):
        """After a broken application, `= rhs` becomes `=` on its own line, then `rhs`."""
        j = i
        while j < len(items) and isinstance(items[j], Tok) and items[j].is_ws():
            j += 1
        if not (j < len(items) and isinstance(items[j], Tok) and items[j].text == '='):
            return i
        self.put('\n' + ' ' * scope_col + '=')
        k = j + 1
        if k < len(items) and isinstance(items[k], Tok) and items[k].is_ws() and '\n' in items[k].text:
            return k                       # the right-hand side already starts on a new line
        while k < len(items) and isinstance(items[k], Tok) and items[k].is_ws():
            k += 1
        self.put('\n' + ' ' * (scope_col + 1))
        return k

    def item(self, it, shift):
        if isinstance(it, Tok):
            t = it.text
            if it.is_ws() and '\n' in t:
                head, _, indent = t.rpartition('\n')
                t = head + '\n' + ' ' * max(0, len(indent) + shift)
            self.put(t)
        elif isinstance(it, Group):
            self.group(it, shift)
        else:
            self.let(it)

    def group(self, g, shift):
        if g.open.text != LP:
            self.put(g.open.text)
            self.emit(g.items, shift)
            if g.close: self.put(g.close.text)
            return
        fields = split_fields(g.items)
        if fields is None or len(fields) < 2:
            self.put(g.open.text)
            self.emit(g.items, shift)
            self.put(g.close.text)
            return
        start_col = self.col()
        one_line = LP + ', '.join('%s %s %s' % (n, op, flat(v)) for n, op, v in fields) + RP
        if len(fields) < MIN_VERTICAL_FIELDS and start_col + vw(one_line) <= MAX_WIDTH \
                and not any(has_let(v) for _, _, v in fields):
            self.put(one_line)
            return
        width = max(vw(n) for n, _, _ in fields)
        base = self.line_indent()
        self.put(LP)
        for i, (n, op, v) in enumerate(fields):
            self.put('\n' + ' ' * (base + 2))
            self.put(n + ' ' * (width - vw(n)) + ' ' + op + ' ')
            self.region(v)
            if i < len(fields) - 1:
                self.put(',')
        self.put('\n' + ' ' * base + RP)

    def let(self, node):
        col = self.col()
        self.put('let ')
        for i, b in enumerate(node.bindings):
            if i:
                self.put('\n' + ' ' * (col + 4))
            k = next((j for j, it in enumerate(b) if isinstance(it, Tok) and it.text == '='), None)
            if k is None:
                self.region(b)
            else:
                self.put(flat(b[:k]) + ' = ')
                self.region(b[k + 1:])
            if i < len(node.bindings) - 1:
                self.put(';')
        self.put('\n' + ' ' * col + 'in ')
        self.region(node.body)


def atomic(cluster):
    """A cluster of adjacent items that contains no operator, so it can be an argument."""
    for it in cluster:
        if isinstance(it, Let):
            return False
        if isinstance(it, Tok) and not (ATOM.match(it.text) and it.text not in KEYWORDS):
            return False
    return True


def cluster_at(items, i):
    j = i
    while j < len(items) and not (isinstance(items[j], Tok) and items[j].is_ws()):
        j += 1
    return items[i:j]


def application(items, i):
    """If items[i:] starts with an application `f a1 ... an` (n >= 1), return (end, clusters)."""
    first = cluster_at(items, i)
    if not first or not atomic(first) or not isinstance(first[0], Tok) or first[0].text.isdigit():
        return None
    k = i - 1                          # not an argument list of a quantifier or lambda
    while k >= 0 and isinstance(items[k], Tok) and items[k].is_ws():
        k -= 1
    if k >= 0 and isinstance(items[k], Tok) and items[k].text in BINDERS:
        return None
    clusters, end = [first], i + len(first)
    while True:
        j = end
        while j < len(items) and isinstance(items[j], Tok) and items[j].is_ws():
            j += 1
        if j == end or j >= len(items):
            break
        nxt = cluster_at(items, j)
        if not atomic(nxt):
            break
        clusters.append(nxt)
        end = j + len(nxt)
    return (end, clusters) if len(clusters) > 1 else None


def walk(items):
    for it in items:
        if isinstance(it, Tok):
            yield it
        elif isinstance(it, Group):
            yield it.open
            yield from walk(it.items)
            if it.close: yield it.close
        else:
            yield it.let
            for b in it.bindings: yield from walk(b)
            yield from walk(it.body)


def has_let(items):
    return any(t.text == 'let' for t in walk(items))


def significant(text):
    return [t.text for t in tokenize(text) if not t.is_ws()]


def format_text(text):
    """Reformat the quoted terms of every non-text command."""
    parts = re.split(r'(?m)^(?=\S)', text)
    result = []
    for part in parts:
        if part.startswith(SKIP_COMMANDS) or any(part.startswith(k + ' ') for k in SKIP_COMMANDS):
            result.append(part)
            continue
        result.append(format_command(part))
    return ''.join(result)


FACT_LINE = re.compile(
    r'^(?P<indent>[ ]*)(?P<facts>(?:from|with|using)\b[^"\n]*?)[ ]+(?P<keyword>have|show|obtain|hence|thus)\b(?P<rest>.*)$')


def break_fact_lines(part):
    """Put `have` (or `show`, ...) on a line of its own after a long `with`/`from` list of facts."""
    lines = part.split('\n')
    for k, line in enumerate(lines):
        m = FACT_LINE.match(line)
        if m and vw(m.group('indent') + m.group('facts')) + 1 > FACT_BREAK_COL:
            lines[k] = (m.group('indent') + m.group('facts') + '\n' + m.group('indent')
                        + m.group('keyword') + m.group('rest'))
    return '\n'.join(lines)


def format_command(part):
    part = break_fact_lines(part)
    out, i = [], 0
    for m in re.finditer(r'"((?:[^"\\]|\\.)*)"', part):
        body = m.group(1)
        out.append(part[i:m.start(1)])
        line_start = part.rfind('\n', 0, m.start(1)) + 1
        prefix = part[line_start:m.start(1)]
        out.append(format_in_context(prefix, body))
        i = m.end(1)
    out.append(part[i:])
    return ''.join(out)


def format_in_context(prefix, body):
    """Format `body` as it appears after `prefix` on its first line."""
    pad = vw(prefix)
    toks = tokenize(' ' * pad + body)
    items = parse(toks)
    p = Printer(len(prefix) - len(prefix.lstrip(' ')))
    p.put(' ' * pad)
    p.emit(items[1:] if items and isinstance(items[0], Tok) and items[0].is_ws() else items, 0)
    return p.text()[pad:]


def format_file(path, check):
    text = path.read_text()
    try:
        new = format_text(text)
    except ValueError as e:
        print('%s: skipped (%s)' % (path, e)); return False
    if significant(new) != significant(text):
        print('%s: skipped (would change more than whitespace)' % path); return False
    if new == text:
        return False
    if not check:
        path.write_text(new)
    print('%s: %s' % (path, 'would change' if check else 'reformatted'))
    return True


def main(argv):
    check = '--check' in argv
    files = [pathlib.Path(a) for a in argv if not a.startswith('--')]
    if not files:
        files = sorted(pathlib.Path(__file__).resolve().parent.glob('*.thy'))
    changed = [format_file(f, check) for f in files]
    return 1 if check and any(changed) else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
