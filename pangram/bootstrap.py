# Ph'nglui mglw'nafh Cthulhu R'lyeh wgah'nagl fhtagn

import re
from collections import namedtuple
import json
import subprocess

_Loc = namedtuple("_Loc", ["line", "col", "offs"])

class Loc(_Loc):
    def advance(self, s):
        line, col, offs = self
        for c in s:
            if c == "\n":
                line += 1
                col = 1
            else:
                col += 1
            offs += 1
        return Loc(line, col, offs)

    def __str__(self):
        return f"{self.line}:{self.col}"

_Span = namedtuple("_Span", ["a", "b"])

class Span(_Span):
    def __str__(self):
        return f"{self.a}..{self.b}"

    def __add__(self, other):
        a = min(self.a, other.a)
        b = max(self.b, other.b)
        return Span(a, b)

_Token = namedtuple("Token", ["name", "text", "span"])

class Token(_Token):
    def __str__(self):
        return f"{self.name} ({self.span})"

def tokenize(regexes, s):
    loc = Loc(1, 1, 0)
    failed = False
    while s:
        long_name = None
        long_length = 0
        long_match = None
        for name, regex in regexes:
            match = regex.match(s)
            if match:
                length = len(match.group(0))
                if length > long_length:
                    long_name = name
                    long_length = length
                    long_match = match
        long_length = max(1, long_length)

        loc_before = loc
        loc = loc.advance(s[:long_length])
        s = s[long_length:]
        span = Span(loc_before, loc)

        if not long_match:
            print(f"no token matched at {loc_before}, skipping...")
            failed = True
        elif long_name:
            yield Token(long_name, long_match.group(0), span)

    yield Token("EOF", "", Span(loc, loc))

    if failed:
        raise ValueError("tokenization errors occured")

class Node:
    def __init__(self, name, data, span):
        super().__init__()
        self.name = name
        self.data = data
        self.span = span

    @classmethod
    def _flatten(cls, nodes):
        for node in nodes:
            if node.name == "FLAT":
                yield from cls._flatten(node.data)
            else:
                yield node

    @classmethod
    def terminal(cls, token):
        return cls(token.name, token.text, token.span)

    @classmethod
    def nonterminal(cls, name, children):
        children = tuple(cls._flatten(children))
        span = None
        for child in children:
            if span is None:
                span = child.span
            else:
                span = span + child.span
        return cls(name, children, span)

    @classmethod
    def flattened(cls, children):
        return cls.nonterminal("FLAT", children)

    @classmethod
    def nothing(cls):
        return cls.flattened([])

    @classmethod
    def error(cls, msg, span):
        return cls("ERR", msg, span)

    def is_error(self):
        return self.name == "ERR"

    def is_terminal(self):
        return isinstance(self.data, str)

    def to_json(self):
        if self.is_terminal():
            data = self.data
        else:
            data = [child.to_json() for child in self.data]
        return {f"{self.name} at {self.span}": data}

    def filter(self, name):
        for child in self.data:
            if child.name == name or child.name.startswith(f"{name}."):
                yield child

    def first(self, name):
        try:
            return next(iter(self.filter(name)))
        except StopIteration:
            return None

    def nth(self, name, n):
        try:
            it = iter(self.filter(name))
            for _ in range(n):
                next(it)
            return next(it)
        except StopIteration:
            return None

    def __eq__(self, other):
        return type(self) == type(other) and self.name == other.name and self.data == other.data and self.span == other.span

    def __hash__(self):
        return hash((type(self), self.name, self.data, self.span))

class Debugger:
    _depth = 0

    def __init__(self, name):
        super().__init__()
        self.name = name
        self.failed = False

    def __enter__(self):
        type(self).print(f"-> {self.name}:")
        type(self)._depth += 1
        return self

    def set_failed(self):
        self.failed = True

    def __exit__(self, exc_type, *_):
        type(self)._depth -= 1
        if exc_type is not None:
            type(self).print(f"## {self.name}")
        elif self.failed:
            type(self).print(f"!! {self.name}")
        else:
            type(self).print(f"<- {self.name}")

    @classmethod
    def print(cls, msg):
        print(f"{'   '*cls._depth}{msg}")


# parse(tokens) -> (node, remaining tokens)
# if node.is_error(), remaining tokens must equal incoming tokens

class ParserFactory:

    @classmethod
    def term(cls, name):
        def out_parser(tokens):
            if tokens[0].name == name:
                return Node.terminal(tokens[0]), tokens[1:]
            return Node.error(f"expected {name}, found {tokens[0].name}", tokens[0].span), tokens
        return cls.debugged(f"term({name})", out_parser)

    @classmethod
    def maybe(cls, parser):
        def out_parser(tokens):
            node, tokens = parser(tokens)
            if node.is_error():
                node = Node.nothing()
            return node, tokens
        return cls.debugged("maybe", out_parser)

    @classmethod
    def any(cls, parser):
        def out_parser(tokens):
            nodes = []
            while True:
                node, tokens = parser(tokens)
                if node.is_error():
                    return Node.flattened(nodes), tokens
                nodes.append(node)
        return cls.debugged("any", out_parser)

    @classmethod
    def many(cls, parser):
        return cls.debugged("many", cls.concat(parser, cls.any(parser)))

    @classmethod
    def concat(cls, *parsers):
        def out_parser(tokens):
            initial_tokens = tokens
            nodes = []
            for parser in parsers:
                node, tokens = parser(tokens)
                if node.is_error():
                    return node, initial_tokens
                nodes.append(node)
            return Node.flattened(nodes), tokens
        return cls.debugged("concat", out_parser)

    @classmethod
    def alter(cls, *parsers):
        def out_parser(tokens):
            for parser in parsers:
                node, new_tokens = parser(tokens)
                if not node.is_error():
                    return node, new_tokens
            return node, tokens
        return cls.debugged("alter", out_parser)

    @classmethod
    def named(cls, name, parser):
        def out_parser(tokens):
            node, tokens = parser(tokens)
            if node.is_error():
                return node, tokens
            return Node.nonterminal(name, [node]), tokens
        return cls.debugged(f"named({name})", out_parser)

    @staticmethod
    def debugged(msg, parser):
        return parser
        def out_parser(tokens):
            with Debugger(f"{msg} at {tokens[0].span.a}") as dbg:
                node, tokens = parser(tokens)
                if node.is_error():
                    dbg.set_failed()
                return node, tokens
        return out_parser


class Parser:
    def __init__(self, name):
        super().__init__()
        self.name = name
        self.options = []
        self.parser = None

    def define_opt(self, name, *parsers):
        if self.parser is not None:
            raise ValueError("can't add definitions after use")
        if len(parsers) == 1:
            parser = parsers[0]
        else:
            parser = ParserFactory().concat(*parsers)
        self.options.append((name, parser))

    def define_one(self, *parsers):
        self.define_opt("", *parsers)

    def __call__(self, tokens):
        if self.parser is None:
            if not self.options:
                raise ValueError(f"no definitions for rule {self.name}")
            pf = ParserFactory()
            if len(self.options) == 1:
                self.parser = pf.named(self.name, self.options[0][1])
            else:
                self.parser = pf.alter(*(pf.named(f"{self.name}.{name}", parser) for name, parser in self.options))
        return self.parser(tokens)

    def parse(self, tokens):
        node, tokens = self(tokens)
        if node.is_error():
            raise ValueError(f"parse error: {node.data} at {node.span}")
        eof_node, tokens = ParserFactory().term("EOF")(tokens)
        if eof_node.is_error():
            for token in tokens:
                print(token)
            raise ValueError(f"parse error: {eof_node.data} at {eof_node.span}")
        return node


class AstGrammar:
    def _clean_doc(self, doc):
        if doc is None:
            return ""
        assert doc.name == "Doc"
        doc = doc.data
        assert doc.startswith("/**")
        assert doc.endswith("*/")
        def strip_line(s):
            s = s.strip()
            if s.startswith("*"):
                s = s[1:]
                if s.startswith(" "):
                    s = s[1:]
            return s
        return "\n".join(map(strip_line, doc[3:-2].strip().split("\n")))

    def _derive_name(self, node):
        if node.is_terminal():
            return ""
        symbol = node.first("Symbol")
        if symbol is not None:
            return symbol.data
        string_literal = node.first("StringLiteral")
        if string_literal is not None:
            return AstLiteral.from_parse_tree(string_literal).as_symbol()
        character_literal = node.first("CharacterLiteral")
        if character_literal is not None:
            return AstLiteral.from_parse_tree(character_literal).as_symbol()
        if not node.data:
            return ""
        for child in node.data:
            name = self._derive_name(child)
            if name:
                return name
        return ""

    def __init__(self, node, case_convert=lambda x: x):
        super().__init__()
        assert node.name == "Grammar"

        # Convert from parse tree to AST for all the rules.
        grammar_rules = [] # [(name, doc, alter_name, alter_doc, rule)]
        token_rules = [] # [(name, doc, rule)]
        used_rules = set("_") # names of rules reachable from any grammar rule
        for rule in node.data:
            doc = self._clean_doc(rule.first("Doc"))
            name = rule.first("Symbol")
            if name is not None:
                name = case_convert(name.data)
            alters = [rule.first("Alternation"), rule.first("FirstAlter")] + list(rule.filter("SubseqAlter"))
            for alter in alters:
                if alter is None:
                    continue
                alter_doc = self._clean_doc(alter.first("Doc"))
                alter_name = alter.first("AlterName")
                if alter_name is not None:
                    alter_name = case_convert(alter_name.first("Symbol").data)
                for sub_alter in alter.filter("Concatenation"):
                    if alter_name is not None:
                        sub_alter_name = alter_name
                    else:
                        sub_alter_name = case_convert(self._derive_name(sub_alter))
                    concat = AstConcatenation.from_parse_tree(sub_alter, case_convert)
                    if rule.name == "Rule.GrammarRule":
                        token_rules.extend(concat.gather_implicit_tokens(case_convert))
                        for used_name in concat.gather_used_tokens(case_convert):
                            used_rules.add(used_name)
                        grammar_rules.append((name, doc, sub_alter_name, alter_doc, concat))
                    elif rule.name == "Rule.TokenRule":
                        token_rules.append((name, doc, concat))
                    elif rule.name == "Rule.WhitespaceRule":
                        token_rules.append(("_", "Whitespace.", concat))
                    else:
                        assert False

        # Combine multiple definitions of grammar- and token rules as
        # alternatives. Note that token_rule_map contains fragments, but
        # token_order does not.
        self.first_rule = grammar_rules[0][0]
        self.grammar_rules = {} # {name: (doc, [(alter_name, alter_doc, rule)])}
        self.token_order = [] # [name]
        self.token_rules = {} # {name: (doc, rule)}
        self.fragment_rules = {} # {name: (doc, rule)}
        token_rule_map = {} # {name: (doc, [rule])}
        token_frag_lookup = {} # {name: rule}
        for name, doc, alter_name, alter_doc, rule in grammar_rules:
            if name in self.grammar_rules:
                self.grammar_rules[name][1].append((alter_name, alter_doc, rule))
            else:
                self.grammar_rules[name] = (doc, [(alter_name, alter_doc, rule)])
        for name, doc, rule in token_rules:
            if name in token_rule_map:
                if rule not in token_rule_map[name][1]:
                    token_rule_map[name][1].append(rule)
            else:
                if name != "_" and name in used_rules:
                    self.token_order.append(name)
                token_rule_map[name] = (doc, [rule])
        if "_" in token_rule_map:
            self.token_order.append("_")
        for name, (doc, rules) in token_rule_map.items():
            if len(rules) == 1:
                rule = rules[0]
            else:
                rule = AstAlternation(rules)
            if name in used_rules:
                self.token_rules[name] = (doc, rule)
            else:
                self.fragment_rules[name] = (doc, rule)
            token_frag_lookup[name] = rule

        # Assert that all rules used in the grammar actually exist and are
        # defined as either a grammar rule or a token rule (but not both).
        for used_rule in used_rules:
            is_grammar = used_rule in self.grammar_rules
            is_token = used_rule in token_rule_map
            if is_token and is_grammar:
                raise ValueError(f"{used_rule} is defined as both a grammar and token rule")
            if not is_token and not is_grammar:
                raise ValueError(f"{used_rule} is not defined")

        # Build regular expressions for the token rules.
        self.token_regexes = {} # {name: regex}
        for name, (_, rule) in self.token_rules.items():
            regex = rule.as_regex(token_frag_lookup, [name])
            self.token_regexes[name] = re.compile(regex)

        # Build ad-hoc recursive-descent parsers for the grammar rules.
        self.grammar_parsers = {name: Parser(name) for name in self.grammar_rules}
        for name, (_, alters) in self.grammar_rules.items():
            parser = self.grammar_parsers[name]
            if len(alters) == 1:
                parser.define_one(alters[0][2].as_parser(self.grammar_parsers, case_convert))
            else:
                for name, _, rule in alters:
                    parser.define_opt(name, rule.as_parser(self.grammar_parsers, case_convert))

    def tokenize(self, s):
        rules = [(token if token != "_" else None, self.token_regexes[token]) for token in self.token_order]
        return tokenize(rules, s)

    def parse(self, tokens, name=None):
        if name is None:
            name = self.first_rule
        return self.grammar_parsers[name].parse(tokens)

    def tokenize_and_parse(self, s, name=None):
        return self.parse(name, list(self.tokenize(s)))


def chumsky_construct(elements, name_lookup, case_convert, type_name, variant_names):
    if variant_names:
        assert len(elements) == len(variant_names)
    children = []
    for index, element in enumerate(elements):
        parser = element.as_chumsky(name_lookup, case_convert)
        tup_len = element.as_chumsky_tuple_length()
        if tup_len == 1:
            map_out = "x"
            map_in = map_out
        else:
            map_out = ", ".join(map(lambda x: f"x{x+1}", range(tup_len)))
            map_in = f"({map_out})"
        if variant_names:
            variant = f"{type_name}::{variant_names[index]}"
        else:
            variant = type_name
        children.append(f"{parser}.map(|{map_in}| {variant}({map_out}))")
    result = [children[0]]
    for index, child in enumerate(children[1:]):
        result.append(f".or({child})")
    last = elements[0].last_terminal(name_lookup, case_convert)
    for element in elements[1:]:
        last2 = element.last_terminal(name_lookup, case_convert)
        if last != last2:
            last = None
    #if last is not None:
        #result.append(f".to_recover(find(|t| t.token_type() == TokenType::{last}).skip().and_return(|_| Default::default()))")
        # TODO add recovery back in
    #result.append(f".labelled(\"{type_name[2:]}\").boxed()")
    result.append(f".boxed()")
    return "".join(result)


def chumsky_define(fil, elements, name_lookup, case_convert, type_name, type_doc, variant_names, variant_docs, index, visit_name):
    if type_doc:
        for line in type_doc.split("\n"):
            fil.write(f"/// {line}\n")
    traverse = []
    traverse_mut = []
    if variant_names:
        assert len(elements) == len(variant_names)
        assert len(elements) == len(variant_docs)
        fil.write("#[derive(Clone, Debug, PartialEq, Eq, Hash)]\n")
        fil.write(f"pub enum {type_name}<'i, S> {{\n")
        fil.write("    /// Used to recover from errors.\n")
        fil.write("    Error,\n")
        traverse.append("match self {")
        traverse_mut.append("match self {")
        traverse.append(f"    {type_name}::Error => (),")
        traverse_mut.append(f"    {type_name}::Error => (),")
        for element, variant, doc in zip(elements, variant_names, variant_docs):
            typ = element.as_chumsky_type(name_lookup, case_convert)
            if not typ.startswith("("):
                typ = f"({typ})"
            fil.write("\n")
            if doc:
                for line in doc.split("\n"):
                    fil.write(f"    /// {line}\n")
            fil.write(f"    {variant}{typ},\n")
            var_names = [f'x{x+1}' for x in range(element.as_chumsky_tuple_length())]
            match = f"    {type_name}::{variant}({', '.join(var_names)}) => {{"
            traverse.append(match)
            traverse_mut.append(match)
            traverse.extend((f"        {x}" for x in element.generate_traverse(name_lookup, case_convert, var_names, False)))
            traverse_mut.extend((f"        {x}" for x in element.generate_traverse(name_lookup, case_convert, var_names, True)))
            traverse.append("    }")
            traverse_mut.append("    }")
        fil.write("}\n\n")
        fil.write(f"impl<'i, S> Default for {type_name}<'i, S> {{\n")
        fil.write("    fn default() -> Self {\n")
        fil.write(f"        {type_name}::Error\n")
        fil.write("    }\n")
        fil.write("}\n\n")
        traverse.append("}")
        traverse_mut.append("}")
    else:
        assert len(elements) == 1
        typ = elements[0].as_chumsky_type(name_lookup, case_convert)
        if not typ.startswith("("):
            typ = f"({typ})"
        fil.write("#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]\n")
        fil.write(f"pub struct {type_name}<'i, S>{typ};\n\n")
        tup_len = elements[0].as_chumsky_tuple_length()
        var_names = [f'x{x+1}' for x in range(tup_len)]
        for var_index, var_name in enumerate(var_names):
            traverse.append(f"let {var_name} = &self.{var_index};")
            traverse_mut.append(f"let {var_name} = &mut self.{var_index};")
        traverse.extend(elements[0].generate_traverse(name_lookup, case_convert, var_names, False))
        traverse_mut.extend(elements[0].generate_traverse(name_lookup, case_convert, var_names, True))
    fil.write(f"impl<'i, S: Default + Eq + std::hash::Hash> {type_name}<'i, S> {{\n")
    if index is not None:
        fil.write(f"""\
    /// Return a Chumsky parser for this rule.
    pub fn parser() -> BoxedParser<'i, {type_name}<'i, S>, S> {{
        make_parsers().{index}
    }}

""")
    if visit_name:
        fil.write(f"""\
    /// Visit this nonterminal node with the given visitor.
    pub fn visit<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {{
        visitor.visit_{visit_name}(self)
    }}

    /// Visit this nonterminal node with the given visitor.
    pub fn visit_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {{
        visitor.visit_{visit_name}(self)
    }}

""")

    traverse = "\n        ".join(traverse)
    traverse_mut = "\n        ".join(traverse_mut)

    fil.write(f"""\
    /// Visit the children of this nonterminal node with the given visitor.
    pub fn traverse<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {{
        {traverse}
        Ok(())
    }}

    /// Visit the children of this nonterminal node with the given visitor.
    pub fn traverse_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {{
        {traverse_mut}
        Ok(())
    }}
}}\n\n""")


def chumsky_define_token(fil, name, doc):
    if doc:
        for line in doc.split("\n"):
            fil.write(f"/// {line}\n")
    fil.write(f"""\
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Pt{name}<'i, S> {{
    pub data: Option<TokenData<'i, S>>,
}}

impl<'i, S: Default + Eq + std::hash::Hash> Pt{name}<'i, S> {{
    fn new(token: &'i types::TerminalToken<TokenType, S>, token_span: std::ops::Range<usize>) -> Self {{
        assert!(token.token_type() == TokenType::{name});
        Self {{
            data: Some(TokenData {{
                token,
                index: token_span.start
            }})
        }}
    }}

    /// Visit this terminal node with the given visitor.
    pub fn visit<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {{
        visitor.visit_{name}(self)
    }}

    /// Visit this terminal node with the given visitor.
    pub fn visit_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {{
        visitor.visit_{name}(self)
    }}
}}

""")


def rust_tuple(elements):
    if not elements:
        return "()"
    if len(elements) == 1:
        return f"({elements[0]},)"
    return f"({', '.join(elements)},)"


class AstAlternation:
    name_counter = 0

    def __init__(self, elements):
        super().__init__()
        self.elements = elements
        if len(self.elements) > 1:
            type(self).name_counter += 1
            self.rust_enum_name = f"UnnamedAlter{type(self).name_counter}"

    @classmethod
    def from_parse_tree(cls, node, case_convert):
        assert node.name == "Alternation"
        elements = [AstConcatenation.from_parse_tree(x, case_convert) for x in node.filter("Concatenation")]
        if len(elements) == 1:
            return elements[0]
        return cls(elements)

    def gather_implicit_tokens(self, case_convert):
        for element in self.elements:
            yield from element.gather_implicit_tokens(case_convert)

    def gather_used_tokens(self, case_convert):
        for element in self.elements:
            yield from element.gather_used_tokens(case_convert)

    def gather_used_fragments(self):
        for element in self.elements:
            yield from element.gather_used_fragments()

    def as_regex(self, rule_lookup, recursion):
        return "|".join((f"(?:{element.as_regex(rule_lookup, recursion)})" for element in self.elements))

    def as_parser(self, parser_lookup, case_convert):
        return ParserFactory().alter(*(element.as_parser(parser_lookup, case_convert) for element in self.elements))

    def as_chumsky(self, name_lookup, case_convert):
        if len(self.elements) > 1:
            return chumsky_construct(
                self.elements,
                name_lookup,
                case_convert,
                self.rust_enum_name,
                [f"Option{index+1}" for index in range(len(self.elements))]
            )

        return self.elements[0].as_chumsky(name_lookup, case_convert)

    def as_chumsky_type(self, name_lookup, case_convert):
        if len(self.elements) > 1:
            return self.rust_enum_name
        return self.elements[0].as_chumsky_type(name_lookup, case_convert)

    def as_chumsky_tuple_length(self):
        return 1

    def define_chumsky_types(self, fil, name_lookup, case_convert):
        if len(self.elements) > 1:
            return chumsky_define(
                fil,
                self.elements,
                name_lookup,
                case_convert,
                self.rust_enum_name,
                None,
                [f"Option{index+1}" for index in range(len(self.elements))],
                [None for _ in self.elements],
                None,
                None
            )
        for element in self.elements:
            element.define_chumsky_types(fil, name_lookup, case_convert)

    def generate_traverse(self, name_lookup, case_convert, var_names, mutable):
        assert len(var_names) == 1
        yield f"{var_names[0]}.traverse(visitor)"

    def last_terminal(self, name_lookup, case_convert):
        if not self.elements:
            return None
        last = self.elements[0].last_terminal(name_lookup, case_convert)
        for element in self.elements[1:]:
            last2 = element.last_terminal(name_lookup, case_convert)
            if last2 != last:
                last = None
        return last

    def __eq__(self, other):
        return type(self) == type(other) and self.elements == other.elements

    def __hash__(self):
        return hash((type(self), *self.elements))


class AstConcatenation:
    def __init__(self, elements):
        super().__init__()
        self.elements = elements

    @classmethod
    def from_parse_tree(cls, node, case_convert):
        assert node.name == "Concatenation"
        elements = [AstRepetition.from_parse_tree(x, case_convert) for x in node.filter("Repetition")]
        if len(elements) == 1:
            return elements[0]
        return cls(elements)

    def gather_implicit_tokens(self, case_convert):
        for element in self.elements:
            yield from element.gather_implicit_tokens(case_convert)

    def gather_used_tokens(self, case_convert):
        for element in self.elements:
            yield from element.gather_used_tokens(case_convert)

    def gather_used_fragments(self):
        for element in self.elements:
            yield from element.gather_used_fragments()

    def as_regex(self, rule_lookup, recursion):
        return "".join((f"(?:{element.as_regex(rule_lookup, recursion)})" for element in self.elements))

    def as_parser(self, parser_lookup, case_convert):
        return ParserFactory().concat(*(element.as_parser(parser_lookup, case_convert) for element in self.elements))

    def as_chumsky(self, name_lookup, case_convert):
        children = [child.as_chumsky(name_lookup, case_convert) for child in self.elements]
        result = [children[0]]
        if len(children) > 1:
            in_pattern = "x1"
            out_pattern = "x1"
            for index, child in enumerate(children[1:]):
                result.append(f".then({child})")
                in_pattern = f"({in_pattern}, x{index+2})"
                out_pattern = f"{out_pattern}, x{index+2}"
            result.append(f".map(|{in_pattern}| ({out_pattern})).boxed()")

            # TODO: if parenthesis-like:
            #   .recover_with(nested_delimiters(types::TerminalToken::new_pattern(TokenType::Lp), types::TerminalToken::new_pattern(TokenType::Rp), [], |_| Default::default()))

        return "".join(result)

    def as_chumsky_type(self, name_lookup, case_convert):
        children = (child.as_chumsky_type(name_lookup, case_convert) for child in self.elements)
        return "(" + ", ".join(children) + ")"

    def as_chumsky_tuple_length(self):
        return len(self.elements)

    def define_chumsky_types(self, fil, name_lookup, case_convert):
        for element in self.elements:
            element.define_chumsky_types(fil, name_lookup, case_convert)

    def generate_traverse(self, name_lookup, case_convert, var_names, mutable):
        assert len(var_names) == len(self.elements)
        for element, var_name in zip(self.elements, var_names):
            yield from element.generate_traverse(name_lookup, case_convert, [var_name], mutable)

    def last_terminal(self, name_lookup, case_convert):
        if not self.elements:
            return None
        return self.elements[-1].last_terminal(name_lookup, case_convert)

    def __eq__(self, other):
        return type(self) == type(other) and self.elements == other.elements

    def __hash__(self):
        return hash((type(self), *self.elements))


class AstRepetition:
    def __init__(self, child, mode):
        super().__init__()
        assert mode in "?*+"
        self.child = child
        self.mode = mode

    @classmethod
    def from_parse_tree(cls, node, case_convert):
        if node.name == "Repetition.One":
            mode = ""
        elif node.name == "Repetition.Maybe":
            mode = "?"
        elif node.name == "Repetition.Any":
            mode = "*"
        elif node.name == "Repetition.Many":
            mode = "+"
        else:
            assert False

        node = node.first("Singular")
        if node.name == "Singular.Nested":
            child = AstAlternation.from_parse_tree(node.first("Alternation"), case_convert)
        elif node.name == "Singular.Symbol":
            child = AstReference.from_parse_tree(node.first("Symbol"), case_convert)
        elif node.name in "Singular.StringLiteral":
            child = AstLiteral.from_parse_tree(node.first("StringLiteral"), case_convert)
        elif node.name == "Singular.CharacterSet":
            child = AstCharacterSet.from_parse_tree(node.first("CharacterSet"), case_convert)
        elif node.name in "Singular.CharacterLiteral":
            child = AstLiteral.from_parse_tree(node.first("CharacterLiteral"), case_convert)
        else:
            assert False

        if not mode:
            return child
        return cls(child, mode)

    def gather_implicit_tokens(self, case_convert):
        yield from self.child.gather_implicit_tokens(case_convert)

    def gather_used_tokens(self, case_convert):
        yield from self.child.gather_used_tokens(case_convert)

    def gather_used_fragments(self):
        yield from self.child.gather_used_fragments()

    def as_regex(self, rule_lookup, recursion):
        return f"(?:{self.child.as_regex(rule_lookup, recursion)}){self.mode}"

    def as_parser(self, parser_lookup, case_convert):
        if self.mode == "?":
            return ParserFactory().maybe(self.child.as_parser(parser_lookup, case_convert))
        elif self.mode == "*":
            return ParserFactory().any(self.child.as_parser(parser_lookup, case_convert))
        elif self.mode == "+":
            return ParserFactory().many(self.child.as_parser(parser_lookup, case_convert))
        assert False

    def as_chumsky(self, name_lookup, case_convert):
        child = self.child.as_chumsky(name_lookup, case_convert)
        if self.mode == "?":
            # https://github.com/zesterer/chumsky/issues/159
            #return f"{child}.or_not().boxed()"
            # Note: * and + are still too greedy!
            return f"{child}.map(Some).or(empty().map(|_| None)).boxed()"
        elif self.mode == "*":
            return f"{child}.repeated().boxed()"
        elif self.mode == "+":
            return f"{child}.repeated().at_least(1).boxed()"
        assert False

    def as_chumsky_type(self, name_lookup, case_convert):
        child = self.child.as_chumsky_type(name_lookup, case_convert)
        if self.mode == "?":
            return f"Option<{child}>"
        elif self.mode in "*+":
            return f"Vec<{child}>"
        assert False

    def as_chumsky_tuple_length(self):
        return 1

    def define_chumsky_types(self, fil, name_lookup, case_convert):
        self.child.define_chumsky_types(fil, name_lookup, case_convert)

    def generate_traverse(self, name_lookup, case_convert, var_names, mutable):
        assert len(var_names) == 1
        tup_len = self.child.as_chumsky_tuple_length()
        if tup_len == 1:
            tup = "x"
            child_var_names = ["x"]
        else:
            child_var_names = [f"x{i+1}" for i in range(tup_len)]
            tup = f"({', '.join(child_var_names)})"
        if self.mode == "?":
            if mutable:
                yield f"if let Some({tup}) = {var_names[0]}.as_mut() {{"
            else:
                yield f"if let Some({tup}) = {var_names[0]}.as_ref() {{"
        elif self.mode in "*+":
            if mutable:
                yield f"for {tup} in {var_names[0]}.iter_mut() {{"
            else:
                yield f"for {tup} in {var_names[0]}.iter() {{"
        else:
            assert False
        for line in self.child.generate_traverse(name_lookup, case_convert, child_var_names, mutable):
            yield f"    {line}"
        yield "}"

    def last_terminal(self, name_lookup, case_convert):
        if self.mode == "+":
            return self.child.last_terminal(name_lookup, case_convert)
        elif self.mode in "?*":
            return None
        assert False

    def __eq__(self, other):
        return type(self) == type(other) and self.child == other.child and self.mode == other.mode

    def __hash__(self):
        return hash((type(self), self.child, self.mode))


class AstLiteral:

    def __init__(self, s):
        super().__init__()
        self.s = s

    @staticmethod
    def _slugify(s):
        elements = []
        prev_is_literal = False
        for c in s:
            cp = ord(c)
            names = ["nul", "soh", "stx", "etx", "eot", "enq", "ack", "bel", "bs", "ht", "lf", "vt", "ff", "cr", "so", "si", "dle", "dc1", "dc2", "dc3", "dc4", "nak", "syn", "etb", "can", "em", "sub", "esc", "fs", "gs", "rs", "us", "sp", "ex", "dqt", "hsh", "dlr", "prc", "amp", "sqt", "lp", "rp", "ast", "pls", "com", "min", "prd", "sl", "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "col", "sem", "lt", "eq", "gt", "qst", "at", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "lsq", "bsl", "rsq", "crt", "usc", "bqt", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "lcr", "bar", "rcr", "tld", "del"]
            if cp < len(names):
                name = names[cp]
            else:
                name = f"u{cp:x}"
            is_literal = len(name) == 1
            if not elements or not is_literal or not prev_is_literal:
                elements.append(name)
            elif prev_is_literal:
                elements[-1] += name
            prev_is_literal = is_literal
        return "-".join(elements)

    @staticmethod
    def scan_char(s):
        if not s.startswith("#"):
            return s[:1], s[1:]
        c = s[1:2]
        s = s[2:]
        if c == "x":
            return chr(int(s[:2], 16)), s[2:]
        elif c == "u":
            return chr(int(s[:4], 16)), s[4:]
        elif c == "U":
            return chr(int(s[:8], 16)), s[8:]
        elif c == "t":
            return "\t", s
        elif c == "n":
            return "\n", s
        elif c == "r":
            return "\r", s
        return c, s

    @classmethod
    def _clean_char(cls, s):
        c, s = cls.scan_char(s)
        assert not s
        return c

    @classmethod
    def _clean_string(cls, s):
        assert s[0] in "'\""
        assert s[-1] in "'\""
        s = s[1:-1]
        cleaned = ""
        while s:
            c, s = cls.scan_char(s)
            cleaned += c
        return cleaned

    @classmethod
    def from_parse_tree(cls, node, case_convert=None):
        if node.name == "StringLiteral":
            return cls(cls._clean_string(node.data))
        elif node.name == "CharacterLiteral":
            return cls(cls._clean_char(node.data))
        else:
            assert False

    def as_symbol(self):
        return self._slugify(self.s)

    def gather_implicit_tokens(self, case_convert):
        yield (case_convert(self.as_symbol()), "Implicit token.", self)

    def gather_used_tokens(self, case_convert):
        yield case_convert(self.as_symbol())

    def gather_used_fragments(self):
        return []

    @staticmethod
    def escape_regex(s):
        escaped = ""
        for c in s:
            if c in ".+*?^$()[]{}|\\-":
                escaped += f"\\{c}"
            else:
                escaped += c
        return escaped

    @staticmethod
    def escape_rust(s):
        escaped = ""
        for c in s:
            if c in "\\\"":
                escaped += f"\\{c}"
            elif c == "\n":
                escaped += "\\n"
            elif c == "\r":
                escaped += "\\r"
            elif c == "\t":
                escaped += "\\t"
            else:
                escaped += c
        return escaped

    def as_regex(self, rule_lookup, recursion):
        return self.escape_regex(self.s)

    def as_parser(self, parser_lookup, case_convert):
        return ParserFactory().term(case_convert(self.as_symbol()))

    def as_chumsky(self, name_lookup, case_convert):
        return f"one_of(&types::TerminalToken::new_pattern(TokenType::{case_convert(self.as_symbol())})).map_with_span(Pt{case_convert(self.as_symbol())}::new).boxed()"

    def as_chumsky_type(self, name_lookup, case_convert):
        return f"Pt{case_convert(self.as_symbol())}<'i, S>"

    def as_chumsky_tuple_length(self):
        return 1

    def define_chumsky_types(self, fil, name_lookup, case_convert):
        pass

    def generate_traverse(self, name_lookup, case_convert, var_names, mutable):
        assert len(var_names) == 1
        yield f"visitor.visit_{case_convert(self.as_symbol())}({var_names[0]})?;"

    def last_terminal(self, name_lookup, case_convert):
        return case_convert(self.as_symbol())

    def __eq__(self, other):
        return type(self) == type(other) and self.s == other.s

    def __hash__(self):
        return hash((type(self), self.s))


class AstReference:

    def __init__(self, s):
        super().__init__()
        self.s = s

    @classmethod
    def from_parse_tree(cls, node, case_convert):
        assert node.name == "Symbol"
        return cls(case_convert(node.data))

    def gather_implicit_tokens(self, case_convert):
        return []

    def gather_used_tokens(self, case_convert):
        yield self.s

    def gather_used_fragments(self):
        yield self.s

    def as_regex(self, rule_lookup, recursion):
        if self.s in recursion:
            raise ValueError(f"recursive token rule: {recursion}")
        recursion = recursion + [self.s]
        rule = rule_lookup.get(self.s, None)
        if rule is None:
            raise ValueError(f"unknown token rule: {self.s}")
        return f"(?:{rule.as_regex(rule_lookup, recursion)})"

    def as_parser(self, parser_lookup, case_convert):
        if self.s in parser_lookup:
            return parser_lookup[self.s]
        else:
            return ParserFactory().term(self.s)

    def as_chumsky(self, name_lookup, case_convert):
        if self.s in name_lookup:
            return f"{name_lookup[self.s]}.clone().map(Box::new)"
        return f"one_of(&types::TerminalToken::new_pattern(TokenType::{self.s})).map_with_span(Pt{self.s}::new).boxed()"

    def as_chumsky_type(self, name_lookup, case_convert):
        if self.s in name_lookup:
            return f"Box<Pt{self.s}<'i, S>>"
        return f"Pt{self.s}<'i, S>"

    def as_chumsky_tuple_length(self):
        return 1

    def define_chumsky_types(self, fil, name_lookup, case_convert):
        pass

    def generate_traverse(self, name_lookup, case_convert, var_names, mutable):
        assert len(var_names) == 1
        if self.s not in name_lookup:
            yield f"visitor.visit_{self.s}({var_names[0]})?;"
        elif mutable:
            yield f"visitor.visit_{self.s}({var_names[0]}.as_mut())?;"
        else:
            yield f"visitor.visit_{self.s}({var_names[0]}.as_ref())?;"

    def last_terminal(self, name_lookup, case_convert):
        if self.s in name_lookup:
            # TODO: should maybe dereference the rule
            return None
        return self.s

    def __eq__(self, other):
        return type(self) == type(other) and self.s == other.s

    def __hash__(self):
        return hash((type(self), self.s))


class AstCharacterSet:

    def __init__(self, inverted, ranges):
        super().__init__()
        self.inverted = inverted
        self.ranges = ranges # [(from, to)]

    @classmethod
    def from_parse_tree(cls, node, case_convert):
        assert node.name == "CharacterSet"
        assert node.data.startswith("[")
        assert node.data.endswith("]")
        s = node.data[1:-1]
        if s.startswith("^"):
            inverted = True
            s = s[1:]
        else:
            inverted = False
        ranges = []
        while s:
            a, s = AstLiteral.scan_char(s)
            if s.startswith("-"):
                b, s = AstLiteral.scan_char(s[1:])
            else:
                b = a
            if ord(a) > ord(b):
                r = f"{a}-{b}"
                raise ValueError(f"invalid character range {r!r}")
            ranges.append((a, b))
        return cls(inverted, ranges)

    def gather_implicit_tokens(self, case_convert):
        raise ValueError("character sets are only allowed within the context of token rules")

    def gather_used_tokens(self, case_convert):
        raise ValueError("character sets are only allowed within the context of token rules")

    def gather_used_fragments(self):
        return []

    def as_regex(self, rule_lookup, recursion):
        body = ""
        for a, b in self.ranges:
            if a == b:
                body += AstLiteral.escape_regex(a)
            else:
                body += AstLiteral.escape_regex(a) + "-" + AstLiteral.escape_regex(b)
        if self.inverted:
            if body:
                return f"[^{body}]"
            else:
                return "."
        return f"[{body}]"

    def as_parser(self, parser_lookup, case_convert):
        raise ValueError("character sets are only allowed within the context of token rules")

    def as_chumsky(self, name_lookup, case_convert):
        raise ValueError("character sets are only allowed within the context of token rules")

    def as_chumsky_type(self, name_lookup, case_convert):
        raise ValueError("character sets are only allowed within the context of token rules")

    def as_chumsky_tuple_length(self):
        return 1

    def define_chumsky_types(self, fil, name_lookup, case_convert):
        pass

    def generate_traverse(self, name_lookup, case_convert, var_names, mutable):
        raise ValueError("character sets are only allowed within the context of token rules")

    def last_terminal(self, name_lookup, case_convert):
        return None

    def __eq__(self, other):
        return type(self) == type(other) and self.s == other.s

    def __hash__(self):
        return hash((type(self), self.inverted, *self.ranges))


if __name__ == "__main__":

    # Manually coded copy of the EBNF grammar.
    regexes = [
        ("ColEqEq", re.compile(r":==")),
        ("Sem", re.compile(r";")),
        ("Usc", re.compile(r"_")),
        ("Symbol", re.compile(r"[a-z][a-z0-9\-]*")),
        ("Bar", re.compile(r"\|")),
        ("ColColEq", re.compile(r"::=")),
        ("MinGt", re.compile(r"->")),
        ("Qst", re.compile(r"\?")),
        ("Ast", re.compile(r"\*")),
        ("Pls", re.compile(r"\+")),
        ("Lp", re.compile(r"\(")),
        ("Rp", re.compile(r"\)")),
        ("StringLiteral", re.compile(r"('([^'#]|#.)+'|\"([^\"#]|#.)+\")")),
        ("CharacterSet", re.compile(r"(\[\^?(([^\^\-\]#]|#([^xuU]|x[0-9a-fA-F][0-9a-fA-F]|u[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]|U[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]))(-([^\^\-\]#]|#([^xuU]|x[0-9a-fA-F][0-9a-fA-F]|u[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]|U[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))?)*\])")),
        ("CharacterLiteral", re.compile(r"(#([^xuU]|x[0-9a-fA-F][0-9a-fA-F]|u[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]|U[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]))")),
        ("Doc", re.compile(r"(/\*\*([^\*]|\*+[^\*/])*\**\*/)")),
        (None, re.compile(r"(/\*([^\*]|\*+[^\*/])*\**\*/|[ \t\n\r]+)")),
    ]

    r_grammar = Parser("Grammar")
    r_rule = Parser("Rule")
    r_alternation = Parser("Alternation")
    r_first_alter = Parser("FirstAlter")
    r_subseq_alter = Parser("SubseqAlter")
    r_alter_name = Parser("AlterName")
    r_concatenation = Parser("Concatenation")
    r_repetition = Parser("Repetition")
    r_singular = Parser("Singular")

    pf = ParserFactory()

    r_grammar.define_one(pf.many(r_rule))
    r_rule.define_opt(
        "TokenRule",
        pf.maybe(pf.term("Doc")),
        pf.term("Symbol"),
        pf.term("ColEqEq"),
        r_alternation,
        pf.term("Sem"),
    )
    r_rule.define_opt(
        "WhitespaceRule",
        pf.maybe(pf.term("Doc")),
        pf.term("Usc"),
        pf.term("ColEqEq"),
        r_alternation,
        pf.term("Sem"),
    )
    r_rule.define_opt(
        "GrammarRule",
        pf.maybe(pf.term("Doc")),
        pf.term("Symbol"),
        r_first_alter,
        pf.any(r_subseq_alter),
        pf.term("Sem"),
    )
    r_alternation.define_one(
        r_concatenation,
        pf.any(pf.concat(pf.term("Bar"), r_concatenation))
    )
    r_first_alter.define_one(
        pf.maybe(pf.term("Doc")),
        pf.term("ColColEq"),
        r_concatenation,
        pf.maybe(r_alter_name),
    )
    r_subseq_alter.define_one(
        pf.maybe(pf.term("Doc")),
        pf.term("Bar"),
        r_concatenation,
        pf.maybe(r_alter_name),
    )
    r_alter_name.define_one(pf.term("MinGt"), pf.term("Symbol"))
    r_concatenation.define_one(pf.many(r_repetition))
    r_repetition.define_opt("Maybe", r_singular, pf.term("Qst"))
    r_repetition.define_opt("Any", r_singular, pf.term("Ast"))
    r_repetition.define_opt("Many", r_singular, pf.term("Pls"))
    r_repetition.define_opt("One", r_singular)
    r_singular.define_opt("Nested", pf.term("Lp"), r_alternation, pf.term("Rp"))
    r_singular.define_opt("Symbol", pf.term("Symbol"))
    r_singular.define_opt("StringLiteral", pf.term("StringLiteral"))
    r_singular.define_opt("CharacterSet", pf.term("CharacterSet"))
    r_singular.define_opt("CharacterLiteral", pf.term("CharacterLiteral"))

    # Parse the self-specification.
    with open("self-spec.ebnf", "r", encoding="utf-8") as fil:
        tokens = list(tokenize(regexes, fil.read()))
    parse_tree = r_grammar.parse(tokens)

    # Analyze the self-specification.
    def case_convert(x):
        #return tuple(x.split("-"))
        return "".join(map(str.title, x.split("-")))
    grammar = AstGrammar(parse_tree, case_convert)

    # Parse the self-specification with the grammar we just constructed from
    # it.
    with open("simple.ebnf", "r", encoding="utf-8") as fil:
        tokens2 = list(grammar.tokenize(fil.read()))
    parse_tree2 = grammar.parse(tokens2)

    # Assert that both result in exactly the same thing.
    #assert tokens == tokens2
    #assert parse_tree == parse_tree2
    grammar = AstGrammar(parse_tree2, case_convert)

    # Now convert to Rust/chumsky as a basis for something more sane than this
    # abominatation of a Python script.
    with open("../src/test.rs", "w", encoding="utf-8") as fil:
        fil.write(r"""
// SPDX-License-Identifier: Apache-2.0

use super::prelude::*;

mod types {

    /// Trait for things that have a span.
    pub trait Spanned {
        type Span;

        fn span(&self) -> &Self::Span;
    }

    //=============================================================================

    /// Trait for the types of tokens within a language.
    pub trait TokenType: Copy + Eq + std::hash::Hash + std::fmt::Debug + std::fmt::Display {
        /// Array-like type returned by all().
        type All: IntoIterator<Item = Self>;

        /// Returns an iterator that iterates over all tokens, in the order in
        /// which they should be matched by the tokenizer.
        fn all() -> Self::All;

        /// Returns the regex for this token type.
        fn regex(&self) -> &'static str;

        /// Returns the regex for matching whitespace between the real tokens.
        fn whitespace() -> &'static str;
    }

    //=============================================================================

    /// Token classification.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum TokenClass<T> {
        /// Used for normal tokens, that the parser should consume.
        Normal(T),

        /// Used for the whitespace between normal tokens.
        Whitespace,

        /// Used to recover from errors; matches any single character when nothing
        /// else matches.
        Error,
    }

    impl<T: TokenType> TokenClass<T> {
        /// Returns the embedded token type if there is one.
        fn token_type(&self) -> Option<T> {
            if let Self::Normal(token_type) = self {
                Some(*token_type)
            } else {
                None
            }
        }

        /// Returns whether this is an error token.
        fn is_error(&self) -> bool {
            matches!(self, Self::Error)
        }

        /// Returns whether this is a whitespace token.
        fn is_whitespace(&self) -> bool {
            matches!(self, Self::Whitespace)
        }
    }

    impl<T: TokenType> std::fmt::Display for TokenClass<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                TokenClass::Normal(token_type) => std::fmt::Display::fmt(token_type, f),
                TokenClass::Whitespace => write!(f, "whitespace"),
                TokenClass::Error => write!(f, "error"),
            }
        }
    }

    //=============================================================================

    /// Tokens as emitted by the tokenizer. This includes errors and whitespace
    /// in addition to regular terminals in the grammar.
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub struct Token<'a, T, L>
    where
        L: crate::location::Tracker<&'a str>,
    {
        class: TokenClass<T>,
        text: &'a str,
        span: L::Span,
    }

    impl<'a, T, L> Token<'a, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<&'a str>,
    {
        /// Creates a new token.
        pub fn new(class: TokenClass<T>, text: &'a str, span: L::Span) -> Self {
            Self { class, text, span }
        }

        /// Converts self to a [TerminalToken] if it is a normal token. Otherwise
        /// returns Err(self).
        pub fn to_grammar_input(self) -> Result<TerminalToken<T, L::Span>, Self> {
            if let Some(token_type) = self.class.token_type() {
                Ok(TerminalToken::new(token_type, self.text, self.span))
            } else {
                Err(self)
            }
        }

        /// Converts self to a [TokenizerError] if it is an error marker. Otherwise
        /// returns Err(self).
        pub fn to_error(self) -> Result<TokenizerError<L::Span>, Self> {
            if self.class.is_error() {
                Ok(TokenizerError::new(
                    self.text.chars().next().unwrap_or('?'),
                    self.span,
                ))
            } else {
                Err(self)
            }
        }

        /// Returns the class of this token.
        pub fn class(&self) -> TokenClass<T> {
            self.class
        }

        /// Returns the text encompassed by the token.
        pub fn text(&self) -> &'a str {
            self.text
        }
    }

    impl<'a, T, L> std::fmt::Display for Token<'a, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<&'a str>,
        L::Span: std::fmt::Display,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{} ({:?} at {})", self.class, self.text, self.span)
        }
    }

    impl<'a, T, L> Spanned for Token<'a, T, L>
    where
        L: crate::location::Tracker<&'a str>,
    {
        type Span = L::Span;

        fn span(&self) -> &Self::Span {
            &self.span
        }
    }

    //=============================================================================

    /// Error type used for a failure to tokenize.
    #[derive(Clone, Debug)]
    pub struct TokenizerError<S> {
        invalid_char: char,
        location: S,
    }

    impl<S: std::fmt::Display> std::fmt::Display for TokenizerError<S> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "failed to match character {:?} as the start of a token at {}",
                self.invalid_char, self.location
            )
        }
    }

    impl<S> TokenizerError<S> {
        pub fn new(invalid_char: char, location: S) -> Self {
            Self {
                invalid_char,
                location,
            }
        }
    }

    //=============================================================================

    pub struct Tokenizer<'s, T, L = crate::location::Simple> {
        regexes: Vec<(regex::Regex, TokenClass<T>)>,
        location: L,
        index: usize,
        remain: &'s str,
    }

    impl<'s, T, L> Tokenizer<'s, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<&'s str>,
    {
        /// Creates a tokenizer for a piece of text with the given initial location
        /// for spans.
        pub fn new_with_location(location: L, text: &'s str) -> Self {
            let mut regexes: Vec<_> = T::all()
                .into_iter()
                .map(|x| {
                    (
                        regex::Regex::new(&format!("^(?:{})", x.regex())).unwrap(),
                        TokenClass::Normal(x),
                    )
                })
                .collect();
            regexes.push((
                regex::Regex::new(&format!("^(?:{})", T::whitespace())).unwrap(),
                TokenClass::Whitespace,
            ));
            Self {
                regexes,
                location,
                index: 0,
                remain: text,
            }
        }

        /// Creates a tokenizer for a piece of text, using L::default() for the
        /// initial location.
        pub fn new(text: &'s str) -> Self
        where
            L: Default,
        {
            Self::new_with_location(L::default(), text)
        }
    }

    impl<'s, T, L> Iterator for Tokenizer<'s, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<&'s str>,
    {
        type Item = Token<'s, T, L>;

        fn next(&mut self) -> Option<Self::Item> {
            // Stop when we reach EOF.
            if self.remain.is_empty() {
                return None;
            }

            // Look for the first longest match.
            let mut token_type = TokenClass::Error;
            let mut length = 0;
            for (regex, candidate_token_type) in self.regexes.iter() {
                let candidate_length = regex
                    .captures(self.remain)
                    .and_then(|x| x.get(0))
                    .map(|x| x.as_str().len())
                    .unwrap_or_default();
                if candidate_length > length {
                    token_type = *candidate_token_type;
                    length = candidate_length;
                }
            }

            // Advance by at least one character, even if nothing matched, in
            // an attempt to recover from errors.
            if length == 0 {
                length = 1;
            }

            // Generate the token and seek past it.
            let text = &self.remain[..length];
            self.remain = &self.remain[length..];
            let start_location = self.location.clone();
            let start_index = self.index;
            self.location.advance(&text);
            self.index += 1;
            let span = start_location.spanning_to(start_index, &self.location, self.index);
            let token = Token::new(token_type, text, span);

            Some(token)
        }
    }

    //=============================================================================

    /// Token type used as terminals at the input of the grammar. This type is a
    /// bit derpy to make Chumsky work right: two terminal tokens are equal iff
    /// they have the same type, with no bearing on the text or span. The text or
    /// span are treated as optional annotations, used only to aid in the
    /// construction of error messages.
    #[derive(Clone, Debug, Eq, Hash)]
    pub struct TerminalToken<T: TokenType, S> {
        token_type: T,
        text: Option<String>,
        span: S,
    }

    impl<T: TokenType, S> PartialEq for TerminalToken<T, S> {
        fn eq(&self, other: &Self) -> bool {
            self.token_type == other.token_type
        }
    }

    impl<T: TokenType, S> TerminalToken<T, S> {
        /// Creates a new terminal node.
        pub fn new<R: ToString>(token_type: T, text: R, span: S) -> Self {
            Self {
                token_type,
                text: Some(text.to_string()),
                span,
            }
        }

        /// Creates a new "pattern" node, only used for error messages and to
        /// compare against.
        pub fn new_pattern(token_type: T) -> Self
        where
            S: Default,
        {
            Self {
                token_type,
                text: None,
                span: S::default(),
            }
        }

        /// Returns the token type.
        pub fn token_type(&self) -> T {
            self.token_type
        }

        /// Returns the text enclosed by the token.
        pub fn text(&self) -> &str {
            self.text.as_ref().map(|x| &x[..]).unwrap_or("")
        }

        /// Unwraps the contents into a tuple.
        pub fn unwrap(self) -> (T, Option<String>, S) {
            (self.token_type, self.text, self.span)
        }
    }

    impl<T: TokenType, S: std::fmt::Display> std::fmt::Display for TerminalToken<T, S> {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            if let Some(text) = &self.text {
                write!(f, "{} ({:?}) at {}", self.token_type, text, self.span)
            } else {
                write!(f, "{}", self.token_type)
            }
        }
    }

    impl<T: TokenType, S> Spanned for TerminalToken<T, S> {
        type Span = S;

        fn span(&self) -> &S {
            &self.span
        }
    }

    //=============================================================================

    // Error type used for both parsing and tokenization.
    #[derive(Clone, Debug)]
    pub enum Error<'i, L>
    where
        L: crate::location::Tracker<&'i str>,
        L::Location: Clone + std::fmt::Debug + std::fmt::Display,
        L::Span: Clone + std::fmt::Debug + std::fmt::Display,
    {
        TokenizerError(TokenizerError<L::Location>),
        ParserError(crate::error::Simple<&'i str, L>),
    }

    impl<'i, L> std::fmt::Display for Error<'i, L>
    where
        L: crate::location::Tracker<&'i str>,
        L::Location: Clone + std::fmt::Debug + std::fmt::Display,
        L::Span: Clone + std::fmt::Debug + std::fmt::Display,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Error::TokenizerError(e) => write!(f, "{e}"),
                Error::ParserError(e) => write!(f, "{e}"),
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TokenType {
""")

        first = True
        regexes = []
        for name in grammar.token_order:
            if name == "_":
                continue
            if first:
                first = False
            else:
                fil.write("\n")
            doc = grammar.token_rules[name][0]
            if doc:
                for line in doc.split("\n"):
                    fil.write(f"    /// {line}\n")
            fil.write(f"    {name},\n")
            regexes.append((
                name,
                AstLiteral.escape_rust(grammar.token_regexes[name].pattern)
            ))

        whitespace_regex = grammar.token_regexes.get("_", None)
        if whitespace_regex is not None:
            whitespace_regex = AstLiteral.escape_rust(whitespace_regex.pattern)
        else:
            whitespace_regex = ""


        fil.write(f"""\
}}

impl types::TokenType for TokenType {{
    type All = [TokenType; {len(regexes)}];

    fn all() -> Self::All {{
        [
""")
        for name, _ in regexes:
            fil.write(f"            Self::{name},\n")

        fil.write("""\
        ]
    }

    fn regex(&self) -> &'static str {
        match self {
""")
        for name, regex in regexes:
            fil.write(f"            Self::{name} => \"{regex}\",\n")

        fil.write(f"""\
        }}
    }}

    fn whitespace() -> &'static str {{
        "{whitespace_regex}"
    }}
}}

impl std::fmt::Display for TokenType {{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {{
        write!(f, "{{:?}}", self)
    }}
}}

/// Tokenizes a piece of text.
pub fn tokenize<'s>(text: &'s str) -> types::Tokenizer<'s, TokenType> {{
    types::Tokenizer::new(text)
}}

/// Tokenizes a piece of text starting from the given source location.
pub fn tokenize_from<'s, L: crate::location::Tracker<&'s str>>(
    location: L,
    text: &'s str,
) -> types::Tokenizer<'s, TokenType, L> {{
    types::Tokenizer::new_with_location(location, text)
}}

/// Helper type for a boxed parser.
pub type BoxedParser<'i, T, S> = crate::combinator::Boxed<
    'i,
    &'i types::TerminalToken<TokenType, S>,
    T
>;

/// Helper type for the contents of a token.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TokenData<'i, S> {{
    pub token: &'i types::TerminalToken<TokenType, S>,
    pub index: usize,
}}

""")

        for name, (doc, _) in grammar.token_rules.items():
            if name != "_":
                chumsky_define_token(fil, name, doc)

        name_lookup = {name: f"parse_{name}" for name in grammar.grammar_rules}
        rule_order = []
        for index, (name, (doc, alters)) in enumerate(grammar.grammar_rules.items()):
            variant_names, variant_docs, elements = zip(*alters)
            if len(alters) == 1:
                variant_names = None
            chumsky_define(
                fil,
                elements,
                name_lookup,
                case_convert,
                f"Pt{name}",
                doc,
                variant_names,
                variant_docs,
                index,
                name
            )
            for element in elements:
                element.define_chumsky_types(fil, name_lookup, case_convert)
            rule_order.append(name)

        decls = []
        defs = []
        return_expr = []
        return_type = []
        for rule_name in rule_order:
            var_name = name_lookup[rule_name]
            alters = grammar.grammar_rules[rule_name][1]
            variant_names, variant_docs, elements = zip(*alters)
            if len(alters) == 1:
                variant_names = None
            chumsky = chumsky_construct(elements, name_lookup, case_convert, f"Pt{rule_name}", variant_names)
            decls.append(f"let mut {var_name} = Recursive::declare();")
            defs.append(f"{var_name}.define({chumsky});")
            return_expr.append(f"{var_name}.then_ignore(end()).boxed()")
            return_type.append(f"BoxedParser<'i, Pt{rule_name}<'i, S>, S>")
        decls = "\n    ".join(decls)
        defs = "\n\n    ".join(defs)
        return_expr = rust_tuple(return_expr)
        return_type = rust_tuple(return_type)

        fil.write(f"""\
/// Constructs Chumsky parsers for all the grammar rules.
#[allow(non_snake_case)]
fn make_parsers<'i, S: Default + Eq + std::hash::Hash>() -> {return_type} {{
    {decls}

    {defs}

    {return_expr}
}}
""")

        visit = []
        for name in grammar.token_rules:
            if name != "_":
                visit.append((name, True))
        for name in rule_order:
            visit.append((name, False))

        fil.write(f"""\

/// Visitor trait for immutably walking the parse tree.
pub trait Visitor<'i, S, E = ()>
where
    Self: Sized,
    S: Default + Eq + std::hash::Hash,
{{
""")

        first = True
        for name, terminal in visit:
            if first:
                first = False
            else:
                fil.write("\n")
            fil.write("    #[allow(non_snake_case)]\n")
            fil.write(f"    fn visit_{name}(&mut self, {'_' if terminal else ''}x: &Pt{name}<'i, S>) -> Result<(), E> {{\n")
            if not terminal:
                fil.write("        x.traverse(self)\n")
            else:
                fil.write("        Ok(())\n")
            fil.write("    }\n")

        fil.write(f"""\
}}

/// Visitor trait for mutably walking the parse tree.
pub trait VisitorMut<'i, S, E = ()>
where
    Self: Sized,
    S: Default + Eq + std::hash::Hash,
{{
""")

        first = True
        for name, terminal in visit:
            if first:
                first = False
            else:
                fil.write("\n")
            fil.write("    #[allow(non_snake_case)]\n")
            fil.write(f"    fn visit_{name}(&mut self, {'_' if terminal else ''}x: &mut Pt{name}<'i, S>) -> Result<(), E> {{\n")
            if not terminal:
                fil.write("        x.traverse_mut(self)\n")
            else:
                fil.write("        Ok(())\n")
            fil.write("    }\n")

        fil.write("""\
}
""")


    subprocess.check_call(["rustfmt", "../src/test.rs"])

    #let mut parse_Grammar = Recursive::declare();

    #parse_Grammar.define(just(types::TerminalToken::new_pattern(TokenType::MinGt)).map(|_| PtGrammar(vec![])));

    #(Box::new(parse_Grammar), )
