from pygments.lexer import RegexLexer
from pygments.token import *

class HeptagonLexer(RegexLexer):
    name = 'Heptagon'
    aliases = ['hept']
    filenames = ['*.ept']

    tokens = {
        'root': [
            (r'\(\*.*\*\)', Comment),
            (r'node|var', Keyword.Declaration),
            (r'open', Keyword.Namespace),
            (r'returns|let|tel|automaton|state|until|unless|if|then|else|end',
             Keyword),
            (r'reset|every', Keyword),
            (r'map|fold|mapfold', Keyword),
            (r'when|merge|fby|do', Keyword),
            (r'present', Keyword.Reserved),
            (r'int|bool', Keyword.Type),
            (r'pre|\-\>|\+|\-|\/|=|&|not|\*|<=|>=|\^', Operator),
            (r'\d+', Number.Integer),
            (r' |\t', Whitespace),
            (r'\(|\)|;|\||:|,|\]|\[|\.|<|>|<<|>>', Punctuation),
            (r'true|false', Literal),
            (r'[A-Z]\w*', String.Symbol),
            (r'\w+', Name)
        ]
    }


class MLSLexer(RegexLexer):
    name = 'MiniLS'
    aliases = ['mls']
    filenames = ['*.mls']

    tokens = {
        'root': [
            (r'\(\*.*\*\)', Comment),
            (r'node|var', Keyword.Declaration),
            (r'open', Keyword.Namespace),
            (r'returns|let|tel|if|then|else|end',
             Keyword),
            (r'map|fold|mapfold', Keyword),
            (r'when|merge|fby|do', Keyword),
            (r'present', Keyword.Reserved),
            (r'int|bool', Keyword.Type),
            (r'pre|\-\>|\+|\-|\/|=|&|not|\*|<=|>=|\^', Operator),
            (r'\d+', Number.Integer),
            (r' |\t', Whitespace),
            (r'\(|\)|;|\||:|,|\]|\[|\.|<<|>>', Punctuation),
            (r'true|false', Literal),
            (r'[A-Z]\w*', String.Symbol),
            (r'\w+', Name)
        ]
    }



class ObcLexer(RegexLexer):
    name = 'Obc'
    aliases = ['obc']
    filenames = ['*.obc']

    tokens = {
        'root': [
            (r'--.*\n', Comment),
            (r'machine|reset|step|var', Keyword.Declaration),
            (r'open', Keyword.Namespace),
            (r'switch|case|mem|returns', Keyword),
            (r'int|bool', Keyword.Type),
            (r'\+|\-|\/|=|&|not', Operator),
            (r'\d+', Number.Integer),
            (r' |\t', Whitespace),
            (r'\(|\)|;|\||:|\{|\}|,', Punctuation),
            (r'true|false', Literal),
            (r'[A-Z]\w*', String.Symbol),
            (r'\w+', Name)
        ]
    }

class VHDLLexer(RegexLexer):
    name = 'VHSIC Hardware Description Language'
    aliases = ['vhdl']
    filenames = ['*.vhd']

    tokens = {
        'root': [
            (r'--.*\n', Comment),
            (r'architecture|process|signal|entity|function',
              Keyword.Declaration),
            (r'library|use', Keyword.Namespace),
            (r'returns|begin|end|if|then|else|elsif|when|of', Keyword),
            (r'port|map|case|is|others', Keyword),
            (r'natural|bit|std_logic|integer', Keyword.Type),
            (r'\(|\)|;|\||:|\{|\}|,|\'|=>', Punctuation),
            (r'\+|\-|\/|=|&|not|<=|\.', Operator),
            (r'\d+', Number.Integer),
            (r' |\t', Whitespace),
            (r'\(|\)|;|\||:|\{|\}|,|\'', Punctuation),
            (r'true|false', Literal),
            (r'[A-Z]\w*', String.Symbol),
            (r'\w+', Name)
        ]
    }
