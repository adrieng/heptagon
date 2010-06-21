# -*- coding: utf-8 -*-
"""
A Pygments lexer for Heptagon
"""
from setuptools import setup

__author__ = 'Adrien Guatto'

setup(
    name='Heptagon-Pygments',
    version='1.0',
    description=__doc__,
    author=__author__,
    packages=['hept_pygments'],
    entry_points='''
    [pygments.lexers]
    Heptagon = hept_pygments:HeptagonLexer
    Obc = hept_pygments:ObcLexer
    VHDL = hept_pygments:VHDLLexer
    MiniLS = hept_pygments:MLSLexer
    '''
)
