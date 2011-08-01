" Vim syntax file
" Language:   Decades
" Filenames:  *.ept *.epi
" Last Changed: 18 Apr 2011 01:35:13 PM


" exit if already loaded
if exists("b:current_syntax") && b:current_syntax == "decades"
  finish
endif

" case sensitive
syn case match


" Errors
syn match    decadesBraceErr     "}"
syn match    decadesBrackErr     "\]"
syn match    decadesParenErr     ")"

syn match    decadesCommentErr   "\*)"

syn match    decadesThenErr      "\<then\>"
syn match    decadesContinueErr  "\<continue\>"
syn match    decadesUntilErr     "\<until\>"
syn match    decadesUnlessErr    "\<unless\>"

syn match    decadesReturnsErr   "\<returns\>"
syn match    decadesTelErr       "\<tel\>"

syn match    decadesEndErr       "\<end\>"


" Some convenient cluster
syn cluster  decadesStateErrs contains=decadesThenErr,decadesContinueErr,decadesUntilErr,decadesUnlessErr

" Enclosing delimiters
syn region   decadesNone matchgroup=decadesEncl start="(" matchgroup=decadesEncl end=")" contains=ALLBUT,decadesParenErr
syn region   decadesNone matchgroup=decadesEncl start="{" matchgroup=decadesEncl end="}"  contains=ALLBUT,decadesBraceErr
syn region   decadesNone matchgroup=decadesEncl start="\[" matchgroup=decadesEncl end="\]" contains=ALLBUT,decadesBrackErr


" Comments
syn region   decadesComment start="(\*" end="\*)" contains=decadesComment,decadesTodo
syn keyword  decadesTodo contained TODO FIXME XXX NOTE


" Functions (let part)
syn region   decadesNone matchgroup=decadesType start="\<\(fun\|node\)\>" matchgroup=decadesKeyword end="\<returns\>" contains=ALLBUT,decadesReturnsErr
syn region   decadesNone matchgroup=decadesLet start="\<let\>" matchgroup=decadesLet end="\<tel\>" contains=ALLBUT,@decadesContained,decadesTelErr


" Automaton
syn region   decadesNone matchgroup=decadesAutomaton start="\<automaton\>" matchgroup=decadesAutomaton end="\<end\>" contains=ALLBUT,decadesEndErr
syn region   decadesNone matchgroup=decadesUntilUnless start="\<\(until\|unless\)\>" matchgroup=decadesUntilUnless end="\<\(then\|continue\)\>" contains=ALLBUT,@decadesStateErrs

" Reset
syn region   decadesNone matchgroup=decadesReset start="\<reset\>" matchgroup=decadesReset end="\<every\>" contains=ALL


" Keywords
syn keyword  decadesKeyword      do
syn keyword  decadesKeyword      at

syn keyword  decadesStatement    open
syn keyword  decadesStatement    val
syn keyword  decadesStatement    var

syn keyword  decadesConditional  if then else

syn keyword  decadesFunction     fby pre
syn keyword  decadesFunction     map fold merge split
syn keyword  decadesFunction     mapi foldi
syn keyword  decadesFunction     init
syn keyword  decadesFunction     last

syn keyword  decadesBoolean      true false

syn keyword  decadesType         int float bool

syn keyword  decadesKeyword      const type

syn keyword  decadesInclude      state

syn match    decadesFunction     '->'

syn match    decadesNumber       "-\=\<\d\+\>"
syn match    decadesFloat        "-\=\<\d\+\.\d\+\>"
syn match    decadesFloat        "-\=\<\d\+\.\d\+[eE]-\=\d\+\>"



" Synchronization
syn sync minlines=50
syn sync maxlines=500
 

" Define the default highlighting
command -nargs=+ HiLink hi def link <args>

HiLink decadesLet          Include
HiLink decadesAutomaton    Include
HiLink decadesEncl         Include
HiLink decadesInclude      Include

HiLink decadesUntilUnless  Keyword
HiLink decadesKeyword      Keyword
HiLink decadesReset        Keyword

HiLink decadesConditional  Conditional

HiLink decadesFunction     Function

HiLink decadesStatement    Statement

HiLink decadesBoolean      Boolean

HiLink decadesType         Type

HiLink decadesConstructor  Constant

HiLink decadesNumber       Number

HiLink decadesFloat        Float

HiLink decadesTodo         Todo

HiLink decadesComment      Comment

delcommand HiLink

let b:current_syntax = "decades"
