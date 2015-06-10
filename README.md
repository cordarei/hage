# Hage

    名状しがたいハゲのような何か

**Author:** Joseph Irwin

## How to Install

Don't.

## How to Use

Don't.

## Design

The Penn Treebank annotates sentences from the Wall Street Journal (from 1983)
with part-of-speech tags and context-free syntactic structure (trees). The trees
in the PTB look like:

    (S (NP (NNP John))
       (VP (VBZ loves)
           (NP (NNP Mary)))
       (. .))

This format is basically Lisp S-Expressions, but with no datatypes (the only
elements are phrase labels, POS tags or words without spaces) and thus no
delimiters other than whitespace and parentheses. Its super easy to parse,
you can even use a regex to wrap quotes around the elements and `read` it in
any Lisp or Scheme.

After parsing (or `read`ing), the tree looks like this:

    '("S"
       ("NP" ("NNP" "John"))
       ("VP" ("VBZ" "loves") ("NP" ("NNP" "Mary")))
       ("." "."))

If this is named `tree`, `(car tree)` will return `"S"` and `(cdr tree)` will result in:

    '(("NP" ("NNP" "John"))
      ("VP" ("VBZ" "loves") ("NP" ("NNP" "Mary")))
      ("." "."))

Some wrinkles:

- Trees are wrapped in an extra pair of parentheses, so instead of

    (S (NP ...)

we are faced with

    ((S (NP ...))

(In context-free parsing it's convenient to have a single unique label for the root node).

- There are a large number of phonetically empty elements added in the parse tree, marking
things like movement traces (if you believe in movement). They look like

    (-NONE- *1*)

- The NPs don't all look like `NP`; many of them look like `NP-SBJ`. Some constituent labels
have function tags added to indicate grammatical function, and numbers for coreference and
coordination. Other examples look like `S-TPC-1`, `ADVP-CLR`, `NP=2`, and `PP-LOC-PRD-TPC-3`.

### Labels

It's not impossible to work with the labels as strings, but it isn't very
convenient, so the `parse-label` function will parse a label string into a
`ptb/label` structure.

### Data type

The s-expression encoding of PTB trees is not easy to work with; everything is a string, the
list representation is slightly awkward, and there is no good way to annotate constituents with extra
information such as length or span etc. We define an improved representation for PTB trees.

## Copying

[![CC0](http://i.creativecommons.org/p/zero/1.0/88x31.png)](http://creativecommons.org/publicdomain/zero/1.0/)

To the extent possible under law, the author(s) have dedicated all copyright
and related and neighboring rights to this software to the public domain
worldwide. This software is distributed without any warranty.

You should have received a copy of the CC0 Public Domain Dedication along with
this software. If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
