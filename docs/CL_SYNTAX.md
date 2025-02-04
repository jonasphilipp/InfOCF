# Using `.cl`-files to encode belief bases

## Belief bases in `.cl`-format:

Belief bases can be read from `.cl`-files by adhering to the following format:
```
signature
  <signature elements separated by ','>
conditionals
<belief base name>{
<list of conditionals separated by ','>
}
```
A conditional is of the form `(B|A)` where `A` and `B` are propositional formulas. 
A propositional formula is made up of variables and the connectors `!` (Negation), `,` (Conjunction) and `;` (Disjunction).
Variables are strings only containing letters (upper- and lower-case allowed).

For ease of reading and expressivity, a formula may be in parentheses `(...)`.
If no parentheses is used the precedence is as follows:
1. `!` (Negation)
2. `,` (Conjunction)
3. `;` (Disjunction)

Comments are also allowed in the file, following the Java comment syntax, i.e. `//` introduces single-line comments and `/*...*/` introduces block comments.

The detailles of the grammar can be checked at the [CLKR-repository](https://www.fernuni-hagen.de/wbs/clkr/html/syntax.html). 

### Example belief base
```
signature
   b, p, f, w

conditionals
birds005{
   (f | b),
   (!f | p),
   (b | p),
   (w | b)
}
```

## Conditionals in `.clq`-format:
The `.clq`-format is used for query files containing conditionals over a signature of a knowledge base.
Each `.clq`-file contains a list of conditionals using the same syntax as for `.cl`-files.
A knowledge base file together with a corresponding query file
`<kb-file>.cl` , `<query-file>.clq`
constitute a problem set. 

### Example queries
```
(f|p),
(w|p)
```

