This is an experiment to extract "blue boxes" from any Racket source
file (not just functions that have blue boxes available via installed
Scribble documentation).

Intended use: To use in racket-mode to support things like
company-mode, eldoc, and so on.

Tactic: Partially expand the file to certain forms, extract
information about function definitions, renamings, and contracts, and
add to a "database".

With this database, given a function name, we can look up information
about its definition signature and contract (if any), and display a
textual version of the Racket documentation's "blue box" summaries.
For example this could go in an Emacs `*company-doc*` buffer.

A one-line "blue line" variant is available (for when your next stop
is Wonderland, or, you want something more likely to fit in the status
bar for eldoc or company-mode).

The database can also be used to find the definition source location,
given a provided rename. (racket-mode already does this via
`identifier-binding` plus some dumpster-divign. However (1) this only
works for symbols in the evaluated namespace, and (2) it's a bit
slower than I'd like. Possibly: Analyzing whole files and caching the
result *might* provide a better experience than looking for functions
one-by-one. Perhaps a racket-mode thread can proactively do this "in
the background", so that the results are ready by the time someone is
interactively using eldoc, company-mode, or racket-visit-definition.)

Strong points:

- Does try to follow transitive renames (e.g. a function is defined,
  provided with a rename, and provided again with a contract, OR,
  `define/contract`ed then provided with a rename).

- Because it uses `local-expand`, it can detect functions defined via
  arbitrary "definer macros" that expand to forms like `define`,
  `define/contract`, `provide/contract`, &c.

Limitations:

- Doesn't (yet) look for Typed Racket types. (Although looking for `:`
  and `define:` forms _seems_ like it should be easy, I haven't tried
  it.)

- Only looks for functions. Doesn't (yet) look for syntax definitions,
  parameters, structs, etc. (This should AFIK be straightforward.)
