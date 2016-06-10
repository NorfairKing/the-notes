# Code conventions

The code is not always consistent with these conventions but any additions should be.

## Modules

`Macro.Chapter.Macro` is deprecated.

- 'text' goes into `Chapter.Section`.
  Text modules can import other Text modules, Macro's and Terms.
- Macro's go into `Chapter.Section.Macro`.
  Macro modules can only import other Macro modules
- Terms, references and labels go into `Chapter.Section.Terms`.
  Term modules cannot import modules other than Types.

## Imports

Modules should be imported in this order:

- Notes
- Any non-chapter modules
- Chapter modules
- The modules' terms and macros

## Terms

Term functions are generated with template haskell with `makeDefs`.

- `term` is the indexed version
- `term'` indexed and bold
- `termDefinitionLabel` label for the definition of the term
- `term_` indexed term with reference with a reference to the definition

Plural forms are also generated: `terms` and `terms'`.

## Top level function

Use the suffix
- S for sections
- SS for subsections
- SSS for subsubsections

## Variables

Make local variables if necessary.

- Use `x` for "x" and `xx` for "X" if both are required.

## Macro's

- A `_` suffix means 'a concrete example implementation'

  Example:
  `pointedSet :: Note -> Note -> Note` but `pointedSet_ :: Note`
