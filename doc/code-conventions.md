# Code conventions

## Modules

`Macro.Chapter.Macro` is deprecated.


- 'text' goes into `Chapter.Section`.
- Macro's go into `Chapter.Section.Macro`.
- Terms go into `Chapter.Section.Terms`.

## Terms

- `term` is the indexed version
- `term'` indexed and bold
- `termDefinitionLabel` label for the definition of the term
- `term_` indexed term with reference with a reference to the definition

## Variables
Make local variables if necessary

- Use `x` for "x" and `xx` for "X" if both are required.

## Macro's

- A `_` suffix means 'a concrete example implementation'

  Example:
  `pointedSet :: Note -> Note -> Note` but `pointedSet_ :: Note`
