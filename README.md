# Lean Collections Library

General-purpose collections library implemented in pure Lean 4.

Collection interfaces and utilities have grown independently in many Lean projects.
This library is an attempt to unify and extend those interfaces/utilities.

Includes:
- Consistent interfaces for collections, to abstract from an implementation
- Thorough body of lemmas for all collections (via the consistent interfaces)
- Utilities to write clean (i.e. proof-friendly) code, without sacrificing performance

### Usage

Add the following to your `lakefile.lean`:
```
require leancolls from git
  "https://github.com/JamesGallicchio/LeanColls" @ "main"
```

#### Branches & Releases

- branch `main`: stays on latest stable version of the compiler,
which also pins us to the corresponding stable mathlib release.
- branch `mathlib-nightly`: automatically updated every night
for anyone who needs a more up to date mathlib/compiler.
- tag `v4.*.0`: the first commit which compiles on `v4.*.0`

Please open an issue if none of these cover your particular use case!

#### Docs

[The latest documentation is available here](https://jamesgallicchio.github.io/LeanColls/docs/).

### Design

See [notes.md](notes.md) for design philosophy and inspiration sources.

### Contributing

Issues and PRs are welcome. You can also DM me on the
[Lean community Zulip](https://leanprover.zulipchat.com/)
as James Gallicchio.

Shoutout to @lecopivo and @T-Brick for helping to maintain
and expand the library in its early stages :-)
