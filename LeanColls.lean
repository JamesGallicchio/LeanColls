/-
Copyright (c) 2023 James Gallicchio.
-/

import LeanColls.Classes.Bag
import LeanColls.Classes.Indexed.Basic
import LeanColls.Classes.Indexed.Notation
import LeanColls.Classes.IndexType.Basic
import LeanColls.Classes.IndexType.Instances
import LeanColls.Classes.Map
import LeanColls.Classes.Ops
import LeanColls.Classes.Seq
import LeanColls.Data.Transformer.FixSize
import LeanColls.Data.Transformer.Slice
import LeanColls.Data.Transformer.View
import LeanColls.Data.Array
import LeanColls.Data.AssocList
import LeanColls.Data.HashMap
import LeanColls.Data.List
import LeanColls.Data.Range
import LeanColls.Data.RBMap
import LeanColls.Util.Cached

/-!
# Lean Collections Library

General-purpose collections implemented in pure Lean 4.

`LeanColls` attempts to make programming and proving
with collections a fun and straightforward experience.
To that end, the library contains:
 1. Comprehensive interfaces for common collection operations.
 2. Lawfulness specifications for those interfaces.
 3. Performant & proven-correct implementations.
 4. Utilities for writing clean, efficient, and provably correct
    code with collections.

which is quite a lot!

More thorough documentation is WIP.
Contributions are welcome and appreciated;
see the [GitHub repository](https://github.com/JamesGallicchio/LeanColls).
-/
