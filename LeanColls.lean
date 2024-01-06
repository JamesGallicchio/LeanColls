/-
Copyright (c) 2023 James Gallicchio.
-/

import LeanColls.Classes.Bag
import LeanColls.Classes.Indexed
import LeanColls.Classes.IndexType
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

Generic collections implemented in pure Lean 4.

`LeanColls` attempts to make programming and proving
with collections a fun and straightforward experience.
To that end, the library contains:
 1. Comprehensive and consistent interfaces for common collection operations.
 2. Comprehensive and consistent lawfulness specifications for implementations.
 3. Efficient implementations of common collections for all major use cases.
 4. Utilities for writing clean, efficient, and provably correct code
    that utilizes collections.

which is quite a lot!

Here is a quick summary of important modules to look at:
 - [LeanColls.Classes.Ops] contains typeclasses for individual operations.

More thorough documentation is WIP.
Contributions are welcome and appreciated;
see the [Github](https://github.com/JamesGallicchio/LeanColls).
-/
