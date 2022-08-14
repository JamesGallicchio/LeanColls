/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.FoldableOps

open LeanColls

namespace List

instance : FoldableOps (List τ) τ := default
