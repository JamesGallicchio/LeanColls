
class MemoStream (ρ) (τ) where
  next? : ρ → (Option (τ × ρ))

partial def fib : Nat → Thunk Stream Unit Nat
| 0 => Thunk (Stream.empty)