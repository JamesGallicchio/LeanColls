
Interface Design
---

1. **Good defaults are important.** Maybe can use/abuse the Inhabited typeclass to provide default implementations of interfaces?

2. **Generic implementations are helpful.** An implementation of a subset of an interface can often be given default implementations for the rest of the interface.
  - Could use typeclass resolution to pick among implementations (with higher priority for non-default implementations), but this seems like a recipe for code obfuscation (see [3])
  - 

3. **Performance-altering decisions should be explicit.** If a choice affects performance, it should have to be made explicit in user code. Even with defaults, one should explicitly specify that one wants a default implementation with no performance guarantees, rather than leave it unspecified. This way, it is obvious to users how to go about improving performance of performance-sensitive code.


Cost tracking
---

It would be cool to implement Calf to automatically track the cost of different operations at the type level, but this would need linear types which idk how to embed in Lean.
