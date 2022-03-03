
Interface Design Principles
---

1. **Good defaults are important.** Maybe can use/abuse the Inhabited typeclass to provide default implementations of interfaces?

2. **Generic implementations are helpful.** An implementation of a subset of an interface can often be given default implementations for the rest of the interface.
  - Could use typeclass resolution to pick among implementations (with higher priority for non-default implementations), but this seems like a recipe for code obfuscation (see [3])
  - 

3. **Performance-altering decisions should be explicit.** If a choice affects performance, it should have to be made explicit in user code. Even with defaults, one should explicitly specify that one wants a default implementation with no performance guarantees, rather than leave it unspecified. This way, it is obvious to users how to go about improving performance of performance-sensitive code.


Comparison to Other Collections Libraries
---

For proof assistant languages:

1. [**Agda Standard Library**](https://github.com/agda/agda-stdlib/tree/master/src/Data/Container). Very .. category theory. Some explanation here [here](https://github.com/agda/agda-stdlib/blob/master/README/Data.agda). Some generalization across container types (Indexed, ???). According to [this](https://www.cse.chalmers.se/~abela/master/agda-collections.html) there was not a "correct by construction" collections library for Agda yet.

2. [**Agda Prelude**](https://github.com/UlfNorell/agda-prelude/tree/master/src/Container). Relatively limited selection, but some generalization across interfaces (Traversable, Foldable). Not really sure what they represent (?) because category theory is hard.

3. [**Coq Stdpp**](https://gitlab.mpi-sws.org/iris/stdpp). Good reference -- generalizations of different interfaces, properties proven across those interfaces. Large selection of interfaces, but they're not super clearly organized...

4. [**Isabelle Collections Framework**](https://www.isa-afp.org/entries/Collections.html). Lovely work. Lots of interfaces, lots of implementations, generalization across interfaces, clear relation between the interfaces. A bit outdated, but /shrug

5. [**Isabelle Containers**](https://www.isa-afp.org/entries/Containers.html). Looks interesting, not sure what it does?

For general languages:

1. [**Scala Std**](https://docs.scala-lang.org/overviews/collections/overview.html). Incredibly well-organized. Lots of interfaces and implementations available, and very clear how those interfaces relate. Clear documentation of performance differences.

2. [**F# Core**](https://docs.microsoft.com/en-us/dotnet/fsharp/language-reference/fsharp-collection-types).
Limited options, but seem to be well-organized and has clear documentation of performance differences.

3. [**Haskell Collections API**](https://hackage.haskell.org/package/collections-api-1.0.0.0/docs/Data-Collections.html). Implementation of a quite reasonable set of interfaces and implementations via typeclasses. Some interesting ideas, like using typeclasses to hint about performance to users (?). Overall seems to just be modelling a similar hierarchy to
Scala but with typeclasses.


Cost tracking
---

It would be cool to implement Calf to automatically track the cost of different operations at the type level, but this would need linear types which idk how to embed in Lean.
