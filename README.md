Contains:
- FairBot.v: stabs at formalizing agents reasoning in modal logic, with aaaaall the problems about well-foundedness and recognizing-algorithms
- DepPairs.v: playing around with IsContr, IsProp, and others
    - notable: attempt at isSet a -> isSet (list a)
- merge.v: pain with proving correctness of mergesort
    - to be clear, we only managed opaque totality there
    - (I _think_ we did manage it?)
- UIP_via_J.v: extremely basic attempt to express UIP via J; this is of course impossible; why did we even do that?

- monads: a stab at expressing proper monads!
    - StdLib.v: this should have contained various things we did not want to import but wanted to have like \o, id, et cetera; did it not..work?
    - ReaderT: intends to build up to the definition / semantics of ReaderT / MonadReader
        - (has functors and monoidals; not applicatives yet)
    - Generic: intends to build things in an arbitrary category
        - on typeclasses
        - has: Type-rich category; functors; product categories; bifunctors;
        - nattrans and natiso; functor composition; functor product A×B -> C×D
        - concept of iso-functor; intension to swap A×B×C ~ A×B×C; half a sketch of a monoidal category.