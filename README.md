# ESCoC: Expanded-Scope Calculus of Constructions

A nano (500 JS LOC, including parser and bidirectional type-checker) "theorem prover" capable of inductive reasoning. Compared to [Cedille-Core](https://github.com/maiavictor/cedille-core), ESCoC is 1. much simpler to implement, 2. much simpler to use, due to lack of redundancy. But it has no consistency proof (see the point at the end).

## Usage

```
npm i -g escoc
escoc main.escoc
```

ESCoC was initially implemented in JS for no special reason, but a Haskell/Rust version would be nice and smaller.

## Why?

I believe elegance is an important heuristics of mathematical exploration. Whenever a mathematical problem is solved in a complex, "human-engineered" manner, such solution is probably broken, and a correct, elegant, simple and clever solution probably exists, waiting to be found. Designing a proof language may be one of those things waiting for an elegant solution. Proof assistants such as Coq and Agda are built by extending an arguably elegant language (CoC) with inductive datatypes, a complex system that feels suspiciously human-engineered. This is necessary to enable inductive reasoning, essential to mathematical practice, and which CoC unfortunately lacks. Under this point of view, exploring simpler alternatives to inductive datatypes is valuable, because it might let us find such "elegant solution".

## How it works?

ESCoC takes the CoC and 1. expands the scope of the dependent function type, so that, in `Π (x : A) B`, `x` is bound in `A`, 2. enables recursive definitions. And that's it. Notice that there are no extra primitives such as dependent intersections or self types, and no fundamental changes such as involving untyped terms in equality checking. ESCoC doesn't extend (recursive) CoC with anything new, just expands in a very minor way its existing constructs. To explain it, remember that, in CoC, the return type of a function can depend on its argument. That is, in an application such as `(f a)`, if the type of `f` is `Π (x : A) B`, then the type of `(f a)` is `[a/x]B`. The difference is that, in ESCoC, the input type of a function can also depend on its argument. That is, in an application such as `(f a)`, instead of checking if `a : A`, we check if `a : [a/x]A`. ESCoC is defined by the following syntax:

```haskell
term ::=
  Type              -- the type of types
  {var : term} term -- dependent function type
  [var : term] term -- a lambda
  (term term)       -- an application
  var : term = term -- a recursive definition
  var               -- a variable
```

And the following typing rules:

```haskell

----------- type in type (temporary?)
Type : Type

(var, type) in ctx
------------------ variables
ctx |- var : type

ctx, x : A |- A : Type    ctx, x : A |- B : Type
------------------------------------------------ pi (dependent function type)
ctx |- {x : A} B : Type

ctx, x : A |- f : B    ctx |- {a : A} B : Type
---------------------------------------------- lambda (dependent function intro)
ctx |- [x : A] B : {x : A} B

ctx |- f : {x : A} B    ctx |- a : [a/x]A
----------------------------------------- application (dependent function elim)
ctx |- (f a) : [a/x]B
```

Notice that the only change with respect to (recursive) CoC is that `x` is always bound in `A`. This is simple to implement, and any CoC implementation can adopt it with almost no change. 

## How can one implement inductive datatypes on it?

To start with a simple example, let's see the Boolean type. In Agda, you'd write it as such:

```agda
data Bool : Set where
  true  : Bool
  false : Bool
```

That is, it is just a type without constructors. Inductive proofs can be expressed with:

```agda
elim : (b : Bool) -> (P : Bool -> Set) -> P true -> P false -> P b
elim true  P t f = t
elim false P t f = f
```

In CoC, you can represent booleans with Church-encodings:

```haskell
Bool : Type =
  {Prop  : Type}
  {true  : Prop}
  {false : Prop}
  Prop

true  : Bool = [Prop] [true] [false] true
false : Bool = [Prop] [true] [false] false
```

(Note that I'll hide the type annotations of lambdas when they can be recovered by bidirectional type checking.) This isn't too different from the Agda definition, other than the need to write `Prop` instead of `Bool`. This is because the Church-encoding represents a datatype as its own fold, and `Prop` allows us to define type returned when folding over it. Unfortunatelly, there is no way to implement elimination for such a type. In ESCoC, you're able to represent indutive booleans as their own induction principles:

```haskell
Bool
: {self  : (Bool self)} Type
= [self]
  {Prop  : {self : (Bool self)} Type}
  {true  : (Prop Bool.true)}
  {false : (Prop Bool.false)}
  (Prop self)

Bool.true  : (Bool Bool.true)  = [Prop] [true] [false] true
Bool.false : (Bool Bool.false) = [Prop] [true] [false] false
```

Compared to the former representation, the main change is that, now, `Bool` isn't a type, but a function that receives a `Bool` and returns a type. It also refers to its own constructors, `Bool.true` and `Bool.false`, in a mutually recursive fashion; this is the reason we don't need dependent intersections. There isn't a single `Bool` type, but many: `Bool.true`, for example, isn't of type `Bool`, but of type `(Bool BOol.true)`, which is different of the type of `false`, which is `(Bool Bool.false)`. But that's not a problem in practice, because we're still able to implement functions that operate on both:

```haskell
id
: {b : (Bool b)} (Bool b)
= [b] self
```

This is the main power of ESCoC: it can express "super-polymorphic" functions that operate on different types, as long as they are "indexed by their own values". So, despite `true` and `false` having different types, they can still be used as one. This allows us to implement induction easily:

```haskell
Bool.induct
: {self  : (Bool self)}
  {Prop  : {self : (Bool self)} Type}
  {true  : (Prop Bool.true)}
  {false : (Prop Bool.false)}
  (Prop self)
= [self] [Prop] [true] [false]
  (self Prop true false)
```

This is just identity because, under this encoding, datatypes are represented precisely by their induction principles. Now you might be wondering: how do we implement something like `not`? If we try this:

```haskell
Bool.not
: {b : (Bool b)} (Bool b)
= [b] (b
  [b](Bool b)
  Bool.false
  Bool.true)
```

We get a type error. The problem is that, when setting the return type, we wrote `(Bool b)`, where `b` is the value of the input, yet, on the `Bool.true` case, we returned `Bool.false`, which has type `(Bool Bool.false)`, not `(Bool Bool.true)`. We could fix this issue by flipping the arguments, but then that'd turn it into the identity function, not the negation. What we want is to change the return type:

```haskell
Bool.not
: {b : (Bool b)} (Bool (Bool.not b))
= [b] (b
  [b](Bool (Bool.not b))
  Bool.false
  Bool.true)
```

This now says that `not` is a function that takes a `Bool` indexed on itself, and returns a `Bool` indexed on its negation. So, for example, if you give it `true : (Bool true)`, then it will return a `false : (Bool (not true))`. Recursive types like `Nat` can be done using the same concept:

```haskell
Nat
: {self : (Nat self)} Type
= [self]
  {Prop  : {self : (Nat self)} Type}
  {succ  : {pred : (Nat pred)} (Prop (Nat.succ pred))}
  {zero  : (Prop Nat.zero)}
  (Prop self)

Nat.succ
: {pred : (Nat pred)} (Nat (Nat.succ pred))
= [pred] [Nat.] [succ.] [zero.]
  (succ. pred)

Nat.zero
: (Nat Nat.zero)
= [Nat.] [succ.] [zero.] zero.
```

Here, again, `Nat` is a type indexed on itself. The only difference is that the `succ` case has an extra field, `pred`, which is, as expected, `(Nat pred)`. This realizes the Scott-encoding, which are computationally equivalent to Haskell's algebraic datatypes. One can implement inductive Parigot and Church encodings too, but I'm not sure if it is possible to implement certain recursive functions such as `is_even : {n : (PNat n)} (Bool (is_even n))`. Equality can be implemented as such:

```haskell
Eq
: {T    : {self : (T self)} Type}
  {a    : (T a)}
  {b    : (T b)}
  {self : (Eq T a b self)}
  Type
= [T] [a] [b] [self]
  {Prop : {b : (T b)} {self : (Eq T a b self)} Type}
  {refl : (Prop a (Eq.refl T a))}
  (Prop b self)

Eq.refl
: {T : {self : (T self)} Type}
  {a : (T a)}
  (Eq T a a (Eq.refl T a))
= [T] [a] [Prop] [refl]
  refl
```

Notice that this is basically the `J` axiom, with one difference: instead of being parameterized `T : Type`, it is parameterized by a `T : {self : (T self)} Type`, allowing you to express equalities on self-referential types. Something interesting about this representation is that, since `Eq` is indexed on itself, its type essentially carries the evidence of equality around. I'm not sure what this implies. More examples can be seen on the [`main.escoc`](main.escoc) file, including some simple theorems on those types.

## But what about consistency?

CoC with equirecursion isn't consistent, as it is trivial to inhabit the empty type:

```
loop : {P : Type} P = loop
```

But it shouldn't be hard to use ESCoC as the foundation of a consistent language. If we, for example, simply restrict recursion to positive type ocurrences, then, I believe we could easily prove strong normalization by erasure to Fω,, as done on the [Self Types](http://homepage.cs.uiowa.edu/~astump/papers/fu-stump-rta-tlca-14.pdf) paper. This would allow us to, for example, use Parigot (but not Scott) encodings for inductive reasoning. An alternative would be to use an alternative to classic logic, such as [light logics](https://arxiv.org/pdf/0704.2448.pdf), which, as argued on the paper, is consistent even in the presence of arbitrary type recursion. This may be attractive for a bunch of reasons, as it simplifies the theory and allows efficient compilation to interaction combinators. This repository will not include any particular restriction though, as it should be just a template to explore those ideas. 
