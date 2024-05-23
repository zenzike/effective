Modular Higher-Order Effects
============================

Abstract
--------

Born out of a vision that human comprehension should be prioritized above
mechanical computation, declarative languages prioritize the purpose of
evaluating programs above the process of evaluating programs. Effect handlers
embrace the two perspectives by offering a programming framework where the
purpose of a program is given by operations from a given syntax and the process
of evaluating such programs is given by handlers that provide semantics.

The popularity of algebraic effects is partly due to the practical benefits they
offer as a tool for describing modular domain-specific languages (DSLs).
Algebraic effect handlers enable the creation of specialized, domain-specific
languages tailored to address the unique requirements of specific application
domains. By encapsulating effectful operations within algebraic theories, these
handlers offer a modular and composable framework for defining and interpreting
computational effects. This not only enhances the expressiveness of DSLs but
also facilitates a more intuitive and maintainable way of reasoning about and
orchestrating complex computations within specific problem domains. The
adaptability and versatility afforded by algebraic effect handlers empower
developers to flexibly extend the domains they are working with and reinterpret
those domains differently depending on the context they require.

Unfortunately, the very mechanism that makes algebraic effects modular—that is,
algebraicity—is also their limitation: not all operations of practical
importance are algebraic. In particular, handlers such as catch for catching
exceptions and once for pruning the results of a logic program violate the
requirements of algebraic operations. This shortcoming motivated the exploration
of generalizations of algebraic effects into scoped and latent effects, whose
additional expressivity comes at the cost of the inherent modularity offered by
algebraic effects. Recent work has shown how to recover modularity by
considering modular models that can be inherently extended with new operations.

This talk outlines the practical aspects of the `effective` library, an
implementation of modular higher-order effects in Haskell that is tailored to
simplify working with modular models of algebraic and scoped effects. The
library enables users to define the syntax and semantics of their own DSLs in a
way that is modular and extensible while integrating well with Haskell’s
primitive I/O mechanisms and monad transformer infrastructure.

Overview
--------


Introduction
------------

It is a joy to have been invited to talk about how my work intersects with the
practical aspects of declarative languages. My work over the last few years
has largely been focused on algebraic effects, and in particular, how modularity
fits into an understanding of such effects, and in this talk I'd like to give
some perspectives on the state-of-the-art in the field.

I have studied this from the declarative perspective, where I have been trying
to understand modular effects in functional programming. For more context, let
me take you to the beginning of modern computer science; where Church and Turing
have two very different views on how to approach the study of computation.
Alonzo Church studied computer science through the lambda calculus, where
everything can be expressed by lambda terms and their reductions. Turing, on the
other hand, was more interested in the effects that computation has on a
machine. We now recognize these two views as complementary, leading naturally
to denotational and operational views of programming languages.


NOTE: This could be a good point to bring Algol into the talk.


Denotative Programming
----------------------

This distinction in giving semantics by either indicating how a machine should
make reduction steps or by indicating the desired outcome is made clear
in one of the famous early works in programming languages: Landon's 1966 paper
on "The Next 700 Programming Languages".
In that paper, Landin puts forward the idea that
a programming language should consist of many smaller languages defined
by the programmer, that is each specialized to solving a particular problem:
it was, in essence, advocating a framework for defining and working
with domain-specific languages.

For him, the distinction between the imperative and declarative languages
is not clear enough, and he advises "denotative" as a more appropriate word.
Denotative programming, he says, is made up of three components:

1. an expression is made up of nested subexpressions
2. each subexpression denotes something
3. the denotation of the expression relies only on the denotation of subexpressions

A few years later, in 1971, we see the formal crystalization of these ideas in
the work of Scott and Strachey in the technical monologue: "Towards a
Mathematical Semantics for Computer Languages".
There, they give an example the the valuation function of an expression
that follows exactly these three conditions:

    V[v0 + v1] = V[v0] + V[v1]

Fits the bill, where  (1) the semantics of "V[v0 + v1]" is given by nested
subexpressions v0 and v1, that (2) denote values in their own right, and
(3) whose values combine to give the final semantics.

Treating programming language constructs in this way leads naturally to a
more mathematical treatment of operations.

Euclid
------

The modern treatment of effects is by understanding operations and the axioms
that they are expected to respect.
This is somewhat similar to the treatment that Euclid gave to geometry, in
what is now called synthetic geometry. There, axioms are given to
describe the basic properties of geometric objects such as points and lines.
The five axioms of Euclid are essentially:

1. Any two points can be connected uniquely by a straight line
2. Any line can be extended infinitely
3. A circle can be drawn around any point with any radius
4. All right angles are congruent
5. Given a line and a point not on it, there is at most one line parallel to the given one that goes through the point

(essentially because the fifth postulate has many formulations)



Effects
-------

We are interested in effects, and it is easy to think of effects as an
inherently operational concept: we give their meaning by looking at their
_action_ on some abstract machine, rather than the inherent _value_ of
effects in their own right.

For example, the effect of assignment seems naturally tied to how it interacts
with the store, the effect of nondeterminism can be understood in terms of
nondeterminism provided by the environment, and so on.





This talk is about modular algebraic effects, so before we start, it's a good
idea to start with the main question: what are effects?

In particular, what are effects when we think of declarative programming?







Before starting, it is worth considering what is meant by an "effect".
Side-effecting computations, which occur ``on the side'', typically
the store, while some value is computed are clearly an example. However,
other forms of effect such as nondeterminism and printing can also
occur while a value is being computed; these are _computational effects_.

1. Effect systems in Haskell
2. Modularity
3. Higher-order effects

```haskell
module Effects where
```


```haskell


```











Monads and Composition
----------------------

The following is a monad:

```haskell
data Choose a = Choose { runChoose :: Bool -> a }
  deriving Functor

instance Monad Choose where
  return x = Choose (\b -> x)
  Choose p >>= f = Choose ( runChoose (f (p b)) b )
```

and so is the `Maybe` monad.

But the combination of the two is not!

```haskell
returnMC :: a -> Maybe (Choose a)
returnMC x = Just (Choose (\b -> x))


fishMChoose :: (a -> (Maybe :.: Choose) b)
            -> (b -> (Maybe :.: Choose) c)
            -> (a -> (Maybe :.: Choose) c)
fishMChoose f g x = case f x of
  O (Nothing)         -> O (Nothing)
  O (Just (Choose p)) -> O (Just (Choose (\b -> g (p b))))
```














