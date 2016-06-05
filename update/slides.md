Two Major Problems
===================================

Two Major Problems
----------------------------

To create a *practical* effect system:

- The problem of *effect polymorphism*
- The problem of *versioning*

The Problem of Effect Polymorphism
----------------------------

How to express *effect-polymorphic* functions with minimal syntactic
overhead and the least verbosity in type signature?

\vspace*{0.3cm}

Classic Solution

```Scala
def map[A, B, E](f: A => B @E)(l: List[A]): List[B] @E
```

Ideal Solution

```Scala
def map[A,B](f: A => B)(l: List[A]): List[B]
```

- *Lightweight polymorphic effects*, Rytz et al., 2012
- my master thesis

The Problem of Versioning
----------------------------

How to avoid annotaing effects along the calling path?

\vspace*{0.3cm}

Need to change annotations of `foo` and `bar` if the effects of `qux` change (Java):

```
def foo(s: String): Unit @IO = bar(s)
def bar(s: String): Unit @IO = qux(s)
def qux(s: String): Unit @IO = println(s)
```

Ideal Solution:

```
def foo(s: String): Unit = bar(s)
def bar(s: String): Unit = qux(s)
def qux(s: String): Unit = println(s)
```

- *Implicit parameters: dynamic scoping with static types*, Lewis, 2000
- Co-effects (a generalization of above, not at right level of abstraction)


Solution in Master Thesis
=====================

-------------------

\tableofcontents[currentsection]


Solution in Master Thesis
---------------------

Handles effect polymorphism with *stoic* and *free* functions:

- Stoic functions ($\to$): **cannot** capture capabilities in the environment
- Free functions ($\Rightarrow$): **can** freely capture anything in environment

No annotation required for effect-polymorphism:

```Scala
def map[A,B](f: A => B)(l: List[A]): List[B]
```

Limitations:

- Can't type abstract over $A \Rightarrow B$ or $E$
- Depend on axioms or disable currying


Overcome the Limitations
----------------------------------

A minor change to restore abstraction over $A \Rightarrow B$ and $E$:

- if $T$ is a *type variable*, then $x: T$ cannot be captured by
*stoic* functions.

Overcome the Limitations (Continued)
----------------------------------

How to enforce purity of polymorphic functions (thanks Nada to raise this issue)?

```Scala
def pmap[A, B](f: A -> B)(l: List[A]): List[B]
def app[A, B](f: A -> B)(x: A): B
```

- *Not a problem*: in practice most polymorphic functions are also effect-polymorphic.
- *Solution*: mark type variables that cannot accept $A \Rightarrow B$ or $E$

```Scala
def pmap[`A, B](f: A -> B)(l: List[A]): List[B]
def app[`A, B](f: A -> B)(x: A): B
```

A New Calculus
=====================

-------------------

\tableofcontents[currentsection]

A New Calculus
----------------------

Attempt to overcome the limitations of master thesis:

- Only pure function: $A \to B$
- Two type lambdas:
    - normal type abstraction: $\uplambda X.T$
    - capability type abstraction: $\uplambda' X.T$


Remark: Capabilities **cannot** be captured, must be explicitly passed

\vspace*{0.5cm}

\textcolor{red}{Can we encode $A \Rightarrow B$ of the system in the thesis?}

Encoding of $A \Rightarrow B$ Impossible
----------------------

*Attempt 1*: $A \Rightarrow B$ as $\exists X.(X, A \to X \to B)$

- Needs to introduce product types as primitive
    - impossible to encode $S \times T$ where S or T is capability type
- Cannot be captured, otherwise $Int \to Int$ can call it to produce effects
- Cannot be type parameter to $\uplambda X.\uplambda x{:}X.\uplambda
  n{:}Int. x$ -- preservation breaks

*Attempt 2*: $A \Rightarrow B$ as $\exists X.A \to X \to B$

- Need a bottom capability in order to call it
- Doesn't work for effect polymorphism

What's the type of `map`?

```Scala
def map[A,B](f: A => B)(l: List[A]): List[B]
```

Encoding of $A \Rightarrow B$ Impossible (Continued 1)
----------------------

Translate $A \Rightarrow B$ differently in *effect polymorphic* functions:

```Scala
def map[A,B](f: A => B)(l: List[A]): List[B]
```

Is translated into the follows:

```Scala
def map[A, B, E](f: A -> E -> B)(l: List[A])(c: E): List[B]
```

\textcolor{red}{The translation doesn't have a simple generalization!}

Encoding of $A \Rightarrow B$ Impossible (Continued 2)
----------------------

There seems to be no simple generalization of the translation!

```Scala
def h(g: Int => Int)(x: Int) = g(x)
// ==>
def h[E](g: Int -> E -> Int)(x: Int)(c: E) = g(c)(x)


def f(g: (A => B) -> C)(h: A => B) = g h
// ==>
// ??
```

How to solve the problem of *effect polymorphism* in the new calculus?

Future Research
=====================

-------------------

\tableofcontents[currentsection]

Possible Direction of Future Research
----------------------

The Problem of Versioning (not investigated so far)

- *Implicit parameters*(Lewis, 2000) provide an elegant solution to
the problem of versioning.
- Difference from Scala implicits:  *dynamic scoping* VS *lexical scoping*

The Problem of Effect Polymorphism

- It seems we do need free functions ($A \Rightarrow B$) in order to
reap the benefits of capability-based effect systems
- The duality of *monad* and *comonad* implies there exist similar
  tricks in monad-based effect systems that side-step the problem of
  effect polymorphism.
