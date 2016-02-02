Background
===================================

----

\tableofcontents[currentsection]


Motivation: Scala Needs An Effect System
------------------------------------
How to restrict that `f` should be *pure*?

```Scala
def pmap(xs: List[Int], f: Int => Int): List[Int]
```

. . .

Scala is in want of an effect system:

- Compiler optimization
- Parallel & distributed computing

Effect Polymorphism
----------------------------
What's the effect of `map`?

```Scala
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}
```

. . .

The effects of `map` depends on `f`, it's *effect-polymorphic*.


Effect Polymorphism : State of the Art (1)
----------------------------
In classical type-and-effect systems:

```Scala
def map[A, B, E](f: A => B @E)(l: List[A]): List[B] @E
```

Effect Polymorphism : State of the Art (2)
----------------------------

In Java:

```Java
public interface FunctionE<T, U, E extends Exception> {
  public U apply(T t) throws E;
}

public interface List<T> {
  public <U, E extends Exception> List<U> mapE(FunctionE<T, U, E> f) throws E;
}
```

Effect Polymorphism : State of the Art (3)
---------------------------

In Haskell:

```Haskell
mapM :: Monad m => (a -> m b) -> List a -> m (List b)
mapM f xs
  = case xs of
    Nil -> return Nil
    Cons x xs -> do x' <- f x
      xs' <- mapM f xs
      return (Cons x' xs')

map :: (a -> b) -> List a -> List b
map f xx = runIdentity (mapM (\x. return (f x)) xx)
```

Problem
--------------------

How to express *effect-polymrophic* functions with minimal syntactical
overhead?

The Glory of Capability-Base Effect Systems
--------------------

No additional annotations in neither typing nor terms!

```Scala
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}
```

An Intuition of Capability-Based Effect Systems
=====================

-------------------

\tableofcontents[currentsection]

Capability-Base Effect Systems: Intuition
---------------------
A **capability** is required to produce side effects:

``` Scala
def println: String -> IO -> ()
def readln: IO -> String
```

By tracking *capabilities* in the type system, it's possible to track
*effects* of programs (functions).

Variable-Capturing Discipline
--------------------------------

Need to ensure capabilities are **not** captured from the environment:
```Scala
def pmap(xs: List[Int], f: Int -> Int): List[Int]

def foo(xs: List[Int], c: IO) =
    pmap(xs, { x => print(x, c); x })    // Error, capturing c!
```

Stoic Functions and Free Functions
-------------------------------

- Stoic functions ($\to$): **cannot** capture capabilities from the environment
- Free functions ($\Rightarrow$): **can** freely capture anything in environment

```Scala
def map(xs: List[Int], f: Int => Int): List[Int]
def pmap(xs: List[Int], f: Int -> Int): List[Int]
def print(x: Any, c: IO): ()

def bar(xs: List[Int])(c: IO) =
    map(xs, { x => print(x, c); x })

def foo(xs: List[Int], c: IO) =
    pmap(xs, { x => print(x, c); x })
    // Error, stoic function required
```

Stoic Functions
-----------------
Stoic functions are not necessarily *pure*, only honest about effects
in their type signature:

``` Scala
def hello(c:IO) = println("hello, world!", c)
```

Following stoic function is certainly *pure*:

``` Scala
def twice(f: Int -> Int)(x: Int) = f (f x)
```

Effect Polymorphism via Capabilities
----------------------------------
Both *free* and *stoic* functions are important:

``` Scala
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}
def squareImpure(c: IO) = map { x => println(x)(c); x*x }
def squarePure(l: List[Int]) = map { x => x*x } l
```

Types of functions:

------------   -------------------------------
map            $(A \Rightarrow B) \to List[A] \Rightarrow List[B]$
squareImpure   $IO \to List[A] \Rightarrow List[B]$
squarePure     $List[A] \to List[B]$
------------   -------------------------------

Intuition is not Enough
-------------------------------

Are following functions *pure*?

```Scala
def bar(f: Int -> IO, x: Int) = print(f x, "hello, world!")

def foo(f: Int -> Int => Int, x: Int) = f (f x)

def mie(f: (Int => Int) -> Int => Int, x: Int) = f(n => n)(x)
```

System STLC-Pure
=====================

-------------------

\tableofcontents[currentsection]

System STLC-Pure: STLC-Variant with Only Stoic Functions
----------------------

\setlength{\columnseprule}{0.4pt}
\begin{multicols}{2}

\begin{tabu} to \linewidth {l l l X[r]}
  $t$ & ::= &                     & terms:               \\
      &     & $x$                 & variable             \\
      &     & $\uplambda x{:}T.\, t$ & abstraction          \\
      &     & $t \quad t$            & application          \\
\\
  $v$ & ::= &                        & values:              \\
      &     & $\uplambda x{:}T.\, t$ &     \\
      &     & \colorbox{shade}{x}    & variable value       \\
\\
  $T$ & ::= &                      & types:               \\
      &     & $B$                  & basic type           \\
      &     & \colorbox{shade}{$E$}& capability type      \\
      &     & $T \to T$            &     \\
\end{tabu}

\columnbreak

\textbf{Typing}

\infrule[T-Abs]
{ \colorbox{shade}{$pure(\Gamma),\; x: S \vdash t_2 : T$} }
{ \colorbox{shade}{$\Gamma \vdash \uplambda x{:}S.\, t_2 : S \to T$} }

\textbf{Pure Environment}

\begin{center}
\begin{tabular}{l c l}
$pure(\varnothing)$      & = &  $\varnothing$ \\
$pure(\Gamma, \; x: E)$  & = &  $pure(\Gamma)$ \\
$pure(\Gamma, \; x: T)$  & = &  $pure(\Gamma), \; x: T$     \\
\end{tabular}
\end{center}

\end{multicols}

Soundness
----------------------

\begin{theorem}[Progress]
If $\varnothing \vdash t : T$, then either $t$ is a value or there is some
$t'$ with $t \longrightarrow t'$.
\end{theorem}

\begin{theorem}[Preservation]
If $\Gamma \vdash t : T$, and $t \longrightarrow t'$, then $\Gamma
\vdash t' : T$.
\end{theorem}

*Preservation* is tricky!

Preservation
----------------------

The classic substitution lemma cannot be proved!

\begin{lemma}[Subsitution-Classic]
If $\Gamma,\; x:S \vdash t : T$, and $\Gamma \vdash s : S$, then $\Gamma
\vdash [x \mapsto s]t : T$.
\end{lemma}

Counterexample
----------------------

Following typings hold:

- $f: E \to B,\; c:E,\; x:B \vdash \uplambda z{:}B.\,\textcolor{red}{x} \; : \; B \to B$

- $f: E \to B,\; c:E \vdash \textcolor{red}{f \; c} \; : \; B$

. . .

However, after $[x \mapsto f \; c]$, it can't be typed:

- $f: E \to B,\; c:E \vdash \uplambda z{:}B.\,\textcolor{red}{f \; c} \; : \; B \to B$

The typing rule \textsc{T-Abs} forbids capturing of the capability
variable `c`.

New Subsitution Lemma
----------------------

Instead of the classic subsitution lemma:

\begin{lemma}[Subsitution-Classic]
If $\Gamma,\; x:S \vdash t : T$, and $\Gamma \vdash s : S$, then $\Gamma
\vdash [x \mapsto s]t : T$.
\end{lemma}

We need to stipulate only *values* can be subsituted:

\begin{lemma}[Subsitution-New]
  If $\Gamma,\; x:S \vdash t : T$, s is a value and
  $\Gamma \vdash s : S$, then $\Gamma \vdash [x \mapsto s]t : T$.
\end{lemma}


Strict Evaluation
----------------------

The new subsitution lemma implies:

-  capabilities can only work with *strict evaluation*!

- Or, only *pure* computations can be delayed.

. . .

Monads can only work with lazy evaluation:

```Haskell
inc :: (Num a, Show a) => a -> a
inc n = (\x -> n + 1) (putStrLn (show n))
```

Effect Safety
----------------------

How can we be sure that a function of the type `B -> B` is actually *pure* ?

Informal Formulation (1)
----------------------

\begin{definition}[Effect-Safety-Informally-1]
A function typed in a pure environment cannot have side effects inside.
\end{definition}

. . .

Problem: \textcolor{red}{Stoic functions of the type $E \to B$ may have side effects.}

Informal Formulation (2)
-----------------------

\begin{definition}[Effect-Safety-Informally-2]
  A function, not taking any capability parameter and typed in a pure
  environment, cannot have side effects inside.
\end{definition}

. . .

Problem: \textcolor{red}{Better, but a little cumbersome}.

Informal Formulation (3)
-----------------------

If $S \neq E$, then $t_2$ cannot have side effects in a pure environment:

\begin{multicols}{3}
\infrule
{ pure(\Gamma), \; x: S \vdash t_2 : T }
{ \Gamma \vdash \uplambda x{:}S.\;t_2 : S \to T }

\columnbreak

\begin{center}
\vspace*{1mm}
$\iff$
\end{center}

\columnbreak

\infrule
{ pure(\Gamma, \; x: S) \vdash t_2 : T }
{ \Gamma \vdash \uplambda x{:}S.\;t_2 : S \to T }

\end{multicols}

. . .

Producing side effects needs capabilities, thus:

\begin{definition}[Effect-Safety-Informally-3]
  It's impossible to construct a term of the capability type $E$ in a
  pure environment.
\end{definition}

. . .

Problem: \textcolor{red}{Neat, but can't be proved!}

Counterexample
---------------------

Let's assume $\Gamma = \{f: B \to E, \; x: B\}$, then $f \; x$ has the
capability type $E$.

\vspace*{\baselineskip}

The problem is caused by *ill* types in pure environments:

- $B \to E$
- $B \to B \to E$

These *ill* types are **not** inhabited.

Inhabited Types
---------------------

An environment with *uninhabited* types is always **actually**
effect-safe, as it means the function can never be actually called.

```Scala
def bar(f: Int -> IO, x: Int) = print(f x, "hello, world!")
```

. . .

We only need to care pure environments without uninhabited types:

\begin{definition}[Effect-Safety-Informally-4]
  It's impossible to construct a term of the capability type $E$ in a
  pure environment with only variables of inhabited types.
\end{definition}

<pre>
Definition of Inhabited Types and Environments
---------------------

\begin{definition}[Inhabited Type]
  A type $T$ is inhabited if there exists a value v with the typing
  $x:B, \; y:E \vdash v : T$.
\end{definition}

\begin{definition}[Inhabited Environment]
  An environment $\Gamma$ is inhabited if it only contains variables
  of inhabited types.
\end{definition}

Effect Safety Formally
--------------------

\begin{definition}[Effect-Safety-Inhabited]
  If $\Gamma$ is a pure and inhabited environment, then there doesn't
  exist $t$ with $\Gamma \vdash t : E$.
\end{definition}

A Construct to Prove Effect Safety
---------------------

*capsafe*: capability safe  \hfill  \emph{caprod}: capability producing

\setlength{\columnseprule}{0.4pt}
\begin{multicols}{2}

\textbf{Capsafe Type}

\infax[CS-Base]
{ B \quad \text{capsafe} }

\infrule[CS-Fun1]
{ S \quad \text{caprod} }
{ S \to T \quad \text{capsafe} }

\infrule[CS-Fun2]
{ T \quad \text{capsafe} }
{ S \to T \quad \text{capsafe} }

\columnbreak

\textbf{Caprod Type}

\infax[CP-Eff]
{ E \quad \text{caprod} }

\infrule[CP-Fun]
{ S \; \text{capsafe} \andalso T \; \text{caprod} }
{ S \to T \quad \text{caprod} }

\textbf{Capsafe Environment}

\infax[CE-Empty]
{ \varnothing \quad \text{capsafe} }

\infrule[CE-Var]
{ \Gamma \; \text{capsafe} \andalso T \; \text{capsafe} }
{ \Gamma, \; x:T \quad \text{capsafe} }

\end{multicols}

Proof Idea
----------------------

\begin{definition}[Effect-Safety]
  If $\Gamma$ is capsafe, then there doesn't exist $t$ with
  $\Gamma \vdash t : E$.
\end{definition}

\begin{center}
$\Downarrow$
\end{center}

\begin{definition}[Effect-Safety-Inhabited]
  If $\Gamma$ is a pure and inhabited environment, then there doesn't
  exist $t$ with $\Gamma \vdash t : E$.
\end{definition}

</pre>

What Does Effect Safety Assure Us?
-----------------------

Any functions of type $S \to T$, where $S \neq E$, are **actually**
effect-free.

System STLC-Impure
=====================

-------------------

\tableofcontents[currentsection]

System STLC-Impure
------------------

The straight-forward extension:

- STLC-Pure + Free functions + Subtyping (with $Top$)
- $Pure$ excludes types $S \Rightarrow T$ in additional to the type
  $E$

. . .

\textcolor{red}{It doesn't work!}

Counterexample
------------------

Following typing holds:

-  $c:E \vdash (\uplambda x{:}Top. \, \uplambda y{:}B. \, x) \; c \; : \; B \to Top$

. . .

After one evaluation step:

-  $c:E \vdash \uplambda y{:}B. \, c  \; : \; B \Rightarrow Top$

\textcolor{red}{Preversation breaks!}

. . .

\vspace*{\baselineskip}

Cause: $Top$ masks impure terms as pure terms.

Solution One: Top-Pure and Top-Impure
-------------------

\begin{figure}
\centering

\begin{tikzpicture}[sibling distance=5em,
  every node/.style = {align=center},
  edge from parent/.style={draw,latex-}]
  \node {$Top-Impure$}
  child { node {$E$} }
  child { node (free) {$S \Rightarrow T$} }
  child { node {$Top-Pure$}
    child { node (stoic) {$S \to T$} }
    child { node {$B$} } };
  \path [draw, -latex] (stoic) -- (free);
\end{tikzpicture}

\caption{Subtyping: $Top-Pure$ and $Top-Impure$}
\end{figure}

Solution Two: Tamper with Evaluation
-------------------

Insight: All inhabitants of $Top$ in the system are semantically equivalent.

\vspace*{\baselineskip}

Introduce a special $top$ value:

\begin{multicols}{2}

\infrule
{ T \neq Top }
{ (\uplambda x{:}T.\, t_1) v_2 \longrightarrow [x \mapsto v_2]t_1 }

\infrule
{ T = Top }
{ (\lambda x{:}T.\, t_1) v_2 \longrightarrow [x \mapsto top]t_1 }

\end{multicols}

Effect Safety
------------------

Now we need two statements in the presence of *free functions*:

\begin{definition}[Effect-Safety-Inhabited-1]
  If $\Gamma$ is a pure and inhabited environment, then there doesn't
  exist $t$ with $\Gamma \vdash t : E$.
\end{definition}

\begin{definition}[Effect-Safety-Inhabited-2]
  If $\Gamma$ is a pure and inhabited environment, and
  $\Gamma \vdash t_1 \; t_2 : T$, then there exists $U$, $V$ such that
  $\Gamma \vdash t_1 : U \to V$.
\end{definition}

The Second Statement of Effect Safety
------------------

Let's assume:

- $\Gamma = \{f: B \to B \Rightarrow B, \; x: B\}$

Then

- $\Gamma$ is *inhabited* and *pure*
- $f \; x$ has the type $B \Rightarrow B$
- $(f \; x) \; x$ executes the *free function*

. . .

Does it mean we can produce effects in a *pure* and *inhabited* environment?

. . .

\vspace*{\baselineskip}

\textcolor{red}{No, due to type equivalence.}

Type Equivalence
--------------------

In fact, the following two types are equivalent:

- $B \to B \Rightarrow B \quad \equiv \quad B \to B \to B$

Justification:

- The inner function of the type $B \Rightarrow B$ cannot capture any
capabilities or free functions.
- Otherwise, the outer function cannot be typed as *stoic*.

Axioms
---------------------

Proof of the second effect safety statement depends on following axioms:

\newgeometry{right=0cm}
\begin{multicols}{2}

\infrule[Ax-Base]
{ \Gamma \vdash t : B \to S \Rightarrow T }
{ \Gamma \vdash t : B \to S \to T }


\infrule[Ax-Top]
{ \Gamma \vdash t : Top \to S \Rightarrow T }
{ \Gamma \vdash t : Top \to S \to T }


\infrule[Ax-Stoic]
{ \Gamma \vdash t : (U \to V) \to S \Rightarrow T }
{ \Gamma \vdash t : (U \to V) \to S \to T }


\infrule[Ax-Poly]
{ \Gamma \vdash t_2 : U \to V \\
  \Gamma \vdash t_1 : (U \Rightarrow V) \to S \Rightarrow T }
{ \Gamma \vdash t_1 \; t_2 : S \to T }

\end{multicols}

\restoregeometry

Justification for \textsc{Ax-Poly}
---------------------

Intuition: $t_1$ is *effect-polymorphic*.

\vspace*{\baselineskip}

\begin{minipage}{\linewidth}
\infrule[Ax-Poly]
{ \Gamma \vdash t_2 : U \to V \andalso
  \Gamma \vdash t_1 : (U \Rightarrow V) \to S \Rightarrow T }
{ \Gamma \vdash t_1 \; t_2 : S \to T }
\end{minipage}

. . .

Justification:

> - The only *free function* variable that the inner function of the
  type $S \Rightarrow T$ can capture is the parameter of type $U
  \Rightarrow V$.

> - The inner function cannot capture any capabilities.

> - Otherwise, the outer function cannot be typed as *stoic*.

> - $t_2$ is stoic means $t_1$ can take the type $(U \to V) \to S
  \Rightarrow T$ in the context.

> - \textsc{Ax-Stoic} allows us type $t_1$ as $(U \to V) \to S \to T$.

What Does Effect Safety Assure Us?
-----------------------

Any functions of type $S \to T$, where $S \neq E$ and $S \neq U
\Rightarrow V$, are **actually** effect-free.

System F-Impure
=====================

-------------------

\tableofcontents[currentsection]

System F-Impure
---------------------

The straight-forward extension:

- STLC-Pure + Free functions + Universal Types (without subtyping)

- $Pure$ excludes types $S \Rightarrow T$ in additional to the type
  $E$

- Type abstraction can only be typed in *pure* environments

. . .

\textcolor{red}{It doesn't work, unless we assume:}

\vspace*{\baselineskip}

\begin{minipage}{\linewidth}
\infrule[T-TApp]
{ \Gamma \vdash t_1 : \forall X.T \andalso \colorbox{shade}{$T_2 \neq E$}
  \andalso \colorbox{shade}{$T_2 \neq U \Rightarrow V$} }
{ \Gamma \vdash t_1 \; [T_2] : [X \mapsto T_2]T }
\end{minipage}

Counterexample
---------------------

Let $t = \uplambda X. \, \uplambda x{:}X. \, \uplambda y{:}B. \, x$, we have:

- $\varnothing \vdash t : \forall X. X \to B \to X$
- $\varnothing \vdash t \; [E]: \textcolor{red}{E \to B \to E}$

. . .

After one evaluation step $t \; [E] \longrightarrow t'$, with $t' = \uplambda
x{:}E. \, \uplambda y{:}B. \, x$:

- $\varnothing \vdash t' : \textcolor{red}{E \to B \Rightarrow E}$

\textcolor{red}{Preservation breaks!}

Effect Polymorphism
=====================

-------------------

\tableofcontents[currentsection]

Effect Polymorphism
---------------------

Three kinds of effect polymorphism:

- Axiomatic Polymorphism
- Currying Polymorphism
- Stoic Polymorphism

Axiomatic Polymorphism
----------------------
Axiomatic polymorphism depends on the axiom \textsc{Ax-Poly}.

```Scala
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}

def squareImpure(c: IO) = map { x => println(x)(c); x*x }
def squarePure = map { x => x*x }
```

Currying Polymorphism
----------------------

It's possible to remove the dependency on \textsc{Ax-Poly} by avoid
*currying*:

```Scala
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}

def squareImpure(c: IO) = map { x => println(x)(c); x*x }
def squarePure(l: List[Int]) = map { x => x*x } l
```

Stoic Polymorphism
----------------------

Stoic functions that take a free function and return a value of a pure
type are inherently effect-polymorphic.

```Scala
def twice(f: Int => Int) = f (f 0)
def pure(x: Int) = twice { n => n + x }
def impure(x: Int)(c: IO) = twice { n => println(n)(c); n + x }
```

Summary
----------------------

- Stoic functions and free functions make *effect polymorphism* easy
- Capabilities can only work with *strict evaluation*
- Universal types can't abstract over types of capabilities or free functions

Thank You
------------------
\begin{center}
\LARGE{Questions?}
\end{center}
