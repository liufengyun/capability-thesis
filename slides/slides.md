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

The effect of `map` depends on `f`, it's *effect-polymorphic*.


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

Problem of Effect Polymorphism
--------------------

How to express *effect-polymorphic* functions with minimal syntactical
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

- Stoic functions ($\to$): **cannot** capture capabilities in the environment
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

Stoic Functions are NOT Pure
-----------------

Stoic functions are not necessarily *pure*, but only honest about
effects in their type signature:

``` Scala
// IO -> ()
def hello(c:IO) = println("hello, world!", c)
```

. . .

Following stoic function is certainly *pure*:

``` Scala
// (Int -> Int) -> Int
def twice(f: Int -> Int) = f 5
```

Free Functions are Important
----------------------------------
Effect polymorphism is only possible with *free functions*:

``` Scala
// (A => B) -> List[A] => List[B]
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}

// IO -> List[A] => List[B]
def squareImpure(c: IO) = map { x => println(x)(c); x*x }

// List[A] -> List[B]
def squarePure(l: List[Int]) = map { x => x*x } l
```

Intuition is not Enough
-------------------------------

Can following functions be called to produce effects?

```Scala
def bar(f: Int -> Int => Int) = f (f 5)
```
. . .

```Scala
def foo(f: (Int -> Int) => Int) = f(n => n)(6)
```
. . .

```Scala
def tee(f: Int -> IO, x: Int) = print(f x, "hello, world!")
```


System STLC-Pure
=====================

-------------------

\tableofcontents[currentsection]

System STLC-Pure
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
      &     & $\uplambda x{:}T.\, t$ & function value    \\
      &     & \colorbox{shade}{$x$}  & variable value       \\
\\
  $T$ & ::= &                      & types:               \\
      &     & $B$                  & basic type           \\
      &     & \colorbox{shade}{$E$}& capability type      \\
      &     & $T \to T$            & stoic type     \\
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

\begin{lemma}[Substitution-Classic]
If $\Gamma,\; x:S \vdash t : T$, and $\Gamma \vdash s : S$, then $\Gamma
\vdash [x \mapsto s]t : T$.
\end{lemma}

. . .

\textcolor{red}{It cannot be proved!}

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

New Substitution Lemma
----------------------

Instead of the classic substitution lemma:

\begin{lemma}[Substitution-Classic]
If $\Gamma,\; x:S \vdash t : T$, and $\Gamma \vdash s : S$, then $\Gamma
\vdash [x \mapsto s]t : T$.
\end{lemma}

We need to stipulate only *values* can be substituted:

\begin{lemma}[Substitution-New]
  If $\Gamma,\; x:S \vdash t : T$, s is a value and
  $\Gamma \vdash s : S$, then $\Gamma \vdash [x \mapsto s]t : T$.
\end{lemma}


Strict Evaluation
----------------------

The new substitution lemma implies:

- Capabilities only work with *strict evaluation*!

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

. . .

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
- $Pure$ excludes types $S \Rightarrow T$ in addition to the type $E$

. . .

\textcolor{red}{It doesn't work!}

Counterexample
------------------

Following typing holds:

-  $c:E \vdash (\uplambda x{:}Top. \, \uplambda y{:}B. \, x) \; c \; : \; B \to Top$

. . .

After one evaluation step:

-  $c:E \vdash \uplambda y{:}B. \, c  \; : \; B \Rightarrow Top$

\textcolor{red}{Preservation breaks!}

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

. . .

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

- $Pure$ excludes types $S \Rightarrow T$ in addition to the type $E$

- Type abstraction can only be typed in *pure* environments

. . .

\textcolor{red}{It doesn't work, unless we restrict type application:}

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
// (A => B) -> List[A] => List[B]
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}

// IO -> List[A] => List[B]
def squareImpure(c: IO) = map { x => println(x)(c); x*x }

// List[A] -> List[B]
def squarePure = map { x => x*x }
```

Another example
---------------------

```Scala
// (A => B) -> List[A] => List[B]
private def mapImpl[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}

// (A -> B) -> List[A] -> List[B]
def map[A,B](f: A -> B) = mapImpl(f)

// IO -> (IO -> A => B) => List[A] => List[B]
def map[A,B](c: IO)(f: IO -> A => B) = mapImpl(f c)
```


Currying Polymorphism
----------------------

It's possible to remove the dependency on \textsc{Ax-Poly} by avoid
*currying*:

```Scala
// (A => B) -> List[A] => List[B]
def map[A,B](f: A => B)(l: List[A]) = l match {
  case Nil => Nil
  case x::xs => f(x)::map(f)(xs)
}

// IO -> List[A] => List[B]
def squareImpure(c: IO) = map { x => println(x)(c); x*x }

// List[A] -> List[B], no currying here
def squarePure(l: List[Int]) = map { x => x*x } l
```

Stoic Polymorphism
----------------------

Stoic functions that take a free function and return a value of a pure
type are inherently effect-polymorphic.

```Scala
// (Int => Int) -> Int
def twice(f: Int => Int) = f (f 0)

// Int -> Int
def pure(x: Int) = twice { n => n + x }

// Int -> IO -> Int
def impure(x: Int)(c: IO) = twice { n => println(n)(c); n + x }
```


Summary
----------------------

- Stoic functions and free functions make *effect polymorphism* easy
- Capabilities can only work with *strict evaluation*
- Universal types can't abstract over types of capabilities or free functions

Questions?
------------------
\begin{center}
\Huge{\textit{Thank You}}
\end{center}

\backupbegin

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

Sum and Product Types
------------------------

Sum Types:

- $pure(\Gamma, \; x: B + E) \quad  = \quad pure(\Gamma), \; x: B + Top$

\vspace*{\baselineskip}

Product Types:

- $pure(\Gamma, \; x: B \times E) \quad  = \quad pure(\Gamma), \; x: B \times Top$

Record Types and Classes
------------------------

Record Types:

- $pure(\Gamma, \; x:\{ a: E, b: B \}) \quad  = \quad pure(\Gamma), \; x: { b: B }$

\vspace*{\baselineskip}

Classes adopt similar ideas:

- Each class have two type signature: `Student` and `StudentPure`
- $pure(\Gamma, \; x: Student) \quad  = \quad pure(\Gamma), \; x: StudentPure$

Mutability Effects
-----------------------

Idea: stoic functions cannot capture mutable variables.

```Scala
var a = 3, b = a + 4

// Int => Int
def impure(n: Int) = n + a

// Int -> Int
def pure(n: Int) = n + b

// Int -> Int
def masking(n: Int) = var x = 5; x = b + 3; x + n

// Int -> Int => Int
def closure(n: Int) => var r = n; x => { r = r + 1; x }
```

\textcolor{red}{The axioms no longer hold, but still safe --
mutability local to pure functions.}

Exception Effects
-----------------------

- `try` introduce implicit capabilities related to types in `catch`
- `throw` requires an implicit capability related to the type of exception

```Scala
try { /* implicit c: Throw[IOException] */ }
catch { ex: IOException =>  }

// throw takes an implicit capability with type Throw[T],
// T is instantiated by the type of ex
throw ex
```

However, whether *checked exceptions* is a good idea or not is disputable.

The Value "null"
-----------------------

- Forbid type `Null` to be cast as capability types

\backupend
