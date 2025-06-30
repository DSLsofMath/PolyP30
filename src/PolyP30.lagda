% notes to self (JG):
%   C-\        toggles input method on and off
%   C-C C-l    loads (typechecks) Agda
%   C-C C-SPC  "give" to this goal
%   C-C C-,    type and context of current goal
%   C-C C-C    refine a variable


\documentclass[fleqn,runningheads]{llncs}

\usepackage{agda}
\setlength{\AgdaEmptySkip}{1ex} % smaller gap for blank lines
\mathindent=\parindent % smaller indentation of code (and displayed maths) blocks
\errorcontextlines=999
\def\scottopen{[\hskip-1pt[}
\def\scottclose{]\hskip-1pt]}
\DeclareRobustCommand{\AgdaFormat}[2]{%
  \ifthenelse{\equal{#1}{\AgdaUnderscore{}⊕\AgdaUnderscore{}}}{$\_\!{\oplus}\!\_$}{%
  \ifthenelse{\equal{#1}{[]}}{$[\,]$}{%
  \ifthenelse{\equal{#1}{+N}}{$\mathbin{+}_{\!N}$}{%
  \ifthenelse{\equal{#1}{*N}}{$\mathbin{*}_{\!N}$}{%
  \ifthenelse{\equal{#1}{==N}}{$\mathbin{==}_N$}{%
  \ifthenelse{\equal{#1}{==B}}{$\mathbin{==}_B$}{%
  \ifthenelse{\equal{#1}{==U}}{$\mathbin{==}_U$}{%
  \ifthenelse{\equal{#1}{*}}{$\color{AgdaInductiveConstructor}\mathbin{\ast}$}{%
  \ifthenelse{\equal{#1}{\AgdaUnderscore{}*\AgdaUnderscore{}}}{$\color{AgdaInductiveConstructor}\AgdaUnderscore\mathbin{\ast}\AgdaUnderscore$}{%
  \ifthenelse{\equal{#1}{[[}}{$\AgdaFunction{\scottopen}\!$}{%
  \ifthenelse{\equal{#1}{]]}}{$\!\AgdaFunction{\scottclose}$}{%
  \ifthenelse{\equal{#1}{]]₀}}{$\!\AgdaFunction{\scottclose}_{\AgdaDatatype{\scriptsize0}}$}{%
  \ifthenelse{\equal{#1}{]]T}}{$\!\AgdaFunction{\scottclose}_{\AgdaFunction{\scriptsize T}}$}{%
  \ifthenelse{\equal{#1}{]]F}}{$\!\AgdaFunction{\scottclose}_{\AgdaFunction{\scriptsize F}}$}{%
  \ifthenelse{\equal{#1}{]]B}}{$\!\AgdaFunction{\scottclose}_{\AgdaFunction{\scriptsize B}}$}{%
  \ifthenelse{\equal{#1}{[[\AgdaUnderscore{}]]}}{$\AgdaFunction{\scottopen\AgdaUnderscore\scottclose}$}{%
  \ifthenelse{\equal{#1}{[[\AgdaUnderscore{}]]₀}}{$\AgdaFunction{\scottopen\AgdaUnderscore\scottclose}_{\AgdaDatatype{\scriptsize0}}$}{%
  \ifthenelse{\equal{#1}{[[\AgdaUnderscore{}]]T}}{$\AgdaFunction{\scottopen\AgdaUnderscore\scottclose}_{\AgdaFunction{\scriptsize T}}$}{%
  \ifthenelse{\equal{#1}{[[\AgdaUnderscore{}]]F}}{$\AgdaFunction{\scottopen\AgdaUnderscore\scottclose}_{\AgdaFunction{\scriptsize F}}$}{%
  \ifthenelse{\equal{#1}{[[\AgdaUnderscore{}]]B}}{$\AgdaFunction{\scottopen\AgdaUnderscore\scottclose}_{\AgdaFunction{\scriptsize B}}$}{%
  \ifthenelse{\equal{#1}{crushB}}{$\AgdaFunction{crush}_{\AgdaFunction{\scriptsize B}}$}{%
  \ifthenelse{\equal{#1}{c'}}{$\AgdaBound{c}^\prime$}{%
  \ifthenelse{\equal{#1}{x'}}{$\AgdaBound{x}^\prime$}{%
  \ifthenelse{\equal{#1}{y'}}{$\AgdaBound{y}^\prime$}{%
  #2}}}}}}}}}}}}}}}}}}}}}}}}}
\paperwidth=210mm \paperheight=297mm
\leftmargini = \parindent

\usepackage[T1]{fontenc}
%\usepackage{microtype}
%\DisableLigatures[--]{encoding=T1}
\DeclareUnicodeCharacter{2219}{\ensuremath{\cdot}}  % ∙
\DeclareUnicodeCharacter{03B5}{\ensuremath{\epsilon}}  % ε
\DeclareUnicodeCharacter{2218}{\ensuremath{\circ}}  % ∘
\DeclareUnicodeCharacter{25E6}{\ensuremath{\circ}}  % ◦
\DeclareUnicodeCharacter{25CF}{\ensuremath{\bullet}}  % ●
\DeclareUnicodeCharacter{2261}{\ensuremath{\equiv}} % ≡
\DeclareUnicodeCharacter{22A4}{\ensuremath{\top}}   % ⊤
\DeclareUnicodeCharacter{03BB}{\ensuremath{\lambda}}
\DeclareUnicodeCharacter{03A3}{\ensuremath{\Sigma}}
\DeclareUnicodeCharacter{2080}{\ensuremath{_{\AgdaFontStyle{\scriptsize0}}}}
\DeclareUnicodeCharacter{2081}{\ensuremath{_{\AgdaFontStyle{\scriptsize1}}}}
\DeclareUnicodeCharacter{2082}{\ensuremath{_{\AgdaFontStyle{\scriptsize2}}}}
\DeclareUnicodeCharacter{2237}{\ensuremath{::}}
\DeclareUnicodeCharacter{2200}{\ensuremath{\forall}}
\DeclareUnicodeCharacter{2192}{\ensuremath{\rightarrow}}
\DeclareUnicodeCharacter{00D7}{\ensuremath{\times}}
\DeclareUnicodeCharacter{2227}{\ensuremath{\land}}
\DeclareUnicodeCharacter{2228}{\ensuremath{\lor}}
\DeclareUnicodeCharacter{2295}{\ensuremath{\oplus}}

\usepackage[safe]{tipa}
\usepackage{hyperref}
\usepackage[capitalise,noabbrev]{cleveref}

\mathchardef\atsign="3040
\def\sumf{\mathbin{\mbox{-}{+}\mbox{-}}}
\def\prodf{\mathbin{\mbox{-}{\!\times\!}\mbox{-}}}

\begin{document}

\title{Agda-ventures with PolyP}
%\subtitle{PolyP, Thirty Years On}

\author{Jeremy Gibbons\inst{1}\orcidID{0000-0002-8426-9917} \and \\
Patrik Jansson\inst{2}\orcidID{0000-0003-3078-1437}}

\institute{University of Oxford, UK \\
\url{https://www.cs.ox.ac.uk/people/jeremy.gibbons/}
\and
Chalmers University of Technology and University of Gothenburg, SE \\
\url{https://patrikja.owlstown.net/}}

\maketitle

\begin{abstract}
Revisiting Johan Jeuring's PolyP 30 years on, we note that a special-purpose language is no longer needed: general-purpose dependently typed programming suffices.
This is a text-based adventure from software archeology, via codes to universes.
Happy 60th Birthday, Johan!
\end{abstract}

\section{Introduction}

Among Johan Jeuring's contributions to the world, not the least is his programming language PolyP, developed in a series of papers from 1995 to 2002. One of us was his first PhD student, and part of this endeavour.
%\footnote{Was it funded?} I don't think there was a separate project funding this - I got a "departmental PhD position" in 1995 and chose to work with Johan on this.

PolyP was a research language designed for the purpose of exploring the notion of \emph{polytypic programming}: programs that are parametrized by the shape of datatypes, so that one program can be applied to many different datatypes. In the first paper on the topic \cite{Jeuring95:Polytypic}, Jeuring quotes the definition from Webster's dictionary:
\begin{quote}
\textbf{poly·typ·ic}
[\textipa{\textsecstress{}p\"{a}-l\={e}-\textprimstress{}ti-pik}], \textit{adj}.:
having or involving several different types
\end{quote}
Other names for the same idea include
`structurally polymorphic', % Hinze
`shape polymorphic, % Jay
`type parametric', % Sheard
`generic', % Bird, de Moor, Hoogendijk
and `datatype-generic'. % Backhouse, Gibbons
Typical polytypic programming problems are structural:
equality,
matching, % 1995 FPCA Polytypic Pattern Matching.pdf
folding, mapping, % 1997 POPL PolyP.pdf
traversal, encoding, printing, parsing, % TODO perhaps cite 2002 SCP Polytypic Data Conversion Programs.pdf
unification, % TODO perhaps cite 1998 JFP Polytypic Unification.pdf
and so on.
A crucial criterion is the maintenance of strong static type safety; in contrast, approaches based on dynamic typing may be able to express the same programs, but cannot make the same static guarantees.

%1998-04-13: first commit: https://github.com/patrikja/PolyP/commit/4e8fd742c3f51870b8ca5dade562b14920099907
PolyP was implemented \cite{Jansson&Jeuring97:Polytypic} as a preprocessor for Haskell, providing an additional \AgdaKeyword{polytypic} construct that gets translated into ordinary Haskell.
% JG: I hate footnotes!
(The source code is available at GitHub \cite{PolyP-github}. The original revision history has been preserved, predating GitHub's birth by a decade.)
The work on PolyP led to a grant from the Dutch research council NWO for the \textit{Generic Haskell} project, running 2000--2004 \cite{GH-project}, another preprocessor for Haskell, and then in turn to many different approaches to generic programming \cite{Garcia*2007:Extended}.

So the ideas involved in PolyP have been influential over the past thirty years or so. But they have also been superseded by developments in programming languages. In particular, what in 1995 required a domain-specific language and a special-purpose preprocessor can be achieved in 2025 by good old-fashioned programming. This has been enabled by the advances that have since been made in \emph{dependent types}. Whilst this theory significantly predates PolyP, it is only recently that tools originally envisioned as supporting theorem proving and formalized mathematics have become plausible programming languages.

In this short paper, we summarize the key ideas behind polytypic programming, and show how they can now be captured directly in a dependently typed programming language. Any dependently typed language will do, but we will use Agda. Maybe we can entice you back, Johan? The water is much warmer these days!

\section{Polytypic programming}

The general idea with PolyP is that ``a polytypic function can be viewed as a family of functions: one function for each datatype'' \cite{Jeuring&Jansson96:Polytypic}, defined by induction over the structure of the datatype. So first one needs to settle on the universe of datatypes.

PolyP used \emph{polynomial types}: sums and products of some basic types, such as booleans, integers, and the unit type. For recursive datatypes such as lists of booleans and trees of integers, it used \emph{regular functors}: initial algebras for functors constructed from polynomial operations on a type parameter, closed under certain compositions (so that one recursive datatype can be used in the shape functor for another). And to accommodate polymorphic (container) datatypes too, it extended to \emph{regular bifunctors}.

For example \cite{Jeuring&Jansson96:Polytypic}, the Haskell datatypes of lists and rose trees
\[ \begin{array}{lcl}
\mathbf{data} \; \mathit{List}\;a &=& \mathit{Nil} \mid \mathit{Cons}\;a\;(\mathit{List}\;a) \\
\mathbf{data} \; \mathit{Rose}\;a &=& \mathit{Fork}\;a\;(\mathit{List}\;(\mathit{Rose}\;a))
\end{array} \]
are the initial algebras respectively of the bifunctors written in PolyP as
\[ \begin{array}{lcl}
\mathit{FList} &=& () + \mathbf{Par} \times \mathbf{Rec} \\
\mathit{FRose} &=& \mathbf{Par} \times (\mathit{List} \atsign \mathbf{Rec})
\end{array} \]
For $\mathit{FList}$, the bifunctor is a sum, with the unit type for the left summand; the right summand is the product of the datatype parameter (that is, the first bifunctor argument) and a recursive call (the second bifunctor argument). For $\mathit{FRose}$, the right factor is the composition of $\mathit{List}$ and the recursive position.
%\footnote{Jeremy: $\mathbf{Mu}$ is a keyword, not an identifier, right? Patrik: It was a keyword at first (AFP 1996), but then we migrated to writing $d @ g$ instead of $Mu f @ g$ (POPL 1997). Jeremy: OK, let's use the later one; but for rose trees, is it $List @ Rec$ or $FList @ Rec$?. Patrik: It is $List @ Rec$.}

Continuing the example from \cite{Jeuring&Jansson96:Polytypic}, inductive datatypes $\mathbf{Mu}\;F\;A$ for bifunctor $F$ and element type $A$ have a constructor and a destructor:
\[ \begin{array}{lcl}
\mathit{inn} &::& f\;a\;(\mathbf{Mu}\;f\;a) \to \mathbf{Mu}\;f\;a \\
\mathit{out} &::& \mathbf{Mu}\;f\;a \to f\;a\;(\mathbf{Mu}\;f\;a) \\
\end{array} \]
A polytypic `map' function for inductive datatypes
\[ \begin{array}{lcl}
\mathit{pmap} &::& (a \to b) \to \mathbf{Mu}\;f\;a \to \mathbf{Mu}\;f\;b \\
\mathit{pmap}\;p &=& \mathit{inn} \mathbin{\cdot} \mathit{fmap}\;p\;(\mathit{pmap}\;p) \mathbin{\cdot} \mathit{out} \\
\end{array} \]
is defined in terms of a polytypic $\mathit{fmap}$ for regular bifunctors:
\[ \begin{array}{l}
\mathbf{polytypic}\;\mathit{fmap} :: (a \to c) \to (b \to d) \to f\;a\;b \to f\;c\;d \\
\qquad = \lambda\;p\;r \rightarrow \mathbf{case}\;f\;\mathbf{of} \\
\qquad \qquad \begin{array}[t]{lcl}
f + g &\rightarrow& \mathit{fmap}\;p\;r \sumf \mathit{fmap}\;p\;r \\
() &\rightarrow& \mathit{id} \\
\mathbf{Con}\;t &\rightarrow& \mathit{id} \\
f \times g &\rightarrow&\mathit{fmap}\;p\;r \prodf \mathit{fmap}\;p\;r \\
d \atsign g &\rightarrow& \mathit{pmap}\;(\mathit{fmap}\;p\;r) \\
\mathbf{Par} &\rightarrow& p \\
\mathbf{Rec} &\rightarrow& r \\
\end{array}
\end{array} \]
where $(\sumf)$ and $(\prodf)$ map over sums and products respectively.

Note that there is no $\mathit{Functor}$ or $\mathit{Bifunctor}$ type class constraint on $f$, requiring a separate instance declaration, as would typically be the case in Haskell. Rather, the definition of $\mathit{fmap}$ is essentially the template by which GHC would automatically \emph{derive} a functor instance.

\section{Dependently typed programming}

\begin{code}[hide]
module PolyP30 where
open import Data.List using (List; _∷_; []; [_]; _++_; foldr; foldl; concat; reverse; length; uncons; splitAt) public
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe; _>>=_ to _>>=M_) public
open import Data.Vec using (Vec;  _∷_; []; map; replicate; insertAt; removeAt) renaming (foldl to vfoldl; lookup to vlookup) public
open import Data.Bool using (Bool; false; true; _∧_; _∨_; not; if_then_else_) renaming (_≟_ to _=?B_) public
open import Function using (id; const; _∘_; case_of_) public
open import Data.Nat using (zero; suc; _<_) renaming (ℕ to Nat; _≟_ to _=?N_; _+_ to _+N_; _*_ to _*N_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Unit using (⊤; tt) public
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to Sum; map to mapSum) public
open import Data.Product using (_×_; _,_; map₁) renaming (map to mapProd) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst) public
open import Relation.Nullary.Decidable using (does; yes; no) public
open import Effect.Monad renaming (RawMonad to Monad) public
open Monad {{...}} public


_==N_ : Nat → Nat → Bool
m ==N n = does (m =?N n)

_==B_ : Bool → Bool → Bool
x ==B y = does (x =?B y) -- (x ∧ y) ∨ (not x ∧ not y)

_==U_ : ⊤ → ⊤ → Bool
tt ==U tt = true

{-# TERMINATING #-}
fix : ∀ {a : Set} → (a → a) → a
fix f = f (fix f)
\end{code}

%The following snippet enables number literals for both |Nat| and |Fin n|.
\begin{code}[hide]
open import Data.Unit.Base using (⊤) -- needed for the Number instance

import Data.Nat.Literals using (number)
import Data.Fin.Literals using (number)
open import Agda.Builtin.FromNat using (Number; fromNat)
  -- fromNat needed although it is not visibly used

instance  -- enable natural number literals
  numNat : Number Nat
  numNat = Data.Nat.Literals.number

instance  -- enable Fin literals
  numFin : forall {n} → Number (Fin n)
  numFin {n} = Data.Fin.Literals.number n
\end{code}

In PolyP, a polytypic definition like that of $\mathit{fmap}$ specifies what code should be generated for a specific type: ``the compiler generates instances from the definition of the polytypic function and the type in the context where it is used''~\cite{Jansson&Jeuring97:Polytypic}. This is more than mere text processing, because PolyP does take care to type check a polytypic definition, in the sense that no generated instance will yield a Haskell type error. Still, PolyP is essentially a standalone domain-specific language for polytypic definitions, which means that the full power of the target language Haskell is not available in polytypic code.

This is a price that need not be paid, provided one can find a single language expressive enough to encompass both the polytypic templates and the actual eventual code. Then a separate code generation phase is not required: it becomes ``a small matter of programming'' in the one language.
It turns out that a dependently typed language like Agda \cite{norell2007towards} provides the expressivity needed: types (and operations on types, such as functors and bifunctors) are values too.

So what would in PolyP be a polytypic function parametrized by a functor becomes in Agda just a function with an argument. However, that argument can't literally be a type, or a functor. We can't work with the types themselves, because we can't analyse them: they would be black boxes, and we need to perform case analyses on them. Instead, we make separate \emph{codes} for the types in the universe, and define the interpretation mapping codes to types. Codes \emph{can} be analysed and manipulated, since they are just terms in an algebraic datatype.

As a simple introduction, let's consider the universe of types consisting of sums and products of the unit type, naturals, and booleans. We start with an algebraic datatype of codes for the types in the universe:
\begin{code}
data Code₀ : Set where
  NatT BoolT UnitT : Code₀
  _*_   _+_   : Code₀ → Code₀ → Code₀
\end{code}
% data Code₀ : Set where
%   NatT   : Code₀
%   BoolT  : Code₀
%   UnitT  : Code₀
%   _*_    : Code₀ → Code₀ → Code₀
%   _+_    : Code₀ → Code₀ → Code₀
For example, here is the code for the sum of the unit type and the product of naturals and booleans (that is, what would be $\mathit{Maybe}\;(\mathit{Nat},\mathit{Bool})$ in Haskell):
\begin{code}
MaybeNatBoolCode : Code₀
MaybeNatBoolCode = UnitT + (NatT * BoolT)
\end{code}
We can then define the interpretation of codes as types:
\begin{code}
[[_]]₀ : Code₀ → Set
[[ NatT ]]₀    = Nat
[[ BoolT ]]₀   = Bool
[[ UnitT ]]₀   = ⊤
[[ c * c' ]]₀  = [[ c ]]₀ × [[ c' ]]₀
[[ c + c' ]]₀  = Sum [[ c ]]₀ [[ c' ]]₀
\end{code}
This interpretation is simply a straightforward function definition---we have exploited Agda's fancy mix-fix syntax, but we might as well have named the function something like ``\AgdaFunction{interp0}''. The definition is by induction over the structure of codes: interpretations of the three base type codes are given directly (``\AgdaRecord{⊤}'' denotes the unit type, with sole element \AgdaInductiveConstructor{tt}), and interpretations of the product and sum code constructors given inductively (``\AgdaFunction{×}'' and ``\AgdaDatatype{Sum}'' denote product and sum types respectively).

Finally, we can define a polytypic function over this universe of types. For example, here is the equality function: it takes the code for some type in the universe, and two elements of the interpretation of that code, and returns a boolean. For the three base cases (constant types), the comparison is delegated to type-specific operators; for the two inductive cases (product and sum), it is given inductively.
% \footnote{I've had to import equality from Agda.Builtin.Nat, whereas zero and suc come from Data.Nat; is that idiomatic? And is there no standard equality on booleans? I've rolled my own. Patrik: the "idiomatic" function is decidable equality which returns both a Bool (extracted with "does") and an equality proof. Should we mention it? Jeremy: Unless we need it somewhere else too, I suggest not mentioning it here.}
\begin{code}
equal₀ : { c : Code₀ } → [[ c ]]₀ → [[ c ]]₀ → Bool
equal₀ {NatT}      n          m          = (n ==N m)
equal₀ {BoolT}     x          y          = (x ==B y)
equal₀ {UnitT}     x          y          = (x ==U y)
equal₀ {c * c'}    (x , x')   (y , y')   = equal₀ x y ∧ equal₀ x' y'
equal₀ {c + c'}    (inj₁ x)   (inj₁ y)   = equal₀ x y
equal₀ {c + c'}    (inj₂ x')  (inj₂ y')  = equal₀ x' y'
equal₀ {c + c'}    _          _          = false
\end{code}
For example, the two elements
\AgdaInductiveConstructor{inj₁}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}
and
\AgdaInductiveConstructor{inj₂}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaNumber{3}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,}}\AgdaSpace{}%
\AgdaInductiveConstructor{false}\AgdaSymbol{)}
in the interpretation of \AgdaDatatype{MaybeNatBoolCode} are not equal; and indeed, the expression
\begin{code}[hide]
test_equal₀ :
\end{code}
\begin{code}
  equal₀ { MaybeNatBoolCode } (inj₁ tt) (inj₂ (3 , false))
\end{code}
\begin{code}[hide]
  ≡ false
test_equal₀ = refl
\end{code}
normalizes to \AgdaInductiveConstructor{false}.
%
Note that the first argument to \AgdaFunction{equal₀} is written in curly braces, marking it as \emph{implicit}, since it can be inferred. In particular, it is omitted for the recursive calls, and not needed for the example either: we can write just
\begin{code}[hide]
test_equal₀_noimplicit : Bool
test_equal₀_noimplicit =
\end{code}
\begin{code}[inline]
  equal₀ (inj₁ tt) (inj₂ (3 , false))
\end{code}.

\section{The full story}

\begin{code}[hide]
variable
  a b c d : Set
\end{code}

So much for codes for types, and their interpretation as actual types.
If we want to handle inductive datatypes as fixpoints, we also want codes for functors.
And for polymorphic inductive datatypes, we want bifunctors.
So here are three mutually recursive datatypes of codes for them:
\begin{code}
mutual
  data Type : Set where
    NatTy BoolTy UnitTy  : Type

  data Functor : Set where
    Fix     : Bifunctor → Functor

  data Bifunctor : Set where
    _*_   _+_   : Bifunctor  → Bifunctor  →  Bifunctor
    Const       : Type                    →  Bifunctor
    _●_         : Functor    → Bifunctor  →  Bifunctor
    Par  Rec    :                            Bifunctor
\end{code}
% PJ: I shortened the code to get a better page break - here it is for an easy revert.
%   data Type : Set where
%     NatTy   : Type
%     BoolTy  : Type
%     UnitTy  : Type
%
%   data Functor : Set where
%     Fix     : Bifunctor → Functor
%
%   data Bifunctor : Set where
%     _*_     : Bifunctor → Bifunctor → Bifunctor
%     _+_     : Bifunctor → Bifunctor → Bifunctor
%     Const   : Type → Bifunctor
%     _●_     : Functor → Bifunctor → Bifunctor
%     Par     : Bifunctor
%     Rec     : Bifunctor

% composition is Unicode "black circle", U+25CF
In order to interpret codes for inductive datatypes, we need to define these:
\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data Mu (f : Set → Set) : Set where
  In : f (Mu f) → Mu f

out : { f : Set → Set } → Mu f → f (Mu f)
out (In xs) = xs
\end{code}
Not all functors induce inductive datatypes, so we have to turn off the check that Agda would otherwise insist on. Since we are modelling PolyP generating Haskell, we don't worry too much about the risk of non-termination.

We can now give the interpretations of the three kinds of code:
\begin{code}
mutual
  [[_]]T : Type       →              Set
  [[_]]F : Functor    → Set →        Set
  [[_]]B : Bifunctor  → Set → Set →  Set

  [[ NatTy ]]T     = Nat
  [[ BoolTy ]]T    = Bool
  [[ UnitTy ]]T    = ⊤

  [[ Fix f ]]F p   = Mu ([[ f ]]B p)

  [[ f * g ]]B    p r   = [[ f ]]B p r × [[ g ]]B p r
  [[ f + g ]]B    p r   = Sum ([[ f ]]B p r) ([[ g ]]B p r)
  [[ Const t ]]B  p r   = [[ t ]]T
  [[ d ● f ]]B    p r   = [[ d ]]F ([[ f ]]B p r)
  [[ Par ]]B      p r   = p
  [[ Rec ]]B      p r   = r
\end{code}
Each base code is interpreted as the corresponding base type.
Our only code for a functor is for a polymorphic inductive datatype, which is interpreted accordingly, using the interpretation of its bifunctor parameter.
Bifunctor codes for lifted product and sum of two bifunctors are interpreted using the standard constructors; the codes for a constant bifunctor and for the composition of a functor and a bifunctor (``$\atsign$'' in PolyP, which is reserved in Agda so written with a bullet here) are defined recursively; and the `parameter' and `recursive argument' are projections.

Next we can define the functorial action for functors and bifunctors (the $\mathit{pmap}$ and $\mathit{fmap}$ we saw above), mutually recursive with catamorphisms:
\begin{code}
mutual
  {-# TERMINATING #-}
  pmap   :  (d : Functor)    → (a → b) → [[ d ]]F a → [[ d ]]F b
  fmap   :  (f : Bifunctor)  → (a → b) → (c → d) → [[ f ]]B a c → [[ f ]]B b d
  cata   :  (f : Bifunctor)  → ([[ f ]]B a b → b) → [[ Fix f ]]F a → b

  cata f h (In xs)           = h (fmap f id (cata f h) xs)

  pmap (Fix f) g             = cata f (In ∘ fmap f g id)

  fmap (f * g) p r (x , y)   = (fmap f p r x , fmap g p r y)
  fmap (f + g) p r (inj₁ x)  = inj₁ (fmap f p r x)
  fmap (f + g) p r (inj₂ y)  = inj₂ (fmap g p r y)
  fmap (Const t) p r x       = x
  fmap (d ● g) p r xs        = pmap d (fmap g p r) xs
  fmap Par p r               = p
  fmap Rec p r               = r
\end{code}
%  -- Alt.:   pmap (Fix f) g (In xs) = In (fmap f g (pmap (Fix f) g) xs)
For example, the code \AgdaFunction{ListF} for the shape bifunctor for lists, the corresponding code \AgdaFunction{ListC} for its fixpoint, and the interpretation \AgdaFunction{MyList} of the latter as an actual functor are:
\begin{code}
ListF   : Bifunctor
ListF   = Const UnitTy + (Par * Rec)

ListC   : Functor
ListC   = Fix ListF

MyList  : Set → Set
MyList  = [[ ListC ]]F
\end{code}
We can define constructors for these lists:
\begin{code}
nilList : MyList a
nilList = In (inj₁ tt)

consList : a → MyList a → MyList a
consList x xs =  In ( inj₂ ( ( x ,  xs )))
\end{code}
and conversion functions from and to built-in lists:
\begin{code}
toMyList : List a → MyList a
toMyList = foldr consList nilList

fromMyList : MyList a → List a
fromMyList = cata ListF alg where
  alg : [[ ListF ]]B a (List a) → List a
  alg (inj₁ tt)           = []
  alg (inj₂ ( x ,  xs ))  = x ∷ xs
\end{code}
One canonical example of a polytypic function on polymorphic container datatypes is to ``crush'' it \cite{Meertens96:Calculate}, aggregating the elements using a monoid:
%\footnote{TODO should we pass in a monoid instead? fix code}
\begin{code}
mutual
  crush : (a → a → a) → a → (d : Functor) → [[ d ]]F a → a
  crush   _⊕_ e (Fix f) = cata f (crushB _⊕_ e f)

  crushB : (a → a → a) → a → (f : Bifunctor) → [[ f ]]B a a → a
  crushB  _⊕_ e (f * g)    (x , y)   = crushB _⊕_ e f x ⊕ crushB _⊕_ e g y
  crushB  _⊕_ e (f + g)    (inj₁ x)  = crushB _⊕_ e f x
  crushB  _⊕_ e (f + g)    (inj₂ y)  = crushB _⊕_ e g y
  crushB  _⊕_ e (Const t)  x         = e
  crushB  _⊕_ e Par        p         = p
  crushB  _⊕_ e Rec        r         = r
  crushB  _⊕_ e (d ● g) =  crush _⊕_ e d ∘ pmap d (crushB _⊕_ e g)
\end{code}
\begin{code}[hide]
-- TODO try to make this work? there's a name clash with _∙_, despite my renaming
--open import Algebra using () renaming (RawMonoid to Monoid; _∙_ to _⊗_)
--open Monoid
--crush' : {{Monoid _ _}} → (d : Functor) → [[ d ]]F Carrier → Carrier --  with (_∙_ , ε)
--crush' = {!!}
\end{code}
The binary operator is used to combine the two aggregations in a product, and the unit value is used for constants. For instance, we can flatten a container to a list, by making every element a singleton list then crushing using the list monoid:
\begin{code}
flatten : (d : Functor) → [[ d ]]F a → List a
flatten d = crush _++_ [] d ∘ pmap d (λ x → [ x ])
\end{code}

\begin{code}[hide]
mutual
  flattenDirectly : (d : Functor) → [[ d ]]F a → List a
  flattenDirectly (Fix f) = cata f (fl f)

  fl : (f : Bifunctor) → [[ f ]]B a (List a) → List a
  fl (f * g)      = λ ( x , y ) → fl f x ++ fl g y
  fl (f + g)      = λ xy → case xy of λ
                       { (inj₁ x) → fl f x
                       ; (inj₂ y) → fl g y }
  fl (Const t)    = λ _ → []
  fl (d ● g)      = concat ∘ flattenDirectly d ∘ pmap d (fl g)
  fl Par          = λ x → [ x ]
  fl Rec          = id
\end{code}

\begin{code}[hide]
testList : List Nat
testList = 1 ∷ 2 ∷ 3 ∷ []
myList : MyList Nat
myList = foldr consList nilList (1 ∷ 2 ∷  3 ∷ [])
checkMyList : toMyList testList ≡ consList 1 (consList 2 (consList 3 nilList))
checkMyList = refl
checkFlatten : let xs = testList in (xs ≡ flatten ListC (toMyList xs))
checkFlatten = refl

proveFlatten : ∀ (xs : List Nat) → xs ≡ flatten ListC (toMyList xs)
proveFlatten [] = refl
proveFlatten (x ∷ xs) = cong (x ∷_) (proveFlatten xs)
\end{code}

\section{Polytypic packing and unpacking}

\begin{code}[hide]
module DivModScope where
  open import Data.Nat.DivMod
  fin2Bool : Fin 2 → Bool
  fin2Bool zero = false
  fin2Bool (suc zero) = true
  divMod2 : Nat → Nat × Bool
  divMod2 n with n divMod 2
  ... | result quotient remainder property = (quotient , fin2Bool remainder)
open DivModScope public
\end{code}

Let us now look at a more extended example: another canonical piece of the polytypism literature, namely polytypic \emph{packing}. By this we mean encoding a value of arbitrary type as a bitstream, in such a way as to be able (given information also about the type) to decode the bitstream back to the original data.

One can think of this as simple-minded data compression. For simplicity, we will encode to lists of bits and ignore the possible refinement of packing the bits into words.
We name the bits used to label left and right choices, and provide a case analysis for them:
% \footnote{TODO did use fin2Bool; but why be indirect? would everything still work with the opposite arrangement, changing only this?}
\begin{code}
leftBit rightBit : Bool
leftBit   = false
rightBit  = true

caseBit : Bool → a → a → a
caseBit b x y = if b then y else x
\end{code}
the idea being that
\begin{quote}%
% b = caseBit b leftBit rightBit
\AgdaBound{b}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{caseBit}\AgdaSpace{}%
\AgdaBound{b}\AgdaSpace{}%
\AgdaFunction{leftBit}\AgdaSpace{}%
\AgdaFunction{rightBit}%
\end{quote}
We provide primitives \AgdaFunction{toBits} and \AgdaFunction{fromBits} to convert between natural numbers and lists of booleans (making the simplifying assumption that all numbers are distinct to \AgdaFunction{bitWidth} bits---we could be cleverer about this):
\begin{code}
bitWidth : Nat
bitWidth = 4 -- we keep it small for testing

toBits : Nat → List Bool
toBits n = reverse (go bitWidth n) where
  go : Nat → Nat → List Bool
  go zero n     = []
  go (suc m) n  = let (q , r) = divMod2 n in r ∷ go m q

fromBits : List Bool → Nat
fromBits = foldl (λ n b → (2 *N n) +N (if b then 1 else 0)) 0
\end{code}
%fromBits = foldl (λ n b → if b then (2 *N n +N 1) else (2 *N n)) 0

Now, as a first attempt we might represent a packer for data as a function from that data to lists of bits. However, an unpacker would have to be more than simply a function in the opposite direction: we have to return the unused bits too, in order to be compositional; and we have to allow for failure, to make a total function. So we define the following:
\begin{code}
Unpacker : Set → Set
Unpacker a = List Bool → Maybe (a × List Bool)
\end{code}
In fact, that type supports a monad---the combination of the state monad transformer on bit-list state around the maybe monad, what would in Haskell be written $\mathit{StateT}\;[\mathit{Bool}]\;\mathit{Maybe}$:
\begin{code}
P : Set → Set
P = Unpacker
\end{code}
\begin{code}[hide]
module UnpackerMonad where
  returnUnpack : a → P a
  returnUnpack x = λ bs → just (x , bs)
  bindUnpack : P a → (a → P b) → P b
  bindUnpack p k bs = p bs >>=M λ (x , bs') → k x bs'
  mapUnpack : (a → b) → P a → P b
  mapUnpack f p = bindUnpack p (λ x → returnUnpack (f x))
  liftM2 : (a → b → c) → P a → P b → P c
  liftM2 op p q = bindUnpack p (λ x → mapUnpack (op x) q)
  join : P (P a) → P a
  join xss = bindUnpack xss id
  unpM : Monad P
  unpM = mkRawMonad P returnUnpack bindUnpack
\end{code}
It turns out to be convenient to define packer using the same type:
\begin{code}
Packer : Set → Set
Packer a = a → P ⊤
\end{code}
A packer will always succeed, and will produce rather than consume some bits. In that sense, the \AgdaFunction{P} monad is overkill---but it allows u now to think about composing packers and unpackers. Note that an unpacker \AgdaFunction{Unpacker}\AgdaSpace{}\AgdaBound{A} for some type \AgdaBound{A} is isomorphic to a function of type
\AgdaRecord{⊤}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaFunction{P}\AgdaSpace{}%
\AgdaBound{A},
which is nicely dual to the packer type
\AgdaBound{A}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaFunction{P}\AgdaSpace{}%
\AgdaRecord{⊤}.
%
(For more on this duality, see \cite{janssonjeuring2002a}.)

The stateful interface is provided by two operations:
\begin{code}[hide]
open UnpackerMonad public
instance
  dummy = unpM

\end{code}
\begin{code}
put : Packer (List Bool)
put bs' = λ bs → just (tt , bs')

get : Unpacker (List Bool)
get = λ bs → just (bs , bs)
\end{code}
But we will not need the full power of these two operations; we will use them only in restricted ways. For packers, we need only add some output:
\begin{code}
packerTell : Packer (List Bool)
packerTell bs = do
  bs' ← get
  put (bs ++ bs')
\end{code}
(for reasons that will become clear in due course, we prepend rather than append). In particular, here are primitive packers for naturals, booleans, and the unit type:
\begin{code}
packNat : Packer Nat
packNat n = packerTell (toBits n)

packBool : Packer Bool
packBool b = packerTell [ b ]

packUnit : Packer ⊤
packUnit tt = return tt
\end{code}
Note that \AgdaFunction{packUnit} is a no-op.
Primitive unpackers for naturals and units are similarly easy:
\begin{code}
unpackBool : Unpacker Bool
unpackBool = uncons

unpackUnit : Unpacker ⊤
unpackUnit = return tt
\end{code}
To unpack a natural, we read a chunk of input, then convert these bits to a number:
\begin{code}
unpackNat : Unpacker Nat
unpackNat = do
  xs ← get
  let (ys , zs) = splitAt bitWidth xs
  put zs
  return (fromBits ys)
\end{code}

\pagebreak[4] % \newpage
\subsection{Packing as a monadic catamorphism}

Now, to pack a structure of an inductive datatype, we will use a \emph{monadic catamorphism} \cite{Meijer&Jeuring95:Merging}, which is like the ordinary catamorphism except that the algebra argument and the catamorphism itself are \emph{Kleisli arrows}---that is, they have a monadic return type:
% "interleaved mutual" only needed when cases from the definitions are mixed
\begin{AgdaAlign}
\begin{code}
mutual
  cataM :  (f : Bifunctor) → ([[ f ]]B a b → P b) → [[ Fix f ]]F a → P b
\end{code}
We will return to the definition of \AgdaFunction{cataM} shortly; but let's first see how it is used.

We define three mutually recursive functions, packers respectively for a type, a functor, and a bifunctor, taking correspondingly many element packers as arguments:
\begin{code}
  packT  : (t : Type)       →                        Packer [[ t ]]T
  packF  : (d : Functor)    → Packer a →             Packer ([[ d ]]F a)
  packB  : (f : Bifunctor)  → Packer a → Packer b →  Packer ([[ f ]]B a b)
\end{code}
The packers for types each delegate to the appropriate primitive defined earlier:
\begin{code}
  packT NatTy n        = packNat n
  packT BoolTy b       = packBool b
  packT UnitTy tt      = packUnit tt
\end{code}
We only have one code for functors, interpreted as an inductive datatype, and this is where we use the monadic catamorphism:
\begin{code}
  packF (Fix f) p = cataM f (packB f p packUnit)
\end{code}
The catamorphism handles the recursive calls, so at the top level we do nothing (\AgdaFunction{packUnit}) for the recursive positions.

Finally, we have one fairly simple case per bifunctor:
\begin{code}
  packB (f * g)    p q ( x , y )  = do  packB g p q y
                                        packB f p q x
  packB (f + g)    p q (inj₁ x)   = do  packB f p q x
                                        packerTell [ leftBit ]
  packB (f + g)    p q (inj₂ y)   = do  packB g p q y
                                        packerTell [ rightBit ]
  packB (Const t)  p q            = packT t
  packB (d ● g)    p q            = packF d id ∘ pmap d (packB g p q)
  packB Par        p q            = p
  packB Rec        p q            = q
\end{code}
Recall that the primitive operations to write bits were defined to prepend to the list. We therefore specify that
for products, we pack the right then the left component of the pair; then the left component will appear first in the output. Similarly---and more importantly---for sums, we emit the discriminator bit after packing the payload.

Now back to the monadic catamorphism. This requires a \emph{distributive law} of the shape bifunctor over the monad---informally, this hoists the monad to the top, executing the computations for each of the recursive positions to make one composite computation collecting all the effects:
\begin{code}
  distr : (f : Bifunctor) → [[ f ]]B a (P b) → P ([[ f ]]B a b)
\end{code}
Then the catamorphism deconstructs the data, makes recursive calls on each of the children, collects all their effects, applies the algebra \AgdaBound{h}, and merges the effects of that:
%\footnote{TODO or we could use fix}
\begin{code}
  {-# TERMINATING #-}
  cataM f h (In xs) =  join (h <$> (distr f (fmap f id (cataM f h) xs)))
\end{code}
Note that the catamorphism is bottom up: the effects from children are incurred before those of the parent. This is why we defined the primitive packers to prepend bits instead of appending them: the encoding of the root of the data structure will end up at the start of the output list, conveniently for unpacking.

The last ingredient is the distributive law. This is in essence another polytypic program, with mutually recursive definitions for functors and bifunctors (types are not needed):
\begin{code}
  distrF  : (f : Functor)    → [[ f ]]F  (P a)        → P ([[ f ]]F  a)
  distrB  : (f : Bifunctor)  → [[ f ]]B  (P a) (P b)  → P ([[ f ]]B  a b)

  distrF (Fix f) (In xs)    = In <$> (distrB f (fmap f id (distrF (Fix f) ) xs))

  distrB (f * g) (xs , ys)  = liftM2 _,_ (distrB f xs) (distrB g ys)
  distrB (f + g) (inj₁ x)   = inj₁ <$> distrB f x
  distrB (f + g) (inj₂ y)   = inj₂ <$> distrB g y
  distrB (Const t) x        = return x
  distrB (d ● g) xs         = distrF d (pmap d (distrB g) xs)
  distrB Par x              = x
  distrB Rec x              = x
\end{code}
The variant we actually use is for bifunctors, but with pure values in the parameter positions, so we must first inject these into the monad:
\begin{code}
  distr f = distrB f ∘ fmap f return id
\end{code}
\end{AgdaAlign}
For example, with bit width set to 4 for brevity, the expression
\begin{code}[hide]
exampleLHS exampleRHS : Maybe (⊤ × List Bool)
exampleLHS  =
\end{code}
\begin{code}
  packF ListC (packT NatTy) (toMyList (1 ∷ 2 ∷ 3 ∷ [])) []
\end{code}
reduces to the expression in \cref{fig:packEx}.

\begin{figure}[hbtp]
\begin{code}[hide]
exampleRHS  =
\end{code}
\begin{code}
  just (tt ,
    true ∷
    false ∷ false ∷ false ∷ true ∷    -- toBits 1
    true ∷
    false ∷ false ∷ true ∷ false ∷    -- toBits 2
    true ∷
    false ∷ false ∷ true ∷ true ∷     -- toBits 3
    false ∷ [])
\end{code}
\caption{The list of bits resulting from packing 1, 2, 3 is
\AgdaInductiveConstructor{true} to indicate a cons cell,
then four bits representing the number \AgdaNumber{1},
then similarly for the next two elements,
then \AgdaInductiveConstructor{false} to indicate a nil cell.}
\label{fig:packEx}
\end{figure}


\subsection{Unpacking as a monadic anamorphism}

Let us now turn to unpacking. Being the inverse of packing, it will use the dual pattern: a \emph{monadic anamorphism}, which is again like the ordinary anamorphism only where the coalgebra and the anamorphism itself are Kleisli arrows:
% interleaved mutual not needed
\begin{AgdaAlign}
\begin{code}
mutual
  {-# TERMINATING #-}
  anaM :  (f : Bifunctor) → (b → P ([[ f ]]B a b)) → b → P ([[ Fix f ]]F a)
\end{code}
Unpacking is again defined in terms of three mutually recursive functions, unpackers respectively for types, functors, and bifunctors, each with the corresponding number of element unpackers as arguments:
\begin{code}
  unpackT  :  (t : Type)       →         Unpacker [[ t ]]T
  unpackF  :  (d : Functor)    →
              Unpacker a →               Unpacker ([[ d ]]F a)
  unpackB  :  (f : Bifunctor)  →
              Unpacker a → Unpacker b →  Unpacker ([[ f ]]B a b)
\end{code}
For the base types we defer to the earlier primitives:
\begin{code}
  unpackT NatTy          = unpackNat
  unpackT BoolTy         = unpackBool
  unpackT UnitTy         = unpackUnit
\end{code}
For the sole functor code, we use the anamorphism:
\begin{code}[hide]
--  unpackF (Fix f) p  = In <$> unpackB f p (unpackF (Fix f) p)
--  unpackF (Fix f) p  = fix (λ q → In <$> unpackB f p q)
--  unpackF (Fix f) p  = anaM f (distr' f) (λ _ → unpackB f p (unpackT UnitTy)) _
\end{code}
\begin{code}
  unpackF (Fix f) u  = anaM f (λ _ → unpackB f u unpackUnit) _
\end{code}
Note that the `seed' of the anamorphism is the unit type: all the information driving the computation comes from the list of booleans, encoded in the monad. So the bound variable of the lambda is irrelevant, and the initial seed of the anamorphism can be inferred. As with packing, the anamorphism handles the recursive calls, so at the top level we need do nothing for the recursive positions (\AgdaFunction{unpackUnit}, another no-op).

And finally, there is one fairly simple case per bifunctor:
\begin{code}
  unpackB (f * g) u v    = liftM2 _,_ (unpackB f u v) (unpackB g u v)
  unpackB (f + g) u v    = do  b ← unpackBool
                               caseBit b
                                 (inj₁ <$> unpackB f u v)
                                 (inj₂ <$> unpackB g u v)
  unpackB (Const x) u v  = unpackT x
  unpackB (d ● g) u v    = unpackF d (unpackB g u v)
  unpackB Par u v        = u
  unpackB Rec u v        = v
\end{code}
For products, we unpack the left then the right components; for sums, we consume one discriminator bit in order to decide which branch to take.

Now back to the monadic anamorphism. This applies the coalgebra to the seed, makes recursive calls to generate each of the children, collects all their effects, merges the effects from the coalgebra and the recursive calls, then wraps the result up in the constructor:
%\footnote{TODO apparently the same distributor works?}
% --  anaM f h y = In <$> join (distr' f <$> (fmap f id (anaM f h) <$> h y))
\begin{code}
  anaM f h y = In <$> join (distr f <$> (fmap f id (anaM f h) <$> h y))
\end{code}
\end{AgdaAlign}

To illustrate the round trip, it should be the case that whatever value we take, if we pack it in front of any bit sequence then unpack the resulting sequence, that composition should succeed, and should return the original value and sequence:
\begin{code}
packUnpack : { a : Set } → Packer a → Unpacker a → a → List Bool → Set
packUnpack p u x bs = (p x >> u) bs ≡ just (x , bs)
\end{code}
% packUnpack p u x bs = (p x >>= λ _ → u) bs ≡ just (x , bs)
(recall that a packer returns unit, which we then discard by \AgdaOperator{\AgdaPostulate{>>}}).
Then we can instantiate this scheme for the types, functors, and bifunctors in our universe:
\begingroup
\def\AgdaSpace{\hskip3pt}
\begin{code}
packUnpackT  :  (a : Type) → [[ a ]]T →                           List Bool → Set
packUnpackT  a = packUnpack (packT a) (unpackT a)

packUnpackF  :  (d : Functor) → (a : Type) → [[ d ]]F [[ a ]]T →  List Bool → Set
packUnpackF  d a = packUnpack  (packF    d (packT a)    )
                               (unpackF  d (unpackT a)  )

packUnpackB  :  (f : Bifunctor) → (a b : Type) →
                [[ f ]]B [[ a ]]T [[ b ]]T →                      List Bool → Set
packUnpackB  f a b = packUnpack  (packB    f (packT a)    (packT b)    )
                                 (unpackB  f (unpackT a)  (unpackT b)  )
\end{code}
\endgroup
For example, we can check the round trip property on a list of three naturals:
\begin{code}
packUnpackList :  ∀ (bs : List Bool) →
                  packUnpackF ListC NatTy (toMyList (1 ∷ 2 ∷ 3 ∷ [])) bs
packUnpackList bs = refl
\end{code}
The value we give to \AgdaFunction{packUnpackList} is simply \AgdaInductiveConstructor{refl}, which indicates that (and is only type correct when) the two sides of the equivalence are definitionally equal.
\begin{code}[hide]
-- Three groups of tests: for some more Type, Functor, Bifunctor cases.
checkPackNat : ∀ bs → let n = 13     in  packUnpackT NatTy   n bs
checkPackNat bs = refl
checkPackBool : ∀ bs → let b = true  in packUnpackT BoolTy  b bs
checkPackBool bs = refl
checkPackUnit : ∀ bs → let x = tt    in packUnpackT UnitTy  x bs
checkPackUnit bs = refl

checkPackNil : ∀ bs → let xs = []       in packUnpackF ListC NatTy (toMyList xs) bs
checkPackNil bs = refl
checkPackCons : ∀ bs → let xs = 1 ∷ []  in packUnpackF ListC NatTy (toMyList xs) bs
checkPackCons bs = refl

checkPackProd : ∀ bs → let xy = (13 , true)  in packUnpackB (Par * Rec) NatTy BoolTy xy bs
checkPackProd bs = refl

checkPackSumL : ∀ bs → let x = inj₁ 13       in packUnpackB (Par + Rec) NatTy BoolTy x bs
checkPackSumL bs = refl
checkPackSumR : ∀ bs → let y = inj₂ true     in packUnpackB (Par + Rec) NatTy BoolTy y bs
checkPackSumR bs = refl

checkPackConst : ∀ bs → let x = 13           in packUnpackB (Const NatTy) NatTy BoolTy x bs
checkPackConst bs = refl

checkPackComp : ∀ bs → let x = myList        in packUnpackB (ListC ● Par) NatTy BoolTy x bs
checkPackComp bs = refl
\end{code}


\section{Discussion}

The technique we have used of identifying an algebraic datatype of \emph{codes} for types drawn from some \emph{universe} is a standard pattern in dependently typed programming. It is an instance in microcosm of the ``formulation \'a la Tarski'' that Martin-L{\"o}f \cite{Martin-Lof84:Intuitionistic} used in macrocosm to construct a universe of discourse for intuitionistic type theory. Another way of looking at it is specifying an embedded domain specific language for types (namely the codes), and semantics by way of a shallow embedding into the host language (namely the interpretation) \cite{Gibbons&Wu2014:Folding}.

This paper is literate Agda, although some of the gory details have been elided for presentation purposes. The full story can be seen in the source, which is available on GitHub~\cite{PolyP30-github}, and typechecks at least with version~2.7.0.1 of Agda and version~2.2 of the Agda standard library.

We have seen that the polytypic programming features that Johan pioneered with PolyP can be done nowadays as `mere programming', given a sufficiently rich language---in particular, a dependently typed one. We have chosen Agda, but Idris would work just as well.

Even Haskell is almost powerful enough these days: much of the PolyP functionality was achieved in Haskell already in 2003 \cite{DBLP:conf/ifl/NorellJ03}. But dependent types have the additional advantage that proofs become part of the language. We have exploited this briefly above: the code contains some unit tests, which are run as part of typechecking. And indeed we have exploited these tests while writing the programs: although many silly errors are ruled out by the types, it is in particular still possible to write out the wrong bit sequences.

But a powerful and informative type system like Agda's is not just there to prevent accidents. It is also hugely valuable when it comes to writing the programs in the first place: the type specifies much about the program, so with suitable interaction between the type checker and the editor---for example, in the Agda mode for Emacs---much of the program can be written automatically. Some values can be inferred; case analyses can be automatically generated; programs can be typechecked while still containing holes, and these holes can be explored with information about the goal type and the variables in scope.

Programming in this type-driven style in many ways feels like a text-based adventure game. You find yourself in a hole, with various objects at your disposal, and you have to find a way out. You keep getting sent on side-quests. Sometimes it feels like you are fighting the typechecker; but sometimes it feels like the universe is on your side, and the obstacles are magically eliminated. In recent years, Johan's research interests have shifted from programming languages to technology for education, including `serious games': perhaps Johan can see scope for closing the circle by bringing the two back together?

\bibliographystyle{splncs04}
\bibliography{polyp}

%\newpage
%\appendix
%See OppositeDistributor.lagda
%See PackerDirectly.lagda
%See Coden.lagda
%See FlattenAttempt.lagda
%See Flatten.lagda
%See AnotherGoAtFlattening.lagda
\end{document}
