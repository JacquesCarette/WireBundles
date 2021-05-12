An exploration of bundling wires together, with multiplicity. Wires are imagined to
be not-necessarily-physical carries of indivisible information. So here the ``types''
will not be inspectable.

Everything will be done in Agda, for greater certainty.
\begin{code}
module WireBundles where
\end{code}

The heart of the exploration involves looking at different concepts of multiplicity.
Thus we need access to various notions of numbers.
\begin{code}
open import Data.Nat as ℕ
open import Data.Fin as F
open import Data.Integer as ℤ
\end{code}

\section{Two wires}

Let us start the exploration of the simplest case, when we have just two wires.
We do, however, need to work with arbitrary types, so let's use |A|, |B| and |C|
for these.  We work without worrying about universe levels at the moment.

\begin{code}
data Ty : Set where
  A B C : Ty
\end{code}

In practice, we'd want to also define |El : Ty → Set| to associate
actual types to these names, but here let's just postulate it.
\begin{code}
postulate
  El : Ty → Set
\end{code}

So then we can have a concrete bundle of two wires:
\begin{code}
2-Bundle : Set
2-Bundle = Fin 2 → Ty

AB : 2-Bundle
AB zero        = A
AB (suc zero)  = B
\end{code}

There is no visible concept of multiplicity in the above. It is because it
is assumed to be $1$ for each element of |Fin 2|.

We want to actually associate a multiplicity to each wire in a bundle,
as well as some constraints on it.  For the constraints, it will be
very useful to have a proof-relevant version of addition~\cite{?}. -- Conor via Uma Z.

\begin{code}
data _+_==_ : ℕ → ℕ → ℕ → Set where
  0+x : {x : ℕ} → 0 + x == x
  x'+y : {x y : ℕ} → (ℕ.suc x) + y == ℕ.suc (x ℕ.+ y)
\end{code}

Let's consider the following constraint construction:
\begin{code}
record _++_ (X Y : Ty) : Set where
  field
    mult : Fin 2 → Fin 2
    just-one : toℕ (mult zero) + toℕ (mult (F.suc zero)) == ℕ.suc zero
  bundle : 2-Bundle
  bundle zero = X
  bundle (suc zero) = Y

open _++_
\end{code}
The three components give us a pair of types, a |0-1| multiplicity for
each component, and the constraint that this function sums to 1.

We also need to define what an \emph{element} of such a type is.
\begin{code}
elem-++ : {X Y : Ty} → (x : X ++ Y) → (i : Fin 2) → El (bundle x i)
elem-++ xx i = {!!}
\end{code}
