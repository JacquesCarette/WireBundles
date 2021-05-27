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

We'll also show that we can build certain type constructors.
\begin{code}
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Function.Bundles
open import Relation.Binary.PropositionalEquality
  using (inspect; refl; [_]; _≡_)
\end{code}

We'll use some variables as natural numbers frequently, so
\begin{code}
private
  variable
    i j k l : ℕ
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
  zer   :            0         + 0       == 0
  left  : i + j == k → ℕ.suc i + j       == ℕ.suc k
  right : i + j == k → i       + ℕ.suc j == ℕ.suc k
\end{code}

A multiplicity function is then one that associates a |ℕ| to
each wire, i.e. |Fin 2 → ℕ|.  We could start with multiplicities
in a smaller domain (like |Fin 2|), but this turns out to be
quite awkward.
\begin{code}
mult-2 : Set
mult-2 = Fin 2 → ℕ
\end{code}

We don't want
any function to count as a multiplicity function. Let's consider
a first one that is constrained to sum to one.

\begin{code}
add-to-one : mult-2 → Set
add-to-one m = m zero + m (F.suc zero) == 1
\end{code}

Furthermore, we want to associate a number to the members of |add-to-one|, as follows:
\begin{code}
count-m2 : {i j : ℕ} → i + j == 1 → Fin 2
count-m2 (left zer) = zero
count-m2 (right zer) = F.suc zero
\end{code}

Given a multiplicity and a |2-Bundle|, we can associate type:
\begin{code}
elem-2-1 : mult-2 → 2-Bundle → Set
elem-2-1 m t = Σ (add-to-one m) (λ pf → El (t (count-m2 pf)))
\end{code}
We also have a 'getter' for that type, by construction:
\begin{code}
get-elem-2-1 : {m : mult-2} {t : 2-Bundle} → (e : elem-2-1 m t) → El (t (count-m2 (proj₁ e)))
get-elem-2-1 = proj₂
\end{code}

What we have done is found an arithmetic encoding of a union type. We can first do
the simple part on just |2-Bundle|. This is an encoding of union as a W type.
\begin{code}
inject₂ : (t : 2-Bundle) → Set
inject₂ t = Σ (Fin 2) (λ pos → El (t pos))

sum : 2-Bundle → Set
sum t = El (t zero) ⊎ El (t (F.suc zero))

equiv : (t : 2-Bundle) → inject₂ t ↔ sum t
equiv t = mk↔′ Σ⇒⊎ ⊎⇒Σ left-inv right-inv
  where
  Σ⇒⊎ : inject₂ t → sum t
  Σ⇒⊎ (zero , t) = inj₁ t
  Σ⇒⊎ (F.suc zero , t) = inj₂ t
  ⊎⇒Σ : sum t → inject₂ t
  ⊎⇒Σ (inj₁ x) = zero , x
  ⊎⇒Σ (inj₂ y) = F.suc zero , y
  left-inv : (x : sum t) →  Σ⇒⊎ (⊎⇒Σ x) ≡ x
  left-inv (inj₁ x) = refl
  left-inv (inj₂ y) = refl
  right-inv : (x : inject₂ t) → ⊎⇒Σ (Σ⇒⊎ x) ≡ x
  right-inv (zero , snd) = refl
  right-inv (F.suc zero , snd) = refl
\end{code}

But what we really want to show is that this is true for |elem-2-1| as well.

It is convenient to first bundle up a multiplity function with a witness
that it adds to one:
\begin{code}
record mult-+ : Set where
  constructor m2
  field
    mult : mult-2
    +1 : add-to-one mult
\end{code}

The problem is that the choice of multiplicity function matters. The point is that
|inject₂ t| maps directly to |A ⊎ B|, but not to |B ⊎ A|. Both are equivalent, but
the choice of equivalence matters. In other words |inject₂ t| does not contain
quite enough information.
\begin{code}
21↔inj₂ : {m : Σ mult-2 add-to-one} {t : 2-Bundle} → elem-2-1 (proj₁ m) t ↔ inject₂ t
21↔inj₂ {m , ≡1} {t} = mk↔′ e21⇒inj₂ inj₂⇒e21 {!!} {!!}
  where
  e21⇒inj₂ : elem-2-1 m t → inject₂ t
  e21⇒inj₂ (fst , snd) with m zero | m (F.suc zero)
  e21⇒inj₂ (right fst , snd) | zero | ℕ.suc zero = count-m2 (right fst) , snd
  e21⇒inj₂ (right () , snd) | zero | ℕ.suc (ℕ.suc ww)
  e21⇒inj₂ (left zer , snd) | ℕ.suc .0 | .0 = zero , snd

  inj₂⇒e21 : inject₂ t → elem-2-1 m t
  inj₂⇒e21 (zero , snd) = ≡1 , {!!}
  inj₂⇒e21 (F.suc fst , snd) = {!!}
\end{code}
