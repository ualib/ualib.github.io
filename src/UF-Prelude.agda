--FILE: UF-Prelude.agda
--BLAME: williamdemeo@gmail.com
--DATE: 21 Apr 2020
--UPDATE: 23 May 2020
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ 
--       In particular, the quoted comments below, along with sections of code to which those comments refer, are due to Martin Escardo.
--       Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

--open import Relation.Unary using (Pred; _∈_; _⊆_)
--open import Data.Product  renaming (_,_ to _؛_) using (∃) -- ; _,_; _×_;Σ-syntax) public renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)

module UF-Prelude where

--------------------------------------------------------------------------------
--TYPE UNIVERSES.
--(cf https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#universes )

open import Agda.Primitive public
 renaming (
            Level to Universe -- We speak of universes rather than of levels.
           ; lzero to 𝓤₀     -- Our first universe is called 𝓤₀
           ; lsuc to _⁺       -- The universe after 𝓤 is 𝓤 ⁺
           ; Setω to 𝓤ω      -- There is a universe 𝓤ω strictly above 𝓤₀, 𝓤₁, ⋯ , 𝓤ₙ, ⋯
           )
 using    (_⊔_)               -- Least upper bound of two universes, e.g. 𝓤₀ ⊔ 𝓤₁ is 𝓤₁

Type = λ ℓ → Set ℓ

_̇   : (𝓤 : Universe) → Type (𝓤 ⁺)
𝓤 ̇  = Type 𝓤

infix  1 _̇
--The ̇ operator maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`,
--a.k.a. Type (𝓤 ⁺). That is, `𝓤 ̇` is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`.
--The level lzero is renamed 𝓤₀, so `𝓤₀ ̇` is an alias for Set lzero. (This corresponds to `Sort 0` in Lean.)
--Thus, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we denote by `𝓤₀ ⁺ ̇`
--
-- +----------------------|-------------------------------|------------------------------+
-- | Agda                 | MHE Notation                  |        Lean analog           |
-- +----------------------|-------------------------------|------------------------------+
-- |  ``Level``           |   ``Universe``                |  ``universe``                |
-- |   ``lzero``          |   ``𝓤₀``                     |  ``0 : universe``            |
-- |  ``Set lzero``       |   ``𝓤₀ ̇`` ( = ``Type 𝓤₀``) |  ``Sort 0``                  |
-- |   ``lsuc lzero``     |   ``𝓤₀ ⁺``                   |  ``1 : universe``            |
-- | ``Set (lsuc lzero)`` |   ``𝓤₀ ⁺ ̇``                 |  ``Sort 1 = Type = Type 0``  |
-- +----------------------|-------------------------------|------------------------------+
--  (Table: translation from standard Agda syntax into MHE notation and Lean syntax)

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
𝓤₃ = 𝓤₂ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : {𝓤 : Universe} (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤

--"We will refer to universes by letters 𝓤,𝓥,𝓦,𝓣 (type these with, resp, ``\MCU``, ``\MCV``, etc)"
variable
  𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓠 𝓡 𝓢 𝓣 𝓤 𝓥 𝓦 𝓧 : Universe

--The one-element type (type `\b1` for 𝟙, and `\*` for ⋆)
data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

--"Here's a mechanism to prove that all points of the type `𝟙` satisfy a given property `A`.
-- The property is a function `A : 𝟙 → 𝓤` for some universe `𝓤`.
𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A A⋆ ⋆ = A⋆

-- IMPORTANT: Instead of supplying an arbitrary `x : 𝟙`, we give `⋆` and Agda accepts this because,
-- from the definition of `𝟙`, `⋆` is the only element of the type `𝟙`. This is *pattern matching*.
𝟙-recursion : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆

data 𝟘 : 𝓤₀ ̇ where
-- no constructors (no way to construct an element of type 𝟘)

𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
𝟘-induction A () -- i.e., "vacuously true"

-- The *unique* function from `𝟘` to any type is a particular case of `𝟘-induction`.
𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

--"We will use the following categorical notation for `𝟘-recursion`:
!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion

--"We give the two names `is-empty` and `¬` to the same function.
is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘
{- "...a type is empty precisely when we have a function to the empty type....
    With univalence we will be able to show ...what amounts to `(𝟘 → 𝟙) ≡ 𝟙`,
    ...there is precisely one function `𝟘 → 𝟙`, namely the (vacuous) function." -}

--"The type `ℕ` of natural numbers.  (The def is similar but not quite the same as the one via Peano Axioms.)
data ℕ : 𝓤₀ ̇ where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

--"In the following, the type family `A` can be seen as playing the role of a property of elements of `ℕ`,
-- except that it doesn't need to be necessarily subsingleton valued. When it is, the *type* of the function
-- gives the familiar principle of mathematical induction for natural numbers, whereas, in general, its
-- definition says how to compute with induction.
ℕ-induction : (A : ℕ → 𝓤 ̇)
 →             A 0                          -- base step     : A 0 (holds)
 →            ((n : ℕ) → A n → A (succ n)) -- inductn. step : ∀n, if A n, then A (succ n)
              ----------------------------- -- ------------------------------------------
 →            (n : ℕ) → A n                -- conclusion    : ∀n, A n

ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h zero = a₀
  h (succ n) = f n (h n)

--"`ℕ-induction` is the dependently typed version of primitive recursion; the non-dependently typed version is
ℕ-recursion : (X : 𝓤 ̇)  →  X  →  (ℕ → X → X)
              --------------------------------------
 →                     ℕ → X
ℕ-recursion X = ℕ-induction λ _ → X

--"The following special case occurs often
-- (and is related to the fact that `ℕ` is the initial algebra of the functor `𝟙 + (-)`)
ℕ-iteration : (X : 𝓤 ̇)
 →            X    →   (X → X)
             --------------------
 →              ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

--"As another example, we define the less-than-or-equal relation by nested induction, on the first argument
--and then the second, but we use pattern matching for the sake of readability."
module ℕ-order where
 _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
 0 ≤ y = 𝟙
 succ x ≤ 0 = 𝟘
 succ x ≤ succ y = x ≤ y
 x ≥ y = y ≤ x
 infix 10 _≤_
 infix 10 _≥_

------------------------------------------------------------------------------------------------
--"The identity function (in two versions with different implicit arguments)
id : {X : 𝓤 ̇} → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇) → X → X
𝑖𝑑 X = id {X = X}


------------------------------------------------------------------------------------------------
-- The identity type former `Id`, also written `_≡_`
-- see: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#identitytype
infix 0 Id
data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇ where
 refl : (x : X) → Id X x x

--The least reflexive relation on the type `X`.
_≡_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≡ y = Id _ x y --( `_` means let Agda to infer which type we are talking about)
infix   0 _≡_

≡-sym : {X : 𝓤 ̇ }{x y : X} → x ≡ y → y ≡ x
≡-sym (refl _) = refl _

𝕁 : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
 →   ((x : X) → A x x (refl x))
 →   (x y : X) (p : x ≡ y) → A x y p

𝕁 X A f x x (refl x) = f x

-- ℍ : {X : 𝓤 ̇} (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇) → B x (refl x)
--  → (y : X) (p : x ≡ y) → B y p
-- ℍ x B b x (refl x) = b

≡-induction : (X : 𝓤 ̇)(A : (x y : X) → x ≡ y → 𝓥 ̇)
 →            ((x : X) → A x x (refl x))
 →            (x y : X) (p : x ≡ y) → A x y p
≡-induction = 𝕁 -- alias

-------------------------------------------------------------------------------------------------------
-- SUMS AND PRODUCTS.
--The binary sum type constructor `_+_`.  The "disjoint sum" (or "direct sum") of the types `X` and `Y`.
--Elements of `X + Y` have the forms `inl x` and `inr y`, with `x : X` and `y : Y`.
infixr 20 _+_
data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 inl : X → X + Y
 inr : Y → X + Y

--"To prove a property `A` of the sum holds for all `z : X + Y`, it is enough to prove that `A (inl x)`
-- holds for all `x : X` and that `A (inr y)` holds for all `y : Y`. This amounts to definition by cases:
+-induction : {X : 𝓤 ̇}{Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇)
 →            ((x : X) → A (inl x))  →  ((y : Y) → A (inr y))
             --------------------------------------------------
 →                      (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-intro : {X : 𝓤 ̇}{Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇)
 →        ((x : X) → A (inl x))  →  ((y : Y) → A (inr y))
          --------------------------------------------------
 →                   (z : X + Y) → A z
+-intro = +-induction -- alias

+-recursion : {X : 𝓤 ̇}{Y : 𝓥 ̇} {A : 𝓦 ̇}
 →            (X → A)  →  (Y → A)
              --------------------
 →                X + Y → A
+-recursion{A = A} = +-induction λ _ → A

--"... `_+_` is used to construct mathematical objects. For example, we can define a two-point type:
𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

--"We can name the left and right points as follows, using patterns, so that they can be used in pattern matching:
pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

--"We can define induction on 𝟚 directly by pattern matching:
𝟚-induction : (A : 𝟚 → 𝓤 ̇) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

--"Or we can prove it by induction on `_+_` and `𝟙`:
𝟚-induction' : (A : 𝟚 → 𝓤 ̇) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A (𝟙-induction (λ z → A (inl z)) a₀) (𝟙-induction (λ z → A (inr z)) a₁)

-- -------------------------------------------------------------------------------------
--`Σ` types
--"We can construct the `Σ` type former as follows in Agda:
infixr 50 _,_
record Σ {𝓤 𝓥} {X : 𝓤 ̇}(Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 constructor
  _,_
 field
  x : X
  y : Y x

--"This says we are defining a binary operator `_,_` to construct the elements of this type as `x , y`.
-- The definition says that an element of `Σ Y` has two `fields`, giving the types for them."

pr₁ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → Σ Y → X
pr₁ (x , y) = x

∣_∣ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → Σ Y → X
∣ x , y ∣ = x

pr₂ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

∥_∥ : {X : 𝓤 ̇}{Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
∥ x , y ∥ = y

--(paraphrasing MHE) Syntax to be able to write `Σ x ꞉ X , y` instead of `Σ λ(x ꞉ X) → y`.
-- For this, first define a version of Σ that makes the index type explicit.
infixr -1 -Σ
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
syntax -Σ X (λ x → y) = Σ x ꞉ X , y -- type `꞉` as `\:4`

--!!!WARNING!!!  "꞉" in the above syntax definition is not the same as ":", even though they may look the same.
-- To produce the Σ x ꞉ A , b used above, you must type the "꞉" symbol as `\:4` in the emacs Agda mode.

--"To prove that `A z` holds for all `z : Σ Y`, for a given property `A`, we just prove that we have `A (x , y)`
-- for all `x : X` and `y : Y x`.  This is called `Σ` induction or `Σ` elimination (or `uncurry`).
Σ-induction : {X : 𝓤 ̇}{Y : X → 𝓥 ̇}{A : Σ Y → 𝓦 ̇}
 →            ((x : X)(y : Y x) → A (x , y))
 --------------------------------------------------
 →            ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇}{Y : X → 𝓥 ̇}{A : Σ Y → 𝓦 ̇}
 →      (((x , y) : Σ Y ) → A (x , y))
       ---------------------------------------------
 →      ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)
-- Σ-inv = curry

--Special case (where the type Y doesn't depend on X).
infixr 30 _×_
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

{-(paraphrasing MHE)
  The general type `Σ (x : X) , A x`---with `X` a collections of objects and `A : X → 𝓤 ̇` (e.g., a prop)
  represents *designated* existence---i.e., there is a designated `x : X` with `A x`. An inhabitant of this type
  is a pair `(x , p)`, with `x : X` and `p : A x`. Here p may be viewed as a proof that (the proposition) A x holds.

  We could also consider an "unspecified" existence `∃ (x : X), A x`, obtained by a sort of quotient of
  `Σ (x : X), A x`, denoted by `∥ Σ (x : X), A x ∥`, that identifies all the elements of the type `Σ (x : X), A x`
  in a single equivalence class, called its "subsingleton truncation."
  (or "truth value truncation" or "propositional truncation").

  Another reading of `Σ (x : X), A x` is as the type (or "set") of those `x : X` satisfying `A x`, similar to the
  set denoted (in "set-builder" notation) by `{ x ∈ X | A x }`... but...
  WARNING: if there is more than one element in the type `A x`, then `x` will occur more than once in this type.
  More precisely, for `a₀ a₁ : A x` we have inhabitants `(x , a₀)` and `(x , a₁)` of the type `Σ (x : X), A x`.
  If we don't want that, we have to either ensure that the type `A x` has at most one element for every `x : X`,
  or instead consider the truncated type ⌞ A x ⌟ and write `Σ (x : X), ⌞ A x ⌟`.

  N.B. MHE uses ∥ A x ∥ to denote the truncation of A x, but we are sometimes using ∥ p ∥ for the second projection
  of p, so we prefer to denote truncation with the floor symbols ⌞ and ⌟ (typed with `\c3` and `\c4`, resp).

  Example. The image of a function `f : X → Y` will be defined as `Σ (y : Y), ⌞ Σ (x : X), f x ≡ y ⌟`,
  (i.e., those `y : Y` for which ∃ an unspecified `x : X` with `f x ≡ y`. (N.B. this *doesn't erase* the
  witness `x : X`.) -}

-------------------------------------
-- `Π` types.
--"...introduce the notation `Π` for them, similar to that for `Σ`:
Π : {X : 𝓤 ̇} (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y
infixr -1 -Π
syntax -Π A (λ x → b) = Π x ꞉ A , b

--Dependent function composition.
infixl 70 _∘_ -- NOTATION. type ∘ as `\circ`
_∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇}
 →    ((y : Y) → Z y)  →  (f : X → Y)  →  (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

--"The following functions are sometimes useful when... using implicit arguments, in order to recover them
-- explicitly without having to list them as given arguments:
domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} _ = X

codomain : {X : 𝓤 ̇}{Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} _ = Y

type-of : {X : 𝓤 ̇} → X → 𝓤 ̇
type-of {𝓤} {X} x = X

-----------------------------------------------------------------------------------------------
--TRANSPORT.
{-"Before embarking on the development of UF within our spartan MLTT, we pause to discuss some basic
   examples of maths in Martin-Löf tt." -}

--"Transport along an identification.
transport : {X : 𝓤 ̇} (F : X → 𝓥 ̇) {s t : X}  →  s ≡ t  →  F s → F t
transport F (refl s) = 𝑖𝑑 (F s)

--              F
--         s ------→ Fs
--         ∥          ∥
-- refl s  ∥          ∥ transport
--         ⇓         ⇓
--         t ------→ Ft
--              F

--"We can equivalently define transport using `𝕁` as follows:"
transport𝕁 : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x y : X} → x ≡ y  →  A x → A y
transport𝕁{𝓤}{𝓥}{X} A {x} {y} = 𝕁 X (λ x₁ y₁ _ → A x₁ → A y₁) (λ x₁ → 𝑖𝑑 (A x₁)) x y

--"In the same way `ℕ`-recursion can be seen as the non-dependent special case of `ℕ`-induction, the following
-- transport function can be seen as the non-dependent special case of the `≡`-induction principle `ℍ` with some
-- of the arguments permuted and made implicit:
-- nondep-ℍ : {X : 𝓤 ̇} (x : X) (A : X → 𝓥 ̇) → A x → (y : X) → x ≡ y → A y
-- nondep-ℍ x A = ℍ x (λ y _ → A y)

-- transportℍ : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y : X} → x ≡ y  →  A x  →  A y
-- transportℍ A {x} {y} x≡y v = nondep-ℍ x A v y x≡y

-- --"All of the above transports coincide:
-- transport-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇) {x y : X} (p : x ≡ y)
--  → (transportℍ A p ≡ transport A p) × (transport𝕁 A p ≡ transport A p)
-- transport-agreement  A (refl x) = refl (transport A (refl x)) , refl (transport A (refl x))

--"The following is for use when we want to recover implicit arguments without mentioning them.
lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤}{X}{x}{y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤}{X}{x}{y} p = y

---------------------------------------------------------------------------------------------------
--"Composition of identifications. Given two identifications `p : x ≡ y` and `q : y ≡ z`, we can compose them
-- to get an identification `p ∙ q : x ≡ z`. This can also be seen as transitivity of equality.  Because the
-- type of composition doesn't mention `p` and `q`, we can use the non-dependent version of `≡`-induction.
_∙_ : {X : 𝓤 ̇}{s t u : X} → s ≡ t → t ≡ u → s ≡ u
p ∙ q = transport ( lhs p ≡_ ) q p
infixl 30 _∙_                                            -- NOTATION: type ∙ using `\.`

--"...we are considering the family `F a = (s ≡ a)`, and using the identification `q : t ≡ u` to transport `F t` to `F u`, that is `s ≡ t` to `s ≡ u`.

--EXERCISE. Can you define an alternative version that uses `p` to transport. Do the two versions give equal results?
-- SOLUTION. Use the family F a = (a ≡ u) and use the identification p : s ≡ t to transport F t to F s.
_⋆'_ : {X : 𝓤 ̇}{s t u : X} → s ≡ t → t ≡ u → s ≡ u
p ⋆' q = transport (_≡ rhs q) (≡-sym p) q

--"When writing `p ∙ q`, we lose information on the lhs and rhs of the identifications `p : s ≡ t` and `q : t ≡ u`,
-- which makes some definitions hard to read. We now introduce notation to be able to write e.g.
-- s ≡⟨ p ⟩ t ≡⟨ q ⟩ u ∎ as a synonym of the expression `p ∙ q` with some of the implicit arguments of `_∙_` made
-- explicit. We have one ternary mixfix operator `_≡⟨_⟩_` and one unary `postfix` operator `_∎`.
infixr  0 _≡⟨_⟩_
_≡⟨_⟩_ : {X : 𝓤 ̇} (s : X) {t u : X} → s ≡ t → t ≡ u → s ≡ u
s ≡⟨ p ⟩ q = p ∙ q

infix   1 _∎
_∎ : {X : 𝓤 ̇} (s : X) → s ≡ s
s ∎ = refl s

--"Given an identification, we get an identification in the opposite direction:
infix  40 _⁻¹
_⁻¹ : {X : 𝓤 ̇} → {s t : X} → s ≡ t → t ≡ s
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))

--With this MHE defines an alternative of identification composition and shows it agrees with the previous one.
_∙'_ : {X : 𝓤 ̇} {s t u : X} → s ≡ t → t ≡ u → s ≡ u
p ∙' q = transport ( _≡ rhs q ) ( p ⁻¹ ) q

∙agreement : {X : 𝓤 ̇}{s t u : X} (p : s ≡ t) (q : t ≡ u) → p ∙' q ≡ p ∙ q
∙agreement (refl s) (refl s) = refl (refl s)

--"But `refl t` is a definitional neutral element for one of them on the right and for the other one on the left,
-- (i.e., `p ∙ refl t = p` and `refl t ∙' q = q`) which can be checked as follows:
rdnel : {X : 𝓤 ̇}{s t : X} (p : s ≡ t)  → p ∙ refl t ≡ p
rdnel p = refl p

rdner : {X : 𝓤 ̇}{t u : X} (q : t ≡ u)  →  refl t ∙' q ≡ q
rdner q = refl q

--EXERCISE. The identification `refl y` is neutral on both sides of each of the two operations `_∙_` and
-- `_∙'_`, although not definitionally. This has to be proved by induction on identifications, as in `∙-agreement`.
--SOLUTION.
∙-left-id : {X : 𝓤 ̇}{t u : X} (q : t ≡ u) → refl t ∙ q ≡ q
∙-left-id (refl s) = refl (refl s)

------------------------------------------------------------------------------------
--"Application of a function to an identification. Given an identification `p : x ≡ x'` we get an identification
-- `ap f p : f x ≡ f x'` for any `f : X → Y`:
ap cong : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))
cong  = ap   -- alias    (NOTATION (cf. `cong` in `Relation/Binary/PropositionalEquality/Core.agda` )

ap-cong : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f f' : X → Y}{x x' : X} → f ≡ f' → x ≡ x' → f x ≡ f' x'
ap-cong {f = f}{x = x} (refl _) (refl _) = refl (f x)

--cf. Relation/Binary/Core.agda
cong-app : ∀ {A : 𝓤 ̇} {B : A → 𝓦 ̇} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
cong-app {f = f} (refl _) a = refl (f a)


--"Notice that we have so far used the recursion principle `transport` only.
-- To reason about `transport`, `_∙_`, `_⁻¹` and `ap`, we will need to use the full
-- induction principle `𝕁` (or equivalently pattern matching on `refl`)."

--------------------------------------------------------------------------------
--POINTWISE (extensional) EQUALITY OF FUNCTIONS.

--"We will work with pointwise equality of functions, defined as follows, which, using univalence,
-- will be equivalent to equality of functions:
_∼_ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x
infix 0 _∼_

--more equations for transport, including a dependent version
transport-× : {X : 𝓤 ̇ }(A : X → 𝓥 ̇ )(B : X → 𝓦 ̇)
              {x y : X}(p : x ≡ y){c : A x × B x}
             ---------------------------------------------------
 →            transport (λ x → A x × B x) p c
               ≡ (transport A p (pr₁ c) , transport B p (pr₂ c))
transport-× A B (refl x) {c} = refl c

transportd : {X : 𝓤 ̇}
             (A : X → 𝓥 ̇)(B : (x : X) → A x → 𝓦 ̇)
             {x : X} (a : A x)
             ((a' , b) : Σ a ꞉ A x , B x a)  {y : X}
             (p : x ≡ y)  →   B x a'
             --------------------------------
 →           B y (transport A p a')
transportd A B a σ (refl y) = id

transport-Σ : {X : 𝓤 ̇}
              (A : X → 𝓥 ̇)(B : (x : X) → A x → 𝓦 ̇)
              {x : X} (y : X) (p : x ≡ y) (a : A x)
              {(a' , b) : Σ a ꞉ A x , B x a}
             ---------------------------------------------------
 →            transport (λ x → Σ y ꞉ A x , B x y) p (a' , b)
               ≡ transport A p a' , transportd A B a (a' , b) p b
transport-Σ A B {x} x (refl x) a {σ} = refl σ

--The following was added later by MHE (see: https://www.cs.bham.ac.uk/~mhe/agda-new/Id.html#1449 )
back-transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} → x ≡ y → A y → A x
back-transport B p = transport B (p ⁻¹)

------------------------------------------------------------------------------------
--"NEGATION. We first introduce notation for double and triple negation to avoid the use of brackets.
¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬ A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

--"To prove `A → ¬¬ A`, start with a hypothetical element `a : A` and function `u : A → 𝟘` and get an element of `𝟘`.
dni ¬¬-intro : (A : 𝓤 ̇) → A → ¬¬ A
dni A a A→𝟘 = A→𝟘 a
¬¬-intro = dni -- alias
{-(paraphrasing MHE) There is no general way to implement the converse (i.e., from a function (A → 𝟘) → 𝟘,
   get a point of A). For truth values A, we can assume this as an axiom if we wish, because it is equivalent to em.
   But for arbitrary types `A`, this would be a form of global choice for type theory, and global choice is known
   to be inconsistent with univalence (see HoTT book, Thm 3.2.2), because there is no way to choose an element of
   every non-empty type in a way that is invariant under automorphisms. (However, the AoC is consistent with UF.) -}

--(paraphrasing MHE) In the next proof, we are given `f : A → B`, `v : B → 𝟘` and `a : A`, and we want an element of 𝟘
--(easy, since `f a : B`, hence `v (f a) : 𝟘`).
contrapositive : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → (¬ B → ¬ A)
contrapositive A→B B→𝟘 = λ a → B→𝟘 (A→B a)

--(paraphrasing MHE) If we have a function `A → B` and `B` is empty, then `A` must be empty, too.
--From this we get that three negations imply one (we call it "triple negation reduction" or ¬¬¬-elim):
tno ¬¬¬-elim : (A : 𝓤 ̇) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)
¬¬¬-elim = tno -- alias
--"Hence, using `dni` once again, we get that `¬¬¬ A` if and only if `¬ A`."

--LOGICAL EQUIVALENCE.
_⇔_  _iff_  : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)
_iff_ = _⇔_ -- alias
infix 10 _⇔_
infix 10 _iff_

lr-implication iff-elim-left : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (X → Y)
lr-implication = pr₁
iff-elim-left = pr₁         -- alias

rl-implication iff-elim-right : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X iff Y) → (Y → X)
rl-implication = pr₂
iff-elim-right = pr₂       -- alias

--(paraphrasing MHE) ...then we can render Brouwer’s argument in Agda as follows (where the 'established fact' is ¬¬-intro):
absurdity³-is-absurdity : {A : 𝓤 ̇} → ¬¬¬ A iff ¬ A
absurdity³-is-absurdity {𝓤} {A} = firstly , secondly
 where
  firstly : ¬¬¬ A → ¬ A
  firstly = contrapositive (¬¬-intro A)

  secondly : ¬ A → ¬¬¬ A
  secondly = ¬¬-intro (¬ A)

--"We now define a symbol for the negation of equality.
_≢_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x₁ ≢ x₂ = ¬ (x₁ ≡ x₂)
infix   0 _≢_

--Here, we have `u≢v : u ≡ v → 𝟘` and we need `v≢u : v ≡ u → 𝟘`, so just compose `u≢v` with the function that inverts ids.
≢-sym : {X : 𝓤 ̇} {u v : X} → u ≢ v → v ≢ u
≢-sym {𝓤} {X} {u}{v} u≢v = u≢v ∘ (_⁻¹)

--(paraphrasing MHE) To show the type `𝟙` is not the type `𝟘`, we use that `transport id` gives `𝟙 ≡ 𝟘 → id 𝟙 → id 𝟘`
-- where `id` is the identity on the universe `𝓤₀`. More generally, we have the following conversion of type ids into functions:
Id→Fun : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇))

--(paraphrasing MHE) Equivalently, we could use the identity on `X`:
Id→Fun' : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id→Fun' (refl X) = 𝑖𝑑 X

Id→Funs-agree : {X Y : 𝓤 ̇} (p : X ≡ Y) → Id→Fun p ≡ Id→Fun' p
Id→Funs-agree (refl X) = refl (𝑖𝑑 X)

--(paraphrasing MHE) So given `p : 𝟙 ≡ 𝟘`, we get a function `𝟙 → 𝟘`. Applying this to `⋆ : 𝟙` we conclude the proof of 𝟙 ≢ 𝟘.
𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 𝟙≡𝟘 = Id→Fun 𝟙≡𝟘 ⋆

--(paraphrasing MHE) To show that the inhabitants `₁` and `₀` of `𝟚` are not equal, we reduce to the above case.
--(recall, 𝟚 = 𝟙 + 𝟙 is the disjoint union of 𝟙 with a copy of itself; we named the points of 𝟚 using patterns `₀ = inl ⋆`, `₁ = inr ⋆`)
₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ ₁≡₀ = 𝟙-is-not-𝟘 𝟙≡𝟘
 where
  f : 𝟚 → 𝓤₀ ̇  -- 𝟚→𝓤₀̇
  f ₀ = 𝟘
  f ₁ = 𝟙

  𝟙≡𝟘 : 𝟙 ≡ 𝟘
  𝟙≡𝟘 = ap f ₁≡₀

--"REMARK. Agda allows us to use a pattern `()` to get the following quick proof.  However, this method of proof doesn't belong to the realm
-- of MLTT. Hence we will use the pattern `()` only in the above definition of `𝟘-induction` and nowhere else.
₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()

--DECIDABILITY.
decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : (X : 𝓤 ̇) → 𝓤 ̇
has-decidable-equality X = (x₁ x₂ : X) → decidable (x₁ ≡ x₂)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ n≢₀ = !𝟘 (₀ ≡ ₁) (n≢₀ (refl ₀))
not-zero-is-one ₁ _ = refl ₁

--"The following generalizes `₁-is-not-₀`... (so we could have formulated it first and used it to deduce `₁-is-not-₀`):
inl-inr-disjoint-images : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤}{𝓥}{X}{Y} inlx≡inry = 𝟙-is-not-𝟘 𝟙≡𝟘
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘

  𝟙≡𝟘 : 𝟙 ≡ 𝟘
  𝟙≡𝟘 = ap f inlx≡inry


--     (P ∨ Q)       ¬Q
--   --------------- (ds)
--             P
disjunctive-syllogism : {P : 𝓤 ̇} {Q : 𝓥 ̇} → P + Q → ¬ Q → P
disjunctive-syllogism (inl p) _ = p
disjunctive-syllogism (inr q) ¬Q = !𝟘 _ (¬Q q)

-------------------------------------------------------------------------------------------------
-- PEANO  (remaining Peano axioms and basic arithmetic).
-- see:  https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#basicarithmetic

s≢0 : (x : ℕ) -> succ x ≢ 0
s≢0 x s≡0 = 𝟙-is-not-𝟘 (g s≡0)
 where
  f : ℕ -> 𝓤₀ ̇
  f 0 = 𝟘
  f (succ x) = 𝟙

  g : succ x ≡ 0 -> 𝟙 ≡ 𝟘
  g = ap f

--"To show that the successor function is left cancellable, we can use the following predecessor function."
pred : ℕ -> ℕ
pred 0 = 0
pred (succ n) = n

succ-elim : {x y : ℕ} -> succ x ≡ succ y -> x ≡ y
succ-elim = ap pred

succ-lc = succ-elim -- alias
--"With this we have proved all the Peano axioms."

--"Without assuming the principle of excluded middle, we can prove that `ℕ` has decidable equality:"
ℕ-decidable : has-decidable-equality ℕ 
ℕ-decidable 0 0 = inl (refl 0)
ℕ-decidable 0 (succ y) = inr (≢-sym (s≢0 y))
ℕ-decidable (succ x) 0 = inr (s≢0 x)
ℕ-decidable (succ x) (succ y) = f (ℕ-decidable x y)
 where
  f : decidable (x ≡ y) -> decidable (succ x ≡ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) -> k (succ-elim s))

ℕ-has-decidable-equality = ℕ-decidable

------------------------------------------------------------------------
-- Unary relations (aka predicates).  (cf. Relation/Unary.agda from the Agda std lib)
--`Pred A 𝓤` can be viewed as some property that elements of type A might satisfy.
--Consequently `P : Pred A 𝓤` can also be seen as a subset of A containing all the elements of A that satisfy property P.
Pred : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred A 𝓥 = A → 𝓥 ̇

------------------------------------------------------------------------
-- Membership (cf. Relation/Unary.agda from the Agda std lib)
infix 4 _∈_ _∉_
_∈_ : {A : 𝓤 ̇} → A → Pred A 𝓦 → 𝓦 ̇
x ∈ P = P x

_∉_ : {A : 𝓤 ̇} → A → Pred A 𝓦 → 𝓦 ̇
x ∉ P = ¬ (x ∈ P)

------------------------------------------------------------------------
-- Subset relations (cf. Relation/Unary.agda from the Agda std lib)
infix 4 _⊆_ _⊇_
_⊆_ : {A : 𝓤 ̇} → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_⊇_ : {A : 𝓤 ̇} → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P ⊇ Q = Q ⊆ P

------------------------------------------------------------------------
--Stuff from our old Preliminaries.agda file, moderately notationally tweaked.

_∈∈_ :  {A : 𝓤 ̇} {B : 𝓦 ̇} →  (A  →  B) →  Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
_∈∈_  f S = (x : _) → f x ∈ S

Im_⊆_ : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
Im_⊆_ {A = A} f S = (x : A) → f x ∈ S

img :  {X : 𝓤 ̇ } {Y : 𝓤 ̇} (f : X → Y) (P : Pred Y 𝓤) → Im f ⊆ P →  X → Σ P
img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁

≡-elim-left : {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇ }
 →            (A₁ , B₁) ≡ (A₂ , B₂)
              ----------------------
 →                   A₁ ≡ A₂
≡-elim-left e = ap pr₁ e

≡-elim-right : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇}
 →             (A₁ , B₁) ≡ (A₂ , B₂)
              -----------------------
 →                    B₁ ≡ B₂
≡-elim-right e = ap pr₂ e

≡-×-intro : {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
 →           A₁ ≡ A₂  →  B₁ ≡ B₂
          ------------------------
 →          (A₁ , B₁) ≡ (A₂ , B₂)
≡-×-intro (refl _) (refl _) = (refl _)

cong-app-pred : ∀{A : 𝓤 ̇}{B₁ B₂ : Pred A 𝓤}
                (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
               ------------------------------
 →                         x ∈ B₂
cong-app-pred x x∈B₁ (refl _) = x∈B₁

cong-pred : {A : 𝓤 ̇}{B : Pred A 𝓤}
            (x y : A) →  x ∈ B  →  x ≡ y
            ----------------------------
 →                       y ∈ B
cong-pred x .x x∈B (refl .x) = x∈B


data Image_∋_ {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

-- image_ : {A : 𝓤 ̇} {B : 𝓦 ̇} → (A → B) → Pred B (𝓤 ⊔ 𝓦)
-- image f = λ b → ∃ λ a → b ≡ f a

ImageIsImage : {A : 𝓤 ̇}{B : 𝓦 ̇}
               (f : A → B) (b : B) (a : A)
 →              b ≡ f a
              ----------------------------
 →              Image f ∋ b
ImageIsImage {A = A}{B = B} f b a b≡fa = eq b a b≡fa

--N.B. the assertion Image f ∋ y must come with a proof, which is of the form
--∃a f a = y, so we have a witness. Thus, the inverse can be "computed" in the
--following way:
Inv : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B)(b : B) → Image f ∋ b  →  A
Inv f .(f a) (im a) = a
Inv f b (eq b a b≡fa) = a

-- special case for Set
inv : {A B : 𝓤₀ ̇}(f : A → B)(b : B) → Image f ∋ b → A
inv {A} {B} = Inv {𝓤₀}{𝓤₀}{A}{B}

InvIsInv : {A : 𝓤 ̇} {B : 𝓦 ̇} (f : A → B)
           (b : B) (b∈Imgf : Image f ∋ b)
          ---------------------------------
 →         f (Inv f b b∈Imgf) ≡ b
InvIsInv f .(f a) (im a) = refl _
InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹

-- Epic (surjective) function from 𝓤 ̇ to 𝓦 ̇
Epic : {A : 𝓤 ̇} {B : 𝓦 ̇} (g : A → B) →  𝓤 ⊔ 𝓦 ̇
Epic g = ∀ y → Image g ∋ y

-- special case: epic function on Set
epic : {A B : 𝓤₀ ̇} (g : A → B) → 𝓤₀ ̇
epic = Epic {𝓤₀} {𝓤₀}

-- The (pseudo-)inverse of an epic function
EpicInv : {A : 𝓤 ̇} {B : 𝓦 ̇ } (f : A → B) → Epic f → B → A
EpicInv f fEpic b = Inv f b (fEpic b)

---------------------------------------------------------
--Monics (injectivity)
--see also: `left-cancellable` aka `injective` in the `UF-Univalence` module.
monic : {A : 𝓤 ̇} {B : 𝓦 ̇} (g : A → B) → 𝓤 ⊔ 𝓦 ̇
monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂
monic₀ : {A B : 𝓤₀ ̇} (g : A → B) → 𝓤₀ ̇
monic₀ = monic {𝓤₀}{𝓤₀}

--The (pseudo-)inverse of a monic function
monic-inv : {A : 𝓤 ̇} {B : 𝓦 ̇} (f : A → B) → monic f
 →           (b : B) → Image f ∋ b → A
monic-inv f fmonic  = λ b Imf∋b → Inv f b Imf∋b

--The (psudo-)inverse of a monic is the left inverse.
monic-inv-is-linv : {A : 𝓤 ̇}{B : 𝓦 ̇}
                    (f : A → B) (fmonic : monic f)(x : A)
                   ----------------------------------------
  →                 (monic-inv f fmonic) (f x) (im x) ≡ x
monic-inv-is-linv f fmonic x = refl x

--bijectivity
bijective : {A B : 𝓤₀ ̇}(g : A → B) → 𝓤₀ ̇
bijective g = epic g × monic g

Bijective : {A : 𝓤 ̇}{B : 𝓦 ̇}(g : A → B) → 𝓤 ⊔ 𝓦 ̇
Bijective g = Epic g × monic g


