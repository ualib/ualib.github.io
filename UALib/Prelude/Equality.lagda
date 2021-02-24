---
layout: default
title : UALib.Prelude.Equality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="equality">Equality</a>

This section describes the [UALib.Prelude.Equality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude.Equality where

open import universes public

open import Prelude.Preliminaries public
open import Sigma-Type renaming (_,_ to infixr 50 _,_) public
open import MGS-MLTT using (pr₁; pr₂; _×_; -Σ) public

-- open import UALib.Prelude.Preliminaries using (Universe; _̇; _⊔_; _⁺; _≡_; refl;
--  Σ; -Σ; _×_; _,_; pr₁; pr₂; ∣_∣; ∥_∥; fst; snd; is-subsingleton; is-prop; 𝟙; ap) public

\end{code}


#### <a id="refl">refl</a>

The type which is often referred to as "reflexivity" or "refl" is a very basic and important one. It represents [definitional equality](https://ncatlab.org/nlab/show/equality#definitional_equality).

The `refl` type we use is a standard one. It is defined in the `Identity-Type` module of the [Type Topology][] library, which we imported in the [Prelude.Preliminaries][] module, but apart from syntax it is equivalent to the identity type used in most other Agda libraries.

In the present module, we make `refl` available by importing it from [Prelude.Preliminaries][], which in turn improts from the `Identity-Type` module.  The latter defines `refl` as the following inductive datatype.

\begin{code}

module hide-refl {𝓤 : Universe} where

 data _≡_ {𝓤} {X : 𝓤 ̇ } : X → X → 𝓤 ̇ where
  refl : {x : X} → x ≡ x

\end{code}

Let us now formalize the obvious fact that `≡` is an equivalence relation.

First we import the original definitions of `_≡_` and `refl` from the [Type Topology][] library. (The definition given above, inside the `hide-refl` module, was merely for illustration.)

\begin{code}

open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁)
pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}

module _  {𝓤 : Universe}{X : 𝓤 ̇ }  where
 ≡-rfl : (x : X) → x ≡ x
 ≡-rfl x = 𝓇ℯ𝒻𝓁

 ≡-sym : (x y : X) → x ≡ y → y ≡ x
 ≡-sym x y 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁

 ≡-trans : (x y z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-trans x y z 𝓇ℯ𝒻𝓁 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁

 ≡-Trans : (x : X){y : X}(z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-Trans x {y} z 𝓇ℯ𝒻𝓁 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁

\end{code}

(The only difference between `≡-trans` and `≡-Trans` is that the second argument to `≡-Trans` is implicit so we can omit it when applying `≡-Trans`.  This is sometimes convenient; after all, `≡-Trans` is used to prove that the first and last arguments are the same, and often we don't care about the middle argument.)

Since we use `refl _` so often, it is convenient to adopt the following shorthand.


#### <a id="functions-preserve-refl">Functions preserve refl</a>

A function is well defined only if it maps equivalent elements to a single element and we often use this nature of functions in Agda proofs.  If we have a function `f : X → Y`, two elements `x x' : X` of the domain, and an identity proof `p : x ≡ x'`, then we obtain a proof of `f x ≡ f x'` by simply applying the `ap` function like so, `ap f p : f x ≡ f x'`.

Escardó defines `ap` in his [Type Topology][] library, and we needn't redefine it here. Instead, we define some variations of `ap` that are sometimes useful.

\begin{code}

ap-cong : {𝓤 𝓦 : Universe}{A : 𝓤 ̇ }{B : 𝓦 ̇ }{f g : A → B} {a b : A}
 →        f ≡ g  →  a ≡ b
          ---------------
 →        f a ≡ g b

ap-cong (refl _) (refl _) = refl _

\end{code}

We sometimes need a version of this that works for [dependent types][], such as the following (which we borrow from the `Relation/Binary/Core.agda` module of the [Agda Standard Library][], transcribed into MHE/UALib notation of course):

\begin{code}

cong-app : {𝓤 𝓦 : Universe}
           {A : 𝓤 ̇} {B : A → 𝓦 ̇}
           {f g : (a : A) → B a}
 →          f ≡ g   →   (a : A)
          -----------------------
 →              f a ≡ g a

cong-app (refl _) a = refl _

\end{code}




#### <a id="≡-intro-and-≡-elim-for-nondependent-pairs">≡-intro and ≡-elim for nondependent pairs</a>

We conclude the Equality module with some occasionally useful introduction and elimination rules for the equality relation on (nondependent) pair types.



\begin{code}

open import MGS-MLTT using (ap) public

≡-elim-left : {𝓤 𝓦 : Universe}
              {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
 →            (A₁ , B₁) ≡ (A₂ , B₂)
              ----------------------
 →                   A₁ ≡ A₂

≡-elim-left e = ap pr₁ e


≡-elim-right : {𝓤 𝓦 : Universe}
               {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇}
 →             (A₁ , B₁) ≡ (A₂ , B₂)
               -----------------------
 →                    B₁ ≡ B₂

≡-elim-right e = ap pr₂ e


≡-×-intro : {𝓤 𝓦 : Universe}
            {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
 →           A₁ ≡ A₂  →  B₁ ≡ B₂
           ------------------------
 →          (A₁ , B₁) ≡ (A₂ , B₂)

≡-×-intro (refl _ ) (refl _ ) = (refl _ )


≡-×-int : {𝓤 𝓦 : Universe}
          {A : 𝓤 ̇} {B : 𝓦 ̇}
          (a a' : A)(b b' : B)
 →         a ≡ a'  →  b ≡ b'
          ------------------------
 →         (a , b) ≡ (a' , b')

≡-×-int a a' b b' (refl _ ) (refl _ ) = (refl _ )
\end{code}

-------------------------------------

[← Prelude.Preliminaries ](Prelude.Preliminaries.html)
<span style="float:right;">[Prelude.Inverses →](Prelude.Inverses.html)</span>

{% include UALib.Links.md %}
