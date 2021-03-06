---
layout: default
title : terms module (of the Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: terms.agda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATE: 12 Jan 2021
-->

## Terms

### Options, imports

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext)

module terms
 {𝑆 : Signature 𝓞 𝓥} {gfe : global-dfunext} 
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import congruences {𝑆 = 𝑆}{gfe}
open import homomorphisms {𝑆 = 𝑆}{gfe}
\end{code}

### The inductive type of terms

\begin{code}
data Term {𝓧 : Universe}{X : 𝓧 ̇} : 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ̇  where
  generator : X → Term{𝓧}{X}
  node : (f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓧}{X}) → Term

open Term
\end{code}

### The (absolutely free) term algebra

\begin{code}
--The term algebra 𝑻(X).
𝑻 : {𝓧 : Universe}(X : 𝓧 ̇) → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺) 𝑆
𝑻 {𝓧} X = Term{𝓧}{X} , node

term-op : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓧}{X} ) → Term
term-op f args = node f args

--1.a. Every map (X → 𝑨) lifts.
free-lift : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)
 →          ∣ 𝑻 X ∣ → ∣ 𝑨 ∣

free-lift _ h (generator x) = h x
free-lift 𝑨 h (node f args) = (f ̂ 𝑨) λ i → free-lift 𝑨 h (args i)

--1.b. The lift is (extensionally) a hom
lift-hom : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)
 →         hom (𝑻 X) 𝑨

lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → ap (_ ̂ 𝑨) 𝓇ℯ𝒻𝓁

--2. The lift to (free → 𝑨) is (extensionally) unique.
free-unique : {𝓧 𝓤 : Universe}{X : 𝓧 ̇} → funext 𝓥 𝓤
 →            (𝑨 : Algebra 𝓤 𝑆)(g h : hom (𝑻 X) 𝑨)
 →            (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
 →            (t : Term{𝓧}{X})
             ---------------------------
 →            ∣ g ∣ t ≡ ∣ h ∣ t

free-unique _ _ _ _ p (generator x) = p x
free-unique fe 𝑨 g h p (node f args) =
   ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
   (f ̂ 𝑨)(λ i → ∣ g ∣ (args i))  ≡⟨ ap (_ ̂ 𝑨) γ ⟩
   (f ̂ 𝑨)(λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
   ∣ h ∣ (node f args)             ∎
   where γ = fe λ i → free-unique fe 𝑨 g h p (args i)
\end{code}

### Lifting and imaging devices

\begin{code}
lift-agrees-on-X : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)(x : X)
        ----------------------------------------
 →       h₀ x ≡ ∣ lift-hom 𝑨 h₀ ∣ (generator x)

lift-agrees-on-X _ h₀ x = 𝓇ℯ𝒻𝓁

--Of course, the lift of a surjective map is surjective.
lift-of-epi-is-epi : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)
 →                    Epic h₀
                     ----------------------
 →                    Epic ∣ lift-hom 𝑨 h₀ ∣

lift-of-epi-is-epi {𝓧}{𝓤}{X} 𝑨 h₀ hE y = γ
 where
  h₀pre : Image h₀ ∋ y
  h₀pre = hE y

  h₀⁻¹y : X
  h₀⁻¹y = Inv h₀ y (hE y)

  η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (generator h₀⁻¹y)
  η =
   y                                 ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
   h₀ h₀⁻¹y                          ≡⟨ lift-agrees-on-X 𝑨 h₀ h₀⁻¹y ⟩
   ∣ lift-hom 𝑨 h₀ ∣ (generator h₀⁻¹y) ∎

  γ : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
  γ = eq y (generator h₀⁻¹y) η
\end{code}

Since it's absolutely free, 𝑻 X is the domain of a homomorphism to any algebra we like. The following shows how to get your hands on such homomorphisms.

\begin{code}

𝑻hom-gen : {𝓧 𝓤 : Universe}{X : 𝓧 ̇} (𝑪 : Algebra 𝓤 𝑆)
 →         Σ h ꞉ (hom (𝑻 X) 𝑪), Epic ∣ h ∣
𝑻hom-gen {𝓧}{𝓤}{X} 𝑪 = h , lift-of-epi-is-epi 𝑪 h₀ hE
 where
  h₀ : X → ∣ 𝑪 ∣
  h₀ = fst (𝕏 𝑪)

  hE : Epic h₀
  hE = snd (𝕏 𝑪)

  h : hom (𝑻 X) 𝑪
  h = lift-hom 𝑪 h₀
\end{code}

### Term operations: interpreting terms in algebras

\begin{code}

_̇_ : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ } → Term{𝓧}{X} → (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
((generator x) ̇ 𝑨) 𝒂 = 𝒂 x
((node f args) ̇ 𝑨) 𝒂 = (f ̂ 𝑨) λ i → (args i ̇ 𝑨) 𝒂
\end{code}

Observe that intepretation of a term is the same as `free-lift` (modulo argument order).

\begin{code}
free-lift-interpretation : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }
                           (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)(p : Term)
 →                         (p ̇ 𝑨) h ≡ free-lift 𝑨 h p

free-lift-interpretation 𝑨 h (generator x) = 𝓇ℯ𝒻𝓁
free-lift-interpretation 𝑨 h (node f args) = ap (f ̂ 𝑨) (gfe λ i → free-lift-interpretation 𝑨 h (args i))
lift-hom-interpretation : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }
                          (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)(p : Term)
 →                        (p ̇ 𝑨) h ≡ ∣ lift-hom 𝑨 h ∣ p

lift-hom-interpretation = free-lift-interpretation
\end{code}

<!--
Want (𝒕 : X → ∣ 𝑻(X) ∣) → ((p ̇ 𝑻(X)) 𝒕) ≡ p 𝒕... but what is (𝑝 ̇ 𝑻(X)) 𝒕 ?
By definition, it depends on the form of 𝑝 as follows:
* if 𝑝 = (generator x), then
     (𝑝 ̇ 𝑻(X)) 𝒕 = ((generator x) ̇ 𝑻(X)) 𝒕 = 𝒕 x
* if 𝑝 = (node f args), then
     (𝑝 ̇ 𝑻(X)) 𝒕 = ((node f args) ̇ 𝑻(X)) 𝒕 = (f ̂ 𝑻(X)) λ i → (args i ̇ 𝑻(X)) 𝒕
Let h : hom 𝑻 𝑨. Then by comm-hom-term,
∣ h ∣ (p ̇ 𝑻(X)) 𝒕 = (p ̇ 𝑨) ∣ h ∣ ∘ 𝒕
* if p = (generator x), then
   ∣ h ∣ p ≡ ∣ h ∣ (generator x)
          ≡ λ 𝒕 → 𝒕 x) (where 𝒕 : X → ∣ 𝑻(X) ∣ )
          ≡ (λ 𝒕 → (∣ h ∣ ∘ 𝒕) x)
   ∣ h ∣ p ≡ ∣ h ∣ (λ 𝒕 → 𝒕 x) (where 𝒕 : X → ∣ 𝑻(X) ∣ )
          ≡ (λ 𝒕 → (∣ h ∣ ∘ 𝒕) x)
* if p = (node f args), then
   ∣ h ∣ p ≡ ∣ h ∣  (p ̇ 𝑻(X)) 𝒕 = ((node f args) ̇ 𝑻(X)) 𝒕 = (f ̂ 𝑻(X)) λ i → (args i ̇ 𝑻(X)) 𝒕
-->

We claim that if p : ∣ 𝑻(X) ∣ then there exists 𝓅 : ∣ 𝑻(X) ∣ and 𝒕 : X → ∣ 𝑻(X) ∣ such that p ≡ (𝓅 ̇ 𝑻(X)) 𝒕. We prove this fact as follows.


\begin{code}
term-op-interp1 : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term)
 →                node f args ≡ (f ̂ 𝑻 X) args

term-op-interp1 = λ f args → 𝓇ℯ𝒻𝓁

term-op-interp2 : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term{𝓧}{X}}
 →                a1 ≡ a2  →  node f a1 ≡ node f a2

term-op-interp2 f a1≡a2 = ap (node f) a1≡a2

term-op-interp3 : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term}
 →                a1 ≡ a2  →  node f a1 ≡ (f ̂ 𝑻 X) a2

term-op-interp3 f {a1}{a2} a1a2 = (term-op-interp2 f a1a2) ∙ (term-op-interp1 f a2)

term-gen : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣)
 →         Σ 𝓅 ꞉ ∣ 𝑻 X ∣ , p ≡ (𝓅 ̇ 𝑻 X) generator

term-gen (generator x) = (generator x) , 𝓇ℯ𝒻𝓁
term-gen (node f args) = node f (λ i → ∣ term-gen (args i) ∣) ,
                                term-op-interp3 f (gfe λ i → ∥ term-gen (args i) ∥)

tg : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣) → Σ 𝓅 ꞉ ∣ 𝑻 X ∣ , p ≡ (𝓅 ̇ 𝑻 X) generator
tg p = term-gen p

term-equality : {𝓧 : Universe}{X : 𝓧 ̇}(p q : ∣ 𝑻 X ∣)
 →              p ≡ q → (∀ t → (p ̇ 𝑻 X) t ≡ (q ̇ 𝑻 X) t)
term-equality p q (refl _) _ = refl _

term-equality' : {𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓤 𝑆}(p q : ∣ 𝑻 X ∣)
 →              p ≡ q → (∀ 𝒂 → (p ̇ 𝑨) 𝒂 ≡ (q ̇ 𝑨) 𝒂)
term-equality' p q (refl _) _ = refl _

term-gen-agreement : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣)
 →               (p ̇ 𝑻 X) generator ≡ (∣ term-gen p ∣ ̇ 𝑻 X) generator
term-gen-agreement (generator x) = 𝓇ℯ𝒻𝓁
term-gen-agreement {𝓧}{X}(node f args) = ap (f ̂ 𝑻 X) (gfe λ x → term-gen-agreement (args x))

term-agreement : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣)
 →            p ≡ (p ̇ 𝑻 X) generator
term-agreement p = snd (term-gen p) ∙ (term-gen-agreement p)⁻¹
\end{code}

### Term interpretation in product algebras

\begin{code}
interp-prod : {𝓧 𝓤 : Universe} → funext 𝓥 𝓤
 →            {X : 𝓧 ̇}(p : Term){I : 𝓤 ̇}
              (𝒜 : I → Algebra 𝓤 𝑆)(x : X → ∀ i → ∣ (𝒜 i) ∣)
              --------------------------------------------------------
 →            (p ̇ (⨅ 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

interp-prod _ (generator x₁) 𝒜 x = 𝓇ℯ𝒻𝓁

interp-prod fe (node f t) 𝒜 x =
 let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
  (f ̂ ⨅ 𝒜)(λ x₁ → (t x₁ ̇ ⨅ 𝒜) x)                             ≡⟨ ap (f ̂ ⨅ 𝒜)(fe IH) ⟩
  (f ̂ ⨅ 𝒜)(λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁)(λ j₁ → x j₁ i₁)))     ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
  (λ i₁ → (f ̂ 𝒜 i₁) (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))   ∎

interp-prod2 : {𝓧 : Universe} → global-dfunext
 →             {X : 𝓧 ̇}(p : Term){I : 𝓤 ̇ }(𝒜 : I → Algebra 𝓤 𝑆)
               ----------------------------------------------------------------------
 →             (p ̇ ⨅ 𝒜) ≡ λ(args : X → ∣ ⨅ 𝒜 ∣) → (λ i → (p ̇ 𝒜 i)(λ x → args x i))

interp-prod2 _ (generator x₁) 𝒜 = 𝓇ℯ𝒻𝓁

interp-prod2 gfe {X} (node f t) 𝒜 = gfe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
  let IH = λ x → interp-prod gfe (t x) 𝒜  in
  let tA = λ z → t z ̇ ⨅ 𝒜 in
   (f ̂ ⨅ 𝒜)(λ s → tA s tup)                          ≡⟨ ap (f ̂ ⨅ 𝒜)(gfe λ x → IH x tup) ⟩
   (f ̂ ⨅ 𝒜)(λ s → λ j → (t s ̇ 𝒜 j)(λ ℓ → tup ℓ j))  ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ ℓ → tup ℓ i))) ∎

\end{code}

### Homomorphisms commute with terms

We can prove this extensionally...
\begin{code}
comm-hom-term : {𝓤 𝓦 𝓧 : Universe} → funext 𝓥 𝓦
 →              {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
                (h : hom 𝑨 𝑩) (t : Term) (a : X → ∣ 𝑨 ∣)
               ------------------------------------------------------
 →              ∣ h ∣ ((t ̇ 𝑨) a) ≡ (t ̇ 𝑩) (∣ h ∣ ∘ a)

comm-hom-term _ 𝑨 𝑩 h (generator x) a = 𝓇ℯ𝒻𝓁

comm-hom-term fe 𝑨 𝑩 h (node f args) a =
 ∣ h ∣((f ̂ 𝑨) λ i₁ → (args i₁ ̇ 𝑨) a)    ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a ) ⟩
 (f ̂ 𝑩)(λ i₁ →  ∣ h ∣((args i₁ ̇ 𝑨) a))  ≡⟨ ap (_ ̂ 𝑩)(fe (λ i₁ → comm-hom-term fe 𝑨 𝑩 h (args i₁) a))⟩
 (f ̂ 𝑩)(λ r → (args r ̇ 𝑩)(∣ h ∣ ∘ a))    ∎
\end{code}

...or intensionally.

\begin{code}
comm-hom-term-intensional : global-dfunext → {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
 →       (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) (t : Term)
         ------------------------------------------------------------------
 →         ∣ h ∣ ∘ (t ̇ 𝑨) ≡ (t ̇ 𝑩) ∘ (λ a → ∣ h ∣ ∘ a)

comm-hom-term-intensional gfe 𝑨 𝑩 h (generator x) = 𝓇ℯ𝒻𝓁

comm-hom-term-intensional gfe {X = X} 𝑨 𝑩 h (node f args) = γ
 where
  γ : ∣ h ∣ ∘ (λ a → (f ̂ 𝑨) (λ i → (args i ̇ 𝑨) a))
      ≡ (λ a → (f ̂ 𝑩)(λ i → (args i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣
  γ = (λ a → ∣ h ∣ ((f ̂ 𝑨)(λ i → (args i ̇ 𝑨) a)))  ≡⟨ gfe (λ a → ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a )) ⟩
      (λ a → (f ̂ 𝑩)(λ i → ∣ h ∣ ((args i ̇ 𝑨) a)))  ≡⟨ ap (λ - → (λ a → (f ̂ 𝑩)(- a))) ih ⟩
      (λ a → (f ̂ 𝑩)(λ i → (args i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣  ∎
    where
     IH : (a : X → ∣ 𝑨 ∣)(i : ∥ 𝑆 ∥ f)
      →   (∣ h ∣ ∘ (args i ̇ 𝑨)) a ≡ ((args i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a
     IH a i = intensionality (comm-hom-term-intensional gfe 𝑨 𝑩 h (args i)) a

     ih : (λ a → (λ i → ∣ h ∣ ((args i ̇ 𝑨) a)))
           ≡ (λ a → (λ i → ((args i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a))
     ih = gfe λ a → gfe λ i → IH a i

\end{code}

### Compatibility of terms and congruences

If t : Term, θ : Con 𝑨, then a θ b → t(a) θ t(b)).

\begin{code}
open congruence-relations

compatible-term : {𝓤 : Universe}{X : 𝓤 ̇}
                  (𝑨 : Algebra 𝓤 𝑆)(t : Term{𝓤}{X})(θ : Con 𝑨)
                 ------------------------------------------------
 →                compatible-fun (t ̇ 𝑨) ∣ θ ∣

compatible-term 𝑨 (generator x) θ p = p x

compatible-term 𝑨 (node f args) θ p = snd ∥ θ ∥ f λ x → (compatible-term 𝑨 (args x) θ) p

compatible-term' : {𝓤 : Universe} {X : 𝓤 ̇}
                   (𝑨 : Algebra 𝓤 𝑆)(t : Term{𝓤}{X}) (θ : Con 𝑨)
                 ---------------------------------------------------
 →                 compatible-fun (t ̇ 𝑨) ∣ θ ∣

compatible-term' 𝑨 (generator x) θ p = p x
compatible-term' 𝑨 (node f args) θ p = snd ∥ θ ∥ f λ x → (compatible-term' 𝑨 (args x) θ) p
\end{code}
