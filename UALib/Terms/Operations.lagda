---
layout: default
title : Terms.Operations module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="term-operations">Term Operations</a>

This section presents the [Terms.Operations][] module of the [Agda Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a particular algebra, and we prove some compatibility properties of term operations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Terms.Operations where

open import Terms.Basic public

module operations {𝑆 : Signature 𝓞 𝓥} where
 open terms {𝑆 = 𝑆} public

\end{code}

When we interpret a term in an algebra we call the resulting function a *term operation*.  Given a term `p` and an algebra `𝑨`, we denote by `𝑨 ⟦ p ⟧` the *interpretation* of `p` in `𝑨`.  This is defined inductively as follows.

1. If `p` is a variable symbol `x : X` and if `a : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then `𝑨 ⟦ p ⟧ a := a x`.

2. If `p = 𝑓 𝑡`, where `𝑓 : ∣ 𝑆 ∣` is an operation symbol, if `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑻 X` is a tuple of terms, and if `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define `𝑨 ⟦ p ⟧ a = 𝑨 ⟦ 𝑓 𝑡 ⟧ a := (𝑓 ̂ 𝑨) (λ i → 𝑨 ⟦ 𝑡 i ⟧ a)`.

Thus the interpretation of a term is defined by induction on the structure of the term, and the definition is formally implemented in the [UALib][] as follows.

\begin{code}


 _⟦_⟧_ : {X : Set 𝓧 }(𝑨 : Algebra 𝓤 𝑆) → Term X → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
 𝑨 ⟦ ℊ x ⟧ a = a x
 𝑨 ⟦ node 𝑓 𝑡 ⟧ a = (𝑓 ̂ 𝑨) (λ i → 𝑨 ⟦ 𝑡 i ⟧ a)

\end{code}

It turns out that the intepretation of a term is the same as the `free-lift` (modulo argument order and assuming function extensionality).

\begin{code}

 free-lift-interp : dfunext 𝓥 𝓤 → {X : Set 𝓧}(𝑨 : Algebra 𝓤 𝑆)(a : X → ∣ 𝑨 ∣)(p : Term X)
  →                 𝑨 ⟦ p ⟧ a ≡ (free-lift 𝑨 a) p
 free-lift-interp _ 𝑨 a (ℊ x) = refl
 free-lift-interp fe 𝑨 a (node 𝑓 𝑡) = ap (𝑓 ̂ 𝑨) (fe λ i → free-lift-interp fe 𝑨 a (𝑡 i))

\end{code}

If the algebra 𝑨 happens to be `𝑻 X`, then we expect that `∀ 𝑠` we have `(𝑻 X)⟦ p ⟧ 𝑠 ≡ p 𝑠`. But what is `(𝑻 X)⟦ p ⟧ 𝑠` exactly? By definition, it depends on the form of `p` as follows:

* if `p = ℊ x`, then `(𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ ℊ x ⟧ 𝑠 ≡ 𝑠 x`

* if `p = node 𝑓 𝑡`, then `(𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠`

Now, assume `ϕ : hom 𝑻 𝑨`. Then by `comm-hom-term`, we have `∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = 𝑨 ⟦ p ⟧ ∣ ϕ ∣ ∘ 𝑠`.

* if `p = ℊ x` (and `𝑡 : X → ∣ 𝑻 X ∣`), then

  `∣ ϕ ∣ p ≡ ∣ ϕ ∣ (ℊ x) ≡ ∣ ϕ ∣ (λ 𝑡 → h 𝑡) ≡ λ 𝑡 → (∣ ϕ ∣ ∘ 𝑡) x`

* if `p = node 𝑓 𝑡`, then

   ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠

We claim that for all `p : Term X` there exists `q : Term X` and `𝔱 : X → ∣ 𝑻 X ∣` such that `p ≡ (𝑻 X)⟦ q ⟧ 𝔱`. We prove this fact as follows.

\begin{code}

 term-interp : {X : Set 𝓧} (𝑓 : ∣ 𝑆 ∣){𝑠 𝑡 : ∥ 𝑆 ∥ 𝑓 → Term X} → 𝑠 ≡ 𝑡 → node 𝑓 𝑠 ≡ (𝑓 ̂ 𝑻 X) 𝑡
 term-interp 𝑓 st = ap (node 𝑓) st

 term-gen : dfunext 𝓥 (ov 𝓧) → {X : Set 𝓧}(p : ∣ 𝑻 X ∣) → Σ q ꞉ ∣ 𝑻 X ∣ , p ≡ (𝑻 X) ⟦ q ⟧ ℊ
 term-gen _ (ℊ x) = (ℊ x) , refl
 term-gen fe (node 𝑓 𝑡) = node 𝑓 (λ i → ∣ term-gen fe (𝑡 i) ∣) , term-interp 𝑓 (fe λ i → ∥ term-gen fe (𝑡 i) ∥)


 term-gen-agreement : {fe : dfunext 𝓥(ov 𝓧)}{X : Set 𝓧}(p : ∣ 𝑻 X ∣) → (𝑻 X)⟦ p ⟧ ℊ ≡ (𝑻 X)⟦ ∣ term-gen fe p ∣ ⟧ ℊ
 term-gen-agreement (ℊ x) = refl
 term-gen-agreement {fe = fe}{X}(node f 𝑡) = ap (f ̂ 𝑻 X) (fe λ x → term-gen-agreement (𝑡 x))

 term-agreement : dfunext 𝓥 (ov 𝓧) → {X : Set 𝓧}(p : ∣ 𝑻 X ∣) → p ≡  (𝑻 X)⟦ p ⟧ ℊ
 term-agreement fe p = snd (term-gen fe p) ∙ (term-gen-agreement p)⁻¹

\end{code}



#### <a id="interpretation-of-terms-in-product-algebras">Interpretation of terms in product algebras</a>

\begin{code}

 module _ {X : Set 𝓧 }{I : Set 𝓦} where

  interp-prod : dfunext 𝓥 (𝓤 ⊔ 𝓦) → (p : Term X)(𝒜 : I → Algebra 𝓤 𝑆)(𝑎 : X → ∀ i → ∣ 𝒜 i ∣)
   →            (⨅ 𝒜 )⟦ p ⟧ 𝑎 ≡ λ i →  (𝒜 i)⟦ p ⟧(λ j → 𝑎 j i)

  interp-prod _ (ℊ x₁) 𝒜 𝑎 = refl

  interp-prod fe (node 𝑓 𝑡) 𝒜 𝑎 = let IH = λ x → interp-prod fe (𝑡 x) 𝒜 𝑎
   in
   (𝑓 ̂ ⨅ 𝒜) (λ x → (⨅ 𝒜 )⟦ 𝑡 x ⟧ 𝑎 )                  ≡⟨ ap (𝑓 ̂ ⨅ 𝒜)(fe IH) ⟩
   (𝑓 ̂ ⨅ 𝒜)(λ x → λ i →  (𝒜 i)⟦ 𝑡 x ⟧ λ j → 𝑎 j i)   ≡⟨ refl ⟩
   (λ i → (𝑓 ̂ 𝒜 i) (λ x → (𝒜 i)⟦ 𝑡 x ⟧ λ j → 𝑎 j i)) ∎

  -- inferred type: 𝑡 : X → ∣ ⨅ 𝒜 ∣
  interp-prod2 : dfunext (𝓤 ⊔ 𝓦 ⊔ 𝓧) (𝓤 ⊔ 𝓦) → dfunext 𝓥 (𝓤 ⊔ 𝓦) → (p : Term X)(𝒜 : I → Algebra 𝓤 𝑆)
   →             (λ a → ⨅ 𝒜 ⟦ p ⟧ a) ≡ λ 𝑡 i → (𝒜 i)⟦ p ⟧(λ x → 𝑡 x i)

  interp-prod2 _ _ (ℊ x₁) 𝒜 = refl

  interp-prod2 fe fev (node f t) 𝒜 = fe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
   let IH = λ x → interp-prod fev (t x) 𝒜  in
   let tA = λ z →  (λ a → (⨅ 𝒜 )⟦ t z ⟧ a) in
   (f ̂ ⨅ 𝒜)(λ s → tA s tup)                          ≡⟨ ap(f ̂ ⨅ 𝒜)(fev λ x → IH x tup)⟩
   (f ̂ ⨅ 𝒜)(λ s → λ j → (𝒜 j)⟦ t s ⟧(λ ℓ → tup ℓ j))   ≡⟨ refl ⟩
   (λ i → (f ̂ 𝒜 i)(λ s →  (𝒜 i)⟦ t s ⟧ (λ ℓ → tup ℓ i))) ∎

\end{code}




#### <a id="compatibility-of-terms">Compatibility of terms</a>

We now prove two important facts about term operations.  The first of these, which is used very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

 comm-hom-term : dfunext 𝓥 𝓦 → {X : Set 𝓧}{𝑨 : Algebra 𝓤 𝑆} (𝑩 : Algebra 𝓦 𝑆)
                 (h : hom 𝑨 𝑩)(t : Term X) → ∀ a → ∣ h ∣(𝑨 ⟦ t ⟧ a) ≡ 𝑩 ⟦ t ⟧(∣ h ∣ ∘ a)

 comm-hom-term _ 𝑩 h (ℊ x) a = refl
 comm-hom-term fe {𝑨 = 𝑨} 𝑩 h (node 𝑓 𝑡) a = ∣ h ∣((𝑓 ̂ 𝑨) λ i →  𝑨 ⟦ 𝑡 i ⟧ a)    ≡⟨ i  ⟩
                                             (𝑓 ̂ 𝑩)(λ i →  ∣ h ∣ (𝑨 ⟦ 𝑡 i ⟧ a))  ≡⟨ ii ⟩
                                             (𝑓 ̂ 𝑩)(λ r → 𝑩 ⟦ 𝑡 r ⟧ (∣ h ∣ ∘ a)) ∎
  where i  = ∥ h ∥ 𝑓 λ r → 𝑨 ⟦ 𝑡 r ⟧ a
        ii = ap (𝑓 ̂ 𝑩)(fe (λ i → comm-hom-term fe 𝑩 h (𝑡 i) a))

\end{code}

To conclude this module, we prove that every term is compatible with every congruence relation. That is, if `t : Term X` and `θ : Con 𝑨`, then `a θ b → t(a) θ t(b)`. (Recall, the compatibility relation `|:` was defined in [Relations.Discrete][].)

\begin{code}


 open IsCongruence

 _∣:_ : {X : Set 𝓤}{𝑨 : Algebra 𝓤 𝑆}(t : Term X)(θ : Con{𝓤}{𝓦} 𝑨) → (λ a → 𝑨 ⟦ t ⟧ a) |: ∣ θ ∣
 ((ℊ x) ∣: θ) p = p x
 ((node 𝑓 𝑡) ∣: θ) p = (is-compatible ∥ θ ∥) 𝑓 λ x → ((𝑡 x) ∣: θ) p

\end{code}

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">We plan to resolve this before the next major release of the [Agda UALib][].</span>

<br>
<br>

[← Terms.Basic](Terms.Basic.html)
<span style="float:right;">[Subalgebras →](Subalgebras.html)</span>

{% include UALib.Links.md %}










<!--  UNUNSED STUFF

Here is an intensional version.

comm-hom-term-intensional : global-dfunext → {𝓤 𝓦 𝓧 : Level}{X : 𝓧 ̇}
 →                          (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)(t : Term X)
                            -------------------------------------------------------------
 →                          ∣ h ∣ ∘ (t ̇ 𝑨) ≡ (t ̇ 𝑩) ∘ (λ a → ∣ h ∣ ∘ a)

comm-hom-term-intensional gfe 𝑨 𝑩 h (ℊ x) = refl

comm-hom-term-intensional gfe {X = X} 𝑨 𝑩 h (node f 𝑡) = γ
 where
  γ : ∣ h ∣ ∘ (λ a → (f ̂ 𝑨) (λ i → (𝑡 i ̇ 𝑨) a)) ≡ (λ a → (f ̂ 𝑩)(λ i → (𝑡 i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣
  γ = (λ a → ∣ h ∣ ((f ̂ 𝑨)(λ i → (𝑡 i ̇ 𝑨) a)))     ≡⟨ gfe (λ a → ∥ h ∥ f ( λ r → (𝑡 r ̇ 𝑨) a )) ⟩
      (λ a → (f ̂ 𝑩)(λ i → ∣ h ∣ ((𝑡 i ̇ 𝑨) a)))     ≡⟨ ap (λ - → (λ a → (f ̂ 𝑩)(- a))) ih ⟩
      (λ a → (f ̂ 𝑩)(λ i → (𝑡 i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣ ∎
   where
    IH : ∀ a i → (∣ h ∣ ∘ (𝑡 i ̇ 𝑨)) a ≡ ((𝑡 i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a
    IH a i = extfun (comm-hom-term-intensional gfe 𝑨 𝑩 h (𝑡 i)) a

    ih : (λ a → (λ i → ∣ h ∣ ((𝑡 i ̇ 𝑨) a))) ≡ (λ a → (λ i → ((𝑡 i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a))
    ih = gfe λ a → gfe λ i → IH a i

-->
