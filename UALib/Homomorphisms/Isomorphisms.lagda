---
layout: default
title : Homomorphisms.Isomoprhisms module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="isomorphisms">Isomorphisms</a>

This section describes the [Homomorphisms.Isomorphisms][] module of the [Agda Universal Algebra Library][].
Here we formalize the informal notion of isomorphism between algebraic structures.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Homomorphisms.Isomorphisms where

open import Homomorphisms.Noether public
open import MGS-Embeddings using (Nat; NatΠ; NatΠ-is-embedding) public


module isomorphisms {𝑆 : Signature 𝓞 𝓥} where
 open noether {𝑆 = 𝑆} public

\end{code}

#### <a id="isomorphism-toolbox">Definition of isomorphism</a>

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of **isomorphism**.

\begin{code}

 _≅_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → Set(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
 𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) , (∣ f ∣ ∘ ∣ g ∣ ∼ ∣ 𝒾𝒹 𝑩 ∣)
                                            × (∣ g ∣ ∘ ∣ f ∣ ∼ ∣ 𝒾𝒹 𝑨 ∣)

\end{code}

That is, two structures are **isomorphic** provided there are homomorphisms going back and forth between them which compose to the identity map.



#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>

\begin{code}

 ≅-refl : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≅ 𝑨
 ≅-refl {𝑨 = 𝑨} = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , (λ a → refl) , (λ a → refl)

 ≅-sym : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} → 𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
 ≅-sym h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

 ≅-trans : {𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆} → 𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪
 ≅-trans {𝑨 = 𝑨}{𝑩}{𝑪} ab bc = f , g , α , β
  where
   f1 : hom 𝑨 𝑩
   f1 = ∣ ab ∣
   f2 : hom 𝑩 𝑪
   f2 = ∣ bc ∣
   f : hom 𝑨 𝑪
   f = ∘-hom 𝑨 𝑪 f1 f2

   g1 : hom 𝑪 𝑩
   g1 = fst ∥ bc ∥
   g2 : hom 𝑩 𝑨
   g2 = fst ∥ ab ∥
   g : hom 𝑪 𝑨
   g = ∘-hom 𝑪 𝑨 g1 g2

   α : ∣ f ∣ ∘ ∣ g ∣ ∼ ∣ 𝒾𝒹 𝑪 ∣
   α x = (ap ∣ f2 ∣(∣ snd ∥ ab ∥ ∣ (∣ g1 ∣ x)))∙(∣ snd ∥ bc ∥ ∣) x

   β : ∣ g ∣ ∘ ∣ f ∣ ∼ ∣ 𝒾𝒹 𝑨 ∣
   β x = (ap ∣ g2 ∣(∥ snd ∥ bc ∥ ∥ (∣ f1 ∣ x)))∙(∥ snd ∥ ab ∥ ∥) x

\end{code}

#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of the universe hierarchy discussed in [Overture.Lifts][].

\begin{code}

 open Lift

 Lift-≅ : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≅ (Lift-alg 𝑨 𝓦)
 Lift-≅ {𝓤}{𝓦}{𝑨} = 𝓁𝒾𝒻𝓉 , (𝓁ℴ𝓌ℯ𝓇{𝓤}{𝓦}{𝑨}) , happly lift∼lower , happly (lower∼lift{𝓦})

 Lift-hom : (𝓧 𝓨 : Level){𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆) → hom 𝑨 𝑩 → hom (Lift-alg 𝑨 𝓧)(Lift-alg 𝑩 𝓨)
 Lift-hom 𝓧 𝓨 {𝑨} 𝑩 (f , fhom) = lift ∘ f ∘ lower , γ
  where
  lABh : is-homomorphism (Lift-alg 𝑨 𝓧) 𝑩 (f ∘ lower)
  lABh = ∘-is-hom (Lift-alg 𝑨 𝓧) 𝑩 {lower}{f} (λ _ _ → refl) fhom

  γ : is-homomorphism(Lift-alg 𝑨 𝓧)(Lift-alg 𝑩 𝓨) (lift ∘ (f ∘ lower))
  γ = ∘-is-hom (Lift-alg 𝑨 𝓧) (Lift-alg 𝑩 𝓨){f ∘ lower}{lift} lABh λ _ _ → refl


 Lift-alg-iso : {𝓧 𝓨 : Level}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
  →             𝑨 ≅ 𝑩 → (Lift-alg 𝑨 𝓧) ≅ (Lift-alg 𝑩 𝓨)

 Lift-alg-iso A≅B = ≅-trans (≅-trans (≅-sym Lift-≅) A≅B) Lift-≅

\end{code}




#### <a id="lift-associativity">Lift associativity</a>

The lift is also associative, up to isomorphism at least.

\begin{code}

 Lift-alg-assoc : {𝓘 : Level}{𝑨 : Algebra 𝓤 𝑆} → Lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (Lift-alg (Lift-alg 𝑨 𝓦) 𝓘)
 Lift-alg-assoc {𝓤}{𝓦}{𝓘} {𝑨} = ≅-trans (≅-trans γ Lift-≅) Lift-≅
  where
  γ : Lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ 𝑨
  γ = ≅-sym Lift-≅

 Lift-alg-associative : {𝓘 : Level}(𝑨 : Algebra 𝓤 𝑆) → Lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (Lift-alg (Lift-alg 𝑨 𝓦) 𝓘)
 Lift-alg-associative 𝑨 = Lift-alg-assoc {𝑨 = 𝑨}

\end{code}




#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.

\begin{code}

 module _ {𝓘 : Level}{I : Set 𝓘}{fe𝓘𝓤 : dfunext 𝓘 𝓤}{fe𝓘𝓦 : dfunext 𝓘 𝓦} where

  ⨅≅ : {𝒜 : I → Algebra 𝓤 𝑆}{ℬ : I → Algebra 𝓦 𝑆} → Π i ꞉ I , 𝒜 i ≅ ℬ i → ⨅ 𝒜 ≅ ⨅ ℬ

  ⨅≅ {𝒜}{ℬ} AB = γ
   where
   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = ∣ fst (AB i) ∣ (a i)

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fe𝓘𝓦 (λ i → ∥ fst (AB i) ∥ 𝑓 (λ x → a x i))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ fst ∥ AB i ∥ ∣ (b i)

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fe𝓘𝓤 (λ i → snd ∣ snd (AB i) ∣ 𝑓 (λ x → 𝒃 x i))

   ϕ~ψ : ϕ ∘ ψ ∼ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ~ψ 𝒃 = fe𝓘𝓦 λ i → fst ∥ snd (AB i) ∥ (𝒃 i)

   ψ~ϕ : ψ ∘ ϕ ∼ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ~ϕ a = fe𝓘𝓤 λ i → snd ∥ snd (AB i) ∥ (a i)

   γ : ⨅ 𝒜 ≅ ⨅ ℬ
   γ = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

\end{code}


A nearly identical proof goes through for isomorphisms of lifted products (though, just for fun, we use the universal quantifier syntax here to express the dependent function type in the statement of the lemma, instead of the Pi notation we used in the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of `Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)

\begin{code}

 module _ {𝓘 𝓩 : Level}{I : Set 𝓘}{fizw : dfunext (𝓘 ⊔ 𝓩) 𝓦}{fiu : dfunext 𝓘 𝓤} where

  Lift-alg-⨅≅ : {𝒜 : I → Algebra 𝓤 𝑆}{ℬ : (Lift{𝓩} I) → Algebra 𝓦 𝑆}
   →            (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-alg (⨅ 𝒜) 𝓩 ≅ ⨅ ℬ

  Lift-alg-⨅≅ {𝒜}{ℬ} AB = γ
   where
   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = ∣ fst (AB  (lower i)) ∣ (a (lower i))

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fizw (λ i → (∥ fst (AB (lower i)) ∥) 𝑓 (λ x → a x (lower i)))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ fst ∥ AB i ∥ ∣ (b (lift i))

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fiu (λ i → (snd ∣ snd (AB i) ∣) 𝑓 (λ x → 𝒃 x (lift i)))

   ϕ~ψ : ϕ ∘ ψ ∼ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ~ψ 𝒃 = fizw λ i → fst ∥ snd (AB (lower i)) ∥ (𝒃 i)

   ψ~ϕ : ψ ∘ ϕ ∼ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ~ϕ a = fiu λ i → snd ∥ snd (AB i) ∥ (a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

   γ : Lift-alg (⨅ 𝒜) 𝓩 ≅ ⨅ ℬ
   γ = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}






#### <a id="embedding-tools">Embedding tools</a>

Finally, we prove some useful facts about embeddings that occasionally come in handy.

\begin{code}

 iso→embedding : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}(ϕ : 𝑨 ≅ 𝑩) → is-embedding (fst ∣ ϕ ∣)
 iso→embedding ϕ = equivs-are-embeddings (fst ∣ ϕ ∣) (invertibles-are-equivs (fst ∣ ϕ ∣) finv)
  where
  finv : invertible (fst ∣ ϕ ∣)
  finv = ∣ fst ∥ ϕ ∥ ∣ , (snd ∥ snd ϕ ∥ , fst ∥ snd ϕ ∥)

 module _ {𝓘 : Level}{I : Set 𝓘}{hiu : hfunext 𝓘 𝓤}{hiw : hfunext 𝓘 𝓦} where

  embedding-lift-nat : {A : I → Set 𝓤}{B : I → Set 𝓦}(h : Nat A B)
   →                   (∀ i → is-embedding (h i)) → is-embedding(NatΠ h)

  embedding-lift-nat h hem = NatΠ-is-embedding hiu hiw h hem


  embedding-lift-nat' : {𝒜 : I → Algebra 𝓤 𝑆}{ℬ : I → Algebra 𝓦 𝑆}(h : Nat(fst ∘ 𝒜)(fst ∘ ℬ))
   →                    (∀ i → is-embedding (h i)) → is-embedding(NatΠ h)

  embedding-lift-nat' h hem = NatΠ-is-embedding hiu hiw h hem


  embedding-lift : {𝒜 : I → Algebra 𝓤 𝑆}{ℬ : I → Algebra 𝓦 𝑆}(h : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣)
   →               (∀ i → is-embedding (h i)) → is-embedding(λ (x : ∣ ⨅ 𝒜 ∣) (i : I) → (h i)(x i))

  embedding-lift {𝒜}{ℬ} h hem = embedding-lift-nat' {𝒜}{ℬ} h hem


\end{code}

--------------------------------------


<br>

[← Homomorphisms.Noether](Homomorphisms.Noether.html)
<span style="float:right;">[Homomorphisms.HomomorphicImages →](Homomorphisms.HomomorphicImages.html)</span>

{% include UALib.Links.md %}

