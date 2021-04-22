---
layout: default
title : Homomorphisms.HomomorphicImages module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="homomorphic-images">Homomorphic Images</a>

This section describes the [Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Homomorphisms.HomomorphicImages where

open import Homomorphisms.Isomorphisms public

module hom-images {𝑆 : Signature 𝓞 𝓥} where
 open isomorphisms {𝑆 = 𝑆} public
\end{code}


#### <a id="images-of-a-single-algebra">Images of a single algebra</a>

We begin with what seems, for our purposes, the most useful way to represent the class of **homomorphic images** of an algebra in dependent type theory.

\begin{code}

 HomImage : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → Set(𝓤 ⊔ 𝓦)
 HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b

 HomImagesOf : Algebra 𝓤 𝑆 → Set(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ lsuc 𝓦)
 HomImagesOf {𝓤}{𝓦} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓦 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : Algebra 𝓤 𝑆`, the type `HomImagesOf 𝑨` denotes the class of algebras `𝑩 : Algebra 𝓦 𝑆` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.

Since we take the class of homomorphic images of an algebra to be closed under isomorphism, we consider `𝑩` to be a homomorphic image of `𝑨` if there exists an algebra `𝑪` which is a homomorphic image of `𝑨` and isomorphic to `𝑩`. The following type expresses this.

\begin{code}

 module _ {𝓤 𝓦 : Level} where

  _is-hom-image-of_ : (𝑩 : Algebra 𝓦 𝑆)(𝑨 : Algebra 𝓤 𝑆) → Set(ov 𝓦 ⊔ 𝓤)
  𝑩 is-hom-image-of 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf{𝓤}{𝓦} 𝑨) , ∣ 𝑪ϕ ∣ ≅ 𝑩

\end{code}


#### <a id="images-of-a-class-of-algebras">Images of a class of algebras</a>

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.

\begin{code}

 _is-hom-image-of-class_ : Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(lsuc 𝓤) → Set(ov 𝓤)
 𝑩 is-hom-image-of-class 𝓚 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

 HomImagesOfClass : Pred (Algebra 𝓤 𝑆) (lsuc 𝓤) → Set(ov 𝓤)
 HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ 𝑆) , (𝑩 is-hom-image-of-class 𝓚)

\end{code}



#### <a id="lifting-tools">Lifting tools</a>

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's HSP theorem).

The first states and proves the simple fact that the lift of an epimorphism is an epimorphism.

\begin{code}

 module _ {𝓤 𝓦 𝓩 : Level} where

  open Lift

  lift-of-alg-epic-is-epic : {𝑨 : Algebra 𝓧 𝑆}(𝑩 : Algebra 𝓨 𝑆)(h : hom 𝑨 𝑩)
   →                         Epic ∣ h ∣  →  Epic ∣ Lift-hom 𝓩 𝓦 𝑩 h ∣

  lift-of-alg-epic-is-epic {𝑨 = 𝑨} 𝑩 h hepi y = eq y (lift a) η
   where
   lh : hom (Lift-alg 𝑨 𝓩) (Lift-alg 𝑩 𝓦)
   lh = Lift-hom _ _ 𝑩 h

   ζ : Image ∣ h ∣ ∋ (lower y)
   ζ = hepi (lower y)

   a : ∣ 𝑨 ∣
   a = Inv ∣ h ∣ ζ

   β : lift (∣ h ∣ a) ≡ (lift ∘ ∣ h ∣ ∘ lower{𝓦}) (lift a)
   β = ap (λ - → lift (∣ h ∣ ( - a))) (lower∼lift{𝓦} )

   η : y ≡ ∣ lh ∣ (lift a)
   η = y               ≡⟨ (happly lift∼lower) y ⟩
       lift (lower y)  ≡⟨ ap lift (InvIsInv ∣ h ∣ ζ)⁻¹ ⟩
       lift (∣ h ∣ a)  ≡⟨ β ⟩
       ∣ lh ∣ (lift a) ∎


  Lift-alg-hom-image : {𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆} → 𝑩 is-hom-image-of 𝑨
   →                   (Lift-alg 𝑩 𝓦) is-hom-image-of (Lift-alg 𝑨 𝓩)

  Lift-alg-hom-image {𝑨 = 𝑨}{𝑩} ((𝑪 , ϕ , ϕhom , ϕepic) , C≅B) =
   (Lift-alg 𝑪 𝓦 , ∣ lϕ ∣ , ∥ lϕ ∥ , lϕepic) , Lift-alg-iso C≅B
    where
    lϕ : hom (Lift-alg 𝑨 𝓩) (Lift-alg 𝑪 𝓦)
    lϕ = (Lift-hom 𝓩 𝓦 𝑪) (ϕ , ϕhom)

    lϕepic : Epic ∣ lϕ ∣
    lϕepic = lift-of-alg-epic-is-epic 𝑪 (ϕ , ϕhom) ϕepic

\end{code}

--------------------------------------

[← Homomorphisms.Isomorphisms](Homomorphisms.Isomorphisms.html)
<span style="float:right;">[Terms →](Terms.html)</span>

{% include UALib.Links.md %}
