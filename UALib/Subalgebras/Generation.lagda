---
layout: default
title : UALib.Subalgebras.Generation module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="subuniverse-generation">Subuniverse generation</a>

This section presents the [UALib.Subalgebras.Generation][] module of the [Agda Universal Algebra Library][].

If 𝑨 is an algebra and B ⊆ ∣ 𝑨 ∣ a subset of the universe of 𝑨, then the **subuniverse of** 𝑨 **generated by** B is typically denoted by Sg<sup>𝑨</sup>(B) and defined to be the smallest subuniverse of 𝑨 containing B.  Equivalently,

Sg<sup>𝑨</sup>(B)  =  ⋂ { U : U is a subuniverse of 𝑨 and  B ⊆ U }.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Subalgebras.Generation {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where


open import UALib.Subalgebras.Subuniverses{𝑆 = 𝑆}{gfe} public
open import Relation.Unary using (⋂) public

\end{code}

We now define an inductive type `Sg` that represents the subuniverse generated by a given collection of elements from the domain of an algebra.

\begin{code}

data Sg {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆)(X : Pred ∣ 𝑨 ∣ 𝓦) :
 Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤) where
  var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
  app : (f : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → Im 𝒂 ⊆ Sg 𝑨 X → (f ̂ 𝑨) 𝒂 ∈ Sg 𝑨 X

\end{code}

Let's now prove that, for any subset `X` of the domain `∣ 𝑨 ∣` of an algebra `𝑨`, the type `Sg X` does indeed represent a subuniverse of 𝑨.

\begin{code}

sgIsSub : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{X : Pred ∣ 𝑨 ∣ 𝓦} → Sg 𝑨 X ∈ Subuniverses 𝑨
sgIsSub = app

\end{code}

Next we show, by induction on the shape of its elements, `Sg X` is the smallest subuniverse of `𝑨` containing `X`.

\begin{code}

sgIsSmallest : {𝓤 𝓦 𝓡 : Universe}(𝑨 : Algebra 𝓤 𝑆){X : Pred ∣ 𝑨 ∣ 𝓦}(Y : Pred ∣ 𝑨 ∣ 𝓡)
 →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y  →  Sg 𝑨 X ⊆ Y

sgIsSmallest _ _ _ XinY (var Xv) = XinY Xv
sgIsSmallest 𝑨 Y YsubA XinY (app f 𝒂 SgXa) = fa∈Y
 where
  IH : Im 𝒂 ⊆ Y
  IH i = sgIsSmallest 𝑨 Y YsubA XinY (SgXa i)

  fa∈Y : (f ̂ 𝑨) 𝒂 ∈ Y
  fa∈Y = YsubA f 𝒂 IH

\end{code}

When the element of `Sg X` is constructed as `app f {a} ima⊆SgX`, we may assume (the induction hypothesis) that the arguments `a` belong to `Y`. Then the result of applying `f` to `a` must also belong to `Y`, since `Y` is a subuniverse.



#### <a id="subuniverse-lemmas">Subuniverse Lemmas</a>

Here we formalize a few basic properties of subuniverses.

First, the intersection of subuniverses is again a subuniverse.

\begin{code}

sub-inter-is-sub : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)
                   (I : 𝓤 ̇)(𝒜 : I → Pred ∣ 𝑨 ∣ 𝓤)
 →                 ((i : I) → 𝒜 i ∈ Subuniverses 𝑨)
                   --------------------------------
 →                 ⋂ I 𝒜 ∈ Subuniverses 𝑨

sub-inter-is-sub 𝑨 I 𝒜 Ai-is-Sub f a ima⊆⋂A = α
 where
  α : (f ̂ 𝑨) a ∈ ⋂ I 𝒜
  α i = Ai-is-Sub i f a λ j → ima⊆⋂A j i

\end{code}

Next, subuniverses are closed under the action of term operations.

\begin{code}

sub-term-closed : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓠 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓤)
 →                (B ∈ Subuniverses 𝑨) → (t : Term{𝓧} X)(b : X → ∣ 𝑨 ∣)
 →                (∀ x → b x ∈ B) → ((t ̇ 𝑨) b) ∈ B

sub-term-closed 𝑨 B AB (Term.generator x) b b∈B = b∈B x
sub-term-closed 𝑨 B AB (Term.node f args) b b∈B = AB f (λ z → (args z ̇ 𝑨) b)
                                                    (λ x → sub-term-closed 𝑨 B AB (args x) b b∈B)
\end{code}

Alternatively, we could express the preceeding fact using an inductive type.

\begin{code}

data TermImage {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤) where
 var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
 app : (f : ∣ 𝑆 ∣) (t : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → (∀ i → t i ∈ TermImage 𝑨 Y) → (f ̂ 𝑨) t ∈ TermImage 𝑨 Y

\end{code}

By what we proved above, it should come as no surprise that `TermImage 𝑨 Y` is a subuniverse of 𝑨 that contains Y.

\begin{code}

TermImageIsSub : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤} → TermImage 𝑨 Y ∈ Subuniverses 𝑨
TermImageIsSub = app

Y⊆TermImageY : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤} → Y ⊆ TermImage 𝑨 Y
Y⊆TermImageY {a} a∈Y = var a∈Y

\end{code}

Since `Sg 𝑨 Y` is the smallest subuniverse containing Y, we obtain the following inclusion.

\begin{code}

SgY⊆TermImageY : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓤) → Sg 𝑨 Y ⊆ TermImage 𝑨 Y
SgY⊆TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y⊆TermImageY

\end{code}




#### <a id="properties-of-homomorphisms">Homomorphic images are subuniverses</a>

Now that we have developed the machinery of subuniverse generation, we can prove two basic facts that play an important role in many theorems about algebraic structures.

First, the image of a homomorphism is a subuniverse of its codomain.

\begin{code}

hom-image-is-sub : {𝓤 𝓦 : Universe} → global-dfunext → {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
                   (ϕ : hom 𝑨 𝑩)  →  (HomImage 𝑩 ϕ) ∈ Subuniverses 𝑩

hom-image-is-sub gfe {𝑨}{𝑩} ϕ f b b∈Imf = eq ((f ̂ 𝑩) b) ((f ̂ 𝑨) ar) γ
 where
  ar : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
  ar = λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)

  ζ : ∣ ϕ ∣ ∘ ar ≡ b
  ζ = gfe (λ x → InvIsInv ∣ ϕ ∣(b x)(b∈Imf x))

  γ : (f ̂ 𝑩) b ≡ ∣ ϕ ∣((f ̂ 𝑨)(λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)))
  γ = (f ̂ 𝑩) b            ≡⟨ ap (f ̂ 𝑩)(ζ ⁻¹) ⟩
      (f ̂ 𝑩)(∣ ϕ ∣ ∘ ar)  ≡⟨(∥ ϕ ∥ f ar)⁻¹ ⟩
      ∣ ϕ ∣((f ̂ 𝑨) ar)    ∎

\end{code}


Next we prove the important fact that homomorphisms are uniquely determined by their values on a generating set.

\begin{code}

HomUnique : {𝓤 𝓦 : Universe} → funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
            (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →          (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
            --------------------------------------------
 →          (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x

HomUnique {𝓤}{𝓦} fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 𝒂 im𝒂⊆SgX) =
  ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )    ∎
 where induction-hypothesis = λ x → HomUnique{𝓤}{𝓦} fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

\end{code}


---------------------------------

[← UALib.Subalgebras.Subuniverses](UALib.Subalgebras.Subuniverses.html)
<span style="float:right;">[UALib.Subalgebras.Subalgebras →](UALib.Subalgebras.Subalgebras.html)</span>

{% include UALib.Links.md %}
