---
layout: default
title : UALib.Varieties.FreeAlgebras module (Agda Universal Algebra Library)
date : 2021-03-01
author: William DeMeo
---

## <a id="free-algebras-and-birkhoffs-theorem">Free Algebras and Birkhoff's Theorem</a>

This section presents the [UALib.Varieties.FreeAlgebras][] module of the [Agda Universal Algebra Library][].

First we will define the relatively free algebra in a variety, which is the "freest" algebra among (universal for) those algebras that model all identities holding in the variety. Then we give a formal proof of Birkhoff's theorem which says that a variety is an equational class. In other terms, a class `𝒦` of algebras is closed under the operators `H`, `S`, and `P` if and only if 𝒦 is the class of algebras that satisfy some set of identities.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Varieties.FreeAlgebras {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Varieties.Preservation {𝑆 = 𝑆}{gfe} public

\end{code}


#### <a id="the-free-algebra-in-theory">The free algebra in theory</a>

Recall, we proved in [the universal property](Terms.Basic.html#the-universal-property) section of the [Terms.Basic][] module that the term algebra `𝑻 X` is the absolutely free algebra in the class of all `𝑆`-structures. In this section, we formalize, for a given class `𝒦` of `𝑆`-algebras, the (relatively) free algebra in `S(P 𝒦)` over `X`.

We use the next definition to take a free algebra *for* a class `𝒦` and produce the free algebra *in* `𝒦`.

`Θ(𝒦, 𝑨) := {θ ∈ Con 𝑨 : 𝑨 / θ ∈ (S 𝒦)}` &nbsp; &nbsp; and &nbsp; &nbsp; `ψ(𝒦, 𝑨) := ⋂ Θ(𝒦, 𝑨)`.

Notice that `Θ(𝒦, 𝑨)` may be empty, in which case `ψ(𝒦, 𝑨) = 1` and then `𝑨 / ψ(𝒦, 𝑨)` is trivial.

The free algebra is constructed by applying the above definitions to the special case in which `𝑨` is the term algebra `𝑻 X` of `𝑆`-terms over `X`.

Since `𝑻 X` is free for (and in) the class of all `𝑆`-algebras, it follows that `𝑻 X` is free for every class `𝒦` of `𝑆`-algebras. Of course, `𝑻 X` is not necessarily a member of `𝒦`, but if we form the quotient of `𝑻 X` modulo the congruence `ψ(𝒦, 𝑻 X)`, which we denote by `𝔉 := (𝑻 X) / ψ(𝒦, 𝑻 X)`, then it's not hard to see that `𝔉` is a subdirect product of the algebras in `{(𝑻 𝑋) / θ}`, where `θ` ranges over `Θ(𝒦, 𝑻 X)`, so `𝔉` belongs to `S(P 𝒦)`, and it follows that `𝔉` satisfies all the identities satisfied by all members of `𝒦`.  Indeed, for each pair `p q : 𝑻 X`, if `𝒦 ⊧ p ≈ q`, then `p` and `q` must belong to the same `ψ(𝒦, 𝑻 X)`-class, so `p` and `q` are identified in the quotient `𝔉`.

The `𝔉` that we have just defined is called the **free algebra over** `𝒦` **generated by** `X` and (because of what we just observed) we may say that `𝔉` is free *in* `S(P 𝒦)`.<sup>[1](Varieties.FreeAlgebras.html#fn1)</sup>

#### <a id="the-free-algebra-in-agda">The free algebra in Agda</a>

Here we represent `𝔉` as a type in Agda by first constructing the congruence `ψ(𝒦, 𝑻 𝑋)` described above.

We assume two ambient universes `𝓤` and `𝓧`, as well as a type `X : 𝓧 ̇`. As usual, this is accomplished with the `module` directive.

\begin{code}

module the-free-algebra {𝓤 𝓧 : Universe}{X : 𝓧 ̇} where

 -- NOTATION (universe aliases for convenience and readability).
 𝓸𝓿𝓾 𝓸𝓿𝓾+ 𝓸𝓿𝓾++ : Universe
 𝓸𝓿𝓾 = ov 𝓤
 𝓸𝓿𝓾+ = 𝓸𝓿𝓾 ⁺
 𝓸𝓿𝓾++ = 𝓸𝓿𝓾 ⁺ ⁺

\end{code}

We first construct the congruence relation `ψCon`, modulo which `𝑻 X` yields the relatively free algebra, `𝔉 𝒦 X := 𝑻 X ╱ ψCon`. We start by letting `ψ` be the collection of identities `(p, q)` satisfied by all subalgebras of algebras in `𝒦`.

\begin{code}

 ψ : (𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾) → Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (𝓧 ⊔ 𝓸𝓿𝓾)
 ψ 𝒦 (p , q) = ∀(𝑨 : Algebra 𝓤 𝑆)(sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦)(h : X → ∣ 𝑨 ∣ )
                  →  (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q

 -- ψ : (𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾) → Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (𝓧 ⊔ 𝓸𝓿𝓾)
 -- ψ 𝒦 (p , q) = Π 𝔸 ꞉ (ℑ (S{𝓤}{𝓤} 𝒦)) ,  (free-lift ∣ 𝔸 ∣ (snd ∥ 𝔸 ∥)) p ≡ (free-lift ∣ 𝔸 ∣ (snd ∥ 𝔸 ∥)) q

\end{code}

We convert the predicate ψ into a relation by [currying](https://en.wikipedia.org/wiki/Currying).

\begin{code}

 ψRel : (𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾) → Rel ∣ 𝑻 X ∣ (𝓧 ⊔ 𝓸𝓿𝓾)
 ψRel 𝒦 p q = ψ 𝒦 (p , q)

\end{code}

To express `ψRel` as a congruence of the term algebra `𝑻 X`, we must prove that

1. `ψRel` is compatible with the operations of `𝑻 X` (which are jsut the terms themselves) and
2. `ψRel` it is an equivalence relation.

\begin{code}

 ψcompatible : (𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾) → compatible (𝑻 X)(ψRel 𝒦)
 ψcompatible 𝒦 𝑓 {p} {q} ψpq 𝑨 sA h = γ
  where
   ϕ : hom (𝑻 X) 𝑨
   ϕ = lift-hom 𝑨 h

   γ : ∣ ϕ ∣ ((𝑓 ̂ 𝑻 X) p) ≡ ∣ ϕ ∣ ((𝑓 ̂ 𝑻 X) q)

   γ = ∣ ϕ ∣ ((𝑓 ̂ 𝑻 X) p) ≡⟨ ∥ ϕ ∥ 𝑓 p ⟩
       (𝑓 ̂ 𝑨) (∣ ϕ ∣ ∘ p) ≡⟨ ap(𝑓 ̂ 𝑨)(gfe λ x → (ψpq x) 𝑨 sA h) ⟩
       (𝑓 ̂ 𝑨) (∣ ϕ ∣ ∘ q) ≡⟨ (∥ ϕ ∥ 𝑓 q)⁻¹ ⟩
       ∣ ϕ ∣ ((𝑓 ̂ 𝑻 X) q) ∎

 ψRefl : {𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾} → reflexive (ψRel 𝒦)
 ψRefl = λ _ _ _ _ → refl

 ψSymm : {𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾} → symmetric (ψRel 𝒦)
 ψSymm _ _ pψRelq 𝑪 ϕ h = (pψRelq 𝑪 ϕ h)⁻¹

 ψTrans : {𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾} → transitive (ψRel 𝒦)
 ψTrans _ _ _ pψq qψr 𝑪 ϕ h = (pψq 𝑪 ϕ h) ∙ (qψr 𝑪 ϕ h)

 ψIsEquivalence : {𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾} → IsEquivalence (ψRel 𝒦)
 ψIsEquivalence = record { rfl = ψRefl ; sym = ψSymm ; trans = ψTrans }

\end{code}

We have collected all the pieces necessary to express the collection of identities satisfied by all subalgebras of algebras in the class as a congruence relation of the term algebra. We call this congruence `ψCon` and define it using the Congruence constructor `mkcon`.

\begin{code}

 ψCon : (𝒦 : Pred (Algebra 𝓤 𝑆) 𝓸𝓿𝓾) → Congruence (𝑻 X)
 ψCon 𝒦 = mkcon (ψRel 𝒦) ψIsEquivalence (ψcompatible 𝒦)

\end{code}


Finally, we are ready to define the type representing the relatively free algebra in Agda.  We denote this type by 𝔉 and define it as the quotient `𝑻 X ╱ (ψCon 𝒦)`.

\begin{code}

module the-relatively-free-algebra
 {𝓤 𝓧 : Universe} {X : 𝓧 ̇} {𝒦 : Pred (Algebra 𝓤 𝑆) (ov 𝓤)} where

 open the-free-algebra{𝓤}{𝓧}{X}

 𝓕 : Universe -- (universe level of the relatively free algebra)
 𝓕 = (𝓧 ⊔ ov 𝓤) ⁺

 𝔉 : Algebra 𝓕 𝑆
 𝔉 =  𝑻 X ╱ (ψCon 𝒦)

\end{code}

The domain of `𝔉` is `∣ 𝔉 ∣ = ∣ 𝑻 X ∣ / ⟨ ψCon 𝒦 ⟩`, which is equal to

`Σ C ꞉ _ ,  Σ p ꞉ ∣ 𝑻 X ∣ ,  C ≡ ( [ p ] ⟨ ψCon 𝒦 ⟩ )`.

This Sigma type denotes the set `{ C : ∃ p ∈ ∣ 𝑻 X ∣ , C ≡ [ p ] ⟨ ψCon 𝒦 ⟩ }` of `⟨ ψCon 𝒦 ⟩`-classses of terms, as desired.

We left the type of `C` implicit (using the underscore symbol) for readability.  Since `C` denotes a particular class of the congruence relation `ψCon 𝒦` of `𝑻 X`, and since congruence classes are subsets of the domain of the underlying algebra, the type of `C` is a predicate on the type of terms; specifically, `C : Pred ∣ 𝑻 X ∣ (𝓧 ⊔ 𝓸𝓿𝓾)`.





-----------------------------




#### <a id="hsp-theorem">HSP Theorem</a>

This section presents a formal proof of the Birkhoff HSP theorem.<sup>[2](Varieties.FreeAlgebras.html#fn2)</sup>

To complete the proof of Birkhoff's HSP theorem, it remains to show that every algebra 𝑨 that belongs to `Mod X (Th (V 𝒦))`---i.e., every algebra that models the equations in `Th (V 𝒦)`---belongs to `V 𝒦`.  This will prove that `V 𝒦` is an equational class.  (The converse, that every equational class is a variety was already proved; see the remarks at the end of this module.)

We accomplish this goal by constructing an algebra `𝔽` with the following properties:

1. `𝔽 ∈ V 𝒦` and

2. Every `𝑨 ∈ Mod X (Th (V 𝒦))` is a homomorphic image of `𝔽`.

(In earlier versions of the [Agda UALib][], the free algebra 𝔉 developed in the [Birkhoff.FreeAlgebra][] section played the role of the algebra 𝔽 with properties 1 and 2.  However, we found a more direct path to the proof using the algebra `𝔽 := (𝑻 X) [ ℭ ]/ker homℭ`.)

We denote by `ℭ` the product of all subalgebras of algebras in `𝒦`, and by `homℭ` the homomorphism from `𝑻 X` to `ℭ` defined as follows:

`homℭ := ⨅-hom-co (𝑻 X) 𝔄s hom𝔄`.

Here, `⨅-hom-co` (defined in [Homomorphisms.Basic](Homomorphisms.Basic.html#product-homomorphisms)) takes the term algebra `𝑻 X`, a family `{𝔄s : I → Algebra 𝓤 𝑆}` of `𝑆`-algebras, and a family `hom𝔄 : ∀ i → hom (𝑻 X) (𝔄s i)` of homomorphisms and constructs the natural homomorphism `homℭ` from `𝑻 X` to the product `ℭ := ⨅ 𝔄`.  The homomorphism `homℭ : hom (𝑻 X) (⨅ ℭ)` is natural in the sense that the `i`-th component of the image of `𝑡 : Term X` under `homℭ` is the image `∣ hom𝔄 i ∣ 𝑡` of 𝑡 under the i-th homomorphism `hom𝔄 i`.

In this module we fix `𝓤`, `X`, and `𝒦` in advance and assume `𝕏`, which supplies, for each algebra `𝑨`, a surjective map `∣ 𝕏 𝑨 ∣` from `X` onto `𝑨`.

\begin{code}

module HSPTheorem
 {𝓤 : Universe} {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆) (ov 𝓤)}
 {𝕏 : {𝓤 : Universe}(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

 open the-free-algebra {𝓤}{𝓤}{X}
 open the-relatively-free-algebra {𝓤}{𝓤}{X}{𝒦}
 open class-products-with-maps {𝓤}{X} 𝒦

\end{code}


#### <a id="F-in-classproduct">𝔽 ≤  ⨅ S(𝒦)</a>
Now we come to a step in the Agda formalization of Birkhoff's theorem that turns out to be surprisingly nontrivial. We must prove that the free algebra embeds in the product ℭ of all subalgebras of algebras in the class `𝒦`.  This is really the only stage in the proof of Birkhoff's theorem that requires the truncation assumption that `ℭ` be a set.

We begin by constructing `ℭ`, using the techniques described in the section on <a href="https://ualib.gitlab.io/Varieties.Varieties.html#products-of-classes">products of classes</a>.

\begin{code}

 -- NOTATION.
 SK𝔄 : (i : ℑ) → (𝔄 i) ∈ S{𝓤}{𝓤} 𝒦
 SK𝔄 = λ (i : ℑ) → fst ∥ i ∥

 𝔄h : (i : ℑ) → X → ∣ 𝔄 i ∣
 𝔄h = λ (i : ℑ) → snd ∥ i ∥

 -- ℭ is the product of all subalgebras of algebras in 𝒦.
 ℭ : Algebra 𝓸𝓿𝓾 𝑆
 ℭ = ⨅ 𝔄

\end{code}

Observe that the inhabitants of `ℭ` are maps from `ℑs` to `{𝔄s i : i ∈ ℑs}`.

\begin{code}

 hom𝔄 : ∀ i → hom (𝑻 X) (𝔄 i)
 hom𝔄 i = lift-hom (𝔄 i) (𝔄h i)

 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co {fe = gfe} 𝔄 hom𝔄

\end{code}


#### <a id="the-new-free-algebra">The new free algebra</a>

As mentioned above, the initial version of the [Agda UALib][] used the free algebra `𝔉` developed above.  However, our new, more direct proof uses the algebra `𝔽`, which we now define, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.<sup>[3](Varieties.FreeAlgebras.html#fn3)</sup>

\begin{code}

 𝔽 : Algebra 𝓸𝓿𝓾+ 𝑆
 𝔽 = (𝑻 X) [ ℭ ]/ker homℭ

 epi𝔽 : epi (𝑻 X) 𝔽
 epi𝔽 = πker ℭ homℭ

 hom𝔽 : hom (𝑻 X) 𝔽
 hom𝔽 = epi-to-hom 𝔽 epi𝔽

 hom𝔽-is-epic : Epic ∣ hom𝔽 ∣
 hom𝔽-is-epic = snd ∥ epi𝔽 ∥

\end{code}

We will need the following facts relating `homℭ`, `hom𝔽`, `and ψ`.

\begin{code}

 ψlemma0 : ∀ p q → (∣ homℭ ∣ p ≡ ∣ homℭ ∣ q) → (p , q) ∈ ψ 𝒦
 ψlemma0 p q phomℭq 𝑨 sA h = cong-app phomℭq (𝑨 , sA , h)

 ψlemma0-ap : {𝑨 : Algebra 𝓤 𝑆}{h : X → ∣ 𝑨 ∣} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦
  →           kernel ∣ hom𝔽 ∣ ⊆ kernel (free-lift 𝑨 h)

 ψlemma0-ap {𝑨}{h} skA {p , q} x = γ where

   ν : ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q
   ν = ker-in-con (𝑻 X) (kercon ℭ homℭ) p q x

   γ : (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q
   γ = ((ψlemma0 p q) ν) 𝑨 skA h


\end{code}

We now use `ψlemma0-ap` to prove that every map `h : X → ∣ 𝑨 ∣`, from `X` to a subalgebra `𝑨 ∈ S 𝒦` of `𝒦`, lifts to a homomorphism from `𝔽` to `𝑨`.

\begin{code}

 𝔽-lift-hom : (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → (X → ∣ 𝑨 ∣) → hom 𝔽 𝑨
 𝔽-lift-hom 𝑨 skA h = fst(HomFactor (𝑻 X){𝑨}{𝔽}(lift-hom 𝑨 h) hom𝔽 hom𝔽-is-epic (ψlemma0-ap skA))

\end{code}


#### <a id="k-models-psi">𝒦 models ψ</a>

The goal of this subsection is to prove that `𝒦` models `ψ 𝒦`. In other terms, for all pairs `(p , q) ∈ Term X × Term X` of terms, if `(p , q) ∈ ψ 𝒦`, then `𝒦 ⊧ p ≋ q`.

Next we define the lift of the natural embedding from `X` into 𝔽. We denote this homomorphism by `𝔑 : hom (𝑻 X) 𝔽` and define it as follows.

\begin{code}

 X↪𝔽 : X → ∣ 𝔽 ∣
 X↪𝔽 x = ⟦ ℊ x ⟧

 𝔑 : hom (𝑻 X) 𝔽
 𝔑 = lift-hom 𝔽 X↪𝔽

\end{code}

It turns out that the homomorphism so defined is equivalent to `hom𝔽`.

\begin{code}

 hom𝔽-is-lift-hom : ∀ p → ∣ 𝔑 ∣ p ≡ ∣ hom𝔽 ∣ p
 hom𝔽-is-lift-hom (ℊ x) = refl
 hom𝔽-is-lift-hom (node 𝑓 𝒕) =
  ∣ 𝔑 ∣ (node 𝑓 𝒕)              ≡⟨ ∥ 𝔑 ∥ 𝑓 𝒕 ⟩
  (𝑓 ̂ 𝔽)(λ i → ∣ 𝔑 ∣(𝒕 i))      ≡⟨ ap(𝑓 ̂ 𝔽)(gfe (λ x → hom𝔽-is-lift-hom(𝒕 x))) ⟩
  (𝑓 ̂ 𝔽)(λ i → ∣ hom𝔽 ∣ (𝒕 i))  ≡⟨ (∥ hom𝔽 ∥ 𝑓 𝒕)⁻¹ ⟩
  ∣ hom𝔽 ∣ (node 𝑓 𝒕)           ∎


\end{code}

We need a three more lemmas before we are ready to tackle our main goal.

\begin{code}

 ψlemma1 : kernel ∣ 𝔑 ∣ ⊆ ψ 𝒦
 ψlemma1 {p , q} 𝔑pq 𝑨 sA h = γ
  where
   f : hom 𝔽 𝑨
   f = 𝔽-lift-hom 𝑨 sA h

   h' ϕ : hom (𝑻 X) 𝑨
   h' = ∘-hom (𝑻 X) 𝑨 𝔑 f
   ϕ = lift-hom 𝑨 h

   f𝔑≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ 𝔑 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
   f𝔑≡ϕ x = refl
   h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ 𝔑 ∣) t ≡ ∣ ϕ ∣ t
   h≡ϕ t = free-unique gfe 𝑨 h' ϕ f𝔑≡ϕ t

   γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
   γ = ∣ ϕ ∣ p         ≡⟨ (h≡ϕ p)⁻¹ ⟩
       ∣ f ∣ ( ∣ 𝔑 ∣ p ) ≡⟨ ap ∣ f ∣ 𝔑pq ⟩
       ∣ f ∣ ( ∣ 𝔑 ∣ q ) ≡⟨ h≡ϕ q ⟩
       ∣ ϕ ∣ q ∎


 ψlemma2 : kernel ∣ hom𝔽 ∣ ⊆ ψ 𝒦
 ψlemma2 {p , q} hyp = ψlemma1 {p , q} γ
   where
    γ : (free-lift 𝔽 X↪𝔽) p ≡ (free-lift 𝔽 X↪𝔽) q
    γ = (hom𝔽-is-lift-hom p) ∙ hyp ∙ (hom𝔽-is-lift-hom q)⁻¹


 ψlemma3 : ∀ p q → (p , q) ∈ ψ 𝒦 → 𝒦 ⊧ p ≋ q
 ψlemma3 p q pψq {𝑨} kA = γ
  where
   skA : 𝑨 ∈ S 𝒦
   skA = siso (sbase kA) (≅-sym Lift-≅)

   γ : (p ̇ 𝑨) ≡ (q ̇ 𝑨)
   γ = gfe λ h → (p ̇ 𝑨) h         ≡⟨ free-lift-interp gfe 𝑨 h p ⟩
                 (free-lift 𝑨 h) p ≡⟨ pψq 𝑨 skA h ⟩
                 (free-lift 𝑨 h) q ≡⟨ (free-lift-interp gfe 𝑨 h q)⁻¹  ⟩
                 (q ̇ 𝑨) h         ∎

\end{code}

With these results in hand, it is now trivial to prove the main theorem of this subsection.

\begin{code}

 class-models-kernel : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝒦 ⊧ p ≋ q
 class-models-kernel  p q hyp = ψlemma3 p q (ψlemma2 hyp)

\end{code}


#### <a id="the-homomorphic-images-of-F">The homomorphic images of 𝔽</a>

Finally we come to one of the main theorems of this module; it asserts that every algebra in `Mod X (Th 𝕍𝒦)` is a homomorphic image of 𝔽.  We prove this below as the function (or proof object) `𝔽-ModTh-epi`.  Before that, we prove two auxiliary lemmas.

\begin{code}

 kernel-in-theory : kernel ∣ hom𝔽 ∣ ⊆ Th (V 𝒦)
 kernel-in-theory {p , q} pKq = (class-ids-⇒ p q (class-models-kernel p q pKq))

 open Congruence

 free-quot-subalg-ℭ : dfunext 𝓥 (ov 𝓤 ) → prop-ext (ov 𝓤) (ov 𝓤) → is-set ∣ ℭ ∣
  →                   (∀ p q → is-subsingleton (⟨ kercon ℭ homℭ ⟩ p q))
  →                   (∀ C → is-subsingleton (𝒞 ⟨ kercon ℭ homℭ ⟩ C))
                      -----------------------------------------------------------
  →                   ((𝑻 X) [ ℭ ]/ker homℭ) ≤ ℭ

 free-quot-subalg-ℭ fe pe Cset ssR ssC = FirstHomCorollary fe pe (𝑻 X) ℭ homℭ Cset ssR ssC


 module _ -- extensionality assumptions:
          (fe : dfunext 𝓥 (ov 𝓤))
          (hfe : hfunext (ov 𝓤)(ov 𝓤))
          (pe : prop-ext (ov 𝓤)(ov 𝓤))

          -- truncation assumptions:
          (Cset : is-set ∣ ℭ ∣)
          (ssR : ∀ p q → is-subsingleton (⟨ kercon ℭ homℭ ⟩ p q))
          (ssC : ∀ C → is-subsingleton (𝒞 ⟨ kercon ℭ homℭ ⟩ C))

  where

  𝔽≤ℭ : ((𝑻 X) [ ℭ ]/ker homℭ) ≤ ℭ
  𝔽≤ℭ = free-quot-subalg-ℭ fe pe Cset ssR ssC

  𝕍𝒦 : Pred (Algebra 𝓸𝓿𝓾+ 𝑆) 𝓸𝓿𝓾++
  𝕍𝒦 = V{𝓤}{𝓸𝓿𝓾+} 𝒦

  𝔽-ModTh-epi : (𝑨 : Algebra 𝓸𝓿𝓾+ 𝑆) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
  𝔽-ModTh-epi 𝑨 AinMTV = γ
   where
    ϕ : hom (𝑻 X) 𝑨
    ϕ = lift-hom 𝑨 (fst(𝕏 𝑨))

    ϕE : Epic ∣ ϕ ∣
    ϕE = lift-of-epi-is-epi (snd (𝕏 𝑨))

    pqlem2 : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝑨 ⊧ p ≈ q
    pqlem2 p q hyp = AinMTV p q (kernel-in-theory hyp)

    kerincl : kernel ∣ hom𝔽 ∣ ⊆ kernel ∣ ϕ ∣
    kerincl {p , q} x = γ
     where
      Apq : 𝑨 ⊧ p ≈ q
      Apq = pqlem2 p q x
      γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
      γ = ∣ ϕ ∣ p                    ≡⟨ refl ⟩
          free-lift 𝑨 (fst(𝕏 𝑨)) p   ≡⟨ (free-lift-interp gfe 𝑨 (fst(𝕏 𝑨)) p)⁻¹ ⟩
          (p ̇ 𝑨) (fst(𝕏 𝑨))          ≡⟨ extfun (pqlem2 p q x) (fst(𝕏 𝑨))  ⟩
          (q ̇ 𝑨) (fst(𝕏 𝑨))          ≡⟨ free-lift-interp gfe 𝑨 (fst(𝕏 𝑨)) q ⟩
          free-lift 𝑨 (fst(𝕏 𝑨)) q   ≡⟨ refl ⟩
          ∣ ϕ ∣ q                    ∎

    γ : epi 𝔽 𝑨
    γ = fst (HomFactorEpi (𝑻 X){𝑨}{𝔽} ϕ ϕE hom𝔽 hom𝔽-is-epic  kerincl)


\end{code}

#### <a id="F-in-VK">𝔽 ∈ V(𝒦)</a>

With this result in hand, along with what we proved earlier---namely, `PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ V 𝒦`---it is not hard to show that `𝔽` belongs to `V 𝒦`.

\begin{code}

  𝔽∈SP : 𝔽 ∈ (S{𝓸𝓿𝓾}{𝓸𝓿𝓾+} (P{𝓤}{𝓸𝓿𝓾} 𝒦))
  𝔽∈SP = ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

  𝔽∈𝕍 : 𝔽 ∈ V 𝒦
  𝔽∈𝕍 = SP⊆V' 𝔽∈SP

\end{code}

#### <a id="the-hsp-theorem"> The HSP Theorem</a>

Now that we have all of the necessary ingredients, it is all but trivial to combine them to prove Birkhoff's HSP theorem.

\begin{code}

  birkhoff : Mod (Th (V 𝒦)) ⊆ V 𝒦

  birkhoff {𝑨} α = γ
   where
    γ : 𝑨 ∈ (V 𝒦)
    γ = vhimg 𝔽∈𝕍 ((𝑨 , 𝔽-ModTh-epi 𝑨 α ) , ≅-refl)

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod X (Th (V 𝒦))`, is a simple consequence of the fact that `Mod Th` is a closure operator. Nonetheless, completeness demands that we formalize this inclusion as well, however trivial the proof.

\begin{code}

  birkhoff' : V{𝓤}{𝓸𝓿𝓾} 𝒦 ⊆ Mod {X = X}(Th (V 𝒦))
  birkhoff' α p q pThq = pThq α

\end{code}

We have thus proved that every variety is an equational class.  Readers familiar with the classical formulation of the Birkhoff HSP theorem, as an "if and only if" result, might worry that we haven't completed the proof.  But recall that in the [Varieties.Preservation][] module we proved the following identity preservation lemmas:

* [(H-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#964) 𝒦 ⊧ p ≋ q → H 𝒦 ⊧ p ≋ q
* [(S-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#2592) 𝒦 ⊧ p ≋ q → S 𝒦 ⊧ p ≋ q
* [(P-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#4111) 𝒦 ⊧ p ≋ q → P 𝒦 ⊧ p ≋ q

From these it follows that every equational class is a variety. Thus, our formal proof of Birkhoff's theorem is complete.

----------------------------

<span class="footnote" id="fn1"><sup>1</sup>Since `X` is not a subset of `𝔉`, technically it doesn't make sense to say "`X` generates `𝔉`." But as long as 𝒦 contains a nontrivial algebra, we will have `ψ(𝒦, 𝑻 𝑋) ∩ X² ≠ ∅`, and we can identify `X` with `X / ψ(𝒦, 𝑻 X)` which does belong to 𝔉.</span>

<span class="footnote" id="fn2"><sup>1</sup> In the previous version of the [UALib][] this section was part of a module called HSPTheorem module.</span>

<span class="footnote" id="fn3"><sup>3</sup> It might be an instructive exercise to prove that `𝔽` is, in fact, isomorphic to the algebra `𝔉` that we defined earlier.</span>

<p></p>
<p></p>


[← Varieties.Preservation](Varieties.Preservation.html)
<span style="float:right;">[Varieties ↑](Varieties.html)</span>

{% include UALib.Links.md %}
