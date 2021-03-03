---
layout: default
title : UALib.Prelude.Inverses module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="inverses">Inverses</a>

This section presents the [UALib.Prelude.Inverses][] module of the [Agda Universal Algebra Library][].
Here we define (the syntax of) a type for the (semantic concept of) **inverse image** of a function.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude.Inverses where

-- Public imports (inherited by modules importing this one)
open import Prelude.Extensionality public 

open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁) public
open import MGS-Subsingleton-Truncation using (_∙_) public
open import MGS-MLTT using (_⁻¹; _∘_; 𝑖𝑑; domain; codomain) public
open import MGS-Embeddings using (equivs-are-embeddings; invertible;
 invertibles-are-equivs) public

module _ {𝓤 𝓦 : Universe} where


 data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

 ImageIsImage : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B)(b : B)(a : A)
                ---------------------------------------------
  →             b ≡ f a → Image f ∋ b

 ImageIsImage f b a b≡fa = eq b a b≡fa

\end{code}

The following restatement of the last lemma simply rearranges the arguments in case that makes it clearer.

\begin{code}

 ImageIsImage' : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B)(a : A)(b : B)
                  ---------------------------------------------
  →               f a ≡ b  →  Image f ∋ b

 ImageIsImage' f a b fab = eq b a (fab ⁻¹)

\end{code}

Note that an inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a "witness" `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a witness-proof pair, `(a , p) : Image f ∋ b`, and returns `a`.

\begin{code}

 Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B){b : B} → Image f ∋ b  →  A
 Inv f {.(f a)} (im a) = a
 Inv f (eq _ a _) = a

\end{code}

We can prove that `Inv f` is the right-inverse of `f`, as follows.

\begin{code}

 InvIsInv : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B){b : B}(b∈Imgf : Image f ∋ b) → f(Inv f b∈Imgf) ≡ b

 InvIsInv f {.(f a)} (im a) = refl _

 InvIsInv f (eq _ _ p) = p ⁻¹

\end{code}





#### <a id="surjective-functions">Surjective functions</a>

An epic (or surjective) function from type `A : 𝓤 ̇` to type `B : 𝓦 ̇` is as an inhabitant of the `Epic` type, which we define as follows.

\begin{code}

 Epic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) →  𝓤 ⊔ 𝓦 ̇
 Epic g = ∀ y → Image g ∋ y

\end{code}

We obtain the right-inverse (or pseudoinverse) of an epic function `f` by applying the function `EpicInv` (which we now define) to the function `f` along with a proof, `fE : Epic f`, that `f` is surjective.

\begin{code}

 EpicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
           (f : A → B) → Epic f
           --------------------
  →        B → A

 EpicInv f fE b = Inv f (fE b)

\end{code}

The function defined by `EpicInv f fE` is indeed the right-inverse of `f`.

\begin{code}

 EpicInvIsRightInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                     (f : A → B)  (fE : Epic f)
                     --------------------------
  →                  f ∘ (EpicInv f fE) ≡ 𝑖𝑑 B

 EpicInvIsRightInv fe f fE = fe (λ x → InvIsInv f (fE x))

\end{code}





#### <a id="injective-functions">Injective functions</a>

We say that a function `g : A → B` is monic (or injective) if we have a proof of `Monic g`, where

\begin{code}

 Monic : {A : 𝓤 ̇ } {B : 𝓦 ̇ }(g : A → B) → 𝓤 ⊔ 𝓦 ̇
 Monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂

\end{code}

Again, we obtain a pseudoinverse. Here it is obtained by applying the function `MonicInv` to `g` and a proof that `g` is monic.

\begin{code}

 --The (pseudo-)inverse of a monic function
 MonicInv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) → Monic f
  →         (b : B) → Image f ∋ b → A

 MonicInv f _ = λ b Imf∋b → Inv f Imf∋b

\end{code}

The function defined by `MonicInv f fM` is the left-inverse of `f`.

\begin{code}

 --The (psudo-)inverse of a monic is the left inverse.
 MonicInvIsLeftInv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(fmonic : Monic f)(x : A)
   →                 (MonicInv f fmonic)(f x)(im x) ≡ x

 MonicInvIsLeftInv f fmonic x = refl _

\end{code}



#### <a id="composition-laws">Composition laws</a>

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 epic-factor : funext 𝓨 𝓨 → {A : 𝓧 ̇}{B : 𝓨 ̇}{C : 𝓩 ̇}
               (β : A → B)(ξ : A → C)(ϕ : C → B)
  →            β ≡ ϕ ∘ ξ →  Epic β → Epic ϕ

 epic-factor fe {A}{B}{C} β ξ ϕ compId βe y = γ
  where
   βinv : B → A
   βinv = EpicInv β βe

   ζ : β (βinv y) ≡ y
   ζ = ap (λ - → - y) (EpicInvIsRightInv fe β βe)
   η : (ϕ ∘ ξ) (βinv y) ≡ y
   η = (ap (λ - → - (βinv y)) (compId ⁻¹)) ∙ ζ
   γ : Image ϕ ∋ y
   γ = eq y (ξ (βinv y)) (η ⁻¹)

\end{code}





#### Injective functions are set embeddings

This is the first point at which [truncation](UALib.Preface.html#truncation) comes into play.  An [embedding](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#embeddings) is defined in the [Type Topology][] library, using the `is-subsingleton` type [described earlier](Prelude.Extensionality.html#alternative-extensionality-type), as follows.


Finally, the type `is-embedding f` will denotes the assertion that `f` is a function all of whose fibers are subsingletons.

\begin{code}
module hide-is-embedding {𝓤 𝓦 : Universe} where

 is-embedding : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } → (X → Y) → 𝓤 ⊔ 𝓦 ̇
 is-embedding f = (y : codomain f) → is-subsingleton (fiber f y)

\end{code}

This is a natural way to represent what we usually mean in mathematics by embedding.  Observe that an embedding does not simply correspond to an injective map.  However, if we assume that the codomain `B` has unique identity proofs (i.e., is a set), then we can prove that a monic function into `B` is an embedding. We will do so in the [Relations.Truncation][] module when we take up the topic of sets in some detail.

Of course, invertible maps are embeddings.

\begin{code}

open import MGS-Embeddings using (is-embedding) public

invertibles-are-embeddings : {𝓧 𝓨 : Universe}
                             {X : 𝓧 ̇} {Y : 𝓨 ̇} (f : X → Y)
 →                           invertible f → is-embedding f

invertibles-are-embeddings f fi = equivs-are-embeddings f (invertibles-are-equivs f fi)

\end{code}

Finally, if we have a proof `p : is-embedding f` that the map `f` is an embedding, here's a tool that can make it easier to apply `p`.  We will use the `fiber` type of the [Type Topology][] library, which is defined as follows.



\begin{code}

open import MGS-Subsingleton-Truncation using (fiber) public

embedding-elim : {𝓧 𝓨 : Universe}{X : 𝓧 ̇} {Y : 𝓨 ̇}
                 (f : X → Y) → is-embedding f
 →               ∀ x x' → f x ≡ f x' → x ≡ x'

embedding-elim f femb x x' fxfx' = ap pr₁ ((femb (f x)) fa fb)
 where
  fa : fiber f (f x)
  fa = x , 𝓇ℯ𝒻𝓁

  fb : fiber f (f x)
  fb = x' , (fxfx' ⁻¹)

\end{code}


-------------------------------------


[← Prelude.Extensionality](Prelude.Extensionality.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>


{% include UALib.Links.md %}


