---
layout: default
title : UALib.Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [UALib.Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Quotients where

open import Relations.Discrete public

\end{code}

**N.B.**. We import [Relations.Discrete][] since we don't yet need any of the types defined in the [Relations.Continuous][] module.


#### <a id="properties-of-binary-relations">Properties of binary relations</a>

Let `𝓤 : Universe` be a universe and `A : 𝓤 ̇` a type.  In [Relations.Discrete][] we defined a type representing a binary relation on A.  In this module we will define types for binary relations that have special properties. The most important special properties of relations are the ones we now define.

\begin{code}

module _ {𝓤 : Universe}{A : 𝓤 ̇ }{𝓦 : Universe} where

 reflexive : Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 reflexive _≈_ = ∀ x → x ≈ x

 symmetric : Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

 antisymmetric : Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 antisymmetric _≈_ = ∀ x y → x ≈ y → y ≈ x → x ≡ y

 transitive : Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

\end{code}

The [Type Topology][] library defines the following *uniqueness-of-proofs* principle for binary relations.

\begin{code}

module hide-is-subsingleton-valued {𝓤 𝓦 : Universe}{A : 𝓤 ̇ } where

 is-subsingleton-valued : Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)

open import MGS-Quotient using (is-subsingleton-valued) public

\end{code}

Thus, if `R : Rel A 𝓦`, then `is-subsingleton-valued R` is the assertion that for each pair `x y : A` there can be at most one proof that `R x y` holds.

In the [Relations.Truncation][] module we introduce a number of similar but more general types used in the \agdaualib to represent uniqueness-of-proofs principles for relations of arbitrary arity over arbitrary types.


#### <a id="equivalence-classes">Equivalence classes</a>

A binary relation is called a **preorder** if it is reflexive and transitive. An **equivalence relation** is a symmetric preorder.


\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇ } where

 is-preorder : Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 is-preorder _≈_ = is-subsingleton-valued _≈_ × reflexive _≈_ × transitive _≈_

 record IsEquivalence (_≈_ : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field
   rfl   : reflexive _≈_
   sym   : symmetric _≈_
   trans : transitive _≈_

 is-equivalence : Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 is-equivalence _≈_ = is-preorder _≈_ × symmetric _≈_

\end{code}

An easy first example of an equivalence relation is the kernel of any function.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 map-kernel-IsEquivalence : (f : A → B) → IsEquivalence (ker{𝓤}{𝓦} f)
 map-kernel-IsEquivalence f = record { rfl = λ x → refl
                                     ; sym = λ x y x₁ → ≡-sym{𝓦} x₁
                                     ; trans = λ x y z x₁ x₂ → ≡-trans x₁ x₂ }

\end{code}




#### <a id="equivalence-classes">Equivalence classes</a>

If R is an equivalence relation on A, then for each `𝑎 : A`, there is an **equivalence class** containing 𝑎, which we denote and define by [ 𝑎 ] R := all `𝑏 : A` such that R 𝑎 𝑏.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇ } where

 [_]_ : A → Rel A 𝓦 → Pred A 𝓦
 [ 𝑎 ] R = λ x → R 𝑎 x

 infix 60 [_]_
\end{code}

Thus, `x ∈ [ a ] R` if and only if `R a x`, as desired.  We often refer to [ 𝑎 ] R as the *R-class containing* 𝑎, and we represent the collection of all such `R`-classes by the following type.

\begin{code}

 𝒞 : {R : Rel A 𝓦} → Pred A 𝓦 → (𝓤 ⊔ 𝓦 ⁺) ̇
 𝒞  {R} C = Σ a ꞉ A , C ≡ ( [ a ] R)

\end{code}

If `R` is an equivalence relation on `A`, then the **quotient** of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ 𝑎 ] R ∣  𝑎 : A}` of all equivalence classes of `R`. There are a few ways we could represent the quotient with respect to a relation as a type, but we find the following to be the most useful.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓦 → 𝓤 ⊔ (𝓦 ⁺) ̇
 A / R = Σ C ꞉ Pred A 𝓦 ,  𝒞 {R = R} C

 infix -1 _/_
\end{code}

The next type is used to represent an `R`-class with a designated representative.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇} where

 ⟦_⟧ : A → {R : Rel A 𝓦} → A / R
 ⟦ a ⟧ {R} = [ a ] R , a , refl

 infix 60 ⟦_⟧
\end{code}

This serves as a kind of *introduction rule*.  Dually, the next type provides an *elimination rule*.<sup>[1](Relations.Quotients.html#fn1)</sup>

\begin{code}

 ⌜_⌝ : {R : Rel A 𝓦} → A / R  → A

 ⌜ 𝕔 ⌝ = fst ∥ 𝕔 ∥

\end{code}

Later we will need the following tools for working with the quotient types defined above.

\begin{code}

 open IsEquivalence{𝓤}{𝓦}

 /-subset : {x y : A}{R : Rel A 𝓦} → IsEquivalence R → R x y →  [ x ] R  ⊆  [ y ] R
 /-subset {x}{y} Req Rxy {z} Rxz = (trans Req) y x z (sym Req x y Rxy) Rxz

 /-supset : {x y : A}{R : Rel A 𝓦} → IsEquivalence R → R x y →  [ y ] R ⊆ [ x ] R
 /-supset {x}{y} Req Rxy {z} Ryz = (trans Req) x y z Rxy Ryz

 /-≐ : {x y : A}{R : Rel A 𝓦} → IsEquivalence R → R x y →  [ x ] R  ≐  [ y ] R
 /-≐ Req Rxy = /-subset Req Rxy , /-supset Req Rxy

\end{code}

(An example application of `/-=̇` is the `class-extensionality` lemma in the [Relations.Truncation] module.)

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">**Unicode Hints**. Type `⌜` and `⌝` as `\cul` and `\cur` in [agda2-mode][].</span>


<br>
<br>


[← Relations.Continuous](Relations.Continuous.html)
<span style="float:right;">[Relations.Truncation →](Relations.Truncation.html)</span>

{% include UALib.Links.md %}



<!-- unused stuff

 -- /-refl : {A : 𝓤 ̇}(a a' : A){R : Rel A 𝓡} → reflexive R → [ a ] R ≡ [ a' ] R → R a a'

 -- /-refl a a' rfl x  = cong-app-pred a' (rfl a') (x ⁻¹)


-->
