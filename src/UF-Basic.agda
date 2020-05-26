--FILE: UF-Basic.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 20 Feb 2020
--UPDATE: 23 May 2020
--REF: Based on the file `basic.agda` (24 Dec 2019).
--       Used for 1st half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; ℕ; _×_; Π; _≡_)
open import UF-Singleton using (is-set)
open import UF-Extensionality using (dep-intensionality)
--open import Data.Fin using (Fin)

module UF-Basic where

-- -- Operations and projections
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A

π : {I : 𝓥 ̇} {A : 𝓤 ̇} → I → Op I A
π i x = x i

-- 𝓞 is the universe in which the operation symbols lives
-- 𝓥 is the universe in which the arities live
Signature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , ( F → 𝓥 ̇ )

-- 𝓤 is the universe level of carriers (or "universes") of structures
Algebra : (𝓤 : Universe) → {𝓞 𝓥 : Universe} → (S : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
Algebra 𝓤 {𝓞} {𝓥} (F , ρ) = Σ A ꞉ 𝓤 ̇ ,  ( (𝓸 : F)  → Op (ρ 𝓸) A )

SmallAlgebra : (𝓤 : Universe) → {𝓞 𝓥 : Universe} → (S : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
SmallAlgebra 𝓤 {𝓞} {𝓥} (F , ρ) = Σ A ꞉ 𝓤 ̇ ,  is-set A × ( (𝓸 : F)  → Op (ρ 𝓸) A )

module _ {S : Signature 𝓞 𝓥} where
  Π' : {I : 𝓘 ̇}( A : I → Algebra 𝓤 S ) → Algebra (𝓤 ⊔ 𝓘) S
  Π' A =  ( ( ᵢ : _) → ∣ A ᵢ ∣ ) ,  λ 𝓸 x ᵢ → ∥ A ᵢ ∥ 𝓸 λ 𝓥 → x 𝓥 ᵢ

  -- We now want to construct a small algebra out of a product of small algebras.
  -- But for that we need that the products of "sets" is a "set".
  product-of-sets-is-set : {I : 𝓘 ̇}(X : I → 𝓤 ̇) → ((i : I) → is-set (X i)) → is-set (Π X)
  product-of-sets-is-set {I = I} X ∀Xset 𝒙 𝒙'  p q = γ
   where
    p-proj : (i : I) → (𝒙 i) ≡ (𝒙' i)
    p-proj i = dep-intensionality{f = 𝒙}{g = 𝒙'} p i

    q-proj : (i : I) → (𝒙 i) ≡ (𝒙' i)
    q-proj i = dep-intensionality{f = 𝒙}{g = 𝒙'} q i

    ζ : (i : I) → (p-proj i) ≡ (q-proj i)
    ζ i = (∀Xset i) (𝒙 i) (𝒙' i) (p-proj i) (q-proj i) 

    γ : p ≡ q
    γ = {!!}

  -- product of small algebras
  Πₛ : {I : 𝓘 ̇}( A : I → SmallAlgebra 𝓤 S ) → SmallAlgebra (𝓤 ⊔ 𝓘) S
  Πₛ A =  ( ( ᵢ : _) → ∣ A ᵢ ∣ ) ,  ( product-of-sets-is-set (λ ᵢ → ∣ A ᵢ ∣ )
                                                                           (λ ᵢ → ∣ ∥ A ᵢ ∥ ∣ ) ) ,   -- is-set ∣ A ᵢ ∣
               λ 𝓸 x ᵢ → ∥ ∥ A ᵢ ∥ ∥ 𝓸 λ 𝓥 → x 𝓥 ᵢ   -- ops are same as for Π' (the Algebra product)

--Example: monoid
--  A monoid signature has two operation symbols, say, `e`  and `·`, of arities 0 and 2 (thus, of types `(𝟘 → A) → A`
--  and `(𝟚 → A) → A`) resp. The types indicate that `e` is nullary (i.e., takes no args, equivalently, takes args
--  of type `𝟘 → A`), while `·` is binary (as indicated  by argument type `𝟚 → A`).
data monoid-op : 𝓤₀ ̇ where
  e : monoid-op
  · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }

module _ {S : Signature 𝓞 𝓥} {n : ℕ} where

  -- cyclic_shift : {A : 𝓤 ̇} (f : Op (Fin n) A) (m : Fin n) → Op (Fin n) A
  -- cyclic_shift f m = ?

-- isCyclic : {I : Fin n} {A : 𝓤 ̇} (f : Op I A)
--    →    (args : I → A) → 

