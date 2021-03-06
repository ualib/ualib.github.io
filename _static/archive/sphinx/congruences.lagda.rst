.. FILE      : congruences.lagda.rst
.. AUTHOR    : William DeMeo and Siva Somayyajula
.. DATE      : 23 Apr 2020
.. UPDATE    : 21 Jul 2020
.. COPYRIGHT : (c) 2020 William DeMeo
.. NOTE      : This file used to be called relations.lagda.rst

.. REF: Some parts of this file is simply a translation of the Agda standard library file Binary/Core.agda into our notation.

====================
Congruences in Agda
====================

This chapter describes the `congruences module`_ of the `agda-ualib`_.

**N.B.** Some of the code in this first part of this chapter pertaining to relations is borrowed from similar code in the `Agda standard library`_ (in the file ``Binary/Core.agda``) that we have translated into our notation for consistency.

-------------------------------------------------

Preliminaries
---------------

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   open import basic

   module congruences where

   open import prelude using (Pred; 𝓡; 𝓢; is-prop; 𝟙; _≡⟨_⟩_; _∎;
    refl; _⁻¹; funext; ap) public



--------------------------------------

Binary relation type
------------------------

Heterogeneous binary relations.

::

   REL : 𝓤 ̇ → 𝓥 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓝 ⁺) ̇
   REL A B 𝓝 = A → B → 𝓝 ̇

Homogeneous binary relations.

::

   Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
   Rel A 𝓝 = REL A A 𝓝


Kernels
~~~~~~~~~~~~~~

The kernel of a function can be defined in many ways. For example,

::

   KER : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → 𝓤 ⊔ 𝓦 ̇
   KER {𝓤}{𝓦}{A} f = Σ x ꞉ A , Σ y ꞉ A , f x ≡ f y

   ker : {A B : 𝓤 ̇ } → (A → B) → 𝓤 ̇
   ker {𝓤} = KER{𝓤}{𝓤}

or as a relation...

::

   KER-rel : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → Rel A 𝓦
   KER-rel g x y = g x ≡ g y

   -- (in the special case 𝓦 ≡ 𝓤)
   ker-rel : {A B : 𝓤 ̇ } → (A → B) → Rel A 𝓤
   ker-rel {𝓤} = KER-rel {𝓤} {𝓤}

or a binary predicate...

::

   KER-pred : {A : 𝓤 ̇ }{B : 𝓦 ̇ } → (A → B) → Pred (A × A) 𝓦
   KER-pred g (x , y) = g x ≡ g y

   -- (in the special case 𝓦 ≡ 𝓤)
   ker-pred : {A : 𝓤 ̇ }{B : 𝓤 ̇ } → (A → B) → Pred (A × A) 𝓤
   ker-pred {𝓤} = KER-pred {𝓤} {𝓤}


Implication
~~~~~~~~~~~

We denote and define implication or containment (which could also be written _⊆_) as follows.

::

   _⇒_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
    →    REL A B 𝓡 → REL A B 𝓢
    →    𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇

   P ⇒ Q = ∀ {i j} → P i j → Q i j

   infixr 4 _⇒_

   _on_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
    →     (B → B → C) → (A → B) → (A → A → C)
   _*_ on f = λ x y → f x * f y

Here is a more general version of implication 

::

   _=[_]⇒_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
    →        Rel A 𝓡 → (A → B) → Rel B 𝓢
    →        𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇

   P =[ f ]⇒ Q = P ⇒ (Q on f)

   infixr 4 _=[_]⇒_


Properties of binary relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Reflexivity of a binary relation (say, ``≈``) on ``X``, can be defined without an underlying equality as follows.

::

   reflexive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   reflexive _≈_ = ∀ x → x ≈ x


Similarly, we have the usual notion of symmetric (resp., transitive) binary relation.

::

   symmetric : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

   transitive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

For a binary relation ≈ on A, denote a single ≈-class (containing a) by `[ a ] ≈`,

::

   [_]_ :  {A : 𝓤 ̇ } →  (a : A) → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
   [ a ] _≈_ = Σ x ꞉ _ ,  a ≈ x

and denote the collection of all ≈-classes of A by `A // ≈`.

::

   _//_ :  (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
   A // ≈ = Σ C ꞉ _ ,   Σ a ꞉ A ,  C ≡ ( [ a ] ≈ )

   is-subsingleton-valued : {A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
   is-subsingleton-valued  _≈_ = ∀ x y → is-prop (x ≈ y)

The "trivial" or "diagonal" or "identity" relation is,

::

   𝟎 : {A : 𝓤 ̇ } → 𝓤 ̇
   𝟎{𝓤} {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

   𝟎-rel : {A : 𝓤 ̇ } → Rel A 𝓤
   𝟎-rel a b = a ≡ b

or, in various other guises, 

::

   -- ...as a binary predicate:
   𝟎-pred : {A : 𝓤 ̇ } → Pred (A × A) 𝓤
   𝟎-pred (a , a') = a ≡ a'

   --...as a binary predicate:
   𝟎'' : {A : 𝓤 ̇ } → 𝓤 ̇
   𝟎'' {𝓤} {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥

The "universal" or "total" or "all" relation.

::

   𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
   𝟏 a b = 𝟙

----------------------------------

Types for equivalences
----------------------

.. The preorders of the standard library are defined in terms of an underlying equivalence relation, and hence equivalence relations are not defined in terms of preorders.

Here are two ways to define an equivalence relation in Agda.

First, we use a record.

::

   record IsEquivalence {A : 𝓤 ̇ } (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
     field
       rfl  : reflexive _≈_
       sym   : symmetric _≈_
       trans : transitive _≈_


Here's an alternative.

::

   is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
   is-equivalence-relation _≈_ =
    is-subsingleton-valued _≈_
     × reflexive _≈_ × symmetric _≈_ × transitive _≈_


Of course, `𝟎` is an equivalence relation, a fact we can prove as follows.

::

   𝟎-IsEquivalence : {A : 𝓤 ̇ } → IsEquivalence {𝓤}{𝓤}{A} 𝟎-rel
   𝟎-IsEquivalence = record { rfl = ρ ; sym = σ ; trans = τ }
    where
     ρ : reflexive 𝟎-rel
     ρ x =  x ≡⟨ refl _ ⟩ x ∎

     σ : symmetric 𝟎-rel
     σ x y x≡y = x≡y ⁻¹

     τ : transitive 𝟎-rel
     τ x y z x≡y y≡z = x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎

We define the **lift** of a binary relation from pairs to pairs of tuples as follows:

::

   lift-rel : {γ : 𝓥 ̇ } {Z : 𝓤 ̇ }
    →         Rel Z 𝓦 → (γ → Z) → (γ → Z)
    →         𝓥 ⊔ 𝓦 ̇
   lift-rel R 𝒇 𝒈 = ∀ x → R (𝒇 x) (𝒈 x)


We define **compatibility** of a given function-relation pair as follows:

::

   compatible-fun : {γ : 𝓥 ̇ } {Z : 𝓤 ̇ }
                    (𝒇 : (γ → Z) → Z)(𝑹 : Rel Z 𝓦)
    →               𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   compatible-fun 𝒇 𝑹 = (lift-rel 𝑹) =[ 𝒇 ]⇒ 𝑹


----------------------------------

Types for congruences
---------------------

Finally, we come to the definition of a congruence, which we define in a module so we have an ambient signature 𝑆 available.

::

   module _ {𝑆 : Signature 𝓞 𝓥}  where

     -- relation compatible with an operation
     compatible-op : {𝑨 : Algebra 𝓤 𝑆}
      →              ∣ 𝑆 ∣ → Rel ∣ 𝑨 ∣ 𝓤
      →              𝓥 ⊔ 𝓤 ̇
     compatible-op {𝓤} {𝑨} 𝑓 𝓻 = (lift-rel 𝓻) =[ (∥ 𝑨 ∥ 𝑓) ]⇒ 𝓻

     --The given relation is compatible with all ops of an algebra.
     compatible : (𝑨 : Algebra 𝓤 𝑆) -> Rel ∣ 𝑨 ∣ 𝓤 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇
     compatible {𝓤} 𝑨 𝓻 = ∀ 𝑓 → compatible-op{𝓤}{𝑨} 𝑓 𝓻

     𝟎-compatible-op : funext 𝓥 𝓤
      →                {𝑨 : Algebra 𝓤 𝑆} (𝑓 : ∣ 𝑆 ∣)
      →                compatible-op {𝓤}{𝑨} 𝑓 𝟎-rel
     𝟎-compatible-op fe {𝑨 = 𝑨} 𝑓 ptws𝟎  =
      ap (𝑓 ̂ 𝑨)(fe (λ x → ptws𝟎 x))

     𝟎-compatible : funext 𝓥 𝓤
      →             {𝑨 : Algebra 𝓤 𝑆}
      →             compatible 𝑨 𝟎-rel
     𝟎-compatible fe {𝑨} =
      λ 𝑓 args → 𝟎-compatible-op fe {𝑨} 𝑓 args

     -- Congruence relations
     Con : (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
     Con {𝓤} 𝑨 =
      Σ θ ꞉ ( Rel ∣ 𝑨 ∣ 𝓤 ) , IsEquivalence θ × compatible 𝑨 θ

     con : (𝑨 : Algebra 𝓤 𝑆)  →  Pred (Rel ∣ 𝑨 ∣ 𝓤) _
     con 𝑨 = λ θ → IsEquivalence θ × compatible 𝑨 θ

     record Congruence (𝑨 : Algebra 𝓤 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
       constructor mkcon
       field
         ⟨_⟩ : Rel ∣ 𝑨 ∣ 𝓤
         Compatible : compatible 𝑨 ⟨_⟩
         IsEquiv : IsEquivalence ⟨_⟩
     open Congruence

----------------------------------

The trivial congruence
~~~~~~~~~~~~~~~~~~~~~~~

We construct the "trivial" or "diagonal" or "identity" relation and prove it is a congruence as follows.

::

     Δ : funext 𝓥 𝓤 → (𝑨 : Algebra 𝓤 𝑆) → Congruence 𝑨
     Δ fe 𝑨 = mkcon 𝟎-rel
                   ( 𝟎-compatible fe {𝑨} )
                   ( 𝟎-IsEquivalence )

     _╱_ : (𝑨 : Algebra 𝓤 𝑆) → Congruence 𝑨
            ---------------------------------
      →     Algebra (𝓤 ⁺) 𝑆
     𝑨 ╱ θ = (( ∣ 𝑨 ∣ // ⟨ θ ⟩ ) , -- carrier
               (λ 𝑓 args        -- operations
                → ([ (𝑓 ̂ 𝑨) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩) ,
                  ((𝑓 ̂ 𝑨)(λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
               )
             )


We would like to round out this chapter with a formalization of the trivial congruence of the free algebra 𝔽(𝒦, 𝑋), which we called Ψ(𝒦, 𝑻(𝑋)) in :numref:`free algebras`.

Unfortunately, this will have to wait until we have formalized the concepts of subalgebra and closure on which this congruence depends. Thus, our Agda definition of Ψ(𝒦, 𝑻(𝑋)) will appear in the `closure module`_ described in Chapter %s :numref:`equational logic in agda`.

------------------------------------------

Unicode Hints
---------------

Table of some special characters used in the `congruences module`_. 

  +--------+------------------------+
  | To get | Type                   |
  +--------+------------------------+
  | ≈      | ``\~~`` or ``\approx`` |
  +--------+------------------------+
  | ⇒      | ``\r2`` or ``\=>``     |
  +--------+------------------------+
  | 𝟎, 𝟏   | ``\B0``, ``\B1``       |
  +--------+------------------------+
  | θ, Δ   | ``\theta``, ``\Delta`` |
  +--------+------------------------+
  | ⟨_⟩     | ``\<_\>``             |
  +--------+------------------------+

See :numref:`unicode hints` for a longer list of symbols used in the agda-ualib_, or better yet, use these

  **Emacs commands providing information about special characters/input methods**:

    * ``M-x describe-char`` (or ``M-m h d c``) with the cursor on the character of interest

    * ``M-x describe-input-method`` (or ``C-h I``)

------------------

.. include:: hyperlink_references.rst

