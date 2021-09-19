---
layout: default
title : Overture module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="prelude">Overture</a>

This is the [Overture][] module of the [Agda Universal Algebra Library][].

The source code for this module comprises the (literate) [Agda][] program that was used to generate the html page displaying the sentence you are now reading. This source code inhabits the file [Overture.lagda][], which resides in the [git repository of the Agda UALib][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture where

open import Overture.Preliminaries public
open import Overture.Equality public
open import Overture.FunExtensionality public
open import Overture.Inverses public
open import Overture.Lifts public

\end{code}

--------------------------------------

<p></p>

[← Preface](Preface.html)
<span style="float:right;">[Overture.Preliminaries →](Overture.Preliminaries.html)</span>

{% include UALib.Links.md %}
