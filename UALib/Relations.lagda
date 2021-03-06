---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="relation-and-quotient-types">Relation and Quotient Types</a>

This chapter presents the [UALib.Relations][] module of the [Agda Universal Algebra Library][].

\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}

\begin{code}
module Relations where

open import Relations.Discrete
open import Relations.Continuous
open import Relations.Quotients
open import Relations.Truncation

\end{code}

-------------------------------------

<p></p>

[← Prelude.Lifts](Prelude.Lifts.html)
<span style="float:right;">[Relations.Unary →](Relations.Small.html)</span>

{% include UALib.Links.md %}
