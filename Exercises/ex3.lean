/-
COMP2012 (LAC) 2025

Exercise 3

This exercise consists of 7 languages over SigmaABC. For each, give the
regular expression defining the language.

Don't change anything else in this file!
-/
import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene
import Proofs.RE

open Kleene Re RE Lang.Examples

-- Abbreviations for a, b, and c as symbols in the RE
abbrev a : RE SigmaABC := sym SigmaABC.a
abbrev b : RE SigmaABC := sym SigmaABC.b
abbrev c : RE SigmaABC := sym SigmaABC.c

/-
Give regular expressions defining the following languages over the alphabet Σ =
{a, b, c}: (SigmaABC)
1. All words that contain exactly one a.
2. All words that contain at least two bs.
3. All words that contain at most two cs.
4. All words such that all b’s appear before all c’s.
5. All words that contain exactly one b and one c (but any number of a’s).
6. All words such that the number of a’s plus the number of b’s is odd.
7. All words that contain the sequence abba at least once.
-/

-- Example
-- 0. All words that contain no a and start with b.
abbrev e0 : RE SigmaABC
:= b ⋅ (b + c)★
--:= append ((sym b) (star (plus (sym b) (sym c)))

-- 1. All words that contain exactly one a.
abbrev e1 : RE SigmaABC
:= sorry

-- 2. All words that contain at least two bs.
abbrev e2 : RE SigmaABC
:= sorry

--- 3. All words that contain at most two cs.
abbrev e3 : RE SigmaABC
:= sorry

--- 4. All words such that all b’s appear before all c’s.
abbrev e4 : RE SigmaABC
:= sorry

--- 5. All words that contain exactly one b and one c (but any number of a’s).
abbrev e5 : RE SigmaABC
:= sorry

-- 6. All words such that the number of a’s plus the number of b’s is odd.
abbrev e6 : RE SigmaABC
:= sorry

-- 7. All words that contain the sequence abba at least once.
abbrev e7 : RE SigmaABC
:= sorry
