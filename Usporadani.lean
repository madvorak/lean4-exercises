import Mathlib.Init.Algebra.Order
import Mathlib.Init.Set
import Mathlib.Tactic.Use


variable {T : Type} [PartialOrder T]

def dolni_zavora (M : Set T) (a : T) := ∀ m ∈ M, a ≤ m

def horni_zavora (M : Set T) (z : T) := ∀ m ∈ M, m ≤ z

def infim (M : Set T) (b : T) := dolni_zavora M b ∧ (∀ a : T, dolni_zavora M a → a ≤ b)

def supre (M : Set T) (y : T) := horni_zavora M y ∧ (∀ z : T, horni_zavora M z → y ≤ z)

def ma_infim (M : Set T) := ∃ b, infim M b

def ma_supre (M : Set T) := ∃ y, supre M y

lemma prvek_je_dolni_zavora_hornich_zavor (M : Set T) : ∀ m ∈ M, dolni_zavora (horni_zavora M) m := by
  intros m hm _ hyp
  exact hyp m hm

lemma prvek_je_horni_zavora_dolnich_zavor (M : Set T) : ∀ m ∈ M, horni_zavora (dolni_zavora M) m := by
  intros m hm _ hyp
  exact hyp m hm

theorem kazda_podm_ma_infim_iff_kazda_podm_ma_supre : (∀ M : Set T, ma_infim M) ↔ (∀ M : Set T, ma_supre M) := by
  constructor
  · intro vsechna_infima M
    cases' vsechna_infima (horni_zavora M) with x hx
    use x
    cases' hx with x_pod x_nad
    constructor
    · intro m hm
      apply x_nad m
      apply prvek_je_dolni_zavora_hornich_zavor
      exact hm
    · intro a ha
      apply x_pod a
      exact ha
  · intros vsechna_suprema M
    cases' vsechna_suprema (dolni_zavora M) with d hd
    use d
    cases' hd with d_nad d_pod
    constructor
    · intro m hm
      apply d_pod m
      apply prvek_je_horni_zavora_dolnich_zavor
      exact hm
    · intro a ha
      apply d_nad a
      exact ha
