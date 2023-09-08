import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

structure ℚ' where
  v : ℚ

def weirdAdd (a b : ℚ') : ℚ' := .mk$ a.v + b.v + 1/2

def weirdMul (a b : ℚ') : ℚ' := .mk$ a.v + b.v + 2 * a.v * b.v

def weirdZero : ℚ' := .mk$ - (1/2)

def weirdOne : ℚ' := .mk 0

def weirdNeg (a : ℚ') : ℚ' := .mk$ - 1 - a.v


lemma weirdZero_weirdAdd (a : ℚ') : weirdAdd weirdZero a = a := by
  simp [weirdAdd, weirdZero]

lemma weirdAdd_weirdZero (a : ℚ') : weirdAdd a weirdZero = a := by
  simp [weirdAdd, weirdZero]

lemma weirdAdd_left_weirdNeg (a : ℚ') : weirdAdd (weirdNeg a) a = weirdZero := by
  simp only [weirdAdd, weirdNeg, weirdZero]
  ring_nf

lemma weirdAdd_comm (a b : ℚ') :
  weirdAdd a b = weirdAdd b a :=
by
  simp only [weirdAdd]
  ring_nf

lemma weirdAdd_assoc (a b c : ℚ') :
  weirdAdd (weirdAdd a b) c = weirdAdd a (weirdAdd b c) :=
by
  simp only [weirdAdd]
  ring_nf

lemma weirdMul_assoc (a b c : ℚ') :
  weirdMul (weirdMul a b) c = weirdMul a (weirdMul b c) :=
by
  simp only [weirdMul]
  ring_nf

lemma weirdOne_weirdMul (a : ℚ') : weirdMul weirdOne a = a := by
  simp [weirdMul, weirdOne]

lemma weirdMul_weirdOne (a : ℚ') : weirdMul a weirdOne = a := by
  simp [weirdMul, weirdOne]

lemma weirdZero_weirdMul (a : ℚ') : weirdMul weirdZero a = weirdZero := by
  simp [weirdMul, weirdZero]

lemma weirdMul_weirdZero (a : ℚ') : weirdMul a weirdZero = weirdZero := by
  simp only [weirdMul, weirdZero]
  ring_nf

lemma weirdMul_left_weirdAdd (a b c : ℚ') :
  weirdMul a (weirdAdd b c) = weirdAdd (weirdMul a b) (weirdMul a c) :=
by
  simp only [weirdMul, weirdAdd]
  ring_nf

lemma weirdMul_right_weirdAdd (a b c : ℚ') :
  weirdMul (weirdAdd a b) c = weirdAdd (weirdMul a c) (weirdMul b c) :=
by
  simp only [weirdMul, weirdAdd]
  ring_nf

instance weirdRing : Ring ℚ' where
  add := weirdAdd
  mul := weirdMul
  zero := weirdZero
  neg := weirdNeg
  one := weirdOne
  zero_add := weirdZero_weirdAdd
  add_zero := weirdAdd_weirdZero
  add_left_neg := weirdAdd_left_weirdNeg
  one_mul := weirdOne_weirdMul
  mul_one := weirdMul_weirdOne
  zero_mul := weirdZero_weirdMul
  mul_zero := weirdMul_weirdZero
  add_comm := weirdAdd_comm
  add_assoc := weirdAdd_assoc
  mul_assoc := weirdMul_assoc
  left_distrib := weirdMul_left_weirdAdd
  right_distrib := weirdMul_right_weirdAdd
