import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith


def Prvocislo (n : ℕ) : Prop :=
  n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n

lemma prvocis : Prvocislo = Nat.Prime := by
  ext n
  constructor <;> intro hyp
  · unfold Nat.Prime
    constructor
    · simp only [IsUnit, not_exists]
      intros x contr
      have x_eq_1 : x = 1
      · exact Nat.units_eq_one x
      have n_gt_1 : n > 1
      · exact hyp.1
      rw [←contr, x_eq_1] at n_gt_1
      trivial
    intros a b soucin
    by_contra contra
    push_neg at contra
    have a_neq_1 : a ≠ 1
    · by_contra a_eq_1
      simp [a_eq_1] at contra
    have b_neq_1 : b ≠ 1
    · by_contra b_eq_1
      simp [b_eq_1] at contra
    cases' hyp.2 a (by { use b; exact soucin }) with a_is_1 a_is_n
    · exact a_neq_1 a_is_1
    apply b_neq_1
    rw [a_is_n] at soucin
    have n_lt_1 := hyp.1
    have n_neq_0 : n ≠ 0
    · intro n_eq_0
      rw [n_eq_0] at n_lt_1
      trivial
    exact Iff.mp (mul_eq_left₀ n_neq_0) (id (Eq.symm soucin))
  · unfold Nat.Prime at hyp
    cases' hyp with notUnit kdyzSoucin
    constructor
    · have : n ≠ 0
      · intro contr
        rw [contr] at kdyzSoucin
        cases' kdyzSoucin 0 2 (by decide) with unit_0 unit_2 <;> simp at *
      cases' n with n'
      · contradiction
      cases' n' with n''
      · simp at notUnit
      exact Nat.one_lt_succ_succ n''
    intros d deli
    rcases deli with ⟨e, soucin⟩
    cases' kdyzSoucin d e soucin with d_unit e_unit
    · left
      exact Iff.mp Nat.isUnit_iff d_unit
    · right
      have e_eq_1 : e = 1
      · exact Iff.mp Nat.isUnit_iff e_unit
      rw [e_eq_1, mul_one] at soucin
      exact soucin.symm


def Prvocislo' (n : ℕ) : Prop :=
  n ≠ 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n

lemma prvocis' : Prvocislo = Prvocislo' := by
  ext n
  constructor <;> intro hyp
  · constructor
    · exact Nat.ne_of_gt hyp.1
    · exact hyp.2
  constructor; swap
  · exact hyp.2
  cases' n with n'
  · exfalso
    cases hyp.2 2 (by decide) <;> trivial
  cases' n' with n''
  · exfalso
    cases' hyp with impos trash
    apply impos
    rfl
  exact Nat.one_lt_succ_succ n''
