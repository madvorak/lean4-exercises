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


private def maDelitelePod (n : ℕ) : ℕ → Bool
| 0   => false
| 1   => false
| 2   => false
| a+1 => n % a == 0 || maDelitelePod n a

def jePrvocislo (n : ℕ) : Bool := n > 1 && !(maDelitelePod n n)

private lemma maDelitelePod_iff (n a : ℕ) (a_lt_n : a ≤ n) :
  (maDelitelePod n a = false) ↔ (∀ d < a, d ∣ n → d = 1) :=
by
  induction a with
  | zero =>
    constructor
    · intros _ d d_lt_0
      cases d_lt_0
    · intro _
      rfl
  | succ b ih =>
    constructor <;> specialize ih (Nat.le_of_lt a_lt_n)
    · intros hyp d d_lt_bs d_dvd_n
      cases b with
      | zero =>
        exfalso
        have d_eq_0 : d = 0
        · exact Iff.mp Nat.lt_one_iff d_lt_bs
        have n_neq_0 : n ≠ 0
        · exact Iff.mp Nat.pos_iff_ne_zero a_lt_n
        rw [d_eq_0] at d_dvd_n
        cases' d_dvd_n with m n_eq
        rw [zero_mul] at n_eq
        exact n_neq_0 n_eq
      | succ c =>
        cases c with
        | zero =>
          cases d with
          | zero =>
            exfalso
            have n_eq_0 : n = 0
            · exact Iff.mp zero_dvd_iff d_dvd_n
            rw [n_eq_0] at a_lt_n
            cases a_lt_n
          | succ e =>
            have e_lt_1 : e < 1
            · exact Iff.mp Nat.succ_lt_succ_iff d_lt_bs
            have e_eq_0 : e = 0
            · exact Iff.mp Nat.lt_one_iff e_lt_1
            rw [e_eq_0]
        | succ k =>
          obtain ⟨nedel, nepod⟩ : ¬n % (k+2) = 0 ∧ maDelitelePod n (k+2) = false
          · convert hyp
            simp [maDelitelePod]
          simp only [nepod, true_iff] at ih
          by_cases d_case : d < k+2
          · exact ih d d_case d_dvd_n
          exfalso
          have d_is : d = k+2
          · linarith
          rw [d_is] at d_dvd_n
          apply nedel
          exact Nat.mod_eq_zero_of_dvd d_dvd_n
    · intro hyp
      cases b with
      | zero => rfl
      | succ c =>
        cases c with
        | zero => rfl
        | succ k =>
          convert_to ¬n % (k+2) = 0 ∧ maDelitelePod n (k+2) = false
          · simp [maDelitelePod]
          constructor
          · specialize hyp (k+2) (Nat.lt.base (k+2))
            intro contr
            specialize hyp (Nat.dvd_of_mod_eq_zero contr)
            linarith
          · rw [ih]
            intros d d_lt
            apply hyp
            exact Nat.lt.step d_lt

lemma jePrvocislo_iff_Prvocislo (n : ℕ) : (jePrvocislo n = true) ↔ Prvocislo n := by
  unfold jePrvocislo
  unfold Prvocislo
  convert_to 1 < n → (maDelitelePod n n = false ↔ ∀ (d : ℕ), d ∣ n → d = 1 ∨ d = n)
  · simp
  rw [maDelitelePod_iff n n (Nat.le_refl n)]
  intro nontriv
  constructor <;> intros hyp d <;> specialize hyp d
  · intro d_dvd_n
    by_cases d_vs_n : d < n
    · left
      exact hyp d_vs_n d_dvd_n
    · right
      have d_le_n : d ≤ n
      · exact Nat.le_of_dvd (Nat.zero_lt_of_lt nontriv) d_dvd_n
      have d_ge_n : d ≥ n
      · exact Iff.mp Nat.not_lt d_vs_n
      exact Nat.le_antisymm d_le_n d_ge_n
  · intros d_lt_n d_dvd_n
    specialize hyp d_dvd_n
    cases' hyp with d_eq_1 d_eq_n
    · exact d_eq_1
    · exfalso
      apply Nat.ne_of_lt d_lt_n
      exact d_eq_n

theorem jePrvocislo_decides_natPrime : jePrvocislo = Nat.Prime := by
  classical
  ext n
  by_cases jep : jePrvocislo n = true
  · simp only [jep, Bool.true_eq_decide_iff]
    rwa [jePrvocislo_iff_Prvocislo, prvocis] at jep
  · simp only [jep, Bool.false_eq_decide_iff]
    rwa [jePrvocislo_iff_Prvocislo, prvocis] at jep
