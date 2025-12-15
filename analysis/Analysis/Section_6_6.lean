import Mathlib.Tactic
import Analysis.Section_6_5
import Analysis.Section_6_1

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by sorry

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := by sorry

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (1:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (1:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

-- Exercise 12 cont.
/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := by
  rw [subseq]
  use (fun n ↦ n)
  constructor
  . rw [StrictMono]
    intro a b h; assumption
  intro n; rfl

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by sorry

-- Exercise 12 cont.
-- thought this would be helpful for prop 6.6.6, wasn't
/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  constructor
  . intro ha_conv b hb_sub
    rw [TendsTo] at *
    intro ε hε; specialize ha_conv ε
    replace ha_conv := ha_conv hε
    rw [Real.EventuallyClose] at *
    obtain ⟨N, ⟨hN, ha_con⟩⟩ := ha_conv
    use (max N (b:Sequence).m)
    obtain ⟨f, ⟨hmono_f, feq⟩⟩ := hb_sub
    constructor
    . simp
    rw [Real.CloseSeq] at *
    simp at ha_con; simp
    intro n hN hn0
    simp [hN, hn0]
    specialize ha_con (f n.toNat)

    have f_bigger: ∀ n : ℕ, n ≤ f n := by
      intro n
      induction n with
      | zero =>
        exact Nat.zero_le _
      | succ n ih =>
        have hstep : f n + 1 ≤ f (n+1) := by
          exact Nat.succ_le_of_lt (hmono_f (Nat.lt_succ_self n))
        exact le_trans (Nat.succ_le_succ ih) hstep

    have t1 : (0 : ℤ)  ≤ Nat.cast (f n.toNat) := by
      linarith [f_bigger n.toNat]
    have t2 : N ≤ Nat.cast (f n.toNat) := by
      have := f_bigger n.toNat
      have also : n ≤ Nat.cast (f n.toNat) := by grind
      linarith
    replace ha_con := ha_con t1 t2
    simp [t1, t2] at ha_con
    rw [feq]; assumption
  intro hb; specialize hb a
  exact hb (subseq_self a)

-- Exercise 12 cont.
/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  constructor
  . intro hLP
    sorry
  intro ⟨b, ⟨hsbsq, htends⟩⟩

  intro ε heps N hN
  rw [Real.Adherent]
  obtain ⟨M, ⟨hM, htends⟩⟩ := htends ε heps
  obtain ⟨f, ⟨hmono_f, feq⟩⟩ := hsbsq
  rw [Real.CloseSeq] at htends
  simp at htends
  use M
  simp at hN hM

  have f_bigger: ∀ n : ℕ, n ≤ f n := by
    intro n
    induction n with
    | zero =>
      exact Nat.zero_le _
    | succ n ih =>
      have hstep : f n + 1 ≤ f (n+1) := by
        exact Nat.succ_le_of_lt (hmono_f (Nat.lt_succ_self n))
      exact le_trans (Nat.succ_le_succ ih) hstep

  have f_big_cast : ∀ n' : ℤ, n' ≤ Nat.cast (f n'.toNat) := by
    intro n'
    have := f_bigger n'.toNat
    have : n' ≤ Nat.cast n'.toNat := by grind
    linarith

  constructor
  . simp
    sorry
  rw [Real.Close]
  simp [hN]
  specialize htends M
  replace htends := htends hM (Int.ge_of_eq rfl)
  simp [hM] at htends
  -- very very close on this one, just running out of time and I'd much rather work
  -- chapter 9 and fomulations of continuity
  sorry

/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

-- Exercise 12
/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf' {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  rw [LimitPoint]; rw [liminf] at h
  intro ε heps
  rw [Real.ContinuallyAdherent]
  intro N hN
  rw [Real.Adherent]
  simp
  rw [← isLUB_iff_sSup_eq] at h
  rw [isLUB_iff_le_iff] at h
  -- this becomes really hard, because now we are dealing with extended reals
  -- and I don't  have a good enough grasp of Lean's libraries to do this (particularly
  -- bounds and sup/inf)
  -- Tao explains in 6_4:
  -- /-
  -- A technical issue uncovered by the formalization: the upper and lower sequences of a real
  -- sequence take values in the extended reals rather than the reals, so the definitions need to be
  -- adjusted accordingly.
  -- -/
  sorry

-- EXERCISE 12
-- just more readable than the provided B-W proof, and I proved one of the lemmas used
theorem Sequence.BW' {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
    obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
    have limit := limit_point_of_liminf' hL_minus
    rw [limit_point_iff_subseq] at limit
    obtain ⟨b, ⟨hsbsq, htends⟩⟩ := limit
    use b
    constructor
    . assumption
    rw [Convergent]; use L_minus

-- EXERCISE 13
theorem Sequence.convergent_of_cauchy {a:ℕ→ ℝ} (ha: (a:Sequence).IsCauchy) :
  (a:Sequence).Convergent := by
  have ha_bndd : (a:Sequence).IsBounded := Sequence.coe_isBounded_of_isCauchy ha
  obtain ⟨b, ⟨hb_sub, hb_conv⟩⟩ := BW' ha_bndd
  rw [Convergent] at *
  obtain ⟨L, hb_conv⟩ := hb_conv
  use L
  rw [TendsTo] at *
  intro ε h
  rw [Sequence.IsCauchy.coe] at ha; rw [Real.EventuallyClose]
  specialize ha (ε / 2); specialize hb_conv (ε / 2)
  have he2z : (ε / 2) > 0 := by nlinarith
  replace ha := ha he2z; replace hb_conv := hb_conv he2z
  rw [Real.EventuallyClose] at hb_conv
  obtain ⟨N1, ha⟩ := ha; obtain ⟨N2, ⟨hb_m, hb_conv⟩⟩ := hb_conv
  let N := max N1 N2.toNat
  have hN_N1 : N ≥ N1 := by
    dsimp [N]
    simp
  have hN_N2 : Nat.cast N ≥ N2 := by
    dsimp [N]
    simp
  use N
  constructor
  . rw [subseq] at hb_sub
    obtain ⟨f, ⟨hmono_f, hb_sub⟩⟩ := hb_sub
    rw [StrictMono] at hmono_f
    have h_nmam : (a:Sequence).m ≤ (b:Sequence).m := by linarith
    linarith
  rw [Real.CloseSeq]
  intro n hn; rw [Real.Close]
  simp at hn; simp [hn]
  rw [Real.CloseSeq] at hb_conv

  rw [subseq] at hb_sub
  obtain ⟨f, ⟨hmono_f, hb_sub⟩⟩ := hb_sub
  rw [StrictMono] at hmono_f
  have h_nmam : (a:Sequence).m ≤ (b:Sequence).m := by linarith

  specialize hb_conv N; simp at hb_conv
  have hNz : 0 ≤ N := by linarith
  replace hb_conv := hb_conv hN_N2
  simp [hN_N2] at hb_conv
  rw [Real.dist_eq]; rw [Real.dist_eq] at hb_conv
  specialize ha n.toNat
  have : 0 ≤ n := by linarith
  simp [this] at ha; simp [this]
  have : Nat.cast N1 ≤ n := by linarith
  simp [this] at ha

  specialize ha (f N)
  have f_bigger: ∀ n : ℕ, n ≤ f n := by
    intro n
    induction n with
    | zero =>
      exact Nat.zero_le _
    | succ n ih =>
      have hstep : f n + 1 ≤ f (n+1) := by
        exact Nat.succ_le_of_lt (hmono_f (Nat.lt_succ_self n))
      exact le_trans (Nat.succ_le_succ ih) hstep
  have : N1 ≤ f N := by linarith [f_bigger N]
  replace ha := ha this
  rw [Real.dist_eq] at ha
  have triangle : |a n.toNat - L| ≤ |a n.toNat - b N| + |b N - L| :=
    abs_sub_le (a n.toNat) (b N) L
  replace hb_sub := hb_sub N; rw [← hb_sub] at ha
  have ee : (ε / 2) + (ε / 2) = ε := by grind
  linarith

/- Exercise 6.6.2 -/
def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
    sorry

/--
  Exercise 6.6.3.  You may find the API around Mathlib's `Nat.find` to be useful
  (and `open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  sorry


end Chapter6
