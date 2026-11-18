import HRS.Sections.QuenchAux24

/-!
# Packet QUENCH (Q27), part 25: `Δ_a = ∑_k δv_k e^{-2λ_k a}(f_{kψ}^{⊗2} + f_{kχ}^{⊗2})`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

section Series2

variable {s β β₀ m T : ℝ}

/-- the weight `κ_j(a) = ⟨j⟩^{-2m} δv_j e^{-2λ_j a}`. -/
def kap (d : ℕ) (s β β₀ m a : ℝ) (j : NonzeroLattice d) : ℝ :=
  Lattice.jp j.1 ^ (-(2 * m)) * deltaVar d s β β₀ j.1 * Real.exp (-(lamMode d s β j.1) * (2 * a))

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
lemma abs_kap_le (hβ₀ : 0 < β₀) {a : ℝ} (ha : 0 ≤ a) (j : NonzeroLattice d) :
    |kap d s β β₀ m a j| ≤ Lattice.jp j.1 ^ (-(2 * m)) := by
  unfold kap
  have h1 := abs_deltaVar_le hd hs0 hsd hβ hβ₀ j
  have h2 : Real.exp (-(lamMode d s β j.1) * (2 * a)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [lamMode_pos hd hs0 hsd hβ j])
  have h3 : 0 ≤ Lattice.jp j.1 ^ (-(2 * m)) := Real.rpow_nonneg (Torus.jp_pos _).le _
  rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_pos (Real.exp_pos _)]
  calc Lattice.jp j.1 ^ (-(2 * m)) * |deltaVar d s β β₀ j.1| * Real.exp (-(lamMode d s β j.1) * (2 * a))
      ≤ Lattice.jp j.1 ^ (-(2 * m)) * 1 * 1 := by gcongr
    _ = _ := by ring

lemma kap_term (k : PosHalf d) (b : Bool) (a : ℝ) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    kap d s β β₀ m a (idx k b) *
      M ![(pathOf (m := m) (fexp (lamMode d s β (idx k b).1) T) (idx k b) : PathSpace d m T),
          (pathOf (m := m) (fexp (lamMode d s β (idx k b).1) T) (idx k b) : PathSpace d m T)] =
    deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
      M ![modePath m T (lamMode d s β k.1) (modeFn k.1 b), modePath m T (lamMode d s β k.1) (modeFn k.1 b)] := by
  have hl := lamMode_idx' s β k b
  rw [modePath_eq (T := T) (s := s) (β := β) k b _ rfl, M_smul]
  unfold kap
  rw [hl, deltaVar_idx' s β β₀ k b, jp_idx k b, ← hl]
  have h1 : (sgn b * Lattice.jp k.1 ^ (-m)) ^ 2 = Lattice.jp k.1 ^ (-(2 * m)) := by
    rw [mul_pow, sgn_sq, one_mul, Torus.jp_rpow_sq]
    congr 1; ring
  rw [h1, hl]
  have h2 : Real.exp (-(lamMode d s β k.1) * (2 * a)) = Real.exp (-2 * lamMode d s β k.1 * a) := by
    congr 1; ring
  rw [h2]
  ring

variable {Ω Ω' : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}
  {Zs : ℝ → Ω' → NegSobolev d m} {Ys : Ω' → NegSobolev d m}

include hd hs0 hsd hβ in
lemma summable_kapM (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) {a : ℝ} (ha : 0 ≤ a)
    (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    Summable fun j : NonzeroLattice d => kap d s β β₀ m a j *
      M ![(pathOf (m := m) (fexp (lamMode d s β j.1) T) j : PathSpace d m T),
          (pathOf (m := m) (fexp (lamMode d s β j.1) T) j : PathSpace d m T)] := by
  have hs := (summable_jp_rpow (d := d) m (by linarith)).mul_left ‖M‖
  refine Summable.of_norm_bounded hs fun j => ?_
  have h1 := abs_multi_le M (pathOf (m := m) (fexp (lamMode d s β j.1) T) j : PathSpace d m T)
    (pathOf (m := m) (fexp (lamMode d s β j.1) T) j : PathSpace d m T)
  have h2 := norm_pathOf_le (m := m) (fexp (lamMode d s β j.1) T) j
  have h3 := norm_fexp_le (T := T) (lamMode_pos hd hs0 hsd hβ j).le
  have h4 := abs_kap_le (m := m) hd hs0 hsd hβ hβ₀ ha j
  have hn : ‖(pathOf (m := m) (fexp (lamMode d s β j.1) T) j : PathSpace d m T)‖ ≤ 1 := h2.trans h3
  rw [Real.norm_eq_abs, abs_mul]
  calc |kap d s β β₀ m a j| * |M ![_, _]|
      ≤ Lattice.jp j.1 ^ (-(2 * m)) * (‖M‖ * 1 * 1) := by
        refine mul_le_mul h4 (h1.trans ?_) (abs_nonneg _) (Real.rpow_nonneg (Torus.jp_pos _).le _)
        gcongr
    _ = ‖M‖ * Lattice.jp j.1 ^ (-(2 * m)) := by ring

include hd hs0 hsd hβ in
theorem window_series (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (mf : ModeField d s β β₀ m P Z Y)
    (mf' : ModeField d s β β m P' Zs Ys) (hT : 0 < T) {a : ℝ} (ha : 0 ≤ a)
    (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    (∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P) -
        (∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P') =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)]) := by
  have w1 := winData_Z hd hs0 hsd hβ hβ₀ hm mf ha hT
  have w2 := winData_Z hd hs0 hsd hβ hβ hm mf' (le_refl (0 : ℝ)) hT
  have hsum1 : Summable fun j : NonzeroLattice d => |kap d s β β₀ m a j| * ‖fexp (lamMode d s β j.1) T‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (summable_jp_rpow (d := d) m (by linarith))
    have h3 := norm_fexp_le (T := T) (lamMode_pos hd hs0 hsd hβ j).le
    have h4 := abs_kap_le (m := m) hd hs0 hsd hβ hβ₀ ha j
    calc |kap d s β β₀ m a j| * ‖fexp (lamMode d s β j.1) T‖ ^ 2
        ≤ Lattice.jp j.1 ^ (-(2 * m)) * 1 ^ 2 :=
          mul_le_mul h4 (pow_le_pow_left₀ (norm_nonneg _) h3 2) (by positivity)
            (Real.rpow_nonneg (Torus.jp_pos _).le _)
      _ = _ := by ring
  have hc : ∀ (j : NonzeroLattice d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) T),
      cwin d s β β₀ m a j t r - cwin d s β β m 0 j t r =
        kap d s β β₀ m a j * fexp (lamMode d s β j.1) T ⟨t, ht⟩ * fexp (lamMode d s β j.1) T ⟨r, hr⟩ := by
    intro j t ht r hr
    have h0 : deltaVar d s β β j.1 = 0 := by unfold deltaVar; exact sub_self _
    simp only [cwin, kap, fexp_apply, h0]
    have e : Real.exp (-(lamMode d s β j.1) * (t + r)) =
        Real.exp (-(lamMode d s β j.1) * t) * Real.exp (-(lamMode d s β j.1) * r) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]; ring
  have hdiff := win_diff hT w1 w2 M (kap d s β β₀ m a) (fun j => fexp (lamMode d s β j.1) T) hc hsum1
  have e1 : (∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P) =
      ∫ ω, M ![toPath m T (fun t ω => Z (a + t) ω) ω, toPath m T (fun t ω => Z (a + t) ω) ω] ∂P := rfl
  have e2 : (∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P') =
      ∫ ω, M ![toPath m T (fun t ω => Zs (0 + t) ω) ω, toPath m T (fun t ω => Zs (0 + t) ω) ω] ∂P' := rfl
  rw [e1, e2, hdiff, tsum_idx _ (summable_kapM hd hs0 hsd hβ hβ₀ hm ha M)]
  refine tsum_congr fun k => ?_
  rw [kap_term, kap_term]
  ring

end Series2

end Qch

end HRS
