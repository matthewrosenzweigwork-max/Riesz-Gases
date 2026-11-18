import HRS.MS.MovSchAux1

/-!
# S64 (S6.4 `mov_schwartz`), part 2: weighted bounds of the thermal data and of `h_u`, `F_u`, and the flux decomposition

Namespace `HRS.MS.MovSch`, prefix `s64_`.  For `u ∈ Σ^m` (`m : ℕ`, `K + d/2 + 4 < m`):
`V_u = mn_repFun (K+3) m u` (the `C^{K+3}` representative; equals the `C³` representative `mneV hm u`), `h_u = √ρ V_u`,
`F_u = ∇g*h_u` (`mneFo`), `Y_u = mneY`.

* `s64_sqrt_W`, `s64_rho_W`: `√ρ` and `ρ` are in `s64_W n L` for every `n, L` (Gaussian bounds).
* `s64_A_P`: `A = q x + ∇g*ρ = -ν ∇log ρ` is `s64_P n 1`.
* `s64_h_W`: `h_u ∈ s64_W (K+2) L` with constant linear in `‖u‖`.
* `s64_Fu_bdd`: `F_u ∈ C^{K+1}` with `‖D^k F_u‖ ≤ C ‖u‖`.
* `s64_Y_decomp`: `Y_u = ν ∇h_u + h_u • A + (ρ + h_u) • F_u` (Euler equation).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Thermal

lemma s64_gapref (H : Mov2dTh d s β q ρ) :
    ∃ B : Euc d → Euc d, HRS.MS.Gap.GapRef d ρ (β * q) B :=
  let ⟨B, _, hR, _⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  ⟨B, hR⟩

lemma s64_sqrt_W (H : Mov2dTh d s β q ρ) (n L : ℕ) : ∃ M : ℝ, s64_W n L (fun x => Real.sqrt (ρ x)) M := by
  obtain ⟨B, hR⟩ := s64_gapref H
  obtain ⟨hsm, -, c, hc, hb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss (mul_pos H.hβ H.hq) hR
  exact s64_W_gauss L hc ((contDiff_infty.1 hsm) n) hb

lemma s64_rho_W (H : Mov2dTh d s β q ρ) (n L : ℕ) : ∃ M : ℝ, s64_W n L ρ M := by
  obtain ⟨B, hR⟩ := s64_gapref H
  obtain ⟨hsm, c, hc, hb⟩ := HRS.MS.Mov0.mv0_hgauss_gapref (mul_pos H.hβ H.hq) hR
  exact s64_W_gauss L hc ((contDiff_infty.1 hsm) n) hb

/-- The Euler equation: `ν ∇log ρ + q x + ∇g*ρ = 0`. -/
lemma s64_euler (H : Mov2dTh d s β q ρ) (x : Euc d) :
    β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + movForce d s ρ x = 0 :=
  HRS.MS.Mov0.mv0_thermal_force H.hd H.hs0 H.hsd H.hq H.hβ H.hρ x

/-- `A = q x + ∇g*ρ = -ν ∇log ρ`. -/
lemma s64_A_eq (H : Mov2dTh d s β q ρ) (x : Euc d) :
    q • x + movForce d s ρ x = -(β⁻¹ • gradient (fun y => Real.log (ρ y)) x) := by
  have := s64_euler H x
  rw [eq_neg_iff_add_eq_zero, ← this]
  abel

lemma s64_P_const_smul {n p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Euc d → F} {B : ℝ}
    (c : ℝ) (h : s64_P n p A B) : s64_P n p (fun x => c • A x) (|c| * B) := by
  refine ⟨h.1.const_smul c, fun k hk x => ?_⟩
  have e : iteratedFDeriv ℝ k (fun x => c • A x) x = c • iteratedFDeriv ℝ k A x :=
    iteratedFDeriv_const_smul_apply (h.1.contDiffAt.of_le (by exact_mod_cast hk))
  rw [e, norm_smul, Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ k A x‖ ≤ |c| * (B * movBracket x ^ p) :=
        mul_le_mul_of_nonneg_left (h.2 k hk x) (abs_nonneg c)
    _ = |c| * B * movBracket x ^ p := by ring

lemma s64_dlog_P (H : Mov2dTh d s β q ρ) (n : ℕ) :
    ∃ B : ℝ, s64_P n 1 (fun y => gradient (fun z => Real.log (ρ z)) y) B := by
  obtain ⟨B0, hR⟩ := s64_gapref H
  have hq' : 0 < β * q := mul_pos H.hβ H.hq
  obtain ⟨hk, M, hM⟩ := HRS.MS.Mov0.mv0_dlog_bounds hq'.le hR
  choose C hC using hk
  have hcd : ContDiff ℝ (n : WithTop ℕ∞) (fun y => gradient (fun z => Real.log (ρ z)) y) := by
    have hfun : (fun y => gradient (fun z => Real.log (ρ z)) y) =
        fun y => (-(β * q)) • y + B0 y := by
      funext y
      exact HRS.MS.Mov0.mov0_grad_log hR y
    rw [hfun]
    exact (contDiff_id.const_smul (-(β * q))).add ((contDiff_infty.1 (HRS.MS.Mov0.mov0_B_smooth hR)) n)
  refine ⟨(β * q) + M + ∑ k ∈ Finset.range (n + 1), |if h : 1 ≤ k then C k h else 0|, hcd, fun k hk x => ?_⟩
  have hb := s64_bracket_pos x
  have hb1 := s64_bracket_one_le x
  have hx := s64_norm_le_bracket x
  by_cases hk0 : k = 0
  · subst hk0
    rw [norm_iteratedFDeriv_zero]
    refine (hM x).trans ?_
    have hS : 0 ≤ ∑ k ∈ Finset.range (n + 1), |if h : 1 ≤ k then C k h else 0| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (by simpa using hM 0)
    rw [pow_one]
    nlinarith [mul_le_mul_of_nonneg_left hx hq'.le, mul_le_mul_of_nonneg_left hb1 hM0,
      mul_le_mul_of_nonneg_left hb1 hS]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    have h1 := hC k hk1 x
    have hCk : |C k hk1| ≤ ∑ k ∈ Finset.range (n + 1), |if h : 1 ≤ k then C k h else 0| := by
      have := Finset.single_le_sum (f := fun k => |if h : 1 ≤ k then C k h else 0|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (show k < n + 1 by omega))
      simpa [hk1] using this
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (by simpa using hM 0)
    have hS : 0 ≤ ∑ k ∈ Finset.range (n + 1), |if h : 1 ≤ k then C k h else 0| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [pow_one]
    nlinarith [le_abs_self (C k hk1), mul_le_mul_of_nonneg_left hb1 hS,
      mul_nonneg hq'.le hb.le, mul_nonneg hM0 hb.le, mul_le_mul_of_nonneg_left hb1 hq'.le]

lemma s64_A_P (H : Mov2dTh d s β q ρ) (n : ℕ) :
    ∃ B : ℝ, s64_P n 1 (fun x => q • x + movForce d s ρ x) B := by
  obtain ⟨B, hB⟩ := s64_dlog_P H n
  refine ⟨|-(β⁻¹)| * B, ?_⟩
  have := s64_P_const_smul (-(β⁻¹)) hB
  have e : (fun x => q • x + movForce d s ρ x) = fun x => (-(β⁻¹)) • gradient (fun z => Real.log (ρ z)) x := by
    funext x
    rw [s64_A_eq H x, neg_smul]
  rw [e]
  exact this

end Thermal

end HRS.MS.MovSch

end
