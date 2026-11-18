import HRS.MS.SA16Y5Pl1
import HRS.MS.SA16Y5Lc1

/-!
# S.A.16 (SA16Y5) Er1: the level-`j` error of `∂^idx P_μ φ` against `-c μ Λ^θ ∂^idx φ` (`d-2 < s < d-1`)

`sa16y5_Err_bound`: there is `c > 0` such that for every `j` there is `K` with
`‖∂^idx(P_μ φ) + c μ Λ^θ(∂^idx φ)‖_p ≤ K S_j(φ)` for `μ` with `S16FracCb`, `Cb 2 Λ`, `Dec (j+2) W`, `φ ∈ C_c^∞`.
There is no unbounded top-order commutator term here (`θ < 1`): `∂^idx P_μ φ + c μ Λ^θ ∂^idx φ` is
`Rem + C1 - c [Λ^θ, μ] w - ∑_i ∂_i(g ⋆ (∂_iμ w))`, `w = ∂^idx φ`, each bounded by `S_j`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Er1
variable {d : ℕ} {s : ℝ}

lemma sa16y5_w_le_S {p : ℝ} {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {j : ℕ} (idx : Fin j → Fin d) :
    eLpNorm (partialDeriv idx φ) (ENNReal.ofReal p) volume ≤ sa16z_S p φ j := by
  refine le_trans ?_ (sa16z_JJ_le_S φ (k := j) (N := j) le_rfl)
  unfold sa16z_JJ
  refine eLpNorm_mono ((sa16j_pd_smooth hφ idx).continuous.aestronglyMeasurable) fun y => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
  exact sa16sz_abs_le_vn φ j idx y

theorem sa16y5_Err_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s < (d : ℝ) - 1)
    (hθ0 : 0 < s + 2 - d) {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ φ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → IsCcInfty φ →
      sa16z_Cb 2 Λ μ → sa16y5_Dec (j + 2) W μ → ∀ idx : Fin j → Fin d,
      eLpNorm (fun x => partialDeriv idx (sa16z_P s μ φ) x +
          c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal K * sa16z_S p φ j := by
  have hθ1 : s + 2 - (d : ℝ) < 1 := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨c, hc, hP⟩ := sa16y5_P_lap' hd hs0 hsd hθ0
  obtain ⟨C1, hC1, hRem⟩ := sa16y5_Rem_bound hd hs0 hsd hs1 hp hfar hW
  obtain ⟨CC, hCC0, hCC⟩ := sa16y5_C1_bound hd hs0 hs1 hp hfar hW
  obtain ⟨Kc, hKc0, hKc⟩ := sa16y5_lamComm_bound hd hθ0 hθ1 (by linarith : 1 ≤ p)
  obtain ⟨Kr, hKr0, hKr⟩ := sa16y5_Rw_bound hd hs0 hs1 hp hfar hW
  refine ⟨c, hc, fun j => ?_⟩
  obtain ⟨KR, hKR0, hKR⟩ := hRem j
  have hKtot : 0 ≤ KR + CC * j + c * (Kc * Λ) + Kr * (d : ℝ) := by positivity
  refine ⟨KR + CC * j + c * (Kc * Λ) + Kr * (d : ℝ), hKtot, fun {μ φ} hμ hφ hCb hdec idx => ?_⟩
  have hμs : ContDiff ℝ ∞ μ := hμ.1
  have hw : IsCcInfty (partialDeriv idx φ) := sa16s_cc_partialDeriv hφ idx
  have hwS := sa16y5_w_le_S (p := p) hφ.1 idx
  -- the four pieces
  have e1 : eLpNorm (fun x => sa16z_Rem s μ φ j idx x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal KR * sa16z_S p φ j := hKR hμs hφ (sa16y5_Dec_mono (by omega) hdec) idx
  have e2 : eLpNorm (fun x => sa16z_C1 s μ φ j idx x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (CC * j) * sa16z_S p φ j := by
    cases j with
    | zero =>
      have : (fun x => sa16z_C1 s μ φ 0 idx x) = 0 := rfl
      rw [this, eLpNorm_zero]; exact zero_le
    | succ n =>
      have h := hCC hμs hφ (sa16y5_Dec_mono (by omega) hdec) n idx
      push_cast
      exact h
  have e3 : eLpNorm ((-c) • fun x => lamComm d (s + 2 - d) μ (partialDeriv idx φ) x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (c * (Kc * Λ)) * sa16z_S p φ j := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_neg, abs_of_pos hc]
    rw [ENNReal.ofReal_mul hc.le, mul_assoc]
    refine mul_le_mul' le_rfl ((hKc hΛ hμs hCb hw).trans ?_)
    exact mul_le_mul' le_rfl hwS
  have e4 : eLpNorm (fun x => -(∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
      (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i))) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (Kr * (d : ℝ)) * sa16z_S p φ j := by
    have e4' : eLpNorm (fun x => -(∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
        (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i))) (ENNReal.ofReal p) volume =
        eLpNorm (fun x => ∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
        (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i)) (ENNReal.ofReal p) volume :=
      eLpNorm_neg _ _ _
    rw [e4']
    exact (hKr hμs (sa16y5_Dec_mono (by omega) hdec) hw).trans (mul_le_mul' le_rfl hwS)
  have hfun : (fun x => partialDeriv idx (sa16z_P s μ φ) x +
      c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x) =
      (fun x => sa16z_Rem s μ φ j idx x) + (fun x => sa16z_C1 s μ φ j idx x) +
        ((-c) • fun x => lamComm d (s + 2 - d) μ (partialDeriv idx φ) x) +
        (fun x => -(∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
          (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i))) := by
    funext x
    have hPw := hP hμ hw x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sa16z_Rem, lamComm]
    rw [hPw]
    ring
  rw [hfun]
  calc eLpNorm ((fun x => sa16z_Rem s μ φ j idx x) + (fun x => sa16z_C1 s μ φ j idx x) +
        ((-c) • fun x => lamComm d (s + 2 - d) μ (partialDeriv idx φ) x) +
        (fun x => -(∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
          (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i)))) (ENNReal.ofReal p) volume
      ≤ eLpNorm ((fun x => sa16z_Rem s μ φ j idx x) + (fun x => sa16z_C1 s μ φ j idx x) +
        ((-c) • fun x => lamComm d (s + 2 - d) μ (partialDeriv idx φ) x)) (ENNReal.ofReal p) volume +
        eLpNorm (fun x => -(∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
          (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i))) (ENNReal.ofReal p) volume :=
        eLpNorm_add_le hp1
    _ ≤ (eLpNorm ((fun x => sa16z_Rem s μ φ j idx x) + (fun x => sa16z_C1 s μ φ j idx x)) (ENNReal.ofReal p) volume +
        eLpNorm ((-c) • fun x => lamComm d (s + 2 - d) μ (partialDeriv idx φ) x) (ENNReal.ofReal p) volume) +
        eLpNorm (fun x => -(∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
          (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i))) (ENNReal.ofReal p) volume := by
        gcongr; exact eLpNorm_add_le hp1
    _ ≤ ((eLpNorm (fun x => sa16z_Rem s μ φ j idx x) (ENNReal.ofReal p) volume +
        eLpNorm (fun x => sa16z_C1 s μ φ j idx x) (ENNReal.ofReal p) volume) +
        eLpNorm ((-c) • fun x => lamComm d (s + 2 - d) μ (partialDeriv idx φ) x) (ENNReal.ofReal p) volume) +
        eLpNorm (fun x => -(∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s)
          (fun z => sa16z_dm μ i z * partialDeriv idx φ z)) x (sa16z_e i))) (ENNReal.ofReal p) volume := by
        gcongr; exact eLpNorm_add_le hp1
    _ ≤ ((ENNReal.ofReal KR * sa16z_S p φ j + ENNReal.ofReal (CC * j) * sa16z_S p φ j) +
        ENNReal.ofReal (c * (Kc * Λ)) * sa16z_S p φ j) + ENNReal.ofReal (Kr * (d : ℝ)) * sa16z_S p φ j := by
        gcongr
    _ = ENNReal.ofReal (KR + CC * j + c * (Kc * Λ) + Kr * (d : ℝ)) * sa16z_S p φ j := by
        have h1 : 0 ≤ KR := hKR0
        have h2 : 0 ≤ CC * j := by positivity
        have h3 : 0 ≤ c * (Kc * Λ) := by positivity
        have h4 : 0 ≤ Kr * (d : ℝ) := by positivity
        rw [← add_mul, ← add_mul, ← add_mul, ← ENNReal.ofReal_add h1 h2,
          ← ENNReal.ofReal_add (add_nonneg h1 h2) h3, ← ENNReal.ofReal_add (add_nonneg (add_nonneg h1 h2) h3) h4]

end Er1

end HRS.Whole.AppendixA.Phase2SA16R
