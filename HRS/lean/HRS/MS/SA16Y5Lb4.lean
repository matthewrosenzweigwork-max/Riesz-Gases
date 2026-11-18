import HRS.MS.SA16Y5Lb3

/-!
# S.A.16 (SA16Y5) Lb4: the heat-gain bound (K2, part 4)

`sa16y5_Tm_bound` (`d - 1 < s < d`, `0 < a ≤ 1`, `1 ≤ p`): for smooth `μ'` with `|μ'| ≤ B0`, `|∂_jμ'| ≤ B1`, `v ∈ C_c^∞`:
`‖g_a ⋆ ∂_i(ρ ⋆ (μ' ∂_j v))‖_p ≤ C (B0 + B1) a^{-(s+2-d)/2} ‖v‖_p`, `C = C(d,s)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lb4
variable {d : ℕ} {s : ℝ}

lemma sa16y5_g_abs_L1 {a : ℝ} (ha : 0 < a) : ∫ z, |sa16r_g d a z| = 1 := by
  rw [← sa16r_g_mass (d := d) ha]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact abs_of_pos (sa16r_g_pos ha z)

theorem sa16y5_Tm_bound (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ p : ℝ, 1 ≤ p → ∀ (μ' v : Euc d → ℝ) (B0 B1 : ℝ) (i j : Fin d),
      ContDiff ℝ ∞ μ' → 0 ≤ B0 → 0 ≤ B1 → (∀ y, |μ' y| ≤ B0) → (∀ y, |fderiv ℝ μ' y (sa16z_e j)| ≤ B1) →
      IsCcInfty v →
      eLpNorm (sa16y5_Tm d s a μ' i j v) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * (B0 + B1) * a ^ (-((s + 2 - d) / 2))) * eLpNorm v (ENNReal.ofReal p) volume := by
  obtain ⟨Cf, hCf0, hCf⟩ := sa16y5_V_L1 hd hs hsd1 (s := s)
  have hd0 : (0 : ℝ) < d - s := by linarith
  set Cn : ℝ := (d : ℝ) * volume.real (ball (0 : Euc d) 1) * ((Real.sqrt 2) ^ ((d : ℝ) - s) / ((d : ℝ) - s)) with hCn
  have hCn0 : 0 ≤ Cn := by
    have : 0 ≤ volume.real (ball (0 : Euc d) 1) := measureReal_nonneg
    positivity
  set Cdd : ℝ := 1 / 2 + (4 / 3 : ℝ) * ((4 / 3 : ℝ) ^ d) with hCdd
  have hCdd0 : 0 ≤ Cdd := by positivity
  set Cdg : ℝ := (4 / 3 : ℝ) ^ ((d : ℝ) / 2) with hCdg
  have hCdg0 : 0 ≤ Cdg := by positivity
  refine ⟨Cn * Cdd + Cn * Cdg + Cf * Cdg + Cf, by positivity, ?_⟩
  intro a ha ha1 p hp μ' v B0 B1 i j hμ hB0 hB1 hμB hdμB hv
  set ε : ℝ := Real.sqrt a with hε
  have hε0 : 0 < ε := Real.sqrt_pos.2 ha
  have hdμ : ContDiff ℝ ∞ (fun y => fderiv ℝ μ' y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hrn := sa16y5_rn_L1 hd hs hsd hε0
  have hV := hCf ε hε0 i
  have hdd := sa16y5_ddg_L1 ha j i
  have hdgI := sa16r_dg_int ha i
  have hdgJ := sa16r_dg_int ha j
  have hgi := sa16r_g_int (d := d) ha
  -- the four terms
  set P : Euc d → ℝ := fun y => μ' y * v y with hP
  have tA := sa16y5_young2 (sa16y5_rn_meas (s := s) ε) (sa16y5_ddg_cont a j i).measurable hrn.1 hdd.1 hμ hB0 hμB hv hp
  have tB := sa16y5_young2 (sa16y5_rn_meas (s := s) ε) (sa16r_dg_cont a i).measurable hrn.1 hdgI hdμ hB1 hdμB hv hp
  have tC := sa16y5_young2 (sa16y5_V_meas (s := s) ε i) (sa16r_dg_cont a j).measurable hV.1 hdgJ hμ hB0 hμB hv hp
  have tD := sa16y5_young2 (sa16y5_V_meas (s := s) ε i) (sa16r_g_meas (d := d) (a := a)) hV.1 hgi hdμ hB1 hdμB hv hp
  -- the function identity
  set FA : Euc d → ℝ := sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P) with hFA
  set FB : Euc d → ℝ := sa16r_cv (sa16y5_rn d s ε)
    (sa16r_cv (sa16r_dg d a i) (fun y => fderiv ℝ μ' y (sa16z_e j) * v y)) with hFB
  set FC : Euc d → ℝ := sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P) with hFC
  set FD : Euc d → ℝ := sa16r_cv (sa16y5_V d s ε i)
    (sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ μ' y (sa16z_e j) * v y)) with hFD
  have hTm : sa16y5_Tm d s a μ' i j v = FA - FB + FC - FD := by
    funext x
    have := sa16y5_Tm_eq hd hs hsd hsd1 ha hε0 hμ hv i j x
    simpa [hFA, hFB, hFC, hFD, hP] using this
  have hQcc : IsCcInfty (fun y => fderiv ℝ μ' y (sa16z_e j) * v y) := sa16y5_cc_dmu hμ hv j
  have hPcc : IsCcInfty P := sa16y5_cc_mul hμ hv
  have hp' : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hsum : eLpNorm (FA - FB + FC - FD) (ENNReal.ofReal p) volume ≤
      eLpNorm FA (ENNReal.ofReal p) volume + eLpNorm FB (ENNReal.ofReal p) volume +
        eLpNorm FC (ENNReal.ofReal p) volume + eLpNorm FD (ENNReal.ofReal p) volume := by
    calc eLpNorm (FA - FB + FC - FD) (ENNReal.ofReal p) volume
        ≤ eLpNorm (FA - FB + FC) (ENNReal.ofReal p) volume + eLpNorm FD (ENNReal.ofReal p) volume :=
          eLpNorm_sub_le hp'
      _ ≤ (eLpNorm (FA - FB) (ENNReal.ofReal p) volume + eLpNorm FC (ENNReal.ofReal p) volume) +
            eLpNorm FD (ENNReal.ofReal p) volume := by
          gcongr
          exact eLpNorm_add_le hp'
      _ ≤ ((eLpNorm FA (ENNReal.ofReal p) volume + eLpNorm FB (ENNReal.ofReal p) volume) +
            eLpNorm FC (ENNReal.ofReal p) volume) + eLpNorm FD (ENNReal.ofReal p) volume := by
          gcongr
          exact eLpNorm_sub_le hp'
  -- the real constants
  have n0 : ∀ k : Euc d → ℝ, 0 ≤ ∫ z, |k z| := fun k => integral_nonneg fun z => abs_nonneg _
  set X : ℝ := a ^ (-((s + 2 - d) / 2)) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg ha.le _
  have hεpow : ∀ r : ℝ, ε ^ r = a ^ (r / 2) := by
    intro r
    rw [hε, Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le]
    congr 1; ring
  have e1 : ε ^ ((d : ℝ) - s) * a⁻¹ = X := by
    rw [hεpow, ← Real.rpow_neg_one, ← Real.rpow_add ha, hX]
    congr 1; ring
  have e2 : ε ^ ((d : ℝ) - s) * a ^ (-(1 / 2 : ℝ)) ≤ X := by
    rw [hεpow, ← Real.rpow_add ha, hX]
    exact Real.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith)
  have e3 : ε ^ ((d : ℝ) - (s + 1)) * a ^ (-(1 / 2 : ℝ)) = X := by
    rw [hεpow, ← Real.rpow_add ha, hX]
    congr 1; ring
  have e4 : ε ^ ((d : ℝ) - (s + 1)) ≤ X := by
    rw [hεpow, hX]
    exact Real.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith)
  have hε1 : 0 ≤ ε ^ ((d : ℝ) - s) := Real.rpow_nonneg hε0.le _
  have hε2 : 0 ≤ ε ^ ((d : ℝ) - (s + 1)) := Real.rpow_nonneg hε0.le _
  have ha12 : 0 ≤ a ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha.le _
  have nrn := hrn.2
  have nddg := hdd.2
  have ndgi := sa16r_dg_L1 ha i
  have ndgj := sa16r_dg_L1 ha j
  have nV := hV.2
  have ng := sa16y5_g_abs_L1 (d := d) ha
  have T1 : (∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16y5_ddg d a j i z|) * B0 ≤ Cn * Cdd * B0 * X := by
    calc _ ≤ (Cn * ε ^ ((d : ℝ) - s)) * (Cdd * a⁻¹) * B0 := by
          gcongr
        _ = Cn * Cdd * B0 * (ε ^ ((d : ℝ) - s) * a⁻¹) := by ring
        _ = _ := by rw [e1]
  have T2 : (∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16r_dg d a i z|) * B1 ≤ Cn * Cdg * B1 * X := by
    calc _ ≤ (Cn * ε ^ ((d : ℝ) - s)) * (a ^ (-(1 / 2 : ℝ)) * Cdg) * B1 := by
          gcongr
        _ = Cn * Cdg * B1 * (ε ^ ((d : ℝ) - s) * a ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ Cn * Cdg * B1 * X := by gcongr
  have T3 : (∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_dg d a j z|) * B0 ≤ Cf * Cdg * B0 * X := by
    calc _ ≤ (Cf * ε ^ ((d : ℝ) - (s + 1))) * (a ^ (-(1 / 2 : ℝ)) * Cdg) * B0 := by
          gcongr
        _ = Cf * Cdg * B0 * (ε ^ ((d : ℝ) - (s + 1)) * a ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [e3]
  have T4 : (∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_g d a z|) * B1 ≤ Cf * B1 * X := by
    rw [ng]
    calc _ ≤ (Cf * ε ^ ((d : ℝ) - (s + 1))) * 1 * B1 := by
          gcongr
        _ = Cf * B1 * ε ^ ((d : ℝ) - (s + 1)) := by ring
        _ ≤ Cf * B1 * X := by gcongr
  have hnn1 := n0 (sa16y5_rn d s ε)
  have hnn2 := n0 (sa16y5_ddg d a j i)
  have hnn3 := n0 (sa16r_dg d a i)
  have hnn4 := n0 (sa16y5_V d s ε i)
  have hnn5 := n0 (sa16r_dg d a j)
  have hnn6 := n0 (sa16r_g d a)
  have hf : ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16y5_ddg d a j i z|) * B0) +
      ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16r_dg d a i z|) * B1) +
      ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_dg d a j z|) * B0) +
      ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_g d a z|) * B1) ≤
      ENNReal.ofReal ((Cn * Cdd + Cn * Cdg + Cf * Cdg + Cf) * (B0 + B1) * X) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 0 ≤ Cn * Cdd := by positivity
    have h2 : 0 ≤ Cn * Cdg := by positivity
    have h3 : 0 ≤ Cf * Cdg := by positivity
    have hdiff : (Cn * Cdd + Cn * Cdg + Cf * Cdg + Cf) * (B0 + B1) * X -
        (Cn * Cdd * B0 * X + Cn * Cdg * B1 * X + Cf * Cdg * B0 * X + Cf * B1 * X) =
        X * (Cn * Cdd * B1 + Cn * Cdg * B0 + Cf * Cdg * B1 + Cf * B0) := by ring
    have hnn : 0 ≤ X * (Cn * Cdd * B1 + Cn * Cdg * B0 + Cf * Cdg * B1 + Cf * B0) := by positivity
    linarith [T1, T2, T3, T4, hdiff, hnn]
  calc eLpNorm (sa16y5_Tm d s a μ' i j v) (ENNReal.ofReal p) volume
      = eLpNorm (FA - FB + FC - FD) (ENNReal.ofReal p) volume := by rw [hTm]
    _ ≤ _ := hsum
    _ ≤ ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16y5_ddg d a j i z|) * B0) *
            eLpNorm v (ENNReal.ofReal p) volume +
          ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16r_dg d a i z|) * B1) *
            eLpNorm v (ENNReal.ofReal p) volume +
          ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_dg d a j z|) * B0) *
            eLpNorm v (ENNReal.ofReal p) volume +
          ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_g d a z|) * B1) *
            eLpNorm v (ENNReal.ofReal p) volume :=
        add_le_add (add_le_add (add_le_add tA tB) tC) tD
    _ = (ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16y5_ddg d a j i z|) * B0) +
      ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16r_dg d a i z|) * B1) +
      ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_dg d a j z|) * B0) +
      ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_g d a z|) * B1)) *
        eLpNorm v (ENNReal.ofReal p) volume := by ring
    _ ≤ _ := by gcongr

end Lb4

end HRS.Whole.AppendixA.Phase2SA16R
