import HRS.MS.SA16Y5Lb5

/-!
# S.A.16 (SA16Y5) Lb6: the heat-gain bound for the bilinear operator `T(P,Q)` (K2 jets, part 2)

`sa16y5_T_bound` (`d-1 < s < d`): `∃ C ≥ 0` such that for `0 < a ≤ 1`, `p ≥ 1`, `P, Q ∈ C_c^∞`,
`‖T_{a,√a}(P,Q)‖_p ≤ C a^{-(s+2-d)/2} (‖P‖_p + ‖Q‖_p)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lb6
variable {d : ℕ} {s : ℝ}

lemma sa16y5_young2' {k₁ k₂ : Euc d → ℝ} (h1m : Measurable k₁) (h2m : Measurable k₂)
    (h1 : Integrable k₁) (h2 : Integrable k₂) {P : Euc d → ℝ} (hP : IsCcInfty P) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (sa16r_cv k₁ (sa16r_cv k₂ P)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((∫ z, |k₁ z|) * (∫ z, |k₂ z|)) * eLpNorm P (ENNReal.ofReal p) volume := by
  have n1 : 0 ≤ ∫ z, |k₁ z| := integral_nonneg fun z => abs_nonneg _
  have n2 : 0 ≤ ∫ z, |k₂ z| := integral_nonneg fun z => abs_nonneg _
  have s1 := sa16y5_young h1m h1 (sa16y5_cv_cont h2 hP) hp
  have s2 := sa16y5_young h2m h2 hP.1.continuous hp
  calc _ ≤ ENNReal.ofReal (∫ z, |k₁ z|) * eLpNorm (sa16r_cv k₂ P) (ENNReal.ofReal p) volume := s1
    _ ≤ ENNReal.ofReal (∫ z, |k₁ z|) * (ENNReal.ofReal (∫ z, |k₂ z|) * eLpNorm P (ENNReal.ofReal p) volume) := by
        gcongr
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul n1]

set_option maxHeartbeats 1600000 in
theorem sa16y5_T_bound (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ p : ℝ, 1 ≤ p → ∀ (i j : Fin d) (P Q : Euc d → ℝ),
      IsCcInfty P → IsCcInfty Q →
      eLpNorm (sa16y5_T d s a (Real.sqrt a) i j P Q) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * a ^ (-((s + 2 - d) / 2))) *
          (eLpNorm P (ENNReal.ofReal p) volume + eLpNorm Q (ENNReal.ofReal p) volume) := by
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
  refine ⟨2 * (Cn * Cdd + Cn * Cdg + Cf * Cdg + Cf), by positivity, ?_⟩
  intro a ha ha1 p hp i j P Q hP hQ
  set ε : ℝ := Real.sqrt a with hε
  have hε0 : 0 < ε := Real.sqrt_pos.2 ha
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sa16y5_kernels_int hd hs hsd hsd1 ha hε0 i j
  have hrn := sa16y5_rn_L1 hd hs hsd hε0
  have hV := hCf ε hε0 i
  have hdd := sa16y5_ddg_L1 ha j i
  have tA := sa16y5_young2' (sa16y5_rn_meas (s := s) ε) (sa16y5_ddg_cont a j i).measurable h1 h2 hP hp
  have tB := sa16y5_young2' (sa16y5_rn_meas (s := s) ε) (sa16r_dg_cont a i).measurable h1 h3 hQ hp
  have tC := sa16y5_young2' (sa16y5_V_meas (s := s) ε i) (sa16r_dg_cont a j).measurable h5 h4 hP hp
  have tD := sa16y5_young2' (sa16y5_V_meas (s := s) ε i) (sa16r_g_meas (d := d) (a := a)) h5 h6 hQ hp
  have hp' : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hsum : eLpNorm (sa16y5_T d s a ε i j P Q) (ENNReal.ofReal p) volume ≤
      eLpNorm (sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P)) (ENNReal.ofReal p) volume +
      eLpNorm (sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q)) (ENNReal.ofReal p) volume +
      eLpNorm (sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P)) (ENNReal.ofReal p) volume +
      eLpNorm (sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q)) (ENNReal.ofReal p) volume := by
    have e : sa16y5_T d s a ε i j P Q =
        sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P)
          - sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q)
          + sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P)
          - sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q) := rfl
    rw [e]
    calc _ ≤ eLpNorm (sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P)
          - sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q)
          + sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P)) (ENNReal.ofReal p) volume +
          eLpNorm (sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q)) (ENNReal.ofReal p) volume :=
          eLpNorm_sub_le hp'
      _ ≤ (eLpNorm (sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P)
          - sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q)) (ENNReal.ofReal p) volume +
          eLpNorm (sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P)) (ENNReal.ofReal p) volume) +
          eLpNorm (sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q)) (ENNReal.ofReal p) volume := by
          gcongr
          exact eLpNorm_add_le hp'
      _ ≤ _ := by
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
  have T1 : (∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16y5_ddg d a j i z|) ≤ Cn * Cdd * X := by
    calc _ ≤ (Cn * ε ^ ((d : ℝ) - s)) * (Cdd * a⁻¹) := by gcongr
        _ = Cn * Cdd * (ε ^ ((d : ℝ) - s) * a⁻¹) := by ring
        _ = _ := by rw [e1]
  have T2 : (∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16r_dg d a i z|) ≤ Cn * Cdg * X := by
    calc _ ≤ (Cn * ε ^ ((d : ℝ) - s)) * (a ^ (-(1 / 2 : ℝ)) * Cdg) := by gcongr
        _ = Cn * Cdg * (ε ^ ((d : ℝ) - s) * a ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ Cn * Cdg * X := by gcongr
  have T3 : (∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_dg d a j z|) ≤ Cf * Cdg * X := by
    calc _ ≤ (Cf * ε ^ ((d : ℝ) - (s + 1))) * (a ^ (-(1 / 2 : ℝ)) * Cdg) := by gcongr
        _ = Cf * Cdg * (ε ^ ((d : ℝ) - (s + 1)) * a ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [e3]
  have T4 : (∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_g d a z|) ≤ Cf * X := by
    rw [ng]
    calc _ ≤ (Cf * ε ^ ((d : ℝ) - (s + 1))) * 1 := by gcongr
        _ = Cf * ε ^ ((d : ℝ) - (s + 1)) := by ring
        _ ≤ Cf * X := by gcongr
  have hnn1 := n0 (sa16y5_rn d s ε)
  have hnn2 := n0 (sa16y5_ddg d a j i)
  have hnn3 := n0 (sa16r_dg d a i)
  have hnn4 := n0 (sa16y5_V d s ε i)
  have hnn5 := n0 (sa16r_dg d a j)
  have hnn6 := n0 (sa16r_g d a)
  set Ctot : ℝ := Cn * Cdd + Cn * Cdg + Cf * Cdg + Cf with hCtot
  have hCt0 : 0 ≤ Ctot := by positivity
  set EP := eLpNorm P (ENNReal.ofReal p) volume with hEP
  set EQ := eLpNorm Q (ENNReal.ofReal p) volume with hEQ
  have fA : ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16y5_ddg d a j i z|)) ≤
      ENNReal.ofReal (Ctot * X) := ENNReal.ofReal_le_ofReal (by
    have : Cn * Cdd * X ≤ Ctot * X := by
      have h : 0 ≤ Cn * Cdg + Cf * Cdg + Cf := by positivity
      nlinarith [mul_nonneg h hX0]
    linarith)
  have fB : ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16r_dg d a i z|)) ≤
      ENNReal.ofReal (Ctot * X) := ENNReal.ofReal_le_ofReal (by
    have : Cn * Cdg * X ≤ Ctot * X := by
      have h : 0 ≤ Cn * Cdd + Cf * Cdg + Cf := by positivity
      nlinarith [mul_nonneg h hX0]
    linarith)
  have fC : ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_dg d a j z|)) ≤
      ENNReal.ofReal (Ctot * X) := ENNReal.ofReal_le_ofReal (by
    have : Cf * Cdg * X ≤ Ctot * X := by
      have h : 0 ≤ Cn * Cdd + Cn * Cdg + Cf := by positivity
      nlinarith [mul_nonneg h hX0]
    linarith)
  have fD : ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_g d a z|)) ≤
      ENNReal.ofReal (Ctot * X) := ENNReal.ofReal_le_ofReal (by
    have : Cf * X ≤ Ctot * X := by
      have h : 0 ≤ Cn * Cdd + Cn * Cdg + Cf * Cdg := by positivity
      nlinarith [mul_nonneg h hX0]
    linarith)
  calc eLpNorm (sa16y5_T d s a ε i j P Q) (ENNReal.ofReal p) volume ≤ _ := hsum
    _ ≤ ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16y5_ddg d a j i z|)) * EP +
          ENNReal.ofReal ((∫ z, |sa16y5_rn d s ε z|) * (∫ z, |sa16r_dg d a i z|)) * EQ +
          ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_dg d a j z|)) * EP +
          ENNReal.ofReal ((∫ z, |sa16y5_V d s ε i z|) * (∫ z, |sa16r_g d a z|)) * EQ :=
        add_le_add (add_le_add (add_le_add tA tB) tC) tD
    _ ≤ ENNReal.ofReal (Ctot * X) * EP + ENNReal.ofReal (Ctot * X) * EQ +
          ENNReal.ofReal (Ctot * X) * EP + ENNReal.ofReal (Ctot * X) * EQ :=
        add_le_add (add_le_add (add_le_add (mul_le_mul_left fA EP) (mul_le_mul_left fB EQ))
          (mul_le_mul_left fC EP)) (mul_le_mul_left fD EQ)
    _ = ENNReal.ofReal (2 * Ctot * X) * (EP + EQ) := by
        have h2 : ENNReal.ofReal (2 * Ctot * X) = 2 * ENNReal.ofReal (Ctot * X) := by
          rw [show 2 * Ctot * X = 2 * (Ctot * X) by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          simp
        rw [h2]
        ring

end Lb6

end HRS.Whole.AppendixA.Phase2SA16R
