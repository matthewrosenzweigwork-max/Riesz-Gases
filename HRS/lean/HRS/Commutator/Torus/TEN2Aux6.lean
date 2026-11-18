import HRS.Commutator.Torus.TEN2Aux5

/-!
# Torus energy layer (packet T-EN2), helper part 6: `‖f_η^𝕋‖_{L^q(𝕋^d)} ≤ Cη^{d/q-s}` and Hölder on `𝕋^d`

Prefix `ten2_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

/-- Properties of the Hölder conjugate of an exponent `p > d/(d-s)`. -/
theorem ten2_conj_facts (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {p q : ℝ≥0∞}
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    q ≠ 0 ∧ q ≠ ⊤ ∧ 1 ≤ q ∧ 1 ≤ q.toReal := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hds : 0 < (d : ℝ) - s := by linarith
  have hρ1 : 1 ≤ (d : ℝ) / (d - s) := by
    rw [le_div_iff₀ hds]; linarith
  have hp1 : 1 < p := lt_of_le_of_lt (by simpa using ENNReal.ofReal_le_ofReal hρ1) hp
  have hpinv : p⁻¹ < 1 := ENNReal.inv_lt_one.2 hp1
  have hqt : q ≠ ⊤ := by
    intro h
    rw [h, ENNReal.inv_top, add_zero] at hpq
    exact absurd hpq hpinv.ne
  have hq1 : 1 ≤ q := by
    have : q⁻¹ ≤ 1 := by
      calc q⁻¹ ≤ p⁻¹ + q⁻¹ := le_add_self
        _ = 1 := hpq
    exact ENNReal.inv_le_one.1 this
  refine ⟨?_, hqt, hq1, ?_⟩
  · intro h; rw [h] at hq1; simp at hq1
  · have := ENNReal.toReal_mono hqt hq1
    simpa using this

/-- `‖f_η^𝕋‖_{L^q(𝕋^d)} ≤ C η^{d/q-s}` for `q` conjugate to `p > d/(d-s)`, `0 < η ≤ 1`. -/
theorem ten2_fTorus_Lq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {p q : ℝ≥0∞}
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      MemLp (fTorus s η : Torus d → ℝ) q volume ∧
        (eLpNorm (fTorus s η : Torus d → ℝ) q volume).toReal ≤ C * η ^ ((d : ℝ) / q.toReal - s) := by
  obtain ⟨hq0, hqt, hq1, hQ1⟩ := ten2_conj_facts hd hs0 hsd hp hpq
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hL1 : MemLp (Whole.fTrunc s 1 : Euc d → ℝ) q volume := Whole.fTrunc_Lq hd hs0 hsd p q hp hpq
  set L1 := eLpNorm (Whole.fTrunc s 1 : Euc d → ℝ) q volume with hL1def
  have hL1fin : L1 ≠ ⊤ := hL1.eLpNorm_lt_top.ne
  have hts := tpos_tScale_pos (s := s) hs0
  have hK1 := ten2K1_nonneg hd hs0 hsd
  have hK := ten2K_nonneg hd hs0 hsd
  refine ⟨tScale s * (L1.toReal + ten2K1 d s) + ten2K d s, by positivity, fun η hη hη1 => ?_⟩
  set e : ℝ := (d : ℝ) / q.toReal - s with he
  have hQd : (d : ℝ) / q.toReal ≤ d := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hηe : 0 < η ^ e := Real.rpow_pos_of_pos hη _
  -- the real-variable pieces
  set P : Torus d → ℝ := perio (Whole.fTrunc s η : Euc d → ℝ) with hP
  set m : ℝ := ∫ y : Torus d, P y with hm
  have hPm : Measurable P := tpos_perio_measurable (tpos_fTrunc_measurable hη)
  have hm_eq := tpos_integral_perio_fTrunc (d := d) hs0 hsd hη
  have hm0 : 0 ≤ m := integral_nonneg fun y => tpos_perio_nonneg
    (fun z => tpos_fTrunc_nonneg hs0 hs2 η z) y
  have hfun : (fTorus s η : Torus d → ℝ) = (tScale s) • (P - fun _ => m) := by
    funext x; simp [fTorus, hP, hm]
  -- bound of `perio`
  set T : ℝ := ten2K1 d s * η ^ (2 * (d : ℝ) + 4 - s) with hT
  have hT0 : 0 ≤ T := by positivity
  have hcrm : AEStronglyMeasurable
      (fun x : Torus d => (Whole.fTrunc s η : Euc d → ℝ) (KernelGrad.centeredRep x)) volume :=
    ((tpos_fTrunc_measurable hη).comp ten2_cr_measurable).aestronglyMeasurable
  have hPle : eLpNorm P q volume ≤
      eLpNorm (fun x : Torus d => (Whole.fTrunc s η : Euc d → ℝ) (KernelGrad.centeredRep x)) q volume +
        ENNReal.ofReal T := by
    have h1 : eLpNorm P q volume ≤ eLpNorm
        ((fun x : Torus d => (Whole.fTrunc s η : Euc d → ℝ) (KernelGrad.centeredRep x)) +
          fun _ => T) q volume := by
      refine eLpNorm_mono hPm.aestronglyMeasurable fun x => ?_
      have hnn := tpos_perio_nonneg (fun z => tpos_fTrunc_nonneg hs0 hs2 η z) x
      have hf0 := tpos_fTrunc_nonneg hs0 hs2 η (KernelGrad.centeredRep x)
      have := ten2_perio_le hd hs0 hsd hη x
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg hnn, abs_of_nonneg (by linarith)]
      exact this
    refine h1.trans ((eLpNorm_add_le hq1).trans ?_)
    refine add_le_add le_rfl (le_of_eq ?_)
    rw [eLpNorm_const _ hq0 (IsProbabilityMeasure.ne_zero _), measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_of_nonneg hT0]
  have hcr := ten2_eLpNorm_cr (d := d) (s := s) hq0 hqt hη
  have hsc := ten2_eLpNorm_fTrunc_scale (d := d) (s := s) hq0 hqt hη
  have hmc : eLpNorm (fun _ : Torus d => m) q volume = ENNReal.ofReal m := by
    rw [eLpNorm_const _ hq0 (IsProbabilityMeasure.ne_zero _), measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_of_nonneg hm0]
  have hmain : eLpNorm (fTorus s η : Torus d → ℝ) q volume ≤
      ENNReal.ofReal (tScale s) * (ENNReal.ofReal (η ^ e) * L1 + ENNReal.ofReal T + ENNReal.ofReal m) := by
    rw [hfun]
    refine (eLpNorm_const_smul_le).trans ?_
    rw [Real.enorm_of_nonneg hts.le]
    refine mul_le_mul' le_rfl ?_
    refine (eLpNorm_sub_le hq1).trans ?_
    rw [hmc]
    refine add_le_add ?_ le_rfl
    calc eLpNorm P q volume ≤ _ := hPle
      _ ≤ ENNReal.ofReal (η ^ e) * L1 + ENNReal.ofReal T := add_le_add (hcr.trans hsc) le_rfl
  -- real inequality
  have hTle : T ≤ ten2K1 d s * η ^ e := by
    refine mul_le_mul_of_nonneg_left ?_ hK1
    exact Real.rpow_le_rpow_of_exponent_ge hη hη1 (by rw [he]; linarith)
  have hmle : tScale s * m ≤ ten2K d s * η ^ e := by
    have hm' : m = Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s) *
        η ^ ((d : ℝ) - s) := hm_eq
    rw [hm']
    have : tScale s * (Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s) *
        η ^ ((d : ℝ) - s)) = ten2K d s * η ^ ((d : ℝ) - s) := by unfold ten2K; ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hK
    exact Real.rpow_le_rpow_of_exponent_ge hη hη1 (by rw [he]; linarith)
  have hfin : ENNReal.ofReal (tScale s) * (ENNReal.ofReal (η ^ e) * L1 + ENNReal.ofReal T +
      ENNReal.ofReal m) =
      ENNReal.ofReal (tScale s * (η ^ e * L1.toReal + T + m)) := by
    rw [ENNReal.ofReal_mul hts.le, ENNReal.ofReal_add (by positivity) hm0,
      ENNReal.ofReal_add (by positivity) hT0, ENNReal.ofReal_mul hηe.le, ENNReal.ofReal_toReal hL1fin]
  have hbound : tScale s * (η ^ e * L1.toReal + T + m) ≤
      (tScale s * (L1.toReal + ten2K1 d s) + ten2K d s) * η ^ e := by
    have h1 : tScale s * T ≤ tScale s * (ten2K1 d s * η ^ e) := mul_le_mul_of_nonneg_left hTle hts.le
    nlinarith [h1, hmle]
  have hR0 : 0 ≤ (tScale s * (L1.toReal + ten2K1 d s) + ten2K d s) * η ^ e := by positivity
  have hle : eLpNorm (fTorus s η : Torus d → ℝ) q volume ≤
      ENNReal.ofReal ((tScale s * (L1.toReal + ten2K1 d s) + ten2K d s) * η ^ e) := by
    refine hmain.trans ?_
    rw [hfin]
    exact ENNReal.ofReal_le_ofReal hbound
  exact ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top, ENNReal.toReal_le_of_le_ofReal hR0 hle⟩

end HRS.Commutator.TorusNote
