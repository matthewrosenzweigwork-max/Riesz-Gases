import HRS.MS.R26T6CI07Pos

/-!
The logarithmic endpoint of the physical L²-to-L³ kernel estimate. A mild
Riesz singularity controls the negative logarithm, while a first spatial
moment controls the positive logarithm. The row envelope belongs to L³.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.R26T6C

variable {d : ℕ}

theorem logarithmic_kernel_bound (z : Euc d) :
    |rieszKernel d 0 z| ≤ 2 * rieszKernel d (1 / 2) z + ‖z‖ := by
  have hp : Real.log ‖z‖ ≤ ‖z‖ := by
    simpa using Real.log_le_rpow_div (norm_nonneg z) (by norm_num : (0 : ℝ) < 1)
  have hn : -Real.log ‖z‖ ≤ 2 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    have h := Real.log_le_rpow_div (inv_nonneg.2 (norm_nonneg z))
      (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.log_inv, Real.inv_rpow (norm_nonneg z),
      ← Real.rpow_neg (norm_nonneg z)] at h
    calc
      _ ≤ ‖z‖ ^ (-(1 / 2 : ℝ)) / (1 / 2) := h
      _ = _ := by ring
  have hpow : 0 ≤ ‖z‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg z) _
  have hbound : |Real.log ‖z‖| ≤ 2 * ‖z‖ ^ (-(1 / 2 : ℝ)) + ‖z‖ :=
    abs_le.2 ⟨by linarith [norm_nonneg z], by linarith⟩
  simpa [rieszKernel, abs_neg] using hbound

theorem logarithmic_Kop_L2_L3 (hd : 2 ≤ d)
    (rho : Euc d → ℝ) (hrho : HRS.Whole.IsProbDensity rho) (M : ℝ)
    (hM : ∀ x, rho x ≤ M)
    (hnorm3 : MemLp (fun x : Euc d => ‖x‖) 3 (HRS.Whole.withDensityReal rho)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ,
      MemLp f 2 (HRS.Whole.withDensityReal rho) →
      MemLp (HRS.Whole.Kop (rieszKernel d 0) (HRS.Whole.withDensityReal rho) f) 3 (HRS.Whole.withDensityReal rho) ∧
      eLpNorm (HRS.Whole.Kop (rieszKernel d 0) (HRS.Whole.withDensityReal rho) f) 3 (HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal C * eLpNorm f 2 (HRS.Whole.withDensityReal rho) := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := Q34.isProbabilityMeasure_nu hrho
  have hdim : (1 : ℝ) < d := by exact_mod_cast (show 1 < d from by omega)
  let K : ℝ := Real.sqrt (M * sphereArea d / ((d : ℝ) - 2 * (1 / 2)) + 1)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hnorm2 : MemLp (fun x : Euc d => ‖x‖) 2 mu :=
    hnorm3.mono_exponent (by norm_num)
  let N : ℝ := (eLpNorm (fun x : Euc d => ‖x‖) 2 mu).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hNe : ENNReal.ofReal N = eLpNorm (fun x : Euc d => ‖x‖) 2 mu :=
    ENNReal.ofReal_toReal hnorm2.ne
  let R : Euc d → ℝ := fun x => 2 * K + ‖x‖ + N
  have hR : MemLp R 3 mu := ((memLp_const (2 * K)).add hnorm3).add (memLp_const N)
  have hR0 : ∀ x, 0 ≤ R x := fun x => by dsimp [R]; positivity
  have hmeas : Measurable (Function.uncurry
      (fun x y : Euc d => rieszKernel d 0 (x - y))) := by
    simp only [rieszKernel, if_pos rfl]
    exact ((measurable_fst.sub measurable_snd).norm.log).neg
  have hrow : ∀ x : Euc d,
      MemLp (fun y => rieszKernel d 0 (x - y)) 2 mu ∧
      eLpNorm (fun y => rieszKernel d 0 (x - y)) 2 mu ≤ ENNReal.ofReal (R x) := by
    intro x
    let k : Euc d → ℝ := fun y => rieszKernel d (1 / 2) (x - y)
    have hk := r26t6c_riesz_row_L2 hd (1 / 2) M (by norm_num)
      (by simpa using hdim) rho hrho hM x
    let G : Euc d → ℝ := fun y => 2 * k y + ‖x‖ + ‖y‖
    have hG : MemLp G 2 mu :=
      ((hk.1.const_mul 2).add (memLp_const ‖x‖)).add hnorm2
    have hm : AEStronglyMeasurable (fun y => rieszKernel d 0 (x - y)) mu :=
      (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hpoint : ∀ y, ‖rieszKernel d 0 (x - y)‖ ≤ G y := by
      intro y
      rw [Real.norm_eq_abs]
      have hz := logarithmic_kernel_bound (x - y)
      have hxy := norm_sub_le x y
      dsimp only [G, k]
      linarith
    have hmem : MemLp (fun y => rieszKernel d 0 (x - y)) 2 mu :=
      hG.mono' hm (ae_of_all _ hpoint)
    have hscale : eLpNorm (fun y => 2 * k y) 2 mu = 2 * eLpNorm k 2 mu := by
      change eLpNorm ((2 : ℝ) • k) 2 mu = _
      rw [eLpNorm_const_smul]
      norm_num [Real.enorm_eq_ofReal_abs]
    have hconst : eLpNorm (fun _ : Euc d => ‖x‖) 2 mu = ENNReal.ofReal ‖x‖ := by
      rw [eLpNorm_const' ‖x‖ (by norm_num) (by norm_num)]
      simp [Real.enorm_eq_ofReal_abs]
    have hsum_inner : eLpNorm (fun y : Euc d => 2 * k y + ‖x‖) 2 mu ≤
        eLpNorm (fun y : Euc d => 2 * k y) 2 mu +
          eLpNorm (fun _ : Euc d => ‖x‖) 2 mu := by
      exact eLpNorm_add_le (f := fun y : Euc d => 2 * k y)
        (g := fun _ : Euc d => ‖x‖) (μ := mu) (by norm_num)
    have hsum_outer : eLpNorm G 2 mu ≤
        eLpNorm (fun y : Euc d => 2 * k y + ‖x‖) 2 mu +
          eLpNorm (fun y : Euc d => ‖y‖) 2 mu := by
      exact eLpNorm_add_le (f := fun y : Euc d => 2 * k y + ‖x‖)
        (g := fun y : Euc d => ‖y‖) (μ := mu) (by norm_num)
    have hb : eLpNorm G 2 mu ≤ ENNReal.ofReal (R x) := by
      calc
        _ ≤ eLpNorm (fun y : Euc d => 2 * k y + ‖x‖) 2 mu +
            eLpNorm (fun y : Euc d => ‖y‖) 2 mu := hsum_outer
        _ ≤ (eLpNorm (fun y => 2 * k y) 2 mu + eLpNorm (fun _ : Euc d => ‖x‖) 2 mu) +
            eLpNorm (fun y : Euc d => ‖y‖) 2 mu :=
          add_le_add hsum_inner le_rfl
        _ = 2 * eLpNorm k 2 mu + ENNReal.ofReal ‖x‖ + ENNReal.ofReal N := by
          exact congrArg₂ (fun a b : ℝ≥0∞ => a + b)
            (congrArg₂ (fun a b : ℝ≥0∞ => a + b) hscale hconst) hNe.symm
        _ ≤ 2 * ENNReal.ofReal K + ENNReal.ofReal ‖x‖ + ENNReal.ofReal N := by
          gcongr
          exact hk.2
        _ = ENNReal.ofReal (R x) := by
          dsimp only [R]
          rw [ENNReal.ofReal_add (by positivity) hN,
            ENNReal.ofReal_add (by positivity) (norm_nonneg x),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    exact ⟨hmem, (eLpNorm_mono_ae_real hm (ae_of_all _ hpoint)).trans hb⟩
  let L : ℝ := (eLpNorm R 3 mu).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hLe : ENNReal.ofReal L = eLpNorm R 3 mu := ENNReal.ofReal_toReal hR.ne
  refine ⟨2 * L, by positivity, fun f hf => ?_⟩
  have hmap := r26t6c_kernel_L2_L3 mu
    (fun x y => rieszKernel d 0 (x - y)) hmeas R hR hR0 hrow f hf
  let F : Euc d → ℝ := fun x => ∫ y, rieszKernel d 0 (x - y) * f y ∂mu
  have hcenter := r26t6c_centered_L3 mu F hmap.1
  change MemLp (HRS.Whole.projMean mu F) 3 mu ∧
    eLpNorm (HRS.Whole.projMean mu F) 3 mu ≤ ENNReal.ofReal (2 * L) * eLpNorm f 2 mu
  refine ⟨hcenter.1, hcenter.2.trans ?_⟩
  calc
    _ ≤ 2 * (eLpNorm R 3 mu * eLpNorm f 2 mu) := mul_le_mul' le_rfl hmap.2
    _ = _ := by
      rw [← hLe, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat, mul_assoc]

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.logarithmic_Kop_L2_L3
