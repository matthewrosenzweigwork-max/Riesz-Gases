import HRS.MS.R26T8AP16d1
import HRS.MS.R26T8AA01j

/-!
# S8.2 T8A P16d2: Fubini domination
For `G` conormal of order `σ < d` (degree 0 in the jets, weight `M`) and a compactly supported continuous `W`:
`(x,y) ↦ W(x) ρ(y) G(x,y)` is integrable on `ℝ^d × ℝ^d` (thermal `ρ`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_comm_dom (hd : 2 ≤ d) (b : ℕ) (a beta M sigma A : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hsd : sigma < d) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (hA : 0 ≤ A) {G : Euc d → Euc d → ℝ}
    (hG : Conormal 0 b M sigma A G) {W : Euc d → ℝ} (hW : Continuous W) (hWc : HasCompactSupport W) :
    Integrable (fun p : Euc d × Euc d => W p.1 * (rho p.2 * G p.1 p.2)) (volume.prod volume) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hbeta
      hrho).1
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hrho0 : ∀ x, 0 ≤ rho x := hprob.nonneg
  have hρc : Continuous rho := hρs.continuous
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M hc
  set a' : Euc d → ℝ := fun y => rho y * jbracket y ^ M with ha'
  have ha'0 : ∀ y, 0 ≤ a' y := fun y => mul_nonneg (hrho0 y) (Real.rpow_nonneg (s83_jb_pos y).le _)
  have ha'c : Continuous a' := hρc.mul (s85_jb_rpow_continuous M)
  have ha'b : ∀ y, a' y ≤ C * Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
    intro y
    have h1 : jbracket y ^ M ≤ (1 + ‖y‖) ^ M :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM
    have h2 := hCp ‖y‖ (norm_nonneg _)
    have h3 : rho y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := (le_abs_self _).trans (hb y).1
    calc a' y = rho y * jbracket y ^ M := rfl
      _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (1 + ‖y‖) ^ M :=
          mul_le_mul h3 h1 (Real.rpow_nonneg (s83_jb_pos y).le _) (by positivity)
      _ = C * ((1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ C * (Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h2 hC
      _ = _ := by ring
  have hKa : ∀ y, a' y ≤ C * Cp := fun y => by
    refine (ha'b y).trans ?_
    have : Real.exp (-(c / 2) * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
    have h0 : 0 ≤ C * Cp := by positivity
    nlinarith
  have ha'i : Integrable a' := by
    refine Integrable.mono' ((r26t8a_p10a_gauss_int (d := d) (b := c / 2) (by linarith)).const_mul (C * Cp))
      ha'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (ha'0 y)]; exact ha'b y
  obtain ⟨sp, hsp⟩ : ∃ sp : ℝ, sp = max sigma 0 := ⟨_, rfl⟩
  have hsp0 : 0 ≤ sp := by rw [hsp]; exact le_max_right _ _
  have hspd : sp < d := by rw [hsp]; exact max_lt hsd (by linarith)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (sp + d) / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd2 : s < d := by rw [hs]; linarith
  have hσsp : sigma ≤ sp := by rw [hsp]; exact le_max_left _ _
  have hσs : sigma < s := by rw [hs]; linarith
  obtain ⟨Cq, hCq0, hCq⟩ := r26t8a_f25_pt_bound (d := d) b hσs hs0
  have hoffm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hres : (volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2} =
      volume.prod volume := Measure.restrict_eq_self_of_ae_mem (r26t8a_g11_diag_null hd)
  have hae2 : ∀ᵐ p : Euc d × Euc d ∂(volume.prod volume), p.1 ≠ p.2 := r26t8a_g11_diag_null hd
  have hGm : AEStronglyMeasurable (fun p : Euc d × Euc d => G p.1 p.2) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (Function.uncurry G)
        ((volume.prod volume : Measure (Euc d × Euc d)).restrict {p : Euc d × Euc d | p.1 ≠ p.2}) :=
      hG.1.continuousOn.aestronglyMeasurable hoffm
    rw [hres] at h1
    exact h1
  set W1 : Euc d → ℝ := fun x => A * Cq * (W x * jbracket x ^ M) with hW1
  have hW1c : Continuous W1 := continuous_const.mul (hW.mul (s85_jb_rpow_continuous M))
  have hW1s : HasCompactSupport W1 := (hWc.mul_right (f' := fun x => jbracket x ^ M)).mul_left
  have hW1i : Integrable W1 := hW1c.integrable_of_hasCompactSupport hW1s
  have hdom := (r26t8a_g3_prod_int hd hs0 hsd2 ha'0 hKa ha'c ha'i hW1i).1
  refine Integrable.mono' hdom ?_ ?_
  · exact (hW.comp continuous_fst).aestronglyMeasurable.mul
      (((hρc.comp continuous_snd).aestronglyMeasurable).mul hGm)
  · filter_upwards [hae2] with p hp
    have hpt := hCq hA hG p.1 p.2 hp
    have hr0 : 0 ≤ 1 + ‖p.1 - p.2‖ ^ (-s) := by
      have := Real.rpow_nonneg (norm_nonneg (p.1 - p.2)) (-s); linarith
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hrho0 p.2)]
    have hWabs : |W1 p.1| = A * Cq * (jbracket p.1 ^ M * |W p.1|) := by
      rw [hW1]; simp only
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ A * Cq), abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos p.1).le _)]
      ring
    rw [hWabs]
    have hpw : HRS.MS.Phase2S82.pairWeight M p.1 p.2 = jbracket p.1 ^ M * jbracket p.2 ^ M := rfl
    rw [hpw] at hpt
    calc |W p.1| * (rho p.2 * |G p.1 p.2|)
        ≤ |W p.1| * (rho p.2 * (A * Cq * (jbracket p.1 ^ M * jbracket p.2 ^ M) * (1 + ‖p.1 - p.2‖ ^ (-s)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpt (hrho0 _)) (abs_nonneg _)
      _ = _ := by rw [ha']; ring

end HRS.MS.R26T8A
