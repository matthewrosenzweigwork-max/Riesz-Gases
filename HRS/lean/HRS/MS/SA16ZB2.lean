import HRS.MS.SA16ZB1

/-!
# S.A.16 (SA16Z) B2: `‖P_a ψ‖_p ≤ C (B_a + L_a) ∑_i (‖∂_iψ‖_p + ∑_l ‖∂_l∂_iψ‖_p)` (`1 < θ < 2`)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section B2
variable {d : ℕ} {s : ℝ}

lemma sa16z_eLpNorm_le_mul {F g : Euc d → ℝ} (hF : AEStronglyMeasurable F volume) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, ‖F y‖ ≤ c * ‖g y‖) (q : ℝ≥0∞) : eLpNorm F q volume ≤ ENNReal.ofReal c * eLpNorm g q volume := by
  calc eLpNorm F q volume ≤ eLpNorm (c • g) q volume := by
        refine eLpNorm_mono hF fun y => ?_
        calc ‖F y‖ ≤ c * ‖g y‖ := h y
          _ = ‖(c • g) y‖ := by simp [norm_smul, abs_of_nonneg hc]
    _ = ENNReal.ofReal c * eLpNorm g q volume := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]

theorem sa16z_P_Lp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a ψ : Euc d → ℝ}, ContDiff ℝ ∞ a → IsCcInfty ψ → ∀ {Ba La : ℝ}, 0 ≤ Ba → 0 ≤ La →
      (∀ y, |a y| ≤ Ba) → (∀ y, ‖fderiv ℝ a y‖ ≤ La) →
      eLpNorm (sa16z_P s a ψ) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (C * (Ba + La)) *
        ∑ i : Fin d, (eLpNorm (fun y => fderiv ℝ ψ y (sa16z_e i)) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => ‖fderiv ℝ (fun z => fderiv ℝ ψ z (sa16z_e i)) y‖) (ENNReal.ofReal p) volume) := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have : (1 : ℝ) ≤ p := hp.le
    simpa using ENNReal.ofReal_le_ofReal this
  have hch : ∀ i : Fin d, ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ f : Euc d → ℝ, IsCcInfty f →
      eLpNorm (pvOdd d (s + 2 - d) (fun u : Euc d => u i) f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal Ci * (eLpNorm f (ENNReal.ofReal p) volume +
          eLpNorm (fun x => ‖fderiv ℝ f x‖) (ENNReal.ofReal p) volume) :=
    fun i => sa16z_pv_W1p hd hθ1 hθ2 hp i
  choose Ci hCi0 hCi using hch
  have hc0 := HRS.CZ.Hls.hlsg_c_nonneg hs0
  set Cm : ℝ := ∑ i, Ci i with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun i _ => hCi0 i
  refine ⟨HRS.CZ.Hls.hlsg_c s * Cm, mul_nonneg hc0 hCm0, fun {a ψ} ha hψ {Ba La} hBa hLa hab hLa' => ?_⟩
  set G : Fin d → ℝ≥0∞ := fun i => eLpNorm (fun y => fderiv ℝ ψ y (sa16z_e i)) (ENNReal.ofReal p) volume with hG
  set H : Fin d → ℝ≥0∞ := fun i => eLpNorm (fun y => ‖fderiv ℝ (fun z => fderiv ℝ ψ z (sa16z_e i)) y‖)
    (ENNReal.ofReal p) volume with hH
  have hPeq : sa16z_P s a ψ = (-(HRS.CZ.Hls.hlsg_c s)) • ∑ i : Fin d,
      pvOdd d (s + 2 - d) (fun u : Euc d => u i) (sa16z_src a ψ i) := by
    funext x
    rw [sa16z_P_pv hd hs0 hsd ha hψ x]
    simp [Finset.sum_apply]
  have hper : ∀ i : Fin d, eLpNorm (pvOdd d (s + 2 - d) (fun u : Euc d => u i) (sa16z_src a ψ i))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal Cm * ENNReal.ofReal (Ba + La) * (G i + H i) := by
    intro i
    have hf := sa16z_src_cc ha hψ i
    have hg1 : Continuous (fun y => fderiv ℝ ψ y (sa16z_e i)) := (sa16so_dir_smooth hψ.1 _).continuous
    have hg2 : Continuous (fun y => ‖fderiv ℝ (fun z => fderiv ℝ ψ z (sa16z_e i)) y‖) :=
      ((sa16so_dir_smooth hψ.1 (sa16z_e i)).continuous_fderiv (by simp)).norm
    have e1 : eLpNorm (sa16z_src a ψ i) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal Ba * G i := by
      refine sa16z_eLpNorm_le_mul hf.1.continuous.aestronglyMeasurable hBa (fun y => ?_) _
      show ‖a y * fderiv ℝ ψ y (sa16z_e i)‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hab y) (norm_nonneg _)
    have e2 : eLpNorm (fun x => ‖fderiv ℝ (sa16z_src a ψ i) x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal La * G i + ENNReal.ofReal Ba * H i := by
      have hm : AEStronglyMeasurable (fun x => ‖fderiv ℝ (sa16z_src a ψ i) x‖) volume :=
        (hf.1.continuous_fderiv (by simp)).norm.aestronglyMeasurable
      have hle : eLpNorm (fun x => ‖fderiv ℝ (sa16z_src a ψ i) x‖) (ENNReal.ofReal p) volume ≤
          eLpNorm ((fun y => La * ‖fderiv ℝ ψ y (sa16z_e i)‖) +
            fun y => Ba * ‖fderiv ℝ (fun z => fderiv ℝ ψ z (sa16z_e i)) y‖) (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono hm fun y => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (mul_nonneg hLa (norm_nonneg _)) (mul_nonneg hBa (norm_nonneg _)))]
        exact sa16z_fderiv_src_bound ha hψ hab hLa' i y
      refine hle.trans ((eLpNorm_add_le hp1).trans (add_le_add ?_ ?_))
      · refine sa16z_eLpNorm_le_mul (continuous_const.mul hg1.norm).aestronglyMeasurable hLa (fun y => ?_) _
        simp [abs_of_nonneg hLa]
      · refine sa16z_eLpNorm_le_mul (continuous_const.mul hg2).aestronglyMeasurable hBa (fun y => ?_) _
        simp [abs_of_nonneg hBa]
    have h1 := hCi i _ hf
    have hBL : ENNReal.ofReal Ba ≤ ENNReal.ofReal (Ba + La) := ENNReal.ofReal_le_ofReal (by linarith)
    have hLB : ENNReal.ofReal La ≤ ENNReal.ofReal (Ba + La) := ENNReal.ofReal_le_ofReal (by linarith)
    have hCle : ENNReal.ofReal (Ci i) ≤ ENNReal.ofReal Cm := by
      refine ENNReal.ofReal_le_ofReal ?_
      exact Finset.single_le_sum (f := Ci) (fun j _ => hCi0 j) (Finset.mem_univ i)
    calc _ ≤ ENNReal.ofReal (Ci i) * (eLpNorm (sa16z_src a ψ i) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => ‖fderiv ℝ (sa16z_src a ψ i) x‖) (ENNReal.ofReal p) volume) := h1
      _ ≤ ENNReal.ofReal Cm * ((ENNReal.ofReal Ba * G i) + (ENNReal.ofReal La * G i + ENNReal.ofReal Ba * H i)) := by
          gcongr
      _ ≤ ENNReal.ofReal Cm * (ENNReal.ofReal (Ba + La) * (G i + H i)) := by
          gcongr
          have e : ENNReal.ofReal Ba * G i + (ENNReal.ofReal La * G i + ENNReal.ofReal Ba * H i) =
              (ENNReal.ofReal Ba + ENNReal.ofReal La) * G i + ENNReal.ofReal Ba * H i := by ring
          rw [e, ← ENNReal.ofReal_add hBa hLa, mul_add]
          gcongr
      _ = _ := by ring
  rw [hPeq]
  refine (eLpNorm_const_smul_le).trans ?_
  rw [Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg hc0]
  have hsum := (eLpNorm_sum_le (f := fun i => pvOdd d (s + 2 - d) (fun u : Euc d => u i) (sa16z_src a ψ i))
    (s := Finset.univ) (μ := (volume : Measure (Euc d))) hp1).trans (Finset.sum_le_sum fun i _ => hper i)
  calc ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * eLpNorm (∑ i, pvOdd d (s + 2 - d) (fun u : Euc d => u i)
        (sa16z_src a ψ i)) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * ∑ i : Fin d,
          ENNReal.ofReal Cm * ENNReal.ofReal (Ba + La) * (G i + H i) := by gcongr
    _ = ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s * Cm * (Ba + La)) * ∑ i : Fin d, (G i + H i) := by
        rw [← Finset.mul_sum, ← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hc0 hCm0), ENNReal.ofReal_mul hc0]
        ring

end B2

end HRS.Whole.AppendixA.Phase2SA16R
