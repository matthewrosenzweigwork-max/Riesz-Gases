import HRS.MP.SelfSimP4MolH2

/-!
# MPP4MOL stage 5c (16): Fatou in `x` and in `s`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_fatou_chain {D : ℝ → EucConfig d N → ℝ} (hDc : Continuous (Function.uncurry D))
    (hnn : ∀ s x, 0 ≤ D s x) {χ : ℕ → EucConfig d N → ℝ} (hχc : ∀ n, Continuous (χ n))
    (hχs : ∀ n, HasCompactSupport (χ n)) (hχ0 : ∀ n x, 0 ≤ χ n x)
    (hlim : ∀ x, ∀ᶠ n in atTop, χ n x = 1) (t : ℝ) {a : ℕ → ℝ} {Lr : ℝ}
    (ha : Tendsto a atTop (𝓝 Lr))
    (hbound : ∀ n, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ n x * D s x ≤ a n) :
    ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ x, ENNReal.ofReal (D s x) ≤ ENNReal.ofReal Lr := by
  -- the cut-off integrals
  have hDn : ∀ n, Continuous (fun s => ∫ x, χ n x * D s x) := fun n =>
    p4m_cont_param_cs (f := fun s x => χ n x * D s x)
      ((hχc n).comp continuous_snd |>.mul hDc) (hχs n) (fun s x hx => by simp [hx])
  have hint : ∀ n s, Integrable (fun x => χ n x * D s x) volume := fun n s =>
    p4m_int_of_supp ((hχc n).mul (hDc.comp (Continuous.prodMk continuous_const continuous_id))) (hχs n)
      (fun x hx => by simp [hx])
  have hDn0 : ∀ n s, 0 ≤ ∫ x, χ n x * D s x := fun n s =>
    integral_nonneg fun x => mul_nonneg (hχ0 n x) (hnn s x)
  -- Fatou in `x`
  have hx : ∀ s, ∫⁻ x, ENNReal.ofReal (D s x) ≤
      liminf (fun n => ENNReal.ofReal (∫ x, χ n x * D s x)) atTop := by
    intro s
    have hm : ∀ n, Measurable (fun x => ENNReal.ofReal (χ n x * D s x)) := fun n =>
      ENNReal.measurable_ofReal.comp
        ((hχc n).mul (hDc.comp (Continuous.prodMk continuous_const continuous_id))).measurable
    have hl := lintegral_liminf_le (u := atTop) (μ := (volume : Measure (EucConfig d N))) hm
    have e1 : ∀ x, liminf (fun n => ENNReal.ofReal (χ n x * D s x)) atTop = ENNReal.ofReal (D s x) := by
      intro x
      have : Tendsto (fun n : ℕ => ENNReal.ofReal (χ n x * D s x)) atTop
          (𝓝 (ENNReal.ofReal (D s x))) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hlim x] with n hn
        rw [hn, one_mul]
      exact this.liminf_eq
    have e2 : ∀ n, ENNReal.ofReal (∫ x, χ n x * D s x) = ∫⁻ x, ENNReal.ofReal (χ n x * D s x) := fun n =>
      ofReal_integral_eq_lintegral_ofReal (hint n s)
        (Filter.Eventually.of_forall fun x => mul_nonneg (hχ0 n x) (hnn s x))
    simp only [e1] at hl
    simp only [e2]
    exact hl
  -- Fatou in `s`
  have hm2 : ∀ n, Measurable (fun s => ENNReal.ofReal (∫ x, χ n x * D s x)) := fun n =>
    ENNReal.measurable_ofReal.comp (hDn n).measurable
  have hs := lintegral_liminf_le (u := atTop) (μ := volume.restrict (Set.Icc (0 : ℝ) t)) hm2
  have e3 : ∀ n, ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (∫ x, χ n x * D s x) =
      ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ n x * D s x) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal ((hDn n).integrableOn_Icc (μ := volume))
      (Filter.Eventually.of_forall fun s => hDn0 n s)).symm
  simp only [e3] at hs
  calc ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ x, ENNReal.ofReal (D s x)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, liminf (fun n => ENNReal.ofReal (∫ x, χ n x * D s x)) atTop :=
        lintegral_mono fun s => hx s
    _ ≤ liminf (fun n => ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ n x * D s x)) atTop := hs
    _ ≤ liminf (fun n => ENNReal.ofReal (a n)) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hbound n))
    _ = ENNReal.ofReal Lr := (ENNReal.tendsto_ofReal ha).liminf_eq

end HRS.MP.SelfSimP4Mol
