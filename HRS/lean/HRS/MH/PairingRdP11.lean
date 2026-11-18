import HRS.MH.PairingRdP9
import HRS.Whole.Q09AAux2
import HRS.MH.DualityRdC1a

/-!
# PairingRd packet PR11 (`pairKernelRdB_integrable_prod_rd`): integrability of the kernel on `ν ⊗ μ`

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route: the Euclidean copy of the torus proof
(`HRS.Duality.pairKernelB_integrable_prod`, `HRS/Duality/PairingExpansion.lean:429`). Fibres: `|K(x,·)| ≤ Kc (db1G(x-·) + 1)` (PR9),
the density bound `ρ ≤ B` (`integrable_withDensityReal_of`, Euclidean copy), and the constant `1` integrable against the
probability measure `μ`. Uniform fibre bound: `db1_rho_kernel_le`. Joint measurability: PR10a. The product integrability is
`integrable_prod_iff` (copy of `integrable_prod_of_bound`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- Integrability on `ν ⊗ μ` from fibrewise integrability and a uniform fibrewise bound (Euclidean copy). -/
theorem pr11_integrable_prod_of_bound {ν μ : Measure (Euc d)} [IsFiniteMeasure ν] [SFinite μ]
    {F : Euc d × Euc d → ℝ} (hF : Measurable F)
    (hx : ∀ x, Integrable (fun y => F (x, y)) μ) {M : ℝ}
    (hM : ∀ x, ∫ y, ‖F (x, y)‖ ∂μ ≤ M) : Integrable F (ν.prod μ) := by
  rw [integrable_prod_iff hF.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => hx x, ?_⟩
  refine Integrable.of_bound ?_ M (Filter.Eventually.of_forall fun x => ?_)
  · exact (hF.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    exact hM x

/-- Euclidean copy of `withDensityReal_le_smul`: a bounded density is dominated by a multiple of Lebesgue measure. -/
theorem pr11_withDensityReal_le_smul {ρ : Euc d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) :
    Whole.withDensityReal ρ ≤ ENNReal.ofReal B • (volume : Measure (Euc d)) := by
  refine Measure.le_iff'.2 fun A => ?_
  unfold Whole.withDensityReal
  rw [withDensity_apply', Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ a in A, ENNReal.ofReal (ρ a) ≤ ∫⁻ _ in A, ENNReal.ofReal B :=
        lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hB a)
    _ = ENNReal.ofReal B * volume A := setLIntegral_const _ _

/-- Euclidean copy of `integrable_withDensityReal_of`. -/
theorem pr11_integrable_withDensityReal_of {ρ : Euc d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B)
    {g : Euc d → ℝ} (hg : Integrable g volume) :
    Integrable g (Whole.withDensityReal ρ) :=
  (hg.smul_measure ENNReal.ofReal_ne_top).mono_measure (pr11_withDensityReal_le_smul hB)

/-- **PR11** `pairKernelRdB_integrable_prod_rd` (proof). -/
theorem pairKernelRdB_integrable_prod_rd (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B) (ν : Measure (Euc d)) [IsFiniteMeasure ν] :
    Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) (ν.prod (Whole.withDensityReal ρ)) := by
  haveI := Whole.Q09A.measure_isProb hρ
  obtain ⟨Kc, hKc0, hK⟩ := pairKernelRdB_bound_rd hs0 M hf
  have hK' : ∀ x y : Euc d, ‖pairKernelRdB f M s x y‖ ≤
      Kc * (HRS.MH.DualityRd.db1G s (x - y) + 1) := fun x y => by
    rw [Real.norm_eq_abs]
    exact hK x y
  have hmeas := pairKernelRdB_measurable_rd (s := s) M hf.1
  have hBint : Integrable (HRS.MH.DualityRd.db1G (d := d) s) := HRS.MH.DualityRd.db1G_integrable hd hsd
  have hmG : ∀ x : Euc d, Measurable (fun y => HRS.MH.DualityRd.db1G (d := d) s (x - y)) := fun x =>
    (HRS.MH.DualityRd.db1_measurable_G s).comp (measurable_const.sub measurable_id)
  -- the dominating function of the fibre, integrable for the probability measure `μ`
  have hdom : ∀ x : Euc d, Integrable (fun y => Kc * HRS.MH.DualityRd.db1G (d := d) s (x - y) + Kc)
      (Whole.withDensityReal ρ) := fun x =>
    ((pr11_integrable_withDensityReal_of hB (hBint.comp_sub_left x)).const_mul Kc).add (integrable_const Kc)
  have hx : ∀ x : Euc d, Integrable (fun y => pairKernelRdB f M s x y) (Whole.withDensityReal ρ) := by
    intro x
    refine Integrable.mono' (hdom x) (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    show ‖pairKernelRdB f M s x y‖ ≤ Kc * HRS.MH.DualityRd.db1G (d := d) s (x - y) + Kc
    exact (hK' x y).trans (le_of_eq (by ring))
  have hM : ∀ x : Euc d, ∫ y, ‖pairKernelRdB f M s x y‖ ∂(Whole.withDensityReal ρ)
      ≤ Kc * (B * ∫ z, HRS.MH.DualityRd.db1G (d := d) s z) + Kc := by
    intro x
    have hgI : Integrable (fun y => Kc * HRS.MH.DualityRd.db1G (d := d) s (x - y))
        (Whole.withDensityReal ρ) :=
      (pr11_integrable_withDensityReal_of hB (hBint.comp_sub_left x)).const_mul Kc
    calc ∫ y, ‖pairKernelRdB f M s x y‖ ∂(Whole.withDensityReal ρ)
        ≤ ∫ y, (Kc * HRS.MH.DualityRd.db1G (d := d) s (x - y) + Kc) ∂(Whole.withDensityReal ρ) :=
          integral_mono (hx x).norm (hdom x) fun y => by
            show ‖pairKernelRdB f M s x y‖ ≤ Kc * HRS.MH.DualityRd.db1G (d := d) s (x - y) + Kc
            exact (hK' x y).trans (le_of_eq (by ring))
      _ = Kc * ∫ y, HRS.MH.DualityRd.db1G (d := d) s (x - y) ∂(Whole.withDensityReal ρ) + Kc := by
          rw [integral_add hgI (integrable_const Kc), integral_const_mul, integral_const]
          simp
      _ ≤ Kc * (B * ∫ z, HRS.MH.DualityRd.db1G (d := d) s z) + Kc := by
          have h1 : ∫ y, HRS.MH.DualityRd.db1G (d := d) s (x - y) ∂(Whole.withDensityReal ρ)
              ≤ B * ∫ z, HRS.MH.DualityRd.db1G (d := d) s z := by
            rw [HRS.MH.DualityRd.dc1a_integral_withDensity hρ.measurable hρ.nonneg
              (fun y => HRS.MH.DualityRd.db1G (d := d) s (x - y))]
            exact HRS.MH.DualityRd.db1_rho_kernel_le hρ hB s x hBint
          linarith [mul_le_mul_of_nonneg_left h1 hKc0]
  exact pr11_integrable_prod_of_bound hmeas hx hM

end HRS.MH.PairingRdP
