import HRS.MS.Fp81S21GaussG4U7

/-! Centered per-time control for the initial G4 Duhamel integrand. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The centered initial increment appearing in the proposed U7 contract. -/
def fp81s21_g4_initialValue {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (f : Euc p.d → ℝ) (v w : ℝ) : ℝ :=
  ∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ)
    (fun y => r26t3_U R 0 w f y - r26t3_U R 0 v f y) x)^2
      ∂HRS.Whole.withDensityReal R.ρβ

/-- Exact proposition header for the proposed U7 theorem, recorded while the
centered time-integral passage remains to be proved. -/
def fp81s21_g4_initial_combo_target (p : Parameters) : Prop :=
  fp81s21_g4Phys p (fun _ R =>
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
        ∀ v w, 0 ≤ v → v ≤ w →
          fp81s21_g4_initialValue R f v w ≤
            A * (w-v)^2 * fp81s21_g4_J p.d f)

/-- The centered propagated generator is uniformly controlled at each positive
terminal time by the same G4 cost. -/
theorem fp81s21_g4_initial_integrand_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ q : ℝ, 0 < q → ∀ f : Euc p.d → ℝ,
        IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
        (∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ)
          (r26t3_U R 0 q (generatorW (r26t3_coeff R) q f)) x)^2
            ∂HRS.Whole.withDensityReal R.ρβ) ≤ B * fp81s21_g4_J p.d f := by
  obtain ⟨δg, hδg, hδghalf, hgen⟩ := fp81s21_g4_generator_combo_cost p
  obtain ⟨δe, Q, Cdec, cdec, hδe, hδehalf, hQ, hQδ, hCdec, hcdec, henergy⟩ :=
    sol13_uniform_adjoint_energy p
  obtain ⟨δc, Co, co, hδc, hδchalf, hco, hcommon⟩ := fp81s21_common_radius p
  let δ0 : ℝ := min δg (min δe δc)
  have hδ0 : 0 < δ0 := lt_min hδg (lt_min hδe hδc)
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left δg (min δe δc)).trans hδghalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδgle : δ ≤ δg := hδle.trans (min_le_left δg (min δe δc))
  have hδele : δ ≤ δe := hδle.trans
    ((min_le_right δg (min δe δc)).trans (min_le_left δe δc))
  have hδcle : δ ≤ δc := hδle.trans
    ((min_le_right δg (min δe δc)).trans (min_le_right δe δc))
  obtain ⟨A, hA, hgenR⟩ := hgen δ hδ hδgle R
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ hδcle R.ρβ R.thermal
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμstar : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμstar
  refine ⟨A * Cdec, mul_nonneg hA hCdec.le, ?_⟩
  intro q hq f hf
  have hq0 : 0 ≤ q := hq.le
  obtain ⟨hgenLp, hgenSq⟩ := hgenR q hq0 f hf
  rcases hf with ⟨S, coeff, rfl⟩
  let g : Euc p.d → ℝ := generatorW (r26t3_coeff R) q
    (fun x => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α x)
  have hcombo := fp81s21_g4_generator_combo p R hterm
    (r := 0) (q := q) le_rfl hq0 S coeff
  obtain ⟨u, hu⟩ := hcombo.2.1
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  have huUnique := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting q hq0 ⟨hq0, le_rfl⟩ hu
  have hUeq : r26t3_U R 0 q g = u 0 := by
    simpa [g, r26t3_U, r26t3_coeff] using huUnique 0 ⟨le_rfl, hq0⟩
  obtain ⟨_, _, _, henergyFor⟩ :=
    henergy δ hδ hδele R q hq g u hu
  obtain ⟨_, hdecay⟩ := henergyFor 0 ⟨le_rfl, hq0⟩
  have hdecay' :
      (∫ x, (HRS.Whole.projMean μstar (r26t3_U R 0 q g) x)^2 ∂μstar) ≤
        Cdec * Real.exp (-cdec * q) *
          (∫ x, (HRS.Whole.projMean μstar g x)^2 ∂μstar) := by
    simpa only [hUeq, sub_zero] using hdecay
  have hcenterNonneg : 0 ≤ ∫ x, (HRS.Whole.projMean μstar g x)^2 ∂μstar :=
    integral_nonneg fun x => sq_nonneg _
  have hrawNonneg : 0 ≤ ∫ x, g x^2 ∂μstar :=
    integral_nonneg fun x => sq_nonneg _
  have hprojNorm := HRS.Whole.S71.s71_l2Norm_projMean_le hgenLp
  have hcenterLE :
      (∫ x, (HRS.Whole.projMean μstar g x)^2 ∂μstar) ≤
        (∫ x, g x^2 ∂μstar) := by
    have hnormCenter : 0 ≤ HRS.Whole.l2Norm μstar
        (HRS.Whole.projMean μstar g) := by
      unfold HRS.Whole.l2Norm
      exact Real.sqrt_nonneg _
    have hnormRaw : 0 ≤ HRS.Whole.l2Norm μstar g := by
      unfold HRS.Whole.l2Norm
      exact Real.sqrt_nonneg _
    have hsq := (sq_le_sq₀ hnormCenter hnormRaw).2 hprojNorm
    simpa [HRS.Whole.l2Norm, Real.sq_sqrt hcenterNonneg,
      Real.sq_sqrt hrawNonneg] using hsq
  have hexp : Real.exp (-cdec * q) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_pos hcdec hq]
  have hfactor : Cdec * Real.exp (-cdec * q) ≤ Cdec := by
    calc
      Cdec * Real.exp (-cdec * q) ≤ Cdec * 1 :=
        mul_le_mul_of_nonneg_left hexp hCdec.le
      _ = Cdec := by ring
  calc
    _ ≤ Cdec * Real.exp (-cdec * q) *
        (∫ x, (HRS.Whole.projMean μstar g x)^2 ∂μstar) := by
      simpa [μstar] using hdecay'
    _ ≤ Cdec * (∫ x, (HRS.Whole.projMean μstar g x)^2 ∂μstar) :=
      mul_le_mul_of_nonneg_right hfactor hcenterNonneg
    _ ≤ Cdec * (∫ x, g x^2 ∂μstar) :=
      mul_le_mul_of_nonneg_left hcenterLE hCdec.le
    _ ≤ Cdec * (A * fp81s21_g4_J p.d
        (fun x => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α x)) :=
      mul_le_mul_of_nonneg_left hgenSq hCdec.le
    _ = A * Cdec * fp81s21_g4_J p.d
        (fun x => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α x) := by ring

#print axioms fp81s21_g4_initial_integrand_bound
end HRS.Fp81.S21
