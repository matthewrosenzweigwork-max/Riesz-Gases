import HRS.MS.R2InterpAux122

/-!
# S10.2 (worker S10S), part 123 (packet M1d): the centred quadratic field `N(pairEnergy h - E pairEnergy h)` as a functional of the kernel

For kernels dominated by `B g` (`g` the polynomial envelope): additivity, homogeneity and the bound `|field| ≤ N B (Env + E Env)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

/-- Measurable kernel with integrable rows and integrable row integrals. -/
structure S102RowOK (μ : Measure (Euc d)) (h : Euc d → Euc d → ℝ) : Prop where
  meas : Measurable fun p : Euc d × Euc d => h p.1 p.2
  row : ∀ x, Integrable (h x) μ
  rowint : Integrable (fun x => ∫ y, h x y ∂μ) μ

theorem s102_rowOK_of_bound {μ : Measure (Euc d)} [SFinite μ] {g h : Euc d → Euc d → ℝ} {B : ℝ}
    (hm : Measurable fun p : Euc d × Euc d => h p.1 p.2)
    (hgi : ∀ x, Integrable (g x) μ) (hgH : Integrable (fun x => ∫ y, g x y ∂μ) μ)
    (hh : ∀ x y, |h x y| ≤ B * g x y) : S102RowOK μ h := by
  have hrow : ∀ x, Integrable (h x) μ := fun x => by
    refine Integrable.mono' ((hgi x).const_mul B) (hm.comp measurable_prodMk_left).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hh x y
  refine ⟨hm, hrow, ?_⟩
  refine Integrable.mono' (hgH.const_mul B) (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have := norm_integral_le_of_norm_le ((hgi x).const_mul B)
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hh x y)
  rw [integral_const_mul] at this
  exact this

/-- The centred quadratic field of a kernel along a random configuration `Y`. -/
def s102_fld {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure (Euc d)) (Y : Ω → EucConfig d N)
    (h : Euc d → Euc d → ℝ) (ζ : Ω) : ℝ :=
  N * (pairEnergy h (Y ζ) μ - ∫ ζ', pairEnergy h (Y ζ') μ ∂P)

theorem s102_fld_smul {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure (Euc d))
    (Y : Ω → EucConfig d N) (c : ℝ) (h : Euc d → Euc d → ℝ) (ζ : Ω) :
    s102_fld P μ Y (fun x y => c * h x y) ζ = c * s102_fld P μ Y h ζ := by
  unfold s102_fld
  simp only [HRS.MS.R2Poly.s95_pe_smul, integral_const_mul]
  ring

theorem s102_fld_add {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure (Euc d))
    (Y : Ω → EucConfig d N) {h1 h2 : Euc d → Euc d → ℝ} (H1 : S102RowOK μ h1) (H2 : S102RowOK μ h2)
    (I1 : Integrable (fun ζ => pairEnergy h1 (Y ζ) μ) P) (I2 : Integrable (fun ζ => pairEnergy h2 (Y ζ) μ) P)
    (ζ : Ω) :
    s102_fld P μ Y (fun x y => h1 x y + h2 x y) ζ = s102_fld P μ Y h1 ζ + s102_fld P μ Y h2 ζ := by
  unfold s102_fld
  simp only [HRS.MS.R2Poly.s95_pe_add H1.row H2.row H1.rowint H2.rowint]
  rw [integral_add I1 I2]
  ring

theorem s102_fld_bound {μ : Measure (Euc d)} [SFinite μ] {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → EucConfig d N) (hY : Measurable Y) {g h : Euc d → Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hgm : Measurable fun p : Euc d × Euc d => g p.1 p.2) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) μ) (hgH : Integrable (fun x => ∫ y, g x y ∂μ) μ)
    (hm : Measurable fun p : Euc d × Euc d => h p.1 p.2) (hh : ∀ x y, |h x y| ≤ B * g x y)
    (hEi : Integrable (fun ζ => s102_Env g (Y ζ) μ) P) :
    Integrable (fun ζ => pairEnergy h (Y ζ) μ) P ∧
      |∫ ζ, pairEnergy h (Y ζ) μ ∂P| ≤ B * ∫ ζ, s102_Env g (Y ζ) μ ∂P ∧
      ∀ ζ, |s102_fld P μ Y h ζ| ≤ N * B * (s102_Env g (Y ζ) μ + ∫ ζ', s102_Env g (Y ζ') μ ∂P) := by
  have hpt : ∀ ζ, ‖pairEnergy h (Y ζ) μ‖ ≤ B * s102_Env g (Y ζ) μ := fun ζ => by
    rw [Real.norm_eq_abs]; exact s102_pE_abs_le_Env hB hg0 hgi hgH hh _
  have hint : Integrable (fun ζ => pairEnergy h (Y ζ) μ) P :=
    Integrable.mono' (hEi.const_mul B) ((HRS.MS.Wr.wr9_measurable_pairEnergy hm).comp hY).aestronglyMeasurable
      (Eventually.of_forall hpt)
  have hint2 : |∫ ζ, pairEnergy h (Y ζ) μ ∂P| ≤ B * ∫ ζ, s102_Env g (Y ζ) μ ∂P := by
    have := norm_integral_le_of_norm_le (hEi.const_mul B) (Eventually.of_forall hpt)
    rw [integral_const_mul] at this
    simpa [Real.norm_eq_abs] using this
  refine ⟨hint, hint2, fun ζ => ?_⟩
  have h1 := s102_pE_abs_le_Env hB hg0 hgi hgH hh (Y ζ)
  unfold s102_fld
  rw [abs_mul, Nat.abs_cast]
  have h3 : |pairEnergy h (Y ζ) μ - ∫ ζ', pairEnergy h (Y ζ') μ ∂P| ≤
      B * (s102_Env g (Y ζ) μ + ∫ ζ', s102_Env g (Y ζ') μ ∂P) :=
    (abs_sub _ _).trans (by linarith)
  calc (N : ℝ) * |pairEnergy h (Y ζ) μ - ∫ ζ', pairEnergy h (Y ζ') μ ∂P|
      ≤ N * (B * (s102_Env g (Y ζ) μ + ∫ ζ', s102_Env g (Y ζ') μ ∂P)) :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg N)
    _ = _ := by ring

end HRS.MS.R2Interp

end
