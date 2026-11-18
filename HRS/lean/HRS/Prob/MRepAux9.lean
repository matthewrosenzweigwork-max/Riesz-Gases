import HRS.Prob.MRepAux8

/-!
# MREP, part 9: the abstract representation theorem

For `ARData`, the Brownian coordinates `Bfam Y` of part 7 and the integrand `Φ_r e_j = 1_{r ≤ T} S_r e_j` satisfy the
conclusions of `HRS.martingale_representation` (on the space carrying the data).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Rep
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ} {Y : ι → ℝ → Ω → ℝ}

/-- The integrand of the representation. -/
def PhiR (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) : ℝ → Ω → ι → H :=
  fun r ω j => if r ≤ T then S r ω (e j) else 0

lemma isProgressive_of_inner_basis (e : HilbertBasis ι ℝ H) {f : ℝ → Ω → H}
    (hf : ∀ j, IsProgressive ℱ (fun r ω => inner ℝ (e j) (f r ω))) : IsProgressive ℱ f := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  exact measurable_of_inner_basis e (fun j => hf j i)

lemma ARData.isProgressive_S (hA : ARData P ℱ e T Mt Ct S W) (x : H) :
    IsProgressive ℱ (fun r ω => S r ω x) := by
  refine isProgressive_of_inner_basis e (fun j => ?_)
  have : (fun r ω => inner ℝ (e j) (S r ω x)) = fun r ω => inner ℝ (S r ω x) (e j) := by
    funext r ω; exact real_inner_comm _ _
  rw [this]
  exact hA.Sprog x (e j)

lemma ARData.isHSIntegrand (hA : ARData P ℱ e T Mt Ct S W) (t : ℝ) :
    IsHSIntegrand P ℱ t (PhiR e T S) := by
  refine ⟨fun k => ?_, fun r ω => ?_, ?_⟩
  · exact isProgressive_ite_le (hA.isProgressive_S (e k)) T 0
  · by_cases h : r ≤ T
    · obtain ⟨Tr, hT, -⟩ := (hA.trace r ω).hasSum_basis e
      refine hT.summable.congr (fun k => ?_)
      simp only [PhiR, h, if_true]
      rw [← real_inner_self_eq_norm_sq, (hA.sqrt r ω).sq]
    · simp [PhiR, h]
  · have hpt : ∀ r ω, ∑' k, ‖PhiR e T S r ω k‖ₑ ^ 2 = ‖dS e T Ct (r, ω)‖ₑ ^ 2 := by
      intro r ω
      by_cases h : r ≤ T
      · have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
        obtain ⟨Tr, hT, -⟩ := (hA.trace r ω).hasSum_basis e
        have e1 : ∀ k, ‖PhiR e T S r ω k‖ₑ ^ 2 = ENNReal.ofReal (Ct r ω (e k) (e k)) := by
          intro k
          simp only [PhiR, h, if_true]
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← real_inner_self_eq_norm_sq,
            (hA.sqrt r ω).sq]
        simp_rw [e1]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hA.trace r ω).nonneg _) hT.summable]
        simp only [dS, h, if_true]
        rw [enorm_sq_real, Real.sq_sqrt hnn]
        rfl
      · simp [PhiR, dS, h]
    unfold hsSqIntegralOn
    simp_rw [hpt]
    have hm := hA.measurable_dS
    have h1 : ∫⁻ p, ‖dS e T Ct p‖ₑ ^ 2 ∂(tsm P t) =
        ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dS e T Ct (r, ω)‖ₑ ^ 2) ∂P := by
      unfold tsm
      rw [lintegral_prod_symm' _ (by fun_prop : Measurable fun p : ℝ × Ω => ‖dS e T Ct p‖ₑ ^ 2)]
    rw [← h1, HRS.lintegral_enorm_sq_eq_eLpNorm_sq hm.aestronglyMeasurable]
    exact ENNReal.pow_lt_top (hA.eLpNorm_dS t).lt_top

lemma ARData.hsCovForm_PhiR (hA : ARData P ℱ e T Mt Ct S W) (r : ℝ) (hr : r ≤ T) (ω : Ω) :
    hsCovForm (PhiR e T S r ω) = Ct r ω := by
  have hsum : Summable fun k => ‖PhiR e T S r ω k‖ ^ 2 := (hA.isHSIntegrand 0).summable r ω
  ext x y
  rw [hsCovForm_apply hsum]
  simp only [PhiR, hr, if_true]
  have := e.hasSum_inner_mul_inner (S r ω x) (S r ω y)
  rw [← (hA.sqrt r ω).sq x y, ← this.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [(hA.sqrt r ω).symm (e k) x, (hA.sqrt r ω).symm (e k) y, real_inner_comm (S r ω x) (e k),
    real_inner_comm (S r ω y) (e k)]

theorem ARData.representation (hA : ARData P ℱ e T Mt Ct S W) :
    ∃ B : ℝ≥0 → Ω → ι → ℝ, IsCylindricalBrownian P ℱ B ∧
      IsHilbertItoIntegral P ℱ B (PhiR e T S) Mt := by
  obtain ⟨Y, hY⟩ := hA.exists_bdata
  exact ⟨Bfam Y, hY.brownian hA.complete, hA.isHilbertItoIntegral hY⟩

end Rep

end HRS.MRep
