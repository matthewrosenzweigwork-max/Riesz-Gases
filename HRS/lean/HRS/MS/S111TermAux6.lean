import HRS.MS.S111TermAux5

/-!
# S11.1 terminal wave, G01 part 4: a common-noise measurable family with fourth-moment increments
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111T

open HRS.Whole

variable {d : ℕ} {m : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem S111tIsGSL.congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : ℕ → Ω → ℝ}
    {ℓ : ℕ → OscDual d m} {Y Y' : Ω → OscDual d m} (h : S111tIsGSL P g ℓ Y) (hae : Y =ᵐ[P] Y') :
    S111tIsGSL P g ℓ Y' := by
  refine ⟨h.memLp.ae_eq hae, ?_⟩
  have : ∀ K, ∫ ω, ‖s111t_gsum g ℓ K ω - Y' ω‖ ^ 2 ∂P = ∫ ω, ‖s111t_gsum g ℓ K ω - Y ω‖ ^ 2 ∂P := by
    intro K
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hω]
  simp_rw [this]
  exact h.tendsto

/-- The common-noise family: one iid Gaussian sequence, measurable `ℓ²`-valued versions `X i t` of the series with
feature vectors `⟨F i t α, e_k⟩`, and fourth-moment increments. -/
theorem s111t_family (m : ℝ) (e : HilbertBasis ℕ ℝ E) (F : Fin 2 → ℝ → MultiIndex d → E)
    (hF : ∀ i t, Summable fun α => ‖F i t α‖ ^ 2) (L : ℝ) (hL : 0 ≤ L)
    (hinc : ∀ i t v, Summable (fun α => ‖F i t α - F i v α‖ ^ 2) ∧
      (∑' α, ‖F i t α - F i v α‖ ^ 2) ≤ L * |t - v|) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P) (g : ℕ → Ω → ℝ)
      (X : Fin 2 → ℝ → Ω → OscDual d m),
      (∀ i, HasLaw (g i) (gaussianReal 0 1) P) ∧ iIndepFun g P ∧
      (∀ i t, Measurable (X i t)) ∧
      (∀ i t, S111tIsGSL P g (fun k => s111t_vec m e (F i t) k) (X i t)) ∧
      ∀ i s t, ∫⁻ ω, ‖X i t ω - X i s ω‖ₑ ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (3 * L ^ 2 * |t - s| ^ ((1 : ℝ) + 1)) := by
  obtain ⟨Ω, mΩ, P, g, hgm, hg, hind, hP⟩ := ProbabilityTheory.exists_iid ℕ (gaussianReal 0 1)
  have hex : ∀ i t, ∃ X : Ω → OscDual d m, Measurable X ∧
      S111tIsGSL P g (fun k => s111t_vec m e (F i t) k) X := by
    intro i t
    obtain ⟨Y, hY⟩ := s111t_gsl_exists (P := P) hg hind (fun k => s111t_vec m e (F i t) k)
      (s111t_vec_norm_sq_summable e (F i t) (hF i t)).1
    refine ⟨hY.memLp.aestronglyMeasurable.mk Y, hY.memLp.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hY.congr_ae hY.memLp.aestronglyMeasurable.ae_eq_mk⟩
  choose X hXm hXg using hex
  refine ⟨Ω, mΩ, P, hP, g, X, hg, hind, hXm, hXg, fun i s t => ?_⟩
  have hsub := (hXg i t).sub hg (hXg i s)
  have hv : (fun k => s111t_vec m e (F i t) k - s111t_vec m e (F i s) k) =
      fun k => s111t_vec m e (fun α => F i t α - F i s α) k := by
    funext k
    exact (s111t_vec_sub e (F i t) (F i s) (hF i t) (hF i s) k).symm
  have hs := s111t_vec_norm_sq_summable (m := m) e _ (hinc i t s).1
  have hfour := s111t_gsl_fourth (P := P) hg hind
    (fun k => s111t_vec m e (fun α => F i t α - F i s α) k) hs.1 (fun ω => X i t ω - X i s ω)
    (by simpa only [hv] using hsub)
  refine hfour.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hs.2]
  have hσ0 : 0 ≤ ∑' α, ‖F i t α - F i s α‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have h1 := (hinc i t s).2
  have h2 : (∑' α, ‖F i t α - F i s α‖ ^ 2) ^ 2 ≤ (L * |t - s|) ^ 2 := pow_le_pow_left₀ hσ0 h1 2
  have h3 : |t - s| ^ ((1 : ℝ) + 1) = |t - s| ^ 2 := by
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  nlinarith [h2]

end HRS.MS.S111T
