import HRS.MC.S7FCDefs
import HRS.MC.S7FCW4Aux
import HRS.MC.S7FCW4D1
import HRS.Sections.AllTimeAux1
import HRS.Dynamics.ParticleWellposed
import HRS.Stochastic.SelectedFlow

/-!
# `field_chaos` packet D2 (worker fcw4): proof of `s7_FC_D2_selected`

Statement copied verbatim from `HRS/MC/S7FCPlan.lean` (spec, sorry); proof here, no sorried module imported.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW4

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec
open HRS.MC.Sec7.FCPlan

variable {d : ℕ}

lemma S7FCW4_eLpNorm_toReal {α : Type*} [MeasurableSpace α] {ν : Measure α} (p : ℝ≥0∞)
    {f : α → ℝ≥0∞} (hf : Measurable f) (hfin : ∀ᵐ x ∂ν, f x ≠ ⊤) :
    eLpNorm (fun x => (f x).toReal) p ν = eLpNorm f p ν := by
  refine eLpNorm_congr_enorm_ae (hf := hf.ennreal_toReal.aestronglyMeasurable)
    (hg := hf.aestronglyMeasurable) ?_
  filter_upwards [hfin] with x hx
  rw [Real.enorm_toReal hx, enorm_eq_self]

lemma S7FCW4_symNonpos_neg_one (n : ℕ) : Torus.SymNonpos (-1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold Torus.SymNonpos Torus.symPart
  simp only [Matrix.transpose_neg, Matrix.transpose_one]
  have : (-((1 / 2 : ℝ) • ((-1 : Matrix (Fin n) (Fin n) ℝ) + -1))) = 1 := by
    rw [← two_smul ℝ (-1 : Matrix (Fin n) (Fin n) ℝ), smul_smul]
    norm_num
  rw [this]
  exact Matrix.PosSemidef.one

lemma S7FCW4_isCk_two (R : Regime d) : Torus.IsCk 2 R.D.V :=
  PDE.ClassicalAux.isCk_of_le (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (m := 2)
    (by first | norm_num | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) R.hV

theorem s7_FC_D2_selected_proof (R : Regime d) :
    ∃ p₀ C : ℝ, 1 < p₀ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ T' : ℝ, 0 < T' →
          SelectedFlow P (s7fcPrep R).dyn T' (X 0) W X ∧
          (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
            (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) ∧
          relEntropy (law P (X 0)) ((s7fcPrep R).refMeasure N 0) < ⊤ ∧
          MemLp (fun Y => (((law P (X 0)).rnDeriv ((s7fcPrep R).refMeasure N 0)) Y).toReal)
            (ENNReal.ofReal p₀) ((s7fcPrep R).refMeasure N 0) ∧
          (s7fcPrep R).B N (law P (X 0)) ≤ C ∧ (s7fcPrep R).J N (law P (X 0)) p₀ ≤ C := by
  obtain ⟨p₀, C₀, hp₀, hC₀, hinit⟩ := alltime_init R
  have hK0 : 0 ≤ (Real.exp C₀ ^ p₀ - 1) / (p₀ - 1) := by
    apply div_nonneg
    · have : 1 ≤ Real.exp C₀ ^ p₀ := Real.one_le_rpow (Real.one_le_exp hC₀) (by linarith)
      linarith
    · linarith
  refine ⟨p₀, 2 + (Real.exp C₀ ^ p₀ - 1) / (p₀ - 1) + C₀, hp₀,
    fun N hN Ω _ P hP X₀ W X hreal T' hT' => ?_⟩
  have hN0 : 0 < N := by omega
  obtain ⟨hac, hL⟩ := hinit N hN
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hcont : Continuous R.ρ₀ :=
    PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift R.ρ₀) from R.hρ₀.smooth)
      (by exact_mod_cast le_top))
  have hβ₀ : 0 ≤ R.β₀ := by rcases R.hβ₀ with h | ⟨_, h⟩ <;> linarith
  have hQ0 : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) :=
    alltime_gibbs_prob hd1 R.D.hs0 R.D.hsd R.hρ₀.density hcont hN0 hβ₀
  have hQb : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀)) :=
    alltime_gibbs_prob hd1 R.D.hs0 R.D.hsd R.hρ₀.density hcont hN0 R.hβ.le
  have hsol := hreal.solution T'
  have hX0 : X 0 =ᵐ[P] X₀ := hsol.init
  have hlaw : law P (X 0) = modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀) :=
    (Measure.map_congr hX0).trans hreal.law_init
  have hR : (s7fcPrep R).refMeasure N 0 =
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀) :=
    S7FCW4_refMeasure R N
  have hNd : (N : ℝ) * deltaN d (s7fcPrep R).s N = 1 := alltime_Ndelta R.hs hN0
  have hrn : ∀ᵐ x ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀)),
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)).rnDeriv
        (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀)) x ≠ ⊤ :=
    (Measure.rnDeriv_lt_top _ _).mono fun x hx => hx.ne
  have hLr : eLpNorm (fun x => ((modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)).rnDeriv
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀)) x).toReal)
      (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀))
      ≤ ENNReal.ofReal (Real.exp C₀) := by
    rw [S7FCW4_eLpNorm_toReal _ (Measure.measurable_rnDeriv _ _) hrn]
    exact hL
  have hKL : relEntropy (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀)) ≤
      ENNReal.ofReal ((Real.exp C₀ ^ p₀ - 1) / (p₀ - 1)) :=
    S7FCW4_kl_le_of_Lp _ _ hac hp₀ (Real.exp_nonneg C₀) hLr
  refine ⟨?_, hreal.filtered, ?_, ?_, ?_, ?_⟩
  · rw [S7FCW4_dyn R]
    have hmeas0 : Measurable (X 0) := hsol.adapted 0
    have hdist : ∀ᵐ ω ∂P, X 0 ω ∉ collisionSet d N := by
      filter_upwards [hsol.no_collision] with ω hω
      exact hω 0 (by simpa using hT'.le)
    have hind0 : ProbabilityTheory.IndepFun (X 0) (fun ω => fun t => W t ω) P :=
      hreal.indep.congr hX0.symm EventuallyEq.rfl
    have hpath := (particle_wellposed P R.D R.hd hN (by rw [R.hM]; exact S7FCW4_symNonpos_neg_one d)
      (S7FCW4_isCk_two R) (X 0) hmeas0 hdist W hreal.brownian hind0 T' hT').2
    exact ⟨hmeas0, hdist, hreal.brownian, hind0,
      Or.inl ⟨⟨hsol.lift, Eventually.of_forall fun _ => rfl, hsol.cont, hsol.adapted, hsol.no_collision⟩,
        hpath⟩⟩
  · rw [hlaw, hR]
    exact lt_of_le_of_lt hKL ENNReal.ofReal_lt_top
  · rw [hlaw, hR]
    exact lt_of_le_of_lt hLr ENNReal.ofReal_lt_top
  · unfold HRS.Main.PreparedData.B
    rw [hlaw, hR, hNd]
    have hent : (relEntropy (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
        (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀))).toReal ≤
        (Real.exp C₀ ^ p₀ - 1) / (p₀ - 1) :=
      ENNReal.toReal_le_of_le_ofReal hK0 hKL
    linarith [hent, hK0, hC₀]
  · unfold HRS.Main.PreparedData.J
    rw [hlaw, hR, hNd]
    have hEle := ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg C₀) hLr
    have hlog : Real.log (eLpNorm (fun x => ((modulatedGibbs (periodicRiesz d R.D.s) N R.β₀
        (withDensityReal R.ρ₀)).rnDeriv (modulatedGibbs (periodicRiesz d R.D.s) N R.β
        (withDensityReal R.ρ₀)) x).toReal) (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d R.D.s) N R.β
        (withDensityReal R.ρ₀))).toReal ≤ C₀ := by
      rcases ENNReal.toReal_nonneg.eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact hC₀
      · exact (Real.log_le_iff_le_exp hpos).2 hEle
    linarith [hlog, hK0]

end HRS.MC.Sec7.S7FCW4

end
