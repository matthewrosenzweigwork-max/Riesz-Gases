import HRS.MP.FlucPath
import HRS.Main.A9Aux2
import HRS.Main.A9Aux32
import HRS.Sections.AdjKGlueAux16
import HRS.Whole.AppendixALemmas2

/-!
# Packet MPGLUE: from finite-dimensional convergence of the statistics to the evaluations of the path

* `mgf_fidi`: the finite-dimensional hypothesis of `HRS.AdjK.adjk_convergence_of_tight_fidi_proof` for the torus
  path sequence (shift `N = n + 2`), from the convergence in law of the statistics `fluctStat`.
* `mgf_final`: the abstract conversion `TendstoInDistribution` (shifted by `2`) `⟹` `ConvergesInLaw`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.GlueFidi

open HRS HRS.AdjK

variable {d : ℕ}

/-- `ConvergesInLaw` of the (shifted) laws of random elements from `TendstoInDistribution`. -/
theorem mgf_final {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Φ : ∀ n, Ω n → E) (Ψ : Ω' → E)
    (h : MeasureTheory.TendstoInDistribution (fun n ω => Φ (n + 2) ω) atTop Ψ
      (fun n => P (n + 2)) P') :
    Main.ConvergesInLaw (fun N => law (P N) (Φ N)) (law P' Ψ) := by
  refine (HRS.Main.A9.a9_conv_shift 2).2 ?_
  intro f
  have h1 := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ h.forall_aemeasurable
    h.aemeasurable_limit).1 h f
  have e : ∀ n, ∫ x, f x ∂(law (P (n + 2)) (Φ (n + 2))) = ∫ ω, f (Φ (n + 2) ω) ∂(P (n + 2)) :=
    fun n => integral_map (h.forall_aemeasurable n) f.continuous.aestronglyMeasurable
  simp only [e]
  rw [show ∫ x, f x ∂(law P' Ψ) = ∫ ω, f (Ψ ω) ∂P' from
    integral_map h.aemeasurable_limit f.continuous.aestronglyMeasurable]
  exact h1

theorem mgf_fidi {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ} (S : Main.MainData d)
    (R : ∀ N, Main.Realization d N)
    (hS : Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (D : DynData d) (ρ' : ℝ → Torus d → ℝ) (c : ℝ)
    (Y₀ : Ω' → NegSobolev d ((Whole.AppendixALemmas.qT d : ℕ) : ℝ))
    (Y : ℝ → Ω' → NegSobolev d ((Whole.AppendixALemmas.qT d : ℕ) : ℝ))
    (hY : HRS.IsLinearFluctuationSolution P' D ρ' ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) c S.T Y₀ Y)
    (hfidi : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin p → Torus d → ℝ),
      (∀ a, Torus.IsSmooth (φ a)) →
      Main.ConvergesInLaw (fun N => Main.fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (law P' (fun ζ => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ζ) (φ a) :
          EuclideanSpace ℝ (Fin p))))) :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin p → Torus d → ℝ),
      (∀ a, Torus.IsSmooth (φ a)) →
      MeasureTheory.TendstoInDistribution
        (fun n ω => (WithLp.toLp 2 fun a => NegSobolev.eval
          ((HRS.flucPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T (S.sigma (n + 2)) (R (n + 2)).X
            (S.ρ (n + 2)) ω).at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)))
        atTop
        (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval
          ((HRS.toPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T Y ω').at'
          ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)))
        (fun n => (R (n + 2)).P) P' := by
  classical
  intro p ts hts φ hφ
  have hm2 : (d : ℝ) < 2 * ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) := by
    simp only [Whole.AppendixALemmas.qT, Main.gammaIdx]
    push_cast
    have : (0 : ℝ) ≤ (PDE.mStar d : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    linarith
  have hS' : Main.TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 :=
    Main.A9.a9_standing_mono (by simp only [Main.gammaIdx]; omega) hS
  have hevc : ∀ a, Continuous fun z : NegSobolev d ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) => NegSobolev.eval z (φ a) := fun a =>
    adjkg_eval_continuous (adjkg_smooth_sobolev (hφ a) ((Whole.AppendixALemmas.qT d : ℕ) : ℝ))
  have hat : ∀ a, Continuous fun w : PathSpace d ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T => w.at' ⟨ts a, hts a⟩ := fun a => by
    show Continuous fun w : C(Set.Icc (0 : ℝ) S.T, NegSobolev d ((Whole.AppendixALemmas.qT d : ℕ) : ℝ)) => w ⟨ts a, hts a⟩
    exact continuous_eval_const _
  have hvec : Continuous fun w : PathSpace d ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T => (WithLp.toLp 2 fun a => NegSobolev.eval
      (w.at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).comp
      (continuous_pi fun a => (hevc a).comp (hat a))
  -- the limit side
  set Ψ' : Ω' → EuclideanSpace ℝ (Fin p) := fun ζ =>
    (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ζ) (φ a) : EuclideanSpace ℝ (Fin p)) with hΨ'
  have hΨ'm : AEMeasurable Ψ' P' :=
    ((PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (hevc a).measurable.comp (hY.meas _))).aemeasurable
  have hΨae : (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval
        ((HRS.toPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T Y ω').at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) =ᵐ[P'] Ψ' := by
    filter_upwards [hY.cont] with ω' hω'
    have hc : Continuous fun t : Set.Icc (0 : ℝ) S.T => Y t ω' :=
      continuousOn_iff_continuous_restrict.1 hω'
    ext a
    simp only [WithLp.ofLp_toLp, hΨ']
    rw [adjkg_toPath_at ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T Y ω' hc ⟨ts a, hts a⟩]
  -- the particle side
  have hN : ∀ n : ℕ, 1 ≤ n + 2 := fun n => by omega
  have hΦae : ∀ n : ℕ, (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval
        ((HRS.flucPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ω).at'
          ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) =ᵐ[(R (n + 2)).P]
      Main.fluctStat (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ts φ := by
    intro n
    have hMFN := hS'.mean_field.solution (n + 2) (hN n)
    filter_upwards [(HRS.MP.FlucPath.mpf_fluc_cont_meas hS' (hN n) ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) hm2).1] with ω hω
    ext a
    simp only [WithLp.ofLp_toLp, Main.fluctStat]
    haveI : IsProbabilityMeasure (empirical ((R (n + 2)).X (Real.toNNReal (ts a)) ω)) :=
      empirical_isProbabilityMeasure (hN n) _
    haveI : IsProbabilityMeasure (withDensityReal (S.ρ (n + 2) (ts a))) :=
      isProb_withDensityReal (hMFN.density (ts a) (hts a))
    rw [adjkg_flucPath_at ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T _ _ _ ω hω ⟨ts a, hts a⟩, adjkg_eval_smul,
      NegSobolev.eval_ofMeasureDiff hm2 _ _ (φ a) (hφ a)]
  have hΦm : ∀ n : ℕ, AEMeasurable (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval
        ((HRS.flucPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ω).at'
          ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) (R (n + 2)).P := fun n =>
    hvec.measurable.comp_aemeasurable (HRS.MP.FlucPath.mpf_fluc_cont_meas hS' (hN n) ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) hm2).2
  have hΨm : AEMeasurable (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval
        ((HRS.toPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T Y ω').at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) P' :=
    hΨ'm.congr hΨae.symm
  have hlim := (HRS.Main.A9.a9_conv_shift 2).1 (hfidi p ts hts φ hφ)
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hΦm hΨm).2 fun f => ?_
  have h1 := hlim f
  have e1 : ∀ n : ℕ, ∫ ω, f ((WithLp.toLp 2 fun a => NegSobolev.eval
        ((HRS.flucPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ω).at'
          ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) ∂(R (n + 2)).P =
      ∫ x, f x ∂(Main.fluctStatLaw (R (n + 2)).P (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ts φ) := by
    intro n
    have hfs : AEMeasurable (Main.fluctStat (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ts φ)
        (R (n + 2)).P := (hΦm n).congr (hΦae n)
    unfold Main.fluctStatLaw
    rw [integral_map hfs f.continuous.aestronglyMeasurable]
    exact integral_congr_ae (by filter_upwards [hΦae n] with ω hω; rw [hω])
  have e2 : ∫ ω', f ((WithLp.toLp 2 fun a => NegSobolev.eval
        ((HRS.toPath ((Whole.AppendixALemmas.qT d : ℕ) : ℝ) S.T Y ω').at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) ∂P' =
      ∫ x, f x ∂(law P' Ψ') := by
    rw [integral_map hΨ'm f.continuous.aestronglyMeasurable]
    exact integral_congr_ae (by filter_upwards [hΨae] with ω hω; rw [hω])
  simp only [e1, e2]
  exact h1

end HRS.MP.GlueFidi
