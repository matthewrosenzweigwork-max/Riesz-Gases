import HRS.MP.SelfSimP5Spec
import HRS.MP.SelfSimP5Mix
import HRS.MP.SelfSimP5Cond
import HRS.MP.SelfSimP5Chamber
import HRS.MP.SelfSimP5Trunc
import HRS.MP.SelfSimP5Reg
import HRS.MP.SelfSimP5Conv
import HRS.MP.SelfSimP5Init
import HRS.MP.SelfSimP5LimC
import HRS.MP.SelfSimP5Fp
import HRS.MP.SelfSimP5Ds

/-!
# S.A.28, packet P5: the self-similar entropy inequality for the ordered one-dimensional flow

The assembly of `HRS.MP.SelfSimP5.ss_P5_entropy_cepa_proof` with each interface lemma replaced by its proof.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim
open HRS.MP.SelfSimP5 (Ch5 ss5_cone ss5_toCh ss5_chNoise ss5_Phi ss5_U ss5_eps ss5_eps_pos ss5_eps_le_one ss5_lip_neg ss5_ent ss5_fish ss5_IsSol)
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Final

/-- **P5, assembly** (statement verbatim from `HRS.MP.SelfSim.ss_P5_entropy_cepa`; every interface lemma replaced by its proof). -/
theorem ss_P5_entropy_cepa_final (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hY : SSAddSol P invβ (ssDrift 1 0 N) S ℱ W' W Y) (hord : SSOrdered P S Y)
    (hH0 : gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law P (Y 0)) < ⊤) :
    SSEntropyIneq 1 0 invβ N S P Y := by
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le _) le_rfl
  refine HRS.MP.SelfSimP5Impl.ss5_mixture_proof N hN invβ hβ S hS P hYm hY.cont hord hY.init_distinct hH0 ?_
  intro σ hA hfin0
  set Q := ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ) with hQ
  haveI : IsProbabilityMeasure Q := cond_isProbabilityMeasure_of_finite hA (measure_ne_top _ _)
  obtain ⟨ℱ', hYQ, hordQ, h0Q⟩ := HRS.MP.SelfSimP5Impl.ss5_cond_solution_proof N hN invβ hβ S hS P hY hord σ hA
  obtain ⟨hBr, hz0m, hm0, hyc, hpath⟩ :=
    HRS.MP.SelfSimP5Impl.ss5_chamber_reading_proof N hN invβ hβ S hS Q hYQ σ hordQ h0Q hfin0
  set z₀ : Ω → Ch5 N := fun ζ => ss5_toCh σ (Y 0 ζ) with hz₀
  -- the regularised strong solutions
  have hreg : ∀ n : ℕ, ∃ Zn : ℝ → Ω → Ch5 N,
      ss5_IsSol Q ℱ' (ss5_chNoise σ W') invβ (fun z => -(gradient (ss5_U N (ss5_eps n)) z)) z₀ Zn ∧
        ∀ ζ, Zn 0 ζ = z₀ ζ := by
    intro n
    obtain ⟨-, ⟨K, hK⟩, -, -⟩ := HRS.MP.SelfSimP5Impl.ss5_trunc_props_proof N (ss5_eps_pos n) (ss5_eps_le_one n)
    exact HRS.MP.SelfSimP5Impl.ss5_regularised_sol_proof hBr hβ (ss5_lip_neg hK) hz0m
  choose Z hZ hZ0 using hreg
  have hZm : ∀ n t, 0 ≤ t → Measurable (Z n t) := fun n t ht => ((hZ n).2.1 t ht).mono (ℱ'.le t) le_rfl
  -- the level-`n` entropy dissipation
  have hdiss : ∀ n, ∀ t ∈ Icc (0 : ℝ) S,
      ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n t)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) t,
          ss5_fish invβ (ss5_U N (ss5_eps n)) (Q.map (Z n r)) : ℝ≥0∞) : EReal)
        ≤ ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n 0)) := by
    intro n
    obtain ⟨hC2, ⟨K, hK⟩, hconf, -⟩ := HRS.MP.SelfSimP5Impl.ss5_trunc_props_proof N (ss5_eps_pos n) (ss5_eps_le_one n)
    obtain ⟨hfp, hmom, hnar⟩ := HRS.MP.SelfSimP5Fp.ss5_sde_weakFP_proof hBr hC2 hK hβ hz0m hm0 (hZ n)
    have hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (Q.map (Z n t)) := fun t ht =>
      (Measure.isProbabilityMeasure_map_iff (hZm n t ht).aemeasurable).2 inferInstance
    have h0eq : Q.map (Z n 0) = Q.map z₀ := by
      congr 1; funext ζ; exact hZ0 n ζ
    have hfin : ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n 0)) < ⊤ := by
      rw [h0eq]
      exact lt_of_le_of_lt (HRS.MP.SelfSimP5Impl.ss5_initial_bound_proof N hN invβ hβ Q σ (hYm 0) h0Q (ss5_eps_pos n)) hfin0
    exact HRS.MP.SelfSimP5Ds.ss5_dissipation_core_proof hC2 hK hconf hβ hprob hS.le (hmom S) (fun g hg hb => hnar g hg hb S) hfp hfin
  -- pathwise convergence of the regularised flows
  have hconv : ∀ᵐ ζ ∂Q, ∀ t ∈ Icc (0 : ℝ) S,
      Tendsto (fun n => Z n t ζ) atTop (𝓝 (ss5_toCh σ (Y (Real.toNNReal t) ζ))) := by
    have hZae : ∀ᵐ ζ ∂Q, ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → Z n t ζ = z₀ ζ +
        (∫ s in (0 : ℝ)..t, -(gradient (ss5_U N (ss5_eps n)) (Z n s ζ))) +
        Real.sqrt (2 * invβ) • WithLp.toLp 2 (ss5_chNoise σ W' (Real.toNNReal t) ζ) :=
      ae_all_iff.2 fun n => (hZ n).2.2
    filter_upwards [hpath, hZae] with ζ hζ hzeq
    obtain ⟨hyC, hgap, hyeq⟩ := hζ
    exact HRS.MP.SelfSimP5Impl.ss5_pathwise_conv_proof (y := fun r => ss5_toCh σ (Y (Real.toNNReal r) ζ))
      (w := fun t => Real.sqrt (2 * invβ) • WithLp.toLp 2 (ss5_chNoise σ W' (Real.toNNReal t) ζ))
      (z := fun n t => Z n t ζ) hS.le (hyc ζ) hyC hgap hyeq (fun n => (hZ n).1 ζ)
      (fun n t ht => hzeq n t ht.1)
  exact HRS.MP.SelfSimP5Impl.ss5_limit_proof N hN invβ hβ S hS Q σ hYm hordQ h0Q (fun n ζ => (hZ n).1 ζ) hZm
    (fun n => Filter.Eventually.of_forall fun ζ => hZ0 n ζ) hconv hdiss

example := (@ss_P5_entropy_cepa_final : type_of% @HRS.MP.SelfSim.ss_P5_entropy_cepa)

end HRS.MP.SelfSimP5Final
