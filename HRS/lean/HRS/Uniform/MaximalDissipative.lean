import HRS.Uniform.KotConv
import HRS.Uniform.MaximalTwoLevel

/-!
# Lemma 3.17, dissipative alternative (packet KOTELENEZ)

The stochastic convolution `Z_t = ∫₀ᵗ V(t,r) dM_r` for a quasi-contractive evolution (second alternative of
Lemma 3.17) exists as an `L²`-limit of Riemann sums over arbitrary partitions, has a continuous version and satisfies
`E sup_t ‖Z_t‖^p ≤ C(p,K,T) E (∫ Tr Σ)^{p/2}`.  The proof is Kotelenez's: the Riemann sums on a partition are, after a
Sz.-Nagy-type dilation of the time-ordered products of the contractions `V(s_{l+1}, s_l)`, contractions of a martingale
transform of `M` with deterministic step operators (`HRS/Uniform/KotDilation.lean`, `KotTransform.lean`), so the
dimension-free Hilbert BDG inequality gives a bound uniform in the partition (`KotMaximal.lean`); differences of Riemann
sums on a partition and a refinement are again of this form with operators tending to `0` strongly (`KotConv.lean`), which
gives the Cauchy property, the continuous version (dyadic partitions, Borel–Cantelli), and the `L²`-convergence over all
partitions.  The TeX's Galerkin difference argument (L2042-2045) is not used.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS
namespace Uniform

open Kot

/-- Clause (1) of Lemma 3.17 for the dissipative alternative. -/
theorem maximal_dissipative (T p K : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (hS : S.IsEvolution T ∧ S.Dissipative T K)
        (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
        (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg),
        ∃ Z : ℝ → Ω → E,
          (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t)) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) ∧
          (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) ^ p ∂P) ^ (1 / p) ≤
            ENNReal.ofReal C *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P) ^
                (1 / p) := by
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  refine ⟨CD p K T ^ (1 / p), Real.rpow_nonneg (CD_nonneg _ _ _) _, ?_⟩
  intro Ω mΩ P _ ℱ H E _ _ _ _ _ _ _ _ _ _ _ _ S hS M Sg hM
  obtain ⟨hev, hD⟩ := hS
  have hD0 := hD
  obtain ⟨hj, hsurj, -, -, -⟩ := hD0
  have hjE : ∀ x, ‖S.j x‖ₑ = ‖x‖ₑ := fun x => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hj x]
  have hcomp : IsCompleteFiltration P (augFiltration P ℱ) := augFiltration_isComplete ℱ
  have hM' := isHMC_aug hM
  have hV : EvolBound S.VH K T :=
    { norm_le := fun r t hr hrt htT => by
        refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x => ?_
        exact EvolData.Dissipative.norm_VH_le S hD ⟨hr, hrt.trans htT⟩ ⟨hrt, htT⟩ x
      comp := fun r t u hr hrt htu huT => by
        have := hev.comp_H r t u hr hrt htu huT
        exact this
      self := fun t ht0 htT => hev.self_H t ⟨ht0, htT⟩ }
  obtain ⟨m, Z', hm, hZc, hlim⟩ := exists_dyadic_limit hcomp hM' hV (EvolData.Dissipative.cont_VH hev hD) hT
  refine ⟨fun t ω => S.j (Z' t ω), ?_, ?_, ?_⟩
  · intro t ht ε hε
    obtain ⟨δ, hδ, hconv⟩ := hconv_Z hcomp hM' hV (EvolData.Dissipative.cont_VH hev hD) hT hm hlim ht ε hε
    refine ⟨δ, hδ, fun n r hr0 hrn hmono hmesh => ?_⟩
    have hrs : ∀ ω, riemannSum S.VE S.j M t r ω =
        S.j (∑ i : Fin n, S.VH t (r i.castSucc) (M (r i.succ) ω - M (r i.castSucc) ω)) := by
      intro ω
      unfold riemannSum
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h0 : 0 ≤ r i.castSucc := hr0 ▸ hmono (Fin.zero_le _)
      have h1 : r i.castSucc ≤ t := hrn ▸ hmono (Fin.le_last _)
      have := congrArg (fun F : H →L[ℝ] E => F (M (r i.succ) ω - M (r i.castSucc) ω))
        (hev.intertwine (r i.castSucc) t h0 h1 ht.2)
      simpa using this
    have := hconv n r hr0 hrn hmono hmesh
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr fun ω => ?_
    rw [hrs ω, ← map_sub, hjE]
  · exact hZc.mono fun ω h => S.j.continuous.comp_continuousOn h
  · have hb := sup_Z_bound hcomp hM' hV hT hZc hlim hp1
    have e : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖S.j (Z' t ω)‖ₑ) = ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z' t ω‖ₑ := by
      intro ω
      refine iSup_congr fun t => iSup_congr fun _ => ?_
      exact hjE _
    simp_rw [e]
    calc (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z' t ω‖ₑ) ^ p ∂P) ^ (1 / p)
        ≤ (ENNReal.ofReal (CD p K T) *
            ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P) ^
              (1 / p) := ENNReal.rpow_le_rpow hb (by positivity)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (CD_nonneg _ _ _) (by positivity)]

/-- **Lemma 3.17** (`HRS.Uniform.maximal_estimate`, proved; the original keeps its `sorry` because `Spec.lean` cannot import
this file). -/
theorem maximal_estimate_proof (T p K : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (hS : S.MaxHyp T K)
        (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
        (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg),
        ∃ Z : ℝ → Ω → E,
          (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t)) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) ∧
          (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) ^ p ∂P) ^ (1 / p) ≤
            ENNReal.ofReal C *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P) ^ (1 / p)) ∧
      (∀ (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        (S : EvolData H E) (hS : S.MaxHyp T K) (b : ℝ → H),
        ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖∫ r in Set.Icc (0 : ℝ) t, S.VE t r (S.j (b r))‖ₑ ≤
          ENNReal.ofReal C * ∫⁻ r in Set.Icc (0 : ℝ) T, ‖b r‖ₑ) := by
  obtain ⟨C₁, hC₁0, hC₁, -⟩ := maximal_estimate_twoLevel T p K hT hp
  obtain ⟨C₂, hC₂0, hC₂⟩ := maximal_dissipative T p K hT hp
  refine ⟨max (max C₁ C₂) (detConst T K), le_max_of_le_left (le_max_of_le_left hC₁0), ?_, ?_⟩
  · intro Ω mΩ P _ ℱ H E _ _ _ _ _ _ _ _ _ _ _ _ S hS M Sg hM
    obtain ⟨hev, h | h⟩ := hS
    · obtain ⟨Z, hZ1, hZ2, hZ3⟩ := hC₁ Ω P ℱ H E S ⟨hev, h⟩ M Sg hM
      refine ⟨Z, hZ1, hZ2, hZ3.trans ?_⟩
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_of_le_left (le_max_left _ _))) le_rfl
    · obtain ⟨Z, hZ1, hZ2, hZ3⟩ := hC₂ Ω P ℱ H E S ⟨hev, h⟩ M Sg hM
      refine ⟨Z, hZ1, hZ2, hZ3.trans ?_⟩
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_of_le_left (le_max_right _ _))) le_rfl
  · intro H E _ _ _ _ _ S hS b
    exact (maximal_deterministic T K hT S hS b).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl)

end Uniform
end HRS
