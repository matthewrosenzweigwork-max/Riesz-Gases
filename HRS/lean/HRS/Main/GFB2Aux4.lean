import HRS.Main.GFB2Aux3
import HRS.Uniform.Q12Final
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Packet GFB2, part 4: lower semicontinuity of the torus Wasserstein distance (for measurability in `gf_transport_moment`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

instance gfb2_borel1 : BorelSpace (Torus d) := Pi.borelSpace

instance gfb2_opens1 : OpensMeasurableSpace (Torus d) := Pi.opensMeasurableSpace

instance gfb2_borel2 : BorelSpace (Torus d × Torus d) := Prod.borelSpace

/-- The quadratic transport cost of a coupling. -/
def gfb2_cost (π : ProbabilityMeasure (Torus d × Torus d)) : ℝ :=
  ∫ z, Torus.tdist z.1 z.2 ^ 2 ∂(π : Measure (Torus d × Torus d))

theorem gfb2_tdist_sq_cont : Continuous fun z : Torus d × Torus d => Torus.tdist z.1 z.2 ^ 2 :=
  (Uniform.Q14.q14_continuous_tdist (d := d)).pow 2

theorem gfb2_cost_cont : Continuous (gfb2_cost (d := d)) := by
  let g : BoundedContinuousFunction (Torus d × Torus d) ℝ := BoundedContinuousFunction.mkOfCompact ⟨_, gfb2_tdist_sq_cont⟩
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction g

theorem gfb2_cost_nonneg (π : ProbabilityMeasure (Torus d × Torus d)) : 0 ≤ gfb2_cost π :=
  integral_nonneg fun z => sq_nonneg _

theorem gfb2_lintegral_cost (π : Measure (Torus d × Torus d)) [IsProbabilityMeasure π] :
    ∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) ∂π =
      ENNReal.ofReal (∫ z, Torus.tdist z.1 z.2 ^ 2 ∂π) := by
  have hint : Integrable (fun z : Torus d × Torus d => Torus.tdist z.1 z.2 ^ 2) π :=
    gfb2_tdist_sq_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => sq_nonneg _)]
  refine lintegral_congr fun z => ?_
  rw [Real.rpow_two]


/-- First marginal of a coupling. -/
def gfb2_m1 (π : ProbabilityMeasure (Torus d × Torus d)) : ProbabilityMeasure (Torus d) := π.map Prod.fst

/-- Second marginal of a coupling. -/
def gfb2_m2 (π : ProbabilityMeasure (Torus d × Torus d)) : ProbabilityMeasure (Torus d) := π.map Prod.snd

theorem gfb2_m1_cont : Continuous (gfb2_m1 (d := d)) :=
  ProbabilityMeasure.continuous_map continuous_fst

theorem gfb2_m2_cont : Continuous (gfb2_m2 (d := d)) :=
  ProbabilityMeasure.continuous_map continuous_snd

theorem gfb2_W_le_cost (μ ν : ProbabilityMeasure (Torus d)) (π : ProbabilityMeasure (Torus d × Torus d))
    (h1 : gfb2_m1 π = μ) (h2 : gfb2_m2 π = ν) :
    torusWassersteinE 2 (μ : Measure (Torus d)) (ν : Measure (Torus d)) ≤
      ENNReal.ofReal (Real.sqrt (gfb2_cost π)) := by
  have e1 : (π : Measure (Torus d × Torus d)).map Prod.fst = μ := by
    rw [← h1]; rfl
  have e2 : (π : Measure (Torus d × Torus d)).map Prod.snd = ν := by
    rw [← h2]; rfl
  refine (Uniform.Q12.q12_W_le_cost e1 e2).trans (le_of_eq ?_)
  rw [gfb2_lintegral_cost]
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun z => sq_nonneg _) (by norm_num),
    Real.sqrt_eq_rpow]
  rfl


theorem gfb2_W_attained (μ ν : ProbabilityMeasure (Torus d)) :
    ∃ π : ProbabilityMeasure (Torus d × Torus d), gfb2_m1 π = μ ∧ gfb2_m2 π = ν ∧
      torusWassersteinE 2 (μ : Measure (Torus d)) (ν : Measure (Torus d)) =
        ENNReal.ofReal (Real.sqrt (gfb2_cost π)) := by
  set S : Set (ProbabilityMeasure (Torus d × Torus d)) := {π | gfb2_m1 π = μ ∧ gfb2_m2 π = ν} with hS
  have hSc : IsCompact S := by
    refine IsClosed.isCompact ?_
    exact (isClosed_eq gfb2_m1_cont continuous_const).inter (isClosed_eq gfb2_m2_cont continuous_const)
  have hne : S.Nonempty := by
    refine ⟨⟨(μ : Measure (Torus d)).prod (ν : Measure (Torus d)), inferInstance⟩, ?_, ?_⟩
    · apply Subtype.ext
      show Measure.map Prod.fst ((μ : Measure (Torus d)).prod (ν : Measure (Torus d))) = μ
      rw [Measure.map_fst_prod]; simp
    · apply Subtype.ext
      show Measure.map Prod.snd ((μ : Measure (Torus d)).prod (ν : Measure (Torus d))) = ν
      rw [Measure.map_snd_prod]; simp
  obtain ⟨π, hπS, hπmin⟩ := hSc.exists_isMinOn hne gfb2_cost_cont.continuousOn
  refine ⟨π, hπS.1, hπS.2, le_antisymm (gfb2_W_le_cost μ ν π hπS.1 hπS.2) ?_⟩
  unfold torusWassersteinE
  refine le_iInf fun π' => ?_
  have hprob : IsProbabilityMeasure π'.1 := by
    refine ⟨?_⟩
    have h := congrArg (fun m : Measure (Torus d) => m Set.univ) π'.2.1
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h
    rw [h]; exact measure_univ
  set πP : ProbabilityMeasure (Torus d × Torus d) := ⟨π'.1, hprob⟩ with hπP
  have hπPS : πP ∈ S := by
    refine ⟨?_, ?_⟩
    · apply Subtype.ext; exact π'.2.1
    · apply Subtype.ext; exact π'.2.2
  have hle : gfb2_cost π ≤ gfb2_cost πP := hπmin hπPS
  have hl := gfb2_lintegral_cost π'.1
  rw [hl, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun z => sq_nonneg _) (by norm_num)]
  rw [Real.sqrt_eq_rpow]
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.rpow_le_rpow (gfb2_cost_nonneg π) hle (by norm_num)


theorem gfb2_W_lsc : LowerSemicontinuous
    (fun p : ProbabilityMeasure (Torus d) × ProbabilityMeasure (Torus d) =>
      torusWassersteinE 2 (p.1 : Measure (Torus d)) (p.2 : Measure (Torus d))) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  by_cases hy : y = ⊤
  · subst hy
    simp only [Set.Iic_top, Set.preimage_univ]
    exact isClosed_univ
  have hy0 : 0 ≤ y.toReal := ENNReal.toReal_nonneg
  set K : Set (ProbabilityMeasure (Torus d) × ProbabilityMeasure (Torus d) ×
      ProbabilityMeasure (Torus d × Torus d)) :=
    {q | gfb2_m1 q.2.2 = q.1 ∧ gfb2_m2 q.2.2 = q.2.1 ∧ gfb2_cost q.2.2 ≤ y.toReal ^ 2} with hK
  have hKc : IsCompact K := by
    refine IsClosed.isCompact ?_
    refine ((isClosed_eq (gfb2_m1_cont.comp (continuous_snd.comp continuous_snd)) continuous_fst).inter
      ((isClosed_eq (gfb2_m2_cont.comp (continuous_snd.comp continuous_snd))
        (continuous_fst.comp continuous_snd)).inter ?_))
    exact isClosed_le (gfb2_cost_cont.comp (continuous_snd.comp continuous_snd)) continuous_const
  have himg : IsCompact ((fun q : ProbabilityMeasure (Torus d) × ProbabilityMeasure (Torus d) ×
      ProbabilityMeasure (Torus d × Torus d) => (q.1, q.2.1)) '' K) :=
    hKc.image (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  convert himg.isClosed using 1
  ext ⟨μ, ν⟩
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_image]
  constructor
  · intro h
    obtain ⟨π, h1, h2, hW⟩ := gfb2_W_attained μ ν
    refine ⟨(μ, ν, π), ⟨h1, h2, ?_⟩, rfl⟩
    rw [hW] at h
    have : Real.sqrt (gfb2_cost π) ≤ y.toReal := by
      have := ENNReal.toReal_mono hy h
      rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
    exact (Real.sqrt_le_left hy0).1 this
  · rintro ⟨q, ⟨h1, h2, h3⟩, hq⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    refine (gfb2_W_le_cost _ _ q.2.2 h1 h2).trans ?_
    calc ENNReal.ofReal (Real.sqrt (gfb2_cost q.2.2)) ≤ ENNReal.ofReal y.toReal :=
          ENNReal.ofReal_le_ofReal ((Real.sqrt_le_left hy0).2 h3)
      _ = y := ENNReal.ofReal_toReal hy


/-- The empirical measure as a probability measure. -/
def gfb2_empPM {N : ℕ} (hN : 0 < N) (x : Config d N) : ProbabilityMeasure (Torus d) :=
  ⟨empirical x, empirical_isProbabilityMeasure hN x⟩

theorem gfb2_empPM_cont {N : ℕ} (hN : 0 < N) : Continuous (gfb2_empPM (d := d) hN) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  have e : (fun x : Config d N => ∫ ω, f ω ∂((gfb2_empPM hN x : ProbabilityMeasure (Torus d)) : Measure (Torus d))) =
      fun x => (N : ℝ)⁻¹ * ∑ i, f (x i) := by
    funext x
    exact integral_empirical x f.continuous
  rw [e]
  exact continuous_const.mul (continuous_finset_sum _ fun i _ => f.continuous.comp (continuous_apply i))

/-- The mean-field density `ρ_N^{r}` (time clamped to `[0,T]`) as a probability measure. -/
def gfb2_rhoPM (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ) (r : ℝ) :
    ProbabilityMeasure (Torus d) :=
  ⟨withDensityReal (S.ρ N (Q54c.clampT S.T r)),
    isProb_withDensityReal ((hMF N).1.density _ (Q54c.clampT_mem S.hT.le r))⟩

theorem gfb2_rhoPM_cont (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ) :
    Continuous (gfb2_rhoPM S M hMF N) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  have hT := S.hT.le
  have e : (fun r : ℝ => ∫ ω, f ω ∂((gfb2_rhoPM S M hMF N r : ProbabilityMeasure (Torus d)) : Measure (Torus d))) =
      fun r => ∫ x, f x * S.ρ N (Q54c.clampT S.T r) x := by
    funext r
    have hp := (hMF N).1.density _ (Q54c.clampT_mem hT r)
    show ∫ ω, f ω ∂(withDensityReal (S.ρ N (Q54c.clampT S.T r))) = _
    rw [integral_withDensityReal_eq _ hp.measurable hp.nonneg]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [e]
  exact (gfb2_weak S M hMF N f f.continuous).comp_continuous (Q54c.continuous_clampT S.T)
    (fun r => Q54c.clampT_mem hT r)

theorem gfb2_W_meas (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 0 < N) :
    Measurable fun p : Config d N × ℝ =>
      torusWassersteinE 2 (empirical p.1) (withDensityReal (S.ρ N (Q54c.clampT S.T p.2))) := by
  have hc : Continuous fun p : Config d N × ℝ => (gfb2_empPM hN p.1, gfb2_rhoPM S M hMF N p.2) :=
    ((gfb2_empPM_cont hN).comp continuous_fst).prodMk ((gfb2_rhoPM_cont S M hMF N).comp continuous_snd)
  have hl := LowerSemicontinuous.comp gfb2_W_lsc hc
  exact hl.measurable

end HRS.GF
