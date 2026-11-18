import HRS.MP.SelfSimP5FpA

/-!
# MPP5FP, part B: transport of the probabilistic data (Brownian filtration, solution)

Namespace `HRS.MP.SelfSimP5Fp`, helpers `p5f_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Fp

variable {N : ℕ}

theorem p5f_pi_reindex (γ : Measure ℝ) [SigmaFinite γ] :
    (Measure.pi fun _ : Fin N × Fin 1 => γ) =
      (Measure.pi fun _ : Fin N => γ).map (fun (f : Fin N → ℝ) (p : Fin N × Fin 1) => f p.1) := by
  refine Measure.pi_eq fun s hs => ?_
  have hm : Measurable (fun (f : Fin N → ℝ) (p : Fin N × Fin 1) => f p.1) :=
    measurable_pi_iff.2 fun p => measurable_pi_apply p.1
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (f : Fin N → ℝ) (p : Fin N × Fin 1) => f p.1) ⁻¹' (Set.pi Set.univ s) =
      Set.pi Set.univ fun i : Fin N => s (i, 0) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i; exact h (i, 0)
    · intro h p
      have : p.2 = 0 := Subsingleton.elim _ _
      have hp : p = (p.1, 0) := Prod.ext rfl this
      rw [hp]; exact h p.1
  rw [this, Measure.pi_pi, Fintype.prod_prod_type]
  simp

/-! ### The filtration frozen at time `0` for negative times, and the reindexed Brownian motion -/

/-- `ℱ' t = ℱ (max t 0)`: the filtration `ℱ` frozen at `ℱ 0` for `t < 0` (so that `ofNNRealTime` of an
`ℱ 0`-measurable initial value is adapted at negative times). -/
def p5f_fil {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' _ _ hst := ℱ.mono (max_le_max hst le_rfl)
  le' t := ℱ.le _

theorem p5f_fil_coe {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) (t : ℝ≥0) :
    p5f_fil ℱ (t : ℝ) = ℱ (t : ℝ) := by
  show ℱ (max (t : ℝ) 0) = ℱ (t : ℝ)
  rw [max_eq_left (NNReal.coe_nonneg t)]

theorem p5f_fil_of_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) {t : ℝ}
    (ht : 0 ≤ t) : p5f_fil ℱ t = ℱ t := by
  show ℱ (max t 0) = ℱ t
  rw [max_eq_left ht]

/-- The noise reindexed along `Fin N × Fin 1 → Fin N`. -/
def p5f_W' {Ω : Type*} (B : ℝ≥0 → Ω → Fin N → ℝ) : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ :=
  fun t ζ p => B t ζ p.1

theorem p5f_brownian {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {B : ℝ≥0 → Ω → Fin N → ℝ} (hB : IsBrownianFiltration P ℱ B) :
    IsBrownianFiltration P (p5f_fil ℱ) (p5f_W' B) := by
  have hproj : Measurable (fun (f : Fin N → ℝ) (p : Fin N × Fin 1) => f p.1) :=
    measurable_pi_iff.2 fun p => measurable_pi_apply p.1
  refine ⟨fun t s hs h0 => hB.complete (max t 0) s hs h0, fun t => ?_, fun ζ => ?_, fun ζ => ?_,
    fun s t hst => ?_, fun s t hst => ?_⟩
  · have h := hB.adapted t
    rw [← p5f_fil_coe] at h
    exact hproj.comp h
  · funext p; simp [p5f_W', hB.zero]
  · exact continuous_pi fun p => continuous_pi_iff.1 (hB.cont ζ) p.1
  · rw [p5f_fil_coe]
    refine indep_of_indep_of_le_left (hB.indep_incr s t hst) ?_
    have : MeasurableSpace.comap (fun ζ => p5f_W' B t ζ - p5f_W' B s ζ) inferInstance =
        MeasurableSpace.comap (fun ζ => B t ζ - B s ζ)
          (MeasurableSpace.comap (fun (f : Fin N → ℝ) (p : Fin N × Fin 1) => f p.1) inferInstance) := by
      rw [MeasurableSpace.comap_comp]; rfl
    rw [this]
    exact MeasurableSpace.comap_mono hproj.comap_le
  · have hp : HasLaw (fun (f : Fin N → ℝ) (p : Fin N × Fin 1) => f p.1)
        (Measure.pi fun _ : Fin N × Fin 1 => gaussianReal 0 (t - s))
        (Measure.pi fun _ : Fin N => gaussianReal 0 (t - s)) :=
      ⟨hproj.aemeasurable, (p5f_pi_reindex _).symm⟩
    exact hp.comp (hB.gaussian_incr s t hst)

/-! ### The transported solution -/

/-- `Y t ζ = e (Z t ζ)`. -/
def p5f_Y {Ω : Type*} (Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)) : ℝ≥0 → Ω → EucConfig 1 N :=
  fun t ζ => p5f_e N (Z (t : ℝ) ζ)

/-- The noise as a configuration of vectors of `Euc 1`. -/
def p5f_W {Ω : Type*} (B : ℝ≥0 → Ω → Fin N → ℝ) : ℝ≥0 → Ω → (Fin N → Euc 1) :=
  fun t ζ i => EuclideanSpace.single (0 : Fin 1) (B t ζ i)

theorem p5f_Y_filtered {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {B : ℝ≥0 → Ω → Fin N → ℝ} (hB : IsBrownianFiltration P ℱ B) {θ : ℝ}
    {b : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {z₀ : Ω → EuclideanSpace ℝ (Fin N)}
    {Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)} (hZ : ss5_IsSol P ℱ B θ b z₀ Z) :
    IsWholeFilteredSolution P (p5f_fil ℱ) (p5f_W' B) (p5f_W B) (p5f_Y Z) := by
  have hecm : Measurable (p5f_e N) := (p5f_e N).continuous.measurable
  have hadapt : ∀ s : ℝ, Measurable[p5f_fil ℱ s] (ofNNRealTime (p5f_Y Z) s) := fun s => by
    have h : Measurable[ℱ ((Real.toNNReal s : ℝ≥0) : ℝ)] (Z ((Real.toNNReal s : ℝ≥0) : ℝ)) :=
      hZ.2.1 _ (NNReal.coe_nonneg _)
    have e1 : p5f_fil ℱ s = ℱ ((Real.toNNReal s : ℝ≥0) : ℝ) := by
      show ℱ (max s 0) = _
      rw [Real.coe_toNNReal']
    rw [e1]
    exact hecm.comp h
  refine ⟨p5f_brownian hB, Eventually.of_forall fun ζ t i j => ?_, fun t => ?_, ?_⟩
  · have : j = 0 := Subsingleton.elim _ _
    subst this
    simp [p5f_W', p5f_W]
  · have h := hZ.2.1 t t.2
    rw [← p5f_fil_coe]  at h
    exact hecm.comp h
  · refine (StronglyAdapted.isStronglyProgressive_of_continuous (fun s => (hadapt s).stronglyMeasurable)
      (fun ζ => ?_)).isProgressive
    show Continuous fun s : ℝ => p5f_e N (Z ((Real.toNNReal s : ℝ≥0) : ℝ) ζ)
    exact (p5f_e N).continuous.comp ((hZ.1 ζ).comp (NNReal.continuous_coe.comp continuous_real_toNNReal))

theorem p5f_addSol {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {B : ℝ≥0 → Ω → Fin N → ℝ} (hB : IsBrownianFiltration P ℱ B)
    {U : EuclideanSpace ℝ (Fin N) → ℝ} (hgc : Continuous (gradient U)) {θ : ℝ}
    {z₀ : Ω → EuclideanSpace ℝ (Fin N)} {Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)}
    (hZ : ss5_IsSol P ℱ B θ (fun z => -(gradient U z)) z₀ Z) (S : ℝ) :
    P4AddSol P θ (p5f_b U) S (p5f_fil ℱ) (p5f_W' B) (p5f_W B) (p5f_Y Z) := by
  refine ⟨p5f_Y_filtered hB hZ, fun ζ => ?_, ?_⟩
  · exact (p5f_e N).continuous.comp ((hZ.1 ζ).comp NNReal.continuous_coe)
  · filter_upwards [hZ.2.2] with ζ hζ t _
    have hfc : Continuous fun r : ℝ => -(gradient U (Z r ζ)) := (hgc.comp (hZ.1 ζ)).neg
    have hb : ∀ r ∈ Icc (0 : ℝ) t, p5f_b U r (p5f_Y Z (Real.toNNReal r) ζ) =
        p5f_e N (-(gradient U (Z r ζ))) := fun r hr => by
      simp only [p5f_b, p5f_Y, ContinuousLinearEquiv.symm_apply_apply, Real.coe_toNNReal r hr.1]
    have hcomp : ∀ i : Fin N, ∃ L : EuclideanSpace ℝ (Fin N) →L[ℝ] Euc 1,
        ∀ v, L v = EuclideanSpace.single (0 : Fin 1) (v i) ∧ p5f_e N v i = L v := fun i =>
      ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc 1) i).comp
        ((p5f_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N)), fun v => ⟨rfl, rfl⟩⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    all_goals obtain ⟨L, hL⟩ := hcomp i
    · have hc : Continuous fun r : ℝ => L (-(gradient U (Z r ζ))) := L.continuous.comp hfc
      refine (hc.integrableOn_Icc (a := 0) (b := (t : ℝ))).congr_fun (fun r hr => ?_) measurableSet_Icc
      rw [hb r hr, (hL _).2]
    · have hc : Integrable (fun r : ℝ => -(gradient U (Z r ζ))) (volume.restrict (Icc (0 : ℝ) t)) :=
        (hfc.integrableOn_Icc)
      have h1 : ∫ r in Icc (0 : ℝ) t, p5f_b U r (p5f_Y Z (Real.toNNReal r) ζ) i =
          L (∫ r in (0 : ℝ)..t, -(gradient U (Z r ζ))) := by
        rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t), ← integral_Icc_eq_integral_Ioc,
          ← L.integral_comp_comm hc]
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        rw [hb r hr, (hL _).2]
      rw [h1]
      have h0 := hζ 0 le_rfl
      have ht := hζ t t.2
      have hB0 : B 0 ζ = 0 := hB.zero ζ
      simp only [intervalIntegral.integral_same, add_zero, Real.toNNReal_zero, hB0] at h0
      rw [Real.toNNReal_coe] at ht
      have hY : ∀ s : ℝ≥0, p5f_Y Z s ζ i = L (Z (s : ℝ) ζ) := fun s => (hL _).2
      rw [hY t, hY 0, NNReal.coe_zero, ht, h0]
      have hLx : L (WithLp.toLp 2 (B t ζ)) = EuclideanSpace.single (0 : Fin 1) (B t ζ i) := (hL _).1
      have h00 : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = 0 := by ext j; simp
      simp only [map_add, map_smul, hLx, p5f_W, hB0, Pi.zero_apply, h00, sub_zero]
      simp only [WithLp.toLp_zero, map_zero, smul_zero, add_zero]

end HRS.MP.SelfSimP5Fp
