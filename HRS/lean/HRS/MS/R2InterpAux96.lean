import HRS.MS.R2InterpAux95

/-!
# S10.2 (worker S10R), part 96 (packet F5k): the drift density `hh` of the Itô representation is progressive and a.s. locally integrable
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d}

/-- The kernel family attached to an orbit. -/
theorem s102_kernel_pkg {s : ℝ} (hs0 : 0 ≤ s) {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ∃ (hK : ℝ → Euc d → Euc d → ℝ) (B : ℝ), (Measurable fun q : ℝ × Euc d × Euc d => hK q.1 q.2.1 q.2.2) ∧
      (∀ r ∈ Icc (0 : ℝ) t, hK r = commutatorKernel d s (fun x => gradient (f r) x)) ∧
      ∀ r ∈ Icc (0 : ℝ) t, IsBoundedPairKernel s B (hK r) := by
  classical
  obtain ⟨B, hB⟩ := s102_orbit_kernel_bdd hs0 hf
  refine ⟨fun r => commutatorKernel d s (fun x => if r ∈ Icc (0 : ℝ) t then gradient (f r) x else 0), B,
    s102_kernelFam_meas s (fun r x => if r ∈ Icc (0 : ℝ) t then gradient (f r) x else 0) (s102_gradJoint_meas hf),
    fun r hr => ?_, fun r hr => ?_⟩
  · beta_reduce
    simp only [if_pos hr]
  · beta_reduce
    simp only [if_pos hr]
    exact hB r hr

/-- The `i`-th coordinate of the drift of the Itô representation. -/
def s102_bdc (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) (sQ : ℝ) (μ : Measure (Euc d)) {N : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (i : Fin (s102_q d L)) (u : ℝ) (ζ : Ω) : ℝ :=
  if 0 ≤ u then -(Real.sqrt N)⁻¹ * s102_hh C m (s102_tauk hT L) (s102_alk L) (fun v => r2QuadField sQ μ P X v ζ) i u
  else 0

set_option maxHeartbeats 800000 in
theorem s102_bdc_prog_int (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {m T : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hS : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {β p K M Lr : ℝ} (hβ : 0 < β) (hp : 1 < p)
    {ρ : Euc d → ℝ} (hρR : IsRound2Density d s M Lr ρ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsProgressive ℱ (ofNNRealTime X))
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    (i : Fin (s102_q d L)) :
    IsProgressive ℱ (fun u ζ => s102_bdc C m hT L s (HRS.Whole.withDensityReal ρ) P X i u ζ) ∧
      ∀ᵐ ζ ∂P, ∀ T' : ℝ, IntegrableOn (fun u => s102_bdc C m hT L s (HRS.Whole.withDensityReal ρ) P X i u ζ)
        (Icc 0 T') := by
  classical
  set t : ℝ := s102_tk hT L i with ht
  have htT : t ∈ Icc (0 : ℝ) T := (s102_tauk hT L i).2
  have hf := s102_orb_classical hS hT L i
  obtain ⟨hK, B, hKm, hKr, hKb⟩ := s102_kernel_pkg hs0 hf
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hμp : IsProbabilityMeasure μ := HRS.MS.R2Mt.s92_isProb_mu hρR.prob
  have hXm : Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2 :=
    measurable_progressive_min_gen (u := ofNNRealTime X) hX t
  have hdens' : ∀ r ∈ Icc (0 : ℝ) t, HasR2ActualDensity s β p K μ (P.map (X r.toNNReal)) :=
    fun r hr => hdens r ⟨hr.1, hr.2.trans htT.2⟩
  obtain ⟨-, hI2⟩ := s102_quad_prodInt hd hs0 hs M Lr β p K B hβ hp hρR hN P X t hXm hdens' hK hKm hKb
  -- the pointwise description
  set cc : ℝ → ℝ := fun u => ∫ ζ', pairEnergy (hK u) (X (min u t).toNNReal ζ') μ ∂P with hcc
  have hpE : Measurable fun q : ℝ × EucConfig d N => pairEnergy (hK q.1) q.2 μ :=
    HRS.MS.R2Chaos.s94_pairEnergy_measurable hKm
  have hccm : Measurable cc :=
    ((hpE.comp (measurable_fst.prodMk hXm)).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  set R : ℝ → Ω → ℝ := fun u ζ => if u ∈ Icc (0 : ℝ) t then
    -(Real.sqrt N)⁻¹ * ((N : ℝ) * (pairEnergy (hK u) (ofNNRealTime X u ζ) μ - cc u)) else 0 with hR
  have hRe : ∀ u ζ, s102_bdc C m hT L s μ P X i u ζ = R u ζ := by
    intro u ζ
    unfold s102_bdc s102_hh
    simp only [hR]
    by_cases hu : 0 ≤ u
    · by_cases hut : u ≤ t
      · have hmem : u ∈ Icc (0 : ℝ) t := ⟨hu, hut⟩
        rw [if_pos hu, if_pos hmem]
        have : (Iic (s102_tauk hT L i : ℝ)).indicator
            (fun u => r2QuadField s μ P X u ζ (propagatorW C u (s102_tauk hT L i) (oscTestFun m (s102_alk L i)))) u =
            r2QuadField s μ P X u ζ (propagatorW C u t (oscTestFun m (s102_alk L i))) :=
          indicator_of_mem (show u ∈ Iic _ from hut) _
        rw [this]
        simp only [r2QuadField, hcc, min_eq_left hut, ofNNRealTime_apply, hKr u hmem, s102_orb]
        rfl
      · have hmem : u ∉ Icc (0 : ℝ) t := fun h => hut h.2
        rw [if_pos hu, if_neg hmem, indicator_of_notMem (show u ∉ Iic (s102_tauk hT L i : ℝ) from hut)]
        simp
    · have hmem : u ∉ Icc (0 : ℝ) t := fun h => hu h.1
      rw [if_neg hu, if_neg hmem]
  simp_rw [hRe]
  constructor
  · intro j
    have h1 : IsProgressive ℱ (fun u ζ => pairEnergy (hK u) (ofNNRealTime X u ζ) μ) :=
      s102_prog_comp (ℱ := ℱ) (V := fun q : ℝ × EucConfig d N => pairEnergy (hK q.1) q.2 μ) hpE hX
    have h2 := h1 j
    have hfst : Measurable[Subtype.instMeasurableSpace.prod (ℱ j)] fun p : Set.Iic j × Ω => (p.1 : ℝ) :=
      measurable_subtype_coe.comp (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ j))
    have hset : @MeasurableSet _ (Subtype.instMeasurableSpace.prod (ℱ j))
        {p : Set.Iic j × Ω | (p.1 : ℝ) ∈ Icc (0 : ℝ) t} := hfst measurableSet_Icc
    refine Measurable.ite hset ?_ measurable_const
    exact ((h2.sub (hccm.comp hfst)).const_mul _).const_mul _
  · have hfst := hI2.prod_left_ae
    filter_upwards [hfst] with ζ hζ T'
    have hI : IntegrableOn (fun u => R u ζ) (Icc 0 t) := by
      refine IntegrableOn.congr_fun (hζ.const_mul (-(Real.sqrt N)⁻¹)) (fun u hu => ?_) measurableSet_Icc
      simp only [hR, if_pos hu, r2QuadFluct, hcc, ofNNRealTime_apply, min_eq_left hu.2]
      rfl
    refine hI.of_forall_sdiff_eq_zero measurableSet_Icc fun u hu => ?_
    simp only [hR, if_neg hu.2]

end HRS.MS.R2Interp

end
