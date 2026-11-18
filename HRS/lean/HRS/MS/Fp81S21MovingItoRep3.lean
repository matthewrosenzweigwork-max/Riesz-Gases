import HRS.MS.Fp81S21MovingItoRep2

/-!
# HRS S2.1(iii), packet 8.5: moving drift coordinates and Itô representation

This file builds progressivity from the moving pair-energy measurability
interface and obtains pathwise local L¹ through the staged moving M1 drift
bound. It does not invoke the stationary `s102_bdc_prog_int` producer or its
fixed-reference density hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

private def fp81s21_itoClip (H : ℝ) (hH : 0 ≤ H) (u : ℝ) : Icc (0 : ℝ) H :=
  ⟨max 0 (min u H), ⟨le_max_left _ _, max_le hH (min_le_right _ _)⟩⟩

private theorem fp81s21_itoClip_continuous (H : ℝ) (hH : 0 ≤ H) :
    Continuous (fp81s21_itoClip H hH) := by
  exact (continuous_const.max (continuous_id.min continuous_const)).subtype_mk
    (fun u => ⟨le_max_left _ _, max_le hH (min_le_right _ _)⟩)

private theorem fp81s21_itoClip_eq {H u : ℝ} (hH : 0 ≤ H)
    (hu : u ∈ Icc (0 : ℝ) H) :
    (fp81s21_itoClip H hH u : ℝ) = u := by
  change max 0 (min u H) = u
  rw [min_eq_left hu.2, max_eq_right hu.1]

private def fp81s21_itoRho (p : Parameters) {δ H : ℝ}
    (R : Trajectory p δ) (hH : 0 ≤ H) : ℝ → Euc p.d → ℝ :=
  fun u x => R.ρ (fp81s21_itoClip H hH u) x

private def fp81s21_itoKernel (p : Parameters) {δ H : ℝ}
    (R : Trajectory p δ) (hH : 0 < H) (L : ℕ) (sQ : ℝ)
    (i : Fin (s102_q p.d L)) : ℝ → Euc p.d → Euc p.d → ℝ :=
  fun u => commutatorKernel p.d sQ
    (fun x => if u ∈ Icc (0 : ℝ) (s102_tk hH L i) then
      gradient (s102_orb (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L i u) x else 0)

private def fp81s21_itoEnergy (p : Parameters) {δ H : ℝ}
    (R : Trajectory p δ) (hH : 0 < H) (L : ℕ) (sQ : ℝ)
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N)
    (i : Fin (s102_q p.d L)) : ℝ → Ω → ℝ :=
  fun u ζ => pairEnergy (fp81s21_itoKernel p R hH L sQ i u)
    (X (min u H).toNNReal ζ)
    (HRS.Whole.withDensityReal (fp81s21_itoRho p R hH.le u))

private def fp81s21_itoQf (p : Parameters) {δ H : ℝ}
    (R : Trajectory p δ) (hH : 0 < H) (L : ℕ) (sQ : ℝ)
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N)
    (i : Fin (s102_q p.d L)) : ℝ → Ω → ℝ :=
  fun u ζ => (N : ℝ) * (fp81s21_itoEnergy p R hH L sQ P X i u ζ -
    ∫ ζ', fp81s21_itoEnergy p R hH L sQ P X i u ζ' ∂P)

private theorem fp81s21_centered_energy_progressive
    {N : ℕ} {Ω E : Type} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (V : ℝ × E → ℝ) (hV : Measurable V)
    (Y : ℝ → Ω → E) (hY : IsProgressive ℱ Y)
    (hYjoint : Measurable (fun q : ℝ × Ω => Y q.1 q.2)) :
    IsProgressive ℱ (fun u ζ => (N : ℝ) *
      (V (u, Y u ζ) - ∫ ζ', V (u, Y u ζ') ∂P)) := by
  have hE : IsProgressive ℱ (fun u ζ => V (u, Y u ζ)) :=
    s102_prog_comp hV hY
  have hEjoint : Measurable (fun q : ℝ × Ω => V (q.1, Y q.1 q.2)) :=
    hV.comp (measurable_fst.prodMk hYjoint)
  have hEm : Measurable (fun q : ℝ => ∫ ζ', V (q, Y q ζ') ∂P) :=
    (hEjoint.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  intro j
  have hfst : Measurable[Subtype.instMeasurableSpace.prod (ℱ j)]
      (fun q : Set.Iic j × Ω => (q.1 : ℝ)) :=
    measurable_subtype_coe.comp measurable_fst
  have hEbase := hE j
  have hmean : Measurable[Subtype.instMeasurableSpace.prod (ℱ j)]
      (fun q : Set.Iic j × Ω => ∫ ζ', V ((q.1 : ℝ), Y (q.1 : ℝ) ζ') ∂P) :=
    hEm.comp hfst
  exact (hEbase.sub hmean).const_mul _

private theorem fp81s21_moving_qf_matches
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N)
    (L : ℕ) (sQ : ℝ) (i : Fin (s102_q p.d L)) :
    ∀ u ∈ Icc (0 : ℝ) H, u ≤ s102_tk hH L i → ∀ ζ,
      fp81s21_itoQf p R hH L sQ P X i u ζ =
        r2QuadField sQ (r26t3_mu R u) P X u ζ
          (s102_orb (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L i u) := by
  intro u huH hut ζ
  have hclip := fp81s21_itoClip_eq hH.le huH
  have hmin : min u H = u := min_eq_left huH.2
  have hρ : fp81s21_itoRho p R hH.le u = R.ρ u := by
    funext x
    change R.ρ (fp81s21_itoClip H hH.le u) x = R.ρ u x
    rw [hclip]
  have hK : fp81s21_itoKernel p R hH L sQ i u =
      commutatorKernel p.d sQ
        (fun x => gradient (s102_orb (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) hH L i u) x) := by
    funext x y
    simp [fp81s21_itoKernel, huH.1, hut]
  have hXtime : X (min u H).toNNReal = X u.toNNReal := by rw [hmin]
  simp only [fp81s21_itoQf, fp81s21_itoEnergy, hK, hXtime, hρ, r26t3_mu,
    r2QuadField]

/-- The scalar moving drift coordinate is progressive when driven by a filtered
particle path. The reference-density and particle paths are clipped only for
the measurability extension outside the physical interval; on `[0,H]` they are
the exact moving data. -/
private theorem fp81s21_moving_qf_data
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (X : ℝ≥0 → Ω → EucConfig p.d N)
    (hX : IsProgressive ℱ (ofNNRealTime X))
    (hρjoint : Measurable
      (fun q : Icc (0 : ℝ) H × Euc p.d => R.ρ q.1 q.2))
    (L : ℕ) (sQ : ℝ) (i : Fin (s102_q p.d L))
    (hAdj : IsClassicalAdjointW (r26t3_coeff R)
      (s102_tk hH L i) (oscTestFun (wholeSpaceIndex p.d : ℝ)
        (s102_alk L i))
      (s102_orb (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L i)) :
    IsProgressive ℱ (fp81s21_itoQf p R hH L sQ P X i) := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let t : ℝ := s102_tk hH L i
  let ρclip : ℝ → Euc p.d → ℝ := fp81s21_itoRho p R hH.le
  have hclipC : Continuous (fp81s21_itoClip H hH.le) :=
    fp81s21_itoClip_continuous H hH.le
  have hρm : Measurable (fun q : ℝ × Euc p.d => ρclip q.1 q.2) := by
    exact hρjoint.comp
      ((hclipC.measurable.comp measurable_fst).prodMk measurable_snd)
  have hρ0 : ∀ u x, 0 ≤ ρclip u x := by
    intro u x
    have hglobal := R.resulting.global H
    exact (hglobal.density (fp81s21_itoClip H hH.le u)
      (fp81s21_itoClip H hH.le u).property).nonneg x
  have hf : IsClassicalAdjointW C t (oscTestFun m (s102_alk L i))
      (s102_orb C m hH L i) := hAdj
  let V : ℝ → Euc p.d → Euc p.d := fun u x =>
    if u ∈ Icc (0 : ℝ) t then gradient (s102_orb C m hH L i u) x else 0
  have hVm : Measurable (fun q : ℝ × Euc p.d => V q.1 q.2) :=
    s102_gradJoint_meas hf
  let k : ℝ → Euc p.d → Euc p.d → ℝ :=
    fun u => commutatorKernel p.d sQ (V u)
  have hkm : Measurable (fun q : ℝ × Euc p.d × Euc p.d =>
      k q.1 q.2.1 q.2.2) := s102_kernelFam_meas sQ V hVm
  have hpE : Measurable (fun q : ℝ × EucConfig p.d N =>
      pairEnergy (k q.1) q.2 (HRS.Whole.withDensityReal (ρclip q.1))) :=
    fp81s21_moving_pairEnergy_joint_meas hρm hρ0 hkm
  have hXjoint : Measurable (fun q : ℝ × Ω =>
      X (min q.1 H).toNNReal q.2) :=
    measurable_progressive_min_gen (u := ofNNRealTime X) hX H
  let Y : ℝ → Ω → EucConfig p.d N := fun u ζ => X (min u H).toNNReal ζ
  have hYprog : IsProgressive ℱ Y := by
    intro j
    have htime : @Measurable (Set.Iic j × Ω) (Set.Iic j × Ω)
        (Subtype.instMeasurableSpace.prod (ℱ j))
        (Subtype.instMeasurableSpace.prod (ℱ j))
        (fun q : Set.Iic j × Ω =>
          ((⟨min (q.1 : ℝ) H,
            (by
              change min (q.1 : ℝ) H ≤ j
              exact (min_le_left _ _).trans q.1.property)⟩ : Set.Iic j), q.2)) := by
      refine Measurable.prodMk (Measurable.subtype_mk ?_)
        (@measurable_snd (Set.Iic j) Ω Subtype.instMeasurableSpace (ℱ j))
      exact (measurable_subtype_coe.comp measurable_fst).min measurable_const
    change Measurable[Subtype.instMeasurableSpace.prod (ℱ j)]
      (fun q : Set.Iic j × Ω => (ofNNRealTime X) (min (q.1 : ℝ) H) q.2)
    exact (hX j).comp htime
  have hcent : IsProgressive ℱ (fun u ζ => (N : ℝ) *
      (pairEnergy (k u) (Y u ζ) (HRS.Whole.withDensityReal (ρclip u)) -
        ∫ ζ', pairEnergy (k u) (Y u ζ')
          (HRS.Whole.withDensityReal (ρclip u)) ∂P)) :=
    fp81s21_centered_energy_progressive (N := N) (Ω := Ω)
      (E := EucConfig p.d N) P
    (fun q : ℝ × EucConfig p.d N =>
      pairEnergy (k q.1) q.2 (HRS.Whole.withDensityReal (ρclip q.1)))
    hpE Y hYprog hXjoint
  change IsProgressive ℱ (fun u ζ => (N : ℝ) *
    (pairEnergy (k u) (Y u ζ) (HRS.Whole.withDensityReal (ρclip u)) -
      ∫ ζ', pairEnergy (k u) (Y u ζ')
        (HRS.Whole.withDensityReal (ρclip u)) ∂P))
  exact hcent

theorem fp81s21_moving_bdc_progressive
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (X : ℝ≥0 → Ω → EucConfig p.d N)
    (hX : IsProgressive ℱ (ofNNRealTime X))
    (hρjoint : Measurable
      (fun q : Icc (0 : ℝ) H × Euc p.d => R.ρ q.1 q.2))
    (L : ℕ) (sQ : ℝ) (i : Fin (s102_q p.d L))
    (hAdj : IsClassicalAdjointW (r26t3_coeff R)
      (s102_tk hH L i) (oscTestFun (wholeSpaceIndex p.d : ℝ)
        (s102_alk L i))
      (s102_orb (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L i)) :
    IsProgressive ℱ (fun u ζ => fp81s21_moving_bdc p R hH L sQ P X i u ζ) := by
  classical
  let qf := fp81s21_itoQf p R hH L sQ P X i
  have hqfprog : IsProgressive ℱ qf := by
    exact fp81s21_moving_qf_data p R hH P X hX hρjoint L sQ i hAdj
  have hquad := fp81s21_moving_qf_matches p R hH P X L sQ i
  let t : ℝ := s102_tk hH L i
  have hEq : ∀ u ζ,
      fp81s21_moving_bdc p R hH L sQ P X i u ζ =
        if u ∈ Icc (0 : ℝ) H ∧ u ≤ t then
          -(Real.sqrt N)⁻¹ * qf u ζ else 0 := by
    intro u ζ
    by_cases huH : u ∈ Icc (0 : ℝ) H
    · by_cases hut : u ≤ t
      · rw [if_pos ⟨huH, hut⟩]
        have hut' : u ≤ s102_tk hH L i := by simpa [t] using hut
        have hstop : u ∈ Iic (s102_tauk hH L i : ℝ) := by
          simpa [s102_tk] using hut'
        unfold fp81s21_moving_bdc
        rw [if_pos huH]
        unfold s102_hh
        rw [Set.indicator_of_mem hstop]
        have hq := hquad u huH hut' ζ
        simpa [s102_orb, s102_tk] using
          (congrArg (fun z => -(Real.sqrt N)⁻¹ * z) hq.symm)
      · have hstop : u ∉ Iic (s102_tauk hH L i : ℝ) := by
          intro h
          exact hut (by simpa [t, s102_tk] using h)
        rw [if_neg (show ¬ (u ∈ Icc (0 : ℝ) H ∧ u ≤ t) from fun h => hut h.2)]
        unfold fp81s21_moving_bdc
        rw [if_pos huH]
        unfold s102_hh
        rw [Set.indicator_of_notMem hstop]
        simp
    · rw [if_neg (show ¬ (u ∈ Icc (0 : ℝ) H ∧ u ≤ t) from fun h => huH h.1)]
      unfold fp81s21_moving_bdc
      rw [if_neg huH]
  intro j
  by_cases hj : 0 ≤ j
  · have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ j)]
        {q : Set.Iic j × Ω | (q.1 : ℝ) ∈ Icc (0 : ℝ) H ∧
          (q.1 : ℝ) ≤ t} := by
      have hfst : Measurable[Subtype.instMeasurableSpace.prod (ℱ j)]
          (fun q : Set.Iic j × Ω => (q.1 : ℝ)) :=
        measurable_subtype_coe.comp measurable_fst
      exact hfst measurableSet_Icc |>.inter (hfst measurableSet_Iic)
    have hval : Measurable[Subtype.instMeasurableSpace.prod (ℱ j)]
        (fun q : Set.Iic j × Ω =>
          if (q.1 : ℝ) ∈ Icc (0 : ℝ) H ∧ (q.1 : ℝ) ≤ t then
            -(Real.sqrt N)⁻¹ * qf (q.1 : ℝ) q.2 else 0) := by
      exact Measurable.ite hset ((hqfprog j).const_mul _) measurable_const
    have hEqj : (fun q : Set.Iic j × Ω =>
        fp81s21_moving_bdc p R hH L sQ P X i q.1 q.2) =
      (fun q => if (q.1 : ℝ) ∈ Icc (0 : ℝ) H ∧ (q.1 : ℝ) ≤ t then
        -(Real.sqrt N)⁻¹ * qf (q.1 : ℝ) q.2 else 0) := by
      funext q
      exact hEq q.1 q.2
    rw [hEqj]
    exact hval
  · have hzero : (fun q : Set.Iic j × Ω =>
        fp81s21_moving_bdc p R hH L sQ P X i q.1 q.2) =
      (fun _ => (0 : ℝ)) := by
      funext q
      have hneg : (q.1 : ℝ) < 0 :=
        lt_of_le_of_lt q.1.property (lt_of_not_ge hj)
      simp [fp81s21_moving_bdc, hneg]
    rw [hzero]
    exact measurable_const

#print axioms HRS.Fp81.S21.fp81s21_moving_bdc_progressive

end HRS.Fp81.S21

end
