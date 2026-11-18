import HRS.MS.R2InterpAux103

/-!
# S10.2 (worker S10R), part 104 (packet M3f): measurability of the initial propagation `𝖨ζ_N^0` and (a.e.) of the path `ζ_N`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_zf_meas {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) (u : ℝ) {g : Euc d → ℝ} (hg : Measurable g) :
    Measurable fun ζ => s102_zf P X ζ u g := by
  unfold s102_zf
  exact (((s102_pairEmp_meas hN hg).comp (hXm u.toNNReal)).sub_const _).const_mul _

theorem s102_y0_eval_meas (hs : S102Std C m T r c) (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m T) (hT : 0 < T)
    (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (hmom : Integrable (fun x : Euc d => jbracket x ^ Pw) (HRS.Whole.meanEmpirical (P.map (X 0))))
    (t : Icc (0 : ℝ) T) : Measurable fun ζ => OscPath.at' (s102_y0 C m T P X ζ) t := by
  have hz : ∀ ζ, S102Z r Pw (s102_zf P X ζ 0) := fun ζ => s102_Z_zf hd hP0 hr hN P X 0 (by simpa using hmom) ζ
  have hy : ∀ ζ, s102_y0 C m T P X ζ = r2InitProp C m T (s102_zf P X ζ 0) := by
    intro ζ
    unfold s102_y0 s102_zf
    simp only [Real.toNNReal_zero]
  have ht0 : (t : ℝ) ∈ Icc (0 : ℝ) T := t.2
  have hmem : ∀ ζ, Memℓp (fun α : MultiIndex d => s102_zf P X ζ 0 (propagatorW C 0 t (oscTestFun m α))) 2 :=
    fun ζ => s102_z_orbit_memℓp hP hs.hD (hz ζ) ⟨le_rfl, hT.le⟩ ⟨ht0.1, ht0.2⟩
  have hfun : (fun ζ => OscPath.at' (s102_y0 C m T P X ζ) t) = fun ζ =>
      (show OscDual d m from (⟨fun α => s102_zf P X ζ 0 (propagatorW C 0 t (oscTestFun m α)), hmem ζ⟩ :
        lp (fun _ : MultiIndex d => ℝ) 2)) := by
    funext ζ
    rw [← s102_r2PathAt_of_mem _ ht0, hy ζ, s102_initProp_at hP hs.hD hlin (hz ζ) hT.le ht0]
    apply s102_ext
    intro α
    rw [s102_Vprop_coord hP hs.hD (hz ζ) hlin ⟨le_rfl, hT.le⟩ ⟨ht0.1, ht0.2⟩ α]
    rfl
  rw [hfun]
  refine s102_measurable_lp _ hmem fun α => ?_
  refine s102_zf_meas hN P X hXm 0 ?_
  exact ((s102_propagator_classical (hs.hcls α t ht0)).c2 0 ⟨le_rfl, ht0.1⟩).continuous.measurable


theorem s102_y0_meas (hs : S102Std C m T r c) (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m T) (hT : 0 < T)
    (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (hmom : Integrable (fun x : Euc d => jbracket x ^ Pw) (HRS.Whole.meanEmpirical (P.map (X 0)))) :
    Measurable fun ζ => s102_y0 C m T P X ζ := by
  have key : Measurable (fun ζ => (show C(Icc (0 : ℝ) T, OscDual d m) from s102_y0 C m T P X ζ)) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact s102_y0_eval_meas hs hP hlin hT hd hP0 hr hN P X hXm hmom t
  exact key

theorem s102_zetaB_meas (hm : (d : ℝ) < m) {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) (u : ℝ) :
    Measurable fun ζ => zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ) := by
  have hmem : ∀ ζ, Memℓp (fun α : MultiIndex d => s102_zf P X ζ u (oscTestFun m α)) 2 := by
    intro ζ
    have := lp.memℓp (show lp (fun _ : MultiIndex d => ℝ) 2 from zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ))
    convert this using 1
    funext α
    exact (s102_coord_zetaB hm hN P X hXm u ζ α).symm
  have hfun : (fun ζ => zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ)) = fun ζ =>
      (show OscDual d m from (⟨fun α => s102_zf P X ζ u (oscTestFun m α), hmem ζ⟩ :
        lp (fun _ : MultiIndex d => ℝ) 2)) := by
    funext ζ
    apply s102_ext
    intro α
    rw [s102_coord_zetaB hm hN P X hXm u ζ α]
    rfl
  rw [hfun]
  refine s102_measurable_lp _ hmem fun α => ?_
  exact s102_zf_meas hN P X hXm u (measurable_const.mul (contDiff_hermiteFunD α).continuous.measurable)

theorem s102_zetaPath_aemeas (hm : (d : ℝ) < m) {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i) :
    AEMeasurable (fun ζ => zetaPathW m T 0 P X ζ) P := by
  classical
  have hcz := s102_zeta_cont hm hN P X hXm hcont
  obtain ⟨B', hsub, hB'm, hB'0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcz)
  set g : Ω → OscPath d m T := fun ζ => if ζ ∈ B' then 0 else zetaPathW m T 0 P X ζ with hg
  have hwat : ∀ ζ, ζ ∉ B' → ∀ t : Icc (0 : ℝ) T,
      OscPath.at' (zetaPathW m T 0 P X ζ) t = zetaB m (P.map (X (t : ℝ).toNNReal)) (X (t : ℝ).toNNReal ζ) := by
    intro ζ hζ t
    have hc : Continuous fun u : ℝ => zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ) := by
      by_contra h
      exact hζ (hsub h)
    rw [← s102_r2PathAt_of_mem _ t.2]
    exact s102_windowPathOf_at (f := fun u : ℝ => zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ))
      hc.continuousOn t.2
  refine ⟨g, ?_, ?_⟩
  · have key : Measurable (fun ζ => (show C(Icc (0 : ℝ) T, OscDual d m) from g ζ)) := by
      refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
      have : (fun ζ => OscPath.at' (g ζ) t) = fun ζ => if ζ ∈ B' then (0 : OscDual d m) else
          zetaB m (P.map (X (t : ℝ).toNNReal)) (X (t : ℝ).toNNReal ζ) := by
        funext ζ
        by_cases hζ : ζ ∈ B'
        · simp [hg, hζ, OscPath.at']
          rfl
        · simp only [hg, hζ, if_false]
          exact hwat ζ hζ t
      show Measurable fun ζ => OscPath.at' (g ζ) t
      rw [this]
      exact Measurable.ite hB'm measurable_const (s102_zetaB_meas hm hN P X hXm _)
    exact key
  · have : ∀ᵐ ζ ∂P, ζ ∉ B' := by
      rw [ae_iff]; simpa using hB'0
    filter_upwards [this] with ζ hζ
    simp [hg, hζ]

end HRS.MS.R2Interp

end
