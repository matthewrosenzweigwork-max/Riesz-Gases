import HRS.MS.R2WinErrNL3

/-!
# S10.4, nonlinear branch, part 4: the three measurability inputs of `S104RealInput` along a nonlinear trajectory

`s104n_M0`, `s104n_M1`, `s104n_M2` (the nonlinear analogues of `s104_M0_stat`, `s104_M1_stat`, `s104_M2_stat`), from the joint measurability of the
clamped density (`s104n_hjm`), the classical adjoint solutions and the joint continuity `S104nOrbit.jcont`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.GenPath HRS.MS.R2GenInit

variable {d N : ℕ}

lemma s104n_gradient_meas (f : Euc d → ℝ) : Measurable fun x => gradient f x := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)

section Meas

variable {s m : ℝ} {C : WholeCoeff d} {ρ : ℝ → Euc d → ℝ} {α : MultiIndex d} {T0 b : ℝ}
  {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N) (hprog : IsProgressive ℱ (ofNNRealTime X))

set_option maxHeartbeats 1600000 in
include hprog in
theorem s104n_M0 (horb : S104nOrbit C (oscTestFun m α) T0)
    (hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp T0 p.1) p.2)
    (hρp : ∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t)) (hb : 0 ≤ b) (hbT : b ≤ T0) :
    AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α b p.2 p.1|)
      (P.prod (volume.restrict (Icc (0 : ℝ) b))) := by
  have hcl := s104n_prop_cl (horb.ex0 b ⟨hb, hbT⟩)
  have hK := s105_kernel_meas (d := d) s C hb hcl
  have hρm' : Measurable fun q : ℝ × Euc d => ρ (mrrClamp T0 q.1) q.2 := hρm
  have hρp' : ∀ θ : ℝ, HRS.Whole.IsProbDensity (ρ (mrrClamp T0 θ)) :=
    fun θ => hρp _ (mrrClamp_mem (hb.trans hbT) θ).1
  have hcpf := s104n_cpf_meas (N := N) (Θ := ℝ)
    (K := fun r => commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp b r) b (oscTestFun m α)) x))
    hK hρm' hρp'
  have hF : Measurable fun q : ℝ × EucConfig d N => |centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp b q.1) b (oscTestFun m α)) x)) q.2
      (HRS.Whole.withDensityReal (ρ (mrrClamp T0 q.1)))| := hcpf.abs
  have h := s56_aemeas_of_clamp P ℱ X hprog hb (fun q => |centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp b q.1) b (oscTestFun m α)) x)) q.2
      (HRS.Whole.withDensityReal (ρ (mrrClamp T0 q.1)))|) hF
  refine (h.ennreal_ofReal).congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict (Icc (0 : ℝ) b))), p.2 ∈ Icc (0 : ℝ) b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hq] with p hp
  have h1 : mrrClamp b p.2 = p.2 := mrrClamp_of_mem hp
  have h2 : mrrClamp T0 p.2 = p.2 := mrrClamp_of_mem ⟨hp.1, hp.2.trans hbT⟩
  unfold r2CommForcingMov
  simp only [h1, h2]

set_option maxHeartbeats 1600000 in
include hprog in
theorem s104n_M1 (horb : S104nOrbit C (oscTestFun m α) T0)
    (hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp T0 p.1) p.2)
    (hρp : ∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t)) (hb : 0 ≤ b) (hbT : b ≤ T0) :
    AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α p.2 p.2 p.1|)
      (P.prod (volume.restrict (Icc b T0))) := by
  have hT0 : 0 ≤ T0 := hb.trans hbT
  have hv : Measurable fun q : ℝ × Euc d => (fun x => gradient (oscTestFun m α) x) q.2 :=
    (s104n_gradient_meas _).comp measurable_snd
  have hK := s104n_kernel_meas_of (Θ := ℝ) s (v := fun _ x => gradient (oscTestFun m α) x) hv
  have hρp' : ∀ θ : ℝ, HRS.Whole.IsProbDensity (ρ (mrrClamp T0 θ)) :=
    fun θ => hρp _ (mrrClamp_mem hT0 θ).1
  have hcpf := s104n_cpf_meas (N := N) (Θ := ℝ)
    (K := fun _ => commutatorKernel d s (fun x => gradient (oscTestFun m α) x)) hK hρm hρp'
  have hF : Measurable fun q : ℝ × EucConfig d N => |centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (oscTestFun m α) x)) q.2
      (HRS.Whole.withDensityReal (ρ (mrrClamp T0 q.1)))| := hcpf.abs
  have h := s56_aemeas_of_clamp P ℱ X hprog hT0 (fun q => |centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (oscTestFun m α) x)) q.2
      (HRS.Whole.withDensityReal (ρ (mrrClamp T0 q.1)))|) hF
  refine s104_aem_mono (A := Icc (0 : ℝ) T0) (Icc_subset_Icc_left hb) ?_
  refine (h.ennreal_ofReal).congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T0))), p.2 ∈ Icc (0 : ℝ) T0 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hq] with p hp
  have h2 : mrrClamp T0 p.2 = p.2 := mrrClamp_of_mem hp
  have hterm : propagatorW C p.2 p.2 (oscTestFun m α) = oscTestFun m α :=
    (s104n_prop_cl (horb.ex0 p.2 hp)).terminal
  unfold r2CommForcingMov
  simp only [h2, hterm]

open Classical in
set_option maxHeartbeats 3200000 in
include hprog in
theorem s104n_M2 (horb : S104nOrbit C (oscTestFun m α) T0)
    (hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp T0 p.1) p.2)
    (hρp : ∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t)) (hb : 0 ≤ b) (hbT : b ≤ T0) :
    AEMeasurable (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |s104_F2 C s m ρ X α p.2 p.1|)
      (P.prod (volume.restrict ((Icc b T0) ×ˢ (Icc (0 : ℝ) T0)))) := by
  have hT0 : 0 ≤ T0 := hb.trans hbT
  set Sset : Set (ℝ × ℝ × Euc d) := {q | 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T0} with hSset
  have hSm : MeasurableSet Sset := by
    refine MeasurableSet.inter (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)) ?_
    exact MeasurableSet.inter (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst)
      (measurableSet_le measurable_fst measurable_const)
  have hVm : Measurable (Sset.piecewise (fun q : ℝ × ℝ × Euc d =>
      gradient (propagatorW C q.2.1 q.1 (generatorW C q.1 (oscTestFun m α))) q.2.2) (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise horb.jcont continuousOn_const hSm
  set v : ℝ × ℝ → Euc d → Euc d := fun θ x => Sset.piecewise (fun q : ℝ × ℝ × Euc d =>
      gradient (propagatorW C q.2.1 q.1 (generatorW C q.1 (oscTestFun m α))) q.2.2) (fun _ => 0)
      (θ.1, θ.2, x) with hv
  have hvm : Measurable fun q : (ℝ × ℝ) × Euc d => v q.1 q.2 :=
    hVm.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hK := s104n_kernel_meas_of (Θ := ℝ × ℝ) s hvm
  have hρm' : Measurable fun q : (ℝ × ℝ) × Euc d => ρ (mrrClamp T0 q.1.2) q.2 :=
    hρm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hρp' : ∀ θ : ℝ × ℝ, HRS.Whole.IsProbDensity (ρ (mrrClamp T0 θ.2)) :=
    fun θ => hρp _ (mrrClamp_mem hT0 θ.2).1
  have hcpf := s104n_cpf_meas (N := N) (Θ := ℝ × ℝ) (K := fun θ => commutatorKernel d s (v θ)) hK hρm' hρp'
  have hE : Measurable fun p : Ω × (ℝ × ℝ) => X (Real.toNNReal (mrrClamp T0 p.2.2)) p.1 :=
    (mrr_prog_meas ℱ X hprog hT0).comp (measurable_snd.comp measurable_snd |>.prodMk measurable_fst)
  have hΨ : Measurable fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |if p.2.2 ≤ p.2.1 then
      centeredPairFunctional (commutatorKernel d s (v p.2)) (X (Real.toNNReal (mrrClamp T0 p.2.2)) p.1)
        (HRS.Whole.withDensityReal (ρ (mrrClamp T0 p.2.2))) else 0| := by
    refine ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp ?_)
    refine Measurable.ite (measurableSet_le (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_snd)) ?_ measurable_const
    have hg : Measurable fun p : Ω × (ℝ × ℝ) => (p.2, X (Real.toNNReal (mrrClamp T0 p.2.2)) p.1) :=
      measurable_snd.prodMk hE
    have hc := hcpf.comp hg
    simpa only [Function.comp_def] using hc
  refine hΨ.aemeasurable.congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict ((Icc b T0) ×ˢ (Icc (0 : ℝ) T0)))),
      p.2 ∈ (Icc b T0) ×ˢ (Icc (0 : ℝ) T0) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  filter_upwards [hq] with p hp
  obtain ⟨⟨hs1, hs2⟩, hr1, hr2⟩ := hp
  by_cases hle : p.2.2 ≤ p.2.1
  · have hm : mrrClamp T0 p.2.2 = p.2.2 := mrrClamp_of_mem ⟨hr1, hr2⟩
    have hvv : v p.2 = fun x => gradient (propagatorW C p.2.2 p.2.1 (generatorW C p.2.1 (oscTestFun m α))) x := by
      funext x
      simp only [hv]
      rw [Set.piecewise_eq_of_mem]
      exact ⟨hr1, hle, hs2⟩
    unfold s104_F2
    simp only [hle, if_true, hm, hvv]
  · simp only [hle, if_false]
    unfold s104_F2
    simp [hle]

end Meas

end HRS.MS.R2WinErr
