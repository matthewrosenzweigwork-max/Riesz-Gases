import HRS.MS.MfeConfAux98
import HRS.MD.EQLawPath1

/-!
# S.B.1, packet F9 (part 2): the solution functional on path space and the law representation

For a globally Lipschitz drift `b` and the noise map `σ`, the Picard limit `Ψ_t(x, w) = picardLim b σ w x t` is a jointly
measurable function of the initial value `x` and the continuous noise path `w ∈ C(ℝ≥0, ℝ^{N×d})` (`sb1_picLim_meas`).  If `Y` is a
strong solution on a Brownian filtration with `ℱ_0`-measurable initial value `Y₀`, then a.s. `Y_t = Ψ_t(Y₀, path)`
(`sb1_sol_eq_picLim`) and, by the independence of `ℱ_0` and the Brownian path, the law of `Y_t` is the image of
`law(Y₀) ⊗ Wiener` under `Ψ_t` (`sb1_law_repr`).  The flow is therefore linear in the initial law (`sb1_flow_mono`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

open HRS HRS.MD.EQLawPath

section Meas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] {ι : Type*} [Fintype ι]

theorem sb1_addNoise_meas (σ : ι → E) (t : ℝ) :
    Measurable (fun p : E × C(ℝ≥0, ι → ℝ) => addNoise σ (fun s => p.2 s) t) := by
  unfold addNoise
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((measurable_pi_apply k).comp ((ContinuousMap.measurable_eval (Real.toNNReal t)).comp measurable_snd))).smul_const (σ k)

theorem sb1_pic_meas (bt : ℝ → E → E) (hbt : IsLipschitzDrift bt) (σ : ι → E) (n : ℕ) :
    ∀ t : ℝ, Measurable (fun p : E × C(ℝ≥0, ι → ℝ) => picardIter bt σ (fun s => p.2 s) p.1 n t) := by
  induction n with
  | zero =>
    intro t
    simp only [picardIter]
    exact measurable_fst.add (sb1_addNoise_meas σ t)
  | succ n ih =>
    intro t
    simp only [picardIter]
    refine (measurable_fst.add ?_).add (sb1_addNoise_meas σ t)
    rcases le_or_gt t 0 with ht | ht
    · have : ∀ p : E × C(ℝ≥0, ι → ℝ), ∫ s in (0:ℝ)..max t 0, bt (max s 0)
          (picardIter bt σ (fun s => p.2 s) p.1 n s) = 0 := by
        intro p; rw [max_eq_right ht]; simp
      simp only [this]; exact measurable_const
    · let G : ℝ → E × C(ℝ≥0, ι → ℝ) → E := fun s p =>
        bt (max s 0) (picardIter bt σ (fun r => p.2 r) p.1 n (min s t))
      have hG : ∀ s, Measurable (G s) := fun s =>
        (hbt.continuous_slice s).measurable.comp (ih (min s t))
      have hc : ∀ p, Continuous fun s => G s p := fun p =>
        continuous_bpos_comp bt hbt
          ((continuous_picardIter bt hbt σ p.2.continuous p.1 n).comp
            (continuous_id.min continuous_const))
      have h := measurable_intervalIntegral_of_continuous G hG hc ht.le
      have e : (fun p : E × C(ℝ≥0, ι → ℝ) => ∫ s in (0:ℝ)..max t 0, bt (max s 0)
          (picardIter bt σ (fun s => p.2 s) p.1 n s)) =
          fun p => ∫ s in (0:ℝ)..t, G s p := by
        ext p
        rw [max_eq_left ht.le]
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le ht.le] at hs
        simp only [G, min_eq_left hs.2]
      rw [e]; exact h

theorem sb1_picLim_meas (bt : ℝ → E → E) (hbt : IsLipschitzDrift bt) (σ : ι → E) (t : ℝ) :
    Measurable (fun p : E × C(ℝ≥0, ι → ℝ) => picardLim bt σ (fun s => p.2 s) p.1 t) :=
  measurable_of_tendsto_metrizable (fun n => sb1_pic_meas bt hbt σ n t)
    (tendsto_pi_nhds.2 fun p => tendsto_picardIter bt hbt σ p.2.continuous p.1 t)

/-- the solution functional `Ψ_t(x,w)` -/
def sb1Ψ (bt : ℝ → E → E) (σ : ι → E) (t : ℝ) (p : E × C(ℝ≥0, ι → ℝ)) : E :=
  picardLim bt σ (fun s => p.2 s) p.1 t

theorem sb1Ψ_meas (bt : ℝ → E → E) (hbt : IsLipschitzDrift bt) (σ : ι → E) (t : ℝ) :
    Measurable (sb1Ψ bt σ t) := sb1_picLim_meas bt hbt σ t

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W' : ℝ≥0 → Ω → ι → ℝ}

/-- a global strong solution is a.s. the Picard limit of its initial value and its noise path -/
theorem sb1_sol_eq_picLim [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W') {bt : ℝ → E → E}
    (hb : IsLipschitzDrift bt) {σ : ι → E} {Y₀ : Ω → E} {Ys : ℝ → Ω → E}
    (hY : IsAdditiveSDESolution P ℱ W' bt σ Y₀ (fun _ => ⊤) Ys) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Ys t ω = picardLim bt σ (fun s => W' s ω) (Y₀ ω) t := by
  filter_upwards [hY.isPathSolution] with ω h t ht
  exact ode_additive_unique Set.univ isOpen_univ bt hb.toLoc σ (fun s => W' s ω) (hW.cont ω) (Y₀ ω) h
    (isPathSolution_picardLim bt hb σ (hW.cont ω) (hW.zero ω) (Y₀ ω)) (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) t ht (by simp)

/-- the joint law of an `ℱ_0`-measurable variable and the Brownian path is the product -/
theorem sb1_joint_law [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W') {Y₀ : Ω → E}
    (hY : Measurable[ℱ 0] Y₀) :
    P.map (fun ω => (Y₀ ω, bfPath hW ω)) = (P.map Y₀).prod (P.map (bfPath hW)) := by
  have hmeas : Measurable Y₀ := hY.mono (ℱ.le _) le_rfl
  have hbf := measurable_bfPath hW
  have hind : IndepFun Y₀ (bfPath hW) P := by
    have h0 := indep_zero_path hW
    have hle : MeasurableSpace.comap (bfPath hW) inferInstance ≤
        MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => W' t ω) inferInstance := by
      rw [measurableSpace_continuousMap_eq, MeasurableSpace.comap_comp]
      exact le_rfl
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right h0 hle) hY.comap_le
  exact (indepFun_iff_map_prod_eq_prod_map_map hmeas.aemeasurable hbf.aemeasurable).1 hind

/-- **law representation**: the law of `Y_t` is the image of `law(Y₀) ⊗ Wiener` under `Ψ_t` -/
theorem sb1_law_repr [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W') {bt : ℝ → E → E}
    (hb : IsLipschitzDrift bt) {σ : ι → E} {Y₀ : Ω → E} (hY0 : Measurable[ℱ 0] Y₀) {Ys : ℝ → Ω → E}
    (hY : IsAdditiveSDESolution P ℱ W' bt σ Y₀ (fun _ => ⊤) Ys) {t : ℝ} (ht : 0 ≤ t) :
    P.map (Ys t) = ((P.map Y₀).prod (P.map (bfPath hW))).map (sb1Ψ bt σ t) := by
  have hae : Ys t =ᵐ[P] fun ω => sb1Ψ bt σ t (Y₀ ω, bfPath hW ω) := by
    filter_upwards [sb1_sol_eq_picLim hW hb hY] with ω h
    exact h t ht
  rw [Measure.map_congr hae, ← sb1_joint_law hW hY0]
  rw [Measure.map_map (sb1Ψ_meas bt hb σ t) ((hY0.mono (ℱ.le _) le_rfl).prodMk (measurable_bfPath hW))]
  rfl

end Meas

end HRS.MS.MfeConf
