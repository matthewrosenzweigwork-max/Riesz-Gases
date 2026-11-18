import HRS.MC.E213Q1
import HRS.Main.T25PAux29
import HRS.Main.T25Aux1
import HRS.Sections.AdjKGlue

/-!
# Packet e213q, GS-3b: finite-dimensional Gaussianity of linear fluctuation solutions

For `Y` an `IsLinearFluctuationSolution` with centred Gaussian initial datum `Y₀`, the Fourier coordinates
`Ŷ^t(j) = G^t(e_j) + Y₀(U^{0,t} e_j)` form, for finitely many times and modes, a centred Gaussian vector: `G` is jointly Gaussian
(`gaussian_part`) and independent of `Y₀` (so `(G, Y₀)` is jointly Gaussian), and `F ↦ F(U^{0,t} e_j)` is a continuous linear
functional of `E_m` because `U^{0,t} e_j ∈ H^m` (`t25p_memSobolev_propagator`).  Combined with GS-3a this gives path-level Gaussianity
of the window of any `IsPreparedLinear` with Gaussian initial law.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213Q

open HRS HRS.Sec7 HRS.Uniform HRS.Uniform.Q54c HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- The functional `F ↦ F(ψ)` for `ψ ∈ H^m`, as a continuous linear functional on `E_m`. -/
def e213qEvalCLM (m : ℝ) {ψ : Torus d → ℝ} (_h : MemSobolev m ψ) : StrongDual ℝ (NegSobolev d m) :=
  innerSL ℝ (lpFun m ψ)

theorem e213qEvalCLM_apply (m : ℝ) {ψ : Torus d → ℝ} (h : MemSobolev m ψ) (F : NegSobolev d m) :
    e213qEvalCLM m h F = NegSobolev.eval F ψ := by
  rw [e213qEvalCLM, innerSL_apply_apply, real_inner_comm, eval_lpFun F h]

/-- **GS-3b (fdd).**  The Fourier coordinates of a linear fluctuation solution with centred Gaussian initial datum are, at finitely
many times of `[0,T']`, jointly centred Gaussian. -/
theorem e213q_lin_fdd {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} (hd : 2 ≤ d)
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ} {T' : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ)
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (hG : IsCenteredGaussian (P.map Y₀))
    (Y : ℝ → Ω → NegSobolev d m) (hY : IsLinearFluctuationSolution P htr.dyn ρ m q T' Y₀ Y) :
    FddGaussian P Y (Set.Icc 0 T') := by
  classical
  intro ι _ τ hτ J
  haveI : IsGaussian (P.map Y₀) := hG.1
  set N := Fintype.card (ι × J) with hN
  let e : ι × J ≃ Fin N := Fintype.equivFin _
  set ts : Fin N → ℝ := fun a => τ (e.symm a).1 with hts_def
  set φ : Fin N → Torus d → ℝ := fun a => Torus.realMode ((e.symm a).2 : NonzeroLattice d) with hφdef
  have hts : ∀ a, ts a ∈ Set.Icc 0 T' := fun a => hτ _
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.Uniform.Q48b.q48b_isSmooth_realMode _
  have hmemφ : ∀ a, MemSobolev m (φ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hmemU : ∀ a, MemSobolev m (propagator htr.dyn ρ 0 (ts a) (φ a)) := fun a =>
    t25p_memSobolev_propagator hd htr hdual hK le_rfl (hts a).1
      (hKb 0 (ts a) le_rfl (hts a).1 (hts a).2) (hφ a)
  obtain ⟨hind, hlaw⟩ := hY.gaussian_part N ts φ hts hφ
  set Gy : Ω → EuclideanSpace ℝ (Fin N) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) -
      NegSobolev.eval (Y₀ ω) (propagator htr.dyn ρ 0 (ts a) (φ a)) with hGy
  have hGym : Measurable Gy := by
    refine measurable_toLp_eval fun a => ?_
    exact ((continuous_eval_const (hmemφ a)).measurable.comp (hY.meas _)).sub
      ((continuous_eval_const (hmemU a)).measurable.comp hY₀)
  have hlaw' : P.map Gy = multivariateGaussian 0 (Matrix.of fun a b =>
      2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (Torus.grad (propagator htr.dyn ρ r (ts a) (φ a)) x)
          (Torus.grad (propagator htr.dyn ρ r (ts b) (φ b)) x) * ρ r x) := hlaw
  haveI : IsGaussian (P.map Gy) := by
    rw [hlaw']; infer_instance
  have hGG : HasGaussianLaw Gy P := IsGaussian.hasGaussianLaw hGym.aemeasurable
  have hGY : HasGaussianLaw Y₀ P := IsGaussian.hasGaussianLaw hY₀.aemeasurable
  have hpair : HasGaussianLaw (fun ω => (Gy ω, Y₀ ω)) P := IndepFun.hasGaussianLaw hGG hGY hind
  -- the linear map
  let Ψ : EuclideanSpace ℝ (Fin N) × NegSobolev d m →L[ℝ] (ι × J → ℝ) :=
    ContinuousLinearMap.pi fun p =>
      (EuclideanSpace.proj (e p) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ _ _) +
      (e213qEvalCLM m (hmemU (e p))).comp (ContinuousLinearMap.snd ℝ _ _)
  have hvec : (fun ω (p : ι × J) => NegSobolev.fourierCoeff (Y (τ p.1) ω) p.2) =
      fun ω => Ψ (Gy ω, Y₀ ω) := by
    funext ω p
    simp only [Ψ, ContinuousLinearMap.pi_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      e213qEvalCLM_apply, EuclideanSpace.coe_proj, hGy]
    simp only [WithLp.ofLp_toLp, sub_add_cancel]
    have h1 : ts (e p) = τ p.1 := by simp [hts_def]
    have h2 : φ (e p) = Torus.realMode ((p.2 : J) : NonzeroLattice d) := by simp [hφdef]
    rw [h1, h2, HRS.Uniform.Q54c.eval_realMode]
  refine ⟨?_, ?_⟩
  · rw [hvec]
    exact hpair.map_fun Ψ
  · -- means
    have hintG : ∀ a, Integrable (fun ω => Gy ω a) P := fun a => by
      have := (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).integrable_comp hGG.integrable
      exact this
    have hmeanG : ∀ a, ∫ ω, Gy ω a ∂P = 0 := fun a => by
      have h0 : ∫ ω, Gy ω ∂P = 0 := by
        have : ∫ x, x ∂(P.map Gy) = ∫ ω, Gy ω ∂P :=
          integral_map hGym.aemeasurable aestronglyMeasurable_id
        rw [← this, hlaw']
        exact integral_id_multivariateGaussian
      have := (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).integral_comp_comm
        hGG.integrable
      simp only [EuclideanSpace.coe_proj] at this
      rw [this, h0]; rfl
    have hmeanY : ∀ a, ∫ ω, NegSobolev.eval (Y₀ ω) (propagator htr.dyn ρ 0 (ts a) (φ a)) ∂P = 0 := by
      intro a
      have hL := hG.2 (e213qEvalCLM m (hmemU a))
      rw [integral_map hY₀.aemeasurable (e213qEvalCLM m (hmemU a)).continuous.aestronglyMeasurable] at hL
      simpa only [e213qEvalCLM_apply] using hL
    have hintY : ∀ a, Integrable (fun ω => NegSobolev.eval (Y₀ ω) (propagator htr.dyn ρ 0 (ts a) (φ a))) P :=
      fun a => by
        have := (e213qEvalCLM m (hmemU a)).integrable_comp hGY.integrable
        simpa only [Function.comp_def, e213qEvalCLM_apply] using this
    intro p
    have hp : (fun ω => NegSobolev.fourierCoeff (Y (τ p.1) ω) p.2) =
        fun ω => Gy ω (e p) +
          NegSobolev.eval (Y₀ ω) (propagator htr.dyn ρ 0 (ts (e p)) (φ (e p))) := by
      funext ω
      have h1 : ts (e p) = τ p.1 := by simp [hts_def]
      have h2 : φ (e p) = Torus.realMode ((p.2 : J) : NonzeroLattice d) := by simp [hφdef]
      simp only [hGy, WithLp.ofLp_toLp]
      rw [← HRS.Uniform.Q54c.eval_realMode, ← h2, ← h1]
      ring
    rw [hp, integral_add (hintG _) (hintY _), hmeanG, hmeanY, add_zero]

/-- The Dirac mass at `0` is a centred Gaussian measure. -/
theorem e213q_isCenteredGaussian_dirac_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] : IsCenteredGaussian (Measure.dirac (0 : E)) :=
  ⟨inferInstance, fun L => by
    rw [integral_dirac' _ _ L.continuous.stronglyMeasurable]; simp⟩

/-- **GS-3b (noise only).**  If the initial datum vanishes a.s. (`Y₀ = 0`), no Gaussianity assumption on `Y₀` is needed. -/
theorem e213q_lin_fdd_zero {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} (hd : 2 ≤ d)
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ} {T' : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ)
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (h0 : Y₀ =ᵐ[P] fun _ => 0)
    (Y : ℝ → Ω → NegSobolev d m) (hY : IsLinearFluctuationSolution P htr.dyn ρ m q T' Y₀ Y) :
    FddGaussian P Y (Set.Icc 0 T') := by
  refine e213q_lin_fdd hd htr hdual hK hKb P q Y₀ hY₀ ?_ Y hY
  rw [Measure.map_congr h0, Measure.map_const, measure_univ, one_smul]
  exact e213q_isCenteredGaussian_dirac_zero

/-- **GS-3b (window).**  The window of any `IsPreparedLinear` with a centred Gaussian initial law is an a.e. measurable random
element of `𝒳_{m,T}` with centred Gaussian law. -/
theorem e213q_prepared_window_gaussian (S : HRS.Main.PreparedData d) (m : ℝ) (T a : ℝ) (hT : 0 < T)
    (ha : 0 ≤ a) (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussian ν)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : HRS.Main.IsPreparedLinear S m (a + T) ν P' Z₀ Z) :
    AEMeasurable (HRS.Main.windowPath m T a Z) P' ∧
      IsCenteredGaussian (law P' (HRS.Main.windowPath m T a Z)) := by
  have htr := HRS.T25.t25_traj S
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ := adjk_evolution_along_trajectory S.hd htr m
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖VA t r‖ ≤ Cr := by
    intro r t hr hrt _
    refine (hdecA r t hr hrt).trans ?_
    have h1 : Real.exp (-cr * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hrt]
    nlinarith
  have hfdd := e213q_lin_fdd S.hd htr hdualA hCr.le hKb P' S.β⁻¹ Z₀ hZ.meas
    (by rw [show P'.map Z₀ = ν from hZ.law_init]; exact hν) Z hZ.sol
  exact gaussian_window_of_fdd T hT P' Z a ha hZ.sol.meas hZ.sol.cont hfdd

end HRS.MC.E213Q
