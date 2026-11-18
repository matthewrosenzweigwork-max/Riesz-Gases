import HRS.Main.A34Aux17
import HRS.PDE.MeanFieldOneLe
import HRS.Dynamics.InitialData
import HRS.Sections.Sec3

/-!
# FULLBOUNDS (stationary time-zero law)

`fb_stat_time0_law`: the time-zero marginal of any `IsStationaryGaussianField` for a smooth potential `V` and a smooth
positive thermal density `ρβ` is the centered Gaussian `ν` with covariance `susceptibilityCov` (the Gaussian initial law
of Theorem 2.5 for a Gibbs preparation).  Proof: the one-dimensional marginals against smooth tests agree
(`stationaryLagCov` at lag zero is `susceptibilityCov`, because `S_β(0) = P_{μ_β}`), hence the characteristic functions
agree on finite trigonometric combinations, hence (dominated convergence along the Fourier truncation) on every
continuous linear functional (`Measure.ext_of_charFunDual`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- `F ↦ ⟨F, ψ⟩` is a continuous linear functional for a smooth test `ψ`. -/
theorem fb_eval_clm (m : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∃ L : StrongDual ℝ (NegSobolev d m), ∀ F, L F = NegSobolev.eval F ψ :=
  ⟨innerSL ℝ (HRS.InitialDataAux.yvec m ψ (HRS.A33.a33_ws_smooth m hψ)), fun F => by
    rw [innerSL_apply_apply]
    exact (HRS.InitialDataAux.eval_eq_inner m ψ _ F).symm⟩

theorem fb_projMean_idem (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (f : Torus d → ℝ) :
    projMean μ (projMean μ f) = projMean μ f := by
  by_cases hf : Integrable f μ
  · funext x
    have : pair μ (projMean μ f) = 0 := by
      unfold pair projMean
      rw [integral_sub hf (integrable_const _)]
      simp [pair]
    simp [projMean, this]
  · funext x
    have h0 : pair μ f = 0 := integral_undef hf
    have h1 : projMean μ f = f := by funext y; simp [projMean, h0]
    rw [h1, h1]

theorem fb_responseInverse_projMean (g : Torus d → ℝ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (β : ℝ) (ψ : Torus d → ℝ) :
    responseInverse g μ β (projMean μ ψ) = responseInverse g μ β ψ := by
  have h : IsResponse g μ β (projMean μ ψ) = IsResponse g μ β ψ := by
    funext h
    unfold IsResponse
    rw [fb_projMean_idem]
  unfold responseInverse
  rw [h]

theorem fb_susceptibilityCov_projMean (g : Torus d → ℝ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (β : ℝ) (φ ψ : Torus d → ℝ) :
    susceptibilityCov g μ β φ (projMean μ ψ) = susceptibilityCov g μ β φ ψ := by
  unfold susceptibilityCov
  rw [fb_responseInverse_projMean]

/-- Time-zero marginals against a smooth test agree: both are `N(0, 𝒞_β(ψ,ψ))`. -/
theorem fb_stat_marginal (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V ρβ : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (m : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z)
    (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν
      (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β))
    {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    (law P (Z 0)).map (fun F => NegSobolev.eval F ψ) =
      ν.map (fun F => NegSobolev.eval F ψ) := by
  haveI hνG : IsGaussian ν := hν.1.1
  haveI hμp : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal hρ.1
  obtain ⟨L, hL⟩ := fb_eval_clm m hψ
  have hLf : (fun F => NegSobolev.eval F ψ) = fun F => L F := funext fun F => (hL F).symm
  set c : ℝ := susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ψ ψ with hc
  have hcν : c = ∫ F, L F * L F ∂ν := by
    rw [hc, ← hν.2 ψ ψ hψ hψ]
    exact integral_congr_ae (Eventually.of_forall fun F => by simp [hL])
  have hc0 : 0 ≤ c := by
    rw [hcν]; exact integral_nonneg fun F => mul_self_nonneg _
  have hLm : Measurable fun F : NegSobolev d m => L F := L.continuous.measurable
  -- the side of `ν`
  have hνside : ν.map (fun F => NegSobolev.eval F ψ) = gaussianReal 0 c.toNNReal := by
    rw [hLf]
    have h1 : ∫ F, L F ∂ν = 0 := hν.1.2 L
    have hv : variance (fun F => L F) ν = c := by
      rw [hcν, variance_of_integral_eq_zero hLm.aemeasurable h1]
      exact integral_congr_ae (Eventually.of_forall fun F => by simp [sq])
    have := IsGaussian.map_eq_gaussianReal (μ := ν) L
    rw [h1, hv] at this
    exact this
  -- the side of `Z 0`
  have hS : (Matrix.of fun _ _ : Fin 1 => c).PosSemidef := by
    have : (Matrix.of fun _ _ : Fin 1 => c) = Matrix.diagonal fun _ => c := by
      ext a b
      fin_cases a; fin_cases b
      simp
    rw [this]
    exact Matrix.posSemidef_diagonal_iff.2 fun _ => hc0
  have hg := hZ.gaussian 1 (fun _ => 0) (fun _ => ψ) (fun _ => le_rfl) (fun _ => hψ)
  have hM : PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ
      (fun _ : Fin 1 => (0 : ℝ)) (fun _ => ψ) = Matrix.of fun _ _ : Fin 1 => c := by
    ext a b
    have h0 := (HRS.PDE.MFOneLe.equilibriumSemigroup_generator_of_one_le (by omega) s hs0 hsd β hβ V
      hV ρβ hρ hρC hpos ψ hψ).1
    simp only [PDE.stationaryLagCov, Matrix.of_apply, le_refl, ite_true, sub_self]
    rw [h0, fb_susceptibilityCov_projMean]
  rw [hM] at hg
  have hEm : Measurable fun F : NegSobolev d m => NegSobolev.eval F ψ := by
    rw [hLf]; exact hLm
  have hZm : Measurable fun ω => NegSobolev.eval (Z 0 ω) ψ := hEm.comp (hZ.meas 0)
  have hmap : (law P (Z 0)).map (fun F => NegSobolev.eval F ψ) =
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ : Fin 1 => c)).map
        (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by
    rw [← hg, law, Measure.map_map hEm (hZ.meas 0)]
    rw [Measure.map_map (by fun_prop)]
    · rfl
    · exact (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp
        (measurable_pi_iff.2 fun a => hZm)
  rw [hmap, hνside, (measurePreserving_eval_multivariateGaussian hS).map_eq]
  simp

/-- A stationary Gaussian field started from its time-zero law: `law (Z 0) = ν`, the centered Gaussian with covariance
`susceptibilityCov` (smooth `V`, smooth positive thermal density `ρβ`). -/
theorem fb_stat_time0_law (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V ρβ : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (m : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z)
    (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν
      (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β)) :
    law P (Z 0) = ν := by
  haveI hνG : IsGaussian ν := hν.1.1
  haveI : IsProbabilityMeasure (law P (Z 0)) := inferInstance
  have key := fun {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) =>
    fb_stat_marginal hd hs0 hsd hβ V ρβ hV hρ hρC hpos m P Z hZ ν hν hψ
  obtain ⟨e⟩ := HRS.A33.a33_exists_equiv (by omega : 1 ≤ d)
  refine Measure.ext_of_charFunDual ?_
  funext L
  set a : NegSobolev d m := (InnerProductSpace.toDual ℝ (NegSobolev d m)).symm L with ha
  have hL : ∀ F : NegSobolev d m, L F = inner ℝ a F := fun F =>
    (InnerProductSpace.toDual_symm_apply (x := F) (y := L)).symm
  set Ln : ℕ → NegSobolev d m → ℝ := fun n F => ∑ i ∈ Finset.range n,
    NegSobolev.coord F (e i) * NegSobolev.coord a (e i) with hLn
  set c : ℕ → ℝ := fun i => NegSobolev.coord a (e i) * Lattice.jp (e i).1 ^ (-m) with hc
  have hLnev : ∀ n F, Ln n F = NegSobolev.eval F (fun x => ∑ i ∈ Finset.range n,
      c i * Torus.realMode (e i) x) := by
    intro n F
    rw [HRS.A34.a34_eval_comb e F c n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hj : Lattice.jp (e i).1 ^ (-m) * Lattice.jp (e i).1 ^ m = 1 := by
      rw [← Real.rpow_add (Torus.jp_pos _)]; simp
    simp only [hLn, hc, NegSobolev.fourierCoeff]
    calc NegSobolev.coord F (e i) * NegSobolev.coord a (e i) =
        NegSobolev.coord F (e i) * NegSobolev.coord a (e i) * 1 := by ring
      _ = _ := by rw [← hj]; ring
  have hLnm : ∀ n, Measurable (Ln n) := fun n =>
    (continuous_finsetSum _ fun i _ =>
      ((HRS.A33.a33_continuous_coord (e i)).mul continuous_const)).measurable
  have hlim : ∀ F, Tendsto (fun n => Ln n F) atTop (𝓝 (L F)) := by
    intro F; rw [hL]; exact HRS.A33.a33_inner_tendsto e a F
  -- the characteristic function of a probability measure along the truncations
  have hlimit : ∀ (μ : Measure (NegSobolev d m)) [IsProbabilityMeasure μ],
      Tendsto (fun n => ∫ F, Complex.exp ((Ln n F : ℂ) * Complex.I) ∂μ) atTop
        (𝓝 (charFunDual μ L)) := by
    intro μ _
    rw [charFunDual_apply]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const _) (fun n => ?_) ?_
    · exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (hLnm n)).mul_const
        Complex.I)).aestronglyMeasurable
    · exact Eventually.of_forall fun F => (Complex.norm_exp_ofReal_mul_I _).le
    · refine Eventually.of_forall fun F => ?_
      have hcont : Continuous fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I) := by fun_prop
      exact (hcont.tendsto _).comp (hlim F)
  have heq : ∀ n, ∫ F, Complex.exp ((Ln n F : ℂ) * Complex.I) ∂(law P (Z 0)) =
      ∫ F, Complex.exp ((Ln n F : ℂ) * Complex.I) ∂ν := by
    intro n
    have hsm := HRS.A34.a34_isSmooth_comb e c n
    have hEm : Measurable fun F : NegSobolev d m => NegSobolev.eval F
        (fun x => ∑ i ∈ Finset.range n, c i * Torus.realMode (e i) x) := by
      obtain ⟨L', hL'⟩ := fb_eval_clm m hsm
      have : (fun F : NegSobolev d m => NegSobolev.eval F
          (fun x => ∑ i ∈ Finset.range n, c i * Torus.realMode (e i) x)) = fun F => L' F :=
        funext fun F => (hL' F).symm
      rw [this]; exact L'.continuous.measurable
    have hfun : (fun F => Complex.exp ((Ln n F : ℂ) * Complex.I)) =
        fun F => Complex.exp (((NegSobolev.eval F
          (fun x => ∑ i ∈ Finset.range n, c i * Torus.realMode (e i) x) : ℝ) : ℂ) * Complex.I) :=
      funext fun F => by rw [hLnev]
    have hcm : Measurable fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I) := by fun_prop
    rw [hfun]
    have h1 := integral_map (μ := law P (Z 0)) hEm.aemeasurable
      (f := fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) hcm.aestronglyMeasurable
    have h2 := integral_map (μ := ν) hEm.aemeasurable
      (f := fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) hcm.aestronglyMeasurable
    rw [← h1, ← h2, key hsm]
  exact tendsto_nhds_unique (hlimit (law P (Z 0)))
    ((funext heq ▸ hlimit ν : _))

end Main

end HRS

end
