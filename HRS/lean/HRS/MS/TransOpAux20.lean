import HRS.MS.TransOpAux19
import HRS.MS.TransOpAux16

/-!
# S611 packet P4f: conjugation of the linear Gaussian evolution by translation

`s611_gaussian_conj`: if `Z` is a linear Gaussian evolution along `ρ^t = ρβ(· - b_t)` (`b_t = movShift q b t`) with initial covariance the
susceptibility form of `ρ^0`, then `Z'_t = Λ_{-b_t} Z_t` is the stationary linear Gaussian evolution along `ρβ`
(initial covariance the susceptibility form of `ρβ`), under uniqueness of classical adjoint solutions and of response solutions for
the stationary data.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_isOscTest_shift (m : ℕ) (hm : 1 ≤ m) (c : Euc d) {φ : Euc d → ℝ}
    (hφ : IsOscTest (m : ℝ) φ) : IsOscTest (m : ℝ) (fun x => φ (x - c)) := by
  refine ⟨hφ.1.comp (contDiff_id.sub contDiff_const), ?_⟩
  have := (s611_memOsc_translate m hm (-c) hφ.2).1
  simpa [sub_eq_add_neg] using this

theorem s611_gaussian_conj (m : ℕ) (hm : 1 ≤ m) (s q β : ℝ) (ρβ : Euc d → ℝ) (b : Euc d) (γ T : ℝ)
    (huniq : s611_Uniq d s q β ρβ T)
    (hsus : ∀ (ψ h1 h2 : Euc d → ℝ),
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ ψ h1 →
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ ψ h2 →
      h1 =ᵐ[HRS.Whole.withDensityReal ρβ] h2)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (Z : ℝ → Ω' → OscDual d (m : ℝ))
    (hZ : IsLinearGaussianEvolutionW P'
      ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) (m : ℝ) β⁻¹ T
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal (movTranslatedDensity q b ρβ 0)) γ) Z) :
    IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) (m : ℝ) β⁻¹ T
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ)
      (fun t ζ => s611_Lam m hm (-(movShift q b t)) (Z t ζ)) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hZ.cont] with ζ hζ
    intro t ht
    have hc : Tendsto (fun t => -(movShift q b t)) (𝓝[Set.Icc 0 T] t) (𝓝 (-(movShift q b t))) :=
      (((s611_continuous_movShift q b).neg).tendsto t).mono_left nhdsWithin_le_nhds
    exact s611_Lam_tendsto m hm hc (hζ t ht)
  · intro t
    exact ((s611_Lam m hm (-(movShift q b t))).continuous.measurable).comp (hZ.meas t)
  · intro p ts φ hts hφ
    have hψ : ∀ a, IsOscTest (m : ℝ) (fun x => φ a (x - movShift q b (ts a))) := fun a =>
      s611_isOscTest_shift m hm _ (hφ a)
    have h1 := hZ.gaussian p ts (fun a x => φ a (x - movShift q b (ts a))) hts hψ
    have hev : ∀ (a : Fin p) (ζ : Ω'),
        OscDual.eval (s611_Lam m hm (-(movShift q b (ts a))) (Z (ts a) ζ)) (φ a) =
          OscDual.eval (Z (ts a) ζ) (fun x => φ a (x - movShift q b (ts a))) := by
      intro a ζ
      rw [s611_eval_Lam m hm _ _ (hφ a).2]
      simp only [sub_eq_add_neg]
    have e1 : (fun ζ => (WithLp.toLp 2 fun a => OscDual.eval
        (s611_Lam m hm (-(movShift q b (ts a))) (Z (ts a) ζ)) (φ a) : EuclideanSpace ℝ (Fin p))) =
        fun ζ => (WithLp.toLp 2 fun a => OscDual.eval (Z (ts a) ζ)
          (fun x => φ a (x - movShift q b (ts a))) : EuclideanSpace ℝ (Fin p)) := by
      funext ζ
      congr 1
      funext a
      exact hev a ζ
    show law P' (fun ζ => (WithLp.toLp 2 fun a => OscDual.eval
        (s611_Lam m hm (-(movShift q b (ts a))) (Z (ts a) ζ)) (φ a) : EuclideanSpace ℝ (Fin p))) = _
    rw [e1, h1]
    congr 2
    funext a c
    have ha : ts a ∈ Set.Icc (0 : ℝ) T := hts a
    have hc : ts c ∈ Set.Icc (0 : ℝ) T := hts c
    have hra : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (ts a) := ⟨le_rfl, ha.1⟩
    have hrc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (ts c) := ⟨le_rfl, hc.1⟩
    try simp only [Matrix.of_apply]
    rw [s611_noiseCov_shift s q β ρβ b T huniq _ ha hc (φ a) (φ c),
      s611_propagator_shift s q β ρβ b T huniq ha (φ a) hra,
      s611_propagator_shift s q β ρβ b T huniq hc (φ c) hrc]
    congr 1
    have hmap : (HRS.Whole.withDensityReal ρβ).map (fun y => y + movShift q b 0) =
        HRS.Whole.withDensityReal (movTranslatedDensity q b ρβ 0) :=
      HRS.MS.A0.a0_map_withDensity ρβ (movShift q b 0)
    rw [← hmap]
    exact s611_susceptibilityCov_shift (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ hsus
      (movShift q b 0) _ _

end HRS.MS.TransOp

end
