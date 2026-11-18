import HRS.Main.HeadlineEdgeworth
import HRS.Main.ThermLin2Fu17
import HRS.Main.ThermLin2Dy2
import HRS.MH.EdgeSharpC3b
import HRS.MP.FidiCov

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.CrossCov

open HRS HRS.Main

variable {d : ℕ}

theorem ccd_propagator_smooth (S : PreparedData d) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Torus.IsSmooth (propagator S.dyn S.ρ u t φ) := by
  rcases (hu.trans hut).eq_or_lt with h0 | hpos
  · subst h0
    have hu0 : u = 0 := le_antisymm hut hu
    subst hu0
    unfold propagator
    by_cases h : ∃ f, IsClassicalAdjointSolution S.dyn S.ρ 0 φ f
    · rw [dif_pos h, h.choose_spec.terminal]; exact hφ
    · rw [dif_neg h]
      unfold Torus.IsSmooth Torus.IsCk
      exact contDiff_const
  · obtain ⟨ρβ, hth, -⟩ :=
      PDE.thermal_exists_unique_smooth S.hd S.s S.hs0 S.hsd S.β S.hβ S.V S.hV
    exact HRS.ThermLin.Plan2.tl2fu_prop_smooth S hth hφ hpos ⟨hu, hut⟩

theorem ccd_cross_cov (S : PreparedData d) (β₀ m T' : ℝ) (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m T' ν P' Z₀ Z)
    {r t : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') (ht : t ∈ Set.Icc (0 : ℝ) T')
    {ψ φ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (hφ : Torus.IsSmooth φ) :
    ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ ∂P' =
      preparedCov d S.s β₀ S.μ0 (propagator S.dyn S.ρ 0 r ψ) (propagator S.dyn S.ρ 0 t φ) +
      2 * S.β⁻¹ * ∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x,
        inner ℝ (Torus.grad (propagator S.dyn S.ρ s r ψ) x)
          (Torus.grad (propagator S.dyn S.ρ s t φ) x) * S.ρ s x := by
  classical
  have hψU : Torus.IsSmooth (propagator S.dyn S.ρ 0 r ψ) := ccd_propagator_smooth S le_rfl hr.1 hψ
  have hφU : Torus.IsSmooth (propagator S.dyn S.ρ 0 t φ) := ccd_propagator_smooth S le_rfl ht.1 hφ
  have hts : ∀ a : Fin 2, (![r, t] : Fin 2 → ℝ) a ∈ Set.Icc (0 : ℝ) T' := by
    intro a; fin_cases a
    · exact hr
    · exact ht
  have hsm : ∀ a : Fin 2, Torus.IsSmooth ((![ψ, φ] : Fin 2 → Torus d → ℝ) a) := by
    intro a; fin_cases a
    · exact hψ
    · exact hφ
  obtain ⟨hind, hlaw⟩ := hZ.sol.gaussian_part 2 ![r, t] ![ψ, φ] hts hsm
  -- the PSD property of the noise covariance
  obtain ⟨ρβ, hth, -⟩ :=
    PDE.thermal_exists_unique_smooth S.hd S.s S.hs0 S.hsd S.β S.hβ S.V S.hV
  have hj : (d : ℝ) / 2 + 4 < ((gammaIdx d + 2 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) ≤ (PDE.mStar d : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    unfold gammaIdx
    push_cast
    linarith
  obtain ⟨R, Λ, hAall⟩ := HRS.ThermLin.Plan2.tl2dy_moving S hth (gammaIdx d + 2) hj
  have hTpos : (0 : ℝ) < max T' 1 := lt_max_of_lt_right one_pos
  have hA := hAall (max T' 1) hTpos
  have hts' : ∀ a : Fin 2, (![r, t] : Fin 2 → ℝ) a ∈ Set.Icc (0 : ℝ) (max T' 1) :=
    fun a => ⟨(hts a).1, (hts a).2.trans (le_max_left _ _)⟩
  have hpsd := HRS.MP.FidiCov.fi3b_psd S.dyn S.ρ hA (inv_nonneg.2 S.hβ.le) ![r, t] hts' ![ψ, φ] hsm
  have hmem : ∀ a : Fin 2, MemSobolev m ((![ψ, φ] : Fin 2 → Torus d → ℝ) a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hsm a) m
  have hUs : ∀ a : Fin 2, Torus.IsSmooth
      (propagator S.dyn S.ρ 0 ((![r, t] : Fin 2 → ℝ) a) ((![ψ, φ] : Fin 2 → Torus d → ℝ) a)) := by
    intro a; fin_cases a
    · exact hψU
    · exact hφU
  have hUmem : ∀ a : Fin 2, MemSobolev m
      (propagator S.dyn S.ρ 0 ((![r, t] : Fin 2 → ℝ) a) ((![ψ, φ] : Fin 2 → Torus d → ℝ) a)) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hUs a) m
  obtain ⟨Lf, hLf⟩ := HRS.MH.EdgeSharp.exists_evalCLM (d := d) m _ hψU
  obtain ⟨Lg, hLg⟩ := HRS.MH.EdgeSharp.exists_evalCLM (d := d) m _ hφU
  have hA2 : MemLp (fun ω => Lf (Z₀ ω)) 2 P' :=
    HRS.MH.EdgeSharp.memLp_two_clm ν hν.1 Lf P' Z₀ hZ.meas hZ.law_init
  have hB2 : MemLp (fun ω => Lg (Z₀ ω)) 2 P' :=
    HRS.MH.EdgeSharp.memLp_two_clm ν hν.1 Lg P' Z₀ hZ.meas hZ.law_init
  set G : Ω' → EuclideanSpace ℝ (Fin 2) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Z ((![r, t] : Fin 2 → ℝ) a) ω) ((![ψ, φ] : Fin 2 → Torus d → ℝ) a) -
        NegSobolev.eval (Z₀ ω) (propagator S.dyn S.ρ 0 ((![r, t] : Fin 2 → ℝ) a)
          ((![ψ, φ] : Fin 2 → Torus d → ℝ) a)) with hG
  have hGm : Measurable G := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp ?_
    refine Measurable.of_eval fun a => ?_
    exact ((HRS.MP.FidiCov.fi_eval_meas (hmem a)).comp (hZ.sol.meas _)).sub
      ((HRS.MP.FidiCov.fi_eval_meas (hUmem a)).comp hZ.meas)
  have hlawG : P'.map G = multivariateGaussian 0
      (HRS.Main.surrogateCov S.dyn S.ρ S.β⁻¹ ![r, t] ![ψ, φ]) := hlaw
  have hGauss : IsGaussian (P'.map G) := by rw [hlawG]; infer_instance
  have hcoord2 : ∀ i : Fin 2, MemLp (fun ω => G ω i) 2 P' := by
    intro i
    have h1 : MemLp (fun v : EuclideanSpace ℝ (Fin 2) => v i) 2 (P'.map G) :=
      IsGaussian.memLp_dual (P'.map G) (EuclideanSpace.proj i) 2 (by simp)
    exact (memLp_map_measure_iff (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.aestronglyMeasurable
      hGm.aemeasurable).1 h1
  have hmean : ∀ i : Fin 2, ∫ ω, G ω i ∂P' = 0 := by
    intro i
    have h2 : ∫ ω, (EuclideanSpace.proj (𝕜 := ℝ) i) (G ω) ∂P' =
        ∫ v, (EuclideanSpace.proj (𝕜 := ℝ) i) v ∂(P'.map G) :=
      (integral_map hGm.aemeasurable
        (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.aestronglyMeasurable).symm
    have h4 : ∫ v, (EuclideanSpace.proj (𝕜 := ℝ) i) v ∂(P'.map G) =
        (EuclideanSpace.proj (𝕜 := ℝ) i) (∫ v, id v ∂(P'.map G)) :=
      ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_id
    have h3 : ∫ v, v ∂(P'.map G) = 0 := by
      rw [hlawG]; exact integral_id_multivariateGaussian
    have := h2.trans h4
    simpa [h3] using this
  have hcov : ∫ ω, G ω 0 * G ω 1 ∂P' =
      HRS.Main.surrogateCov S.dyn S.ρ S.β⁻¹ ![r, t] ![ψ, φ] 0 1 := by
    have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 2))) hpsd 0 1
    rw [← hlawG] at hc
    have m0 : MemLp (fun v : EuclideanSpace ℝ (Fin 2) => v 0) 2 (P'.map G) :=
      IsGaussian.memLp_dual (P'.map G) (EuclideanSpace.proj 0) 2 (by simp)
    have m1 : MemLp (fun v : EuclideanSpace ℝ (Fin 2) => v 1) 2 (P'.map G) :=
      IsGaussian.memLp_dual (P'.map G) (EuclideanSpace.proj 1) 2 (by simp)
    rw [covariance_eq_sub m0 m1] at hc
    have e0 : ∫ v, (fun v : EuclideanSpace ℝ (Fin 2) => v 0) v ∂(P'.map G) = 0 := by
      exact (integral_map hGm.aemeasurable
        (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.aestronglyMeasurable).trans (hmean 0)
    have e1 : ∫ v, (fun v : EuclideanSpace ℝ (Fin 2) => v 1) v ∂(P'.map G) = 0 := by
      exact (integral_map hGm.aemeasurable
        (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.aestronglyMeasurable).trans (hmean 1)
    rw [e0, e1, mul_zero, sub_zero] at hc
    rw [← hc]
    have hcont : Continuous fun v : EuclideanSpace ℝ (Fin 2) => v 0 * v 1 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.mul
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
    rw [show (fun v : EuclideanSpace ℝ (Fin 2) => v 0) * (fun v => v 1) =
        fun v : EuclideanSpace ℝ (Fin 2) => v 0 * v 1 from rfl,
      integral_map hGm.aemeasurable hcont.aestronglyMeasurable]
  -- independence
  have hindL : ∀ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (L : NegSobolev d m →L[ℝ] ℝ), Measurable f →
      IndepFun (fun ω => f (G ω)) (fun ω => L (Z₀ ω)) P' := fun f L hf =>
    hind.comp hf L.continuous.measurable
  have hX0 : MemLp (fun ω => G ω 0) 2 P' := hcoord2 0
  have hY0 : MemLp (fun ω => G ω 1) 2 P' := hcoord2 1
  have h3 : ∫ ω, G ω 0 * Lg (Z₀ ω) ∂P' = 0 := by
    have hi := hindL (fun v => v 0) Lg (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.measurable
    have := hi.integral_mul_eq_mul_integral hX0.aestronglyMeasurable hB2.aestronglyMeasurable
    simpa [hmean 0] using this
  have h3' : ∫ ω, Lf (Z₀ ω) * G ω 1 ∂P' = 0 := by
    have hi := hindL (fun v => v 1) Lf (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.measurable
    have := hi.symm.integral_mul_eq_mul_integral hA2.aestronglyMeasurable hY0.aestronglyMeasurable
    simpa [hmean 1] using this
  have h4 : ∫ ω, Lf (Z₀ ω) * Lg (Z₀ ω) ∂P' =
      preparedCov d S.s β₀ S.μ0 (propagator S.dyn S.ρ 0 r ψ) (propagator S.dyn S.ρ 0 t φ) := by
    have hmap : ∫ F, Lf F * Lg F ∂ν = ∫ ω, Lf (Z₀ ω) * Lg (Z₀ ω) ∂P' := by
      rw [← hZ.law_init]
      exact integral_map hZ.meas.aemeasurable
        ((Lf.continuous.mul Lg.continuous).aestronglyMeasurable)
    rw [← hmap, ← hν.2 _ _ hψU hφU]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [hLf, hLg]
  have h1 : ∀ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ =
      (G ω 0 + Lf (Z₀ ω)) * (G ω 1 + Lg (Z₀ ω)) := by
    intro ω
    have e0 : G ω 0 = NegSobolev.eval (Z r ω) ψ -
        NegSobolev.eval (Z₀ ω) (propagator S.dyn S.ρ 0 r ψ) := rfl
    have e1 : G ω 1 = NegSobolev.eval (Z t ω) φ -
        NegSobolev.eval (Z₀ ω) (propagator S.dyn S.ρ 0 t φ) := rfl
    rw [e0, e1, hLf, hLg]
    ring
  have hi1 : Integrable (fun ω => G ω 0 * G ω 1) P' := hX0.integrable_mul hY0
  have hi2 : Integrable (fun ω => G ω 0 * Lg (Z₀ ω)) P' := hX0.integrable_mul hB2
  have hi3 : Integrable (fun ω => Lf (Z₀ ω) * G ω 1) P' := hA2.integrable_mul hY0
  have hi4 : Integrable (fun ω => Lf (Z₀ ω) * Lg (Z₀ ω)) P' := hA2.integrable_mul hB2
  have h5 : ∫ ω, (G ω 0 + Lf (Z₀ ω)) * (G ω 1 + Lg (Z₀ ω)) ∂P' =
      ∫ ω, G ω 0 * G ω 1 ∂P' + ∫ ω, G ω 0 * Lg (Z₀ ω) ∂P' + ∫ ω, Lf (Z₀ ω) * G ω 1 ∂P' +
        ∫ ω, Lf (Z₀ ω) * Lg (Z₀ ω) ∂P' := by
    have a1 : ∫ ω, (G ω 0 * G ω 1 + G ω 0 * Lg (Z₀ ω)) ∂P' =
        ∫ ω, G ω 0 * G ω 1 ∂P' + ∫ ω, G ω 0 * Lg (Z₀ ω) ∂P' := integral_add hi1 hi2
    have a2 : ∫ ω, (G ω 0 * G ω 1 + G ω 0 * Lg (Z₀ ω) + Lf (Z₀ ω) * G ω 1) ∂P' =
        ∫ ω, (G ω 0 * G ω 1 + G ω 0 * Lg (Z₀ ω)) ∂P' + ∫ ω, Lf (Z₀ ω) * G ω 1 ∂P' :=
      integral_add (hi1.add hi2) hi3
    have a3 : ∫ ω, (G ω 0 * G ω 1 + G ω 0 * Lg (Z₀ ω) + Lf (Z₀ ω) * G ω 1 +
        Lf (Z₀ ω) * Lg (Z₀ ω)) ∂P' =
        ∫ ω, (G ω 0 * G ω 1 + G ω 0 * Lg (Z₀ ω) + Lf (Z₀ ω) * G ω 1) ∂P' +
          ∫ ω, Lf (Z₀ ω) * Lg (Z₀ ω) ∂P' := integral_add ((hi1.add hi2).add hi3) hi4
    rw [← a1, ← a2, ← a3]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  simp_rw [h1]
  rw [h5, hcov, h3, h3', h4]
  simp only [HRS.Main.surrogateCov, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end HRS.MC.CrossCov

end
