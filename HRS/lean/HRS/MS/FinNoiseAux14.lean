import HRS.MS.FinNoiseAux13

/-!
# S8.6 `finite_noise`, packet P-08 (S86): the adapted polar coupling with the maximal reconstruction estimate

`s86_coupling_maximal` (statement adapted from the Pro packet S8.6.08, checked and proved here): given the
Hilbert-Schmidt data `(Φ, M)` of the empirical noise, a reference covariance density `Cdet` and a bound `A` on
the expected squared Hilbert-Schmidt distance of the symmetric roots at each time `r ∈ [0,H]`, there is an
`IsAdaptedGaussianCoupling` with `(E sup_{t≤H} ‖𝒯M^t - 𝒯G^t‖²)^{1/2} ≤ K √A` (`K` depends on `H` only).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole

set_option maxHeartbeats 4000000 in
theorem s86_coupling_maximal (d : ℕ) (m H : ℝ) (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (κ : Type) [Countable κ]
        (W : ℝ≥0 → Ω → κ → ℝ), IsCylindricalBrownian P ℱ W →
      ∀ Φ : ℝ → Ω → κ → KSpace d m H,
        (∀ T : ℝ, IsHSIntegrand P ℱ T Φ) →
      ∀ M : ℝ → Ω → KSpace d m H, IsHilbertItoIntegral P ℱ W Φ M →
      ∀ Cdet : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ,
        IsDetCovDensity H Cdet →
      ∀ A : ℝ, 0 ≤ A →
        (∀ r ∈ Set.Icc (0 : ℝ) H,
          ∀ (ι : Type) [Countable ι] (e : HilbertBasis ι ℝ (KSpace d m H))
            (S : Ω → KSpace d m H →L[ℝ] KSpace d m H)
            (Sb : KSpace d m H →L[ℝ] KSpace d m H),
            (∀ z, IsSqrtOfForm (S z) (hsCovForm (Φ r z))) →
            IsSqrtOfForm Sb (Cdet r) →
            (∫⁻ z, ∑' j, ‖(S z - Sb) (e j)‖ₑ ^ 2 ∂P) ≤ ENNReal.ofReal A) →
        ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
          (ℱ' : Filtration ℝ mΩ') (ι : Type) (_ : Countable ι)
          (e : HilbertBasis ι ℝ (KSpace d m H)) (B : ℝ≥0 → Ω' → ι → ℝ)
          (S : ℝ → Ω → KSpace d m H →L[ℝ] KSpace d m H)
          (Sb : ℝ → KSpace d m H →L[ℝ] KSpace d m H)
          (G : ℝ → Ω' → KSpace d m H),
          HRS.Whole.IsAdaptedGaussianCoupling P ℱ Φ M H Cdet P' π ℱ' e B S Sb G ∧
          (∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) H, ENNReal.ofReal
            ‖reconstructPath m H (fun τ z => M τ (π z)) w t -
              reconstructPath m H G w t‖) ^ 2 ∂P') ^ (1 / 2 : ℝ) ≤
                ENNReal.ofReal (K * Real.sqrt A) := by
  classical
  obtain ⟨Crec, hCrec0, hrec⟩ := s86_reconstruction_estimate d m H hH
  refine ⟨Crec * Real.sqrt H, by positivity, ?_⟩
  intro Ω mΩ P hP ℱ κ hκ W hW Φ hΦ M hM Cdet hC A hA hcost
  obtain ⟨Ω', mΩ', P', hP', π, hπp, ℱ', ι, hι, e, B, S, Sb, G, hfilt, hB, hind, hSsq, hMI, hSb,
    hGI, -, -, -, -, -, hHS1, hHS2, hSprog, -⟩ :=
    HRS.s86_polar_ext P ℱ H hH ⟨ℱ 0, le_rfl⟩ W hW Φ hΦ M hM Cdet hC
  refine ⟨Ω', mΩ', P', π, ℱ', ι, hι, e, B, S, Sb, G, ?_, ?_⟩
  · exact
    { prob := hP'
      preserving := hπp
      filtration := hfilt
      brownian := hB
      indep := hind
      sqrtS := fun r _ z => hSsq r z
      empirical := hMI
      sqrtSb := hSb
      gaussian := hGI }
  -- the difference martingale
  set Ψ : ℝ → Ω' → ι → KSpace d m H := fun r w j =>
    (if r ≤ H then S r (π w) (e j) else 0) - (if r ≤ H then Sb r (e j) else 0) with hΨdef
  have hΨ : ∀ T : ℝ, IsHSIntegrand P' ℱ' T Ψ := fun T => s86_hs_sub P' (hHS1 T) (hHS2 T)
  have hDI := s86_hito_sub P' B hB hHS1 hHS2 hMI hGI
  have hHM := HRS.Uniform.Comp28.isHM_of_hilbertIto hB hΨ hDI H
  -- the cost
  set ψc : ℝ → Ω' → ℝ≥0∞ := fun r w => ∑' j, ‖Ψ (min r H) w j‖ₑ ^ 2 with hψc
  have hψm : Measurable (Function.uncurry fun (w : Ω') (r : ℝ) => ψc r w) := by
    have key := hdsum_measurable_tsum Ψ (hΨ 0).prog H
    have e : (Function.uncurry fun (w : Ω') (r : ℝ) => ψc r w) =
        (fun p : ℝ × Ω' => ∑' j, ‖Ψ (min p.1 H) p.2 j‖ₑ ^ 2) ∘ Prod.swap := by
      funext p; rfl
    rw [e]
    exact key.comp measurable_swap
  have hJ : (∫ w, (∫ r in Set.Icc (0 : ℝ) H, traceNormForm (hsCovForm (Ψ r w))) ∂P') ≤ H * A := by
    have h1 := HRS.MS.U9.u9_lintegral_trace hHM
    have h2 : ∫⁻ w, (∫⁻ r in Set.Icc (0 : ℝ) H, ENNReal.ofReal (traceNormForm (hsCovForm (Ψ r w)))) ∂P' =
        ∫⁻ w, (∫⁻ r in Set.Icc (0 : ℝ) H, ψc r w) ∂P' := by
      refine lintegral_congr fun w => setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [hψc, min_eq_left hr.2]
      rw [HRS.Uniform.Q07c.traceNormForm_hsCovForm_eq ((hΨ 0).summable r w),
        s86_tsum_enorm_sq _ ((hΨ 0).summable r w)]
    have h3 : ∫⁻ w, (∫⁻ r in Set.Icc (0 : ℝ) H, ψc r w) ∂P' =
        ∫⁻ r in Set.Icc (0 : ℝ) H, (∫⁻ w, ψc r w ∂P') :=
      lintegral_lintegral_swap hψm.aemeasurable
    have h4 : ∀ r ∈ Set.Icc (0 : ℝ) H, ∫⁻ w, ψc r w ∂P' ≤ ENNReal.ofReal A := by
      intro r hr
      have hm : Measurable fun z : Ω => ∑' j, ‖(S r z - Sb r) (e j)‖ₑ ^ 2 := by
        refine Measurable.ennreal_tsum fun j => ?_
        refine ((?_ : Measurable fun z => (S r z - Sb r) (e j)).enorm).pow_const 2
        obtain ⟨ι₀, hι₀, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := KSpace d m H)
        have := hι₀
        refine measurable_of_inner_basis b fun i => ?_
        have hsec : Measurable fun z : Ω => inner ℝ (S r z (e j)) (b i) := by
          have h' : Measurable[ℱ r] fun z : Ω => inner ℝ (S r z (e j)) (b i) :=
            (hSprog (e j) (b i)).adapted r
          exact h'.mono (ℱ.le r) le_rfl
        have : (fun z : Ω => inner ℝ (b i) ((S r z - Sb r) (e j))) = fun z =>
            inner ℝ (S r z (e j)) (b i) - inner ℝ (Sb r (e j)) (b i) := by
          funext z; simp [real_inner_comm, inner_sub_right, inner_sub_left]
        rw [this]
        exact hsec.sub measurable_const
      have hcomp : ∫⁻ w, ψc r w ∂P' = ∫⁻ z, ∑' j, ‖(S r z - Sb r) (e j)‖ₑ ^ 2 ∂P := by
        rw [← hπp.lintegral_comp hm]
        refine lintegral_congr fun w => ?_
        simp only [hψc, min_eq_left hr.2, hΨdef, hr.2, ite_true]
        rfl
      rw [hcomp]
      exact hcost r hr ι e (S r) (Sb r) (fun z => hSsq r z) (hSb r hr)
    have h5 : ENNReal.ofReal (∫ w, (∫ r in Set.Icc (0 : ℝ) H, traceNormForm (hsCovForm (Ψ r w))) ∂P') ≤
        ENNReal.ofReal (H * A) := by
      rw [← h1, h2, h3]
      calc ∫⁻ r in Set.Icc (0 : ℝ) H, (∫⁻ w, ψc r w ∂P')
          ≤ ∫⁻ r in Set.Icc (0 : ℝ) H, ENNReal.ofReal A :=
            setLIntegral_mono' measurableSet_Icc h4
        _ = ENNReal.ofReal (H * A) := by
            rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul hA, mul_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h5
  have hmain := hrec P' ℱ' (fun τ w => M (min τ H) (π w) - G τ w)
    (fun r w => hsCovForm (Ψ r w)) hHM (H * A) (by positivity) hJ
  have hrecEq : ∀ w (t : Set.Icc (0 : ℝ) H),
      reconstructPath m H (fun τ z => M τ (π z)) w t - reconstructPath m H G w t =
      reconstructPath m H (fun τ w => M (min τ H) (π w) - G τ w) w t := by
    intro w t
    rw [s86_recon_sub]
    unfold reconstructPath
    simp [min_eq_left t.2.2]
  have hrhs : ENNReal.ofReal (Crec * Real.sqrt (H * A)) =
      ENNReal.ofReal (Crec * Real.sqrt H * Real.sqrt A) := by
    rw [Real.sqrt_mul hH]; ring_nf
  rw [← hrhs]
  refine le_trans (le_of_eq ?_) hmain
  congr 2
  funext w
  congr 1
  refine iSup_congr fun t => ?_
  rw [hrecEq]

end HRS.MS.FinNoise
