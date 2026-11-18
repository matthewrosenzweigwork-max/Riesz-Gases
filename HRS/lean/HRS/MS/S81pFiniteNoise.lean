import HRS.MS.FinNoiseAux15
import HRS.MS.FinNoiseTie
import HRS.MS.S81pPolarExt

/-!
# S8.1 (worker S81P): the recent-block producer `finite_noise` with the original Brownian motion exported

`s81p_coupling_maximal` is `s86_coupling_maximal` with the union polar coupling `s81p_polar_ext` and the extra conclusion that
`W ∘ π` stays `ℱ'`-Brownian; `s81p_finite_noise` is the frozen `finite_noise` (assembled from the same cost bound `s86_cost`) with that
extra conclusion on the enlargement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.S81P

open HRS HRS.Whole HRS.MS.FinNoise

set_option maxHeartbeats 4000000 in
theorem s81p_coupling_maximal (d : ℕ) (m H : ℝ) (hH : 0 ≤ H) :
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
                ENNReal.ofReal (K * Real.sqrt A) ∧
          IsCylindricalBrownian P' ℱ' (fun t w k => W t (π w) k) := by
  classical
  obtain ⟨Crec, hCrec0, hrec⟩ := s86_reconstruction_estimate d m H hH
  refine ⟨Crec * Real.sqrt H, by positivity, ?_⟩
  intro Ω mΩ P hP ℱ κ hκ W hW Φ hΦ M hM Cdet hC A hA hcost
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := KSpace d m H)
  obtain ⟨Ω', mΩ', P', hP', π, hπp, ℱ', B, S, Sb, G, hfilt, hB, hind, hSsq, hMI, hSb,
    hGI, -, -, -, -, -, hHS1, hHS2, hSprog, -, -, hWb⟩ :=
    HRS.Whole.S81P.s81p_polar_ext P e ℱ H hH ⟨ℱ 0, le_rfl⟩ W hW Φ hΦ M hM Cdet hC
  refine ⟨Ω', mΩ', P', π, ℱ', ι, hι, e, B, S, Sb, G, ?_, ?_, hWb⟩
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


theorem s81p_finite_noise {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (Hz : ℝ) (hHz : 0 < Hz) (Cin : ℝ) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ ℱ : Filtration ℝ mΩ,
        IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
        (∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) →
        (∀ t ∈ Set.Icc (0 : ℝ) Hz, LinearInputBounds d ((d : ℝ) / 2) N (withDensityReal ρβ) Cin P
          (X (Real.toNNReal t))) →
        let Φ : ℝ → Ω → (Fin N × Fin d) → KSpace d m Hz := fun r z ia =>
          Real.sqrt (2 / (N * β)) •
            gradFeature (critCoeff d a β ρβ) m Hz ia.2 (max r 0) (X (Real.toNNReal r) z ia.1)
        IsHSIntegrand P ℱ Hz Φ ∧
        ∀ M : ℝ → Ω → KSpace d m Hz,
          IsHilbertItoIntegral P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) Φ M →
          ∃ (Cdet : ℝ → KSpace d m Hz →L[ℝ] KSpace d m Hz →L[ℝ] ℝ),
            (∀ r ∈ Set.Icc 0 Hz, ∀ u v, Cdet r u v =
              featureForm m Hz β⁻¹ (fun i => gradFeature (critCoeff d a β ρβ) m Hz i r)
                (withDensityReal ρβ) u v) ∧
            ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
              (ℱ' : Filtration ℝ mΩ') (ι : Type) (_ : Countable ι)
              (e : HilbertBasis ι ℝ (KSpace d m Hz)) (B : ℝ≥0 → Ω' → ι → ℝ)
              (S : ℝ → Ω → KSpace d m Hz →L[ℝ] KSpace d m Hz)
              (Sb : ℝ → KSpace d m Hz →L[ℝ] KSpace d m Hz) (G : ℝ → Ω' → KSpace d m Hz),
              IsAdaptedGaussianCoupling P ℱ Φ M Hz Cdet P' π ℱ' e B S Sb G ∧
              (∫⁻ w', (⨆ t : Set.Icc (0 : ℝ) Hz, ENNReal.ofReal
                  ‖reconstructPath m Hz (fun τ w => M τ (π w)) w' t -
                    reconstructPath m Hz G w' t‖) ^ 2 ∂P') ^ (1 / 2 : ℝ) ≤
                ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N)) ∧
              IsCylindricalBrownian P' ℱ'
                (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2) := by
  obtain ⟨B, hB0, hdata⟩ := s86_feat_data hd a β ha hβ m hm Hz hHz
  obtain ⟨Ccost, hC0, hcostC⟩ := HRS.MS.FinNoise.s86_cost hd a β ha hβ m hm Hz hHz Cin
  obtain ⟨K, hK0, hK⟩ := s81p_coupling_maximal d m Hz hHz.le
  refine ⟨K * Real.sqrt Ccost, ?_⟩
  intro ρβ hρβ N hN Ω mΩ P hP X₀ W X hreal ℱ hW hprog hlin
  obtain ⟨hfeat, hbnd⟩ := hdata ρβ hρβ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := HRS.Whole.Q09A.measure_isProb hρβ.1.1
  set Γ : Fin d → ℝ → Euc d → KSpace d m Hz := fun i r x =>
    gradFeature (critCoeff d a β ρβ) m Hz i (max r 0) x with hΓ
  have hΓm : ∀ i, Measurable (fun p : ℝ × Euc d => Γ i p.1 p.2) := fun i =>
    s86_feat_meas _ hfeat hHz.le i
  have hΓb : ∀ (i : Fin d) (r : ℝ) (x : Euc d), ‖Γ i r x‖ ≤ B := hbnd
  intro Φ
  have hHS : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ :=
    s86_hs_all_horizons d N m Hz β B hB0 Γ hΓm hΓb P ℱ X hprog
  refine ⟨hHS Hz, fun M hM => ?_⟩
  obtain ⟨Cdet, hCdet, hform, -⟩ := s86_reference_density d m Hz β B hβ (HRS.Whole.withDensityReal ρβ) Γ hΓm hΓb
  have hformr : ∀ r ∈ Set.Icc (0 : ℝ) Hz, ∀ u v, Cdet r u v = featureForm m Hz β⁻¹
      (fun i => gradFeature (critCoeff d a β ρβ) m Hz i r) (HRS.Whole.withDensityReal ρβ) u v := by
    intro r hr u v
    rw [hform]
    simp only [hΓ, max_eq_left hr.1]
  refine ⟨Cdet, hformr, ?_⟩
  have hδ := s86_deltaN_nonneg d N (by omega)
  set A : ℝ := Ccost * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨Ω', mΩ', P', π, ℱ', ι, hι, e, B', S, Sb, G, hcoup, hbound, hWb⟩ :=
    hK P ℱ (Fin N × Fin d) (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) hW Φ hHS M hM Cdet hCdet
      A hA0 (by
        intro r hr ι hι e S Sb hS hSb
        refine hcostC ρβ hρβ N hN P X₀ W X hreal ℱ hprog hlin r hr (Cdet r) (hformr r hr) ι e S Sb ?_ hSb
        intro z
        have := hS z
        simp only [Φ, max_eq_left hr.1] at this
        exact this)
  refine ⟨Ω', mΩ', P', π, ℱ', ι, hι, e, B', S, Sb, G, hcoup, ?_, hWb⟩
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : Real.sqrt A = Real.sqrt Ccost * Real.sqrt ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) :=
    Real.sqrt_mul hC0 _
  have h2 := s86_sqrt_le ((N : ℝ)⁻¹) (deltaN d ((d : ℝ) / 2) N) (by positivity) hδ
  have h3 : Real.sqrt ((N : ℝ)⁻¹) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
  rw [h3] at h2
  calc K * Real.sqrt A = K * Real.sqrt Ccost *
        Real.sqrt ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) := by rw [h1]; ring
    _ ≤ K * Real.sqrt Ccost * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)


end HRS.Whole.S81P
