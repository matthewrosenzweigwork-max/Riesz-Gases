import HRS.MS.S111X2Aux33

/-!
# S11.1 X2, packet H01 (part 2): sharp decay of the generator orbit `G_t = U_t (Gφ)`

`s111x2_orbit_energy`: `‖P_μ U_{0,τ}(Gφ)‖² ≤ η⁻² e^{2κ} e^{-2κτ} (‖P_μ φ‖² + ‖P_μ Gφ‖²)`, `κ = λ/β` (E07 + E08).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_cs_nonneg (μ : Measure (Euc d)) (f : Euc d → ℝ) : 0 ≤ s111x2_centeredSquare μ f :=
  integral_nonneg fun x => sq_nonneg _

theorem s111x2_orbit_energy (hd : 2 ≤ d) (s a β lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hlam : 0 < lam) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      IsR2Poincare (HRS.Whole.withDensityReal ρ) lam →
      ∀ H : ℝ, 0 < H → ∀ φ : Euc d → ℝ, MemCb 2 φ → ∀ f h : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f →
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H
          (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 φ) h →
        ∀ τ ∈ Icc (0 : ℝ) H,
          s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) (h (H - τ)) ≤
            η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ) *
              (s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) φ +
                s111x2_centeredSquare (HRS.Whole.withDensityReal ρ)
                  (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 φ)) := by
  obtain ⟨η, hη0, hη1, hall⟩ := s111x2_sharp_decay hd s a β lam β hs0 hs ha hβ hlam le_rfl
  refine ⟨η, hη0, hη1, fun ρ hρ hP H hH φ hφ f h hf hh τ hτ => ?_⟩
  obtain ⟨hRF, hdec⟩ := hall ρ hρ
  have RF := hRF β ⟨hβ.le, le_rfl⟩
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  obtain ⟨-, -, -, hDac, hDder⟩ := s111x2_generator_orbit hd hs0 hs ha hβ hH hρ hφ hf hh
  obtain ⟨hderf, hcontf⟩ := s111x2_classical_fd_deriv hd hs0 hs ha hβ hH hρ hf hf
  obtain ⟨hderh, hconth⟩ := s111x2_classical_fd_deriv hd hs0 hs ha hβ hH hρ hh hh
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hf
  obtain ⟨Bh0, Bh1, Bh2, hBh0, hBh1, hBh2, hhB⟩ := HRS.MS.S111X1.classical_bounds hh
  have hrefl : ∀ r ∈ Icc (0 : ℝ) H, H - r ∈ Icc (0 : ℝ) H := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hreflo : ∀ r ∈ Ioo (0 : ℝ) H, H - r ∈ Ioo (0 : ℝ) H := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hmemf : ∀ r ∈ Icc (0 : ℝ) H, MemLp (f r) 2 μ := fun r hr =>
    MemLp.of_bound (hf.c2 r hr).continuous.aestronglyMeasurable Bf0
      (Filter.Eventually.of_forall fun x => (hfB r hr x).1) |>.mono_exponent le_top
  have hmemh : ∀ r ∈ Icc (0 : ℝ) H, MemLp (h r) 2 μ := fun r hr =>
    MemLp.of_bound (hh.c2 r hr).continuous.aestronglyMeasurable Bh0
      (Filter.Eventually.of_forall fun x => (hhB r hr x).1) |>.mono_exponent le_top
  set Efun : ℝ → ℝ := fun t => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (f (H - t)) (f (H - t))
    with hEfun
  set Dfun : ℝ → ℝ := fun t => s111x2_dirichlet μ (f (H - t)) (f (H - t)) with hDfun
  set Ffun : ℝ → ℝ := fun t => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (h (H - t)) (h (H - t))
    with hFfun
  have hDb : ∀ r ∈ Icc (0 : ℝ) H, |s111x2_dirichlet μ (f r) (f r)| ≤ Bf1 * Bf1 := fun r hr =>
    s111x2_dirichlet_bound T (fun x => (hfB r hr x).2.1) (fun x => (hfB r hr x).2.1)
  -- E: forward energy of f
  have hcontE : ContinuousOn Efun (Icc 0 H) :=
    hcontf.comp (by fun_prop : ContinuousOn (fun r : ℝ => H - r) (Icc 0 H)) (fun r hr => hrefl r hr)
  have hderE : ∀ r ∈ Ioo (0 : ℝ) H, HasDerivAt Efun (-2 * β⁻¹ * Dfun r) r := by
    intro r hr
    have h1 : HasDerivAt (fun q : ℝ => H - q) (-1) r := by simpa using (hasDerivAt_id r).const_sub H
    have h2 := HasDerivAt.comp r (hderf (H - r) (hreflo r hr)) h1
    refine h2.congr_deriv ?_
    simp only [hDfun]; ring
  have hbdE : ∀ r ∈ Ioo (0 : ℝ) H, |-2 * β⁻¹ * Dfun r| ≤ 2 * β⁻¹ * (Bf1 * Bf1) := by
    intro r hr
    have hβ2 : 0 < 2 * β⁻¹ := by positivity
    have : -2 * β⁻¹ * Dfun r = -(2 * β⁻¹ * Dfun r) := by ring
    rw [this, abs_neg, abs_mul, abs_of_pos hβ2]
    exact mul_le_mul_of_nonneg_left (hDb _ (hrefl r ⟨hr.1.le, hr.2.le⟩)) hβ2.le
  have hEac := s111x2_ac_of_deriv_bdd hH hcontE hderE hbdE
  -- F: forward energy of the generator orbit
  have hcontF : ContinuousOn Ffun (Icc 0 H) :=
    hconth.comp (by fun_prop : ContinuousOn (fun r : ℝ => H - r) (Icc 0 H)) (fun r hr => hrefl r hr)
  have hmonoh : MonotoneOn (fun q => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (h q) (h q))
      (Icc 0 H) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 H) hconth ?_ ?_
    · rw [interior_Icc]
      exact fun r hr => (hderh r hr).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro r hr
      rw [(hderh r hr).deriv]
      have : 0 ≤ s111x2_dirichlet μ (h r) (h r) := integral_nonneg fun x => real_inner_self_nonneg
      positivity
  have hantiF : AntitoneOn Ffun (Icc 0 H) := by
    intro t₁ ht₁ t₂ ht₂ h12
    exact hmonoh (hrefl t₂ ht₂) (hrefl t₁ ht₁) (by linarith)
  -- positivity
  have hpos : ∀ t ∈ Icc (0 : ℝ) H, 0 ≤ Efun t ∧ 0 ≤ Dfun t ∧ 0 ≤ Ffun t := by
    intro t ht
    have hI := hrefl t ht
    refine ⟨?_, integral_nonneg fun x => real_inner_self_nonneg, ?_⟩
    · exact (mul_nonneg hη0.le (s111x2_cs_nonneg μ _)).trans (RF.coercive _ (hmemf _ hI)).1
    · exact (mul_nonneg hη0.le (s111x2_cs_nonneg μ _)).trans (RF.coercive _ (hmemh _ hI)).1
  -- F(0) bound
  have hF0 : Ffun 0 ≤ s111x2_centeredSquare μ (generatorW C 0 φ) := by
    have hHI : H ∈ Icc (0 : ℝ) H := ⟨hH.le, le_rfl⟩
    have := (RF.coercive _ (hmemh H hHI)).2
    simp only [hFfun, sub_zero]
    rwa [hh.terminal] at this ⊢
  have hcsφ := s111x2_cs_nonneg μ φ
  have hcsG := s111x2_cs_nonneg μ (generatorW C 0 φ)
  have hκ : 0 ≤ lam / β := by positivity
  have hinv : 1 ≤ η⁻¹ := (one_le_inv₀ hη0).2 hη1
  have hcoerc : ∀ τ ∈ Icc (0 : ℝ) H, η * s111x2_centeredSquare μ (h (H - τ)) ≤ Ffun τ := fun τ hτ =>
    (RF.coercive _ (hmemh _ (hrefl τ hτ))).1
  have hVle : ∀ τ ∈ Icc (0 : ℝ) H, s111x2_centeredSquare μ (h (H - τ)) ≤ η⁻¹ * Ffun τ := by
    intro τ hτ
    have := hcoerc τ hτ
    calc s111x2_centeredSquare μ (h (H - τ)) = η⁻¹ * (η * s111x2_centeredSquare μ (h (H - τ))) := by
          field_simp
      _ ≤ η⁻¹ * Ffun τ := by gcongr
  by_cases hτ1 : τ ≤ 1
  · -- initial layer
    have h1 : Ffun τ ≤ s111x2_centeredSquare μ (generatorW C 0 φ) :=
      (hantiF ⟨le_rfl, hH.le⟩ hτ hτ.1).trans hF0
    have hV := (hVle τ hτ).trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    have he : 1 ≤ Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc s111x2_centeredSquare μ (h (H - τ)) ≤ η⁻¹ * s111x2_centeredSquare μ (generatorW C 0 φ) := hV
      _ ≤ η⁻¹ * η⁻¹ * (Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ)) *
            (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ)) := by
          have : 1 ≤ η⁻¹ * (Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ)) := by nlinarith
          have h3 : η⁻¹ * s111x2_centeredSquare μ (generatorW C 0 φ) ≤
              η⁻¹ * (η⁻¹ * (Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ)) *
                (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ η⁻¹ * (Real.exp (2 * (lam / β)) *
              Real.exp (-2 * (lam / β) * τ)) - 1 + 0) hcsφ]
          linarith [h3]
      _ = _ := by ring
  · -- decay layer: τ ≥ 1, hence 1 ≤ H
    rw [not_le] at hτ1
    have hH1 : 1 ≤ H := by linarith [hτ.2]
    have hdE : ∀ᵐ t ∂(volume.restrict (Icc 0 H)), HasDerivAt Efun (-2 * β⁻¹ * Dfun t) t :=
      s111x2_ae_icc_of_ioo hderE
    have hdD : ∀ᵐ t ∂(volume.restrict (Icc 0 H)), HasDerivAt Dfun (-2 / β⁻¹ * Ffun t) t :=
      s111x2_ae_icc_of_ioo fun r hr => by
        have := hDder r hr
        convert this using 1
        simp only [hFfun]
        field_simp
        rfl
    have key := s111x2_fenergy_le H β⁻¹ hH1 (inv_pos.2 hβ) Efun Dfun Ffun hEac hDac hcontF hpos hantiF hdE hdD
      τ ⟨hτ1.le, hτ.2⟩
    have hτ1' : τ - 1 ∈ Icc (0 : ℝ) H := ⟨by linarith, by linarith [hτ.2]⟩
    have hEle : Efun (τ - 1) ≤ s111x2_centeredSquare μ (f (H - (τ - 1))) :=
      (RF.coercive _ (hmemf _ (hrefl _ hτ1'))).2
    have hdecτ := hdec hP H hH φ f hf (τ - 1) hτ1'
    have e1 : Real.exp (-2 * (lam / β) * (τ - 1)) = Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1] at hdecτ
    have hV := (hVle τ ⟨by linarith, hτ.2⟩).trans (mul_le_mul_of_nonneg_left
      (key.trans (hEle.trans hdecτ)) (by positivity))
    have hfinal : η⁻¹ * (η⁻¹ * (Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ)) *
        s111x2_centeredSquare μ φ) ≤ η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ) *
        (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ)) := by
      have : 0 ≤ η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ) *
          s111x2_centeredSquare μ (generatorW C 0 φ) := by positivity
      nlinarith
    exact hV.trans hfinal

end HRS.MS.S111X2
