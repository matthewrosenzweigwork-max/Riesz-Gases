import HRS.PDE.MovFAux6

/-!
# MOVF Aux7: `IsC12Test` from a weak solution with jointly continuous `C²`-jets (the core)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_isC12_core (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ}
    (hmf : IsMeanFieldSolution D T ρ) (hck : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (ρ r))
    (hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2) :
    ∃ ρt : ℝ → Torus d → ℝ, IsC12Test T ρ ρt := by
  have hcP := movf_cont_pde D hV hck hcc
  obtain ⟨G, hGdef⟩ : ∃ G : Set.Icc (0 : ℝ) T × Torus d → ℝ,
      G = fun p => mova_pdeRHS D (ρ p.1) p.2 := ⟨_, rfl⟩
  have hGc : Continuous G := by rw [hGdef]; exact hcP
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ × Torus d → ℝ,
      F = fun p => G (Set.projIcc 0 T hT p.1, p.2) := ⟨_, rfl⟩
  have hproj : Continuous fun p : ℝ × Torus d => ((Set.projIcc 0 T hT p.1, p.2) : Set.Icc (0 : ℝ) T × Torus d) :=
    (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
  have hF : Continuous F := by
    rw [hFdef]
    exact hGc.comp hproj
  have hFeq : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x, F (s, x) = mova_pdeRHS D (ρ s) x := by
    intro s hs x
    rw [hFdef, hGdef]
    simp only [Set.projIcc_of_mem hT hs]
  have hρc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (ρ r) := fun r hr =>
    mova_continuous_of_isCk (hck r hr)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  -- the integrated form
  have hE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, ρ r x = ρ 0 x + ∫ s in (0 : ℝ)..r, F (s, x) := by
    intro r hr
    have hWc : Continuous fun x => ρ r x - ρ 0 x - ∫ s in (0 : ℝ)..r, F (s, x) := by
      refine ((hρc r hr).sub (hρc 0 h0)).sub ?_
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (x : Torus d) (s : ℝ) => F (s, x)) (hF.comp (continuous_snd.prodMk continuous_fst))
        0 r
    have hz := mova_eq_zero_of_integral_zero hWc (fun ψ hψ => by
      have hψc := mova_continuous_of_isCk hψ
      -- time-continuous integrand
      have hAc : Continuous fun s : ℝ => ∫ x, ψ x * F (s, x) := by
        have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
          (f := fun (s : ℝ) (x : Torus d) => ψ x * F (s, x))
          ((hψc.comp continuous_snd).mul hF) (s := Set.univ) isCompact_univ
        simpa using this
      have hweak := hmf.weak ψ hψ r hr
      have hpair : ∀ s ∈ Set.Icc (0 : ℝ) T, pair (withDensityReal (ρ s)) ψ = ∫ x, ψ x * ρ s x := by
        intro s hs
        unfold pair
        rw [PDE.MFPairing.integral_withDensityReal (hmf.density s hs).measurable (hmf.density s hs).nonneg]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      rw [hpair r hr, hpair 0 h0] at hweak
      have hint : ∫ s in Set.Icc (0 : ℝ) r, (pair (withDensityReal (ρ s)) (fun x => D.invβ *
          Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) +
            interactionPairing D ψ (withDensityReal (ρ s)) (withDensityReal (ρ s))) =
          ∫ s in Set.Icc (0 : ℝ) r, ∫ x, ψ x * F (s, x) := by
        refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
        have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hr.2⟩
        rw [mova_wk_eq D hM (hck s hsT) (hmf.density s hsT) hV (ψ := ψ) hψ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hFeq s hsT x]
      rw [hint, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.1] at hweak
      -- Fubini
      have hswap : ∫ s in (0 : ℝ)..r, ∫ x, ψ x * F (s, x) =
          ∫ x, ∫ s in (0 : ℝ)..r, ψ x * F (s, x) := by
        refine intervalIntegral_integral_swap ?_
        -- integrability on `uIoc 0 r × torus`
        have hcont : Continuous (Function.uncurry fun (s : ℝ) (x : Torus d) => ψ x * F (s, x)) :=
          (hψc.comp continuous_snd).mul hF
        obtain ⟨Bψ, hBψ⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hψc.continuousOn
        obtain ⟨BG, hBG⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_bound_of_continuousOn
          hGc.continuousOn
        have hr0 : 0 ≤ r := hr.1
        rw [Set.uIoc_of_le hr0]
        refine Integrable.of_bound (C := Bψ * BG) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
        show ‖ψ p.2 * F (p.1, p.2)‖ ≤ Bψ * BG
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |ψ p.2| ≤ Bψ := by simpa using hBψ p.2 trivial
        have h2 : |F (p.1, p.2)| ≤ BG := by
          rw [hFdef]; simpa using hBG (Set.projIcc 0 T hT p.1, p.2) trivial
        exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
      have e1 : ∫ x, ψ x * ∫ s in (0 : ℝ)..r, F (s, x) =
          ∫ x, ∫ s in (0 : ℝ)..r, ψ x * F (s, x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only [intervalIntegral.integral_const_mul])
      have hρi : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable fun x => ψ x * ρ s x := fun s hs =>
        mova_int_cont (hψc.mul (hρc s hs))
      have hsub : ∫ x, ψ x * (ρ r x - ρ 0 x - ∫ s in (0 : ℝ)..r, F (s, x)) =
          (∫ x, ψ x * ρ r x) - (∫ x, ψ x * ρ 0 x) - ∫ x, ψ x * ∫ s in (0 : ℝ)..r, F (s, x) := by
        have hI3 : Integrable fun x => ψ x * ∫ s in (0 : ℝ)..r, F (s, x) := by
          refine mova_int_cont (hψc.mul ?_)
          exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            (f := fun (x : Torus d) (s : ℝ) => F (s, x)) (hF.comp (continuous_snd.prodMk continuous_fst))
            0 r
        have e : (fun x => ψ x * (ρ r x - ρ 0 x - ∫ s in (0 : ℝ)..r, F (s, x))) =
            fun x => (ψ x * ρ r x - ψ x * ρ 0 x) - ψ x * ∫ s in (0 : ℝ)..r, F (s, x) :=
          funext fun x => by ring
        have i12 : Integrable fun x => ψ x * ρ r x - ψ x * ρ 0 x := (hρi r hr).sub (hρi 0 h0)
        rw [e, integral_sub i12 hI3, integral_sub (hρi r hr) (hρi 0 h0)]
      rw [hsub, e1, ← hswap]
      linarith)
    intro x
    have := hz x
    linarith
  -- time derivative
  refine ⟨fun r x => mova_pdeRHS D (ρ r) x, hck, hcc, fun x r hr => ?_, ?_⟩
  · have hrI : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have hcu : Continuous fun s : ℝ => F (s, x) := hF.comp (continuous_id.prodMk continuous_const)
    have hd := (hcu.integral_hasStrictDerivAt 0 r).hasDerivAt.const_add (ρ 0 x)
    have hd' : HasDerivAt (fun r => ρ r x) (F (r, x)) r := by
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs using hE s ⟨hs.1.le, hs.2.le⟩ x
    rwa [hFeq r hrI x] at hd'
  · exact hcP
end HRS

end
