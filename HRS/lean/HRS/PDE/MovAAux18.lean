import HRS.PDE.MovAAux17

/-!
# MOVA Aux18: the mean-field equation holds pointwise (`C^{1,2}` regularity + weak form).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_cont_rho_slice {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (hρt : IsC12Test T ρ ρt) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) : Continuous (ρ r) :=
  mova_continuous_of_isCk (mova_isCk_one_of_two (hρt.c2 r hr))

theorem mova_cont_ρt_slice {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (hρt : IsC12Test T ρ ρt) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) : Continuous (ρt r) :=
  (hρt.cont_time_deriv.comp (continuous_const.prodMk continuous_id :
    Continuous fun x : Torus d => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), x)))

theorem mova_hasDerivAt_pair {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (hρt : IsC12Test T ρ ρt)
    {ψ : Torus d → ℝ} (hψ : Continuous ψ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => ∫ x, ψ x * ρ r x) (∫ x, ψ x * ρt t x) t := by
  have hIcc : ∀ r ∈ Set.Ioo (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.le⟩
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_bound_of_continuousOn
    hρt.cont_time_deriv.continuousOn
  have hB' : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρt r x| ≤ max B 0 := fun r hr x => by
    have := hB (⟨r, hr⟩, x) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hmeasF : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun x => ψ x * ρ r x) volume := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact (hψ.mul (mova_cont_rho_slice hρt (hIcc r hr))).aestronglyMeasurable
  have hintF : Integrable (fun x => ψ x * ρ t x) :=
    mova_int_cont (hψ.mul (mova_cont_rho_slice hρt (hIcc t ht)))
  have hmeasF' : AEStronglyMeasurable (fun x => ψ x * ρt t x) volume :=
    (hψ.mul (mova_cont_ρt_slice hρt (hIcc t ht))).aestronglyMeasurable
  have hbound : Integrable (fun x => |ψ x| * max B 0) :=
    (mova_int_cont hψ.abs).mul_const _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun r x => ψ x * ρ r x)
    (F' := fun r x => ψ x * ρt r x) (bound := fun x => |ψ x| * max B 0) (s := Set.Ioo 0 T)
    (Ioo_mem_nhds ht.1 ht.2) hmeasF hintF hmeasF' ?_ hbound ?_).2
  · refine Filter.Eventually.of_forall fun x r hr => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB' r (hIcc r hr) x) (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun x r hr => ?_
    exact (hρt.time_deriv x r hr).const_mul (ψ x)

theorem mova_pde_Ioo (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T) {ρ ρt : ℝ → Torus d → ℝ}
    (hmf : IsMeanFieldSolution D T ρ) (hρt : IsC12Test T ρ ρt) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) :
    ∫ x, ψ x * ρt t x = ∫ x, ψ x * mova_pdeRHS D (ρ t) x := by
  have hψc := mova_continuous_of_isCk hψ
  have hcP := mova_cont_pde D hρt hV
  -- the continuous time integrand
  have hA : Continuous fun q : Set.Icc (0 : ℝ) T => ∫ x, ψ x * mova_pdeRHS D (ρ q) x := by
    have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
      (f := fun (q : Set.Icc (0 : ℝ) T) (x : Torus d) => ψ x * mova_pdeRHS D (ρ q) x)
      (hψc.comp continuous_snd |>.mul hcP) (s := Set.univ) isCompact_univ
    simpa using this
  set A' : ℝ → ℝ := fun s => ∫ x, ψ x * mova_pdeRHS D (ρ (Set.projIcc 0 T hT.le s)) x with hA'
  have hA'c : Continuous A' := hA.comp continuous_projIcc
  have hA'eq : ∀ s ∈ Set.Icc (0 : ℝ) T, A' s = ∫ x, ψ x * mova_pdeRHS D (ρ s) x := by
    intro s hs
    simp only [hA', Set.projIcc_of_mem hT.le hs]
  set Φ : ℝ → ℝ := fun r => ∫ x, ψ x * ρ r x with hΦ
  have hΦw : ∀ r ∈ Set.Icc (0 : ℝ) T, Φ r = Φ 0 + ∫ s in (0 : ℝ)..r, A' s := by
    intro r hr
    have hw := hmf.weak ψ hψ r hr
    have hpair : ∀ s ∈ Set.Icc (0 : ℝ) T, pair (withDensityReal (ρ s)) ψ = Φ s := by
      intro s hs
      unfold pair
      rw [PDE.MFPairing.integral_withDensityReal (hmf.density s hs).measurable (hmf.density s hs).nonneg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    rw [hpair r hr, hpair 0 h0] at hw
    have hint : ∫ s in Set.Icc (0 : ℝ) r, (pair (withDensityReal (ρ s)) (fun x => D.invβ *
        Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) +
          interactionPairing D ψ (withDensityReal (ρ s)) (withDensityReal (ρ s))) =
        ∫ s in Set.Icc (0 : ℝ) r, A' s := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hr.2⟩
      rw [mova_wk_eq D hM (hρt.c2 s hsT) (hmf.density s hsT) hV (ψ := ψ) hψ, hA'eq s hsT]
    rw [hint, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.1] at hw
    linarith
  have hderiv1 := mova_hasDerivAt_pair hρt hψc ht
  have hderiv2 : HasDerivAt Φ (A' t) t := by
    have h := ((hA'c.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (Φ 0)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr using hΦw r ⟨hr.1.le, hr.2.le⟩
  have := hderiv1.unique hderiv2
  rw [this]
  exact hA'eq t ⟨ht.1.le, ht.2.le⟩

end HRS
