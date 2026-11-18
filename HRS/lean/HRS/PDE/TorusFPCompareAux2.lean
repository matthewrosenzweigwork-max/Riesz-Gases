import HRS.PDE.TorusFPCompareAux1
import HRS.PDE.TorusFPExistAux2
import HRS.PDE.TorusFPExistAux17
import HRS.PDE.TorusFPExistAux7
import HRS.Stochastic.EmpiricalIto

/-!
# D1 comparison, helper 2: stationarity of the Gibbs weight along backward solutions

For a classical backward solution `f` of `∂_r f = -(κΔf - ∇U·∇f)` on `[0,t]` with terminal datum `ψ`,
`∫ f_0 G dx = ∫ ψ G dx`, `G = exp(-U/κ)`.  Proof: `g(s) = ∫ f_s G dx` is continuous on `[0,t]`,
differentiable on `(0,t)` with derivative `-∫ (L f_s) G dx = 0` (`d1c_ibp`), so `g(t) = g(0)` by the
mean value theorem.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS

variable {n : ℕ}

theorem d1c_stationary {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {t : ℝ}
    (ht : 0 < t) {ψ : Torus n → ℝ} {f : ℝ → Torus n → ℝ}
    (hf : D1BackwardSolution κ (d1_gradDrift U) t ψ f) :
    (∫ x, f 0 x * d1_gibbsWeight κ U x) = ∫ x, ψ x * d1_gibbsWeight κ U x := by
  have hU1 : Torus.IsCk 1 U := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift U) := hU
    exact h.of_le (by norm_num)
  have hGc : Continuous (fun x => d1_gibbsWeight κ U x) :=
    Torus.continuous_of_continuous_lift
      (show ContDiff ℝ 1 (Torus.lift (fun x => d1_gibbsWeight κ U x)) from
        d1c_gibbs_isCk1 (κ := κ) hU1).continuous
  have hI : IsCompact (Set.Icc 0 t ×ˢ (Set.univ : Set (Torus n))) :=
    isCompact_Icc.prod isCompact_univ
  have hjoint : ContinuousOn (fun p : ℝ × Torus n => f p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    continuousOn_Icc_prod_of_subtype hf.continuous_joint
  have hgen : ContinuousOn (fun p : ℝ × Torus n => d1_gen κ (d1_gradDrift U) (f p.1) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) :=
    continuousOn_Icc_prod_of_subtype hf.cont_time_deriv
  obtain ⟨Cf, hCf⟩ : ∃ C : ℝ, ∀ p ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Torus n)),
      ‖f p.1 p.2‖ ≤ C := hI.exists_bound_of_continuousOn hjoint
  obtain ⟨Cd, hCd⟩ : ∃ C : ℝ, ∀ p ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Torus n)),
      ‖d1_gen κ (d1_gradDrift U) (f p.1) p.2‖ ≤ C := hI.exists_bound_of_continuousOn hgen
  obtain ⟨Gm, hGm⟩ : ∃ C : ℝ, ∀ x : Torus n, ‖d1_gibbsWeight κ U x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hGc.continuousOn
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  have hcont_s : ∀ s ∈ Set.Icc 0 t, Continuous (f s) := fun s hs =>
    d1_continuous_of_isCk2 (hf.c2 s hs)
  have htime : ∀ x : Torus n, ContinuousOn (fun s => f s x) (Set.Icc 0 t) := fun x =>
    hjoint.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, Set.mem_univ _⟩)
  have hFb : ∀ s ∈ Set.Icc 0 t, ∀ x : Torus n, ‖f s x * d1_gibbsWeight κ U x‖ ≤ Cf * Gm := by
    intro s hs x
    have h1 : ‖f s x‖ ≤ Cf := hCf (s, x) (Set.mk_mem_prod hs (Set.mem_univ x))
    have h2 : ‖d1_gibbsWeight κ U x‖ ≤ Gm := hGm x
    calc ‖f s x * d1_gibbsWeight κ U x‖ = ‖f s x‖ * ‖d1_gibbsWeight κ U x‖ := norm_mul _ _
      _ ≤ Cf * Gm := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hgen_s : ∀ s ∈ Set.Icc 0 t, Continuous (fun x => d1_gen κ (d1_gradDrift U) (f s) x) :=
    fun s hs => d1_gen_continuous (d1_gradDrift_continuous hU) (hf.c2 s hs)
  have hint_c : ∀ g : Torus n → ℝ, Continuous g → Integrable g := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgcont : ContinuousOn (fun s => ∫ x, f s x * d1_gibbsWeight κ U x) (Set.Icc 0 t) := by
    refine continuousOn_of_dominated (bound := fun _ => Cf * Gm)
      (fun s hs => ((hcont_s s hs).mul hGc).aestronglyMeasurable)
      (fun s hs => ae_of_all _ (fun x => hFb s hs x)) (integrable_const _)
      (ae_of_all _ fun x => (htime x).mul continuousOn_const)
  have hderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun s => ∫ x, f s x * d1_gibbsWeight κ U x)
      (∫ x, (-(d1_gen κ (d1_gradDrift U) (f s) x)) * d1_gibbsWeight κ U x) s := by
    intro s hs
    have hsI : s ∈ Set.Icc 0 t := ⟨hs.1.le, hs.2.le⟩
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun s' x => f s' x * d1_gibbsWeight κ U x)
      (F' := fun s' x => (-(d1_gen κ (d1_gradDrift U) (f s') x)) * d1_gibbsWeight κ U x)
      (x₀ := s) (s := Set.Ioo 0 t) (bound := fun _ => Cd * Gm)
      (Ioo_mem_nhds hs.1 hs.2) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
    · exact Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun s' hs' =>
        ((hcont_s s' ⟨hs'.1.le, hs'.2.le⟩).mul hGc).aestronglyMeasurable
    · exact hint_c _ ((hcont_s s hsI).mul hGc)
    · exact ((((hgen_s s hsI).neg).mul hGc)).aestronglyMeasurable
    · refine ae_of_all _ fun a s' hs' => ?_
      rw [norm_mul, norm_neg]
      have h1 : ‖d1_gen κ (d1_gradDrift U) (f s') a‖ ≤ Cd := hCd (s', a)
        ⟨⟨hs'.1.le, hs'.2.le⟩, Set.mem_univ _⟩
      exact mul_le_mul h1 (hGm a) (norm_nonneg _) ((norm_nonneg _).trans h1)
    · refine ae_of_all _ fun a s' hs' => ?_
      exact (hf.time_deriv a s' hs').mul_const (d1_gibbsWeight κ U a)
  have hzero : ∀ s ∈ Set.Ioo 0 t,
      (∫ x, (-(d1_gen κ (d1_gradDrift U) (f s) x)) * d1_gibbsWeight κ U x) = 0 := by
    intro s hs
    simp_rw [neg_mul]
    rw [integral_neg, d1c_ibp hκ hU (hf.c2 s ⟨hs.1.le, hs.2.le⟩), neg_zero]
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope
    (fun s => ∫ x, f s x * d1_gibbsWeight κ U x)
    (fun s => ∫ x, (-(d1_gen κ (d1_gradDrift U) (f s) x)) * d1_gibbsWeight κ U x)
    ht hgcont hderiv
  have hc0 := hzero c hc
  simp only [hc0] at hceq
  have hdiff : (∫ x, f t x * d1_gibbsWeight κ U x) - ∫ x, f 0 x * d1_gibbsWeight κ U x = 0 := by
    rcases div_eq_zero_iff.1 hceq.symm with h | h
    · exact h
    · exfalso
      linarith
  have hterm : (∫ x, f t x * d1_gibbsWeight κ U x) = ∫ x, ψ x * d1_gibbsWeight κ U x := by
    rw [hf.terminal]
  linarith

end HRS
