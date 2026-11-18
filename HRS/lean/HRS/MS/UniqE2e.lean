import HRS.MS.UniqE2d

/-!
# E2 of `UniqPlan.md`, part 5: the cell energy identity for the flow cutoffs

`e2_energy_identity`: for a forward solution `z` with `LocMass B (z τ)` on `[0,t]`, the flow bundle `FlowBundle`
of `b σ = meanFieldDriftW D (ρ (t-σ))`, `ε > 0`, every centre `c` and every `τ ∈ [0,t]`:
`∫ ς_c^τ z_ε(τ)² = ∫_{[0,τ]} ( ∫ (b·∇ς_c^σ) z_ε(σ)² + 2 ⟨𝓛^σ z(σ), η_ε * (ς_c^σ z_ε(σ))⟩ ) dσ`.
(`∫ ς z_ε f_ε` is rewritten as a `forwardPairing` by `forwardPairing_superpose`.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqE2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1 HRS.MS.UniqC3

variable {d : ℕ}

theorem e2_slice_t {E : Type*} [TopologicalSpace E] {t : ℝ} {F : ℝ × Euc d → E} (hF : ContinuousOn F (Icc 0 t ×ˢ univ)) (x : Euc d) :
    ContinuousOn (fun σ => F (σ, x)) (Icc 0 t) :=
  hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun σ hσ => ⟨hσ, mem_univ _⟩)

theorem e2_slice_x {E : Type*} [TopologicalSpace E] {t : ℝ} {F : ℝ × Euc d → E} (hF : ContinuousOn F (Icc 0 t ×ˢ univ)) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) : Continuous (fun x : Euc d => F (σ, x)) :=
  continuousOn_univ.1 (hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => (⟨hσ, mem_univ _⟩ : (σ, x) ∈ Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)))))

theorem e2_energy_identity (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzB : ∀ τ ∈ Icc (0 : ℝ) t, LocMass B (z τ))
    {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K) (c : Euc d)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    ∫ x, varsigma χ Ψ τ c x * (moll d ε (z τ) x) ^ 2 =
      ∫ σ in Icc 0 τ,
        ((∫ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) *
            (moll d ε (z σ) x) ^ 2) +
          2 * forwardPairing D ρ t σ (z σ)
            (fun y => ∫ x, (varsigma χ Ψ σ c x * moll d ε (z σ) x) * eta d ε (x - y))) := by
  have hςd : ∀ x, ∀ σ ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt (fun σ => varsigma χ Ψ σ c x)
        (inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x))
        (Icc 0 t) σ := fun x σ hσ => hF.deriv σ hσ c x
  have hς'c : ∀ x, ContinuousOn (fun σ =>
      inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x)) (Icc 0 t) :=
    fun x => e2_slice_t (hF.cont_deriv c) x
  -- the compact set
  obtain ⟨MΨ, hMΨ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (f := fun σ => Ψ σ c)
    (e2_slice_t (F := fun p : ℝ × Euc d => Ψ p.1 p.2) hF.flow.cont c)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 * Real.exp (Cb * t) + MΨ := ⟨_, rfl⟩
  have hnot : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R < ‖x‖ → x ∉ tsupport (varsigma χ Ψ σ c) := by
    intro σ hσ x hx hxs
    have h1 := hF.supp σ hσ c hxs
    rw [mem_closedBall, dist_eq_norm] at h1
    have h2 := hMΨ σ hσ
    have h3 : ‖x‖ ≤ ‖x - Ψ σ c‖ + ‖Ψ σ c‖ := by
      have := norm_add_le (x - Ψ σ c) (Ψ σ c); simpa using this
    linarith
  have hς0 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R < ‖x‖ → varsigma χ Ψ σ c x = 0 :=
    fun σ hσ x hx => image_eq_zero_of_notMem_tsupport (hnot σ hσ x hx)
  have hgrad0 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R < ‖x‖ →
      gradient (varsigma χ Ψ σ c) x = 0 := by
    intro σ hσ x hx
    have hev : varsigma χ Ψ σ c =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 (hnot σ hσ x hx)
    have : fderiv ℝ (varsigma χ Ψ σ c) x = 0 := by rw [hev.fderiv_eq]; simp
    show (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (varsigma χ Ψ σ c) x) = 0
    rw [this]; simp
  obtain ⟨Mg, hMg⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := t)).prod
    (isCompact_closedBall (0 : Euc d) R)).exists_bound_of_continuousOn
    ((hF.cont_deriv c).mono (prod_mono subset_rfl (subset_univ _)))
  have key := e2_core hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε hz hzB
    (ς := fun σ x => varsigma χ Ψ σ c x)
    (ς' := fun σ x => inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x))
    (R := R) (Mg := Mg)
    (Φ := fun σ => forwardPairing D ρ t σ (z σ)
      (fun y => ∫ x, (varsigma χ Ψ σ c x * moll d ε (z σ) x) * eta d ε (x - y)))
    hςd hς'c (hF.cont c) (hF.cont_deriv c)
    (fun σ hσ => (hF.contDiff σ hσ c).continuous)
    (fun σ hσ => e2_slice_x (hF.cont_deriv c) hσ)
    (fun σ hσ x hx => ⟨hς0 σ hσ x hx, by simp [hgrad0 σ hσ x hx]⟩)
    (fun σ hσ x => by
      have := (hF.range σ hσ c x)
      rw [abs_of_nonneg this.1]; exact this.2)
    (fun σ hσ x hx => by
      have := hMg (σ, x) ⟨hσ, by simpa [mem_closedBall, dist_zero_right] using hx⟩
      simpa using this)
    (fun σ hσ => ?_) hτ
  · exact key
  · have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
    obtain ⟨hbs, -, -, hρs, hρ0, hρ1⟩ := e1_coeff hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef hr
    have hcont : Continuous (fun x => varsigma χ Ψ σ c x * moll d ε (z σ) x) :=
      (hF.contDiff σ hσ c).continuous.mul
        (moll_contDiff hε (hzB σ hσ).locallyIntegrable).continuous
    have hcs : HasCompactSupport (fun x => varsigma χ Ψ σ c x * moll d ε (z σ) x) :=
      (hF.compact_supp σ hσ c).mul_right
    exact forwardPairing_superpose D ρ t σ hs0 hsd hbs hρs _ hρ0 hρ1 (z σ) (hzB σ hσ).1 (B ^ 2)
      (hzB σ hσ).2 (eta d ε) eta_contDiff (eta_hasCompactSupport hε) _ hcont hcs

end HRS.MS.UniqE2
