import HRS.MS.UniqG2aInt
import HRS.MS.UniqE3i
import HRS.MS.UniqE4h

/-!
# G2a of `UniqPlan.md`: the per-cell master inequality

`g2a_integrable`: the integrand `I σ` of `e2_energy_identity` is integrable on `[0,t]`
(route (a): the proof of `e2_core` re-run with the integrability conclusion, `e2_core_int`).
`g2a_master`: combining `e2_energy_identity`, `e3_forwardPairing_form` and `e4_nonlocal_residue`
(no regime-specific nonlocal estimate is used).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqG2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1 HRS.MS.UniqC3 HRS.MS.UniqE2 HRS.MS.UniqE3 HRS.MS.UniqE4

variable {d : ℕ}

/-- Integrability of the integrand of `e2_energy_identity` on `[0,t]`. -/
theorem g2a_integrable (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzB : ∀ τ ∈ Icc (0 : ℝ) t, LocMass B (z τ))
    {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K) (c : Euc d) :
    IntegrableOn (fun σ =>
        (∫ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) *
            (moll d ε (z σ) x) ^ 2) +
          2 * forwardPairing D ρ t σ (z σ)
            (fun y => ∫ x, (varsigma χ Ψ σ c x * moll d ε (z σ) x) * eta d ε (x - y)))
      (Icc 0 t) := by
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
  refine e2_core_int hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε hz hzB
    (ς := fun σ x => varsigma χ Ψ σ c x)
    (ς' := fun σ x => inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x))
    (R := R) (Mg := Mg)
    (Φ := fun σ => forwardPairing D ρ t σ (z σ)
      (fun y => ∫ x, (varsigma χ Ψ σ c x * moll d ε (z σ) x) * eta d ε (x - y)))
    (hF.cont c) (hF.cont_deriv c)
    (fun σ hσ => (hF.contDiff σ hσ c).continuous)
    (fun σ hσ => e2_slice_x (hF.cont_deriv c) hσ)
    (fun σ hσ x hx => ⟨hς0 σ hσ x hx, by simp [hgrad0 σ hσ x hx]⟩)
    (fun σ hσ x => by
      have := (hF.range σ hσ c x)
      rw [abs_of_nonneg this.1]; exact this.2)
    (fun σ hσ x hx => by
      have := hMg (σ, x) ⟨hσ, by simpa [mem_closedBall, dist_zero_right] using hx⟩
      simpa using this)
    (fun σ hσ => ?_)
  have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  obtain ⟨hbs, -, -, hρs, hρ0, hρ1⟩ := e1_coeff hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef hr
  have hcont : Continuous (fun x => varsigma χ Ψ σ c x * moll d ε (z σ) x) :=
    (hF.contDiff σ hσ c).continuous.mul
      (moll_contDiff hε (hzB σ hσ).locallyIntegrable).continuous
  have hcs : HasCompactSupport (fun x => varsigma χ Ψ σ c x * moll d ε (z σ) x) :=
    (hF.compact_supp σ hσ c).mul_right
  exact forwardPairing_superpose D ρ t σ hs0 hsd hbs hρs _ hρ0 hρ1 (z σ) (hzB σ hσ).1 (B ^ 2)
    (hzB σ hσ).2 (eta d ε) eta_contDiff (eta_hasCompactSupport hε) _ hcont hcs

theorem g2a_master (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (hm : 1 ≤ m) (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ) (hν : 0 ≤ D.invβ)
    (hb : IsAdvectingDrift m Cb t (fun σ => meanFieldDriftW D (ρ (t - σ))))
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ} (hB : 0 ≤ B)
    (hzu : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (z τ) ≤ ENNReal.ofReal B) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ c : Euc d, ∃ I : ℝ → ℝ,
      IntervalIntegrable I MeasureTheory.volume 0 t ∧
      (∀ τ ∈ Set.Icc (0:ℝ) t, ∫ x, varsigma χ Ψ τ c x * moll d ε (z τ) x ^ 2 =
        ∫ σ in (0:ℝ)..τ, I σ) ∧
      ∀ σ ∈ Set.Icc (0:ℝ) t, I σ ≤
        -(D.invβ * ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2) +
          C₁ * (D.invβ + 1) * (cellEnergy χ Ψ σ (moll d ε (z σ))).toReal + C₂ * ε * B ^ 2 -
          2 * HRS.MS.UniqNDefs.nMain D (ρ (t - σ)) (moll d ε (z σ))
            (fun x => varsigma χ Ψ σ c x * moll d ε (z σ) x) := by
  have ht0 : 0 ≤ t := ht.1
  obtain ⟨C₁, C₂, h1, h2, hE3⟩ := e3_forwardPairing_form hν ht0 hm hχ hb hF
  obtain ⟨CE, hCE, hE4⟩ := e4_nonlocal_residue hd hs0 hsd hcoef ht hχ hF
  have hLM : ∀ τ ∈ Icc (0 : ℝ) t, LocMass B (z τ) := fun τ hτ =>
    locMass_of_ulocNormE hχ hB (hzu τ hτ)
  refine ⟨C₁, C₂ + 2 * CE, h1, by positivity, fun ε hε hε1 c => ?_⟩
  refine ⟨fun σ =>
    (∫ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) *
        (moll d ε (z σ) x) ^ 2) +
      2 * forwardPairing D ρ t σ (z σ) (phiTest d χ Ψ σ c ε (z σ)), ?_, ?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]
    exact g2a_integrable hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε hz hLM hF c
  · intro τ hτ
    rw [intervalIntegral.integral_of_le hτ.1, ← integral_Icc_eq_integral_Ioc]
    exact e2_energy_identity hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε hz hLM hF c hτ
  · intro σ hσ
    have a1 := hE3 (z σ) B hB (hzu σ hσ) σ hσ ε hε hε1 c
    have a2 := hE4 (z σ) B hB (hzu σ hσ) σ hσ ε hε hε1 c
    rw [abs_le] at a2
    have : (C₂ + 2 * CE) * ε * B ^ 2 = C₂ * ε * B ^ 2 + 2 * (CE * ε * B ^ 2) := by ring
    rw [this]
    linarith [a2.1, a2.2]

end HRS.MS.UniqG2a
