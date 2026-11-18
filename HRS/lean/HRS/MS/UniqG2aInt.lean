import HRS.MS.UniqE2e

/-!
# G2a of `UniqPlan.md`, part 1: integrability of the integrand of the energy identity

`e2_core_int` has the hypotheses of `e2_core` (with `τ = t`) and concludes that
`σ ↦ ∫ ς' z_ε² + 2 Φ σ` is integrable on `[0,t]` (so that the Bochner integral in `e2_core` is not junk).
`e2_energy_identity_int` is the version for the flow cutoffs `varsigma` (same hypotheses as
`e2_energy_identity`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqG2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1 HRS.MS.UniqC3 HRS.MS.UniqE2

variable {d : ℕ}

/-- Joint integrability on `[0,τ] × B̄(0,R)` (the integrability half of `e2_fubini`). -/
theorem g2a_fubini_int {τ R M : ℝ} {G : ℝ → Euc d → ℝ}
    (hG : AEStronglyMeasurable (fun p : ℝ × Euc d => G p.1 p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))))
    (hout : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ x : Euc d, R < ‖x‖ → G σ x = 0)
    (hin : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ x : Euc d, ‖x‖ ≤ R → |G σ x| ≤ M) :
    Integrable (fun σ => ∫ x, G σ x) (volume.restrict (Icc 0 τ)) := by
  set g : Euc d → ℝ := (closedBall (0 : Euc d) R).indicator (fun _ => |M|) with hg
  have hgi : Integrable g volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
  have hbound : Integrable (fun p : ℝ × Euc d => (1 : ℝ) * g p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) :=
    (integrable_const (1 : ℝ)).mul_prod hgi
  have hae : ∀ᵐ p ∂((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))),
      p.1 ∈ Icc (0 : ℝ) τ := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hint : Integrable (fun p : ℝ × Euc d => G p.1 p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) := by
    refine hbound.mono' hG ?_
    filter_upwards [hae] with p hp
    by_cases hx : ‖p.2‖ ≤ R
    · have : g p.2 = |M| := by
        rw [hg, indicator_of_mem (by simpa [mem_closedBall, dist_zero_right] using hx)]
      rw [this, one_mul, Real.norm_eq_abs]
      exact (hin p.1 hp p.2 hx).trans (le_abs_self _)
    · rw [not_le] at hx
      rw [hout p.1 hp p.2 hx]; simp only [norm_zero]
      rw [one_mul]
      exact indicator_nonneg (fun _ _ => abs_nonneg _) _
  exact hint.integral_prod_left

theorem e2_core_int (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzB : ∀ τ ∈ Icc (0 : ℝ) t, LocMass B (z τ))
    {ς ς' : ℝ → Euc d → ℝ} {R Mg : ℝ} {Φ : ℝ → ℝ}
    (hςm : ContinuousOn (fun p : ℝ × Euc d => ς p.1 p.2) (Icc 0 t ×ˢ univ))
    (hς'm : ContinuousOn (fun p : ℝ × Euc d => ς' p.1 p.2) (Icc 0 t ×ˢ univ))
    (hςx : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (ς σ))
    (hς'x : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (ς' σ))
    (hout : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R < ‖x‖ → ς σ x = 0 ∧ ς' σ x = 0)
    (h1 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |ς σ x| ≤ 1)
    (hMg : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → |ς' σ x| ≤ Mg)
    (hΦ : ∀ σ ∈ Icc (0 : ℝ) t,
      ∫ x, ς σ x * moll d ε (z σ) x * fEps D ρ t z ε σ x = Φ σ) :
    IntegrableOn (fun σ => (∫ x, ς' σ x * (moll d ε (z σ) x) ^ 2) + 2 * Φ σ) (Icc 0 t) := by
  have ht0 : 0 ≤ t := ht.1
  have hτ : t ∈ Icc (0 : ℝ) t := ⟨ht0, le_rfl⟩
  have hzB' : ∀ τ ∈ Icc (0 : ℝ) t, LocMass |B| (z τ) := fun τ hτ =>
    (hzB τ hτ).mono_B (by rw [abs_abs])
  obtain ⟨C0, hC00, hC0⟩ := moll_iteratedFDeriv_le (d := d) hε 0
  obtain ⟨C, hC0', hCmain⟩ := e1_bound_lipschitz hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε
  obtain ⟨hfint, hfbd, hlip⟩ := hCmain z hz |B| (abs_nonneg B) hzB'
  have hZbd : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |moll d ε (z σ) x| ≤ C0 * |B| := by
    intro σ hσ x
    have := hC0 |B| (z σ) (abs_nonneg B) (hzB' σ hσ) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hZc : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (moll d ε (z σ)) := fun σ hσ =>
    (moll_contDiff hε (hzB' σ hσ).locallyIntegrable).continuous
  have hZt : ∀ x, ContinuousOn (fun σ => moll d ε (z σ) x) (Icc 0 t) := by
    intro x
    have hnn : 0 ≤ C * |B| * (1 + ‖x‖) := by positivity
    have : LipschitzOnWith (C * |B| * (1 + ‖x‖)).toNNReal (fun σ => moll d ε (z σ) x) (Icc 0 t) :=
      LipschitzOnWith.of_dist_le_mul fun a ha b hb => by
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hnn]
        exact hlip a ha b hb x
    exact this.continuousOn
  have hfm : AEStronglyMeasurable (fun p : ℝ × Euc d => fEps D ρ t z ε p.1 p.2)
      ((volume.restrict (Icc 0 t)).prod (volume : Measure (Euc d))) :=
    e1_aestronglyMeasurable hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε hz hzB'
  have hZm := e2_moll_aesm (z := z) (ε := ε) ht0 le_rfl hZt hZc
  have hςae := e2_ae_of_contOn (τ := t) le_rfl hςm
  have hς'ae := e2_ae_of_contOn (τ := t) le_rfl hς'm
  set G : ℝ → Euc d → ℝ := fun σ x =>
    ς' σ x * (moll d ε (z σ) x) ^ 2 + 2 * (ς σ x * moll d ε (z σ) x * fEps D ρ t z ε σ x) with hG
  have hGm : AEStronglyMeasurable (fun p : ℝ × Euc d => G p.1 p.2)
      ((volume.restrict (Icc 0 t)).prod (volume : Measure (Euc d))) := by
    have := (hς'ae.mul (hZm.mul hZm)).add (aestronglyMeasurable_const (b := (2 : ℝ)) |>.mul
      ((hςae.mul hZm).mul hfm))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [hG, sq]
    rfl
  have hGout : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R < ‖x‖ → G σ x = 0 := by
    intro σ hσ x hx
    obtain ⟨h0, h0'⟩ := hout σ hσ x hx
    simp [hG, h0, h0']
  set a : ℝ := C0 * |B| with ha
  set e : ℝ := C * |B| * (1 + R) with he
  have hGin : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → |G σ x| ≤ Mg * a ^ 2 + 2 * (a * e) := by
    intro σ hσ x hx
    have hz1 := hZbd σ hσ x
    have hf1 : |fEps D ρ t z ε σ x| ≤ e := by
      refine (hfbd σ hσ x).trans ?_
      simp only [he]
      gcongr
    have hs1 := h1 σ hσ x
    have hg1 := hMg σ hσ x hx
    have ha0 : 0 ≤ a := (abs_nonneg _).trans hz1
    have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans hg1
    have he0 : 0 ≤ e := (abs_nonneg _).trans hf1
    simp only [hG]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_pow]
      exact mul_le_mul hg1 (pow_le_pow_left₀ (abs_nonneg _) hz1 2) (by positivity) hMg0
    · rw [abs_mul, abs_mul, abs_mul, abs_two]
      have : |ς σ x| * |moll d ε (z σ) x| * |fEps D ρ t z ε σ x| ≤ 1 * a * e :=
        mul_le_mul (mul_le_mul hs1 hz1 (abs_nonneg _) zero_le_one) hf1 (abs_nonneg _)
          (by positivity)
      linarith
  have hI := g2a_fubini_int hGm hGout hGin
  have hIe : IntegrableOn (fun σ => ∫ x, G σ x) (Icc 0 t) := hI
  refine hIe.congr_fun (fun σ hσ => ?_) measurableSet_Icc
  have hcs : ∀ g : Euc d → ℝ, (∀ x, R < ‖x‖ → g x = 0) → HasCompactSupport g := fun g hg =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R) fun x hx => hg x (by
      simpa [mem_closedBall, dist_zero_right] using hx)
  have hfc : Continuous (fun x => fEps D ρ t z ε σ x) :=
    e1_cont_x hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε (hzB' σ hσ) hσ
  have i1 : Integrable (fun x => ς' σ x * (moll d ε (z σ) x) ^ 2) volume := by
    refine Continuous.integrable_of_hasCompactSupport ((hς'x σ hσ).mul ((hZc σ hσ).pow 2))
      (hcs _ fun x hx => ?_)
    simp [(hout σ hσ x hx).2]
  have i2 : Integrable (fun x => ς σ x * moll d ε (z σ) x * fEps D ρ t z ε σ x) volume := by
    refine Continuous.integrable_of_hasCompactSupport (((hςx σ hσ).mul (hZc σ hσ)).mul hfc)
      (hcs _ fun x hx => ?_)
    simp [(hout σ hσ x hx).1]
  simp only [hG]
  rw [integral_add i1 (i2.const_mul 2), integral_const_mul, hΦ σ hσ]

end HRS.MS.UniqG2a
