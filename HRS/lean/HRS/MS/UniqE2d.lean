import HRS.MS.UniqE2c

/-!
# E2 of `UniqPlan.md`, part 4: the abstract energy identity

`e2_core`: for an abstract family `ς(σ,x)`, `C¹` in `σ` with derivative `ς'`, supported in a fixed ball in `x`,
`∫ ς(τ) z_ε(τ)² = ∫_{[0,τ]} ( ∫ ς' z_ε² + 2 Φ(σ) )`, where `Φ(σ) = ∫ ς(σ) z_ε(σ) f_ε(σ)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqE2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1

variable {d : ℕ}

theorem e2_core (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzB : ∀ τ ∈ Icc (0 : ℝ) t, LocMass B (z τ))
    {ς ς' : ℝ → Euc d → ℝ} {R Mg : ℝ} {Φ : ℝ → ℝ}
    (hςd : ∀ x, ∀ σ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun σ => ς σ x) (ς' σ x) (Icc 0 t) σ)
    (hς'c : ∀ x, ContinuousOn (fun σ => ς' σ x) (Icc 0 t))
    (hςm : ContinuousOn (fun p : ℝ × Euc d => ς p.1 p.2) (Icc 0 t ×ˢ univ))
    (hς'm : ContinuousOn (fun p : ℝ × Euc d => ς' p.1 p.2) (Icc 0 t ×ˢ univ))
    (hςx : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (ς σ))
    (hς'x : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (ς' σ))
    (hout : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R < ‖x‖ → ς σ x = 0 ∧ ς' σ x = 0)
    (h1 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |ς σ x| ≤ 1)
    (hMg : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → |ς' σ x| ≤ Mg)
    (hΦ : ∀ σ ∈ Icc (0 : ℝ) t,
      ∫ x, ς σ x * moll d ε (z σ) x * fEps D ρ t z ε σ x = Φ σ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    ∫ x, ς τ x * (moll d ε (z τ) x) ^ 2 =
      ∫ σ in Icc 0 τ, ((∫ x, ς' σ x * (moll d ε (z σ) x) ^ 2) + 2 * Φ σ) := by
  have ht0 : 0 ≤ t := ht.1
  have hsub : ∀ σ ∈ Icc (0 : ℝ) τ, σ ∈ Icc (0 : ℝ) t := fun σ hσ => ⟨hσ.1, hσ.2.trans hτ.2⟩
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
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) :=
    (e1_aestronglyMeasurable hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε hz hzB').mono_measure
      (Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hτ.2) le_rfl) le_rfl)
  have hZm := e2_moll_aesm (z := z) (ε := ε) ht0 hτ.2 hZt hZc
  have hςae := e2_ae_of_contOn (τ := τ) hτ.2 hςm
  have hς'ae := e2_ae_of_contOn (τ := τ) hτ.2 hς'm
  set G : ℝ → Euc d → ℝ := fun σ x =>
    ς' σ x * (moll d ε (z σ) x) ^ 2 + 2 * (ς σ x * moll d ε (z σ) x * fEps D ρ t z ε σ x) with hG
  have hGm : AEStronglyMeasurable (fun p : ℝ × Euc d => G p.1 p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) := by
    have := (hς'ae.mul (hZm.mul hZm)).add (aestronglyMeasurable_const (b := (2 : ℝ)) |>.mul
      ((hςae.mul hZm).mul hfm))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [hG, sq]
    rfl
  -- support and bound
  have hGout : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ x : Euc d, R < ‖x‖ → G σ x = 0 := by
    intro σ hσ x hx
    obtain ⟨h0, h0'⟩ := hout σ (hsub σ hσ) x hx
    simp [hG, h0, h0']
  set a : ℝ := C0 * |B| with ha
  set e : ℝ := C * |B| * (1 + R) with he
  have hGin : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ x : Euc d, ‖x‖ ≤ R → |G σ x| ≤ Mg * a ^ 2 + 2 * (a * e) := by
    intro σ hσ x hx
    have hσ' := hsub σ hσ
    have hz1 := hZbd σ hσ' x
    have hf1 : |fEps D ρ t z ε σ x| ≤ e := by
      refine (hfbd σ hσ' x).trans ?_
      simp only [he]
      gcongr
    have hs1 := h1 σ hσ' x
    have hg1 := hMg σ hσ' x hx
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
  -- the pointwise identity and Fubini
  have hpt : ∀ x, ς τ x * (moll d ε (z τ) x) ^ 2 = ∫ σ in Icc 0 τ, G σ x := fun x =>
    e2_pointwise hε hz hfint hςd hς'c hτ x
  rw [integral_congr_ae (Eventually.of_forall hpt),
    e2_fubini hGm hGout hGin]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  have hσ' := hsub σ hσ
  have hcs : ∀ g : Euc d → ℝ, (∀ x, R < ‖x‖ → g x = 0) → HasCompactSupport g := fun g hg =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R) fun x hx => hg x (by
      simpa [mem_closedBall, dist_zero_right] using hx)
  have hfc : Continuous (fun x => fEps D ρ t z ε σ x) :=
    e1_cont_x hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε (hzB' σ hσ') hσ'
  have i1 : Integrable (fun x => ς' σ x * (moll d ε (z σ) x) ^ 2) volume := by
    refine Continuous.integrable_of_hasCompactSupport ((hς'x σ hσ').mul ((hZc σ hσ').pow 2))
      (hcs _ fun x hx => ?_)
    simp [(hout σ hσ' x hx).2]
  have i2 : Integrable (fun x => ς σ x * moll d ε (z σ) x * fEps D ρ t z ε σ x) volume := by
    refine Continuous.integrable_of_hasCompactSupport (((hςx σ hσ').mul (hZc σ hσ')).mul hfc)
      (hcs _ fun x hx => ?_)
    simp [(hout σ hσ' x hx).1]
  simp only [hG]
  rw [integral_add i1 (i2.const_mul 2), integral_const_mul, hΦ σ hσ']

end HRS.MS.UniqE2
