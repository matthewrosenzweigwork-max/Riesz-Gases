import HRS.MC.D3EW
import HRS.MC.D3T1Aux1

/-!
# Packet D3TW, helper 1: smoothness of parametric integrals, smoothness of `w_λ` away from `0`,
the finite-sum representation of the periodised kernel, a lattice-point count.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TW

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3EW HRS.MC.D3T1

variable {d : ℕ}

theorem d3tw_contDiff_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hJfin : volume J < ⊤) (hU : IsOpen U) (hJU : J ⊆ U)
    (m : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : ℝ → E → F),
      ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ) →
      (∀ k : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ z, ‖iteratedFDeriv ℝ k (K t) z‖ ≤ B) →
      ContDiff ℝ m (fun z => ∫ t in J, K t z) := by
  induction m with
  | zero =>
    intro F _ _ _ K hK hB
    obtain ⟨B0, hB0⟩ := hB 0
    obtain ⟨B1, hB1⟩ := hB 1
    have hd : Differentiable ℝ (fun z => ∫ t in J, K t z) := fun y =>
      (d3ew_hasFDerivAt_integral hJm hJfin hU hJU hK (B0 := B0) (B1 := B1)
        (fun t ht z => by simpa using hB0 t ht z)
        (fun t ht z => by
          have := hB1 t ht z
          rwa [norm_iteratedFDeriv_one] at this) y).differentiableAt
    exact contDiff_zero.2 hd.continuous
  | succ m ih =>
    intro F _ _ _ K hK hB
    set K' : ℝ → E → (E →L[ℝ] F) := fun t z => fderiv ℝ (K t) z with hK'
    have hK'd : ContDiffOn ℝ ∞ (Function.uncurry K') (U ×ˢ univ) := d3ew_contDiffOn_fderiv hU hK
    have hB' : ∀ k : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ z, ‖iteratedFDeriv ℝ k (K' t) z‖ ≤ B := by
      intro k
      obtain ⟨B, hB⟩ := hB (k + 1)
      refine ⟨B, fun t ht z => ?_⟩
      show ‖iteratedFDeriv ℝ k (fderiv ℝ (K t)) z‖ ≤ B
      rw [norm_iteratedFDeriv_fderiv]
      exact hB t ht z
    obtain ⟨B0, hB0⟩ := hB 0
    obtain ⟨B1, hB1⟩ := hB 1
    have hderiv : ∀ y, HasFDerivAt (fun z => ∫ t in J, K t z) (∫ t in J, K' t y) y := fun y =>
      d3ew_hasFDerivAt_integral hJm hJfin hU hJU hK (B0 := B0) (B1 := B1)
        (fun t ht z => by simpa using hB0 t ht z)
        (fun t ht z => by
          have := hB1 t ht z
          rwa [norm_iteratedFDeriv_one] at this) y
    have hder : fderiv ℝ (fun z => ∫ t in J, K t z) = fun z => ∫ t in J, K' t z := by
      funext y; exact (hderiv y).fderiv
    have := ih K' hK'd hB'
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv]
    refine ⟨fun y => (hderiv y).differentiableAt, by simp, ?_⟩
    rw [hder]
    exact this

/-- `w_λ` is smooth away from the origin. -/
theorem d3tw_wE_contDiffAt {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) {lam : ℝ}
    {w : Euc d} (hw : w ≠ 0) (m : ℕ) : ContDiffAt ℝ m (fdlWE ψ s b lam) w := by
  have hzpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set a : ℝ := ‖w‖ / 2 with ha_def
  have ha : 0 < a := by positivity
  have haz : a < ‖w‖ := by linarith
  have hV : ContDiff ℝ m (fun z : Euc d => ∫ t in Ioc a lam,
      (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z)) :=
    d3tw_contDiff_integral (U := Ioi 0) (E := Euc d) measurableSet_Ioc measure_Ioc_lt_top isOpen_Ioi
      (fun t ht => lt_trans ha ht.1) m
      (fun t z => (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z))
      (d3ew_K_contDiffOn (d3ew_phi_smooth hψ) b s) (d3ew_K_bdd hψ b s a lam ha)
  have hev : fdlWE ψ s b lam =ᶠ[𝓝 w] fun z => ∫ t in Ioc a lam,
      (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds haz] with z hz
    exact d3ew_rep_loc hψ s b lam ha.le hz.le
  exact hV.contDiffAt.congr_of_eventuallyEq hev

/-- Integrability of the integrand of `w_λ` at a point `w ≠ 0`. -/
lemma d3tw_integrable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s : ℝ) (lam : ℝ)
    {w : Euc d} (hw : w ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t w / t) (Ioc 0 lam) := by
  have hzpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set a : ℝ := ‖w‖ / 2 with ha_def
  have ha : 0 < a := by positivity
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • w)) (Icc a lam) := by
    have hne : ∀ t ∈ Icc a lam, t ≠ 0 := fun t ht => (lt_of_lt_of_le ha ht.1).ne'
    refine ContinuousOn.mul (ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (hne t ht)))
      ((fdle_phi_cont hψ).comp_continuousOn ?_)
    exact ContinuousOn.smul (continuousOn_inv₀.mono (fun t ht => hne t ht)) continuousOn_const
  have hI : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t w / t) (Ioc a lam) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • w)) (Ioc a lam) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioc
    exact (d3ew_integrand ψ s (lt_trans ha ht.1) w).symm
  refine hI.of_forall_diff_eq_zero measurableSet_Ioc (fun t ht => ?_)
  obtain ⟨⟨ht0, htl⟩, hn⟩ := ht
  have hta : t ≤ a := by
    by_contra h
    exact hn ⟨not_le.1 h, htl⟩
  simp [per_phiScale_zero hψ ht0 (show t ≤ ‖w‖ by linarith)]

/-- The finite-sum representation of the periodised short-scale kernel. -/
lemma d3tw_rep_sum {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) {y : Euc d} (hy : ∀ n : Lattice d, y + Lattice.toEuc n ≠ 0)
    (S : Finset (Lattice d)) (hS : ∀ n : Lattice d, ‖y + Lattice.toEuc n‖ < 1 → n ∈ S) :
    fdlWT ψ s b lam (Torus.mk y) = ∑ n ∈ S, fdlWE ψ s b lam (y + Lattice.toEuc n) := by
  unfold fdlWT fdlWE
  have h1 : ∀ t ∈ Ioc (0 : ℝ) lam, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) (Torus.mk y) / t
      = ∑ n ∈ S, t ^ ((d : ℝ) - s) * fdlPhiScale ψ t (y + Lattice.toEuc n) / t := by
    intro t ht
    rw [per_fdlPer_mk, tsum_eq_sum (s := S), Finset.mul_sum, Finset.sum_div]
    intro n hn
    apply per_phiScale_zero hψ ht.1
    by_contra h
    exact hn (hS n (by linarith [not_le.1 h, ht.2]))
  rw [setIntegral_congr_fun measurableSet_Ioc h1, integral_finset_sum, Finset.mul_sum]
  intro n _
  exact d3tw_integrable hψ s lam (hy n)

/-- A uniform count of lattice points in a unit ball. -/
lemma d3tw_card (d : ℕ) : ∃ N : ℕ, ∀ (y : Euc d) (F : Finset (Lattice d)),
    (∀ n ∈ F, ‖y + Lattice.toEuc n‖ ≤ 1) → F.card ≤ N := by
  refine ⟨(per_finite_lattice (d := d) 2).toFinset.card, fun y F hF => ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | ⟨n0, hn0⟩
  · simp
  · refine Finset.card_le_card_of_injOn (fun n => n - n0) (fun n hn => ?_) ?_
    · simp only [Finset.coe_sort_coe, Set.Finite.coe_toFinset, mem_setOf_eq]
      have e : Lattice.toEuc (n - n0) = (y + Lattice.toEuc n) - (y + Lattice.toEuc n0) := by
        ext i; simp [Lattice.toEuc]
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have := hF n hn
      have := hF n0 hn0
      linarith
    · intro n _ m _ h
      simpa using h
