import HRS.MC.D3TGAux1

/-!
# Packet D3TG, helper 2: derivatives of the periodized profile sum, lattice counting, the kernel `K`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TG

open HRS HRS.MC.D3EW HRS.MC.Per HRS.MC.D3T1 HRS.MC.FDLE

variable {d : ℕ}

lemma d3tg_iter_zero {f : Euc d → ℝ} {R : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0) (k : ℕ) {x : Euc d}
    (hx : R < ‖x‖) : iteratedFDeriv ℝ k f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with w hw using hR w hw
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  simp

lemma d3tg_iter_tsum {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0)
    (k : ℕ) (y : Euc d) :
    iteratedFDeriv ℝ k (fun w => ∑' n : Lattice d, f (w + Lattice.toEuc n)) y
      = ∑' n : Lattice d, iteratedFDeriv ℝ k f (y + Lattice.toEuc n) := by
  set S : Finset (Lattice d) := (per_finite_lattice (d := d) (R + ‖y‖ + 1)).toFinset with hS
  have hev : (fun w : Euc d => ∑' n : Lattice d, f (w + Lattice.toEuc n)) =ᶠ[𝓝 y]
      fun w => ∑ n ∈ S, f (w + Lattice.toEuc n) := by
    filter_upwards [Metric.ball_mem_nhds y one_pos] with w hw
    refine tsum_eq_sum fun n hn => ?_
    by_contra hne
    apply hn
    rw [hS, Set.Finite.mem_toFinset]
    have := per_term_ne_zero hR (r := ‖w‖) le_rfl hne
    have h3 : ‖w‖ ≤ ‖y‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have := norm_le_norm_add_norm_sub' w y
      linarith
    show ‖Lattice.toEuc n‖ ≤ R + ‖y‖ + 1
    linarith
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  have hterm : ∀ n ∈ S, ContDiffAt ℝ k (fun w : Euc d => f (w + Lattice.toEuc n)) y := fun n _ =>
    ((hf.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hterm]
  have hshift : ∀ n : Lattice d, iteratedFDeriv ℝ k (fun w : Euc d => f (w + Lattice.toEuc n)) y
      = iteratedFDeriv ℝ k f (y + Lattice.toEuc n) := fun n => iteratedFDeriv_comp_add_right k _ y
  simp_rw [hshift]
  symm
  refine tsum_eq_sum fun n hn => ?_
  apply d3tg_iter_zero hR
  by_contra hle
  apply hn
  rw [hS, Set.Finite.mem_toFinset]
  show ‖Lattice.toEuc n‖ ≤ R + ‖y‖ + 1
  have h2 : ‖Lattice.toEuc n‖ ≤ ‖y + Lattice.toEuc n‖ + ‖y‖ := by
    have := norm_sub_le (y + Lattice.toEuc n) y
    simpa using this
  linarith [not_lt.mp hle]

lemma d3tg_card_le (y : Euc d) :
    ∃ T : Finset (Lattice d), T.card ≤ 3 ^ d ∧ ∀ n : Lattice d, ‖y + Lattice.toEuc n‖ ≤ 1 → n ∈ T := by
  refine ⟨Fintype.piFinset (fun i : Fin d => Finset.Icc (⌊-y i⌋ - 1) (⌊-y i⌋ + 1)), ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    have : ∀ i : Fin d, (Finset.Icc (⌊-y i⌋ - 1) (⌊-y i⌋ + 1)).card = 3 := by
      intro i
      rw [Int.card_Icc]
      omega
    simp [this]
  · intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    have h1 := PiLp.norm_apply_le (y + Lattice.toEuc n) i
    have e : ‖(y + Lattice.toEuc n) i‖ = |y i + (n i : ℝ)| := by simp [Lattice.toEuc]
    rw [e] at h1
    have h2 := abs_le.mp (h1.trans hn)
    have h3 := Int.floor_le (-y i)
    have h4 := Int.lt_floor_add_one (-y i)
    rw [Finset.mem_Icc]
    constructor
    · have : ((⌊-y i⌋ - 1 : ℤ) : ℝ) ≤ n i := by push_cast; linarith [h2.1]
      exact_mod_cast this
    · have : (n i : ℝ) < ((⌊-y i⌋ + 1 : ℤ) : ℝ) + 1 := by push_cast; linarith [h2.2]
      have : n i < ⌊-y i⌋ + 1 + 1 := by exact_mod_cast this
      omega

/-- Derivative bound for one scaled profile. -/
lemma d3tg_dphiScale {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (k : ℕ) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k (fdlPhi ψ) x‖ ≤ M) (z : Euc d) :
    ‖iteratedFDeriv ℝ k (fdlPhiScale ψ t) z‖ ≤
      if ‖z‖ ≤ t then (t ^ d)⁻¹ * (t⁻¹) ^ k * M else 0 := by
  have h := d3ew_scale_bound (d3ew_phi_smooth hψ) ((t ^ d)⁻¹) ht k z
  have heq : fdlPhiScale ψ t = fun z => (t ^ d)⁻¹ * fdlPhi ψ (t⁻¹ • z) := rfl
  rw [heq]
  split_ifs with hz
  · refine h.trans ?_
    rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg ht.le d))]
    gcongr
    exact hM _
  · push Not at hz
    have h1 : 1 < ‖t⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), ← div_eq_inv_mul, one_lt_div ht]
      exact hz
    rw [d3ew_dphi_zero hψ k h1] at h
    simpa using h

/-- Derivative bound of the periodized profile sum for `t ≤ 1`, localized at distance `a`. -/
lemma d3tg_dper_bound {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (k : ℕ) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ k (fdlPhi ψ) x‖ ≤ M) (y : Euc d) {a : ℝ}
    (ha : ∀ n : Lattice d, a ≤ ‖y + Lattice.toEuc n‖) :
    ‖iteratedFDeriv ℝ k (fun w => ∑' n : Lattice d, fdlPhiScale ψ t (w + Lattice.toEuc n)) y‖
      ≤ if a ≤ t then 3 ^ d * ((t ^ d)⁻¹ * (t⁻¹) ^ k * M) else 0 := by
  have hzero : ∀ x : Euc d, t < ‖x‖ → fdlPhiScale ψ t x = 0 :=
    fun x hx => per_phiScale_zero hψ ht hx.le
  rw [d3tg_iter_tsum (per_phiScale_contDiff hψ t) hzero k y]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ (t ^ d)⁻¹ * (t⁻¹) ^ k * M := by positivity
  split_ifs with hat
  · obtain ⟨T, hT, hmem⟩ := d3tg_card_le y
    rw [tsum_eq_sum (s := T)]
    · refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ T, ‖iteratedFDeriv ℝ k (fdlPhiScale ψ t) (y + Lattice.toEuc n)‖
          ≤ ∑ _n ∈ T, (t ^ d)⁻¹ * (t⁻¹) ^ k * M := by
            refine Finset.sum_le_sum fun n _ => ?_
            refine (d3tg_dphiScale hψ ht k hM _).trans ?_
            split_ifs
            · exact le_rfl
            · exact hB0
        _ = T.card * ((t ^ d)⁻¹ * (t⁻¹) ^ k * M) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 ^ d * ((t ^ d)⁻¹ * (t⁻¹) ^ k * M) := by
            gcongr
            exact_mod_cast hT
    · intro n hn
      apply d3tg_iter_zero hzero
      by_contra hle
      exact hn (hmem n (le_trans (not_lt.mp hle) ht1))
  · push Not at hat
    have : ∀ n : Lattice d, iteratedFDeriv ℝ k (fdlPhiScale ψ t) (y + Lattice.toEuc n) = 0 :=
      fun n => d3tg_iter_zero hzero k (lt_of_lt_of_le hat (ha n))
    simp [this]

end HRS.MC.D3TG
