import HRS.MC.D3TGAux3

/-!
# Packet D3TG, helper 4: bounds of the kernel `K` for large scales, the tail integral `H_λ` and its derivatives
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TG

open HRS HRS.MC.D3EW HRS.MC.Per HRS.MC.D3T1 HRS.MC.FDLE

variable {d : ℕ}

/-- Large scales `t ≥ 1`. -/
lemma d3tgK_large (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) (N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ k (d3tgK ψ s b t) y‖ ≤ |b| * t ^ ((d : ℝ) - s - 1) * (C * t ^ (-(N : ℝ))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨C, hC⟩ := per_decay_const hd hψ N
    refine ⟨|C|, abs_nonneg _, fun t ht y => ?_⟩
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hc : 0 < t ^ ((d : ℝ) - s - 1) := Real.rpow_pos_of_pos ht0 _
    rw [norm_iteratedFDeriv_zero, d3tgK_eq' ψ s b ht0, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos hc]
    have h1 := hC t ht (Torus.mk y)
    have h2 : C * t ^ (-(N : ℝ)) ≤ |C| * t ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg ht0.le _)
    have h3 : |b| * t ^ ((d : ℝ) - s - 1) *
        |fdlPer (fdlPhiScale ψ t) (Torus.mk y) - ∫ x, fdlPhi ψ x|
        ≤ |b| * t ^ ((d : ℝ) - s - 1) * (|C| * t ^ (-(N : ℝ))) := by
      gcongr
      exact h1.trans h2
    exact h3
  · obtain ⟨C, hC⟩ := per_decay_deriv hd hψ k hk N
    refine ⟨|C|, abs_nonneg _, fun t ht y => ?_⟩
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hc : 0 < t ^ ((d : ℝ) - s - 1) := Real.rpow_pos_of_pos ht0 _
    rw [d3tgK_eq ψ s b ht0, d3tg_diter_affine_pos (d3tgK_smooth hψ s b ht0) _ _ hk y,
      abs_mul, abs_of_pos hc]
    have h1 := hC t ht y
    rw [per_lift_fdlPer] at h1
    have h2 : C * t ^ (-(N : ℝ)) ≤ |C| * t ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg ht0.le _)
    gcongr
    exact h1.trans h2

/-- The combined pointwise bound (with `N = d + 1`). -/
lemma d3tgK_bound (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) (k : ℕ) :
    ∃ A A' Cl : ℝ, 0 ≤ A ∧ 0 ≤ A' ∧ 0 ≤ Cl ∧ ∀ (y : Euc d) (a : ℝ),
      (∀ n : Lattice d, a ≤ ‖y + Lattice.toEuc n‖) → ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ k (d3tgK ψ s b t) y‖ ≤
        if t ≤ 1 then
          (if a ≤ t then A * t ^ (-((k : ℝ) + s) - 1) else 0) + A' * t ^ ((d : ℝ) - s - 1)
        else Cl * t ^ (-s - 2) := by
  obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ k
  obtain ⟨C, hC0, hC⟩ := d3tgK_large hd hψ s b (d + 1) k
  refine ⟨|b| * 3 ^ d * M, |b| * |∫ x, fdlPhi ψ x|, |b| * C, by positivity, by positivity,
    by positivity, fun y a ha t ht => ?_⟩
  by_cases ht1 : t ≤ 1
  · rw [if_pos ht1]
    exact d3tgK_small hψ s b k hM ht ht1 y ha
  · rw [if_neg ht1]
    push Not at ht1
    refine (hC t ht1.le y).trans (le_of_eq ?_)
    have : t ^ ((d : ℝ) - s - 1) * t ^ (-((d + 1 : ℕ) : ℝ)) = t ^ (-s - 2) := by
      rw [← Real.rpow_add ht]
      congr 1
      push_cast
      ring
    calc |b| * t ^ ((d : ℝ) - s - 1) * (C * t ^ (-((d + 1 : ℕ) : ℝ)))
        = |b| * C * (t ^ ((d : ℝ) - s - 1) * t ^ (-((d + 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [this]

lemma d3tg_int_rpow_Ioc {lam : ℝ} (hlam : 0 < lam) (e : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ e) (Ioc lam 1) := by
  have : ContinuousOn (fun t : ℝ => t ^ e) (Icc lam 1) :=
    ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (lt_of_lt_of_le hlam ht.1).ne')
  exact (this.integrableOn_Icc).mono_set Ioc_subset_Icc_self

lemma d3tg_int_rpow_Ioi {s : ℝ} (hs : 0 ≤ s) : IntegrableOn (fun t : ℝ => t ^ (-s - 2)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) one_pos

/-- The tail integral `H_λ(y) = ∫_{λ}^∞ K_t(y) dt`. -/
def d3tgH (ψ : Euc d → ℝ) (s b lam : ℝ) (y : Euc d) : ℝ := ∫ t in Ioi lam, d3tgK ψ s b t y

lemma d3tgK_dbound (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) (b : ℝ)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) :
    D3TGBound (Ioi lam) (d3tgK ψ s b : ℝ → Euc d → ℝ) := by
  intro k
  obtain ⟨A, A', Cl, hA, hA', hCl, hb⟩ := d3tgK_bound hd hψ s b k
  set ρ : ℝ → ℝ := fun t =>
    (Ioc lam 1).indicator (fun t => A * t ^ (-((k : ℝ) + s) - 1) + A' * t ^ ((d : ℝ) - s - 1)) t
      + (Ioi (1 : ℝ)).indicator (fun t => Cl * t ^ (-s - 2)) t with hρ
  refine ⟨ρ, ?_, fun t ht z => ?_⟩
  · have h1 : IntegrableOn (fun t : ℝ => A * t ^ (-((k : ℝ) + s) - 1) + A' * t ^ ((d : ℝ) - s - 1))
        (Ioc lam 1) :=
      ((d3tg_int_rpow_Ioc hlam _).const_mul A).add ((d3tg_int_rpow_Ioc hlam _).const_mul A')
    have h2 : IntegrableOn (fun t : ℝ => Cl * t ^ (-s - 2)) (Ioi 1) :=
      (d3tg_int_rpow_Ioi hs0).const_mul Cl
    exact (((integrable_indicator_iff measurableSet_Ioc).2 h1).add
      ((integrable_indicator_iff measurableSet_Ioi).2 h2)).integrableOn
  · have ht0 : 0 < t := lt_trans hlam ht
    have := hb z 0 (fun n => norm_nonneg _) t ht0
    by_cases ht1 : t ≤ 1
    · rw [if_pos ht1, if_pos ht0.le] at this
      refine this.trans (le_of_eq ?_)
      simp only [hρ]
      rw [Set.indicator_of_mem (show t ∈ Ioc lam 1 from ⟨ht, ht1⟩),
        Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => absurd h.out (not_lt.2 ht1)),
        add_zero]
    · rw [if_neg ht1] at this
      refine this.trans (le_of_eq ?_)
      simp only [hρ]
      rw [Set.indicator_of_notMem (show t ∉ Ioc lam 1 from fun h => ht1 h.2),
        Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from not_le.1 ht1), zero_add]

lemma d3tgH_contDiff (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) (b : ℝ)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) :
    ContDiff ℝ ∞ (d3tgH ψ s b lam) :=
  d3tg_contDiff_integral_infty measurableSet_Ioi isOpen_Ioi (Ioi_subset_Ioi hlam.le) _
    (d3tgK_contDiffOn hψ s b) (d3tgK_dbound hd hψ hs0 b hlam hlam1)

lemma d3tgH_iter (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) (b : ℝ)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) (j : ℕ) (y : Euc d) :
    iteratedFDeriv ℝ j (d3tgH ψ s b lam) y = ∫ t in Ioi lam, iteratedFDeriv ℝ j (d3tgK ψ s b t) y :=
  d3tg_iter_integral measurableSet_Ioi isOpen_Ioi (Ioi_subset_Ioi hlam.le) j _
    (d3tgK_contDiffOn hψ s b) (d3tgK_dbound hd hψ hs0 b hlam hlam1) y

end HRS.MC.D3TG
