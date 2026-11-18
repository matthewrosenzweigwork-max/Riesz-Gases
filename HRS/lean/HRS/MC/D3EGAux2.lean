import HRS.MC.D3EGAux1

/-!
# Packet D3EG, helper 2: the manifestly smooth representation `G_λ(z) = ∫_λ^∞ K_t(z) dt` of `g_λ`
and its derivative bounds.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3EG

open HRS HRS.MC.FDLE HRS.MC.D3EW

variable {d : ℕ}

/-- Subtracted constant: `φ(0)` for `s = 0`, `0` otherwise. -/
def d3eg_iota (ψ : Euc d → ℝ) (s : ℝ) : ℝ := if s = 0 then fdlPhi ψ 0 else 0

/-- The kernel `K_t(z) = b t^{-s-1} (φ(z/t) - ι)`. -/
def d3eg_K (ψ : Euc d → ℝ) (s b : ℝ) (t : ℝ) (z : Euc d) : ℝ :=
  b * t ^ (-s - 1) * (fdlPhi ψ (t⁻¹ • z) - d3eg_iota ψ s)

/-- `G_λ(z) = ∫_{λ}^∞ K_t(z) dt`. -/
def d3eg_G (ψ : Euc d → ℝ) (s b lam : ℝ) (z : Euc d) : ℝ :=
  ∫ t in Ioi lam, d3eg_K ψ s b t z

lemma d3eg_K_contDiffOn {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (d3eg_K ψ s b)) (Ioi (0 : ℝ) ×ˢ univ) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hp0 : p.1 ≠ 0 := (show (0 : ℝ) < p.1 from hp.1).ne'
  have h1 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => p.1 ^ (-s - 1)) p :=
    (Real.contDiffAt_rpow_const_of_ne hp0).comp p contDiff_fst.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => p.1⁻¹) p :=
    (contDiffAt_inv ℝ hp0).comp p contDiff_fst.contDiffAt
  have h3 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => p.1⁻¹ • p.2) p :=
    h2.smul contDiff_snd.contDiffAt
  have h4 : ContDiffAt ℝ ∞ (fun p : ℝ × Euc d => fdlPhi ψ (p.1⁻¹ • p.2)) p :=
    ((d3ew_phi_smooth hψ).contDiffAt).comp p h3
  exact (contDiffAt_const.mul h1).mul (h4.sub contDiffAt_const)

/-- For `0 < k + s`, the iterated derivative of `K_t` is that of the plain scaled profile. -/
lemma d3eg_iter_K_eq {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) (t : ℝ) (k : ℕ)
    (hk : 0 < (k : ℝ) + s) (z : Euc d) :
    iteratedFDeriv ℝ k (d3eg_K ψ s b t) z
      = iteratedFDeriv ℝ k (fun z => (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z)) z := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    have hs : s ≠ 0 := by
      intro h; subst h; simp at hk
    have : d3eg_K ψ s b t = fun z => (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z) := by
      funext y; simp [d3eg_K, d3eg_iota, hs]
    rw [this]
  · have hc : ContDiff ℝ ∞ (fun z : Euc d => (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z)) :=
      contDiff_const.mul ((d3ew_phi_smooth hψ).comp (contDiff_const_smul t⁻¹))
    have hfun : d3eg_K ψ s b t = (fun z : Euc d => (b * t ^ (-s - 1)) * fdlPhi ψ (t⁻¹ • z))
        + fun _ => -((b * t ^ (-s - 1)) * d3eg_iota ψ s) := by
      funext y; simp [d3eg_K]; ring
    rw [hfun, iteratedFDeriv_add_apply (hc.contDiffAt.of_le (by exact_mod_cast le_top))
      contDiffAt_const, iteratedFDeriv_const_of_ne h0.ne']
    simp

lemma d3eg_phi_lip {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ 1 (fdlPhi ψ) x‖ ≤ M) (w : Euc d) :
    |fdlPhi ψ w - fdlPhi ψ 0| ≤ M * ‖w‖ := by
  have h := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := fdlPhi ψ) (C := M) (fun x _ => (d3ew_phi_smooth hψ).differentiable (by simp) x)
    (fun x _ => by simpa [norm_iteratedFDeriv_one] using hM x) (mem_univ 0) (mem_univ w)
  simpa [Real.norm_eq_abs] using h

lemma d3eg_pow_int {e lam : ℝ} (he : 0 < e) (hl : 0 < lam) :
    IntegrableOn (fun t : ℝ => t ^ (-e - 1)) (Ioi lam) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) hl

lemma d3eg_K_int {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) {b : ℝ} (hb0 : 0 < b)
    {lam : ℝ} (hl : 0 < lam) (z : Euc d) :
    IntegrableOn (fun t => d3eg_K ψ s b t z) (Ioi lam) := by
  have hcont : ContinuousOn (fun t => d3eg_K ψ s b t z) (Ioi lam) :=
    d3eg_cont_slice (fun t ht => lt_trans hl ht) (d3eg_K_contDiffOn hψ s b) z
  have hmeas : AEStronglyMeasurable (fun t => d3eg_K ψ s b t z) (volume.restrict (Ioi lam)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  rcases hs0.lt_or_eq with hs | hs
  · obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ 0
    refine Integrable.mono' ((d3eg_pow_int hs hl).const_mul (b * M)) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hl ht
    have hpos : 0 < t ^ (-s - 1) := Real.rpow_pos_of_pos ht0 _
    have := hM (t⁻¹ • z)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    simp only [d3eg_K, d3eg_iota, if_neg hs.ne', sub_zero, Real.norm_eq_abs, abs_mul,
      abs_of_pos hb0, abs_of_pos hpos]
    calc b * t ^ (-s - 1) * |fdlPhi ψ (t⁻¹ • z)| ≤ b * t ^ (-s - 1) * M := by gcongr
      _ = b * M * t ^ (-s - 1) := by ring
  · subst hs
    obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ 1
    refine Integrable.mono' ((d3eg_pow_int one_pos hl).const_mul (b * M * ‖z‖)) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hl ht
    have hpos : 0 < t ^ (-(0 : ℝ) - 1) := Real.rpow_pos_of_pos ht0 _
    have := d3eg_phi_lip hψ hM (t⁻¹ • z)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)] at this
    simp only [d3eg_K, d3eg_iota, Real.norm_eq_abs, abs_mul,
      abs_of_pos hb0, abs_of_pos hpos]
    have e1 : t ^ (-(0 : ℝ) - 1) * t⁻¹ = t ^ (-(1 : ℝ) - 1) := by
      rw [show -(0 : ℝ) - 1 = -1 by norm_num, show -(1 : ℝ) - 1 = -1 + -1 by norm_num,
        Real.rpow_add ht0, Real.rpow_neg_one]
    calc b * t ^ (-(0 : ℝ) - 1) * |fdlPhi ψ (t⁻¹ • z) - fdlPhi ψ 0|
        ≤ b * t ^ (-(0 : ℝ) - 1) * (M * (t⁻¹ * ‖z‖)) := by gcongr
      _ = b * M * ‖z‖ * (t ^ (-(0 : ℝ) - 1) * t⁻¹) := by ring
      _ = b * M * ‖z‖ * t ^ (-(1 : ℝ) - 1) := by rw [e1]

lemma d3eg_hyp {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) {b : ℝ} (hb0 : 0 < b)
    {lam : ℝ} (hl : 0 < lam) : d3eg_Hyp (Ioi lam) (Ioi 0) (d3eg_K ψ s b) := by
  refine ⟨d3eg_K_contDiffOn hψ s b, d3eg_K_int hψ hs0 hb0 hl, fun k hk => ?_⟩
  obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ k
  have hks : 0 < (k : ℝ) + s := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨fun t => (b * M) * t ^ (-((k : ℝ) + s) - 1), ((d3eg_pow_int hks hl).const_mul (b * M)),
    fun t ht z => ?_⟩
  have ht0 : 0 < t := lt_trans hl ht
  rw [d3eg_iter_K_eq hψ s b t k hks z]
  refine (d3ew_scale_bound (d3ew_phi_smooth hψ) _ ht0 k z).trans ?_
  have hpos : 0 ≤ t ^ (-s - 1) := Real.rpow_nonneg ht0.le _
  have h1 : t ^ (-((k : ℝ) + s) - 1) = t ^ (-s - 1) * (t⁻¹) ^ k := by
    rw [show -((k : ℝ) + s) - 1 = (-s - 1) + (-(k : ℝ)) by ring, Real.rpow_add ht0,
      Real.rpow_neg ht0.le, Real.rpow_natCast, inv_pow]
  show _ ≤ (b * M) * t ^ (-((k : ℝ) + s) - 1)
  rw [h1, abs_of_nonneg (mul_nonneg hb0.le hpos)]
  have := hM (t⁻¹ • z)
  calc b * t ^ (-s - 1) * (t⁻¹) ^ k * ‖iteratedFDeriv ℝ k (fdlPhi ψ) (t⁻¹ • z)‖
      ≤ b * t ^ (-s - 1) * (t⁻¹) ^ k * M := by gcongr
    _ = b * M * (t ^ (-s - 1) * (t⁻¹) ^ k) := by ring

/-- Derivative bound for `G_λ`, valid at every point (including `0`). -/
theorem d3eg_G_deriv {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) {b : ℝ}
    (hb0 : 0 < b) (m : ℕ) (hm : 0 < (m : ℝ) + s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ z : Euc d,
      ‖iteratedFDeriv ℝ m (d3eg_G ψ s b lam) z‖ ≤ C * (max lam ‖z‖) ^ (-s - (m : ℝ)) := by
  obtain ⟨M, hM0, hM⟩ := d3ew_dphi_bound hψ m
  refine ⟨b * M / ((m : ℝ) + s), div_nonneg (mul_nonneg hb0.le hM0) hm.le, fun lam hl z => ?_⟩
  have hc : 0 < max lam ‖z‖ := lt_of_lt_of_le hl (le_max_left _ _)
  have hmain : iteratedFDeriv ℝ m (d3eg_G ψ s b lam) z
      = ∫ t in Ioi lam, iteratedFDeriv ℝ m (d3eg_K ψ s b t) z :=
    d3eg_iter_integral (J := Ioi lam) (U := Ioi 0) measurableSet_Ioi isOpen_Ioi
      (fun t ht => lt_trans hl ht) m (d3eg_K ψ s b) (d3eg_hyp hψ hs0 hb0 hl) z
  rw [hmain]
  have hκ : 0 ≤ b * M := mul_nonneg hb0.le hM0
  obtain ⟨htail, hint⟩ := d3ew_tail hm hc hκ (Ioi lam)
  calc ‖∫ t in Ioi lam, iteratedFDeriv ℝ m (d3eg_K ψ s b t) z‖
      ≤ ∫ t in Ioi lam, ‖iteratedFDeriv ℝ m (d3eg_K ψ s b t) z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi lam, (Ici (max lam ‖z‖)).indicator
          (fun t : ℝ => (b * M) * t ^ (-((m : ℝ) + s) - 1)) t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans hl ht
        rw [d3eg_iter_K_eq hψ s b t m hm z]
        refine (d3ew_scale_bound (d3ew_phi_smooth hψ) _ ht0 m z).trans ?_
        refine (d3ew_pt_bound hψ b s hb0 m hM z ht0).trans ?_
        by_cases hz : ‖z‖ ≤ t
        · rw [Set.indicator_of_mem (show t ∈ Ici ‖z‖ from hz),
            Set.indicator_of_mem (show t ∈ Ici (max lam ‖z‖) from max_le (le_of_lt ht) hz)]
        · rw [Set.indicator_of_notMem (show t ∉ Ici ‖z‖ from hz)]
          exact Set.indicator_nonneg (fun u hu => mul_nonneg hκ (Real.rpow_nonneg
            (lt_of_lt_of_le hc hu).le _)) t
    _ ≤ (b * M) * ((max lam ‖z‖) ^ (-((m : ℝ) + s)) / ((m : ℝ) + s)) := htail
    _ = b * M / ((m : ℝ) + s) * (max lam ‖z‖) ^ (-s - (m : ℝ)) := by
        rw [show -s - (m : ℝ) = -((m : ℝ) + s) by ring]; ring

end HRS.MC.D3EG
