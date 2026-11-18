import HRS.Commutator.Torus.NRSTAux42

/-!
# NRS-T, part 43: the `Ḣ^σ` norm of the lifts is at most `N^d m₀ (hom σ h + o(1))`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_theta0_sq_integrable : Integrable (fun η : 𝔼 => ‖nrstr_theta0 (d := d) η‖ ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport (((nrstr_theta0 (d := d)).continuous.norm).pow 2) ?_
  have : HasCompactSupport (fun v : 𝔼 => ‖nrstr_theta0 (d := d) v‖) := by
    simp_rw [nrstr_theta0_norm]; exact nrstr_bumpE_cs
  exact this.comp_left (g := fun x : ℝ => x ^ 2) (by simp)

/-- The `k`-th bump in the Fourier transform of the lift. -/
def nrstr_a (h : NRST.TPA d) (N : ℝ) (k : Lattice d) (ξ : 𝔼) : ℂ :=
  h.coeff k * (((N ^ d : ℝ) : ℂ) * nrstr_theta0 (d := d) (N • (ξ - Lattice.toEuc k)))

lemma nrstr_FW_eq (h : NRST.TPA d) {N : ℝ} (hN : 0 < N) (ξ : 𝔼) :
    𝓕 (⇑(nrstr_W h N hN)) ξ = ∑ k ∈ h.coeff.support, nrstr_a h N k ξ := by
  classical
  have hs := nrstr_fourierW h hN ξ
  refine hs.unique ?_
  refine hasSum_sum_of_ne_finset_zero (fun k hk => ?_)
  have : h.coeff k = 0 := by simpa using hk
  simp [this]

lemma nrstr_toEuc_sub (k k' : Lattice d) : Lattice.toEuc (k - k') = Lattice.toEuc k - Lattice.toEuc k' := by
  ext i; simp [Lattice.toEuc]

lemma nrstr_a_near {h : NRST.TPA d} {N : ℝ} (hN : 1 ≤ N) {k : Lattice d} {ξ : 𝔼}
    (hk : nrstr_a h N k ξ ≠ 0) : ‖ξ - Lattice.toEuc k‖ < 1 / (8 * N) := by
  have hN0 : 0 < N := by linarith
  have h1 : nrstr_theta0 (d := d) (N • (ξ - Lattice.toEuc k)) ≠ 0 := by
    intro h0; apply hk; simp [nrstr_a, h0]
  by_contra hcon
  push Not at hcon
  apply h1
  refine nrstr_theta0_zero_of_far ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN0]
  rw [div_le_iff₀ (by positivity)] at hcon
  nlinarith

lemma nrstr_a_disjoint {h : NRST.TPA d} {N : ℝ} (hN : 1 ≤ N) {k k' : Lattice d} {ξ : 𝔼}
    (hk : nrstr_a h N k ξ ≠ 0) (hk' : nrstr_a h N k' ξ ≠ 0) : k = k' := by
  by_contra hne
  have h1 := nrstr_one_le_enorm (sub_ne_zero.2 hne)
  rw [nrstr_toEuc_sub] at h1
  have h2 := nrstr_a_near hN hk
  have h3 := nrstr_a_near hN hk'
  have h4 : ‖Lattice.toEuc k - Lattice.toEuc k'‖ ≤ ‖ξ - Lattice.toEuc k'‖ + ‖ξ - Lattice.toEuc k‖ := by
    calc ‖Lattice.toEuc k - Lattice.toEuc k'‖
        = ‖(ξ - Lattice.toEuc k') - (ξ - Lattice.toEuc k)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h5 : 1 / (8 * N) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  linarith

/-- Pointwise bound of the weighted `|𝓕W|²` by the sum of the weighted bumps. -/
lemma nrstr_pointwise {σ : ℝ} (hσ : 0 < σ) (h : NRST.TPA d) {N : ℝ} (hN : 1 ≤ N) (ξ : 𝔼) :
    (2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 (⇑(nrstr_W h N (by linarith))) ξ‖ ^ 2 ≤
      ∑ k ∈ h.coeff.support, (2 * Real.pi * (‖Lattice.toEuc k‖ + 1 / (8 * N))) ^ (2 * σ) *
        ‖nrstr_a h N k ξ‖ ^ 2 := by
  classical
  have hN0 : 0 < N := by linarith
  rw [nrstr_FW_eq h hN0]
  by_cases hex : ∃ k0 ∈ h.coeff.support, nrstr_a h N k0 ξ ≠ 0
  · obtain ⟨k0, hk0S, hk0⟩ := hex
    have hsum : ∑ k ∈ h.coeff.support, nrstr_a h N k ξ = nrstr_a h N k0 ξ := by
      refine Finset.sum_eq_single_of_mem k0 hk0S fun k _ hk => ?_
      by_contra hne
      exact hk (nrstr_a_disjoint hN hne hk0)
    rw [hsum]
    have hnear := nrstr_a_near hN hk0
    have hξ : ‖ξ‖ ≤ ‖Lattice.toEuc k0‖ + 1 / (8 * N) := by
      have := norm_le_insert' ξ (Lattice.toEuc k0)
      have h2 : ‖ξ‖ ≤ ‖Lattice.toEuc k0‖ + ‖ξ - Lattice.toEuc k0‖ := by
        calc ‖ξ‖ = ‖Lattice.toEuc k0 + (ξ - Lattice.toEuc k0)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    refine le_trans ?_ (Finset.single_le_sum (f := fun k => (2 * Real.pi * (‖Lattice.toEuc k‖ + 1 / (8 * N))) ^ (2 * σ) *
        ‖nrstr_a h N k ξ‖ ^ 2) (fun k _ => by positivity) hk0S)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)) (by positivity)
  · push Not at hex
    have hsum : ∑ k ∈ h.coeff.support, nrstr_a h N k ξ = 0 :=
      Finset.sum_eq_zero fun k hk => hex k hk
    rw [hsum]
    simp only [norm_zero]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this, mul_zero]
    exact Finset.sum_nonneg fun k _ => by positivity

lemma nrstr_a_norm_sq (h : NRST.TPA d) {N : ℝ} (hN : 0 < N) (k : Lattice d) (ξ : 𝔼) :
    ‖nrstr_a h N k ξ‖ ^ 2 = ‖h.coeff k‖ ^ 2 * (N ^ d) ^ 2 * ‖nrstr_theta0 (d := d) (N • (ξ - Lattice.toEuc k))‖ ^ 2 := by
  unfold nrstr_a
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  ring

lemma nrstr_a_sq_integrable (h : NRST.TPA d) {N : ℝ} (hN : 0 < N) (k : Lattice d) :
    Integrable (fun ξ : 𝔼 => ‖nrstr_a h N k ξ‖ ^ 2) := by
  have h1 : Integrable (fun ξ : 𝔼 => ‖nrstr_theta0 (d := d) (N • (ξ - Lattice.toEuc k))‖ ^ 2) :=
    ((nrstr_theta0_sq_integrable (d := d)).comp_smul hN.ne').comp_sub_right (Lattice.toEuc k)
  have h2 := h1.const_mul (‖h.coeff k‖ ^ 2 * (N ^ d) ^ 2)
  refine h2.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [nrstr_a_norm_sq h hN]

lemma nrstr_a_sq_integral (h : NRST.TPA d) {N : ℝ} (hN : 0 < N) (k : Lattice d) :
    ∫ ξ : 𝔼, ‖nrstr_a h N k ξ‖ ^ 2 = ‖h.coeff k‖ ^ 2 * N ^ d * nrstr_m0 d := by
  simp_rw [nrstr_a_norm_sq h hN]
  rw [integral_const_mul]
  have := nrstr_int_scale (fun η : 𝔼 => ‖nrstr_theta0 (d := d) η‖ ^ 2) hN (Lattice.toEuc k)
  simp only [smul_eq_mul] at this
  rw [this]
  unfold nrstr_m0
  have hNd : (N ^ d : ℝ) ≠ 0 := by positivity
  field_simp

/-- The `Ḣ^σ` norm of the lift. -/
lemma nrstr_xhom_le {σ : ℝ} (hσ : 0 < σ) (h : NRST.TPA d) {N : ℝ} (hN : 1 ≤ N) :
    HRS.Commutator.Whole.XNRS.xhom σ (nrstr_W h N (by linarith)) ≤
      N ^ d * nrstr_m0 d * ((1 + 1 / (8 * N)) ^ (2 * σ) * NRST.hom σ h +
        (2 * Real.pi / (8 * N)) ^ (2 * σ) * ‖h.coeff 0‖ ^ 2) := by
  classical
  have hN0 : 0 < N := by linarith
  unfold HRS.Commutator.Whole.XNRS.xhom
  have hint : Integrable (fun ξ : 𝔼 => ∑ k ∈ h.coeff.support,
      (2 * Real.pi * (‖Lattice.toEuc k‖ + 1 / (8 * N))) ^ (2 * σ) * ‖nrstr_a h N k ξ‖ ^ 2) :=
    integrable_finset_sum _ fun k _ => (nrstr_a_sq_integrable h hN0 k).const_mul _
  refine (integral_mono (HRS.Commutator.Whole.XNRS.integrable_xhom hσ.le _) hint
    (fun ξ => nrstr_pointwise hσ h hN ξ)).trans ?_
  rw [integral_finset_sum _ fun k _ => (nrstr_a_sq_integrable h hN0 k).const_mul _]
  simp_rw [integral_const_mul, nrstr_a_sq_integral h hN0]
  set R1 : ℝ := (1 + 1 / (8 * N)) ^ (2 * σ) with hR1
  set E : ℝ := (2 * Real.pi / (8 * N)) ^ (2 * σ) with hE
  have hper : ∀ k ∈ h.coeff.support,
      (2 * Real.pi * (‖Lattice.toEuc k‖ + 1 / (8 * N))) ^ (2 * σ) * (‖h.coeff k‖ ^ 2 * N ^ d * nrstr_m0 d) ≤
        N ^ d * nrstr_m0 d * (R1 * (NRST.lw σ k ^ 2 * ‖h.coeff k‖ ^ 2) +
          (if k = 0 then E * ‖h.coeff k‖ ^ 2 else 0)) := by
    intro k _
    have hm0 := nrstr_m0_pos (d := d)
    have hNd : (0 : ℝ) < N ^ d := by positivity
    by_cases hk : k = 0
    · subst hk
      simp only [NRST.enorm_zero, NRST.lw_zero, if_true]
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      rw [this, norm_zero, zero_add]
      have e : 2 * Real.pi * (1 / (8 * N)) = 2 * Real.pi / (8 * N) := by ring
      rw [e, ← hE]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, zero_add]
      nlinarith [mul_nonneg hNd.le hm0.le, sq_nonneg ‖h.coeff 0‖, Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.pi / (8 * N)) (2 * σ)]
    · simp only [hk, if_false, add_zero]
      have h1 := nrstr_one_le_enorm hk
      have hlw : NRST.lw σ k ^ 2 = (2 * Real.pi * ‖Lattice.toEuc k‖) ^ (2 * σ) := by
        rw [NRST.lw_sq, NRST.lw]
        simp [hk, Lattice.enorm]
      have h2 : (2 * Real.pi * (‖Lattice.toEuc k‖ + 1 / (8 * N))) ^ (2 * σ) ≤ R1 * (2 * Real.pi * ‖Lattice.toEuc k‖) ^ (2 * σ) := by
        rw [hR1, ← Real.mul_rpow (by positivity) (by positivity)]
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        have : 1 / (8 * N) ≤ 1 / (8 * N) * ‖Lattice.toEuc k‖ := by
          nlinarith [one_div_pos.2 (by positivity : 0 < 8 * N)]
        nlinarith [Real.pi_pos]
      rw [hlw]
      have hq : 0 ≤ ‖h.coeff k‖ ^ 2 * N ^ d * nrstr_m0 d := by positivity
      calc (2 * Real.pi * (‖Lattice.toEuc k‖ + 1 / (8 * N))) ^ (2 * σ) * (‖h.coeff k‖ ^ 2 * N ^ d * nrstr_m0 d)
          ≤ (R1 * (2 * Real.pi * ‖Lattice.toEuc k‖) ^ (2 * σ)) * (‖h.coeff k‖ ^ 2 * N ^ d * nrstr_m0 d) :=
            mul_le_mul_of_nonneg_right h2 hq
        _ = _ := by ring
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by have := nrstr_m0_pos (d := d); positivity)
  have hz : ∑ k ∈ h.coeff.support, (if k = 0 then E * ‖h.coeff k‖ ^ 2 else 0) ≤ E * ‖h.coeff 0‖ ^ 2 := by
    rw [Finset.sum_ite_eq' (h.coeff.support) 0 (fun k => E * ‖h.coeff k‖ ^ 2)]
    by_cases h0 : (0 : Lattice d) ∈ h.coeff.support
    · rw [if_pos h0]
    · have : h.coeff 0 = 0 := by simpa using h0
      rw [if_neg h0, this]; simp
  unfold NRST.hom
  exact add_le_add le_rfl hz

end HRS.Commutator.TorusNote
