import HRS.Sections.ScrnAux14

/-!
# Packet SCRN, part 15: scaling identities for the multiplier `λ_k` and its lower bound

With `r = 2π|k|`, `c = c_{d,s}`, `q = d - s`:
* `λ_k = β⁻¹ r² + c r^{2-q}` (`scrn_lam_eq`);
* `ℓ^{2-q} λ_k = scrnA c q b_N (ℓ r)` for `b_N = β ℓ^q` (`scrn_lam_scale`);
* `β⁻¹ r² / λ_k = scrnS c q b_N (ℓ r)` (`scrn_S_scale`);
* `λ_k ≥ min(c, 1/b₊) ℓ^{max(q-2,0)}` for `k ≠ 0`, `β ℓ^q ≤ b₊` (`scrn_lam_lower`).
-/

noncomputable section

open Set Filter Topology

namespace HRS

variable {d : ℕ}

lemma scrn_lam_eq {s : ℝ} (invβ : ℝ) {k : Lattice d} (hk : k ≠ 0) :
    scrnLam d s invβ k =
      invβ * (2 * Real.pi * Lattice.enorm k) ^ 2 +
        rieszConst d s * (2 * Real.pi * Lattice.enorm k) ^ (2 - ((d : ℝ) - s)) := by
  have he : 1 ≤ Lattice.enorm k := one_le_enorm_of_ne_zero hk
  have hr : 0 < 2 * Real.pi * Lattice.enorm k := by positivity
  unfold scrnLam rieszCoeff
  rw [if_neg hk]
  have : (2 * Real.pi * Lattice.enorm k) ^ (2 - ((d : ℝ) - s)) =
      (2 * Real.pi * Lattice.enorm k) ^ 2 * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) := by
    rw [show (2 - ((d : ℝ) - s)) = ((2 : ℕ) : ℝ) + (s - (d : ℝ)) by push_cast; ring,
      Real.rpow_add hr, Real.rpow_natCast]
  rw [this]
  ring

lemma scrn_lam_scale {s : ℝ} {β ℓ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) {k : Lattice d} (hk : k ≠ 0) :
    ℓ ^ (2 - ((d : ℝ) - s)) * scrnLam d s β⁻¹ k =
      scrnA (rieszConst d s) ((d : ℝ) - s) (β * ℓ ^ ((d : ℝ) - s))
        (2 * Real.pi * (ℓ * Lattice.enorm k)) := by
  rw [scrn_lam_eq _ hk]
  unfold scrnA
  set q : ℝ := (d : ℝ) - s with hq
  have he : 1 ≤ Lattice.enorm k := one_le_enorm_of_ne_zero hk
  have hr : 0 < 2 * Real.pi * Lattice.enorm k := by positivity
  have hρ : 2 * Real.pi * (ℓ * Lattice.enorm k) = ℓ * (2 * Real.pi * Lattice.enorm k) := by ring
  rw [hρ, Real.mul_rpow hℓ.le hr.le]
  have h1 : (0 : ℝ) < ℓ ^ q := Real.rpow_pos_of_pos hℓ _
  have h2 : ℓ ^ (2 - q) = ℓ ^ 2 / ℓ ^ q := by
    rw [Real.rpow_sub hℓ, Real.rpow_two]
  rw [h2]
  field_simp

lemma scrn_S_scale {s : ℝ} {β ℓ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ) {k : Lattice d} (hk : k ≠ 0)
    (hc : 0 < rieszConst d s) :
    scrnS (rieszConst d s) ((d : ℝ) - s) (β * ℓ ^ ((d : ℝ) - s))
        (2 * Real.pi * (ℓ * Lattice.enorm k)) =
      β⁻¹ * (2 * Real.pi * Lattice.enorm k) ^ 2 / scrnLam d s β⁻¹ k := by
  rw [scrn_lam_eq _ hk]
  unfold scrnS
  set q : ℝ := (d : ℝ) - s with hq
  have he : 1 ≤ Lattice.enorm k := one_le_enorm_of_ne_zero hk
  have hr : 0 < 2 * Real.pi * Lattice.enorm k := by positivity
  have hρ : 2 * Real.pi * (ℓ * Lattice.enorm k) = ℓ * (2 * Real.pi * Lattice.enorm k) := by ring
  rw [hρ, Real.mul_rpow hℓ.le hr.le]
  set r := 2 * Real.pi * Lattice.enorm k with hrdef
  have h1 : (0 : ℝ) < ℓ ^ q := Real.rpow_pos_of_pos hℓ _
  have h3 : (0 : ℝ) < r ^ q := Real.rpow_pos_of_pos hr _
  have h2 : r ^ (2 - q) = r ^ 2 / r ^ q := by
    rw [Real.rpow_sub hr, Real.rpow_two]
  rw [h2]
  have hr2 : 0 < r ^ 2 := by positivity
  field_simp

lemma scrn_lam_lower {s : ℝ} (hc : 0 < rieszConst d s) {invβ ℓ bp : ℝ} (hℓ : 0 < ℓ) (hbp : 0 < bp)
    (hβ : ℓ ^ ((d : ℝ) - s) / bp ≤ invβ) {k : Lattice d} (hk : k ≠ 0) :
    min (rieszConst d s) bp⁻¹ * ℓ ^ (max ((d : ℝ) - s - 2) 0) ≤ scrnLam d s invβ k := by
  rw [scrn_lam_eq _ hk]
  set q : ℝ := (d : ℝ) - s with hq
  have he : 1 ≤ Lattice.enorm k := one_le_enorm_of_ne_zero hk
  have hr1 : 1 ≤ 2 * Real.pi * Lattice.enorm k := by
    have := Real.pi_gt_three
    nlinarith
  set r := 2 * Real.pi * Lattice.enorm k with hrdef
  have hr : 0 < r := by linarith
  have hm1 : min (rieszConst d s) bp⁻¹ ≤ rieszConst d s := min_le_left _ _
  have hm2 : min (rieszConst d s) bp⁻¹ ≤ bp⁻¹ := min_le_right _ _
  have hm0 : 0 < min (rieszConst d s) bp⁻¹ := lt_min hc (inv_pos.2 hbp)
  have hinv : 0 ≤ invβ * r ^ 2 := by
    have : 0 ≤ invβ := le_trans (by positivity) hβ
    positivity
  rcases le_total q 2 with hq2 | hq2
  · rw [max_eq_right (by linarith), Real.rpow_zero, mul_one]
    have : 1 ≤ r ^ (2 - q) := Real.one_le_rpow hr1 (by linarith)
    nlinarith
  · rw [max_eq_left (by linarith)]
    have hlq : 0 < ℓ ^ (q - 2) := Real.rpow_pos_of_pos hℓ _
    rcases le_total (ℓ * r) 1 with hlr | hlr
    · -- `r ≤ 1/ℓ`
      have h1 : 1 ≤ (ℓ * r) ^ (2 - q) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) hlr (by linarith)
      rw [Real.mul_rpow hℓ.le hr.le] at h1
      have h2 : ℓ ^ (q - 2) * ℓ ^ (2 - q) = 1 := by
        rw [← Real.rpow_add hℓ]; simp
      have h3 : ℓ ^ (q - 2) ≤ r ^ (2 - q) := by
        have hp : 0 < ℓ ^ (2 - q) := Real.rpow_pos_of_pos hℓ _
        nlinarith [Real.rpow_pos_of_pos hr (2 - q)]
      calc min (rieszConst d s) bp⁻¹ * ℓ ^ (q - 2) ≤ rieszConst d s * r ^ (2 - q) :=
            mul_le_mul hm1 h3 hlq.le hc.le
        _ ≤ _ := by linarith
    · have h4 : ℓ ^ q = ℓ ^ (q - 2) * ℓ ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hℓ]; congr 1; push_cast; ring
      have h5 : ℓ ^ (q - 2) / bp * (ℓ * r) ^ 2 ≤ invβ * r ^ 2 := by
        have : ℓ ^ q / bp * r ^ 2 ≤ invβ * r ^ 2 :=
          mul_le_mul_of_nonneg_right hβ (by positivity)
        calc ℓ ^ (q - 2) / bp * (ℓ * r) ^ 2 = ℓ ^ q / bp * r ^ 2 := by rw [h4]; ring
          _ ≤ _ := this
      have h6 : ℓ ^ (q - 2) / bp ≤ ℓ ^ (q - 2) / bp * (ℓ * r) ^ 2 := by
        have : 1 ≤ (ℓ * r) ^ 2 := by nlinarith
        have h7 : 0 ≤ ℓ ^ (q - 2) / bp := by positivity
        nlinarith
      have h8 : 0 ≤ r ^ (2 - q) := Real.rpow_nonneg hr.le _
      calc min (rieszConst d s) bp⁻¹ * ℓ ^ (q - 2) ≤ bp⁻¹ * ℓ ^ (q - 2) :=
            mul_le_mul_of_nonneg_right hm2 hlq.le
        _ = ℓ ^ (q - 2) / bp := by ring
        _ ≤ invβ * r ^ 2 := h6.trans h5
        _ ≤ _ := by nlinarith [mul_nonneg hc.le h8]

end HRS
