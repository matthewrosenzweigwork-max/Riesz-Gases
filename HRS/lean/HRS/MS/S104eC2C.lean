import HRS.MS.S104eC2A
import HRS.MS.WhoAux4

/-!
# S104E route C, packet C2, part C: Hölder data of the product `ρ · ∂_i f`

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.

* `s104c2_shift_iter`: `D^m (u(· + z) - u) x = D^m u (x+z) - D^m u x`;
* `s104c2_prod_hol`: if `ρ ∈ U2Dec (j+1) L A` and `g ∈ C^j` has jets `≤ M`, `D^j g` `η`-Hölder near with constant `Hg`, then every `D^m (ρ g)`, `m ≤ j`,
  is `η`-Hölder near with constant `2^j A (Hg + 2M)` (Leibniz bound of Mathlib applied to the increments `ρ(·+z) · Δ_z g + Δ_z ρ · g`);
* `s104c2_dir_data`: for `f ∈ HolB j η B`, the directional derivative `∂_v f` is `C^j`, has jets `≤ B ‖v‖`, and `D^j ∂_v f` is `η`-Hölder with constant `B ‖v‖`;
* `s104c2_k_data`: the resulting data of `k = ρ ∂_v f`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL HRS.MS.Who

variable {d : ℕ}

lemma s104c2_norm_le_rpow {η t : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t ≤ t ^ η := by
  rcases ht0.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hη0.ne']
  · simpa using Real.rpow_le_rpow_of_exponent_ge h ht1 hη1

lemma HolNear.mono_H {F : Type*} [NormedAddCommGroup F] {η H H' : ℝ} {g : Euc d → F} (h : HolNear η H g)
    (hH : H ≤ H') : HolNear η H' g := fun a b hab =>
  (h a b hab).trans (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg _) _))

lemma s104c2_hol_of_lip {F : Type*} [NormedAddCommGroup F] {η B : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hB : 0 ≤ B)
    {g : Euc d → F} (h : ∀ a b, ‖g a - g b‖ ≤ B * ‖a - b‖) : HolNear η B g := fun a b hab =>
  (h a b).trans (mul_le_mul_of_nonneg_left (s104c2_norm_le_rpow hη0 hη1 (norm_nonneg _) (by linarith)) hB)

lemma s104c2_shift_iter {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {u : Euc d → F}
    (hu : ContDiff ℝ n u) {m : ℕ} (hm : m ≤ n) (x z : Euc d) :
    iteratedFDeriv ℝ m (fun y => u (y + z) - u y) x = iteratedFDeriv ℝ m u (x + z) - iteratedFDeriv ℝ m u x := by
  have h1 : ContDiff ℝ n (fun y => u (y + z)) := hu.comp (contDiff_id.add contDiff_const)
  have e : (fun y => u (y + z) - u y) = (fun y => u (y + z)) - u := rfl
  rw [e, iteratedFDeriv_sub_apply (h1.of_le (by exact_mod_cast hm)).contDiffAt
    (hu.of_le (by exact_mod_cast hm)).contDiffAt, iteratedFDeriv_comp_add_right]

lemma s104c2_lip_iter {n : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ n u) {m : ℕ} (hm : m + 1 ≤ n) {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ (m + 1) u y‖ ≤ B) (a b : Euc d) :
    ‖iteratedFDeriv ℝ m u a - iteratedFDeriv ℝ m u b‖ ≤ B * ‖a - b‖ :=
  ult_lip_of_fderiv ((s104c2_iter_cd1 hu hm).differentiable one_ne_zero)
    (fun y => by rw [u2_norm_fderiv_iteratedFDeriv]; exact hB y) a b

/-- Increment of `D^m u` over a step `z`, `‖z‖ ≤ 1/4`, when `D^{m+1} u` is bounded. -/
lemma s104c2_lip_step {n : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ n u) {m : ℕ} (hm : m + 1 ≤ n) {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ (m + 1) u y‖ ≤ B) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hB0 : 0 ≤ B)
    (x z : Euc d) (hz : ‖z‖ ≤ 1 / 4) :
    ‖iteratedFDeriv ℝ m u (x + z) - iteratedFDeriv ℝ m u x‖ ≤ B * ‖z‖ ^ η := by
  have := s104c2_lip_iter hu hm hB (x + z) x
  simp only [add_sub_cancel_left] at this
  exact this.trans (mul_le_mul_of_nonneg_left (s104c2_norm_le_rpow hη0 hη1 (norm_nonneg _) (by linarith)) hB0)

theorem s104c2_prod_hol {j : ℕ} {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {L A : ℝ} (hL0 : 0 ≤ L) {ρ : Euc d → ℝ}
    (hρ : U2Dec (j + 1) L A ρ) {g : Euc d → ℝ} (hg : ContDiff ℝ j g) {M Hg : ℝ}
    (hM : ∀ m ≤ j, ∀ y, ‖iteratedFDeriv ℝ m g y‖ ≤ M) (hHg : HolNear η Hg (iteratedFDeriv ℝ j g)) (hHg0 : 0 ≤ Hg) :
    ∀ m ≤ j, HolNear η (2 ^ j * A * (Hg + 2 * M)) (iteratedFDeriv ℝ m (fun y => ρ y * g y)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hρ.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  have hρj : U2Dec j L A ρ := ⟨hρ.1.of_le (by exact_mod_cast Nat.le_succ j),
    fun m hm => hρ.2 m (by omega)⟩
  have hprod := who_u2dec_mul hρj hg hM
  have hρb : ∀ m ≤ j + 1, ∀ y, ‖iteratedFDeriv ℝ m ρ y‖ ≤ A := fun m hm y => by
    refine (hρ.2 m hm y).trans ?_
    have := u2Wt_le_one (d := d) hL0 y
    nlinarith
  have hWcd : ContDiff ℝ j (fun y => ρ y * g y) := hprod.1
  have hK0 : 0 ≤ 2 ^ j * A * (Hg + 2 * M) := by positivity
  intro m hm
  rcases hm.lt_or_eq with hlt | heq
  · -- lower levels: Lipschitz
    refine (s104c2_hol_of_lip hη0 hη1 (by positivity) (s104c2_lip_iter hWcd (m := m) (by omega) (B := A * M * 2 ^ j)
      (fun y => (hprod.2 (m + 1) (by omega) y).trans ?_))).mono_H ?_
    · have := u2Wt_le_one (d := d) hL0 y
      have h0 : 0 ≤ A * M * 2 ^ j := by positivity
      nlinarith
    · have : A * M * 2 ^ j ≤ 2 ^ j * A * (Hg + 2 * M) := by nlinarith [mul_nonneg (mul_nonneg hA0 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) j)) hHg0, mul_nonneg hA0 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) j)]
      exact this
  · rw [heq]
    intro a b hab
    obtain ⟨z, rfl⟩ : ∃ z, a = b + z := ⟨a - b, by abel⟩
    have hz : ‖z‖ ≤ 1 / 4 := by simpa using hab
    have hzn : ‖b + z - b‖ = ‖z‖ := by simp
    rw [hzn]
    -- the increment identity
    have hid : (fun y => ρ (y + z) * g (y + z) - ρ y * g y) =
        fun y => ρ (y + z) * (g (y + z) - g y) + (ρ (y + z) - ρ y) * g y := by
      funext y; ring
    have hI := s104c2_shift_iter (u := fun y => ρ y * g y) hWcd (m := j) le_rfl b z
    rw [← hI, hid]
    have hρz : ContDiff ℝ j (fun y => ρ (y + z)) := hρj.1.comp (contDiff_id.add contDiff_const)
    have hgz : ContDiff ℝ j (fun y => g (y + z) - g y) :=
      (hg.comp (contDiff_id.add contDiff_const)).sub hg
    have hdρ : ContDiff ℝ j (fun y => ρ (y + z) - ρ y) := hρz.sub hρj.1
    rw [show (fun y => ρ (y + z) * (g (y + z) - g y) + (ρ (y + z) - ρ y) * g y) =
        (fun y => ρ (y + z) * (g (y + z) - g y)) + (fun y => (ρ (y + z) - ρ y) * g y) from rfl,
      iteratedFDeriv_add_apply ((hρz.mul hgz).of_le le_rfl).contDiffAt ((hdρ.mul hg).of_le le_rfl).contDiffAt]
    refine (norm_add_le _ _).trans ?_
    have T1 : ‖iteratedFDeriv ℝ j (fun y => ρ (y + z) * (g (y + z) - g y)) b‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * ((Hg + M) * ‖z‖ ^ η)) := by
      refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (j : ℕ∞ω)) hρz hgz b (n := j) le_rfl).trans ?_
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have e1 : iteratedFDeriv ℝ i (fun y => ρ (y + z)) b = iteratedFDeriv ℝ i ρ (b + z) :=
        iteratedFDeriv_comp_add_right i z b
      have e2 := s104c2_shift_iter hg (m := j - i) (by omega) b z
      rw [e1, e2]
      refine mul_le_mul (hρb i (by omega) _) ?_ (norm_nonneg _) hA0
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        simp only [Nat.sub_zero]
        have := hHg (b + z) b (by simpa using hz)
        simp only [add_sub_cancel_left] at this
        nlinarith [Real.rpow_nonneg (norm_nonneg z) η]
      · have := s104c2_lip_step hg (m := j - i) (by omega) (B := M) (fun y => hM _ (by omega) y) hη0 hη1 hM0 b z hz
        nlinarith [Real.rpow_nonneg (norm_nonneg z) η]
    have T2 : ‖iteratedFDeriv ℝ j (fun y => (ρ (y + z) - ρ y) * g y) b‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * ‖z‖ ^ η * M) := by
      refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (j : ℕ∞ω)) hdρ hg b (n := j) le_rfl).trans ?_
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have e2 := s104c2_shift_iter hρ.1 (m := i) (by omega) b z
      rw [e2]
      exact mul_le_mul (s104c2_lip_step hρ.1 (m := i) (by omega) (hρb (i + 1) (by omega)) hη0 hη1 hA0 b z hz)
        (hM _ (by omega) _) (norm_nonneg _) (by positivity)
    have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; rfl
    rw [← Finset.sum_mul, hsum] at T1 T2
    have hp : 0 ≤ ‖z‖ ^ η := Real.rpow_nonneg (norm_nonneg z) η
    calc _ ≤ 2 ^ j * (A * ((Hg + M) * ‖z‖ ^ η)) + 2 ^ j * (A * ‖z‖ ^ η * M) := add_le_add T1 T2
      _ = 2 ^ j * A * (Hg + 2 * M) * ‖z‖ ^ η := by ring

theorem s104c2_dir_data {j : ℕ} {η B : ℝ} {f : Euc d → ℝ} (hf : HolB j η B f) (v : Euc d) :
    ContDiff ℝ j (fun y => fderiv ℝ f y v) ∧
    (∀ m ≤ j, ∀ y, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y v) y‖ ≤ B * ‖v‖) ∧
    HolNear η (B * ‖v‖) (iteratedFDeriv ℝ j (fun y => fderiv ℝ f y v)) := by
  have hb := hf.bd.deriv (N := j) v
  refine ⟨hb.1, hb.2, ?_⟩
  have hcd : ContDiff ℝ j (fderiv ℝ f) := hf.bd.1.fderiv_right (by exact_mod_cast le_refl (j + 1))
  intro a b hab
  obtain ⟨z, rfl⟩ : ∃ z, a = b + z := ⟨a - b, by abel⟩
  have hzn : ‖b + z - b‖ = ‖z‖ := by simp
  rw [hzn]
  have h1 := s104c2_shift_iter hb.1 (m := j) le_rfl b z
  rw [← h1]
  have hu : ContDiff ℝ j (fun y => fderiv ℝ f (y + z) - fderiv ℝ f y) :=
    (hcd.comp (contDiff_id.add contDiff_const)).sub hcd
  have hfun : (fun y => fderiv ℝ f (y + z) v - fderiv ℝ f y v) =
      fun y => (fun y => fderiv ℝ f (y + z) - fderiv ℝ f y) y v := by
    funext y; simp
  rw [hfun]
  refine (norm_iteratedFDeriv_clm_apply_const (N := (j : WithTop ℕ∞)) (c := v) (n := j)
    hu.contDiffAt (by exact_mod_cast le_refl j)).trans ?_
  rw [s104c2_shift_iter hcd (m := j) le_rfl b z]
  have h2 := (continuousMultilinearCurryRightEquiv' ℝ j (Euc d) ℝ).symm.norm_map
    (iteratedFDeriv ℝ j (fderiv ℝ f) (b + z) - iteratedFDeriv ℝ j (fderiv ℝ f) b)
  rw [LinearIsometryEquiv.map_sub] at h2
  have e : ∀ y, iteratedFDeriv ℝ (j + 1) f y =
      (continuousMultilinearCurryRightEquiv' ℝ j (Euc d) ℝ).symm (iteratedFDeriv ℝ j (fderiv ℝ f) y) :=
    fun y => iteratedFDeriv_succ_eq_comp_right
  have h3 := hf.2 b z
  rw [e (b + z), e b] at h3
  have h4 : ‖iteratedFDeriv ℝ j (fderiv ℝ f) (b + z) - iteratedFDeriv ℝ j (fderiv ℝ f) b‖ ≤ B * ‖z‖ ^ η := by
    rw [← h2]; exact h3
  calc _ ≤ ‖v‖ * (B * ‖z‖ ^ η) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = _ := by ring

theorem s104c2_k_data {j : ℕ} {η B : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {L A : ℝ} (hL0 : 0 ≤ L) {ρ : Euc d → ℝ}
    (hρ : U2Dec (j + 1) L A ρ) {f : Euc d → ℝ} (hf : HolB j η B f) (v : Euc d) :
    U2Dec j L (A * (B * ‖v‖) * 2 ^ j) (fun y => ρ y * fderiv ℝ f y v) ∧
    ∀ m ≤ j, HolNear η (2 ^ j * A * (B * ‖v‖ + 2 * (B * ‖v‖)))
      (iteratedFDeriv ℝ m (fun y => ρ y * fderiv ℝ f y v)) := by
  obtain ⟨hcd, hbd, hh⟩ := s104c2_dir_data hf v
  have hB0 : 0 ≤ B := hf.bd.nonneg
  have hρj : U2Dec j L A ρ := ⟨hρ.1.of_le (by exact_mod_cast Nat.le_succ j),
    fun m hm => hρ.2 m (by omega)⟩
  exact ⟨who_u2dec_mul hρj hcd hbd,
    s104c2_prod_hol hη0 hη1 hL0 hρ hcd hbd hh (by positivity)⟩

end HRS.MS.S104e.C

end
