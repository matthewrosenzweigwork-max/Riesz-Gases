import HRS.MC.CepE6DS1

/-!
# Packet CEPE6D, part 2b: S1 (cyclic-gap form) and S2 (the Slater lemma)

`t_ε = ε / (16 Cz N³)`.  For `z` in the closed alcove (e.g. `z ∈ closure (Alc N)`) and any `e` with
`‖e - v_ε(z)‖ ≤ 1/2`, the point `z + t_ε e` lies in the OPEN alcove.
-/

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MC.CepE6D

variable {N : ℕ}

/-- The Slater step `t_ε = ε/(16 Cz N³)`. -/
def tEps (ε : ℝ) (N : ℕ) : ℝ := ε / (16 * Cz * (N : ℝ) ^ 3)

theorem tEps_pos {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N) : 0 < tEps ε N := by
  have h1 := one_le_Cz
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold tEps; positivity

theorem tEps_eq {ε : ℝ} (hN : 1 ≤ N) : tEps ε N = theta ε N / (4 * (N : ℝ) ^ 2) := by
  have h1 := one_le_Cz
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hC : Cz ≠ 0 := by linarith
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  unfold tEps theta
  field_simp
  ring

/-- `t_ε (2N² + 1) < θ`. -/
theorem tEps_mul_lt {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N) :
    tEps ε N * (2 * (N : ℝ) ^ 2 + 1) < theta ε N := by
  have hth := theta_pos hε hN
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [tEps_eq hN, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  have h2 : 2 * (N : ℝ) ^ 2 + 1 < 4 * (N : ℝ) ^ 2 := by nlinarith
  exact mul_lt_mul_of_pos_left h2 hth

theorem coord_le_norm (x : Ch6D N) (i : Fin N) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- **S2 (Slater lemma).** `0 < ε ≤ 1/8`, `z` in the closed alcove, `‖e - v_ε(z)‖ ≤ 1/2`
  ⟹ `z + t_ε e` is in the open alcove, `t_ε = ε/(16 Cz N³)` (any `N`; for `N = 0` the alcove is everything,
  for `N = 1` it is `ℝ` since there are no pairs). -/
theorem cepe6d_S2_slater {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {z : Ch6D N} (hz : z ∈ ClAlc N)
    {e : Ch6D N} (he : ‖e - vv ε z‖ ≤ 1 / 2) : z + tEps ε N • e ∈ Alc N := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · exact ⟨fun k => k.elim0, fun k => k.elim0⟩
  have hN : 1 ≤ N := hNpos
  have ht := tEps_pos hε hN
  have hth := theta_pos hε hN
  have hlt := tEps_mul_lt hε hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hv := norm_vv_le ε z
  have he1 : ‖e‖ ≤ (N : ℝ) ^ 2 + 1 / 2 := by
    calc ‖e‖ = ‖(e - vv ε z) + vv ε z‖ := by rw [sub_add_cancel]
      _ ≤ ‖e - vv ε z‖ + ‖vv ε z‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hee : ∀ k l : Fin N, |e l - e k| ≤ 2 * (N : ℝ) ^ 2 + 1 := by
    intro k l
    have h1 := coord_le_norm e l
    have h2 := coord_le_norm e k
    calc |e l - e k| ≤ |e l| + |e k| := abs_sub _ _
      _ ≤ _ := by linarith
  have hww : ∀ k l : Fin N, |(e l - vv ε z l) - (e k - vv ε z k)| ≤ 1 := by
    intro k l
    have h1 := coord_le_norm (e - vv ε z) l
    have h2 := coord_le_norm (e - vv ε z) k
    simp only [PiLp.sub_apply] at h1 h2
    calc |(e l - vv ε z l) - (e k - vv ε z k)| ≤ |e l - vv ε z l| + |e k - vv ε z k| := abs_sub _ _
      _ ≤ _ := by linarith
  have hy : ∀ i : Fin N, (z + tEps ε N • e) i = z i + tEps ε N * e i := by
    intro i; simp
  have hdiff : ∀ k l : Fin N, (z + tEps ε N • e) l - (z + tEps ε N • e) k =
      (z l - z k) + tEps ε N * (e l - e k) := by
    intro k l; rw [hy, hy]; ring
  have hbound : ∀ k l : Fin N, |tEps ε N * (e l - e k)| < theta ε N := by
    intro k l
    rw [abs_mul, abs_of_pos ht]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hee k l) ht.le) hlt
  have hlow : ∀ k l : Fin N, k < l → (z + tEps ε N • e) k < (z + tEps ε N • e) l := by
    intro k l hkl
    have hd0 : 0 ≤ z l - z k := sub_nonneg.2 (hz.1 k l hkl)
    suffices 0 < (z + tEps ε N • e) l - (z + tEps ε N • e) k by linarith
    rw [hdiff]
    by_cases hd : z l - z k < theta ε N
    · have hA := (cepe6d_S1_pair hε hε1 hz hkl).1 hd
      have hsplit : e l - e k = (vv ε z l - vv ε z k) + ((e l - vv ε z l) - (e k - vv ε z k)) := by ring
      have := hww k l
      have h3 : 3 / 4 ≤ e l - e k := by
        rw [hsplit]; linarith [neg_abs_le ((e l - vv ε z l) - (e k - vv ε z k))]
      nlinarith
    · have := hbound k l
      have h5 := neg_abs_le (tEps ε N * (e l - e k))
      linarith [not_lt.1 hd]
  refine ⟨hlow, fun k l => ?_⟩
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · suffices (z + tEps ε N • e) l - (z + tEps ε N • e) k < 1 by linarith
    rw [hdiff]
    have hd1 : z l - z k ≤ 1 := by linarith [hz.2 k l]
    by_cases hρ : 1 - (z l - z k) < theta ε N
    · have hB := (cepe6d_S1_pair hε hε1 hz hkl).2 hρ
      have hsplit : e l - e k = (vv ε z l - vv ε z k) + ((e l - vv ε z l) - (e k - vv ε z k)) := by ring
      have := hww k l
      have h3 : e l - e k ≤ -(3 / 4) := by
        rw [hsplit]; linarith [le_abs_self ((e l - vv ε z l) - (e k - vv ε z k))]
      nlinarith
    · have := hbound k l
      have h5 := le_abs_self (tEps ε N * (e l - e k))
      linarith [not_lt.1 hρ]
  · linarith
  · have := hlow l k hlk
    linarith

/-- S2 with the hypothesis in the form used downstream (`z ∈ closure (Alc N)`). -/
theorem cepe6d_S2_slater_closure {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {z : Ch6D N}
    (hz : z ∈ closure (Alc N)) {e : Ch6D N} (he : ‖e - vv ε z‖ ≤ 1 / 2) :
    z + tEps ε N • e ∈ Alc N :=
  cepe6d_S2_slater hε hε1 (closure_Alc_subset hz) he

/-- The cyclic gap from `i` to its cyclic successor `j` (`= z_j - z_i`, plus `1` when the step wraps). -/
def cycGap (z : Ch6D N) (i j : Fin N) : ℝ := z j - z i + if j ≤ i then 1 else 0

theorem inner_vv_single (ε : ℝ) (z : Ch6D N) (i j : Fin N) :
    ⟪vv ε z, EuclideanSpace.single j (1 : ℝ) - EuclideanSpace.single i (1 : ℝ)⟫ =
      vv ε z j - vv ε z i := by
  simp [inner_sub_right, EuclideanSpace.inner_single_right]

/-- **S1 (gap form).**  For `z` in the closed alcove and `j` the cyclic successor of `i`
(`j = i+1`, or `j = 0` for `i = N-1`), a small cyclic gap `g_i(z) < ε/(4 Cz N)` gives
`⟨v_ε(z), ∇g_i⟩ ≥ 7/4`, where `∇g_i = e_j - e_i`.  (For `N = 1` the single gap is `1`, never small.) -/
theorem cepe6d_S1_gap {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {z : Ch6D N} (hz : z ∈ ClAlc N)
    {i j : Fin N} (hij : j.val = (i.val + 1) % N) (hg : cycGap z i j < theta ε N) :
    7 / 4 ≤ ⟪vv ε z, EuclideanSpace.single j (1 : ℝ) - EuclideanSpace.single i (1 : ℝ)⟫ := by
  rw [inner_vv_single]
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact i.elim0)
  have hthle := theta_le hε hN
  by_cases hlt : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hlt] at hij
    have hij' : i < j := by rw [Fin.lt_def, hij]; omega
    have hnle : ¬ j ≤ i := not_le.2 hij'
    have := (cepe6d_S1_pair hε hε1 hz hij').1 (by simpa [cycGap, hnle] using hg)
    linarith
  · have hi : i.val + 1 = N := by have := i.2; omega
    rw [hi, Nat.mod_self] at hij
    by_cases hN1 : N = 1
    · subst hN1
      have hji : j = i := Subsingleton.elim _ _
      subst hji
      simp [cycGap] at hg
      linarith
    · have hji : j < i := by rw [Fin.lt_def, hij]; omega
      have := (cepe6d_S1_pair hε hε1 hz hji).2 (by have h := hg; simp [cycGap, hji.le] at h; linarith)
      linarith

end HRS.MC.CepE6D
