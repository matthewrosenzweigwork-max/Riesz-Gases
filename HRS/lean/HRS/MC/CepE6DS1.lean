import HRS.MC.CepE6DCut2

/-!
# Packet CEPE6D, part 2a: S1 (the algebraic inequality at small gaps)

For `z` in the closed alcove and a pair `k < l`: if `d = z_l - z_k < θ = ε/(4 Cz N)` then
`(v_ε)_l - (v_ε)_k ≥ 7/4`; if `1 - d < θ` then `(v_ε)_l - (v_ε)_k ≤ -7/4`.  (`(v_ε)_l - (v_ε)_k = ⟨v_ε, e_l - e_k⟩`.)
The consecutive gaps `g_i` (incl. the wrap gap) are the pairs `(i,i+1)` (case 1) and `(0,N-1)` (case 2).
-/

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MC.CepE6D

variable {N : ℕ}

/-- The open cyclic alcove (copy of `HRS.MC.Cepa.cep_Alcove`; the two are equal by `rfl`). -/
def Alc (N : ℕ) : Set (Ch6D N) :=
  {z | (∀ k l : Fin N, k < l → z k < z l) ∧ ∀ k l : Fin N, z l < z k + 1}

/-- The closed alcove; `closure (Alc N) ⊆ ClAlc N` (`closure_Alc_subset`). -/
def ClAlc (N : ℕ) : Set (Ch6D N) :=
  {z | (∀ k l : Fin N, k < l → z k ≤ z l) ∧ ∀ k l : Fin N, z l ≤ z k + 1}

theorem isClosed_ClAlc : IsClosed (ClAlc N) := by
  have hc : ∀ k : Fin N, Continuous fun z : Ch6D N => z k := fun k => (EuclideanSpace.proj k).continuous
  have h1 : IsClosed {z : Ch6D N | ∀ k l : Fin N, k < l → z k ≤ z l} := by
    have : {z : Ch6D N | ∀ k l : Fin N, k < l → z k ≤ z l} =
        ⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k < l), {z : Ch6D N | z k ≤ z l} := by
      ext z; simp
    rw [this]
    exact isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ =>
      isClosed_le (hc k) (hc l)
  have h2 : IsClosed {z : Ch6D N | ∀ k l : Fin N, z l ≤ z k + 1} := by
    have : {z : Ch6D N | ∀ k l : Fin N, z l ≤ z k + 1} =
        ⋂ k : Fin N, ⋂ l : Fin N, {z : Ch6D N | z l ≤ z k + 1} := by
      ext z; simp
    rw [this]
    exact isClosed_iInter fun k => isClosed_iInter fun l =>
      isClosed_le (hc l) ((hc k).add continuous_const)
  exact h1.inter h2

theorem Alc_subset_ClAlc : Alc N ⊆ ClAlc N :=
  fun _ hz => ⟨fun k l hkl => (hz.1 k l hkl).le, fun k l => (hz.2 k l).le⟩

theorem closure_Alc_subset : closure (Alc N) ⊆ ClAlc N :=
  closure_minimal Alc_subset_ClAlc isClosed_ClAlc

/-- Lipschitz bound for `χ_ε'`. -/
theorem abs_chi1_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) (a b : ℝ) :
    |chi1 ε a - chi1 ε b| ≤ Cz / ε * |a - b| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := chi1 ε) (f' := chi2 ε) (C := Cz / ε) (x := b) (y := a)
    (fun x _ => (chi1_hasDerivAt ε x).hasDerivWithinAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using abs_chi2_le (d := x) hε hε1)
    (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using h

/-- The threshold `θ = ε/(4 Cz N)` below which a gap counts as small. -/
def theta (ε : ℝ) (N : ℕ) : ℝ := ε / (4 * Cz * N)

theorem theta_pos {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N) : 0 < theta ε N := by
  have h1 := one_le_Cz
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold theta; positivity

theorem theta_le {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N) : theta ε N ≤ ε / 4 := by
  have h1 := one_le_Cz
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold theta
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_le_mul h1 this zero_le_one (by linarith)]

theorem Cz_div_mul_theta {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N) :
    Cz / ε * theta ε N = 1 / (4 * N) := by
  have h1 := one_le_Cz
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold theta
  field_simp

theorem acomp_of_lt (ε : ℝ) (z : Ch6D N) {j k : Fin N} (h : k < j) :
    acomp ε z j k = chi1 ε (z j - z k) := by simp [acomp, h]

theorem acomp_of_gt (ε : ℝ) (z : Ch6D N) {j k : Fin N} (h : j < k) :
    acomp ε z j k = - chi1 ε (z k - z j) := by simp [acomp, h, not_lt.2 h.le]

theorem acomp_self (ε : ℝ) (z : Ch6D N) (j : Fin N) : acomp ε z j j = 0 := by simp [acomp]

/-- `(v_ε)_l - (v_ε)_k` split into the pair terms and the others. -/
theorem vv_sub_eq (ε : ℝ) (z : Ch6D N) {k l : Fin N} (hkl : k < l) :
    vv ε z l - vv ε z k = 2 * chi1 ε (z l - z k) +
      ∑ m ∈ (Finset.univ.erase k).erase l, (acomp ε z l m - acomp ε z k m) := by
  rw [vv_apply, vv_apply, ← Finset.sum_sub_distrib,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase (Finset.univ.erase k) _ (Finset.mem_erase.2 ⟨hkl.ne', Finset.mem_univ l⟩)]
  rw [acomp_of_lt ε z hkl, acomp_self, acomp_self, acomp_of_gt ε z hkl]
  ring

theorem card_rest_le (k l : Fin N) : (((Finset.univ.erase k).erase l).card : ℝ) ≤ N := by
  have : ((Finset.univ.erase k).erase l).card ≤ N :=
    (Finset.card_le_univ _).trans (by simp)
  exact_mod_cast this


theorem Dm_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {z : Ch6D N} (hz : z ∈ ClAlc N)
    {k l m : Fin N} (hkl : k < l) (hmk : m ≠ k) (hml : m ≠ l) (hd : z l - z k ≤ ε / 4) :
    -(Cz / ε * (z l - z k)) ≤ acomp ε z l m - acomp ε z k m := by
  have hd0 : 0 ≤ z l - z k := sub_nonneg.2 (hz.1 k l hkl)
  have hCe : 0 ≤ Cz / ε := div_nonneg (by linarith [one_le_Cz]) hε.le
  have hQ : 0 ≤ Cz / ε * (z l - z k) := mul_nonneg hCe hd0
  rcases lt_or_gt_of_ne hmk with hmk' | hmk'
  · have hml' : m < l := hmk'.trans hkl
    rw [acomp_of_lt ε z hml', acomp_of_lt ε z hmk']
    have := abs_chi1_sub_le hε hε1 (z l - z m) (z k - z m)
    have e : z l - z m - (z k - z m) = z l - z k := by ring
    rw [e, abs_of_nonneg hd0] at this
    linarith [neg_abs_le (chi1 ε (z l - z m) - chi1 ε (z k - z m))]
  · rcases lt_or_gt_of_ne hml with hml' | hml'
    · rw [acomp_of_lt ε z hml', acomp_of_gt ε z hmk']
      have h1 : chi1 ε (z l - z m) = 1 :=
        chi1_eq_one hε hε1 (by linarith [hz.1 k m hmk'])
      have h2 : chi1 ε (z m - z k) = 1 :=
        chi1_eq_one hε hε1 (by linarith [hz.1 m l hml'])
      rw [h1, h2]; linarith
    · have hkm : k < m := hkl.trans hml'
      rw [acomp_of_gt ε z hml', acomp_of_gt ε z hkm]
      have := abs_chi1_sub_le hε hε1 (z m - z k) (z m - z l)
      have e : z m - z k - (z m - z l) = z l - z k := by ring
      rw [e, abs_of_nonneg hd0] at this
      linarith [neg_abs_le (chi1 ε (z m - z k) - chi1 ε (z m - z l))]

theorem Dm_upper {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {z : Ch6D N} (hz : z ∈ ClAlc N)
    {k l m : Fin N} (hkl : k < l) (hmk : m ≠ k) (hml : m ≠ l) (hρ : 1 - (z l - z k) ≤ ε / 4) :
    acomp ε z l m - acomp ε z k m ≤ Cz / ε * (1 - (z l - z k)) := by
  have hρ0 : 0 ≤ 1 - (z l - z k) := by linarith [hz.2 k l]
  have hCe : 0 ≤ Cz / ε := div_nonneg (by linarith [one_le_Cz]) hε.le
  have hQ : 0 ≤ Cz / ε * (1 - (z l - z k)) := mul_nonneg hCe hρ0
  rcases lt_or_gt_of_ne hmk with hmk' | hmk'
  · have hml' : m < l := hmk'.trans hkl
    rw [acomp_of_lt ε z hml', acomp_of_lt ε z hmk']
    have h1 : chi1 ε (z l - z m) = -1 :=
      chi1_eq_neg_one hε hε1 (by linarith [hz.1 m k hmk'])
    have h2 : chi1 ε (z k - z m) = 1 :=
      chi1_eq_one hε hε1 (by linarith [hz.2 m l])
    rw [h1, h2]; linarith
  · rcases lt_or_gt_of_ne hml with hml' | hml'
    · rw [acomp_of_lt ε z hml', acomp_of_gt ε z hmk']
      have e1 : z l - z m = 1 - ((z m - z k) + (1 - (z l - z k))) := by ring
      have h1 : chi1 ε (z l - z m) = - chi1 ε ((z m - z k) + (1 - (z l - z k))) := by
        rw [e1, chi1_one_sub]
      rw [h1]
      have := abs_chi1_sub_le hε hε1 (z m - z k) ((z m - z k) + (1 - (z l - z k)))
      have e : z m - z k - ((z m - z k) + (1 - (z l - z k))) = -(1 - (z l - z k)) := by ring
      rw [e, abs_neg, abs_of_nonneg hρ0] at this
      linarith [le_abs_self (chi1 ε (z m - z k) - chi1 ε ((z m - z k) + (1 - (z l - z k))))]
    · have hkm : k < m := hkl.trans hml'
      rw [acomp_of_gt ε z hml', acomp_of_gt ε z hkm]
      have h1 : chi1 ε (z m - z l) = 1 :=
        chi1_eq_one hε hε1 (by linarith [hz.2 k m])
      have h2 : chi1 ε (z m - z k) = -1 :=
        chi1_eq_neg_one hε hε1 (by linarith [hz.1 l m hml'])
      rw [h1, h2]; linarith

/-- **S1 (pair form).**  `z` in the closed alcove, `k < l`, `d = z_l - z_k`, `θ = ε/(4 Cz N)`:
a small gap `d < θ` forces `(v_ε)_l - (v_ε)_k ≥ 7/4`, and `1 - d < θ` forces `(v_ε)_l - (v_ε)_k ≤ -7/4`. -/
theorem cepe6d_S1_pair {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {z : Ch6D N} (hz : z ∈ ClAlc N)
    {k l : Fin N} (hkl : k < l) :
    (z l - z k < theta ε N → 7 / 4 ≤ vv ε z l - vv ε z k) ∧
    (1 - (z l - z k) < theta ε N → vv ε z l - vv ε z k ≤ -(7 / 4)) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact k.elim0)
  have hth := theta_pos hε hN
  have hthle := theta_le hε hN
  have hCe : 0 ≤ Cz / ε := div_nonneg (by linarith [one_le_Cz]) hε.le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard := card_rest_le k l
  have hmem : ∀ m ∈ (Finset.univ.erase k).erase l, m ≠ k ∧ m ≠ l := by
    intro m hm
    rw [Finset.mem_erase, Finset.mem_erase] at hm
    exact ⟨hm.2.1, hm.1⟩
  have hkey : ∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / (4 * N) → (((Finset.univ.erase k).erase l).card : ℝ) * Q ≤ 1 / 4 := by
    intro Q hQ0 hQ
    calc _ ≤ (N : ℝ) * Q := mul_le_mul_of_nonneg_right hcard hQ0
      _ ≤ (N : ℝ) * (1 / (4 * N)) := mul_le_mul_of_nonneg_left hQ hNpos.le
      _ = 1 / 4 := by field_simp
  constructor
  · intro hd
    have hd0 : 0 ≤ z l - z k := sub_nonneg.2 (hz.1 k l hkl)
    have hdq : z l - z k ≤ ε / 4 := (hd.le).trans hthle
    rw [vv_sub_eq ε z hkl, chi1_eq_one hε hε1 hdq]
    have hQ0 : 0 ≤ Cz / ε * (z l - z k) := mul_nonneg hCe hd0
    have hQ : Cz / ε * (z l - z k) ≤ 1 / (4 * N) := by
      rw [← Cz_div_mul_theta hε hN]; exact mul_le_mul_of_nonneg_left hd.le hCe
    have hsum : ∑ _m ∈ (Finset.univ.erase k).erase l, (-(Cz / ε * (z l - z k))) ≤
        ∑ m ∈ (Finset.univ.erase k).erase l, (acomp ε z l m - acomp ε z k m) :=
      Finset.sum_le_sum fun m hm =>
        Dm_lower hε hε1 hz hkl (hmem m hm).1 (hmem m hm).2 hdq
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have := hkey _ hQ0 hQ
    linarith
  · intro hρ
    have hρ0 : 0 ≤ 1 - (z l - z k) := by linarith [hz.2 k l]
    have hρq : 1 - (z l - z k) ≤ ε / 4 := (hρ.le).trans hthle
    have hd1 : z l - z k ≤ 1 := by linarith
    rw [vv_sub_eq ε z hkl, chi1_eq_neg_one hε hε1 (by linarith)]
    have hQ0 : 0 ≤ Cz / ε * (1 - (z l - z k)) := mul_nonneg hCe hρ0
    have hQ : Cz / ε * (1 - (z l - z k)) ≤ 1 / (4 * N) := by
      rw [← Cz_div_mul_theta hε hN]; exact mul_le_mul_of_nonneg_left hρ.le hCe
    have hsum : ∑ m ∈ (Finset.univ.erase k).erase l, (acomp ε z l m - acomp ε z k m) ≤
        ∑ _m ∈ (Finset.univ.erase k).erase l, (Cz / ε * (1 - (z l - z k))) :=
      Finset.sum_le_sum fun m hm =>
        Dm_upper hε hε1 hz hkl (hmem m hm).1 (hmem m hm).2 hρq
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have := hkey _ hQ0 hQ
    linarith

end HRS.MC.CepE6D
