import Mathlib
import HRS.MC.CepN4

/-!
# Packet CEPN3, auxiliary 1: the steering target configuration

For a permutation `σ` and a gap `g` we define a strictly `σ`-ordered configuration `ystar` whose first pair
`(σ 0, σ 1)` has gap `g` and whose other particles are far from the pair, together with the robustness of
these properties under perturbations of size `ε'`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN3

open HRS HRS.MC.CepN4

variable {N : ℕ}

/-- Rank coordinates of the target. -/
def cepn3_z (g : ℝ) (k : Fin N) : ℝ :=
  if k.val = 0 then 0 else if k.val = 1 then g else 1 / 4 + (k.val : ℝ) / (2 * N)

lemma cepn3_z_zero (g : ℝ) (k : Fin N) (hk : k.val = 0) : cepn3_z g k = 0 := by
  simp [cepn3_z, hk]

lemma cepn3_z_one (g : ℝ) (k : Fin N) (hk : k.val = 1) : cepn3_z g k = g := by
  simp [cepn3_z, hk]

lemma cepn3_z_big (g : ℝ) (k : Fin N) (hk : 2 ≤ k.val) :
    cepn3_z g k = 1 / 4 + (k.val : ℝ) / (2 * N) := by
  have h0 : k.val ≠ 0 := by omega
  have h1 : k.val ≠ 1 := by omega
  simp [cepn3_z, h0, h1]

lemma cepn3_big_bounds (k : Fin N) (hk : 2 ≤ k.val) :
    1 / 4 + 1 / (N : ℝ) ≤ 1 / 4 + (k.val : ℝ) / (2 * N) ∧ 1 / 4 + (k.val : ℝ) / (2 * N) < 3 / 4 := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by have := k.2; omega
    exact_mod_cast this
  have hk2 : (2 : ℝ) ≤ k.val := by exact_mod_cast hk
  have hkN : (k.val : ℝ) < N := by exact_mod_cast k.2
  constructor
  · have : 1 / (N : ℝ) = 2 / (2 * N) := by field_simp
    rw [this]
    have : (2 : ℝ) / (2 * N) ≤ (k.val : ℝ) / (2 * N) := by
      apply div_le_div_of_nonneg_right hk2 (by positivity)
    linarith
  · have : (k.val : ℝ) / (2 * N) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    linarith

lemma cepn3_z_nonneg {g : ℝ} (hg : 0 ≤ g) (k : Fin N) : 0 ≤ cepn3_z g k := by
  by_cases h0 : k.val = 0
  · rw [cepn3_z_zero g k h0]
  by_cases h1 : k.val = 1
  · rw [cepn3_z_one g k h1]; exact hg
  rw [cepn3_z_big g k (by omega)]
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by have := k.2; omega
    exact_mod_cast this
  positivity

lemma cepn3_z_lt {g : ℝ} (hg : g ≤ 1 / 32) (k : Fin N) : cepn3_z g k < 3 / 4 := by
  by_cases h0 : k.val = 0
  · rw [cepn3_z_zero g k h0]; norm_num
  by_cases h1 : k.val = 1
  · rw [cepn3_z_one g k h1]; linarith
  rw [cepn3_z_big g k (by omega)]
  exact (cepn3_big_bounds k (by omega)).2

/-- Gaps between ranks. -/
lemma cepn3_z_gap {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1 / 32) {k k' : Fin N} (hkk : k < k') (hN : 2 ≤ N) :
    min g (1 / (2 * (N : ℝ))) ≤ cepn3_z g k' - cepn3_z g k := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hkk' : k.val < k'.val := hkk
  have hinv : 1 / (2 * (N : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hinvN : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hNpos]; linarith
  by_cases h0 : k.val = 0
  · rw [cepn3_z_zero g k h0]
    by_cases h1 : k'.val = 1
    · rw [cepn3_z_one g k' h1]; simp
    · rw [cepn3_z_big g k' (by omega)]
      have := (cepn3_big_bounds k' (by omega)).1
      have h3 : 0 < 1 / (N : ℝ) := by positivity
      exact (min_le_right _ _).trans (by linarith)
  by_cases h1 : k.val = 1
  · rw [cepn3_z_one g k h1, cepn3_z_big g k' (by omega)]
    have := (cepn3_big_bounds k' (by omega)).1
    exact (min_le_right _ _).trans (by linarith)
  · rw [cepn3_z_big g k (by omega), cepn3_z_big g k' (by omega)]
    refine (min_le_right _ _).trans ?_
    have hd : (1 : ℝ) ≤ (k'.val : ℝ) - k.val := by
      have : k.val + 1 ≤ k'.val := hkk'
      have : ((k.val + 1 : ℕ) : ℝ) ≤ k'.val := by exact_mod_cast this
      push_cast at this; linarith
    have : (k'.val : ℝ) / (2 * N) - (k.val : ℝ) / (2 * N) = ((k'.val : ℝ) - k.val) / (2 * N) := by
      ring
    have h2 : 1 / (2 * (N : ℝ)) ≤ ((k'.val : ℝ) - k.val) / (2 * N) :=
      div_le_div_of_nonneg_right hd (by positivity)
    linarith

/-- The target configuration: `ystar σ g (σ k) 0 = z k`. -/
def cepn3_ystar (σ : Equiv.Perm (Fin N)) (g : ℝ) : Fin N → Euc 1 :=
  fun i => WithLp.toLp 2 (fun _ => cepn3_z g (σ.symm i))

lemma cepn3_ystar_apply (σ : Equiv.Perm (Fin N)) (g : ℝ) (k : Fin N) :
    cepn3_ystar σ g (σ k) 0 = cepn3_z g k := by
  simp [cepn3_ystar]


lemma cepn3_not_near_int {u : ℝ} (h1 : 7 / 32 ≤ u) (h2 : u ≤ 3 / 4) (m : ℤ) : 7 / 32 ≤ |u - m| := by
  rcases le_or_gt m 0 with hm | hm
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [abs_of_nonpos (by linarith)]; linarith

lemma cepn3_iso_aux {A B zj zi e : ℝ} (hA : |A - zj| < e) (hB : |B - zi| < e) (h1 : 7 / 32 ≤ zj - zi)
    (h2 : zj - zi ≤ 3 / 4) (m : ℤ) : 7 / 32 - 2 * e ≤ |A - B - m| := by
  have hm := cepn3_not_near_int h1 h2 m
  have e1 : zj - zi - m = (A - B - m) - ((A - zj) - (B - zi)) := by ring
  have : |zj - zi - m| ≤ |A - B - m| + (|A - zj| + |B - zi|) := by
    rw [e1]
    refine (abs_sub _ _).trans ?_
    gcongr
    exact abs_sub _ _
  linarith

lemma cepn3_sep_aux {A B zj zj' e c : ℝ} (hA : |A - zj| < e) (hB : |B - zj'| < e) (hu : c ≤ zj' - zj)
    (hu2 : zj' - zj ≤ 1 / 2) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (m : ℤ) : c - 2 * e ≤ |A - B - m| := by
  have hm : c ≤ |zj' - zj + m| := by
    rcases le_or_gt 0 m with h | h
    · have : (0 : ℝ) ≤ m := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      rw [abs_of_nonpos (by linarith)]; linarith
  have e1 : zj' - zj + m = -(A - B - m) + ((A - zj) - (B - zj')) := by ring
  have : |zj' - zj + m| ≤ |A - B - m| + (|A - zj| + |B - zj'|) := by
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    gcongr
    exact abs_sub _ _
  linarith

lemma cepn3_big_diff {N : ℕ} (g : ℝ) {j j' : Fin N} (hj : 2 ≤ j.val) (hjj : j.val < j'.val) :
    1 / (2 * (N : ℝ)) ≤ cepn3_z g j' - cepn3_z g j ∧ cepn3_z g j' - cepn3_z g j ≤ 1 / 2 := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by have := j.2; omega
    exact_mod_cast this
  rw [cepn3_z_big g j hj, cepn3_z_big g j' (by omega)]
  have hd : (1 : ℝ) ≤ (j'.val : ℝ) - j.val := by
    have : ((j.val + 1 : ℕ) : ℝ) ≤ j'.val := by exact_mod_cast hjj
    push_cast at this; linarith
  have hlt : (j'.val : ℝ) < N := by exact_mod_cast j'.2
  have : (j'.val : ℝ) / (2 * N) - (j.val : ℝ) / (2 * N) = ((j'.val : ℝ) - j.val) / (2 * N) := by ring
  constructor
  · have h2 : 1 / (2 * (N : ℝ)) ≤ ((j'.val : ℝ) - j.val) / (2 * N) :=
      div_le_div_of_nonneg_right hd (by positivity)
    linarith
  · have h2 : ((j'.val : ℝ) - j.val) / (2 * N) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; have : (0:ℝ) ≤ j.val := by positivity
      linarith
    linarith

/-- Robustness of the target under perturbations. -/
theorem cepn3_robust (hN : 2 ≤ N) (σ : Equiv.Perm (Fin N)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8)
    {ε' : ℝ} (hε'0 : 0 < ε') (hε'1 : ε' ≤ ε / 16) (hε'2 : ε' ≤ 1 / (16 * (N : ℝ)))
    {y : Fin N → Euc 1} (hy : ∀ i, |y i 0 - cepn3_ystar σ (ε / 4) i 0| < ε') :
    cep_StrictlyOrdered σ y ∧
      (0 < y (σ (cep_i1 hN)) 0 - y (σ (cep_i0 hN)) 0 ∧ y (σ (cep_i1 hN)) 0 - y (σ (cep_i0 hN)) 0 ≤ ε / 2) ∧
      cep_PairIsolated hN σ y (1 / (8 * (N : ℝ))) ∧
      (∀ k l : Fin N, k ≠ l → k ≠ σ (cep_i0 hN) → k ≠ σ (cep_i1 hN) →
        l ≠ σ (cep_i0 hN) → l ≠ σ (cep_i1 hN) → ∀ m : ℤ, 1 / (8 * (N : ℝ)) ≤ |y k 0 - y l 0 - m|) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hg0 : 0 < ε / 4 := by linarith
  have hg1 : ε / 4 ≤ 1 / 32 := by linarith
  have hy' : ∀ k, |y (σ k) 0 - cepn3_z (ε / 4) k| < ε' := fun k => by
    have := hy (σ k); rwa [cepn3_ystar_apply] at this
  have h2ε : 2 * ε' < ε / 4 := by linarith
  have hinvN : 2 * (1 / (16 * (N : ℝ))) = 1 / (8 * N) := by
    field_simp; norm_num
  have h2ε2 : 2 * ε' < 1 / (2 * (N : ℝ)) := by
    have : 1 / (8 * (N : ℝ)) < 1 / (2 * N) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hε'small : ε' ≤ 1 / 128 := by linarith
  refine ⟨⟨fun k k' hkk => ?_, fun k k' => ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have hz := cepn3_z_gap hg0 hg1 hkk hN
    have h1 := abs_lt.1 (hy' k)
    have h2 := abs_lt.1 (hy' k')
    have : 2 * ε' < min (ε / 4) (1 / (2 * (N : ℝ))) := lt_min h2ε h2ε2
    linarith
  · have h1 := abs_lt.1 (hy' k)
    have h2 := abs_lt.1 (hy' k')
    have a1 := cepn3_z_nonneg hg0.le k
    have a2 := cepn3_z_lt hg1 k'
    linarith
  · have hz := cepn3_z_gap hg0 hg1 (k := cep_i0 hN) (k' := cep_i1 hN) (by
      show (0 : ℕ) < 1; omega) hN
    rw [cepn3_z_zero _ (cep_i0 hN) rfl, cepn3_z_one _ (cep_i1 hN) rfl] at hz
    have h1 := abs_lt.1 (hy' (cep_i0 hN))
    have h2 := abs_lt.1 (hy' (cep_i1 hN))
    rw [cepn3_z_zero _ (cep_i0 hN) rfl] at h1
    rw [cepn3_z_one _ (cep_i1 hN) rfl] at h2
    linarith
  · have h1 := abs_lt.1 (hy' (cep_i0 hN))
    have h2 := abs_lt.1 (hy' (cep_i1 hN))
    rw [cepn3_z_zero _ (cep_i0 hN) rfl] at h1
    rw [cepn3_z_one _ (cep_i1 hN) rfl] at h2
    linarith
  · intro k hk0 hk1 m
    obtain ⟨j, rfl⟩ : ∃ j, σ j = k := ⟨σ.symm k, by simp⟩
    have hj0 : j ≠ cep_i0 hN := fun h => hk0 (by rw [h])
    have hj1 : j ≠ cep_i1 hN := fun h => hk1 (by rw [h])
    have hjv : 2 ≤ j.val := by
      have a : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa [cep_i0] using h))
      have b : j.val ≠ 1 := fun h => hj1 (Fin.ext (by simpa [cep_i1] using h))
      omega
    have hzj := cepn3_z_big (ε / 4) j hjv
    have hb := cepn3_big_bounds j hjv
    have hinvpos : 0 < 1 / (N : ℝ) := by positivity
    have hε'N : 2 * ε' ≤ 1 / (8 * (N : ℝ)) := by linarith
    have hNinv : 1 / (8 * (N : ℝ)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hj := abs_lt.1 (hy' j)
    have h1 := abs_lt.1 (hy' (cep_i0 hN))
    have h2 := abs_lt.1 (hy' (cep_i1 hN))
    rw [cepn3_z_zero _ (cep_i0 hN) rfl] at h1
    rw [cepn3_z_one _ (cep_i1 hN) rfl] at h2
    have hu1 : 7 / 32 ≤ cepn3_z (ε / 4) j - 0 := by
      rw [hzj]; linarith
    have hu2 : 7 / 32 ≤ cepn3_z (ε / 4) j - ε / 4 := by
      rw [hzj]; linarith
    have hv : cepn3_z (ε / 4) j < 3 / 4 := cepn3_z_lt hg1 j
    constructor
    · have hB : |y (σ (cep_i0 hN)) 0 - 0| < ε' := by
        have h := hy' (cep_i0 hN)
        rwa [cepn3_z_zero _ (cep_i0 hN) rfl] at h
      have := cepn3_iso_aux (hy' j) hB hu1 (by linarith) m
      linarith
    · have := cepn3_iso_aux (hy' j) (by
        have h := hy' (cep_i1 hN)
        rw [cepn3_z_one _ (cep_i1 hN) rfl] at h; exact h) hu2 (by linarith) m
      linarith
  · have hε'N : 2 * ε' ≤ 1 / (8 * (N : ℝ)) := by linarith
    have hinv2 : 1 / (8 * (N : ℝ)) ≤ 1 / (2 * (N : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hinv4 : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have key : ∀ j j' : Fin N, 2 ≤ j.val → 2 ≤ j'.val → j.val < j'.val → ∀ m : ℤ,
        1 / (8 * (N : ℝ)) ≤ |y (σ j) 0 - y (σ j') 0 - m| := by
      intro j j' hj hj' hjj m
      obtain ⟨hd1, hd2⟩ := cepn3_big_diff (ε / 4) hj hjj
      have := cepn3_sep_aux (hy' j) (hy' j') hd1 hd2 (by positivity) hinv4 m
      -- 1/(2N) - 2ε' ≥ 1/(2N) - 1/(8N) ≥ 1/(8N)
      have h3 : 1 / (8 * (N : ℝ)) ≤ 1 / (2 * (N : ℝ)) - 1 / (8 * (N : ℝ)) := by
        have : 1 / (2 * (N : ℝ)) = 4 / (8 * N) := by field_simp; norm_num
        have h8 : 1 / (8 * (N : ℝ)) * 2 ≤ 4 / (8 * N) := by
          have : (4 : ℝ) / (8 * N) = 4 * (1 / (8 * N)) := by ring
          rw [this]; have : 0 < 1 / (8 * (N : ℝ)) := by positivity
          linarith
        rw [this]; linarith
      linarith
    intro k l hkl hk0 hk1 hl0 hl1 m
    obtain ⟨j, rfl⟩ : ∃ j, σ j = k := ⟨σ.symm k, by simp⟩
    obtain ⟨j', rfl⟩ : ∃ j, σ j = l := ⟨σ.symm l, by simp⟩
    have hv : ∀ j : Fin N, σ j ≠ σ (cep_i0 hN) → σ j ≠ σ (cep_i1 hN) → 2 ≤ j.val := by
      intro j h0 h1
      have a : j.val ≠ 0 := fun h => h0 (by rw [show j = cep_i0 hN from Fin.ext (by simpa [cep_i0] using h)])
      have b : j.val ≠ 1 := fun h => h1 (by rw [show j = cep_i1 hN from Fin.ext (by simpa [cep_i1] using h)])
      omega
    have hjv := hv j hk0 hk1
    have hjv' := hv j' hl0 hl1
    have hne : j.val ≠ j'.val := fun h => hkl (by rw [Fin.ext h])
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j j' hjv hjv' h m
    · have := key j' j hjv' hjv h (-m)
      have e : |y (σ j') 0 - y (σ j) 0 - ((-m : ℤ) : ℝ)| = |y (σ j) 0 - y (σ j') 0 - m| := by
        rw [← abs_neg]; congr 1; push_cast; ring
      linarith

end HRS.MC.CepN3
