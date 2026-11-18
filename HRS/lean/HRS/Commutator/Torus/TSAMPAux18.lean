import HRS.Commutator.Torus.TSAMPAux17

/-!
# T-SAMP helpers, part 18: partition into cells, averaging inequality
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_cell_cover {m : ℕ} (hm : 1 ≤ m) (x : Torus d) : ∃ j : Fin d → Fin m, x ∈ cellT m j := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfl : ∀ i, ⌊(m : ℝ) * Torus.rep x i⌋₊ < m := by
    intro i
    have hr := KernelGrad.rep_mem x i
    rw [Nat.floor_lt (by have := hr.1; positivity)]
    nlinarith [hr.2]
  refine ⟨fun i => ⟨⌊(m : ℝ) * Torus.rep x i⌋₊, hfl i⟩, fun i => ?_⟩
  have hr := KernelGrad.rep_mem x i
  have h0 : 0 ≤ (m : ℝ) * Torus.rep x i := by have := hr.1; positivity
  constructor
  · rw [div_le_iff₀ hm0]
    have := Nat.floor_le h0
    simpa [mul_comm] using this
  · rw [lt_div_iff₀ hm0]
    have := Nat.lt_floor_add_one ((m : ℝ) * Torus.rep x i)
    simpa [mul_comm] using this

lemma tsamp_cell_disjoint {m : ℕ} (hm : 1 ≤ m) :
    Pairwise (Function.onFun Disjoint (cellT (d := d) m)) := by
  intro j j' hjj'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  apply hjj'
  funext i
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨a1, a2⟩ := hx i
  obtain ⟨b1, b2⟩ := hx' i
  rw [div_le_iff₀ hm0] at a1 b1
  rw [lt_div_iff₀ hm0] at a2 b2
  apply Fin.ext
  have h1 : ((j i : ℕ) : ℝ) < (j' i : ℕ) + 1 := by nlinarith
  have h2 : ((j' i : ℕ) : ℝ) < (j i : ℕ) + 1 := by nlinarith
  have h1' : (j i : ℕ) < (j' i : ℕ) + 1 := by exact_mod_cast h1
  have h2' : (j' i : ℕ) < (j i : ℕ) + 1 := by exact_mod_cast h2
  omega

lemma tsamp_lintegral_cells {m : ℕ} (hm : 1 ≤ m) (F : Torus d → ℝ≥0∞) :
    ∫⁻ x, F x = ∑ j : Fin d → Fin m, ∫⁻ x in cellT m j, F x := by
  have hU : (⋃ j : Fin d → Fin m, cellT m j) = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact tsamp_cell_cover hm x
  have := lintegral_iUnion (μ := (volume : Measure (Torus d))) (f := F)
    (fun j => tsamp_measurableSet_cell m j) (tsamp_cell_disjoint hm)
  rw [hU, Measure.restrict_univ] at this
  rw [this, tsum_fintype]

lemma tsamp_cell_diam {m : ℕ} (hm : 1 ≤ m) {j : Fin d → Fin m} {x x' : Torus d}
    (hx : x ∈ cellT m j) (hx' : x' ∈ cellT m j) : KernelGrad.tdist x x' ≤ d / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [KernelGrad.tdist_eq_sub_zero]
  have e : x - x' = Torus.mk (Torus.rep x - Torus.rep x') := by
    rw [KernelGrad.mk_sub, Torus.mk_rep, Torus.mk_rep]
  rw [e]
  refine (EnergyAux.tdist_mk_le _).trans ?_
  have h1 := Whole.cmxHLS_norm_toLp_le (d := d) (fun i => (Torus.rep x - Torus.rep x') i)
  have e2 : (WithLp.toLp 2 (fun i => (Torus.rep x - Torus.rep x') i) : Euc d) =
      Torus.rep x - Torus.rep x' := by ext i; rfl
  rw [e2] at h1
  refine h1.trans ?_
  calc ∑ i, |(Torus.rep x - Torus.rep x') i| ≤ ∑ _i : Fin d, (1 / (m : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        obtain ⟨a1, a2⟩ := hx i
        obtain ⟨b1, b2⟩ := hx' i
        have : (Torus.rep x - Torus.rep x') i = Torus.rep x i - Torus.rep x' i := rfl
        rw [this, abs_le]
        have e3 : ((j i : ℝ) + 1) / m = (j i : ℝ) / m + 1 / m := by ring
        constructor <;> linarith
    _ = d / m := by simp [div_eq_mul_inv]

lemma tsamp_nCells {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    1 ≤ nCells η ∧ η ≤ 1 / (nCells η : ℝ) ∧ 1 / (nCells η : ℝ) ≤ 2 * η := by
  have hinv : 1 ≤ η⁻¹ := by rw [le_inv_comm₀ one_pos hη]; simpa using hη1
  have hm1 : 1 ≤ nCells η := by
    unfold nCells; exact Nat.le_floor (by simpa using hinv)
  have hm0 : (0 : ℝ) < nCells η := by exact_mod_cast hm1
  refine ⟨hm1, ?_, ?_⟩
  · have : (nCells η : ℝ) ≤ η⁻¹ := Nat.floor_le (by positivity)
    rw [le_div_iff₀ hm0]
    calc η * nCells η ≤ η * η⁻¹ := by gcongr
      _ = 1 := by field_simp
  · have h1 : η⁻¹ < (nCells η : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (nCells η : ℝ) ≥ 1 := by exact_mod_cast hm1
    rw [div_le_iff₀ hm0]
    have h3 : 1 ≤ 2 * η * nCells η := by
      have : 1 < η * ((nCells η : ℝ) + 1) := by
        calc 1 = η * η⁻¹ := by field_simp
          _ < η * ((nCells η : ℝ) + 1) := by gcongr
      nlinarith
    exact h3

lemma tsamp_sum_sup_le {m : ℕ} (hm : 1 ≤ m) {u Φ : Torus d → ℝ≥0∞} {p : ℝ} (hp : 0 < p)
    (h : ∀ j : Fin d → Fin m, ∀ x' ∈ cellT m j, ⨆ x ∈ cellT m j, u x ≤ Φ x') :
    ∑ j : Fin d → Fin m, (⨆ x ∈ cellT m j, u x) ^ p ≤ (m : ℝ≥0∞) ^ d * ∫⁻ x, Φ x ^ p := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hvol : ∀ j : Fin d → Fin m, (m : ℝ≥0∞) ^ d * volume (cellT m j) = 1 := by
    intro j
    rw [tsamp_cell_volume hm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    rw [show ((m : ℝ) ^ d * (1 / (m : ℝ)) ^ d) = 1 by
      rw [← mul_pow, mul_one_div_cancel hm0.ne', one_pow]]
    simp
  rw [tsamp_lintegral_cells hm, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : (⨆ x ∈ cellT m j, u x) ^ p * volume (cellT m j) ≤ ∫⁻ x in cellT m j, Φ x ^ p := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' (tsamp_measurableSet_cell m j) fun x' hx' => ?_
    exact ENNReal.rpow_le_rpow (h j x' hx') hp.le
  calc (⨆ x ∈ cellT m j, u x) ^ p
      = (m : ℝ≥0∞) ^ d * volume (cellT m j) * (⨆ x ∈ cellT m j, u x) ^ p := by rw [hvol j, one_mul]
    _ = (m : ℝ≥0∞) ^ d * ((⨆ x ∈ cellT m j, u x) ^ p * volume (cellT m j)) := by ring
    _ ≤ (m : ℝ≥0∞) ^ d * ∫⁻ x in cellT m j, Φ x ^ p := by gcongr

end HRS.Commutator.TorusNote
