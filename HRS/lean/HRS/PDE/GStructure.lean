import HRS.PDE.GalerkinLimit

/-!
# Helper lemmas for Lemma 3.12 (`G_structure`)

Coefficient-level product rule for convolutions of `H¹` sequences, commutativity of `mulCoeff`,
and the per-mode algebra of `B:lem:G-structure`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- The per-mode algebra of Lemma 3.12: `Mᵀ = S - A` with `S = -∑ λ_l q_l q_lᵀ`, `A` antisymmetric,
`e_i = 2π k_i`, `g = ĝ(k)`, `U = (aF)^(k)`, `R_j = (F ∂_j a)^(k)`. -/
theorem gstruct_core (M A : Fin d → Fin d → ℝ) (lam : Fin d → ℝ) (q : Fin d → Fin d → ℝ)
    (hM : ∀ i j, M j i = -(∑ l, lam l * q l i * q l j) - A i j) (hA : ∀ i j, A i j = -A j i)
    (e : Fin d → ℝ) (g : ℝ) (U : ℂ) (R : Fin d → ℂ) :
    ∑ i, ∑ j, ((M j i : ℝ) : ℂ) * ((Complex.I * (e i : ℂ)) *
        ((g : ℂ) * ((Complex.I * (e j : ℂ)) * U - R j))) =
      ∑ l, ((lam l : ℝ) : ℂ) * ((((∑ i, q l i * e i) ^ 2 * g : ℝ) : ℂ) * U +
        (Complex.I * ((∑ i, q l i * e i : ℝ) : ℂ)) * ((g : ℂ) * ∑ i, (q l i : ℂ) * R i)) +
      ∑ i, ∑ j, ((A i j : ℝ) : ℂ) * ((Complex.I * (e i : ℂ)) * ((g : ℂ) * R j)) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h1 : ∀ i j, ((M j i : ℝ) : ℂ) * ((Complex.I * (e i : ℂ)) *
        ((g : ℂ) * ((Complex.I * (e j : ℂ)) * U - R j))) =
      (∑ l, ((lam l : ℝ) : ℂ) * (q l i : ℂ) * (q l j : ℂ)) *
        ((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U + Complex.I * (e i : ℂ) * (g : ℂ) * R j) +
      ((A i j : ℝ) : ℂ) * ((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U) +
      ((A i j : ℝ) : ℂ) * ((Complex.I * (e i : ℂ)) * ((g : ℂ) * R j)) := by
    intro i j
    have := hM i j
    have hc : ((M j i : ℝ) : ℂ) = -(∑ l, ((lam l : ℝ) : ℂ) * (q l i : ℂ) * (q l j : ℂ)) -
        ((A i j : ℝ) : ℂ) := by
      rw [this]; push_cast; rfl
    rw [hc]
    linear_combination (((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U) *
      (-(∑ l, ((lam l : ℝ) : ℂ) * (q l i : ℂ) * (q l j : ℂ)) - ((A i j : ℝ) : ℂ))) * hI
  simp_rw [h1]
  simp only [Finset.sum_add_distrib]
  have h0 : ∑ i, ∑ j, ((A i j : ℝ) : ℂ) * ((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U) = 0 := by
    have hs : ∑ i, ∑ j, ((A i j : ℝ) : ℂ) * ((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U) =
        -∑ i, ∑ j, ((A i j : ℝ) : ℂ) * ((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA j i]; push_cast; ring
    linear_combination (1 / 2 : ℂ) * hs
  rw [h0, add_zero]
  congr 1
  simp_rw [Finset.sum_mul]
  have e1 : ∀ i, ∑ j, ∑ l, ((lam l : ℝ) : ℂ) * (q l i : ℂ) * (q l j : ℂ) *
        ((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U + Complex.I * (e i : ℂ) * (g : ℂ) * R j) =
      ∑ l, ∑ j, ((lam l : ℝ) : ℂ) * (q l i : ℂ) * (q l j : ℂ) *
        ((e i : ℂ) * (e j : ℂ) * (g : ℂ) * U + Complex.I * (e i : ℂ) * (g : ℂ) * R j) :=
    fun i => Finset.sum_comm
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast
  have hA2 : (∑ i, (q l i : ℂ) * (e i : ℂ)) * (∑ j, (q l j : ℂ) * (e j : ℂ)) =
      ∑ i, ∑ j, (q l i : ℂ) * (e i : ℂ) * ((q l j : ℂ) * (e j : ℂ)) := Finset.sum_mul_sum _ _ _ _
  have hB2 : (∑ i, (q l i : ℂ) * (e i : ℂ)) * (∑ j, (q l j : ℂ) * R j) =
      ∑ i, ∑ j, (q l i : ℂ) * (e i : ℂ) * ((q l j : ℂ) * R j) := Finset.sum_mul_sum _ _ _ _
  have hR : ((lam l : ℝ) : ℂ) * ((∑ i, (q l i : ℂ) * (e i : ℂ)) ^ 2 * (g : ℂ) * U +
        Complex.I * (∑ i, (q l i : ℂ) * (e i : ℂ)) * ((g : ℂ) * ∑ i, (q l i : ℂ) * R i)) =
      ((lam l : ℝ) : ℂ) * ((g : ℂ) * U * ((∑ i, (q l i : ℂ) * (e i : ℂ)) *
        (∑ j, (q l j : ℂ) * (e j : ℂ))) + Complex.I * (g : ℂ) *
        ((∑ i, (q l i : ℂ) * (e i : ℂ)) * (∑ j, (q l j : ℂ) * R j))) := by ring
  rw [hR, hA2, hB2]
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


/-! ### Convolution facts -/

/-- `mulCoeff` is commutative (reindex `j ↦ k - j`). -/
theorem mulCoeff_comm (a b : Coeff d) (k : Lattice d) : mulCoeff a b k = mulCoeff b a k := by
  unfold mulCoeff
  conv_rhs => rw [← (Equiv.subLeft k).tsum_eq (fun j => b (k - j) * a j)]
  exact tsum_congr fun j => by simp [mul_comm]

private theorem memHs_zero_derivCoeff' {c : Coeff d} (hc : MemHs 1 c) (j : Fin d) :
    MemHs 0 (derivCoeff j c) := by
  rw [memHs_zero_iff]
  exact Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => norm_derivCoeff_sq_le j c k) hc

/-- Product rule for coefficient convolutions of `H¹` sequences. -/
theorem derivCoeff_mulCoeff_memHs (j : Fin d) {a c : Coeff d} (ha : MemHs 1 a) (hc : MemHs 1 c)
    (k : Lattice d) :
    derivCoeff j (mulCoeff a c) k =
      mulCoeff (derivCoeff j a) c k + mulCoeff a (derivCoeff j c) k := by
  have s1 := summable_mulCoeff (derivCoeff j a) c (memHs_zero_derivCoeff' ha j)
    (hc.mono (by norm_num)) k
  have s2 := summable_mulCoeff a (derivCoeff j c) (ha.mono (by norm_num))
    (memHs_zero_derivCoeff' hc j) k
  unfold mulCoeff
  rw [← s1.tsum_add s2]
  show 2 * Real.pi * Complex.I * (k j : ℂ) * ∑' l, a (k - l) * c l = _
  rw [← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [derivCoeff, Pi.sub_apply]
  push_cast
  ring

theorem inner_toEuc_eq (x : Euc d) (k : Lattice d) :
    inner ℝ x (Lattice.toEuc k) = ∑ i, x i * (k i : ℝ) := by
  simp only [PiLp.inner_apply, Lattice.toEuc]
  simp
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _


/-- The per-mode form of Lemma 3.12, with the definitions of `Energy.lean` unfolded. -/
theorem gstruct_mode (s : ℝ) (M A : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hM : ∀ i j, M j i = -(∑ l, lam l * q l i * q l j) - A i j) (hA : ∀ i j, A i j = -A j i)
    (a F : Coeff d) (ha : MemHs 1 a) (hF : MemHs 1 F) (k : Lattice d) :
    ∑ i : Fin d, ∑ j : Fin d, ((M j i : ℝ) : ℂ) *
        gradRieszCoeff d s i (mulCoeff a (derivCoeff j F)) k =
      (∑ l : Fin d, ((lam l : ℝ) : ℂ) *
        (((symbolK d s (q l) k : ℝ) : ℂ) * mulCoeff a F k +
          (2 * Real.pi * Complex.I * (inner ℝ (q l) (Lattice.toEuc k) : ℂ)) *
            (((rieszCoeff d s k : ℝ) : ℂ) * mulCoeff F
              (fun l' => (2 * Real.pi * Complex.I * (inner ℝ (q l) (Lattice.toEuc l') : ℂ)) * a l') k))) +
      ∑ i : Fin d, ∑ j : Fin d, ((A i j : ℝ) : ℂ) *
        gradRieszCoeff d s i (mulCoeff F (derivCoeff j a)) k := by
  have hP : ∀ j, mulCoeff a (derivCoeff j F) k =
      2 * Real.pi * Complex.I * (k j : ℂ) * mulCoeff a F k - mulCoeff F (derivCoeff j a) k := by
    intro j
    have := derivCoeff_mulCoeff_memHs j ha hF k
    rw [mulCoeff_comm (derivCoeff j a) F k] at this
    show _ = derivCoeff j (mulCoeff a F) k - _
    rw [this]; ring
  have hgr : ∀ (i : Fin d) (c : Coeff d), gradRieszCoeff d s i c k =
      Complex.I * ((2 * Real.pi * (k i : ℝ) : ℝ) : ℂ) * (((rieszCoeff d s k : ℝ) : ℂ) * c k) := by
    intro i c
    show 2 * Real.pi * Complex.I * (k i : ℂ) * (((rieszCoeff d s k : ℝ) : ℂ) * c k) = _
    push_cast; ring
  have hsumR : ∀ l : Fin d, mulCoeff F
      (fun l' => (2 * Real.pi * Complex.I * (inner ℝ (q l) (Lattice.toEuc l') : ℂ)) * a l') k =
      ∑ i, (q l i : ℂ) * mulCoeff F (derivCoeff i a) k := by
    intro l
    have hs : ∀ i, Summable fun l' => F (k - l') * derivCoeff i a l' := fun i =>
      summable_mulCoeff F (derivCoeff i a) (hF.mono (by norm_num)) (memHs_zero_derivCoeff' ha i) k
    unfold mulCoeff
    calc ∑' l', F (k - l') * ((2 * Real.pi * Complex.I * (inner ℝ (q l) (Lattice.toEuc l') : ℂ)) * a l')
        = ∑' l', ∑ i, (q l i : ℂ) * (F (k - l') * derivCoeff i a l') := by
          refine tsum_congr fun l' => ?_
          rw [inner_toEuc_eq]
          simp only [derivCoeff]
          push_cast
          conv_lhs => simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i, ∑' l', (q l i : ℂ) * (F (k - l') * derivCoeff i a l') :=
          Summable.tsum_finsetSum (fun i _ => (hs i).mul_left _)
      _ = _ := Finset.sum_congr rfl fun i _ => tsum_mul_left
  set e : Fin d → ℝ := fun i => 2 * Real.pi * (k i : ℝ) with he
  set g : ℝ := rieszCoeff d s k with hg
  set U : ℂ := mulCoeff a F k with hU
  set R : Fin d → ℂ := fun j => mulCoeff F (derivCoeff j a) k with hR
  have hP' : ∀ j, mulCoeff a (derivCoeff j F) k = Complex.I * (e j : ℂ) * U - R j := by
    intro j
    rw [hP]; simp only [he, hU, hR]; push_cast; ring
  have hq : ∀ l, ∑ i, q l i * e i = 2 * Real.pi * inner ℝ (q l) (Lattice.toEuc k) := by
    intro l
    rw [inner_toEuc_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [he]; ring
  have hL : ∑ i : Fin d, ∑ j : Fin d, ((M j i : ℝ) : ℂ) *
        gradRieszCoeff d s i (mulCoeff a (derivCoeff j F)) k =
      ∑ i, ∑ j, ((M j i : ℝ) : ℂ) * ((Complex.I * (e i : ℂ)) *
        ((g : ℂ) * ((Complex.I * (e j : ℂ)) * U - R j))) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hgr, hP' j]
  rw [hL, gstruct_core (fun i j => M i j) (fun i j => A i j) lam (fun l i => q l i) hM hA e g U R]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsumR l, hq l]
    simp only [symbolK, hg]
    push_cast
    ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hgr]

end HRS.PDE
