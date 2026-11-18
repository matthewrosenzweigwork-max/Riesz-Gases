import HRS.MS.Fp81S21GaussianIncrementApprox2

/-! Packet 36: a common finite grid and the physical approximation producer. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 3
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Every finite family of algebraic tensors and vectors has one finite list
of directions. Both tensor factors are included, without a symmetry assumption. -/
theorem fp81s21_algebraicTensor2_common_grid
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (d r : ℕ) (x : Fin d → B) (t : Fin r → projTensor B 2)
    (ht : ∀ l, t l ∈ fp81s21_algebraicTensor2 B) :
    ∃ (k : ℕ) (h : Fin k → B) (A : Fin d → Fin k → ℝ)
      (C : Fin r → Fin k → Fin k → ℝ),
      (∀ l, (∑ i, A l i • h i) = x l) ∧
      (∀ l, (∑ i, ∑ j, C l i j • elemTensor ![h i, h j]) =
        (t l : TensorDual B 2)) := by
  choose b hb using fun l => Finsupp.mem_span_range_iff_exists_finsupp.mp (ht l)
  let I := Fin d ⊕ ((Σ l : Fin r, (b l).support) × Fin 2)
  let e := Fintype.equivFin I
  let h : Fin (Fintype.card I) → B := fun i =>
    Sum.elim x (fun z => z.1.2.val z.2) (e.symm i)
  let L (l : Fin r) (q : (b l).support) : Fin (Fintype.card I) :=
    e (Sum.inr (⟨l, q⟩, 0))
  let U (l : Fin r) (q : (b l).support) : Fin (Fintype.card I) :=
    e (Sum.inr (⟨l, q⟩, 1))
  let A : Fin d → Fin (Fintype.card I) → ℝ := fun l i =>
    if i = e (Sum.inl l) then 1 else 0
  let C : Fin r → Fin (Fintype.card I) → Fin (Fintype.card I) → ℝ := fun l i j =>
    ∑ q : (b l).support, if i = L l q ∧ j = U l q then b l q else 0
  refine ⟨_, h, A, C, ?_, ?_⟩
  · intro l
    simp [A, ite_smul, h]
  · intro l
    have hv (q : (b l).support) : ![h (L l q), h (U l q)] = q.val := by
      ext i
      fin_cases i <;> simp [h, L, U]
    calc
      (∑ i, ∑ j, C l i j • elemTensor ![h i, h j]) =
          ∑ q : (b l).support, b l q • elemTensor ![h (L l q), h (U l q)] := by
        simp only [C, Finset.sum_smul]
        simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin (Fintype.card I)))
          (t := Finset.univ (α := (b l).support))]
        simp [ite_smul, ite_and]
      _ = ∑ q : (b l).support, b l q • elemTensor q.val := by simp_rw [hv]
      _ = (t l : TensorDual B 2) := by
        exact ((b l).support.sum_coe_sort (fun z => b l z • elemTensor z)).trans (hb l)

/-- Scalar contraction of a finite direction grid preserves the represented
vector. This is used for every random coefficient value separately. -/
theorem fp81s21_grid_vector_contract
    {B : Type*} [AddCommGroup B] [Module ℝ B]
    {d k : ℕ} (x : Fin d → B) (h : Fin k → B) (A : Fin d → Fin k → ℝ)
    (hA : ∀ l, (∑ i, A l i • h i) = x l) (c : Fin d → ℝ) :
    (∑ i, (∑ l, c l * A l i) • h i) = ∑ l, c l • x l := by
  simp only [Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, hA]

/-- The analogous contraction identity for a nonsymmetric two-factor grid. -/
theorem fp81s21_grid_tensor_contract
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {r k : ℕ} (t : Fin r → projTensor B 2) (h : Fin k → B)
    (C : Fin r → Fin k → Fin k → ℝ)
    (hC : ∀ l, (∑ i, ∑ j, C l i j • elemTensor ![h i, h j]) =
      (t l : TensorDual B 2)) (c : Fin r → ℝ) :
    (∑ i, ∑ j, (∑ l, c l * C l i j) • elemTensor ![h i, h j]) =
      ∑ l, c l • (t l : TensorDual B 2) := by
  simp only [Finset.sum_smul, mul_smul]
  calc
    (∑ i, ∑ j, ∑ l, c l • C l i j • elemTensor ![h i, h j]) =
        ∑ l, ∑ i, ∑ j, c l • C l i j • elemTensor ![h i, h j] := by
      simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin k))
        (t := Finset.univ (α := Fin r))]
    _ = ∑ l, c l • (t l : TensorDual B 2) := by
      simp_rw [← Finset.smul_sum, hC]

/-- The retained literal increments admit a common finite-grid approximation,
with integrable coefficients measurable from the retained past at `v`. -/
theorem fp81s21_gaussian_increment_approximations
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a + p.T) :
    Nonempty (fp81s21_IncrementApprox36 Q a ha u v) := by
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  obtain ⟨d, x, b, hb, hbpast, hblim⟩ :=
    fp81s21_gaussian_drift_increment_approx Q a ha u v hu huv hv
  obtain ⟨r, t, c, ht, hc, hcpast, hclim⟩ :=
    fp81s21_gaussian_covariance_increment_algebraic_approx Q a ha u v hu huv hv
  choose k h A C hA hC using fun n =>
    fp81s21_algebraicTensor2_common_grid (d n) (r n) (x n) (t n) (ht n)
  let b' : ∀ n, Fin (k n) → Q.src.G0.Ω → ℝ := fun n i ω =>
    ∑ l, b n l ω * A n l i
  let c' : ∀ n, Fin (k n) → Fin (k n) → Q.src.G0.Ω → ℝ := fun n i j ω =>
    ∑ l, c n l ω * C n l i j
  have hb' (n i) : Integrable (b' n i) Q.src.G0.P :=
    integrable_finsetSum _ (fun l _ => (hb n l).mul_const _)
  have hc' (n i j) : Integrable (c' n i j) Q.src.G0.P :=
    integrable_finsetSum _ (fun l _ => (hc n l).mul_const _)
  have hbpast' (n : ℕ) (i : Fin (k n)) :
      AEStronglyMeasurable[fp81s21_incrementPast36 Q v] (b' n i) Q.src.G0.P := by
    let g : Fin (d n) → Q.src.G0.Ω → ℝ := fun l => (hbpast n l).mk (b n l)
    have hg (l : Fin (d n)) : StronglyMeasurable[fp81s21_incrementPast36 Q v] (g l) :=
      (hbpast n l).stronglyMeasurable_mk
    have hgs : StronglyMeasurable[fp81s21_incrementPast36 Q v]
        (fun ω => ∑ l, g l ω * A n l i) := by
      letI : MeasurableSpace Q.src.G0.Ω := fp81s21_incrementPast36 Q v
      exact Finset.stronglyMeasurable_fun_sum Finset.univ
        (fun l _ => (hg l).mul_const (A n l i))
    refine hgs.aestronglyMeasurable.congr ?_
    have he : ∀ᵐ ω ∂Q.src.G0.P, ∀ l : Fin (d n), b n l ω = g l ω :=
      ae_all_iff.2 (fun l => (hbpast n l).ae_eq_mk)
    filter_upwards [he] with ω hω
    change (∑ l, g l ω * A n l i) = ∑ l, b n l ω * A n l i
    exact Finset.sum_congr rfl (fun l _ => by rw [hω l])
  have hcpast' (n : ℕ) (i j : Fin (k n)) :
      AEStronglyMeasurable[fp81s21_incrementPast36 Q v] (c' n i j) Q.src.G0.P := by
    let g : Fin (r n) → Q.src.G0.Ω → ℝ := fun l => (hcpast n l).mk (c n l)
    have hg (l : Fin (r n)) : StronglyMeasurable[fp81s21_incrementPast36 Q v] (g l) :=
      (hcpast n l).stronglyMeasurable_mk
    have hgs : StronglyMeasurable[fp81s21_incrementPast36 Q v]
        (fun ω => ∑ l, g l ω * C n l i j) := by
      letI : MeasurableSpace Q.src.G0.Ω := fp81s21_incrementPast36 Q v
      exact Finset.stronglyMeasurable_fun_sum Finset.univ
        (fun l _ => (hg l).mul_const (C n l i j))
    refine hgs.aestronglyMeasurable.congr ?_
    have he : ∀ᵐ ω ∂Q.src.G0.P, ∀ l : Fin (r n), c n l ω = g l ω :=
      ae_all_iff.2 (fun l => (hcpast n l).ae_eq_mk)
    filter_upwards [he] with ω hω
    change (∑ l, g l ω * C n l i j) = ∑ l, c n l ω * C n l i j
    exact Finset.sum_congr rfl (fun l _ => by rw [hω l])
  have heD (n ω) : (∑ i, b' n i ω • h n i) = ∑ l, b n l ω • x n l :=
    fp81s21_grid_vector_contract (x n) (h n) (A n) (hA n) (fun l => b n l ω)
  have heJ (n ω) :
      (⟨fp81s21_finiteRandomTensor2 (k n) (h n) (c' n) ω,
        fp81s21_finiteRandomTensor2_mem_projTensor (k n) (h n) (c' n) ω⟩ :
          projTensor (Window p) 2) = ∑ l, c n l ω • t n l := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact fp81s21_grid_tensor_contract (t n) (h n) (C n) (hC n) (fun l => c n l ω)
  refine ⟨{
    integrableD := (fp81s21_gaussian_increments_integrable Q a ha u v).1
    integrableJ := (fp81s21_gaussian_increments_integrable Q a ha u v).2
    k := k, h := h, cD := b', cJ := c'
    hcD := hb', hcJ := hc', hcpastD := hbpast', hcpastJ := hcpast'
    hlimD := ?_, hlimJ := ?_ }⟩
  · simpa only [heD] using hblim
  · simpa only [heJ] using hclim

#print axioms fp81s21_algebraicTensor2_common_grid
#print axioms fp81s21_grid_vector_contract
#print axioms fp81s21_grid_tensor_contract
#print axioms fp81s21_gaussian_increment_approximations
end HRS.Fp81.S21
end
