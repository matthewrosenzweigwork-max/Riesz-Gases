import HRS.Whole.Basic

/-!
# S21G2 S11 -- second moment of a degenerate product U-statistic (R26-T3.S11)

For a symmetric `h ∈ L²(μ ⊗ μ)` with `∫ h(x, y) dμ(y) = 0` a.e., under `μ^{⊗N}`:
`E[(N⁻¹ ∑_{i≠j} h(X_i, X_j))²] = 2 (N-1)/N ‖h‖²_{L²(μ⊗μ)}`.
Route: expand the square, kill every pair of ordered pairs with a coordinate occurring once (Fubini over that
coordinate, `s21g2_s11_kill`), the two surviving index identifications give `‖h‖²` each.
Helper names carry the prefix `s21g2_s11_`.  The contract is taken verbatim (generic space instead of
`Euc d` is used for the helpers only).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.MS.R26T3

section Helpers

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

/-- Fubini over the coordinate `i`: a function of `(x_i, x_j)` degenerate in `x_i`, times a function not
involving `x_i`, has integral zero. -/
theorem s21g2_s11_kill {n : ℕ} (h : E → E → ℝ) (hc : ∀ᵐ y ∂μ, ∫ x, h x y ∂μ = 0)
    (i j : Fin (n + 1)) (hij : j ≠ i) (G : (Fin (n + 1) → E) → ℝ)
    (hG : ∀ x t, G (Function.update x i t) = G x)
    (hint : Integrable (fun x => h (x i) (x j) * G x) (Measure.pi fun _ : Fin (n + 1) => μ)) :
    ∫ x, h (x i) (x j) * G x ∂(Measure.pi fun _ : Fin (n + 1) => μ) = 0 := by
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  set F : (Fin (n + 1) → E) → ℝ := fun x => h (x i) (x j) * G x with hF
  have h1 : ∫ x, F x ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    rw [← mp.integral_comp' (f := e) (g := fun p => F (e.symm p))]
    simp
  have hint' : Integrable (fun p => F (e.symm p)) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
    (mp.symm e).integrable_comp_of_integrable hint
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij
  obtain ⟨t0⟩ := nonempty_of_isProbabilityMeasure μ
  rw [h1, integral_prod_symm _ hint']
  have hae : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ), ∫ x, h x (y j') ∂μ = 0 :=
    (measurePreserving_eval (fun _ : Fin n => μ) j').quasiMeasurePreserving.ae hc
  have hz : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ),
      ∫ t, F (e.symm (t, y)) ∂μ = 0 := by
    filter_upwards [hae] with y hy
    have key : ∀ t, F (e.symm (t, y)) = h t (y j') * G (Fin.insertNth i t0 y) := fun t => by
      have hs : e.symm (t, y) = Fin.insertNth i t y := rfl
      have hG1 : G (Fin.insertNth i t y) = G (Fin.insertNth i t0 y) := by
        rw [← Fin.update_insertNth (α := fun _ : Fin (n + 1) => E) i t0 t y, hG]
      simp only [hF, hs, hG1, Fin.insertNth_apply_same, ← hj', Fin.insertNth_apply_succAbove]
    simp only [key]
    rw [integral_mul_const, hy, zero_mul]
  rw [integral_congr_ae hz]; simp

/-- Two distinct coordinates of a product measure are independent with law `μ ⊗ μ`. -/
theorem s21g2_s11_pair_mp {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin N → E => (x i, x j)) (Measure.pi fun _ : Fin N => μ) (μ.prod μ) := by
  have hind : iIndepFun (fun (k : Fin N) (x : Fin N → E) => x k) (Measure.pi fun _ : Fin N => μ) :=
    iIndepFun_pi (X := fun _ => (id : E → E)) (fun _ => aemeasurable_id)
  have hI := hind.indepFun hij
  have hev : ∀ k, (Measure.pi fun _ : Fin N => μ).map (fun x : Fin N → E => x k) = μ := fun k =>
    (measurePreserving_eval (fun _ : Fin N => μ) k).map_eq
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 hI
  rw [hev, hev] at this
  exact this

theorem s21g2_s11_memLp {N : ℕ} (h : E → E → ℝ) (hm : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ))
    {i j : Fin N} (hij : i ≠ j) :
    MemLp (fun x : Fin N → E => h (x i) (x j)) 2 (Measure.pi fun _ : Fin N => μ) :=
  hm.comp_measurePreserving (s21g2_s11_pair_mp μ hij)

theorem s21g2_s11_int {N : ℕ} (h : E → E → ℝ) (hm : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ))
    {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) :
    Integrable (fun x : Fin N → E => h (x i) (x j) * h (x k) (x l))
      (Measure.pi fun _ : Fin N => μ) :=
  (s21g2_s11_memLp μ h hm hij).integrable_mul (s21g2_s11_memLp μ h hm hkl)

theorem s21g2_s11_orth {n : ℕ} (h : E → E → ℝ) (hs : ∀ x y, h x y = h y x)
    (hc : ∀ᵐ x ∂μ, ∫ y, h x y ∂μ = 0) (hm : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ))
    {i j k l : Fin (n + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hne : ¬(k = i ∧ l = j) ∧ ¬(k = j ∧ l = i)) :
    ∫ x, h (x i) (x j) * h (x k) (x l) ∂(Measure.pi fun _ : Fin (n + 1) => μ) = 0 := by
  have hc' : ∀ᵐ y ∂μ, ∫ x, h x y ∂μ = 0 := by
    filter_upwards [hc] with y hy
    rw [← hy]; congr 1; ext x; exact hs x y
  by_cases h1 : i ≠ k ∧ i ≠ l
  · exact s21g2_s11_kill μ h hc' i j hij.symm (fun x => h (x k) (x l))
      (fun x t => by simp [Function.update_of_ne h1.1.symm, Function.update_of_ne h1.2.symm])
      (s21g2_s11_int μ h hm hij hkl)
  by_cases h2 : j ≠ k ∧ j ≠ l
  · have e : (fun x : Fin (n + 1) → E => h (x i) (x j) * h (x k) (x l)) =
        fun x => h (x j) (x i) * h (x k) (x l) := funext fun x => by rw [hs (x i) (x j)]
    rw [e]
    exact s21g2_s11_kill μ h hc' j i hij (fun x => h (x k) (x l))
      (fun x t => by simp [Function.update_of_ne h2.1.symm, Function.update_of_ne h2.2.symm])
      (by rw [← e]; exact s21g2_s11_int μ h hm hij hkl)
  exfalso
  rw [not_and_or, not_ne_iff, not_ne_iff] at h1 h2
  obtain ⟨hn1, hn2⟩ := hne
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hij (h1.trans h2.symm)
  · exact hn1 ⟨h1.symm, h2.symm⟩
  · exact hn2 ⟨h2.symm, h1.symm⟩
  · exact hij (h1.trans h2.symm)

theorem s21g2_s11_diag {N : ℕ} (h : E → E → ℝ) (hm : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ))
    {i j : Fin N} (hij : i ≠ j) :
    ∫ x : Fin N → E, h (x i) (x j) * h (x i) (x j) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ z : E × E, h z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  have mp := s21g2_s11_pair_mp μ hij
  have hfm : AEStronglyMeasurable (fun z : E × E => h z.1 z.2 * h z.1 z.2)
      ((Measure.pi fun _ : Fin N => μ).map fun x : Fin N → E => (x i, x j)) := by
    rw [mp.map_eq]; exact hm.aestronglyMeasurable.mul hm.aestronglyMeasurable
  have := integral_map mp.measurable.aemeasurable hfm
  rw [mp.map_eq] at this
  simpa [sq] using this.symm

end Helpers

theorem r26t3_product_pair_identity {d N : ℕ} (hN : 2 ≤ N) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (h : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y=h y x) (hc : ∀ᵐ x ∂μ, ∫ y, h x y ∂μ=0) :
    ∫ X : HRS.Whole.EucConfig d N, ((N : ℝ)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j))^2
      ∂(Measure.pi fun _ : Fin N => μ) =
      2*((N : ℝ)-1)/N * ∫ z : Euc d × Euc d, h z.1 z.2^2 ∂(μ.prod μ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set P : Measure (Fin (n + 1) → Euc d) := Measure.pi fun _ : Fin (n + 1) => μ with hP
  set H : ℝ := ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) with hH
  have hexp : ∀ x : Fin (n + 1) → Euc d,
      (∑ i, ∑ j ∈ Finset.univ.erase i, h (x i) (x j)) ^ 2 =
        ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k, ∑ l ∈ Finset.univ.erase k,
          h (x i) (x j) * h (x k) (x l) := fun x => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
  have hval : ∀ i j k l : Fin (n + 1), i ≠ j → k ≠ l →
      ∫ x, h (x i) (x j) * h (x k) (x l) ∂P =
        H * ((if k = i ∧ l = j then 1 else 0) + (if k = j ∧ l = i then 1 else 0)) := by
    intro i j k l hij hkl
    by_cases e1 : k = i ∧ l = j
    · obtain ⟨h1, h2⟩ := e1
      rw [h1, h2, s21g2_s11_diag μ h hm hij, ← hH]
      have : ¬(i = j ∧ j = i) := fun hh => hij hh.1
      simp [this]
    by_cases e2 : k = j ∧ l = i
    · obtain ⟨h1, h2⟩ := e2
      have e : (fun x : Fin (n + 1) → Euc d => h (x i) (x j) * h (x k) (x l)) =
          fun x => h (x i) (x j) * h (x i) (x j) := funext fun x => by
        rw [h1, h2, hs (x j) (x i)]
      rw [e, s21g2_s11_diag μ h hm hij, ← hH]
      have : ¬(k = i ∧ l = j) := e1
      simp [h1, h2, this, hij.symm]
    · rw [s21g2_s11_orth μ h hs hc hm hij hkl ⟨e1, e2⟩]; simp [e1, e2]
  have hT : ∀ i j : Fin (n + 1), i ≠ j → ∑ k, ∑ l ∈ Finset.univ.erase k,
      H * ((if k = i ∧ l = j then 1 else 0) + (if k = j ∧ l = i then 1 else 0)) = 2 * H := by
    intro i j hij
    have s1 : ∀ a b : Fin (n + 1), a ≠ b → ∑ k, ∑ l ∈ Finset.univ.erase k,
        (if k = a ∧ l = b then (1 : ℝ) else 0) = 1 := fun a b hab => by
      rw [Finset.sum_eq_single a]
      · simp [hab.symm]
      · intro k _ hk; simp [hk]
      · simp
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [s1 i j hij, s1 j i hij.symm]; ring
  have hint : ∀ i j k l : Fin (n + 1), i ≠ j → k ≠ l →
      Integrable (fun x => h (x i) (x j) * h (x k) (x l)) P := fun i j k l hij hkl =>
    s21g2_s11_int μ h hm hij hkl
  simp only [mul_pow, hexp]
  rw [integral_const_mul]
  have hsum : ∫ x, ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k, ∑ l ∈ Finset.univ.erase k,
      h (x i) (x j) * h (x k) (x l) ∂P =
      ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k, ∑ l ∈ Finset.univ.erase k,
        ∫ x, h (x i) (x j) * h (x k) (x l) ∂P := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l hl =>
        hint i j k l (Finset.ne_of_mem_erase hj).symm (Finset.ne_of_mem_erase hl).symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j hj => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l hl =>
        hint i j k l (Finset.ne_of_mem_erase hj).symm (Finset.ne_of_mem_erase hl).symm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l hl =>
      hint i j k l (Finset.ne_of_mem_erase hj).symm (Finset.ne_of_mem_erase hl).symm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact integral_finsetSum _ fun l hl =>
      hint i j k l (Finset.ne_of_mem_erase hj).symm (Finset.ne_of_mem_erase hl).symm
  rw [hsum]
  have hcalc : ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k, ∑ l ∈ Finset.univ.erase k,
        ∫ x, h (x i) (x j) * h (x k) (x l) ∂P = ((n + 1 : ℕ) : ℝ) * (n : ℝ) * (2 * H) := by
    have : ∀ i, ∑ j ∈ Finset.univ.erase i, ∑ k, ∑ l ∈ Finset.univ.erase k,
        ∫ x, h (x i) (x j) * h (x k) (x l) ∂P = (n : ℝ) * (2 * H) := fun i => by
      rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l hl =>
          hval i j k l (Finset.ne_of_mem_erase hj).symm (Finset.ne_of_mem_erase hl).symm]
      rw [Finset.sum_congr rfl fun j hj => hT i j (Finset.ne_of_mem_erase hj).symm]
      simp [Finset.card_erase_of_mem]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  rw [hcalc]
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end HRS.MS.R26T3
