import HRS.MS.S21G2_S11aA

/-!
# S21G2 S11a (part B) -- an isonormal Gaussian field driven by one i.i.d. sequence (R26-T3.S11a)

For a real inner product space `H` with a Parseval sequence `e` (`∑ ⟪e_n,h⟫⟪e_n,h'⟫ = ⟪h,h'⟫`), one i.i.d. standard Gaussian
sequence `ξ` and measurable `W h = L²-lim ∑_{n<m} ⟪e_n,h⟫ ξ_n` with: every finite combination `∑ c_i W f_i` has law
`N(0, ‖∑ c_i f_i‖²)`, and `E[W h W h'] = ⟪h,h'⟫` (polarisation).  Helper names carry the prefix `s21g2_s11a_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_s11a_second {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ} (hF : AEMeasurable F P) {v : ℝ≥0} (h : P.map F = gaussianReal 0 v) :
    ∫ ω, F ω ^ 2 ∂P = v := by
  have h1 : ∫ ω, F ω ^ 2 ∂P = ∫ x, x ^ 2 ∂(gaussianReal 0 v) := by
    rw [← h, integral_map hF (by fun_prop : Continuous fun x : ℝ => x ^ 2).aestronglyMeasurable]
  rw [h1, ← variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := fun x : ℝ => x)
    measurable_id'.aemeasurable (by simpa using integral_id_gaussianReal (μ := 0) (v := v))]
  exact variance_fun_id_gaussianReal

theorem s21g2_s11a_isonormal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H)
    (hP : ∀ h h' : H, HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h')) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ → Ω → ℝ) (W : H → Ω → ℝ),
      HRS.IsStdGaussianSeq P ξ ∧ (∀ i, MemLp (ξ i) 2 P) ∧ (∀ h, Measurable (W h)) ∧ (∀ h, MemLp (W h) 2 P) ∧
      (∀ h, Tendsto (fun m => ∫ ω, (∑ i ∈ Finset.range m, inner ℝ (e i) h * ξ i ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0)) ∧
      (∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → H),
        P.map (fun ω => ∑ i, c i * W (f i) ω) = gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2))) ∧
      (∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h') := by
  obtain ⟨Ω, mΩ, P, X, hXm, hXlaw, hXind, hPprob⟩ := ProbabilityTheory.exists_iid ℕ (gaussianReal 0 1)
  have hsum : ∀ h : H, Summable fun n => (inner ℝ (e n) h) ^ 2 := fun h => by
    simpa [sq] using (hP h h).summable
  have hlim : ∀ h : H, ∃ F : Ω → ℝ, Measurable F ∧ MemLp F 2 P ∧
      Tendsto (fun k => ∫ ω, (s21g2_s11a_S X (fun n => inner ℝ (e n) h) k ω - F ω) ^ 2 ∂P)
        atTop (𝓝 0) := fun h => s21g2_s11a_limit hXlaw hXind _ (hsum h)
  choose W hWm hW2 hWlim using hlim
  have htsum : ∀ u : H, ∑' n, (inner ℝ (e n) u) ^ 2 = ‖u‖ ^ 2 := fun u => by
    have := (hP u u).tsum_eq
    simpa [sq, real_inner_self_eq_norm_sq] using this
  have hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → H),
      P.map (fun ω => ∑ i, c i * W (f i) ω) = gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)) := by
    intro n c f
    set u : H := ∑ i, c i • f i with hu
    set a : ℕ → ℝ := fun j => inner ℝ (e j) u with ha
    have hpt : ∀ k ω, s21g2_s11a_S X a k ω =
        ∑ i, c i * s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω := fun k ω => by
      simp only [s21g2_s11a_S, ha, hu, inner_sum, inner_smul_right, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have hmem : MemLp (fun ω => ∑ i, c i * W (f i) ω) 2 P :=
      memLp_finsetSum (f := fun i ω => c i * W (f i) ω) Finset.univ fun i _ => (hW2 (f i)).const_mul (c i)
    have hgk := s21g2_s11a_memLp hXlaw (fun j => inner ℝ (e j) u)
    refine s21g2_s11a_law hXlaw hXind a (hsum u) hmem ?_ |>.trans ?_
    · have hbound : ∀ k, ∫ ω, (s21g2_s11a_S X a k ω - ∑ i, c i * W (f i) ω) ^ 2 ∂P ≤
          n * ∑ i, c i ^ 2 * ∫ ω, (s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω - W (f i) ω) ^ 2 ∂P := by
        intro k
        have hd : ∀ i, MemLp (fun ω => s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω - W (f i) ω) 2 P :=
          fun i => (s21g2_s11a_memLp hXlaw _ k).sub (hW2 (f i))
        have e1 : ∀ ω, s21g2_s11a_S X a k ω - ∑ i, c i * W (f i) ω =
            ∑ i, c i * (s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω - W (f i) ω) := fun ω => by
          rw [hpt]; simp only [mul_sub, Finset.sum_sub_distrib]
        simp_rw [e1]
        have hi : ∀ i, Integrable (fun ω => (c i * (s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω
            - W (f i) ω)) ^ 2) P := fun i => ((hd i).const_mul (c i)).integrable_sq
        calc ∫ ω, (∑ i, c i * (s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω - W (f i) ω)) ^ 2 ∂P
            ≤ ∫ ω, (n : ℝ) * ∑ i, (c i * (s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω
                - W (f i) ω)) ^ 2 ∂P := by
              refine integral_mono ?_ ((integrable_finsetSum _ fun i _ => hi i).const_mul _) fun ω => ?_
              · exact (memLp_finsetSum (f := fun i ω => c i * (s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω
                  - W (f i) ω)) Finset.univ fun i _ => (hd i).const_mul (c i)).integrable_sq
              · simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
                  (f := fun i => c i * (s21g2_s11a_S X (fun j => inner ℝ (e j) (f i)) k ω - W (f i) ω))
          _ = _ := by
              rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i]
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← integral_const_mul]
              exact integral_congr_ae (ae_of_all _ fun ω => by ring)
      refine squeeze_zero (fun k => integral_nonneg fun _ => sq_nonneg _) hbound ?_
      have : Tendsto (fun k => (n : ℝ) * ∑ i, c i ^ 2 * ∫ ω, (s21g2_s11a_S X
          (fun j => inner ℝ (e j) (f i)) k ω - W (f i) ω) ^ 2 ∂P) atTop (𝓝 ((n : ℝ) * ∑ i : Fin n, c i ^ 2 * 0)) :=
        (tendsto_finset_sum _ fun i _ => (hWlim (f i)).const_mul (c i ^ 2)).const_mul _
      simpa using this
    · rw [htsum u]
  have hsecond : ∀ h : H, ∫ ω, W h ω ^ 2 ∂P = ‖h‖ ^ 2 := fun h => by
    have := hcomb 1 (fun _ => 1) (fun _ => h)
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, one_smul] at this
    rw [s21g2_s11a_second (hWm h).aemeasurable this, Real.coe_toNNReal _ (sq_nonneg _)]
  refine ⟨Ω, mΩ, P, hPprob, X, W, ⟨hXind, fun i => (hXlaw i).map_eq⟩,
    fun i => HRS.HilbertCLTAux.gauss_memLp hXlaw i, hWm, hW2, fun h => hWlim h, hcomb, ?_⟩
  intro h h'
  have hpm : ∀ s : ℝ, ∫ ω, (W h ω + s * W h' ω) ^ 2 ∂P = ‖h + s • h'‖ ^ 2 := fun s => by
    have := hcomb 2 ![1, s] ![h, h']
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, one_smul] at this
    have hm : Measurable (fun ω => W h ω + s * W h' ω) := (hWm h).add ((hWm h').const_mul s)
    rw [s21g2_s11a_second hm.aemeasurable this, Real.coe_toNNReal _ (sq_nonneg _)]
  have h1 := hpm 1
  have h2 := hpm (-1)
  have hi1 : Integrable (fun ω => W h ω * W h' ω) P := (hW2 h).integrable_mul (hW2 h')
  have hexp : ∀ s : ℝ, ∫ ω, (W h ω + s * W h' ω) ^ 2 ∂P =
      ∫ ω, W h ω ^ 2 ∂P + 2 * s * ∫ ω, W h ω * W h' ω ∂P + s ^ 2 * ∫ ω, W h' ω ^ 2 ∂P := fun s => by
    have e1 : ∀ ω, (W h ω + s * W h' ω) ^ 2 =
        W h ω ^ 2 + (2 * s) * (W h ω * W h' ω) + s ^ 2 * W h' ω ^ 2 := fun ω => by ring
    simp_rw [e1]
    have i1 : Integrable (fun ω => W h ω ^ 2) P := (hW2 h).integrable_sq
    have i2 : Integrable (fun ω => (2 * s) * (W h ω * W h' ω)) P := hi1.const_mul _
    have i3 : Integrable (fun ω => s ^ 2 * W h' ω ^ 2) P := (hW2 h').integrable_sq.const_mul _
    rw [integral_add (f := fun ω => W h ω ^ 2 + (2 * s) * (W h ω * W h' ω))
      (g := fun ω => s ^ 2 * W h' ω ^ 2) (i1.add i2) i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul]
  rw [hexp, hsecond, hsecond] at h1 h2
  simp only [one_smul, neg_smul, ← sub_eq_add_neg, norm_add_sq_real, norm_sub_sq_real] at h1 h2
  linarith

end HRS.MS.R26T3
