import HRS.Whole.Q09AAux4
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ComplexInnerProductSpace ContDiff

/-!
# Packet Q09-A, part 5: `H^m` norms through chains of weak derivatives

`chain_of_memSobolev` (a function in `H^m` has the chain of weak derivatives `∂_i^j u ∈ L²`, with norms
controlled by `‖u‖_{H^m}`) and `memSobolev_of_chains` (conversely, chains in every coordinate direction
give `ψ ∈ H^m` with `‖ψ‖²_{H^m} ≤ (d+1)^{m-1}(‖ψ‖² + ∑_i ‖∂_i^m ψ‖²)`).
-/

noncomputable section

namespace HRS.Whole.Q09A
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux LineDeriv

variable {d : ℕ}

theorem sq_coord_le_wt (i : Fin d) (ξ : Euc d) : (2 * Real.pi * ξ i) ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
  have h1 : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
  have h2 : (ξ i) ^ 2 ≤ ‖ξ‖ ^ 2 := sq_le_sq.mpr (by simpa [abs_norm] using h1)
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

theorem coord_pow_le_wt (i : Fin d) (ξ : Euc d) (j : ℕ) :
    ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j‖ ^ 2 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j := by
  have hz : ‖2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)‖ ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
    have : ‖2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)‖ ^ 2 = (2 * Real.pi * ξ i) ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_mul, mul_pow, abs_of_pos Real.pi_pos, sq_abs]
    rw [this]
    exact sq_coord_le_wt i ξ
  calc ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) ^ j‖ ^ 2
      = (‖2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)‖ ^ 2) ^ j := by
        rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j 2]
    _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hz j


theorem chain_of_memSobolev {u : Euc d → ℝ} {m : ℕ} (hu : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u) (i : Fin d) :
    ∃ G : ℕ → Euc d → ℂ, Chain i m (fun x => ((u x : ℝ) : ℂ)) G ∧
      ∀ j ≤ m, ∃ hj : MemLp (G j) 2 volume,
        ∫ x, ‖G j x‖ ^ 2 ≤ HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) u := by
  have hf : MemLp (fun x => ((u x : ℝ) : ℂ)) 2 volume := hu.1.ofReal (K := ℂ)
  have hfL : fourierL2 u = fcL hf := fourierL2_eq hu.1
  have hF : MemLp (fcL hf) 2 volume := fcL_memLp hf
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m * ‖fcL hf ξ‖ ^ 2)
      volume := by
    have := hu.2
    rw [hfL] at this
    simpa [Real.rpow_natCast] using this
  -- `(2πiξ_i)^j f̂ ∈ L²` for `j ≤ m`
  have hmem : ∀ j ≤ m, MemLp (fun ξ : Euc d => (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j * fcL hf ξ)
      2 volume := by
    intro j hj
    have hc : Continuous fun ξ : Euc d => (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j := by fun_prop
    have hasm : AEStronglyMeasurable (fun ξ : Euc d =>
        (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j * fcL hf ξ) volume :=
      hc.aestronglyMeasurable.mul hF.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hasm]
    refine hint.mono' (hasm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    have hw1 : 1 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg Real.pi, sq_nonneg ‖ξ‖]
    have h1 := coord_pow_le_wt i ξ j
    have h2 : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m :=
      pow_le_pow_right₀ hw1 hj
    rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)
  obtain ⟨G, hG, hGf⟩ := exists_chain hf i m (by
    have := (hmem m le_rfl).const_mul (((2 * Real.pi * Complex.I) ^ m)⁻¹)
    refine this.ae_eq (Eventually.of_forall fun ξ => ?_)
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ^ m ≠ 0 := by
      apply pow_ne_zero
      simp [Real.pi_ne_zero]
    simp only [mul_pow]
    field_simp)
  refine ⟨G, hG, fun j hj => ?_⟩
  obtain ⟨hGj, hGjf⟩ := hGf j hj
  refine ⟨hGj, ?_⟩
  have e1 : ∫ x, ‖G j x‖ ^ 2 = ∫ ξ, ‖fcL hGj ξ‖ ^ 2 := (integral_norm_sq_fcL hGj).symm
  rw [e1]
  have e2 : ∫ ξ, ‖fcL hGj ξ‖ ^ 2 =
      ∫ ξ, ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j * fcL hf ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hGjf] with ξ h
    rw [h]
  rw [e2]
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  rw [hfL]
  refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity) ?_
    (Eventually.of_forall fun ξ => ?_)
  · have := hu.2
    rw [hfL] at this
    exact this
  · have hw1 : 1 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg Real.pi, sq_nonneg ‖ξ‖]
    have h1 := coord_pow_le_wt i ξ j
    have h2 : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m :=
      pow_le_pow_right₀ hw1 hj
    beta_reduce
    rw [norm_mul, mul_pow, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)

theorem pow_sum_le_aux {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) (m : ℕ) (hm : 1 ≤ m) :
    (1 + ∑ i, y i) ^ m ≤ ((d : ℝ) + 1) ^ (m - 1) * (1 + ∑ i, y i ^ m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Option (Fin d))))
    (f := fun o : Option (Fin d) => o.elim (1 : ℝ) y) (n := n) (by
      intro o _; cases o <;> simp [hy])
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, Finset.card_univ,
    Fintype.card_option, Fintype.card_fin, one_pow] at h
  have hc : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) ^ n := by positivity
  rw [div_le_iff₀ hc] at h
  simpa [mul_comm] using h

theorem norm_coord_sq (i : Fin d) (ξ : Euc d) (m : ℕ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) ^ m‖ ^ 2 = ((2 * Real.pi * ξ i) ^ 2) ^ m := by
  have h : ‖2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)‖ = |2 * Real.pi * ξ i| := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) = ((2 * Real.pi * ξ i : ℝ) : ℂ) * Complex.I
      by push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_pow, h, ← pow_mul, Nat.mul_comm m 2, pow_mul, sq_abs]

theorem memSobolev_of_chains {ψ : Euc d → ℝ} {m : ℕ} (hm : 1 ≤ m) (hψ : MemLp ψ 2 volume)
    (G : Fin d → ℕ → Euc d → ℂ)
    (hG : ∀ i, Chain i m (fun x => ((ψ x : ℝ) : ℂ)) (G i)) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) ψ ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) ψ ≤
        ((d : ℝ) + 1) ^ (m - 1) * ((∫ x, ψ x ^ 2) + ∑ i, ∫ x, ‖G i m x‖ ^ 2) := by
  have hf : MemLp (fun x => ((ψ x : ℝ) : ℂ)) 2 volume := hψ.ofReal (K := ℂ)
  have hfL : fourierL2 ψ = fcL hf := fourierL2_eq hψ
  have hF : MemLp (fcL hf) 2 volume := fcL_memLp hf
  have hGm : ∀ i, ∃ hj : MemLp (G i m) 2 volume,
      fcL hj =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ m * fcL hf ξ :=
    fun i => Chain.fourier (hG i) hf m le_rfl
  have hA : ∀ i, Integrable (fun ξ : Euc d =>
      ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ m * fcL hf ξ‖ ^ 2) volume := by
    intro i
    obtain ⟨hj, hjf⟩ := hGm i
    have h1 : Integrable (fun ξ : Euc d => ‖fcL hj ξ‖ ^ 2) volume :=
      (fcL_memLp hj).norm.integrable_sq
    refine h1.congr ?_
    filter_upwards [hjf] with ξ h
    simp only [h]
  have hA' : ∀ i, ∫ ξ, ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ m * fcL hf ξ‖ ^ 2 =
      ∫ x, ‖G i m x‖ ^ 2 := by
    intro i
    obtain ⟨hj, hjf⟩ := hGm i
    rw [← integral_norm_sq_fcL hj]
    refine integral_congr_ae ?_
    filter_upwards [hjf] with ξ h
    simp only [h]
  have hF2 : Integrable (fun ξ : Euc d => ‖fcL hf ξ‖ ^ 2) volume := hF.norm.integrable_sq
  have hF2' : ∫ ξ, ‖fcL hf ξ‖ ^ 2 = ∫ x, ψ x ^ 2 := by
    rw [integral_norm_sq_fcL hf]
    simp
  have hpt : ∀ ξ : Euc d, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) * ‖fcL hf ξ‖ ^ 2 ≤
      ((d : ℝ) + 1) ^ (m - 1) * (‖fcL hf ξ‖ ^ 2 +
        ∑ i, ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ m * fcL hf ξ‖ ^ 2) := by
    intro ξ
    have hw : 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = 1 + ∑ i, (2 * Real.pi * ξ i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by rw [Real.norm_eq_abs, sq_abs]; ring
    have hy : ∀ i, 0 ≤ (2 * Real.pi * ξ i) ^ 2 := fun i => sq_nonneg _
    have h1 := pow_sum_le_aux (fun i => (2 * Real.pi * ξ i) ^ 2) hy m hm
    have h3 : ∀ i, ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ m * fcL hf ξ‖ ^ 2 =
        ((2 * Real.pi * ξ i) ^ 2) ^ m * ‖fcL hf ξ‖ ^ 2 := by
      intro i
      rw [norm_mul, mul_pow, norm_coord_sq]
    rw [Real.rpow_natCast, hw]
    calc (1 + ∑ i, (2 * Real.pi * ξ i) ^ 2) ^ m * ‖fcL hf ξ‖ ^ 2
        ≤ (((d : ℝ) + 1) ^ (m - 1) * (1 + ∑ i, ((2 * Real.pi * ξ i) ^ 2) ^ m)) * ‖fcL hf ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = _ := by
          simp only [h3]
          rw [← Finset.sum_mul]
          ring
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) *
      ‖fcL hf ξ‖ ^ 2) volume := by
    have hbound : Integrable (fun ξ : Euc d => ((d : ℝ) + 1) ^ (m - 1) * (‖fcL hf ξ‖ ^ 2 +
        ∑ i, ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ m * fcL hf ξ‖ ^ 2)) volume :=
      (hF2.add (integrable_finsetSum _ fun i _ => hA i)).const_mul _
    refine hbound.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · have hc : Continuous fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) := by
        simp only [Real.rpow_natCast]; fun_prop
      exact hc.aestronglyMeasurable.mul (hF.norm.aemeasurable.pow_const 2).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact hpt ξ
  refine ⟨⟨hψ, by rw [hfL]; exact hint⟩, ?_⟩
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  rw [hfL]
  calc ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) * ‖fcL hf ξ‖ ^ 2
      ≤ ∫ ξ, ((d : ℝ) + 1) ^ (m - 1) * (‖fcL hf ξ‖ ^ 2 +
        ∑ i, ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ m * fcL hf ξ‖ ^ 2) :=
        integral_mono hint ((hF2.add (integrable_finsetSum _ fun i _ => hA i)).const_mul _) hpt
    _ = ((d : ℝ) + 1) ^ (m - 1) * ((∫ x, ψ x ^ 2) + ∑ i, ∫ x, ‖G i m x‖ ^ 2) := by
        rw [integral_const_mul, integral_add hF2 (integrable_finsetSum _ fun i _ => hA i),
          integral_finsetSum _ fun i _ => hA i, hF2']
        simp only [hA']

end HRS.Whole.Q09A
