import HRS.MS.S21G2_S11
import HRS.MS.S21K2_S13C
import HRS.MS.S21H2_S14aD1
import HRS.MS.R2ChaosAux13

/-!
# S21L S13V -- uniform-in-`N` variance bound for the product pair energy (R26-T3.S13, obstacle (2))

For a symmetric `h ∈ L²(μ⊗μ)` and `N ≥ 2`, under `μ^{⊗N}`:
`E[(N 𝖥_N^h(X,μ) + ½ ∬h)²] ≤ 18 ‖h‖²_{L²(μ⊗μ)}` (`s21l_s13_variance`).  Route: the exact Hoeffding identity
`N 𝖥_N^h + ½∬h = (1/(2N)) ∑_{i≠j} h_c(X_i,X_j) - (1/N) ∑_i (m(X_i) - ∬h)` (`s21l_s13_alg`, `h_c = r2CenterKernel μ h`,
`m = ∫h(·,y)dμ`), the degenerate U-statistic identity of S11 for `h_c`, orthogonality of the row terms (S13C), and
`‖h_c‖² ≤ 16 ‖h‖²`.  Applied to `h - h'` this is the uniform `N`-independent `L²` approximation estimate of packet S13.
Prefix `s21l_s13_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.deprecated false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

theorem s21l_s13_alg {N : ℕ} (hN : 2 ≤ N) (h : Euc d → Euc d → ℝ) (hs : ∀ x y, h x y = h y x)
    (X : EucConfig d N) :
    (N : ℝ) * pairEnergy h X μ + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ =
      (1 / 2) * ((N : ℝ)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j)) -
        (1 / N) * ∑ i, ((∫ y, h (X i) y ∂μ) - ∫ x, ∫ y, h x y ∂μ ∂μ) := by
  set m : Euc d → ℝ := fun x => ∫ y, h x y ∂μ with hm
  set c : ℝ := ∫ x, ∫ y, h x y ∂μ ∂μ with hc
  have hdec : ∀ x y, h x y = r2CenterKernel μ h x y + m x + m y - c := fun x y => by
    have e : ∫ x', h x' y ∂μ = m y := integral_congr_ae (ae_of_all _ fun x' => hs x' y)
    simp only [r2CenterKernel, e]
    ring
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  set B : ℝ := ∑ j, m (X j) with hB
  have hrow : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) =
      ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j) + ((N : ℝ) - 1) * m (X i) +
        (B - m (X i)) - ((N : ℝ) - 1) * c := fun i => by
    have hcardi : ((Finset.univ.erase i).card : ℝ) = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp [Nat.cast_sub (by omega : 1 ≤ N)]
    calc ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
        = ∑ j ∈ Finset.univ.erase i, (r2CenterKernel μ h (X i) (X j) + m (X i) + m (X j) - c) :=
          Finset.sum_congr rfl fun j _ => hdec _ _
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.sum_const, Finset.sum_erase_eq_sub (f := fun j => m (X j)) (Finset.mem_univ i), nsmul_eq_mul, nsmul_eq_mul,
            hcardi]
  unfold pairEnergy
  rw [Finset.sum_congr rfl fun i _ => hrow i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hmB : ∑ i, m (X i) = B := rfl
  simp only [hmB]
  have hmm : ∀ i, (∫ y, h (X i) y ∂μ) = m (X i) := fun i => rfl
  simp only [hmm, hmB]
  field_simp
  ring


theorem s21l_s13_arith' (N : ℝ) (hN : 2 ≤ N) (Hc σ2 M2 H2 : ℝ) (hHc0 : 0 ≤ Hc) (hσ0 : 0 ≤ σ2)
    (hσ : σ2 ≤ M2) (hM2 : M2 ≤ H2) :
    2 * (((N - 1) / (2 * N)) * Hc) + 2 * (σ2 / N) ≤ Hc + 2 * H2 / N := by
  have hN0 : 0 < N := by linarith
  have h1 : (N - 1) / (2 * N) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : ((N - 1) / (2 * N)) * Hc ≤ 1 / 2 * Hc := mul_le_mul_of_nonneg_right h1 hHc0
  have h3 : σ2 / N ≤ H2 / N := div_le_div_of_nonneg_right (hσ.trans hM2) hN0.le
  have e : 2 * H2 / N = 2 * (H2 / N) := by ring
  rw [e]
  nlinarith

theorem s21l_s13_arith (N : ℝ) (hN : 2 ≤ N) (Hc σ2 M2 H2 : ℝ) (hHc0 : 0 ≤ Hc) (hσ0 : 0 ≤ σ2)
    (hHc16 : Hc ≤ 16 * H2) (hσ : σ2 ≤ M2) (hM2 : M2 ≤ H2) (hH20 : 0 ≤ H2) :
    2 * (((N - 1) / (2 * N)) * Hc) + 2 * (σ2 / N) ≤ 18 * H2 := by
  have hN0 : 0 < N := by linarith
  have h1 : (N - 1) / (2 * N) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 1 / N ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hN
  have h3 : σ2 / N ≤ σ2 / 2 := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div σ2 2]
    exact mul_le_mul_of_nonneg_left h2 hσ0
  have h4 : ((N - 1) / (2 * N)) * Hc ≤ 1 / 2 * Hc := mul_le_mul_of_nonneg_right h1 hHc0
  nlinarith


theorem s21l_s13_coord_integral {N : ℕ} (φ : Euc d → ℝ) (hφ : AEStronglyMeasurable φ μ) (i : Fin N) :
    ∫ ω, φ (ω i) ∂(Measure.pi fun _ : Fin N => μ) = ∫ x, φ x ∂μ := by
  have hm : AEMeasurable (fun ω : Fin N → Euc d => ω i) (Measure.pi fun _ : Fin N => μ) :=
    (measurable_pi_apply i).aemeasurable
  have h1 := integral_map hm (f := φ) (by rw [s21k2_s13_coord_law (μ := μ) i]; exact hφ)
  rw [s21k2_s13_coord_law] at h1
  exact h1.symm

theorem s21l_s13_variance_sharp {N : ℕ} (hN : 2 ≤ N) (h : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ)) (hs : ∀ x y, h x y = h y x) :
    (∫ X : EucConfig d N, ((N : ℝ) * pairEnergy h X μ + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ) ^ 2
      ∂(Measure.pi fun _ : Fin N => μ) ≤
      ∫ z : Euc d × Euc d, (r2CenterKernel μ h z.1 z.2) ^ 2 ∂(μ.prod μ) +
        2 * (∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ)) / N) ∧
    ∫ z : Euc d × Euc d, (r2CenterKernel μ h z.1 z.2) ^ 2 ∂(μ.prod μ) ≤
      16 * ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  set ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hν
  set m : Euc d → ℝ := fun x => ∫ y, h x y ∂μ with hmdef
  set c : ℝ := ∫ x, ∫ y, h x y ∂μ ∂μ with hc
  set H2 : ℝ := ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) with hH2
  have hH20 : 0 ≤ H2 := integral_nonneg fun z => sq_nonneg _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmL : MemLp m 2 μ := s21h2_m_memLp μ hm
  have hcL : MemLp (fun z : Euc d × Euc d => r2CenterKernel μ h z.1 z.2) 2 (μ.prod μ) := s21h2_c_memLp μ hm
  have hcs : ∀ x y, r2CenterKernel μ h x y = r2CenterKernel μ h y x := s94_center_symm hs
  have hc0 : ∀ᵐ x ∂μ, ∫ y, r2CenterKernel μ h x y ∂μ = 0 := by
    filter_upwards [s21h2_c_slice μ hm] with x hx using hx.2
  have hid := r26t3_product_pair_identity hN μ (r2CenterKernel μ h) hcL hcs hc0
  set Hc : ℝ := ∫ z : Euc d × Euc d, (r2CenterKernel μ h z.1 z.2) ^ 2 ∂(μ.prod μ) with hHc
  set Sx : EucConfig d N → ℝ := fun X => ∑ i, ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j) with hSx
  set V : EucConfig d N → ℝ := fun X => (1 / 2) * ((N : ℝ)⁻¹ * Sx X) with hV
  set R : EucConfig d N → ℝ := fun X => -((1 / (N : ℝ)) * ∑ i, (m (X i) - c)) with hR
  have hex : ∀ X : EucConfig d N, (N : ℝ) * pairEnergy h X μ + (1 / 2) * c = V X + R X := fun X => by
    rw [s21l_s13_alg μ hN h hs X]
    simp only [hV, hR, hSx, hmdef, hc]
    ring
  have hterm : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      MemLp (fun X : EucConfig d N => r2CenterKernel μ h (X i) (X j)) 2 ν := fun i j hj =>
    s21g2_s11_memLp μ (r2CenterKernel μ h) hcL (Finset.ne_of_mem_erase hj).symm
  have hVL : MemLp V 2 ν := by
    have := (memLp_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun i X => ∑ j ∈ Finset.univ.erase i, r2CenterKernel μ h (X i) (X j)) (p := 2) (μ := ν)
      fun i _ => memLp_finsetSum _ fun j hj => hterm i j hj)
    exact (this.const_mul (N : ℝ)⁻¹).const_mul (1 / 2)
  have hu : ∀ i : Fin N, MemLp (fun X : EucConfig d N => m (X i) - c) 2 ν := fun i => by
    have := (hmL.sub (memLp_const c)).comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
    simpa [Function.comp_def] using this
  have hRL : MemLp R 2 ν := by
    have := (memLp_finsetSum (Finset.univ : Finset (Fin N)) (f := fun i X => m (X i) - c) (p := 2) (μ := ν)
      fun i _ => hu i)
    exact (this.const_mul (1 / (N : ℝ))).neg
  -- second moment of `V`
  have hV2 : ∫ X, V X ^ 2 ∂ν = ((N : ℝ) - 1) / (2 * N) * Hc := by
    have e : ∫ X, V X ^ 2 ∂ν = (1 / 4) * ∫ X, ((N : ℝ)⁻¹ * Sx X) ^ 2 ∂ν := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun X => ?_)
      simp only [hV]
      ring
    rw [e]
    have hid' : ∫ X, ((N : ℝ)⁻¹ * Sx X) ^ 2 ∂ν = 2 * ((N : ℝ) - 1) / N * Hc := hid
    rw [hid']
    field_simp
    ring
  -- second moment of `R`
  have hmean0 : ∫ x, (m x - c) ∂μ = 0 := by
    rw [integral_sub (hmL.integrable one_le_two) (integrable_const c)]
    have e : (∫ a, m a ∂μ) = c := rfl
    rw [e, integral_const]
    simp
  have hGm : AEStronglyMeasurable (fun z : Euc d × Euc d => (m z.1 - c) * (m z.2 - c)) (μ.prod μ) :=
    (((hmL.sub (memLp_const c)).comp_fst μ).aestronglyMeasurable).mul
      (((hmL.sub (memLp_const c)).comp_snd μ).aestronglyMeasurable)
  set σ2 : ℝ := ∫ x, (m x - c) ^ 2 ∂μ with hσ2
  have hcross : ∀ i j : Fin N, ∫ X, (m (X i) - c) * (m (X j) - c) ∂ν = if i = j then σ2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have := s21l_s13_coord_integral (N := N) μ (fun x => (m x - c) ^ 2)
        ((hmL.sub (memLp_const c)).aestronglyMeasurable.pow 2) i
      simp only [← sq]
      exact this
    · simp only [hij, if_false]
      have := s21k2_s13_integral_pair (μ := μ) (N := N) hij hGm
      refine this.trans ?_
      have h2 := integral_prod_mul (μ := μ) (ν := μ) (fun x => m x - c) (fun y => m y - c)
      rw [h2, hmean0, zero_mul]
  have hR2 : ∫ X, R X ^ 2 ∂ν = σ2 / N := by
    have e : ∀ X, R X ^ 2 = (1 / (N : ℝ)) ^ 2 * ∑ i, ∑ j, (m (X i) - c) * (m (X j) - c) := fun X => by
      simp only [hR]
      rw [neg_sq, mul_pow, sq (∑ i, (m (X i) - c)), Finset.sum_mul_sum]
    have hI : ∀ i j : Fin N, Integrable (fun X : EucConfig d N => (m (X i) - c) * (m (X j) - c)) ν :=
      fun i j => (hu i).integrable_mul (hu j)
    simp_rw [e]
    rw [integral_const_mul, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hI i j]
    have e2 : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∫ X, ∑ j, (m (X i) - c) * (m (X j) - c) ∂ν =
        ∑ j, ∫ X, (m (X i) - c) * (m (X j) - c) ∂ν := fun i _ =>
      integral_finset_sum _ fun j _ => hI i j
    rw [Finset.sum_congr rfl e2]
    simp only [hcross, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- size bounds
  have hM2 : ∫ x, (m x) ^ 2 ∂μ ≤ H2 := by
    have hint : Integrable (fun x => ∫ y, h x y ^ 2 ∂μ) μ := hm.integrable_sq.integral_prod_left
    have h1 : ∫ x, ∫ y, h x y ^ 2 ∂μ ∂μ = H2 := (integral_prod _ hm.integrable_sq).symm
    rw [← h1]
    refine integral_mono_ae hmL.integrable_sq hint ?_
    filter_upwards [s21h2_slice_memLp μ hm] with x hx
    exact s21h2_sq_integral_le μ hx
  have hc2 : c ^ 2 ≤ ∫ x, (m x) ^ 2 ∂μ := s21h2_sq_integral_le μ hmL
  have hσ : σ2 ≤ ∫ x, (m x) ^ 2 ∂μ := by
    have e : σ2 = ∫ x, (m x) ^ 2 ∂μ - c ^ 2 := by
      have e1 : ∀ x, (m x - c) ^ 2 = (m x) ^ 2 - 2 * c * m x + c ^ 2 := fun x => by ring
      simp_rw [hσ2, e1]
      have i1 : Integrable (fun x => (m x) ^ 2) μ := hmL.integrable_sq
      have i2 : Integrable (fun x => 2 * c * m x) μ := (hmL.integrable one_le_two).const_mul _
      have i12 : Integrable (fun x => (m x) ^ 2 - 2 * c * m x) μ := i1.sub i2
      rw [integral_add i12 (integrable_const _), integral_sub i1 i2, integral_const_mul]
      simp [hc]
      ring
    rw [e]
    nlinarith [sq_nonneg c]
  have hHc16 : Hc ≤ 16 * H2 := by
    have hdec : ∀ x y, r2CenterKernel μ h x y = h x y - m x - m y + c := fun x y => by
      have e : ∫ x', h x' y ∂μ = m y := integral_congr_ae (ae_of_all _ fun x' => hs x' y)
      simp only [r2CenterKernel, e, hmdef, hc]
    have hmf : Integrable (fun z : Euc d × Euc d => (m z.1) ^ 2) (μ.prod μ) :=
      ((hmL.comp_fst μ).integrable_sq)
    have hms : Integrable (fun z : Euc d × Euc d => (m z.2) ^ 2) (μ.prod μ) :=
      ((hmL.comp_snd μ).integrable_sq)
    have hI1 : ∫ z : Euc d × Euc d, (m z.1) ^ 2 ∂(μ.prod μ) = ∫ x, (m x) ^ 2 ∂μ := by
      rw [integral_prod _ hmf]; simp
    have hI2 : ∫ z : Euc d × Euc d, (m z.2) ^ 2 ∂(μ.prod μ) = ∫ x, (m x) ^ 2 ∂μ := by
      rw [integral_prod _ hms]; simp
    have hpt : ∀ z : Euc d × Euc d, (r2CenterKernel μ h z.1 z.2) ^ 2 ≤
        4 * (h z.1 z.2 ^ 2 + (m z.1) ^ 2 + (m z.2) ^ 2 + c ^ 2) := fun z => by
      rw [hdec]
      nlinarith [sq_nonneg (h z.1 z.2 - m z.1 - m z.2 + c), sq_nonneg (h z.1 z.2 + m z.1), sq_nonneg (m z.2 + c),
        sq_nonneg (h z.1 z.2 - m z.1), sq_nonneg (m z.2 - c), sq_nonneg (h z.1 z.2 + m z.2), sq_nonneg (m z.1 - c),
        sq_nonneg (h z.1 z.2 - m z.2), sq_nonneg (m z.1 + c)]
    have hA1 : Integrable (fun z : Euc d × Euc d => h z.1 z.2 ^ 2 + (m z.1) ^ 2) (μ.prod μ) := hm.integrable_sq.add hmf
    have hA2 : Integrable (fun z : Euc d × Euc d => h z.1 z.2 ^ 2 + (m z.1) ^ 2 + (m z.2) ^ 2) (μ.prod μ) := hA1.add hms
    have hint : Integrable (fun z : Euc d × Euc d => 4 * (h z.1 z.2 ^ 2 + (m z.1) ^ 2 + (m z.2) ^ 2 + c ^ 2))
        (μ.prod μ) := (hA2.add (integrable_const _)).const_mul 4
    have := integral_mono hcL.integrable_sq hint hpt
    rw [integral_const_mul, integral_add hA2 (integrable_const _), integral_add hA1 hms,
      integral_add hm.integrable_sq hmf, hI1, hI2] at this
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    rw [← hH2] at this
    nlinarith [hM2, hc2, this]
  -- conclusion
  have hfun : ∀ X : EucConfig d N, ((N : ℝ) * pairEnergy h X μ + (1 / 2) * c) ^ 2 = (V X + R X) ^ 2 := fun X => by
    rw [hex X]
  have hint1 : Integrable (fun X => (V X + R X) ^ 2) ν := (hVL.add hRL).integrable_sq
  have hint2 : Integrable (fun X => 2 * V X ^ 2 + 2 * R X ^ 2) ν :=
    (hVL.integrable_sq.const_mul 2).add (hRL.integrable_sq.const_mul 2)
  have hle : ∫ X, (V X + R X) ^ 2 ∂ν ≤ 2 * ∫ X, V X ^ 2 ∂ν + 2 * ∫ X, R X ^ 2 ∂ν := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hVL.integrable_sq.const_mul 2)
      (hRL.integrable_sq.const_mul 2)]
    exact integral_mono hint1 hint2 fun X => by nlinarith [sq_nonneg (V X - R X)]
  refine ⟨?_, hHc16⟩
  simp_rw [hfun]
  refine hle.trans ?_
  rw [hV2, hR2]
  have hHc0 : 0 ≤ Hc := integral_nonneg fun z => sq_nonneg _
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun x => sq_nonneg _
  exact s21l_s13_arith' (N : ℝ) (by exact_mod_cast hN) Hc σ2 (∫ x, (m x) ^ 2 ∂μ) H2 hHc0 hσ0 hσ hM2

/-- The uniform-in-`N` variance bound `E[(N 𝖥_N^h + ½∬h)²] ≤ 18 ‖h‖²`. -/
theorem s21l_s13_variance {N : ℕ} (hN : 2 ≤ N) (h : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ)) (hs : ∀ x y, h x y = h y x) :
    ∫ X : EucConfig d N, ((N : ℝ) * pairEnergy h X μ + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ) ^ 2
      ∂(Measure.pi fun _ : Fin N => μ) ≤ 18 * ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  obtain ⟨h1, h2⟩ := s21l_s13_variance_sharp μ hN h hm hs
  have hH0 : 0 ≤ ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) := integral_nonneg fun z => sq_nonneg _
  have hN2 : 2 / (N : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hN
  have : 2 * (∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ)) / N ≤ ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) := by
    calc 2 * (∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ)) / N =
          (2 / (N : ℝ)) * ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) := by ring
      _ ≤ 1 * ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) := mul_le_mul_of_nonneg_right hN2 hH0
      _ = _ := one_mul _
  linarith

/-- The uniform-in-`N` `L²` approximation estimate for two symmetric kernels. -/
theorem s21l_s13_variance_diff {N : ℕ} (hN : 2 ≤ N) (h h' : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hm' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) (hs' : ∀ x y, h' x y = h' y x) :
    ∫ X : EucConfig d N, ((N : ℝ) * (pairEnergy h X μ - pairEnergy h' X μ) +
        (1 / 2) * ∫ x, ∫ y, (h x y - h' x y) ∂μ ∂μ) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      ∫ z : Euc d × Euc d, (r2CenterKernel μ (fun x y => h x y - h' x y) z.1 z.2) ^ 2 ∂(μ.prod μ) +
        2 * (∫ z : Euc d × Euc d, (h z.1 z.2 - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) / N := by
  set ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hν
  have hΔm : MemLp (fun z : Euc d × Euc d => (fun x y => h x y - h' x y) z.1 z.2) 2 (μ.prod μ) := hm.sub hm'
  have key := (s21l_s13_variance_sharp μ hN (fun x y => h x y - h' x y) hΔm (fun x y => by simp only [hs x y, hs' x y])).1
  have hslice : ∀ᵐ x ∂μ, Integrable (fun y => h x y) μ ∧ Integrable (fun y => h' x y) μ := by
    filter_upwards [s21h2_slice_memLp μ hm, s21h2_slice_memLp μ hm'] with x h1 h2
    exact ⟨h1.integrable one_le_two, h2.integrable one_le_two⟩
  have hmL : MemLp (fun x => ∫ y, h x y ∂μ) 2 μ := s21h2_m_memLp μ hm
  have hmL' : MemLp (fun x => ∫ y, h' x y ∂μ) 2 μ := s21h2_m_memLp μ hm'
  have hc : ∫ x, ∫ y, (h x y - h' x y) ∂μ ∂μ =
      (∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h' x y ∂μ ∂μ := by
    rw [← integral_sub (hmL.integrable one_le_two) (hmL'.integrable one_le_two)]
    refine integral_congr_ae ?_
    filter_upwards [hslice] with x hx
    exact integral_sub hx.1 hx.2
  have hae : ∀ᵐ X ∂ν, ∀ i : Fin N, Integrable (fun y => h (X i) y) μ ∧ Integrable (fun y => h' (X i) y) μ :=
    ae_all_iff.2 fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hslice
  refine le_trans (le_of_eq (integral_congr_ae ?_)) key
  filter_upwards [hae] with X hX
  have hpe : pairEnergy (fun x y => h x y - h' x y) X μ = pairEnergy h X μ - pairEnergy h' X μ +
      (1 / 2) * ((∫ x, ∫ y, (h x y - h' x y) ∂μ ∂μ) - ((∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h' x y ∂μ ∂μ)) := by
    unfold pairEnergy
    have e1 : ∀ i : Fin N, ∫ y, (h (X i) y - h' (X i) y) ∂μ = (∫ y, h (X i) y ∂μ) - ∫ y, h' (X i) y ∂μ :=
      fun i => integral_sub (hX i).1 (hX i).2
    simp only [e1, Finset.sum_sub_distrib, mul_sub]
    ring
  rw [hpe, hc]
  ring

end HRS.MS.R26T3
