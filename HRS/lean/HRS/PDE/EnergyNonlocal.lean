import HRS.PDE.EnergySymbol

/-!
# The nonlocal term: decomposition and the regime R1 bound
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- `μ ∂_j f = ∂_j (μ f) - (∂_j μ) f`: decomposition of the nonlocal coefficient. -/
theorem nonlocalCoeff_decomp {n : ℕ} (D : DynData d) (μ : Torus d → ℝ) (F : Coeff d)
    (hF : IsTrigPoly n F) (k : Lattice d) :
    nonlocalCoeff D μ F k = ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
      (((2 * Real.pi * Complex.I * (k i : ℂ)) * (2 * Real.pi * Complex.I * (k j : ℂ)) *
          ((rieszCoeff d D.s k : ℝ) : ℂ)) * mulCoeff (coeffOf μ) F k -
        ((2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d D.s k : ℝ) : ℂ)) *
          mulCoeff (derivCoeff j (coeffOf μ)) F k) := by
  unfold nonlocalCoeff
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := derivCoeff_mulCoeff j (coeffOf μ) F hF k
  have h2 : derivCoeff j (mulCoeff (coeffOf μ) F) k =
      2 * Real.pi * Complex.I * (k j : ℂ) * mulCoeff (coeffOf μ) F k := rfl
  rw [h2] at h
  have h3 : mulCoeff (coeffOf μ) (derivCoeff j F) k =
      2 * Real.pi * Complex.I * (k j : ℂ) * mulCoeff (coeffOf μ) F k -
        mulCoeff (derivCoeff j (coeffOf μ)) F k := by
    rw [h]; ring
  simp only [gradRieszCoeff, derivCoeff, rieszMult]
  rw [h3]
  ring

theorem pt_bound (M A B x y : ℂ) (MB c₀ : ℝ) (hM : ‖M‖ ≤ MB) (hA : ‖A‖ ≤ c₀) (hB : ‖B‖ ≤ c₀) :
    ‖M * (A * x - B * y)‖ ^ 2 ≤ 2 * MB ^ 2 * c₀ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hMB : 0 ≤ MB := (norm_nonneg _).trans hM
  have hc : 0 ≤ c₀ := (norm_nonneg _).trans hA
  have h1 : ‖M * (A * x - B * y)‖ ≤ MB * (c₀ * ‖x‖ + c₀ * ‖y‖) := by
    rw [norm_mul]
    refine mul_le_mul hM ?_ (norm_nonneg _) hMB
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  calc ‖M * (A * x - B * y)‖ ^ 2 ≤ (MB * (c₀ * ‖x‖ + c₀ * ‖y‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = MB ^ 2 * c₀ ^ 2 * (‖x‖ + ‖y‖) ^ 2 := by ring
    _ ≤ MB ^ 2 * c₀ ^ 2 * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    _ = _ := by ring


/-- The constant of `leibniz_l2_bound`. -/
def leibConst (α : Fin d → ℕ) (K : ℝ) : ℝ :=
  ((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, (binomW α β : ℝ) ^ 2 * K ^ 2

theorem leibConst_nonneg (α : Fin d → ℕ) (K : ℝ) : 0 ≤ leibConst α K := by
  unfold leibConst
  positivity

/-- The constant of the regime R1 bound for a fixed multi-index. -/
def r1Const (d : ℕ) (s : ℝ) (MB Λ : ℝ) (α : Fin d → ℕ) : ℝ :=
  (Fintype.card (Fin d × Fin d) : ℝ) ^ 2 * (4 * (MB * |rieszConst d s|) ^ 2 * leibConst α Λ)

theorem r1Const_nonneg (s MB Λ : ℝ) (α : Fin d → ℕ) : 0 ≤ r1Const d s MB Λ α := by
  unfold r1Const
  have := leibConst_nonneg α Λ
  positivity

theorem nonlocal_R1_fixed (s : ℝ) (hs : s ≤ (d : ℝ) - 2) (m : ℕ) (MB Λ : ℝ)
    (D : DynData d) (hDs : D.s = s) (hM : MatBound MB D.M) (μ : Torus d → ℝ)
    (hμ : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (Torus.lift μ))
    (hΛ : Torus.cbNorm (m + 3) μ ≤ Λ)
    (α : Fin d → ℕ) (hα : ∑ i, α i ≤ m) {n : ℕ} (F : Coeff d) (hF : IsTrigPoly n F)
    (S : Finset (Lattice d)) :
    ∑ k ∈ S, ‖multiDerivCoeff α (nonlocalCoeff D μ F) k‖ ^ 2 ≤
      r1Const d s MB Λ α * hsNormSq (m : ℝ) F := by
  classical
  set N := hsNormSq (m : ℝ) F with hN
  have hN0 : 0 ≤ N := hsNormSq_nonnegE _ _
  subst hDs
  have haX : ∀ β ∈ leibnizSet α, ∃ φ : Torus d → ℝ, Continuous φ ∧
      coeffOf φ = multiDerivCoeff β (coeffOf μ) ∧ ∀ x, |φ x| ≤ Λ := by
    intro β hβ
    have hβα := mem_leibnizSet.mp hβ
    obtain ⟨φ, hc, hφ, hb⟩ := exists_derivFun μ (m + 3) hμ β
      (le_trans (Finset.sum_le_sum fun i _ => hβα i) (hα.trans (by omega)))
    exact ⟨φ, hc, hφ, fun x => (hb x).trans hΛ⟩
  have haY : ∀ j : Fin d, ∀ β ∈ leibnizSet α, ∃ φ : Torus d → ℝ, Continuous φ ∧
      coeffOf φ = multiDerivCoeff β (derivCoeff j (coeffOf μ)) ∧ ∀ x, |φ x| ≤ Λ := by
    intro j β hβ
    have hβα := mem_leibnizSet.mp hβ
    obtain ⟨φ, hc, hφ, hb⟩ := exists_derivFun μ (m + 3) hμ (β + Pi.single j 1)
      (by
        have h1 : ∑ i, (β + Pi.single j 1 : Fin d → ℕ) i = ∑ i, β i + 1 := by
          simp [Finset.sum_add_distrib]
        have h2 : ∑ i, β i ≤ ∑ i, α i := Finset.sum_le_sum fun i _ => hβα i
        omega)
    refine ⟨φ, hc, ?_, fun x => (hb x).trans hΛ⟩
    rw [hφ, multiDerivCoeff_comm_single]
  have hX := leibniz_l2_bound m Λ α hα (coeffOf μ) haX F hF S
  have hY := fun j => leibniz_l2_bound m Λ α hα (derivCoeff j (coeffOf μ)) (haY j) F hF S
  set c₀ := |rieszConst d D.s| with hc₀
  let g : Fin d × Fin d → Lattice d → ℂ := fun p k =>
    ((D.M p.2 p.1 : ℝ) : ℂ) *
      (((2 * Real.pi * Complex.I * (k p.1 : ℂ)) * (2 * Real.pi * Complex.I * (k p.2 : ℂ)) *
          ((rieszCoeff d D.s k : ℝ) : ℂ)) * multiDerivCoeff α (mulCoeff (coeffOf μ) F) k -
        ((2 * Real.pi * Complex.I * (k p.1 : ℂ)) * ((rieszCoeff d D.s k : ℝ) : ℂ)) *
          multiDerivCoeff α (mulCoeff (derivCoeff p.2 (coeffOf μ)) F) k)
  have hsum : ∀ k, multiDerivCoeff α (nonlocalCoeff D μ F) k = ∑ p : Fin d × Fin d, g p k := by
    intro k
    rw [multiDerivCoeff_apply, nonlocalCoeff_decomp D μ F hF k, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, multiDerivCoeff_apply]
    ring
  simp_rw [hsum]
  have key := sum_sq_le_of_terms (Finset.univ : Finset (Fin d × Fin d)) S g
    (fun _ => 4 * (MB * c₀) ^ 2 * leibConst α Λ * N) (fun p _ => by
      have hpt : ∀ k ∈ S, ‖g p k‖ ^ 2 ≤ 2 * MB ^ 2 * c₀ ^ 2 *
          (‖multiDerivCoeff α (mulCoeff (coeffOf μ) F) k‖ ^ 2 +
            ‖multiDerivCoeff α (mulCoeff (derivCoeff p.2 (coeffOf μ)) F) k‖ ^ 2) := by
        intro k _
        refine pt_bound _ _ _ _ _ MB c₀ ?_ (norm_symT_R1 D.s hs p.1 p.2 k) (norm_symS_R1 D.s hs p.1 k)
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hM _ _
      calc ∑ k ∈ S, ‖g p k‖ ^ 2
          ≤ ∑ k ∈ S, 2 * MB ^ 2 * c₀ ^ 2 *
            (‖multiDerivCoeff α (mulCoeff (coeffOf μ) F) k‖ ^ 2 +
              ‖multiDerivCoeff α (mulCoeff (derivCoeff p.2 (coeffOf μ)) F) k‖ ^ 2) :=
            Finset.sum_le_sum hpt
        _ = 2 * MB ^ 2 * c₀ ^ 2 * (∑ k ∈ S, ‖multiDerivCoeff α (mulCoeff (coeffOf μ) F) k‖ ^ 2 +
              ∑ k ∈ S, ‖multiDerivCoeff α (mulCoeff (derivCoeff p.2 (coeffOf μ)) F) k‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 2 * MB ^ 2 * c₀ ^ 2 * (leibConst α Λ * N + leibConst α Λ * N) := by
            refine mul_le_mul_of_nonneg_left (add_le_add hX (hY p.2)) (by positivity)
        _ = _ := by ring)
  refine key.trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, r1Const]
  ring

end HRS.PDE
