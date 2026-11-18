import HRS.MS.SA12X3N1I

/-!
# S.A.12 N1/N2 (SA12X3), part J: pointwise bound and convergence of the periodic nonlocal test function
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x3n_term_alg (f1 f2 c1 e1 m1 m2 c2 e2 : ℝ) :
    |(f1 * c1 + m1 * c2) - (f2 * e1 + m2 * e2)| ≤
      |f1 - f2| * |c1| + |f2| * |c1 - e1| + |m1 - m2| * |c2| + |m2| * |c2 - e2| := by
  have : (f1 * c1 + m1 * c2) - (f2 * e1 + m2 * e2) =
      (f1 - f2) * c1 + f2 * (c1 - e1) + ((m1 - m2) * c2 + m2 * (c2 - e2)) := by ring
  rw [this]
  calc _ ≤ |(f1 - f2) * c1 + f2 * (c1 - e1)| + |(m1 - m2) * c2 + m2 * (c2 - e2)| := abs_add_le _ _
    _ ≤ (|(f1 - f2) * c1| + |f2 * (c1 - e1)|) + (|(m1 - m2) * c2| + |m2 * (c2 - e2)|) :=
        add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ = _ := by simp only [abs_mul]; ring

theorem sa12x3n_nlsum_eq {K : Euc d → ℝ} (hK : LocallyIntegrable K volume) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ}
    (hμ : ContDiff ℝ 1 μ) (x : Euc d) :
    ∑ i : Fin d, ∑ j : Fin d, M j i *
        partialDeriv (fun _ : Fin 1 => j) (fun y => μ y * gradient (HRS.Whole.convFun K ψ) y i) x =
      ∑ i : Fin d, ∑ j : Fin d, M j i * (fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) *
        HRS.Whole.convFun K (D1 i ψ) x + μ x * HRS.Whole.convFun K (D1 j (D1 i ψ)) x) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sa12x3n_nl_formula hK hψ hψc hμ i j x]

theorem sa12x3n_nlper_eq {L : ℝ} {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ}
    (hμ : ContDiff ℝ 1 μ) (x : Euc d) :
    nonlocalTestPer L γ M μ ψ x =
      ∑ i : Fin d, ∑ j : Fin d, M j i * (fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) *
        HRS.Whole.convFun γ (D1 i ψ) x + μ x * HRS.Whole.convFun γ (D1 j (D1 i ψ)) x) :=
  sa12x3n_nlsum_eq hγ hψ hψc M hμ x

theorem sa12x3n_fderiv_e {μ : Euc d → ℝ} (x : Euc d) (j : Fin d) :
    |fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ))| ≤ ‖fderiv ℝ μ x‖ := by
  have := (fderiv ℝ μ x).le_opNorm (EuclideanSpace.single j (1 : ℝ))
  simpa [PiLp.norm_single, Real.norm_eq_abs] using this

theorem sa12x3n_nl_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ L₁ Kc : ℝ, 1 ≤ L₁ ∧ 0 ≤ Kc ∧
      (∀ L : ℝ, L₁ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ → ∀ μ : Euc d → ℝ, ContDiff ℝ 1 μ →
        ∀ x : Euc d, |nonlocalTestPer L γ M μ ψ x| ≤ Kc * (‖fderiv ℝ μ x‖ + |μ x|)) ∧
      ∀ R2 : ℝ, ∃ L₂ Kq : ℝ, 1 ≤ L₂ ∧ 0 ≤ Kq ∧
        ∀ L : ℝ, L₂ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ → ∀ μ₁ μ₂ : Euc d → ℝ,
          ContDiff ℝ 1 μ₁ → ContDiff ℝ 1 μ₂ → ∀ x : Euc d, ‖x‖ ≤ R2 →
            |nonlocalTestPer L γ M μ₁ ψ x - ∑ i : Fin d, ∑ j : Fin d, M j i *
                partialDeriv (fun _ : Fin 1 => j) (fun y => μ₂ y * gradient (HRS.Whole.convFun (rieszKernel d s) ψ) y i) x| ≤
              Kc * (‖fderiv ℝ μ₁ x - fderiv ℝ μ₂ x‖ + |μ₁ x - μ₂ x|) +
                Kq / L * (‖fderiv ℝ μ₂ x‖ + |μ₂ x|) := by
  obtain ⟨R, B, hR, hB, hd1, hd2⟩ := sa12x3n_test_data hψ hψc
  obtain ⟨L₁, Kc1, hL₁, hKc1, hK1⟩ := sa12x3n_conv_bound hd s hs0 hsd R hR
  set Ms : ℝ := ∑ i : Fin d, ∑ j : Fin d, |M j i| with hMs
  have hMs0 : 0 ≤ Ms := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hloc := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  refine ⟨L₁, Ms * (Kc1 * B), hL₁, by positivity, ?_, fun R2 => ?_⟩
  · intro L hL γ hγ μ hμ x
    rw [sa12x3n_nlper_eq hγ.locInt hψ hψc M hμ x]
    have hc1 : ∀ i, |HRS.Whole.convFun γ (D1 i ψ) x| ≤ Kc1 * B := fun i =>
      hK1 L hL γ hγ _ (hd1 i).1 (hd1 i).2.1 (hd1 i).2.2.1 B (hd1 i).2.2.2 x
    have hc2 : ∀ i j, |HRS.Whole.convFun γ (D1 j (D1 i ψ)) x| ≤ Kc1 * B := fun i j =>
      hK1 L hL γ hγ _ (hd2 i j).1 (hd2 i j).2.1 (hd2 i j).2.2.1 B (hd2 i j).2.2.2 x
    have hT : ∀ i j : Fin d, |fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) * HRS.Whole.convFun γ (D1 i ψ) x +
        μ x * HRS.Whole.convFun γ (D1 j (D1 i ψ)) x| ≤ (Kc1 * B) * (‖fderiv ℝ μ x‖ + |μ x|) := by
      intro i j
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 := sa12x3n_fderiv_e (μ := μ) x j
      nlinarith [mul_le_mul h1 (hc1 i) (abs_nonneg _) (norm_nonneg _),
        mul_le_mul_of_nonneg_left (hc2 i j) (abs_nonneg (μ x))]
    calc _ ≤ ∑ i : Fin d, |∑ j : Fin d, M j i * (fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) *
            HRS.Whole.convFun γ (D1 i ψ) x + μ x * HRS.Whole.convFun γ (D1 j (D1 i ψ)) x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |M j i| * ((Kc1 * B) * (‖fderiv ℝ μ x‖ + |μ x|)) := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hT i j) (abs_nonneg _)
      _ = Ms * (Kc1 * B) * (‖fderiv ℝ μ x‖ + |μ x|) := by
          rw [hMs, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  · obtain ⟨L₂, Kq1, hL₂, hKq1, hK2⟩ := sa12x3n_conv_conv hd s hs0 hsd R hR R2
    refine ⟨max L₁ L₂, Ms * (Kq1 * B), le_max_of_le_left hL₁, by positivity,
      fun L hL γ hγ μ₁ μ₂ hμ₁ hμ₂ x hx => ?_⟩
    have hLa : L₁ ≤ L := (le_max_left _ _).trans hL
    have hLb : L₂ ≤ L := (le_max_right _ _).trans hL
    have hL0 : 0 < L := by linarith
    rw [sa12x3n_nlper_eq hγ.locInt hψ hψc M hμ₁ x, sa12x3n_nlsum_eq hloc hψ hψc M hμ₂ x]
    have hc1 : ∀ i, |HRS.Whole.convFun γ (D1 i ψ) x| ≤ Kc1 * B := fun i =>
      hK1 L hLa γ hγ _ (hd1 i).1 (hd1 i).2.1 (hd1 i).2.2.1 B (hd1 i).2.2.2 x
    have hc2 : ∀ i j, |HRS.Whole.convFun γ (D1 j (D1 i ψ)) x| ≤ Kc1 * B := fun i j =>
      hK1 L hLa γ hγ _ (hd2 i j).1 (hd2 i j).2.1 (hd2 i j).2.2.1 B (hd2 i j).2.2.2 x
    have hd1' : ∀ i, |HRS.Whole.convFun γ (D1 i ψ) x - HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) x| ≤
        Kq1 * B / L := fun i =>
      hK2 L hLb γ hγ _ (hd1 i).1 (hd1 i).2.1 (hd1 i).2.2.1 B (hd1 i).2.2.2 x hx
    have hd2' : ∀ i j, |HRS.Whole.convFun γ (D1 j (D1 i ψ)) x -
        HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) x| ≤ Kq1 * B / L := fun i j =>
      hK2 L hLb γ hγ _ (hd2 i j).1 (hd2 i j).2.1 (hd2 i j).2.2.1 B (hd2 i j).2.2.2 x hx
    have hT : ∀ i j : Fin d,
        |(fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ)) * HRS.Whole.convFun γ (D1 i ψ) x +
            μ₁ x * HRS.Whole.convFun γ (D1 j (D1 i ψ)) x) -
          (fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ)) * HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) x +
            μ₂ x * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) x)| ≤
        (Kc1 * B) * (‖fderiv ℝ μ₁ x - fderiv ℝ μ₂ x‖ + |μ₁ x - μ₂ x|) +
          (Kq1 * B / L) * (‖fderiv ℝ μ₂ x‖ + |μ₂ x|) := by
      intro i j
      refine (sa12x3n_term_alg _ _ _ _ _ _ _ _).trans ?_
      have e1 : |fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ)) - fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ))| ≤
          ‖fderiv ℝ μ₁ x - fderiv ℝ μ₂ x‖ := by
        have := sa12x3n_fderiv_e (μ := fun _ => (0 : ℝ)) x j
        have h := (fderiv ℝ μ₁ x - fderiv ℝ μ₂ x).le_opNorm (EuclideanSpace.single j (1 : ℝ))
        simpa [PiLp.norm_single, Real.norm_eq_abs] using h
      have e2 := sa12x3n_fderiv_e (μ := μ₂) x j
      have hq0 : 0 ≤ Kq1 * B / L := by positivity
      nlinarith [mul_le_mul e1 (hc1 i) (abs_nonneg _) (norm_nonneg _),
        mul_le_mul e2 (hd1' i) (abs_nonneg _) (norm_nonneg _),
        mul_le_mul_of_nonneg_left (hc2 i j) (abs_nonneg (μ₁ x - μ₂ x)),
        mul_le_mul_of_nonneg_left (hd2' i j) (abs_nonneg (μ₂ x))]
    have hSum : ∀ T : ℝ, ∑ i : Fin d, ∑ j : Fin d, |M j i| * T = Ms * T := fun T => by
      rw [hMs, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    calc _ ≤ ∑ i : Fin d, |∑ j : Fin d, M j i * ((fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ)) *
            HRS.Whole.convFun γ (D1 i ψ) x + μ₁ x * HRS.Whole.convFun γ (D1 j (D1 i ψ)) x) -
          (fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ)) * HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) x +
            μ₂ x * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) x))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |M j i| * ((Kc1 * B) * (‖fderiv ℝ μ₁ x - fderiv ℝ μ₂ x‖ + |μ₁ x - μ₂ x|) +
          (Kq1 * B / L) * (‖fderiv ℝ μ₂ x‖ + |μ₂ x|)) := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hT i j) (abs_nonneg _)
      _ = Ms * (Kc1 * B) * (‖fderiv ℝ μ₁ x - fderiv ℝ μ₂ x‖ + |μ₁ x - μ₂ x|) +
          Ms * (Kq1 * B) / L * (‖fderiv ℝ μ₂ x‖ + |μ₂ x|) := by
          rw [hSum]
          ring

end HRS.MH.AdjointRd.Phase2SA12Construction
