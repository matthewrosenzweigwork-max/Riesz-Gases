import HRS.MS.S21T4ProdBJ
import HRS.MS.R2ChaosAux56

/-!
Finite linearity of actual Wick limits on an arbitrary common probability
space. Only measurable L2 kernels are required; no pointwise integrable-row
hypothesis is introduced. The finite sections and L2-sum convergence are
the accepted S13 results, and the kernel coefficient identity uses the
accepted product-integral representation.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2Chaos HRS.MS.R26T3

variable {d : ℕ} {mu : Measure (Euc d)} [IsProbabilityMeasure mu]

theorem wick_coeff_family_linear_L2 {m : ℕ}
    (basis : ℕ → Euc d → ℝ) (hbasis : ∀ i, IsR2Test (basis i))
    (k : Fin m → Euc d → Euc d → ℝ)
    (hkm : ∀ j, Measurable (fun xy : Euc d × Euc d => k j xy.1 xy.2))
    (hk2 : ∀ j, MemLp (fun xy : Euc d × Euc d => k j xy.1 xy.2) 2 (mu.prod mu))
    (c : Fin m → ℝ) (i j : ℕ) :
    r2WickCoeff mu basis (fun x y => ∑ l, c l * k l x y) i j =
      ∑ l : Fin m, c l * r2WickCoeff mu basis (k l) i j := by
  let g : Euc d × Euc d → ℝ := s94E2 mu basis (i,j)
  obtain ⟨C, hC⟩ := s94E2_bounded (μ := mu) hbasis (i,j)
  have hgi : ∀ l : Fin m, Integrable
      (fun xy : Euc d × Euc d => c l * (k l xy.1 xy.2 * g xy)) (mu.prod mu) :=
    fun l => (s94_integrable_k_mul mu (hk2 l)
      (s94E2_measurable hbasis (i,j)) hC).const_mul _
  have hsm : Measurable (fun xy : Euc d × Euc d => ∑ l, c l * k l xy.1 xy.2) :=
    Finset.measurable_sum _ fun l _ => measurable_const.mul (hkm l)
  have hs2 : MemLp (fun xy : Euc d × Euc d => ∑ l, c l * k l xy.1 xy.2)
      2 (mu.prod mu) := memLp_finsetSum _ fun l _ => (hk2 l).const_mul (c l)
  rw [s94_coeff_eq_prod hbasis hsm hs2]
  change (∫ xy, (∑ l : Fin m, c l * k l xy.1 xy.2) * g xy ∂mu.prod mu) = _
  have he : ∀ xy : Euc d × Euc d,
      (∑ l : Fin m, c l * k l xy.1 xy.2) * g xy =
        ∑ l : Fin m, c l * (k l xy.1 xy.2 * g xy) := by
    intro xy
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [he]
  rw [integral_finset_sum _ fun l _ => hgi l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, s94_coeff_eq_prod hbasis (hkm l) (hk2 l)]

/-- The actual finite combination is the Wick chaos of the corresponding
finite kernel combination on the same probability space. -/
theorem wick_family_linear_L2 {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] {z : ℕ → Omega → ℝ} {L : ℝ}
    (hz : S94GSeq P z L) (basis : ℕ → Euc d → ℝ)
    (hbasis : ∀ i, IsR2Test (basis i)) {m : ℕ}
    (k : Fin m → Euc d → Euc d → ℝ)
    (hkm : ∀ j, Measurable (fun xy : Euc d × Euc d => k j xy.1 xy.2))
    (hk2 : ∀ j, MemLp (fun xy : Euc d × Euc d => k j xy.1 xy.2) 2 (mu.prod mu))
    (c : Fin m → ℝ) (Q : Fin m → Omega → ℝ)
    (hQ : ∀ j, IsR2WickChaos P mu basis z (k j) (Q j)) :
    IsR2WickChaos P mu basis z (fun x y => ∑ j, c j * k j x y)
      (fun w => ∑ j : Fin m, c j * Q j w) := by
  let A : Fin m → ℕ → ℕ → ℝ := fun j i l => r2WickCoeff mu basis (k j) i l
  have hm : ∀ j : Fin m, ∀ n, AEStronglyMeasurable
      (fun w => c j * s94Sec P z (A j) n w) P :=
    fun j n => ((s94_sec_memLp hz (A j) n).const_mul (c j)).aestronglyMeasurable
  have hlim : ∀ j : Fin m, TendstoL2 P
      (fun n w => c j * s94Sec P z (A j) n w) (fun w => c j * Q j w) :=
    fun j => s21t4_tendstoL2_const_mul
      (fun n => (s94_sec_memLp hz (A j) n).aestronglyMeasurable) (hQ j) (c j)
  have hsum := s21t4_tendstoL2_finset_sum Finset.univ
    (fun j _ => hm j) (fun j _ => hlim j)
  have hcoeff : (fun i l => r2WickCoeff mu basis
      (fun x y => ∑ j : Fin m, c j * k j x y) i l) =
        fun i l => ∑ j : Fin m, c j * A j i l := by
    funext i l
    exact wick_coeff_family_linear_L2 basis hbasis k hkm hk2 c i l
  change TendstoL2 P (fun n w => s94Sec P z
    (fun i l => r2WickCoeff mu basis (fun x y => ∑ j : Fin m, c j * k j x y) i l) n w)
    (fun w => ∑ j : Fin m, c j * Q j w)
  rw [hcoeff]
  simpa only [s21t4_wick_section_family_linear] using hsum

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.wick_coeff_family_linear_L2
#print axioms HRS.MS.ProClosureS111.wick_family_linear_L2
