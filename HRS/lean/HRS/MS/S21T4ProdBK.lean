import HRS.MS.S21T4ProdBJ
import HRS.MS.S21T4ProdBG

/-!
# R26-T3.S13: linearity of the common-space singular Wick limit

The almost-sure limit of a finite linear combination of L² symmetric kernels
is the corresponding linear combination of Wick limits on the SAME canonical
ProductGaussian space. This is the identification needed by Cramér-Wold.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_product_wick_family_linear
    (I : ProductGaussian μ) (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB μ a) {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, S94KOK μ (h k)) (α : Fin m → ℝ)
    (Q : Fin m → I.Ω → ℝ)
    (hQ : ∀ k, IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (h k) (Q k))
    (R : I.Ω → ℝ)
    (hR : IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (fun x y => ∑ k, α k * h k x y) R) :
    R =ᵐ[I.P] (fun ω => ∑ k : Fin m, α k * Q k ω) := by
  letI := I.mΩ
  letI := I.prob
  let z : ℕ → I.Ω → ℝ := fun i => I.η (a i)
  let A : Fin m → ℕ → ℕ → ℝ := fun k i j => r2WickCoeff μ a (h k) i j
  have hz : S94GSeq I.P z 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  have hm : ∀ k : Fin m, ∀ n, AEStronglyMeasurable
      (fun ω => α k * s94Sec I.P z (A k) n ω) I.P :=
    fun k n => ((s94_sec_memLp hz (A k) n).const_mul (α k)).aestronglyMeasurable
  have hlim : ∀ k : Fin m, TendstoL2 I.P
      (fun n ω => α k * s94Sec I.P z (A k) n ω)
      (fun ω => α k * Q k ω) := by
    intro k
    exact s21t4_tendstoL2_const_mul
      (fun n => (s94_sec_memLp hz (A k) n).aestronglyMeasurable)
      (hQ k) (α k)
  have hsum : TendstoL2 I.P
      (fun n ω => ∑ k : Fin m, α k * s94Sec I.P z (A k) n ω)
      (fun ω => ∑ k : Fin m, α k * Q k ω) :=
    s21t4_tendstoL2_finset_sum Finset.univ (fun k _ => hm k)
      (fun k _ => hlim k)
  have hcoeff : (fun i j => r2WickCoeff μ a
      (fun x y => ∑ k : Fin m, α k * h k x y) i j) =
      (fun i j => ∑ k : Fin m, α k * A k i j) := by
    funext i j
    exact s21t4_wick_coeff_family_linear a ha.1 h hh α i j
  have hsections : (fun n ω => s94Sec I.P z
      (fun i j => r2WickCoeff μ a
        (fun x y => ∑ k : Fin m, α k * h k x y) i j) n ω) =
      (fun n ω => ∑ k : Fin m, α k * s94Sec I.P z (A k) n ω) := by
    funext n ω
    rw [hcoeff]
    exact s21t4_wick_section_family_linear I.P z A α n ω
  change TendstoL2 I.P (fun n ω => s94Sec I.P z
      (fun i j => r2WickCoeff μ a
        (fun x y => ∑ k : Fin m, α k * h k x y) i j) n ω) R at hR
  rw [hsections] at hR
  have hmSum : ∀ n, AEStronglyMeasurable
      (fun ω => ∑ k : Fin m, α k * s94Sec I.P z (A k) n ω) I.P :=
    fun n => Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun k _ => hm k n)
  exact TendstoL2.ae_unique hmSum hR hsum

end HRS.MS.R26T3
