import HRS.MS.R2ChaosAux8

/-!
# HRS.MS.R2ChaosAux9 -- identification of the Wick chaos of finite-rank kernels with the explicit polynomial in `ξ`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Setting3

variable {s T b p K : ℝ} {μ : Measure (Euc d)} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_gseq_of_setting (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) [IsProbabilityMeasure μ]
    {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean μ a x) ^ 2 ∂μ)
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    S94GSeq P' (fun i ζ => r2PathEval T (ξ (a i) ζ) t) Λ := fun n =>
  ⟨s94_gfam_of_setting hset (a := fun i : Fin n => a i) (fun i => ha i) ht,
    fun α => s94_q_le hset hcov hΛ0 (a := fun i : Fin n => a i) (fun i => ha i)
      (fun i j => by simpa [Fin.ext_iff] using hon i j) ht α⟩

/-- The joint Gaussian family `(ξ(u_α)(t))_α, (ξ(a_i)(t))_{i<n}`. -/
theorem s94_gfam_joint (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) {m n : ℕ}
    {u : Fin m → Euc d → ℝ} (hu : ∀ α, IsR2Test (u α)) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    S94GFam P' (fun (j : Fin (m + n)) ζ => r2PathEval T (ξ (Fin.append u (fun i : Fin n => a i) j) ζ) t) := by
  refine s94_gfam_of_setting hset (a := Fin.append u (fun i : Fin n => a i)) (fun j => ?_) ht
  refine Fin.addCases (fun α => ?_) (fun i => ?_) j
  · simpa using hu α
  · simpa using ha i

theorem s94_lin_joint_X {m n : ℕ} (u : Fin m → Euc d → ℝ) (a : ℕ → Euc d → ℝ) (t : ℝ) (α : Fin m) (ζ : Ω') :
    s94lin (fun (j : Fin (m + n)) ζ => r2PathEval T (ξ (Fin.append u (fun i : Fin n => a i) j) ζ) t)
      (Fin.append (Pi.single α 1) (fun _ : Fin n => (0 : ℝ))) ζ = r2PathEval T (ξ (u α) ζ) t := by
  unfold s94lin
  rw [Fin.sum_univ_add]
  simp [Pi.single_apply]

theorem s94_lin_joint_Z {m n : ℕ} (u : Fin m → Euc d → ℝ) (a : ℕ → Euc d → ℝ) (t : ℝ) (γ : Fin n → ℝ) (ζ : Ω') :
    s94lin (fun (j : Fin (m + n)) ζ => r2PathEval T (ξ (Fin.append u (fun i : Fin n => a i) j) ζ) t)
      (Fin.append (fun _ : Fin m => (0 : ℝ)) γ) ζ = ∑ i : Fin n, γ i * r2PathEval T (ξ (a i) ζ) t := by
  unfold s94lin
  rw [Fin.sum_univ_add]
  simp

end Setting3

section SecEq

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

theorem s94_sum_swap4 {n m : ℕ} (f : Fin n → Fin n → Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ α, ∑ β, f i j α β = ∑ α, ∑ β, ∑ i, ∑ j, f i j α β := by
  calc ∑ i, ∑ j, ∑ α, ∑ β, f i j α β = ∑ i, ∑ α, ∑ j, ∑ β, f i j α β :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ α, ∑ i, ∑ j, ∑ β, f i j α β := Finset.sum_comm
    _ = ∑ α, ∑ i, ∑ β, ∑ j, f i j α β :=
        Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ α, ∑ β, ∑ i, ∑ j, f i j α β := Finset.sum_congr rfl fun α _ => Finset.sum_comm

theorem s94_sec_eq_of_coeff {z : ℕ → Ω' → ℝ} (hzint : ∀ i j, Integrable (fun ζ => z i ζ * z j ζ) P')
    {m : ℕ} (c : Fin m → Fin m → ℝ) (γ : Fin m → ℕ → ℝ) (n : ℕ) (ζ : Ω') :
    s94Sec P' z (fun i j => ∑ α, ∑ β, c α β * γ α i * γ β j) n ζ =
      ∑ α, ∑ β, c α β * ((∑ i : Fin n, γ α i * z i ζ) * (∑ i : Fin n, γ β i * z i ζ) -
        ∫ ζ', (∑ i : Fin n, γ α i * z i ζ') * (∑ i : Fin n, γ β i * z i ζ') ∂P') := by
  unfold s94Sec
  rw [← s94_sum_fin_range (n := n) (fun i => ∑ j ∈ Finset.range n, (∑ α, ∑ β, c α β * γ α i * γ β j) *
    (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P'))]
  have hfin : ∀ i : Fin n, ∑ j ∈ Finset.range n, (∑ α, ∑ β, c α β * γ α i * γ β j) *
      (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P') =
      ∑ j : Fin n, (∑ α, ∑ β, c α β * γ α i * γ β j) * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P') :=
    fun i => (s94_sum_fin_range (n := n) (fun j => (∑ α, ∑ β, c α β * γ α i * γ β j) *
      (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P'))).symm
  simp_rw [hfin]
  have h1 : ∀ i j : Fin n, (∑ α, ∑ β, c α β * γ α i * γ β j) * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P') =
      ∑ α, ∑ β, c α β * ((γ α i * γ β j) * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P')) := fun i j => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun β _ => by ring
  simp_rw [h1]
  rw [s94_sum_swap4 (fun i j α β => c α β * ((γ α i * γ β j) * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P')))]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  simp_rw [← Finset.mul_sum]
  congr 1
  have e1 : (∑ i : Fin n, γ α i * z i ζ) * (∑ i : Fin n, γ β i * z i ζ) =
      ∑ i : Fin n, ∑ j : Fin n, (γ α i * γ β j) * (z i ζ * z j ζ) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∫ ζ', (∑ i : Fin n, γ α i * z i ζ') * (∑ i : Fin n, γ β i * z i ζ') ∂P' =
      ∑ i : Fin n, ∑ j : Fin n, (γ α i * γ β j) * ∫ ζ', z i ζ' * z j ζ' ∂P' := by
    have : ∀ ζ', (∑ i : Fin n, γ α i * z i ζ') * (∑ i : Fin n, γ β i * z i ζ') =
        ∑ i : Fin n, ∑ j : Fin n, (γ α i * γ β j) * (z i ζ' * z j ζ') := fun ζ' => by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    have hI : ∀ i j : Fin n, Integrable (fun ζ' => (γ α i * γ β j) * (z i ζ' * z j ζ')) P' :=
      fun i j => (hzint i j).const_mul _
    have hI2 : ∀ i : Fin n, Integrable (fun ζ' => ∑ j : Fin n, (γ α i * γ β j) * (z i ζ' * z j ζ')) P' :=
      fun i => integrable_finset_sum _ fun j _ => hI i j
    rw [integral_finset_sum _ fun i _ => hI2 i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hI i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [e1, e2]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

end SecEq

end HRS.MS.R2Chaos
