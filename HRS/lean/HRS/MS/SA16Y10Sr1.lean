import HRS.MS.SA16Y10Fd2
import HRS.MS.SA16Y9En3
import HRS.MS.SA16V2Calc

/-!
# S.A.16 (SA16Y10) Sr1: the source bound for the difference of two approximants (stability G3(d))

`sa16y10_src_bound`: for `A1, A2 : SA16Approx` with `‖(T0¹-T0²) ∘ ι²‖ ≤ KT δ`, `‖B_{bc¹} - B_{bc²}‖ ≤ Kb δ`, `|ν¹-ν²| ≤ ν'`
and `‖u²_n(τ)‖_{W^{m+2}} ≤ U`:
`jetEnergy(sa16y9_src A1 A2 n τ)^{1/p} ≤ Cs ((ν' + (Kb + KT) δ) U)`, `Cs` depending only on `d, m, p`.
This is the hypothesis `hS` of `sa16y9_mild_diff_sub`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y10_energy_le_norm (m : ℕ) :
    ∃ Cj : ℝ, 0 < Cj ∧ ∀ G : WmpSpace d m p, jetEnergy d m p G ^ (1 / p) ≤ Cj * ‖G‖ := by
  have hp0 : 0 < p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  obtain ⟨-, ⟨C, hC0, hC⟩, hpow, -⟩ := closed_jet_energy_calculus d m p
  refine ⟨C, hC0, fun G => ?_⟩
  have h1 : jetEnergy d m p G ^ (1 / p) = jetNorm d m p G := by
    rw [← hpow G, one_div, Real.rpow_rpow_inv (le_trans (norm_nonneg _) (hC G).1) hp0.ne']
  rw [h1]
  exact (hC G).2

theorem sa16y10_src_bound (m : ℕ) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ {t CG Bm : ℝ} (A1 A2 : SA16Approx d m p t CG Bm) (n : ℕ) {δ ν' KT Kb U : ℝ}
      (hδ : 0 ≤ δ) (hν' : 0 ≤ ν') (hKT : 0 ≤ KT) (hKb : 0 ≤ Kb) (hU : 0 ≤ U),
      (∀ τ ∈ Set.Icc (0 : ℝ) t, ‖(A1.T0 n τ - A2.T0 n τ).comp (sa16sz_iota2 d m p)‖ ≤ KT * δ) →
      (∀ τ ∈ Set.Icc (0 : ℝ) t, ‖sa16so_B d (m + 1) p (A1.bc n τ) - sa16so_B d (m + 1) p (A2.bc n τ)‖ ≤ Kb * δ) →
      |A1.ν n - A2.ν n| ≤ ν' → (∀ τ ∈ Set.Icc (0 : ℝ) t, ‖A2.u n τ‖ ≤ U) →
      ∀ τ ∈ Set.Icc (0 : ℝ) t,
        jetEnergy d m p (sa16y9_src A1 A2 n τ) ^ (1 / p) ≤ Cs * ((ν' + (Kb + KT) * δ) * U) := by
  obtain ⟨Cj, hCj, hE⟩ := sa16y10_energy_le_norm (d := d) (p := p) m
  set CL : ℝ := ‖sa16so_Lap d m p‖ with hCL
  set Ci : ℝ := ‖sa16r_iota d m p‖ with hCi
  refine ⟨Cj * (CL + Ci + 1), by positivity, fun {t CG Bm} A1 A2 n {δ ν' KT Kb U} hδ hν' hKT hKb hU hT hB hν hu τ hτ => ?_⟩
  refine (hE _).trans ?_
  have hu2 := hu τ hτ
  have hCL0 : 0 ≤ CL := by rw [hCL]; exact ContinuousLinearMap.opNorm_nonneg _
  have hCi0 : 0 ≤ Ci := by rw [hCi]; exact ContinuousLinearMap.opNorm_nonneg _
  have hLap : ‖(A1.ν n - A2.ν n) • sa16so_Lap d m p (A2.u n τ)‖ ≤ ν' * (CL * U) := by
    refine (norm_smul_le (A1.ν n - A2.ν n) (sa16so_Lap d m p (A2.u n τ))).trans ?_
    refine mul_le_mul (by rwa [Real.norm_eq_abs]) ?_ (norm_nonneg (sa16so_Lap d m p (A2.u n τ))) hν'
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hu2 hCL0)
  have hBop : ‖sa16r_iota d m p (sa16so_B d (m + 1) p (A1.bc n τ) (A2.u n τ) -
      sa16so_B d (m + 1) p (A2.bc n τ) (A2.u n τ))‖ ≤ Ci * (Kb * δ * U) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCi0
    have e : sa16so_B d (m + 1) p (A1.bc n τ) (A2.u n τ) - sa16so_B d (m + 1) p (A2.bc n τ) (A2.u n τ) =
        (sa16so_B d (m + 1) p (A1.bc n τ) - sa16so_B d (m + 1) p (A2.bc n τ)) (A2.u n τ) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [e]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hB τ hτ) hu2 (norm_nonneg _) (by positivity))
  have hTop : ‖(A1.T0 n τ - A2.T0 n τ) (sa16sz_iota2 d m p (A2.u n τ))‖ ≤ KT * δ * U := by
    have e : (A1.T0 n τ - A2.T0 n τ) (sa16sz_iota2 d m p (A2.u n τ)) =
        ((A1.T0 n τ - A2.T0 n τ).comp (sa16sz_iota2 d m p)) (A2.u n τ) := rfl
    rw [e]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hT τ hτ) hu2 (norm_nonneg _) (by positivity))
  have hS : ‖sa16y9_src A1 A2 n τ‖ ≤ ν' * (CL * U) + Ci * (Kb * δ * U) + KT * δ * U := by
    unfold sa16y9_src
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add hLap hBop)) hTop
  refine (mul_le_mul_of_nonneg_left hS hCj.le).trans ?_
  have hX : 0 ≤ ν' * U := mul_nonneg hν' hU
  have hY : 0 ≤ Kb * δ * U := by positivity
  have hZ : 0 ≤ KT * δ * U := by positivity
  have hrhs : (ν' + (Kb + KT) * δ) * U = ν' * U + Kb * δ * U + KT * δ * U := by ring
  rw [hrhs]
  have : ν' * (CL * U) + Ci * (Kb * δ * U) + KT * δ * U ≤ (CL + Ci + 1) * (ν' * U + Kb * δ * U + KT * δ * U) := by
    nlinarith [mul_nonneg hCL0 hX, mul_nonneg hCL0 hY, mul_nonneg hCL0 hZ, mul_nonneg hCi0 hX, mul_nonneg hCi0 hY,
      mul_nonneg hCi0 hZ]
  calc Cj * (ν' * (CL * U) + Ci * (Kb * δ * U) + KT * δ * U) ≤ Cj * ((CL + Ci + 1) * (ν' * U + Kb * δ * U + KT * δ * U)) :=
        mul_le_mul_of_nonneg_left this hCj.le
    _ = Cj * (CL + Ci + 1) * (ν' * U + Kb * δ * U + KT * δ * U) := by ring

end HRS.Whole.AppendixA.Phase2SA16R

end
