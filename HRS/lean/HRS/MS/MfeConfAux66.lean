import HRS.MS.MfeConfAux65

/-!
# S.B.1, packet F6 (part 27): the tilt of the regularised system is a one-body function

`sb1_Psi_onebody`: with `β = θ⁻¹`, `Ψ_s(Z) = -θ log q_s(Z) - H(Z) = ∑_i ψ_s(Z_i) + κ_s`,
`ψ_s = -(θ log ρ_s + G_s + V)`, `κ_s = θ log K_s + (N/2) c_s` (the pair terms of `q_s` and `H` cancel exactly);
`sb1_hasFDerivAt_onebody`: the gradient of a one-body function `∑_i ψ(Z_i) + κ` with `∇ψ = -u` is `sb1wOne u`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_Psi_onebody (D : Whole.WholeDyn d) (k : Euc d → ℝ) {θ : ℝ} (hθ : 0 < θ) {ρ : ℝ → Euc d → ℝ} {s : ℝ}
    (hρp : ∀ x, 0 < ρ s x) (hK : 0 < Whole.gibbsNormalizer k N θ⁻¹ (Whole.withDensityReal (ρ s)))
    (hN : 1 ≤ N) (Z : Whole.EucConfig d N) :
    sb1Psi θ (sb1Hs D k N) k θ⁻¹ ρ s Z =
      (∑ i, -(θ * Real.log (ρ s (Z i)) + sb1G k (ρ s) (Z i) + D.V (Z i))) +
        (θ * Real.log (Whole.gibbsNormalizer k N θ⁻¹ (Whole.withDensityReal (ρ s))) +
          ((N : ℝ) / 2) * sb1c k (ρ s)) := by
  set K := Whole.gibbsNormalizer k N θ⁻¹ (Whole.withDensityReal (ρ s)) with hKdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP : (∏ i, ρ s (Z i)) ≠ 0 := (Finset.prod_pos fun i _ => hρp (Z i)).ne'
  have hE : Real.exp (-θ⁻¹ * N * sb1En k (ρ s) Z) ≠ 0 := (Real.exp_pos _).ne'
  have hlog : Real.log (sb1qd k θ⁻¹ N (ρ s) Z) =
      -Real.log K + ∑ i, Real.log (ρ s (Z i)) + (-θ⁻¹ * N * sb1En k (ρ s) Z) := by
    unfold sb1qd
    rw [Real.log_mul (inv_pos.2 hK).ne' (mul_ne_zero hP hE), Real.log_inv, Real.log_mul hP hE,
      Real.log_prod (fun i _ => (hρp (Z i)).ne'), Real.log_exp]
    ring
  unfold sb1Psi sb1Hs
  rw [hlog]
  unfold sb1En p4k_pairSum
  set S1 : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, k (Z i - Z j) with hS1
  set S2 : ℝ := ∑ i, Real.log (ρ s (Z i)) with hS2
  set S3 : ℝ := ∑ i, sb1G k (ρ s) (Z i) with hS3
  set S4 : ℝ := ∑ i, D.V (Z i) with hS4
  have hsum : ∑ i, -(θ * Real.log (ρ s (Z i)) + sb1G k (ρ s) (Z i) + D.V (Z i)) = -(θ * S2) - S3 - S4 := by
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsum]
  field_simp
  ring

theorem sb1_hasFDerivAt_onebody {ψ : Euc d → ℝ} {u : Euc d → Euc d}
    (hψ : ∀ x, HasFDerivAt ψ (innerSL ℝ (-(u x))) x) (κ : ℝ) (Z : Whole.EucConfig d N) :
    HasFDerivAt (fun Z : Whole.EucConfig d N => ∑ i, ψ (Z i) + κ) (p4InnerL (sb1wOne u Z)) Z := by
  have h1 : HasFDerivAt (fun Z : Whole.EucConfig d N => ∑ i, ψ (Z i))
      (∑ i, (innerSL ℝ (-(u (Z i)))).comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin N => Euc d) i)) Z :=
    HasFDerivAt.fun_sum fun i _ => (hψ (Z i)).comp (f := fun Y : Whole.EucConfig d N => Y i) Z
      (hasFDerivAt_apply i Z)
  refine (show HasFDerivAt (fun Z : Whole.EucConfig d N => ∑ i, ψ (Z i) + κ) _ Z from h1.add_const κ).congr_fderiv ?_
  ext v
  simp [p4InnerL, sb1wOne]

end HRS.MS.MfeConf
