import HRS.MS.S113EndAux18

/-!
# S11.3 endpoint (worker S11X), part 19: the fixed-time algebraic identity of the source

`s113x_alg`: at a fixed time (density `f`, field `u = movU f`, `D = div(f u)`, `Γ' = g * D`, `A' = ∫(DΓ + fΓ')`), for a collision-free `X`,
```
∑_i (div u(X_i) + ∑_k Ψ_{ik} u_k(X_i)) - (-κ' - βN(-N⁻¹∑_a Γ'(X_a) + ½A') + ∑_a D(X_a)/f(X_a)) = -βN (F^{h_u}(X) - E)
```
whenever `κ' = βN E`: the physical Fokker-Planck term minus the time derivative of `log q_N` is the centered commutator energy.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d N : ℕ}

section Alg

variable {s q β : ℝ} {f : Euc d → ℝ} {c B M : ℝ}

theorem s113x_Psi_sub (hβ : β ≠ 0) (f : Euc d → ℝ) (Y : EucConfig d N) (i : Fin N) (k : Fin d) :
    s113x_Psi d s q β N (movU d s q β f) i k Y - (gradient (fun z => Real.log (f z)) (Y i)) k =
      β * ((movForce d s f (Y i)) k - (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (rieszKernelGrad d s (Y i - Y j)) k) := by
  unfold s113x_Psi s113x_drift movU
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem s113x_D_div (S : S113XSlice f (movU d s q β f) c B M) (x : Euc d) :
    movDiv (fun y => f y • movU d s q β f y) x / f x =
      movDiv (movU d s q β f) x + ∑ k, (gradient (fun z => Real.log (f z)) x) k * (movU d s q β f x) k := by
  have hf : DifferentiableAt ℝ f x := S.cd.differentiable (by norm_num) x
  have hu : DifferentiableAt ℝ (movU d s q β f) x := S.ucd.differentiable (by norm_num) x
  have hpos := S.pos x
  rw [HRS.MS.MovForce.mv1_movDiv_smul hf hu]
  have hk : ∀ k : Fin d, fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ)) =
      f x * (gradient (fun z => Real.log (f z)) x) k := by
    intro k
    rw [movtr_gradient_apply]
    exact HRS.MS.MovForce.mv1_fderiv_rho hf hpos _
  simp only [hk]
  have hs : ∑ k, f x * (gradient (fun z => Real.log (f z)) x) k * (movU d s q β f x) k =
      f x * ∑ k, (gradient (fun z => Real.log (f z)) x) k * (movU d s q β f x) k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  field_simp

theorem s113x_alg (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : β ≠ 0)
    (S : S113XSlice f (movU d s q β f) c B M) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N)
    (hN : (N : ℝ) ≠ 0) (κ' E : ℝ) (hκ : κ' = β * N * E) :
    ∑ i, (movDiv (movU d s q β f) (X i) +
        ∑ k, s113x_Psi d s q β N (movU d s q β f) i k X * (movU d s q β f (X i)) k) -
      (-κ' - β * N * (-(1 / (N : ℝ)) * ∑ a, (∫ z, rieszKernel d s z * movDiv (fun y => f y • movU d s q β f y) (X a - z)) +
          (1 / 2) * ∫ x, (movDiv (fun y => f y • movU d s q β f y) x * (∫ z, rieszKernel d s z * f (x - z)) +
            f x * ∫ z, rieszKernel d s z * movDiv (fun y => f y • movU d s q β f y) (x - z))) +
        ∑ a, movDiv (fun y => f y • movU d s q β f y) (X a) / f (X a)) =
      -β * N * (pairEnergy (commutatorKernel d s (movU d s q β f)) X (HRS.Whole.withDensityReal f) - E) := by
  set u := movU d s q β f with hu
  set D : Euc d → ℝ := fun x => movDiv (fun y => f y • u y) x with hD
  set A' : ℝ := ∫ x, (D x * (∫ z, rieszKernel d s z * f (x - z)) + f x * ∫ z, rieszKernel d s z * D (x - z)) with hA'
  set P : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (rieszKernelGrad d s (X i - X j)) (u (X i)) with hP
  set Q1 : ℝ := ∑ i, inner ℝ (u (X i)) (movForce d s f (X i)) with hQ1
  set Q2 : ℝ := ∑ a, ∫ z, rieszKernel d s z * D (X a - z) with hQ2
  -- per-particle identity
  have hper : ∀ i, movDiv u (X i) + ∑ k, s113x_Psi d s q β N u i k X * (u (X i)) k - D (X i) / f (X i) =
      β * (inner ℝ (u (X i)) (movForce d s f (X i)) -
        (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, inner ℝ (rieszKernelGrad d s (X i - X j)) (u (X i))) := by
    intro i
    have h1 := s113x_D_div (s := s) (q := q) (β := β) S (X i)
    simp only [hD, h1]
    have h2 : ∑ k, s113x_Psi d s q β N u i k X * (u (X i)) k - ∑ k, (gradient (fun z => Real.log (f z)) (X i)) k * (u (X i)) k =
        ∑ k, β * ((movForce d s f (X i)) k - (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (rieszKernelGrad d s (X i - X j)) k) * (u (X i)) k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← sub_mul, s113x_Psi_sub hβ f X i k]
    have h3 : ∑ k, β * ((movForce d s f (X i)) k - (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (rieszKernelGrad d s (X i - X j)) k) * (u (X i)) k =
        β * (inner ℝ (u (X i)) (movForce d s f (X i)) -
          (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, inner ℝ (rieszKernelGrad d s (X i - X j)) (u (X i))) := by
      have e1 : inner ℝ (u (X i)) (movForce d s f (X i)) = ∑ k, (movForce d s f (X i)) k * (u (X i)) k := by
        simp [PiLp.inner_apply, mul_comm]
      have e2 : ∀ j, inner ℝ (rieszKernelGrad d s (X i - X j)) (u (X i)) =
          ∑ k, (u (X i)) k * (rieszKernelGrad d s (X i - X j)) k := by
        intro j; simp [PiLp.inner_apply]
      rw [e1]
      simp only [e2]
      have hk : ∀ k : Fin d, β * ((movForce d s f (X i)) k - (1 / (N : ℝ)) *
          ∑ j ∈ Finset.univ.erase i, (rieszKernelGrad d s (X i - X j)) k) * (u (X i)) k =
          β * ((movForce d s f (X i)) k * (u (X i)) k) -
            β * (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (u (X i)) k * (rieszKernelGrad d s (X i - X j)) k := by
        intro k
        rw [← Finset.mul_sum]
        ring
      simp only [hk]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm (s := Finset.univ.erase i)]
      ring
    linarith
  have hsum : ∑ i, (movDiv u (X i) + ∑ k, s113x_Psi d s q β N u i k X * (u (X i)) k) - ∑ a, D (X a) / f (X a) =
      β * (Q1 - (1 / (N : ℝ)) * P) := by
    rw [← Finset.sum_sub_distrib]
    simp only [hper]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hP2 : ∑ i, ∑ j ∈ Finset.univ.erase i, commutatorKernel d s u (X i) (X j) = 2 * P := by
    have := s113x_pair_antisym s u hX
    rw [hP]; linarith
  have hb : ∀ i, ∫ y, commutatorKernel d s u (X i) y ∂(HRS.Whole.withDensityReal f) =
      inner ℝ (u (X i)) (movForce d s f (X i)) - ∫ z, rieszKernel d s z * D (X i - z) :=
    fun i => s113x_onebody hd hs0 hsd S (X i)
  have hc : ∫ x, ∫ y, commutatorKernel d s u x y ∂(HRS.Whole.withDensityReal f) ∂(HRS.Whole.withDensityReal f) = -A' := by
    have := s113x_A_identity hd hs0 hsd S
    rw [hA']
    linarith
  have hpe : pairEnergy (commutatorKernel d s u) X (HRS.Whole.withDensityReal f) =
      1 / (2 * (N : ℝ) ^ 2) * (2 * P) - 1 / (N : ℝ) * (Q1 - Q2) + 1 / 2 * (-A') := by
    unfold pairEnergy
    rw [hP2, hc]
    congr 2
    rw [hQ1, hQ2, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hb i
  rw [hpe]
  have e1 : ∑ i, (movDiv u (X i) + ∑ k, s113x_Psi d s q β N u i k X * (u (X i)) k) -
      (-κ' - β * N * (-(1 / (N : ℝ)) * Q2 + (1 / 2) * A') + ∑ a, D (X a) / f (X a)) =
      (∑ i, (movDiv u (X i) + ∑ k, s113x_Psi d s q β N u i k X * (u (X i)) k) - ∑ a, D (X a) / f (X a)) +
        κ' + β * N * (-(1 / (N : ℝ)) * Q2 + (1 / 2) * A') := by ring
  rw [e1, hsum, hκ]
  field_simp
  ring

end Alg

end HRS.MS.S113BD

end
