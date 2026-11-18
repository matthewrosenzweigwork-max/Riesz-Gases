import HRS.MS.R2WinOrbNLAux10
import HRS.MS.WhoAux5

/-!
# S10.3 (nonlinear branch), part 11: the force of a decaying density as a `Sy` function, and the generator on `Sy`

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103n_force_sy`: if `h` satisfies the weighted decay `U2Dec (k+1) L A h` with `L > d+k+s+3` then every coordinate of the cancellation force
  `∇g*h` lies in `Sy k (C A)` with `C = C(d,s,k,L)` (`ult_core`, S5.1 kernel calculus).
* `s103n_Lt_bd`: for a density `h` with `U2Dec (N+1) L Ah h` and `g ∈ Sy (N+2) A`, the generator `L_h g = νΔg - (a x + ∇g*h)·∇g + J(h)g`
  of the frozen coefficient lies in `Bd N ((C₀ + C₁ Ah) A)`; `C₀, C₁` depend on `(d,s,a,β,N,L)` only.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc HRS.MS.Ul HRS.MS.Who

variable {d : ℕ}

theorem s103n_force_sy {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) {L : ℝ}
    (hL : (d : ℝ) + k + s + 3 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (h : Euc d → ℝ), 0 ≤ A → U2Dec (k + 1) L A h →
      ∀ i : Fin d, Sy k (C * A) (fun x => movForce d s h x i) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  choose Ci hCi0 hCi using fun i : Fin d => ult_core (by omega : 1 ≤ d) (ult_ker_kap hs0 hsd i) k hL
  refine ⟨∑ i, Ci i, Finset.sum_nonneg fun i _ => hCi0 i, fun A h hA hdec i => ?_⟩
  have hfun : (fun x => movForce d s h x i) = ultK (u2_kap d s i) h := by
    funext x
    exact (ult_conv_comp (by omega : 1 ≤ d) hs0 hsd hdL hA (ult_U2Dec_mono hdec (by omega : 1 ≤ k + 1)) x).2 i
  rw [hfun]
  obtain ⟨hcd, hb⟩ := hCi i A h hA hdec
  refine ⟨hcd, fun j hj x => (hb j hj x).trans ?_⟩
  have hle : Ci i ≤ ∑ i, Ci i := Finset.single_le_sum (f := Ci) (fun i _ => hCi0 i) (Finset.mem_univ i)
  have hw : (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) ≤ (1 + ‖x‖)⁻¹ := by
    rw [← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) ?_
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  calc Ci i * A * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) ≤ Ci i * A * (1 + ‖x‖)⁻¹ :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg (hCi0 i) hA)
    _ ≤ (∑ i, Ci i) * A * (1 + ‖x‖)⁻¹ := by
        have : 0 ≤ (1 + ‖x‖)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg x])
        gcongr

set_option maxHeartbeats 3200000 in
theorem s103n_Lt_bd {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (N : ℕ) {L : ℝ}
    (hL : (d : ℝ) + N + s + 3 < L) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ (Ah : ℝ) (h : Euc d → ℝ), 0 ≤ Ah → U2Dec (N + 1) L Ah h →
      ∀ (A : ℝ) (g : Euc d → ℝ), Sy (N + 2) A g →
        Bd N ((C0 + C1 * Ah) * A)
          (fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0 g x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd N hL
  refine ⟨|β⁻¹| * d + d * (|a| * (N + 1)), d * 2 ^ N * Cf + d * (Cf * 2 ^ (N + 1)), by positivity,
    by positivity, fun Ah h hAh hdec A g hg => ?_⟩
  have hA := hg.nonneg
  have hgB : Bd (N + 2) A g := hg.bd
  have hn : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hDg : ∀ i : Fin d, Bd (N + 1) A (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    have := hgB.deriv (EuclideanSpace.single i (1 : ℝ))
    rw [hn i, mul_one] at this
    exact this
  have hDgS : ∀ i : Fin d, Sy (N + 1) A (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    have := hg.deriv (EuclideanSpace.single i (1 : ℝ))
    rw [hn i, mul_one] at this
    exact this
  -- the four terms
  have T1 : Bd N (|β⁻¹| * (d * A)) (fun x => β⁻¹ * Laplacian.laplacian g x) := (Bd.lap hgB).smul β⁻¹
  have T2 : Bd N (∑ i : Fin d, |(-a)| * ((N + 1) * A))
      (fun x => ∑ i : Fin d, (-a) * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))) :=
    Bd.sum Finset.univ _ _ (fun i _ => (Sy.xmul ((hDgS i).mono_N (Nat.le_succ N)) i).smul (-a))
  have hFS : ∀ i : Fin d, Sy N (Cf * Ah) (fun x => movForce d s h x i) := fun i => hCf Ah h hAh hdec i
  have T3 : Bd N (∑ i : Fin d, |(-1 : ℝ)| * (2 ^ N * (Cf * Ah) * A))
      (fun x => ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))) :=
    Bd.sum Finset.univ _ _ (fun i _ => ((hFS i).bd.mul ((hDg i).mono_N (Nat.le_succ N))).smul (-1))
  have hhj : ∀ j : Fin d, U2Dec (N + 1) L (Ah * A * 2 ^ (N + 1))
      (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    who_u2dec_mul hdec (hDg j).1 (fun i hi y => (hDg j).2 i hi y)
  have T4 : Bd N (∑ j : Fin d, Cf * (Ah * A * 2 ^ (N + 1)))
      (fun x => ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j) :=
    Bd.sum Finset.univ _ _ (fun j _ => (hCf _ _ (by positivity) (hhj j) j).bd)
  have hsum := (T1.add (T2.add T3)).add T4
  have hfun : (fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0 g x) =
      fun x => (β⁻¹ * Laplacian.laplacian g x + (∑ i : Fin d, (-a) * (x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) + ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))))) +
        ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := by
    funext x
    rw [s67_gen_eq s a β h 0 g x, s67bd26_inner]
    have hJ : s67J d s h g x = ∑ j : Fin d, movForce d s
        (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := by
      unfold s67J
      refine Finset.sum_congr rfl fun j _ => ?_
      have hg' : (fun y => h y * gradient g y j) =
          fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) :=
        funext fun y => by rw [mov2d_grad_coord]
      show (movForce d s (fun y => h y * gradient g y j) x) j = _
      rw [hg']
    rw [hJ, ← Finset.sum_add_distrib]
    have e : ∀ i : Fin d, (-(a • x) - movForce d s h x) i * gradient g x i =
        (-a) * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) +
          (-1 : ℝ) * (movForce d s h x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
      intro i
      rw [mov2d_grad_coord]
      simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    simp only [e]
  rw [hfun]
  refine hsum.mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_one]
  nlinarith [mul_nonneg hA hAh, mul_nonneg (mul_nonneg hA hAh) hCf0]

end HRS.MS.R2WinOrbNL

end
