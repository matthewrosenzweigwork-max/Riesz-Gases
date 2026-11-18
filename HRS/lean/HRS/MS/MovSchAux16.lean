import HRS.MS.MovSchAux15

/-!
# S64 (S6.9), part 11: clause (3) of `mov_moving_reference`

Namespace `HRS.MS.MovSch`, prefix `s64_`.  `s64_ref3`: for `N ≥ 1`, `t ≥ 0` and a non-collision `X`, `q_N^t(X) > 0` and
`τ ↦ q_N^τ(X)` has derivative `movFP q_N^t X` at `t`; here `q_N^τ(X) = Qc(X - a_τ)`
(`s64_movQ_Qc`, translation covariance and the canonical form of the thermal density), `∂_t q = -β q ∑_j q ⟨x_j - a_t, q a_t⟩` and the force
terms of `movFP` cancel by antisymmetry of `∇g` (`s64_antisym`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

lemma s64_movQ_Qc {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {ρ₀ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalDensity (rieszKernel d s) (confinement q) β ρ₀) (hN : 1 ≤ N) (a₀ : Euc d) (τ : ℝ)
    (X : EucConfig d N) :
    movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ τ) X =
      s64_Qc d s q β N (fun i => X i - movShift q a₀ τ) := by
  have e : movTranslatedDensity q a₀ ρ₀ τ = fun x => ρ₀ (x - movShift q a₀ τ) := rfl
  rw [e, s64_movQ_translate hρ.1, s64_movQ_thermal hs0 hq hβ hρ hN]
  rfl

lemma s64_shift_hasDeriv (q : ℝ) (a₀ x : Euc d) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => x - movShift q a₀ τ) (q • movShift q a₀ τ) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => Real.exp (-q * τ)) (Real.exp (-q * τ) * (-q)) τ := by
    have := (hasDerivAt_id τ).const_mul (-q)
    simpa using this.exp
  have h2 := h1.smul_const a₀
  have h3 : HasDerivAt (fun τ : ℝ => x - movShift q a₀ τ) (-((Real.exp (-q * τ) * -q) • a₀)) τ := h2.const_sub x
  have e : -((Real.exp (-q * τ) * -q) • a₀) = q • movShift q a₀ τ := by
    unfold movShift
    rw [smul_smul, ← neg_smul]
    congr 1
    ring
  exact h3.congr_deriv e

lemma s64_H_translate (s q : ℝ) (X : EucConfig d N) (b : Euc d) :
    HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) (fun j => X j - b) =
      ∑ j, confinement q (X j - b) +
        (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), rieszKernel d s (X i - X j) := by
  unfold HRS.Whole.canonicalHamiltonian
  simp only [sub_sub_sub_cancel_right]

lemma s64_antisym (s : ℝ) (k : Fin d) {Z : EucConfig d N} (hZ : s64_NC Z) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Z i - Z j) k = 0 := by
  set T : Fin N → Fin N → ℝ := fun i j => rieszKernelGrad d s (Z i - Z j) k with hT
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, T i j = ∑ j, T i j - T i i := fun i =>
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  have h2 : ∀ i j : Fin N, T i j + T j i = if i = j then 2 * T i i else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp; ring
    · rw [if_neg h]
      have hne : Z i - Z j ≠ 0 := sub_ne_zero.2 (hZ i j h)
      have := s64_G_odd s k hne
      rw [neg_sub] at this
      simp only [hT]
      rw [this]; ring
  have h3 : ∑ i, ∑ j, (T i j + T j i) = 2 * ∑ i, T i i := by
    simp_rw [h2]
    simp [Finset.mul_sum]
  have h4 : ∑ i : Fin N, ∑ j : Fin N, (T i j + T j i) = 2 * ∑ i : Fin N, ∑ j : Fin N, T i j := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => T j i)]
    ring
  show ∑ i, ∑ j ∈ Finset.univ.erase i, T i j = 0
  simp_rw [h1]
  rw [Finset.sum_sub_distrib]
  linarith

lemma s64_inner_eq (x y : Euc d) : inner ℝ x y = ∑ k, y k * x k := by
  simp [PiLp.inner_apply]

lemma s64_drift_sum (s q : ℝ) {Z : EucConfig d N} (hZ : s64_NC Z) (a : Euc d) :
    ∑ i, ∑ k, a k * s64_drift d s q N i k Z = q * ∑ i, inner ℝ (Z i) a := by
  unfold s64_drift
  have e1 : ∀ i k, a k * (q * Z i k + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Z i - Z j) k) =
      q * (a k * Z i k) + (1 / (N : ℝ)) * (a k * ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Z i - Z j) k) := by
    intro i k; ring
  simp_rw [e1, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin N, ∑ k : Fin d, q * (a k * Z i k) = q * ∑ i, inner ℝ (Z i) a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [s64_inner_eq, Finset.mul_sum]
  have h2 : ∑ i : Fin N, ∑ k : Fin d, (1 / (N : ℝ)) *
      (a k * ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Z i - Z j) k) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := s64_antisym s k hZ
    rw [← Finset.mul_sum, ← Finset.mul_sum, this]
    ring
  rw [h1, h2, add_zero]

theorem s64_ref3 {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {ρ₀ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalDensity (rieszKernel d s) (confinement q) β ρ₀) (hN : 1 ≤ N) (a₀ : Euc d)
    (t : ℝ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    0 < movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ t) X ∧
      HasDerivAt (fun τ => movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ τ) X)
        (movFP d s q β N (movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ t)) X) t := by
  have hZc := s64_Zpos (d := d) hs0 hq hβ hN
  set a : Euc d := movShift q a₀ t with ha
  have hNC : s64_NC (fun j => X j - a) := by
    intro i j hij h
    exact s64_NC_of_not_mem hX i j hij (sub_left_inj.1 h)
  refine ⟨?_, ?_⟩
  · rw [s64_movQ_Qc hs0 hq hβ hρ hN a₀ t X]
    exact mul_pos (inv_pos.2 hZc) (Real.exp_pos _)
  set c : ℝ := (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), rieszKernel d s (X i - X j) with hc
  have hfun : (fun τ => movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ τ) X) =
      fun τ : ℝ => (HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β)⁻¹ *
        Real.exp (-β * (∑ j, confinement q (X j - movShift q a₀ τ) + c)) := by
    funext τ
    rw [s64_movQ_Qc hs0 hq hβ hρ hN a₀ τ X]
    unfold s64_Qc
    rw [s64_H_translate]
  rw [hfun]
  have hS : HasDerivAt (fun τ : ℝ => ∑ j, confinement q (X j - movShift q a₀ τ))
      (∑ j, q * inner ℝ (X j - a) (q • a)) t := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := (s64_shift_hasDeriv q a₀ (X j) t).norm_sq
    have h2 := (h1.const_mul q).div_const 2
    refine h2.congr_deriv ?_
    ring
  have hE := ((hS.add_const c).const_mul (-β)).exp.const_mul
    (HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β)⁻¹
  refine hE.congr_deriv ?_
  have hmovQ : movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ t) =
      fun Y => s64_Qc d s q β N (fun j => Y j - a) := by
    funext Y; exact s64_movQ_Qc hs0 hq hβ hρ hN a₀ t Y
  rw [hmovQ, s64_movFP_Qc s q β hβ.ne' a hNC]
  have hQ : s64_Qc d s q β N (fun j => X j - a) =
      (HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β)⁻¹ *
        Real.exp (-β * (∑ j, confinement q (X j - a) + c)) := by
    unfold s64_Qc
    rw [s64_H_translate]
  have hsum := s64_drift_sum s q hNC a
  have hR : ∑ i, ∑ k, (q * a k) * (-β * s64_drift d s q N i k (fun j => X j - a) *
      s64_Qc d s q β N (fun j => X j - a)) =
      (-β * s64_Qc d s q β N (fun j => X j - a) * q) *
        ∑ i, ∑ k, a k * s64_drift d s q N i k (fun j => X j - a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hR, hsum, hQ]
  have hinner : ∀ j, q * inner ℝ (X j - a) (q • a) = q * q * inner ℝ (X j - a) a := by
    intro j; rw [inner_smul_right]; ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  ring

end HRS.MS.MovSch

end
