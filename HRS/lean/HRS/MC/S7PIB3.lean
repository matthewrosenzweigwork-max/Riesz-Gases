import HRS.MC.S7PIB2

/-!
# Packet piB, part 3: termwise differentiation of the Fourier series of a propagated test function

For smooth `φ`, `0 ≤ u ≤ t ≤ T` and `ψ = U^{u,t}φ` (a `C¹` function with coefficients `ψ̂_j = ∑_k φ̂_k T_{jk}`
bounded by `A ⟨j⟩^{-(N+1)}`, `N > d`): `∂_a ψ(y) = ∑_j ψ̂_j ∂_a e_j(y)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIB

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV HRS.MC.Sec7.S7PIS1

variable {d : ℕ}

/-- coefficient bound `|ψ̂_j| ≤ A C_φ ⟨j⟩^{-(N+1)}` of a propagated smooth function -/
theorem S7PIB_coeff_bound {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (N : ℕ) (hN : 1 ≤ N) (hNJ : N + 1 ≤ J)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j : NonzeroLattice d,
      |Torus.funRealCoeff (propagator D μ u t φ) j| ≤ K * Lattice.jp j.1 ^ (-((N : ℝ) + 1)) := by
  obtain ⟨AN, hAN1, hANb⟩ := S7PIDV_finBd_unif H ((N : ℝ) + 1) N hN hNJ (by linarith) le_rfl
  have hentry := S7PIS1_entry (by linarith) (hANb u t hu hut htT)
  have hξs := S7PIS1_summ_phi hφ ((N : ℝ) + 1)
  set Cφ : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ ((N : ℝ) + 1) * |Torus.funRealCoeff φ k| with hCφ
  have hCφ0 : 0 ≤ Cφ := tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _)
  refine ⟨AN * Cφ, mul_nonneg (by linarith) hCφ0, fun j => ?_⟩
  have hs := S7PIS1_hasSum H hu hut htT hφ j
  have hg : HasSum (fun k : NonzeroLattice d => AN * Lattice.jp j.1 ^ (-((N : ℝ) + 1)) *
      (Lattice.jp k.1 ^ ((N : ℝ) + 1) * |Torus.funRealCoeff φ k|))
      (AN * Lattice.jp j.1 ^ (-((N : ℝ) + 1)) * Cφ) := hξs.hasSum.mul_left _
  have key := tsum_of_norm_bounded hg
    (f := fun k : NonzeroLattice d => Torus.funRealCoeff φ k * pieT D μ u t j k) (fun k => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hentry j k
      calc |Torus.funRealCoeff φ k| * |pieT D μ u t j k|
          ≤ |Torus.funRealCoeff φ k| * (AN * (Lattice.jp j.1 ^ (-((N : ℝ) + 1)) *
              Lattice.jp k.1 ^ ((N : ℝ) + 1))) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = _ := by ring)
  rw [hs.tsum_eq, Real.norm_eq_abs] at key
  calc _ ≤ _ := key
    _ = _ := by ring

/-- termwise differentiation: `∂_a ψ(y) = ∑_j ψ̂_j ∂_a e_j(y)` -/
theorem S7PIB_partial_series {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (N : ℕ) (hN : 1 ≤ N) (hNJ : N + 1 ≤ J) (hNd : (d : ℝ) < N)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (a : Fin d) (y : Torus d) :
    Torus.partialDeriv a (propagator D μ u t φ) y =
      ∑' j, Torus.funRealCoeff (propagator D μ u t φ) j * S7PIB_dmode a j y := by
  classical
  obtain ⟨K, hK0, hKb⟩ := S7PIB_coeff_bound H N hN hNJ hu hut htT hφ
  set ψ := propagator D μ u t φ with hψ
  set c : NonzeroLattice d → ℝ := fun j => Torus.funRealCoeff ψ j with hc
  have hψ1 : Torus.IsCk 1 ψ := HRS.MC.Sec7.S7PIS3.S7PIS3_prop_isCk D μ t φ hu hut
  have hψc : Continuous ψ := Torus.continuous_of_continuous_lift (hψ1.continuous)
  -- summabilities
  have hsM : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-((N : ℝ) + 1)) :=
    S7PIB_summ_jp ((N : ℝ) + 1) (by linarith)
  have hsN : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-(N : ℝ)) :=
    S7PIB_summ_jp (N : ℝ) hNd
  have hcs : Summable fun j => |c j| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => hKb j) (hsM.mul_left K)
  have hcs1 : Summable fun j => |c j| * (2 * Real.sqrt 2 * Lattice.jp j.1) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _)
      (mul_nonneg (by positivity) (Torus.jp_pos _).le)) (fun j => ?_)
      (hsN.mul_left (K * (2 * Real.sqrt 2)))
    have hj := Torus.jp_pos j.1
    calc |c j| * (2 * Real.sqrt 2 * Lattice.jp j.1)
        ≤ (K * Lattice.jp j.1 ^ (-((N : ℝ) + 1))) * (2 * Real.sqrt 2 * Lattice.jp j.1) :=
          mul_le_mul_of_nonneg_right (hKb j) (by positivity)
      _ = K * (2 * Real.sqrt 2) * (Lattice.jp j.1 ^ (-((N : ℝ) + 1)) * Lattice.jp j.1) := by ring
      _ = K * (2 * Real.sqrt 2) * Lattice.jp j.1 ^ (-(N : ℝ)) := by
          have : Lattice.jp j.1 ^ (-((N : ℝ) + 1)) * Lattice.jp j.1 = Lattice.jp j.1 ^ (-(N : ℝ)) := by
            rw [show -(N : ℝ) = -((N : ℝ) + 1) + 1 by ring, Real.rpow_add hj, Real.rpow_one]
          rw [this]
  -- the series of the mean-zero part
  have hdiff : ∀ j : NonzeroLattice d, ∀ z : Euc d,
      HasFDerivAt (Torus.lift (Torus.realMode j)) (fderiv ℝ (Torus.lift (Torus.realMode j)) z) z := by
    intro j z
    have hs : ContDiff ℝ 1 (Torus.lift (Torus.realMode j)) := S7PIB_cd1 j
    exact ((hs.differentiable (by norm_num)) z).hasFDerivAt
  have hf : ∀ (j : NonzeroLattice d) (z : Euc d), HasFDerivAt (fun z => c j * Torus.lift (Torus.realMode j) z)
      (c j • fderiv ℝ (Torus.lift (Torus.realMode j)) z) z := fun j z => (hdiff j z).const_mul (c j)
  have hf' : ∀ (j : NonzeroLattice d) (z : Euc d), ‖c j • fderiv ℝ (Torus.lift (Torus.realMode j)) z‖ ≤
      |c j| * (2 * Real.sqrt 2 * Lattice.jp j.1) := fun j z => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (S7PIB_norm_fderiv_mode_le j z) (abs_nonneg _)
  have hf0 : Summable fun j : NonzeroLattice d => c j * Torus.lift (Torus.realMode j) 0 := by
    refine Summable.of_norm_bounded (hcs.mul_right (Real.sqrt 2)) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (Torus.abs_realMode_le j _) (abs_nonneg _)
  have hder := hasFDerivAt_tsum (𝕜 := ℝ) hcs1 hf hf' hf0
  -- the expansion of `lift ψ`
  have hfc : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖ := by
    rw [Torus.summable_lattice_iff]
    have hneg : Summable fun k : NonzeroLattice d => |c (Torus.negNZ d k)| :=
      (Torus.negNZ d).summable_iff.mpr hcs
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hcs.add hneg)
    have hint : Integrable ψ := hψc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h2 := Torus.two_mul_norm_fcoef_sq hint k
    have h3 : ‖Torus.fcoef ψ k.1‖ ^ 2 ≤ (|c k| + |c (Torus.negNZ d k)|) ^ 2 := by
      have : 2 * ‖Torus.fcoef ψ k.1‖ ^ 2 ≤ 2 * (|c k| + |c (Torus.negNZ d k)|) ^ 2 := by
        rw [h2]
        simp only [hc]
        nlinarith [sq_abs (Torus.funRealCoeff ψ k), sq_abs (Torus.funRealCoeff ψ (Torus.negNZ d k)),
          abs_nonneg (Torus.funRealCoeff ψ k), abs_nonneg (Torus.funRealCoeff ψ (Torus.negNZ d k))]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
      two_ne_zero).1 h3
  have hexp : ∀ z : Euc d, Torus.lift ψ z = Torus.mean ψ + ∑' j, c j * Torus.lift (Torus.realMode j) z := by
    intro z
    have := (Torus.hasSum_realExpansion hψc hfc (Torus.mk z)).tsum_eq
    simp only [Torus.lift, Function.comp] at this ⊢
    linarith
  have hlift : Torus.lift ψ = fun z => Torus.mean ψ + ∑' j, c j * Torus.lift (Torus.realMode j) z :=
    funext hexp
  have hderψ : HasFDerivAt (Torus.lift ψ)
      (∑' j, c j • fderiv ℝ (Torus.lift (Torus.realMode j)) (Torus.rep y)) (Torus.rep y) := by
    rw [hlift]
    exact (hder (Torus.rep y)).const_add _
  unfold Torus.partialDeriv
  rw [hderψ.fderiv]
  have hsum' : Summable fun j : NonzeroLattice d => c j • fderiv ℝ (Torus.lift (Torus.realMode j)) (Torus.rep y) :=
    Summable.of_norm_bounded hcs1 fun j => hf' j _
  rw [show (∑' j, c j • fderiv ℝ (Torus.lift (Torus.realMode j)) (Torus.rep y)) (EuclideanSpace.single a (1 : ℝ)) =
      ∑' j, (c j • fderiv ℝ (Torus.lift (Torus.realMode j)) (Torus.rep y)) (EuclideanSpace.single a (1 : ℝ)) from
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single a (1 : ℝ))).map_tsum hsum']
  refine tsum_congr fun j => ?_
  simp [S7PIB_dmode, Torus.partialDeriv, hc]

end HRS.MC.Sec7.S7PIB

end
