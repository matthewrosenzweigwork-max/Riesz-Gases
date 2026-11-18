import HRS.MC.S7S7bAux11
import HRS.MC.S7S7cAux1
import HRS.MC.S7S7cAux7
import HRS.MC.SEdgeB5a
import HRS.Energy.StaticLimitTiltedGauss

/-!
# Packet `s7_FC_D3`, sub-statement L4: mean shift `η_N - ζ_N`

For every configuration `X`, `η_N(X) - ζ_N(X)` is a deterministic shift of size `O(N^{-1/2})`: its coordinates
are `√N ⟨k⟩^{-r} (E_Q μ_N(e_k) - μ(e_k))`, bounded by the uniform mean bias `s7b_bias_uniform` (`|E_Q μ_N(w) - μ(w)| ≤ C T/N`),
and `∑_k ⟨k⟩^{-2r} < ∞`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCD3

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ}

/-- Coordinates of a difference in `E_m` (helper). -/
theorem d3a_coord_sub {m : ℝ} (F G : NegSobolev d m) (l : NonzeroLattice d) :
    NegSobolev.coord (F - G) l = NegSobolev.coord F l - NegSobolev.coord G l := by
  have h := congrFun (lp.coeFn_sub (E := fun _ : NonzeroLattice d => ℝ) (p := 2)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2) (G : lp (fun _ : NonzeroLattice d => ℝ) 2)) l
  rw [Pi.sub_apply] at h
  exact h

/-- Coordinates of `η_N(X) - ζ_N(X)` (with `ζ_N` centred at the mean of the law `P`). -/
theorem d3a_coord_diff {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : (d : ℝ) < 2 * r) (P : Measure (Config d N))
    [IsProbabilityMeasure P] {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (X : Config d N)
    (k : NonzeroLattice d) :
    NegSobolev.coord (etaE r X μ - zetaE r P X) k =
      Real.sqrt N * (Lattice.jp k.1 ^ (-r) *
        (∫ Y, pair (empirical Y) (Torus.realMode k) ∂P - pair μ (Torus.realMode k))) := by
  haveI := empirical_isProbabilityMeasure (by omega : 0 < N) X
  haveI := isProbabilityMeasure_meanEmpirical P hN
  have hA : NegSobolev.coord (etaE r X μ) k = Real.sqrt N *
      (Lattice.jp k.1 ^ (-r) * (Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff μ k)) := by
    unfold etaE flucE
    rw [NegSobolev.coord_smul', coord_ofMeasureDiff hr]
  have hB : NegSobolev.coord (zetaE r P X) k = Real.sqrt N *
      (Lattice.jp k.1 ^ (-r) * (Torus.measureRealCoeff (empirical X) k -
        Torus.measureRealCoeff (meanEmpirical P) k)) := by
    unfold zetaE
    rw [NegSobolev.coord_smul', coord_ofMeasureDiff hr]
  have hM : Torus.measureRealCoeff (meanEmpirical P) k =
      ∫ Y, pair (empirical Y) (Torus.realMode k) ∂P := by
    unfold Torus.measureRealCoeff
    exact HRS.MC.Sec7.S7c.s7c_meanEmp_integral hN P (continuous_realMode' k)
  rw [d3a_coord_sub, hA, hB, hM]
  unfold Torus.measureRealCoeff pair
  ring

/-- **L4** mean shift: `‖η_N(X) - ζ_N(X)‖_{E_r} ≤ C / √N` for every configuration `X`, uniformly in `N ≥ 1`. -/
theorem d3_eta_sub_zeta (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : Config d N,
      ‖etaE r X (withDensityReal ρ) - zetaE r (sed_Q d s N γ ρ) X‖ ≤ C / Real.sqrt N := by
  obtain ⟨B, hB0, hB⟩ := HRS.MC.Sec7.S7b.s7b_bias_uniform hd hs0 hs hγ hρ
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  have hr2 : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hsumm : Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * r))) :=
    summable_jp_rpow r hr2
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = B * Real.sqrt 2 := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; exact mul_nonneg hB0 (Real.sqrt_nonneg _)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r)) := ⟨_, rfl⟩
  refine ⟨Real.sqrt (e ^ 2 * S), Real.sqrt_nonneg _, fun N hN X => ?_⟩
  haveI : IsProbabilityMeasure (sed_Q d s N γ ρ) := HRS.MC.SEdge.B5a.b5a_Q_prob hd hs0 hs hγ hρ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  -- coordinate-wise bound: coord_k(η - ζ)^2 * N ≤ ⟨k⟩^{-2r} e^2
  have hcoordbd : ∀ k : NonzeroLattice d,
      NegSobolev.coord (etaE r X (withDensityReal ρ) - zetaE r (sed_Q d s N γ ρ) X) k ^ 2 * N ≤
        Lattice.jp k.1 ^ (-(2 * r)) * e ^ 2 := by
    intro k
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∫ Y, pair (empirical Y) (Torus.realMode k) ∂(sed_Q d s N γ ρ) -
        pair (withDensityReal ρ) (Torus.realMode k) := ⟨_, rfl⟩
    have hDb : |D| ≤ e / N := by
      have h1 := hB (Torus.realMode k) (Real.sqrt 2) (HRS.StaticLimitAux.isSmooth_realMode' k)
        (fun x => Torus.abs_realMode_le k x) N hN
      rw [hD]
      exact h1.trans_eq (by rw [he])
    have hcoord := d3a_coord_diff hN hr2 (sed_Q d s N γ ρ) X k (μ := withDensityReal ρ)
    rw [hcoord, ← hD]
    have hD2 : D ^ 2 ≤ (e / N) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hDb 2
    have hj := Real.rpow_nonneg (Torus.jp_pos k.1).le (-r)
    have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
    have hsq : Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ (-r) = Lattice.jp k.1 ^ (-(2 * r)) := by
      rw [← Real.rpow_add (Torus.jp_pos k.1)]
      congr 1
      ring
    have hsq2 : (Real.sqrt N * (Lattice.jp k.1 ^ (-r) * D)) ^ 2 =
        (N : ℝ) * ((Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ (-r)) * D ^ 2) := by
      rw [mul_pow, mul_pow, hsqN]
      ring
    calc (Real.sqrt N * (Lattice.jp k.1 ^ (-r) * D)) ^ 2 * N
        = (N : ℝ) ^ 2 * ((Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ (-r)) * D ^ 2) := by
          rw [hsq2]; ring
      _ ≤ (N : ℝ) ^ 2 * ((Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ (-r)) * (e / N) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD2 (mul_nonneg hj hj)) (sq_nonneg _)
      _ = Lattice.jp k.1 ^ (-(2 * r)) * e ^ 2 := by
          rw [hsq]
          field_simp
  -- summing over `k` (Parseval for the norm)
  have hnorm : ‖etaE r X (withDensityReal ρ) - zetaE r (sed_Q d s N γ ρ) X‖ ^ 2 * N ≤ e ^ 2 * S := by
    obtain ⟨hs2, hn⟩ :=
      NegSobolev.coord_sq (etaE r X (withDensityReal ρ) - zetaE r (sed_Q d s N γ ρ) X)
    rw [hn]
    calc (∑' k : NonzeroLattice d, NegSobolev.coord (etaE r X (withDensityReal ρ) -
            zetaE r (sed_Q d s N γ ρ) X) k ^ 2) * N
        = ∑' k : NonzeroLattice d, NegSobolev.coord (etaE r X (withDensityReal ρ) -
            zetaE r (sed_Q d s N γ ρ) X) k ^ 2 * N := (tsum_mul_right).symm
      _ ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r)) * e ^ 2 :=
          Summable.tsum_le_tsum (fun k => hcoordbd k) (hs2.mul_right _) (hsumm.mul_right _)
      _ = e ^ 2 * S := by rw [tsum_mul_right, hS]; ring
  -- conclude
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  rw [le_div_iff₀ hsN]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  exact hnorm

end HRS.MC.Sec7.FCD3
