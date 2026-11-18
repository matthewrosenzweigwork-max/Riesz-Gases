import Mathlib
import HRS.Torus.Sobolev
import HRS.PDE.MeanFieldDefs
import HRS.Energy.Modulated
import HRS.Equilibrium.StaticLimits

/-!
# Mean-particle packet: the observation against `ψ_k` as a Sobolev evaluation

* `mp_cosTest_eq_realMode`, `mp_integral_cosTest` : `ψ_k = √2 cos(2π k·x)` is a basis function
  `e_K` of the real basis, `K = ±k`; hence `∫ ψ_k = 0` and `funRealCoeff ψ_k = δ_K`;
* `mp_eval_cosTest_eq`, `mp_abs_eval_cosTest_le` : `F(ψ_k) = F̂(K)`, `|F(ψ_k)| ≤ ⟨k⟩^m ‖F‖`;
* `mp_linCoord_eq_eval`, `mp_linCoord_cosTest` : the linear observable
  `Z_N = √N(μ_N(ψ) - μ_0(ψ))` equals the Sobolev evaluation `(√N (μ_N - ν))(ψ)` plus the
  deterministic part `√N(ν(ψ) - μ_0(ψ))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {d : ℕ}

/-- `ψ_k = cosTest k` is a basis function `e_K` of the real orthonormal basis with `K = ±k`. -/
theorem mp_cosTest_eq_realMode (k : Lattice d) (hk : k ≠ 0) :
    ∃ K : NonzeroLattice d, (K.1 = k ∨ K.1 = -k) ∧ PDE.cosTest k = Torus.realMode K := by
  by_cases hp : Lattice.IsPosHalf k
  · refine ⟨⟨k, hk⟩, Or.inl rfl, ?_⟩
    funext x
    simp [Torus.realMode, hp, PDE.cosTest]
  · have hn : Lattice.IsPosHalf (-k) := (Torus.isPosHalf_neg k hk).mpr hp
    refine ⟨⟨-k, neg_ne_zero.mpr hk⟩, Or.inr rfl, ?_⟩
    funext x
    simp [Torus.realMode, hn, PDE.cosTest, Torus.cosMode_neg]

/-- `∫ ψ_k dx = 0` for `k ≠ 0`. -/
theorem mp_integral_cosTest (k : Lattice d) (hk : k ≠ 0) :
    ∫ x : Torus d, PDE.cosTest k x = 0 := by
  obtain ⟨K, -, hK⟩ := mp_cosTest_eq_realMode k hk
  rw [hK]
  exact Torus.integral_realMode K

/-- The real Fourier coefficients of `ψ_k` are a single Kronecker delta at `K = ±k`. -/
theorem mp_funRealCoeff_cosTest (k : Lattice d) (hk : k ≠ 0) :
    ∃ K : NonzeroLattice d, (K.1 = k ∨ K.1 = -k) ∧
      ∀ j : NonzeroLattice d, Torus.funRealCoeff (PDE.cosTest k) j = if j = K then 1 else 0 := by
  obtain ⟨K, hK1, hK⟩ := mp_cosTest_eq_realMode k hk
  refine ⟨K, hK1, fun j => ?_⟩
  unfold Torus.funRealCoeff
  rw [hK]
  exact Torus.realMode_orthonormal j K

/-- `F(ψ_k) = F̂(K)` for the basis index `K = ±k`. -/
theorem mp_eval_cosTest_eq {m : ℝ} (k : Lattice d) (hk : k ≠ 0) :
    ∃ K : NonzeroLattice d, (K.1 = k ∨ K.1 = -k) ∧
      ∀ F : NegSobolev d m, NegSobolev.eval F (PDE.cosTest k) = NegSobolev.fourierCoeff F K := by
  obtain ⟨K, hK1, hK⟩ := mp_funRealCoeff_cosTest k hk
  refine ⟨K, hK1, fun F => ?_⟩
  unfold NegSobolev.eval
  rw [tsum_eq_single K]
  · rw [hK K]; simp
  · intro j hj
    rw [hK j]; simp [hj]

/-- **Evaluation against `ψ_k` is a bounded functional on `E_m`**:
`|F(ψ_k)| ≤ ⟨k⟩^m ‖F‖` (`ψ_k` has a single nonzero Fourier coefficient). -/
theorem mp_abs_eval_cosTest_le {m : ℝ} (k : Lattice d) (hk : k ≠ 0) (F : NegSobolev d m) :
    |NegSobolev.eval F (PDE.cosTest k)| ≤ Lattice.jp k ^ m * ‖F‖ := by
  obtain ⟨K, hK1, hK⟩ := mp_eval_cosTest_eq (m := m) k hk
  rw [hK F]
  have hjp : Lattice.jp K.1 = Lattice.jp k := by
    rcases hK1 with h | h
    · rw [h]
    · rw [h, Torus.jp_neg]
  unfold NegSobolev.fourierCoeff
  rw [abs_mul, hjp, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k) m)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Torus.jp_pos k) m).le
  exact lp.norm_apply_le_norm (by norm_num) (F : lp (fun _ : NonzeroLattice d => ℝ) 2) K

/-- Evaluation is homogeneous in `F`. -/
theorem mp_eval_smul {m : ℝ} (κ : ℝ) (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (κ • F) φ = κ * NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have : NegSobolev.fourierCoeff (κ • F) k = κ * NegSobolev.fourierCoeff F k := by
    have hc : NegSobolev.coord (κ • F) k = κ * NegSobolev.coord F k := rfl
    unfold NegSobolev.fourierCoeff
    rw [hc]
    ring
  rw [this]; ring

/-- **The linear observable as a Sobolev evaluation.** For a smooth test function `ψ`, a probability
measure `ν` (the centring of the empirical error) and a reference measure `μ₀`,
`Z_N := √N (μ_N(ψ) - μ₀(ψ)) = (√N (μ_N - ν))(ψ) + √N (ν(ψ) - μ₀(ψ))`. -/
theorem mp_linCoord_eq_eval {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 0 < N)
    (μ₀ ν : Measure (Torus d)) [IsProbabilityMeasure ν] (ψ : Torus d → ℝ)
    (hψ : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (X : Config d N) :
    linCoord μ₀ ψ X = NegSobolev.eval (NegSobolev.scaledFluc m (Real.sqrt N) X ν) ψ +
      Real.sqrt N * (pair ν ψ - pair μ₀ ψ) := by
  have := empirical_isProbabilityMeasure hN X
  unfold NegSobolev.scaledFluc
  rw [mp_eval_smul, NegSobolev.eval_ofMeasureDiff hm (empirical X) ν ψ hψ, pair_empirical hN]
  unfold linCoord
  ring

/-- `ψ_k` is `C^∞` on the torus. -/
theorem mp_isCk_top_cosTest (k : Lattice d) :
    Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) (PDE.cosTest k) := by
  have e : Torus.lift (PDE.cosTest k) =
      fun y => Real.sqrt 2 * Real.cos (Torus.freqFunctional k y) := by
    funext y
    simp [PDE.cosTest, Torus.lift, Torus.cosMode_mk, Torus.freqFunctional_apply]
  unfold Torus.IsCk
  rw [e]
  exact contDiff_const.mul (Real.contDiff_cos.comp (Torus.freqFunctional k).contDiff)

/-- **The `ψ_k`-observation of the `N`-particle system, split into fluctuation and drift.**
For `k ≠ 0`, a measurable density `ρ_u ≥ 0` with `withDensityReal ρ_u` a probability measure, and
`N ≥ 1`:
`linCoord dx ψ_k X = (√N (μ_N - ρ_u dx))(ψ_k) + √N ∫ ρ_u ψ_k`
(the latter is `√N ∫ ψ_k (ρ_u - 1)` since `∫ψ_k = 0`). -/
theorem mp_linCoord_cosTest {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) (hk : k ≠ 0) (ρu : Torus d → ℝ) (hρ : Measurable ρu) (hρ0 : ∀ x, 0 ≤ ρu x)
    [IsProbabilityMeasure (withDensityReal ρu)] (X : Config d N) :
    linCoord (volume : Measure (Torus d)) (PDE.cosTest k) X =
      NegSobolev.eval (NegSobolev.scaledFluc m (Real.sqrt N) X (withDensityReal ρu))
        (PDE.cosTest k) + Real.sqrt N * ∫ x, ρu x * PDE.cosTest k x := by
  rw [mp_linCoord_eq_eval hm hN volume (withDensityReal ρu) (PDE.cosTest k)
    (mp_isCk_top_cosTest k) X]
  unfold pair
  rw [integral_withDensityReal_eq ρu hρ hρ0, mp_integral_cosTest k hk]
  ring

end HRS
