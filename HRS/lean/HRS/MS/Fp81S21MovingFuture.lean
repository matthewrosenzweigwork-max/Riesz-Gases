import HRS.MS.Fp81S21MovingNoiseBounds2
import HRS.MS.ProClosureS111GaussianLaw
import HRS.MS.ProClosureS111FeatureEmbedding

/-!
# S2.1(iii), SOL39 packet 3: inputs for the continuous future path constructor

For fixed `p`, `δ`, `R`, `H`, and forcing cutoff `u`, the exact hypotheses of
`gaussian_paths_of_linear_features` are:

* a real Hilbert space `E` with `HilbertBasis ℕ ℝ E`;
* `G : Fin 2 → ℝ → oscSub d m →ₗ[ℝ] E`;
* for each side and admissible terminal time, some `B ≥ 0` such that
  `‖G i t φ‖ ≤ B * oscNorm m (φ : Euc d → ℝ)` for every oscillator test;
* summability of `‖G i t (initialTestBasis m α)‖ ^ 2` over all Hermite indices;
* one `L ≥ 0` such that, for every side and pair of admissible terminal times,
  the squared coordinate increments are summable and their sum is at most
  `L * |t - v|`.

The feature space `MovingNoiseHilbert d` is the fixed Lebesgue `L²` space on
`ℝ × Euc d`. `separable_feature_embedding` supplies an isometric linear
embedding into the countable Gaussian coordinate Hilbert space, where the
constructor's required basis is `gaussianFeatureBasis`. The wR28 linearity
lemma supplies linearity of the physical map. The wR34 `movingNoiseFeature_bounds`
supplies the operator estimate in precisely the displayed `oscNorm` form, the
Hermite square summability, and the increment exponent `|t-v|` (equivalently
the constructor's `|t-s|` after renaming `v` to `s`). Its single `L` is chosen
before `u`, `s`, and `t`, so it is uniform in the forcing cutoff. Its constants
are uniform over both sides as well, since both sides below use the same map.

The physical Gram identity is
`inner (movingNoiseFeature ... ta φ) (movingNoiseFeature ... tb ψ) =
  2 * p.β⁻¹ * ∫_{Icc u (min ta tb)} ∫ ... R.ρ`.
By unfolding `r26t3_coeff`, `WholeDyn.coeff`, and `quadraticGradientDyn`, the
coefficient in `IsR2FutureGaussian` has `.ν = p.β⁻¹` and `.ρ = R.ρ`; unfolding
`r26t3_U` gives the same propagator. Thus the constructor's Gram covariance
has the required normalization, including empty intervals and endpoints.

The constructor builds a continuous modification on `OscPath`; this packet
only packages its input hypotheses. It does not assert a common field adapted
in `u`: later laws are marginal laws indexed by `(H,u)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology
open Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.ProClosureS111

noncomputable def fp81s21_movingFutureEmbedding (d : ℕ) :
    MovingNoiseHilbert d →ₗᵢ[ℝ] GaussianFeatureHilbert :=
  Classical.choice (separable_feature_embedding (E := MovingNoiseHilbert d))

private theorem fp81s21_movingFutureFeature_zero
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H) :
    movingNoiseFeature R u t (fun _ => 0) = 0 := by
  classical
  have hz : IsOscTest (wholeSpaceIndex p.d : ℝ) (fun _ : Euc p.d => (0 : ℝ)) :=
    (0 : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)).property
  have h00 := fp81s21_movingNoiseFeature_add_smul p R hδ hδhalf hH hu ht
    hz hz (1 : ℝ)
  have hc : movingNoiseFeature R u t (fun _ : Euc p.d => (0 : ℝ)) +
      (0 : MovingNoiseHilbert p.d) = movingNoiseFeature R u t (fun _ : Euc p.d => (0 : ℝ)) +
        movingNoiseFeature R u t (fun _ : Euc p.d => (0 : ℝ)) := by
    simpa using h00
  have hzero : (0 : MovingNoiseHilbert p.d) =
      movingNoiseFeature R u t (fun _ : Euc p.d => (0 : ℝ)) :=
    add_left_cancel hc
  exact hzero.symm

def fp81s21_movingFutureFeatureMap
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    (u t : ℝ) (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H) :
    HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ) →ₗ[ℝ]
      GaussianFeatureHilbert where
  toFun := fun φ =>
    fp81s21_movingFutureEmbedding p.d
      (movingNoiseFeature R u t (φ : Euc p.d → ℝ))
  map_add' := by
    intro φ ψ
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) (φ : Euc p.d → ℝ) := φ.property
    have hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) (ψ : Euc p.d → ℝ) := ψ.property
    have h := fp81s21_movingNoiseFeature_add_smul p R hδ hδhalf hH hu ht hφ hψ 1
    change fp81s21_movingFutureEmbedding p.d
        (movingNoiseFeature R u t (fun x => (φ : Euc p.d → ℝ) x + (ψ : Euc p.d → ℝ) x)) = _
    simpa using congrArg (fp81s21_movingFutureEmbedding p.d) h
  map_smul' := by
    intro c φ
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) (φ : Euc p.d → ℝ) := φ.property
    have hzero : IsOscTest (wholeSpaceIndex p.d : ℝ) (fun _ : Euc p.d => (0 : ℝ)) :=
      (0 : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)).property
    have h := fp81s21_movingNoiseFeature_add_smul p R hδ hδhalf hH hu ht
      hzero hφ c
    have hz := fp81s21_movingFutureFeature_zero p R hδ hδhalf hH hu ht
    have h' : movingNoiseFeature R u t (fun x => c * (φ : Euc p.d → ℝ) x) =
        movingNoiseFeature R u t (fun _ => (0 : ℝ)) +
          c • movingNoiseFeature R u t (φ : Euc p.d → ℝ) := by
      simpa only [zero_add] using h
    have h'' := congrArg (fp81s21_movingFutureEmbedding p.d) h'
    change fp81s21_movingFutureEmbedding p.d
        (movingNoiseFeature R u t (fun x => c * (φ : Euc p.d → ℝ) x)) = _
    rw [h'', hz]
    simp

private def fp81s21_movingFutureFeatureFamily
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) H) :
    Fin 2 → ℝ → HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ) →ₗ[ℝ]
      GaussianFeatureHilbert := by
  classical
  exact fun _ t => if ht : t ∈ Icc (0 : ℝ) H then
    fp81s21_movingFutureFeatureMap p R hδ hδhalf hH u t hu ht else 0

theorem fp81s21_movingFuture_constructor_inputs (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ H : ℝ, 0 < H → ∀ u ∈ Icc (0 : ℝ) H,
          ∃ G : Fin 2 → ℝ →
              HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ) →ₗ[ℝ]
                GaussianFeatureHilbert,
            (∀ i, ∀ t ∈ Icc (0 : ℝ) H,
              ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : HRS.MS.S111X1.oscSub p.d
                  (wholeSpaceIndex p.d : ℝ),
                ‖G i t φ‖ ≤ B * oscNorm (wholeSpaceIndex p.d : ℝ)
                  (φ : Euc p.d → ℝ)) ∧
            (∀ i, ∀ t ∈ Icc (0 : ℝ) H,
              Summable (fun α : MultiIndex p.d =>
                ‖G i t (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2)) ∧
            (∃ L : ℝ, 0 ≤ L ∧ ∀ i, ∀ t v : ℝ,
              t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
              Summable (fun α : MultiIndex p.d =>
                ‖G i t (initialTestBasis (wholeSpaceIndex p.d : ℝ) α) -
                  G i v (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ∧
              (∑' α : MultiIndex p.d,
                ‖G i t (initialTestBasis (wholeSpaceIndex p.d : ℝ) α) -
                  G i v (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ≤
                L * |t - v|) ∧
            (∀ i j, ∀ t v : ℝ, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
              ∀ φ ψ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ),
                inner ℝ (G i t φ) (G j v ψ) =
                  inner ℝ (movingNoiseFeature R u t (φ : Euc p.d → ℝ))
                    (movingNoiseFeature R u v (ψ : Euc p.d → ℝ))) := by
  obtain ⟨δ0, hδ0, hδ0half, hbounds⟩ := movingNoiseFeature_bounds p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R H hH u hu
  obtain ⟨hop, hsum, ⟨L, hL, hinc⟩⟩ := hbounds δ hδ hδle R H hH
  let J := fp81s21_movingFutureEmbedding p.d
  let G := fp81s21_movingFutureFeatureFamily p R hδ (hδle.trans hδ0half) hH u hu
  have hGapply : ∀ (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H)
      (φ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)),
      G i t φ = J (movingNoiseFeature R u t (φ : Euc p.d → ℝ)) := by
    intro i t ht φ
    simp [G, fp81s21_movingFutureFeatureFamily,
      fp81s21_movingFutureFeatureMap, J, ht]
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro i t ht
    obtain ⟨B, hB, hBbound⟩ := hop u hu t ht
    refine ⟨B, hB, ?_⟩
    intro φ
    rw [hGapply i t ht φ, J.norm_map]
    exact hBbound (φ : Euc p.d → ℝ) φ.property
  · intro i t ht
    have hs := hsum u hu t ht
    simpa only [hGapply i t ht, J.norm_map,
      initialTestBasis, movingNoiseCoordinate] using hs
  · refine ⟨L, hL, ?_⟩
    intro i t v ht hv
    obtain ⟨hsummable, hsumle⟩ := hinc u hu v hv t ht
    refine ⟨?_, ?_⟩
    · simpa only [hGapply i t ht, hGapply i v hv, ← J.map_sub,
        J.norm_map, initialTestBasis, movingNoiseCoordinate] using hsummable
    · simpa only [hGapply i t ht, hGapply i v hv, ← J.map_sub,
        J.norm_map, initialTestBasis, movingNoiseCoordinate] using hsumle
  · intro i j t v ht hv φ ψ
    rw [hGapply i t ht φ, hGapply j v hv ψ]
    exact J.inner_map_map _ _

#print axioms fp81s21_movingFutureEmbedding
#print axioms fp81s21_movingFutureFeatureMap
#print axioms fp81s21_movingFuture_constructor_inputs

end HRS.Fp81.S21

end
