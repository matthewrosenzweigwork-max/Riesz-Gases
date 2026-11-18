import HRS.MC.S7PIS3Cov3
import HRS.MC.S7PIHC12

/-!
# Packet piF6, part A: the covariance bookkeeping for one piece between observation times

* `S7PIF6_obsCov_T`, `S7PIF6_gaussHeat_T`: `obsCov = 0` at `T`, hence `gaussHeat obsCov G T = G`;
* `S7PIF6_obsCov_psd`: `obsCov u` is positive semidefinite for `u ∈ [0,T]` (no `IsFutureGaussian` measure needed);
* `S7PIF6_c12`: the `C^{1,2}` extension of `gaussHeat obsCov G` from `[a,b]` (no observation time in `(a,b)`), with
  the time derivative given through `obsRate`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIF6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {d : ℕ}

/-- The centred Gaussian with covariance `0` is the Dirac mass at `0`. -/
theorem S7PIF6_mvG_zero {q : ℕ} :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) (0 : Matrix (Fin q) (Fin q) ℝ) = Measure.dirac 0 := by
  unfold multivariateGaussian
  have : (fun x : EuclideanSpace ℝ (Fin q) =>
      (0 : EuclideanSpace ℝ (Fin q)) + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (0 : Matrix (Fin q) (Fin q) ℝ)) x) =
      fun _ => 0 := by
    funext x
    simp
  rw [this, Measure.map_const]
  simp

/-- the covariance of the observations vanishes at `T` -/
theorem S7PIF6_obsCov_T (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) : obsCov R.D R.ρ t φ T = 0 := by
  ext i j
  simp only [obsCov, Matrix.of_apply, Matrix.zero_apply]
  have hm : min (t i) (t j) ≤ T := (min_le_left _ _).trans (ht i).2
  have h0 : volume (Set.Icc T (min (t i) (t j))) = 0 := by
    refine measure_mono_null (t := {T}) (fun v hv => ?_) (measure_singleton T)
    exact le_antisymm (hv.2.trans hm) hv.1
  rw [setIntegral_measure_zero _ h0, mul_zero]

/-- `gaussHeat obsCov G T = G` -/
theorem S7PIF6_gaussHeat_T (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (G : EuclideanSpace ℝ (Fin q) → ℝ) (c : EuclideanSpace ℝ (Fin q)) :
    gaussHeat (obsCov R.D R.ρ t φ) G T c = G c := by
  unfold gaussHeat
  rw [S7PIF6_obsCov_T R t φ ht, S7PIF6_mvG_zero, integral_dirac]
  simp

/-- `obsCov u` is the integral of the rate over `(u,T]` -/
theorem S7PIF6_obsCov_eq_int (R : Regime d) {T : ℝ} (hT : 0 < T) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (i j : Fin q) :
    obsCov R.D R.ρ t φ u i j = ∫ v in Set.Ioc u T, obsRate R.D R.ρ t φ v i j := by
  have := (s7_PIS_cov_struct_proof' R T hT t φ ht hφ).2.2.2.1 u T hu.1 hu.2 le_rfl i j
  rw [this, S7PIF6_obsCov_T R t φ ht]
  simp

/-- the covariance of the observations is positive semidefinite on `[0,T]` -/
theorem S7PIF6_obsCov_psd (R : Regime d) {T : ℝ} (hT : 0 < T) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) : (obsCov R.D R.ρ t φ u).PosSemidef := by
  have hE : obsCov R.D R.ρ t φ u = Matrix.of fun i j => ∫ v in Set.Ioc u T, obsRate R.D R.ρ t φ v i j := by
    ext i j
    simp [S7PIF6_obsCov_eq_int R hT t φ ht hφ hu i j]
  have hsub : Set.Ioc u T ⊆ Set.Icc 0 T := fun v hv => ⟨hu.1.trans hv.1.le, hv.2⟩
  have hApsd : ∀ v ∈ Set.Ioc u T, (obsRate R.D R.ρ t φ v).PosSemidef := fun v hv =>
    (s7_PIS_cov_struct_proof' R T hT t φ ht hφ).1 v (hsub hv)
  rw [hE, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, star_trivial]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    exact Matrix.IsHermitian.apply (hApsd v hv).isHermitian i j
  · intro x
    have hI : ∀ i j, IntegrableOn (fun v => x i * (obsRate R.D R.ρ t φ v i j * x j)) (Set.Ioc u T) := by
      intro i j
      have h1 : IntegrableOn (fun v => obsRate R.D R.ρ t φ v i j) (Set.Ioc u T) := by
        have h2 : IntegrableOn (fun v => 2 * R.D.invβ * S7PIS3_h R t φ i j v) (Set.Icc 0 T) :=
          (S7PIS3_h_intOn R t φ ht hφ i j).const_mul (2 * R.D.invβ)
        have h2 := h2.mono_set hsub
        refine h2.congr_fun (fun v hv => ?_) measurableSet_Ioc
        exact (S7PIS3_obsRate_eq R t φ i j (hu.1.trans hv.1.le)).symm
      exact (h1.mul_const (x j)).const_mul (x i)
    have hq : star x ⬝ᵥ (Matrix.of fun i j => ∫ v in Set.Ioc u T, obsRate R.D R.ρ t φ v i j).mulVec x =
        ∫ v in Set.Ioc u T, ∑ i, ∑ j, x i * (obsRate R.D R.ρ t φ v i j * x j) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hI i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_mul_const]
    rw [hq]
    refine setIntegral_nonneg measurableSet_Ioc fun v hv => ?_
    have := ((Matrix.posSemidef_iff_dotProduct_mulVec.1 (hApsd v hv))).2 x
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, star_trivial] using this

/-- **The `C^{1,2}` extension on one piece.**  `[a,b] ⊆ [0,T]` with no observation time in `(a,b)`;
`f = gaussHeat obsCov G` on `[a,b]` and `∂_r f = -½ ⟨obsRate, D²f⟩` on `(a,b]`. -/
theorem S7PIF6_c12 (R : Regime d) {T : ℝ} (hT : 0 < T) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hno : ∀ i, ¬ (a < t i ∧ t i < b)) :
    ∃ f : ℝ → EuclideanSpace ℝ (Fin q) → ℝ, HRS.IsC12On T Set.univ f ∧
      (∀ r ∈ Set.Icc a b, f r = gaussHeat (obsCov R.D R.ρ t φ) G r) ∧
      ∀ r ∈ Set.Ioc a b, ∀ c, derivWithin (fun s => f s c) (Set.Icc 0 T) r =
        -(1 / 2) * ∑ i, ∑ j, obsRate R.D R.ρ t φ r i j *
          iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G r) c
            ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  obtain ⟨-, hpsdR, hc, hd, -⟩ := s7_PIS_cov_struct_proof' R T hT t φ ht hφ
  obtain ⟨hAc, hAeq⟩ := hc a b ha hab hb hno
  have hApsd : ∀ v ∈ Set.Icc a b, (obsRateR R.D R.ρ t φ a v).PosSemidef := by
    intro v hv
    refine hpsdR a v ⟨ha.trans hv.1, hv.2.trans hb⟩ fun i hi => ?_
    have : b ≤ t i := by
      by_contra h
      exact hno i ⟨hi, not_le.1 h⟩
    exact hv.2.trans this
  have hSb : (obsCov R.D R.ρ t φ b).PosSemidef :=
    S7PIF6_obsCov_psd R hT t φ ht hφ ⟨ha.trans hab, hb⟩
  have hS : ∀ u ∈ Set.Icc a b, ∀ i j, obsCov R.D R.ρ t φ u i j =
      obsCov R.D R.ρ t φ b i j + ∫ v in Set.Ioc u b, obsRateR R.D R.ρ t φ a v i j := by
    intro u hu i j
    rw [hd u b (ha.trans hu.1) hu.2 hb i j]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    rw [hAeq v ⟨hu.1.trans_lt hv.1, hv.2⟩]
  obtain ⟨f, hf, hfeq, hfd⟩ := HRS.MC.Sec7.S7PIH.s7_PIH_heat_c12_proof' a b T ha hab hb hT
    (obsRateR R.D R.ρ t φ a) (obsCov R.D R.ρ t φ) hAc hApsd hSb hS G hG
  refine ⟨f, hf, hfeq, fun r hr c => ?_⟩
  rw [hfd r ⟨hr.1.le, hr.2⟩ c, hAeq r hr]

end HRS.MC.Sec7.S7PIF6

end
