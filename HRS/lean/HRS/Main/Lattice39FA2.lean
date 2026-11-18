import HRS.Main.Lattice39FA1
import HRS.Uniform.Q54cAux14

/-!
# Example A.39 final form: D2' (assembly of `InitialFluctuationField`), relocated proof
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-- Square-summability of the real Fourier coefficients of an `L²` function. -/
theorem lat39fa_summable_sq {φ : Torus d → ℝ} (hφ : MemLp φ 2 volume) :
    Summable fun k : NonzeroLattice d => Torus.funRealCoeff φ k ^ 2 := by
  have hT := (Torus.hasSum_sq_coeff hφ).summable
  have hTn : Summable fun k : NonzeroLattice d => Torus.cosCoeff φ k.1 ^ 2 + Torus.sinCoeff φ k.1 ^ 2 :=
    hT.comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hTn.mul_left 2)
  have h := Torus.funRealCoeff_sq_add_neg (φ := φ) k
  have := sq_nonneg (Torus.funRealCoeff φ ⟨-k.1, neg_ne_zero.mpr k.2⟩)
  linarith

theorem lat39fa_mean_add {u v : Torus d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Torus.mean (fun x => u x + v x) = Torus.mean u + Torus.mean v := by
  unfold Torus.mean
  exact integral_add (hu.integrable one_le_two) (hv.integrable one_le_two)

theorem lat39fa_mean_sub {u v : Torus d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Torus.mean (fun x => u x - v x) = Torus.mean u - Torus.mean v := by
  unfold Torus.mean
  exact integral_sub (hu.integrable one_le_two) (hv.integrable one_le_two)

/-- Parseval, polarised, for a mean-zero `u`. -/
theorem lat39fa_integral_mul_eq_tsum {u v : Torus d → ℝ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) (hu0 : Torus.mean u = 0) :
    ∫ x, u x * v x = ∑' k : NonzeroLattice d, Torus.funRealCoeff u k * Torus.funRealCoeff v k := by
  have hp : MemLp (fun x => u x + v x) 2 volume := hu.add hv
  have hm : MemLp (fun x => u x - v x) 2 volume := hu.sub hv
  have ep := Torus.parseval_realCoeff _ hp
  have em := Torus.parseval_realCoeff _ hm
  have cp : ∀ k, Torus.funRealCoeff (fun x => u x + v x) k =
      Torus.funRealCoeff u k + Torus.funRealCoeff v k := fun k => by
    simpa using HRS.Uniform.Q54c.funRealCoeff_comb hu hv 1 1 k
  have cm : ∀ k, Torus.funRealCoeff (fun x => u x - v x) k =
      Torus.funRealCoeff u k - Torus.funRealCoeff v k := fun k =>
    HRS.Uniform.Q54.funRealCoeff_sub' hu hv k
  rw [lat39fa_mean_add hu hv, hu0] at ep
  rw [lat39fa_mean_sub hu hv, hu0] at em
  simp only [cp] at ep
  simp only [cm] at em
  have s1 := lat39fa_summable_sq hu
  have s2 := lat39fa_summable_sq hv
  have sp := lat39fa_summable_sq hp
  have sm := lat39fa_summable_sq hm
  simp only [cp] at sp
  simp only [cm] at sm
  have hint : ∫ x, ((u x + v x) ^ 2 - (u x - v x) ^ 2) = 4 * ∫ x, u x * v x := by
    rw [← integral_const_mul]
    congr 1; funext x; ring
  rw [integral_sub (hp.integrable_sq) (hm.integrable_sq), ep, em] at hint
  have hsub := sp.tsum_sub sm
  have : ∑' k : NonzeroLattice d, ((Torus.funRealCoeff u k + Torus.funRealCoeff v k) ^ 2 -
      (Torus.funRealCoeff u k - Torus.funRealCoeff v k) ^ 2) =
      4 * ∑' k : NonzeroLattice d, Torus.funRealCoeff u k * Torus.funRealCoeff v k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  have h0 : ((0 : ℝ) + Torus.mean v) ^ 2 - ((0 : ℝ) - Torus.mean v) ^ 2 = 0 := by ring
  linarith

open InitialDataAux in
theorem lat39fa_eval_eta {a : Torus d → Euc d} (ha : Torus.IsSmooth a) {ψ : Torus d → ℝ}
    (hψ : MemSobolev (gammaIdx d : ℝ) ψ) (h0 : Torus.mean ψ = 0) :
    NegSobolev.eval (lattice39fEta a) ψ = ∫ x, ψ x * (-Torus.div a x) := by
  have hca : Torus.IsCk 1 a := lat39fa_isCk1 ha
  have hcont : Continuous (fun x => -Torus.div a x) := (continuous_div a hca).neg
  have hγ : (d : ℝ) < 2 * (gammaIdx d : ℝ) := by
    have := lat39fa_gamma_gt d
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hmem := NegSobolev.memℓp_of_bounded hγ _ (bdd_funRealCoeff _ hcont)
  have hf2 : MemLp (fun x => -Torus.div a x) 2 volume :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [lat39fa_integral_mul_eq_tsum hψ.1 hf2 h0]
  unfold NegSobolev.eval
  refine tsum_congr fun k => ?_
  have hj := Torus.jp_pos k.1
  have : NegSobolev.fourierCoeff (lattice39fEta a) k = Torus.funRealCoeff (fun x => -Torus.div a x) k := by
    unfold NegSobolev.fourierCoeff lattice39fEta NegSobolev.ofFun
    rw [NegSobolev.coord_ofSeq_of_mem _ hmem k, ← mul_assoc, ← Real.rpow_add hj]
    simp
  rw [this, mul_comm]

/-- D2' relocated. -/
theorem lattice39f_initialFluctuationField_of_moments_proof (S : MainData d)
    (R : ∀ N, Realization d N)
    (a : Torus d → Euc d) (ha : Torus.IsSmooth a) (Cin : ℝ) (εf : ℕ → ℝ)
    (hη : ∀ (N : ℕ) (ω : (R N).Ω) (ψ : Torus d → ℝ), (R N).η ω ψ = ∫ x, ψ x * (-Torus.div a x))
    (hεf : ∀ N : ℕ, 1 ≤ N → 0 ≤ εf N)
    (h1 : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0 -
          lattice39fEta a‖ₑ ∂(R N).P ≤ ENNReal.ofReal (εf N))
    (h2 : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
          ∂(R N).P +
        ∫⁻ _ω, ‖lattice39fEta a‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2)) :
    InitialFluctuationField S R (gammaIdx d) Cin εf (fun _ _ => lattice39fEta a)
      (Measure.dirac (lattice39fEta a)) := by
  refine ⟨fun N => measurable_const, fun N _ => ?_, hεf, ?_, h1, h2⟩
  · show (R N).P.map (fun _ => lattice39fEta a) = _
    rw [Measure.map_const, measure_univ, one_smul]
  · intro N ω ψ hψ h0
    rw [hη N ω ψ, lat39fa_eval_eta ha hψ h0]

example := (@lattice39f_initialFluctuationField_of_moments_proof :
  type_of% @lattice39f_initialFluctuationField_of_moments)

end Main

end HRS
