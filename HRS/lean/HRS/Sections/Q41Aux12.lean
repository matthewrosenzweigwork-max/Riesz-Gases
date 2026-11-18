import Mathlib
import HRS.Energy.StaticLimitBasic
import HRS.Sections.Q41Aux11

/-!
# Packet Q41, helper 12: the continuous `E_m`-valued Gaussian process with mode kernel `r`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix RealInnerProductSpace

namespace HRS.Q41

open HRS

variable {d : ℕ} {r : ℝ → ℝ → NonzeroLattice d → NonzeroLattice d → ℝ}

lemma q41_continuous_fourierCoeff (m : ℝ) (k : NonzeroLattice d) :
    Continuous fun F : NegSobolev d m => NegSobolev.fourierCoeff F k := by
  have : (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) =
      fun F => Lattice.jp k.1 ^ m * negCoordCLM (m := m) k F := rfl
  rw [this]
  exact (negCoordCLM (m := m) k).continuous.const_mul _

lemma q41_D_floor_mem (n : ℕ) (t : ℝ) : (⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n ∈ q41_D := q41_D_mem n _

lemma q41_floor_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n) atTop (𝓝 t) := by
  have hlow : ∀ n : ℕ, t - (1 / 2) ^ n ≤ (⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n := by
    intro n
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have h2 : 2 ^ n * t < (⌊2 ^ n * t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [one_div_pow, le_div_iff₀ hp, sub_mul, one_div, inv_mul_cancel₀ hp.ne']
    linarith
  have hup : ∀ n : ℕ, (⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n ≤ t := by
    intro n
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have h1 : (⌊2 ^ n * t⌋₊ : ℝ) ≤ 2 ^ n * t := Nat.floor_le (by positivity)
    rw [div_le_iff₀ hp]; linarith
  have hg : Tendsto (fun n : ℕ => t - (1 / 2 : ℝ) ^ n) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds hlow hup

/-- Finite-dimensional laws of the modes at dyadic times. -/
lemma Q41Fam.dyadic_law (F : Q41Fam d r) (hr : ModeKernel d r) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    {Bv : ℝ} (hB : ∀ (q : q41_D) (k : NonzeroLattice d), r q q k k ≤ Bv)
    (hgood : ∀ᵐ ω ∂gpP, ω ∈ F.good m) {ι : Type} [Fintype ι] [DecidableEq ι] (q : ι → q41_D) (k : ι → NonzeroLattice d) :
    gpP.map (fun ω => (WithLp.toLp 2 (fun a => NegSobolev.fourierCoeff (F.Zc m (q a) ω) (k a)) :
        EuclideanSpace ℝ ι)) =
      multivariateGaussian 0 (Matrix.of fun a b => r (q a) (q b) (k a) (k b)) := by
  have hae : ∀ᵐ ω ∂gpP, ∀ a, Memℓp (fun k' : NonzeroLattice d => Lattice.jp k'.1 ^ (-m) *
      F.Y (q a, k') ω) 2 := ae_all_iff.2 fun a => F.ae_memℓp hm hB (q a)
  have heq : (fun ω => (WithLp.toLp 2 (fun a => NegSobolev.fourierCoeff (F.Zc m (q a) ω) (k a)) :
        EuclideanSpace ℝ ι)) =ᵐ[gpP]
      (fun ω => (WithLp.toLp 2 (fun a => F.Y (q a, k a) ω) : EuclideanSpace ℝ ι)) := by
    filter_upwards [hgood, hae] with ω hg hmem
    congr 1
    funext a
    obtain ⟨⟨n, j⟩, hqa⟩ := (q a).2
    have h1 : F.Zc m (q a) ω = F.Zbar m (q a) ω := by
      rw [← hqa]; exact F.Zc_dyadic m hg n j
    rw [h1, F.Zbar_of_mem]
    exact q41_fourierCoeff_ofSeq (hmem a) (k a)
  rw [Measure.map_congr heq]
  exact q41_vec_law gpP F.Y F.gauss F.meas F.mean (fun a => (q a, k a)) _
    (hr.psd ι (fun a => (q a : ℝ)) k (fun a => q41_D_nonneg (q a).2)) (fun a b => F.cov _ _)

/-- **Mode process.**  A continuous `E_m`-valued centred Gaussian process whose Fourier-mode
coordinates have cross-covariance `r`. -/
theorem q41_modes_process (hd : 1 ≤ d) {m : ℝ} (hm : (d : ℝ) + 2 < 2 * m)
    (hr : ModeKernel d r) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : ℝ → Ω → NegSobolev d m), (∀ t, Measurable (Z t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0)) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (k : ι → NonzeroLattice d), (∀ a, 0 ≤ τ a) →
        P.map (fun ω => (WithLp.toLp 2 (fun a => NegSobolev.fourierCoeff (Z (τ a) ω) (k a)) :
          EuclideanSpace ℝ ι)) =
        multivariateGaussian 0 (Matrix.of fun a b => r (τ a) (τ b) (k a) (k b)) := by
  obtain ⟨Y, hYm, hYg, hYmean, hYcov⟩ := q41_gp_family hd hr
  let F : Q41Fam d r := ⟨Y, hYm, hYg, hYmean, hYcov⟩
  obtain ⟨Bv, hBv⟩ := hr.var
  obtain ⟨Bi, hBi⟩ := hr.inc
  have hm0 : (d : ℝ) < 2 * m := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hB : ∀ (q : q41_D) (k : NonzeroLattice d), r q q k k ≤ Bv :=
    fun q k => hBv q k (q41_D_nonneg q.2)
  have hBi' : ∀ (q q' : q41_D) (k : NonzeroLattice d),
      r q' q' k k + r q q k k - 2 * r q' q k k ≤ Bi * Lattice.jp k.1 ^ 2 * |(q' : ℝ) - q| :=
    fun q q' k => hBi q' q k (q41_D_nonneg q'.2) (q41_D_nonneg q.2)
  have hgood : ∀ᵐ ω ∂gpP, ω ∈ F.good m := F.ae_incr hd hm hB hBi'
  refine ⟨ℕ → ℝ, inferInstance, gpP, inferInstance, F.Zc m, F.measurable_Zc hd m, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω
    exact F.continuousOn_Zc m hω
  · intro ι _ _ τ k hτ
    -- dyadic approximations
    set τn : ℕ → ι → ℝ := fun n a => (⌊2 ^ n * τ a⌋₊ : ℝ) / 2 ^ n with hτn
    have hτn_mem : ∀ n a, τn n a ∈ q41_D := fun n a => q41_D_floor_mem n (τ a)
    have hdy := fun n => F.dyadic_law hr hm0 hB hgood (fun a => (⟨τn n a, hτn_mem n a⟩ : q41_D)) k
    have hcoef : ∀ (t : ℝ) (a : ι), Measurable fun ω => NegSobolev.fourierCoeff (F.Zc m t ω) (k a) :=
      fun t a => (q41_continuous_fourierCoeff m (k a)).measurable.comp (F.measurable_Zc hd m t)
    have hvm : ∀ (t : ι → ℝ), Measurable fun ω =>
        (WithLp.toLp 2 (fun a => NegSobolev.fourierCoeff (F.Zc m (t a) ω) (k a)) :
          EuclideanSpace ℝ ι) := fun t =>
      (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable.comp
        (measurable_pi_iff.2 fun a => hcoef (t a) a)
    refine q41_gauss_limit gpP
      (fun n ω => (WithLp.toLp 2 (fun a => NegSobolev.fourierCoeff (F.Zc m (τn n a) ω) (k a)) :
        EuclideanSpace ℝ ι))
      (fun ω => (WithLp.toLp 2 (fun a => NegSobolev.fourierCoeff (F.Zc m (τ a) ω) (k a)) :
        EuclideanSpace ℝ ι))
      (fun n => (hvm _).aemeasurable) (hvm τ).aemeasurable
      (fun n => Matrix.of fun a b => r (τn n a) (τn n b) (k a) (k b)) _ hdy
      (fun n => hr.psd ι (τn n) k (fun a => q41_D_nonneg (hτn_mem n a))) ?_ ?_
    · filter_upwards [hgood] with ω hω
      have hc := F.continuousOn_Zc m hω
      refine (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).tendsto _ |>.comp ?_
      refine tendsto_pi_nhds.2 fun a => ?_
      have h1 : Tendsto (fun n => τn n a) atTop (𝓝[Set.Ici 0] (τ a)) :=
        tendsto_nhdsWithin_iff.2 ⟨q41_floor_tendsto (hτ a),
          Eventually.of_forall fun n => q41_D_nonneg (hτn_mem n a)⟩
      exact ((q41_continuous_fourierCoeff m (k a)).tendsto _).comp ((hc (τ a) (hτ a)).tendsto.comp h1)
    · intro a b
      exact hr.tendsto (fun n => q41_D_nonneg (hτn_mem n a)) (fun n => q41_D_nonneg (hτn_mem n b))
        (hτ a) (hτ b) (q41_floor_tendsto (hτ a)) (q41_floor_tendsto (hτ b)) (k a) (k b)

end HRS.Q41
