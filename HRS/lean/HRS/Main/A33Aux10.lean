import Mathlib
import HRS.Main.A33Aux9

/-!
# Packet A33, helper 10: the `E_J`-valued Gaussian field `G_t` and its pairings with smooth tests
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

/-- The properties of the isonormal process of `a33_isonormal`. -/
structure A33Iso {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (W : H → Ω → ℝ) : Prop where
  meas : ∀ h, Measurable (W h)
  memLp : ∀ h, MemLp (W h) 2 P
  lin : ∀ (a b : ℝ) (h h' : H), W (a • h + b • h') =ᵐ[P] fun ω => a * W h ω + b * W h' ω
  fin : ∀ {κ : Type} (h : κ → H) (t : κ → ℝ) (J : Finset κ),
    W (∑ a ∈ J, t a • h a) =ᵐ[P] fun ω => ∑ a ∈ J, t a * W (h a) ω
  inner : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = ⟪h, h'⟫
  single : ∀ g : H, P.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2))
  gauss : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (h : κ → H),
    P.map (fun ω => (WithLp.toLp 2 (fun a => W (h a) ω) : EuclideanSpace ℝ κ)) =
      multivariateGaussian 0 (Matrix.of fun a b => ⟪h a, h b⟫)

lemma a33_tendstoInMeasure_of_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P)
    (hg : MemLp g 2 P)
    (h : Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop g := by
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
  have e : ∀ n, eLpNorm (f n - g) 2 P =
      ENNReal.ofReal ((∫ ω, (f n ω - g ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) := by
    intro n
    rw [(show MemLp (f n - g) 2 P from (hf n).sub hg).eLpNorm_eq_integral_rpow_norm (by norm_num)
      (by norm_num)]
    congr 2
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [Real.rpow_two, sq_abs]
    · norm_num
  simp_rw [e]
  have h2 : Tendsto (fun n => (∫ ω, (f n ω - g ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) atTop (𝓝 (0 ^ (1 / 2 : ℝ))) :=
    h.rpow_const (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h2
  simpa using ENNReal.tendsto_ofReal h2

lemma A33Iso.sq_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : H → Ω → ℝ} (hI : A33Iso P W) (a b : H) :
    ∫ ω, (W a ω - W b ω) ^ 2 ∂P = ‖a - b‖ ^ 2 := by
  have h1 : W (a - b) =ᵐ[P] fun ω => W a ω - W b ω := by
    have := hI.lin 1 (-1) a b
    filter_upwards [this] with ω h
    simpa [sub_eq_add_neg] using h
  have h2 := hI.inner (a - b) (a - b)
  rw [real_inner_self_eq_norm_sq] at h2
  rw [← h2]
  refine integral_congr_ae ?_
  filter_upwards [h1] with ω h
  rw [h]; ring

section Field

variable (S : A33Setup d) (q : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  (W : Lp (Euc d) 2 (a33_nu d S.T S.ρ) → Ω → ℝ)

/-- The coordinates `X_{t,k} = W(h_{t,e_k})` of the noise field. -/
def a33_X (t : ℝ) (k : NonzeroLattice d) (ω : Ω) : ℝ := W (a33_vec S q t (Torus.realMode k)) ω

/-- The `E_J`-valued noise field `G_t`. -/
def a33_Gfield (t : ℝ) (ω : Ω) : NegSobolev d (S.J : ℝ) :=
  NegSobolev.ofSeq (S.J : ℝ) (fun k => a33_X S q W t k ω)

theorem a33_Gfield_meas (e : ℕ ≃ NonzeroLattice d) (hI : A33Iso P W) (t : ℝ) :
    Measurable (a33_Gfield S q W t : Ω → NegSobolev d (S.J : ℝ)) :=
  HRS.Q41.q41_measurable_ofSeq (m := (S.J : ℝ)) e e.surjective
    (fun k ω => a33_X S q W t k ω) (fun k => hI.meas _)

theorem a33_X_sq (hI : A33Iso P W) (t : ℝ) (k : NonzeroLattice d) :
    ∫ ω, a33_X S q W t k ω ^ 2 ∂P = ‖a33_vec S q t (Torus.realMode k)‖ ^ 2 := by
  have := hI.inner (a33_vec S q t (Torus.realMode k)) (a33_vec S q t (Torus.realMode k))
  rw [real_inner_self_eq_norm_sq] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [a33_X, sq]

theorem a33_ae_summable [IsProbabilityMeasure P] (hI : A33Iso P W) {t : ℝ}
    (ht : t ∈ Set.Icc 0 S.T) :
    ∀ᵐ ω ∂P, Summable fun k : NonzeroLattice d =>
      (Lattice.jp k.1 ^ (-(S.J : ℝ)) * a33_X S q W t k ω) ^ 2 := by
  have h := a33_ae_summable_sq (P := P) (fun k ω => a33_X S q W t k ω) (fun k => hI.meas _)
    (fun k => hI.memLp _) (fun k => (Lattice.jp k.1 ^ (-(S.J : ℝ))) ^ 2)
    (fun k => sq_nonneg _) (by
      refine (S.trace_summable q ht).congr fun k => ?_
      rw [a33_X_sq S q W hI t k, mul_pow])
  filter_upwards [h] with ω hω
  refine hω.congr fun k => ?_
  rw [mul_pow]

theorem a33_eval_ae [IsProbabilityMeasure P] (e : ℕ ≃ NonzeroLattice d) (hI : A33Iso P W)
    {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∀ᵐ ω ∂P, NegSobolev.eval (a33_Gfield S q W t ω) φ = W (a33_vec S q t φ) ω := by
  classical
  set u : NonzeroLattice d → Lp (Euc d) 2 (a33_nu d S.T S.ρ) :=
    fun k => a33_vec S q t (Torus.realMode k) with hu
  set c : ℕ → ℝ := fun i => Torus.funRealCoeff φ (e i) with hc
  set w : ℕ → Lp (Euc d) 2 (a33_nu d S.T S.ρ) := fun n => ∑ i ∈ Finset.range n, c i • u (e i) with hw
  have hS : ∀ n, ∀ᵐ ω ∂P, W (w n) ω = ∑ i ∈ Finset.range n, a33_X S q W t (e i) ω * c i := by
    intro n
    filter_upwards [hI.fin (fun i : ℕ => u (e i)) c (Finset.range n)] with ω h
    rw [hw]
    simp only
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [a33_X, hu, mul_comm]
  have hSall : ∀ᵐ ω ∂P, ∀ n, W (w n) ω = ∑ i ∈ Finset.range n, a33_X S q W t (e i) ω * c i :=
    ae_all_iff.2 hS
  obtain ⟨K, hK0, hK⟩ := S.vec_res_norm q
  have hnorm : Tendsto (fun n => ‖w n - a33_vec S q t φ‖) atTop (𝓝 0) := by
    have h1 := (a33_trunc_sob hφ e (mStar d : ℝ)).2
    have h2 : Tendsto (fun n => K * sobolevNorm (mStar d : ℝ) (a33_res φ e n)) atTop (𝓝 0) := by
      simpa using h1.const_mul K
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2
    rw [norm_sub_rev]
    exact hK ht hφ e n
  have hconv : Tendsto (fun n => ∫ ω, (W (w n) ω - W (a33_vec S q t φ) ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simp_rw [hI.sq_sub]
    simpa using hnorm.pow 2
  have hmeas : TendstoInMeasure P (fun n => W (w n)) atTop (W (a33_vec S q t φ)) :=
    a33_tendstoInMeasure_of_L2 _ _ (fun n => hI.memLp _) (hI.memLp _) hconv
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hgood := a33_ae_summable S q W hI ht
  filter_upwards [hSall, hae, hgood] with ω h1 h2 h3
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(S.J : ℝ)) *
      a33_X S q W t k ω) 2 := (Torus.memℓp_two_iff _).2 h3
  have hfc : ∀ k, NegSobolev.fourierCoeff (a33_Gfield S q W t ω) k = a33_X S q W t k ω :=
    fun k => HRS.Q41.q41_fourierCoeff_ofSeq (m := (S.J : ℝ)) hmem k
  have ht1 := a33_eval_tendsto e (a33_Gfield S q W t ω) hφ
  simp_rw [hfc] at ht1
  have ht2 : Tendsto (fun i => W (w (ns i)) ω) atTop (𝓝 (NegSobolev.eval (a33_Gfield S q W t ω) φ)) := by
    have := ht1.comp hns.tendsto_atTop
    refine this.congr fun i => ?_
    simp only [Function.comp]
    rw [h1 (ns i)]
  exact tendsto_nhds_unique ht2 h2

end Field

end HRS.A33
