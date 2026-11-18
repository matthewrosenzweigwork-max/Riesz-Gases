import Mathlib
import HRS.Sections.Q41Aux5
import HRS.Sections.Q41Aux6
import HRS.Sections.Q41Aux7
import HRS.Sections.Q41Aux8

/-!
# Packet Q41, helper 9: the continuous `E_m`-valued Gaussian process with a given mode kernel
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix RealInnerProductSpace

namespace HRS.Q41

open HRS

/-- The finite-dimensional law of a centred Gaussian process. -/
lemma q41_vec_law {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ι → Ω → ℝ) (hY : IsGaussianProcess Y P) (hm : ∀ i, Measurable (Y i))
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (idx : κ → ι) (Γ : Matrix κ κ ℝ) (hΓ : Γ.PosSemidef)
    (hcov : ∀ a b, cov[Y (idx a), Y (idx b); P] = Γ a b) :
    P.map (fun ω => (WithLp.toLp 2 (fun a => Y (idx a) ω) : EuclideanSpace ℝ κ)) =
      multivariateGaussian 0 Γ := by
  classical
  have hVm : Measurable (fun ω => (WithLp.toLp 2 (fun a => Y (idx a) ω) : EuclideanSpace ℝ κ)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => hm (idx a))
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_multivariateGaussian hΓ]
  set X : Ω → ℝ := fun ω => ∑ a : κ, t a * Y (idx a) ω with hX
  have hproc : IsGaussianProcess (fun (a : κ) ω => t a • Y (idx a) ω) P :=
    (hY.comp_right idx).smul (fun a => t a)
  have hXg : HasGaussianLaw X P := by
    have := hproc.hasGaussianLaw_fun_sum (I := Finset.univ)
    simpa [hX] using this
  have hmemLp : ∀ a, MemLp (Y (idx a)) 2 P := fun a => (hY.hasGaussianLaw_eval (idx a)).memLp_two
  have hXmean : ∫ ω, X ω ∂P = 0 := by
    simp only [hX]
    rw [integral_finset_sum _ fun a _ => ((hmemLp a).integrable (by norm_num)).const_mul _]
    simp [integral_const_mul, hmean]
  have hXvar : variance X P = t ⬝ᵥ (Γ *ᵥ t) := by
    have hm' : AEMeasurable X P := hXg.aemeasurable
    rw [← covariance_self hm']
    have hmem2 : ∀ a ∈ Finset.univ, MemLp (fun ω => t a * Y (idx a) ω) 2 P :=
      fun a _ => (hmemLp a).const_mul _
    rw [show X = fun ω => ∑ a ∈ Finset.univ, t a * Y (idx a) ω from rfl,
      covariance_fun_sum_fun_sum' hmem2 hmem2]
    simp only [dotProduct, Matrix.mulVec, covariance_const_mul_left, covariance_const_mul_right, hcov]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hXlaw : P.map X = gaussianReal 0 (t ⬝ᵥ (Γ *ᵥ t)).toNNReal := by
    rw [hXg.map_eq_gaussianReal, hXmean, hXvar]
  have hip : ∀ ω, ⟪(WithLp.toLp 2 (fun a => Y (idx a) ω) : EuclideanSpace ℝ κ), t⟫ = X ω := by
    intro ω
    simp [hX, PiLp.inner_apply, mul_comm]
  have hcf : charFun (P.map (fun ω => (WithLp.toLp 2 (fun a => Y (idx a) ω) : EuclideanSpace ℝ κ))) t =
      charFun (P.map X) 1 := by
    rw [charFun_apply, charFun_apply, integral_map hVm.aemeasurable (by fun_prop),
      integral_map hXg.aemeasurable (by fun_prop)]
    simp [hip]
  rw [hcf, hXlaw, charFun_gaussianReal]
  have hq : 0 ≤ t ⬝ᵥ (Γ *ᵥ t) := by simpa using hΓ.dotProduct_mulVec_nonneg t
  simp [Real.coe_toNNReal _ hq]

/-- Hypotheses on the cross-covariance `r t s k l = Cov(Z^k_t, Z^l_s)` of the Fourier-mode
coordinates. -/
structure ModeKernel (d : ℕ) (r : ℝ → ℝ → NonzeroLattice d → NonzeroLattice d → ℝ) : Prop where
  symm : ∀ t s k l, r t s k l = r s t l k
  psd : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ι → ℝ) (k : ι → NonzeroLattice d),
    (∀ a, 0 ≤ t a) →
    (Matrix.of fun a b => r (t a) (t b) (k a) (k b)).PosSemidef
  var : ∃ B : ℝ, ∀ t k, 0 ≤ t → r t t k k ≤ B
  inc : ∃ B : ℝ, ∀ t s k, 0 ≤ t → 0 ≤ s →
    r t t k k + r s s k k - 2 * r t s k k ≤ B * Lattice.jp k.1 ^ 2 * |t - s|

variable {d : ℕ} {r : ℝ → ℝ → NonzeroLattice d → NonzeroLattice d → ℝ}

lemma ModeKernel.diag_nonneg (hr : ModeKernel d r) {t : ℝ} (ht : 0 ≤ t) (k : NonzeroLattice d) :
    0 ≤ r t t k k := by
  have := (hr.psd (Fin 1) (fun _ => t) (fun _ => k) (fun _ => ht)).dotProduct_mulVec_nonneg (fun _ => 1)
  simpa [dotProduct, Matrix.mulVec] using this

/-- Cauchy–Schwarz for the positive semidefinite mode kernel. -/
lemma ModeKernel.cs (hr : ModeKernel d r) {t t' s : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (hs : 0 ≤ s)
    (k l : NonzeroLattice d) :
    (r t s k l - r t' s k l) ^ 2 ≤
      (r t t k k + r t' t' k k - 2 * r t t' k k) * r s s l l := by
  have hpsd := hr.psd (Fin 3) ![t, t', s] ![k, k, l] (by intro a; fin_cases a <;> simp [ht, ht', hs])
  have hsym : ∀ a b : Fin 3, (Matrix.of fun a b => r (![t, t', s] a) (![t, t', s] b) (![k, k, l] a) (![k, k, l] b)) a b =
      (Matrix.of fun a b => r (![t, t', s] a) (![t, t', s] b) (![k, k, l] a) (![k, k, l] b)) b a := by
    intro a b
    simp only [Matrix.of_apply]
    exact hr.symm _ _ _ _
  have hq : ∀ u v : ℝ, 0 ≤ (r t t k k + r t' t' k k - 2 * r t t' k k) * u ^ 2 +
      2 * (r t s k l - r t' s k l) * u * v + r s s l l * v ^ 2 := by
    intro u v
    have := hpsd.dotProduct_mulVec_nonneg ![u, -u, v]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.of_apply, star_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at this
    have e1 : r t' t k k = r t t' k k := hr.symm t' t k k
    have e2 : r s t l k = r t s k l := (hr.symm t s k l).symm
    have e3 : r s t' l k = r t' s k l := (hr.symm t' s k l).symm
    have e4 : r t s k l = r t s k l := rfl
    simp only [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons] at this
    rw [e1, e2, e3] at this
    nlinarith [this]
  have := discrim_le_zero (a := r t t k k + r t' t' k k - 2 * r t t' k k)
    (b := 2 * (r t s k l - r t' s k l)) (c := r s s l l) (fun u => by
      have := hq u 1
      nlinarith [this])
  unfold discrim at this
  nlinarith [this]

lemma ModeKernel.abs_diff_le (hr : ModeKernel d r) {Bv Bi : ℝ}
    (hBv : ∀ t k, 0 ≤ t → r t t k k ≤ Bv)
    (hBi : ∀ t s k, 0 ≤ t → 0 ≤ s →
      r t t k k + r s s k k - 2 * r t s k k ≤ Bi * Lattice.jp k.1 ^ 2 * |t - s|)
    {t t' s : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (hs : 0 ≤ s) (k l : NonzeroLattice d) :
    |r t s k l - r t' s k l| ≤ Real.sqrt (|Bi| * Lattice.jp k.1 ^ 2 * |t - t'| * |Bv|) := by
  apply Real.abs_le_sqrt
  have h1 := hr.cs ht ht' hs k l
  have hC0 := hr.diag_nonneg hs l
  have hC : r s s l l ≤ |Bv| := (hBv s l hs).trans (le_abs_self _)
  have hA : r t t k k + r t' t' k k - 2 * r t t' k k ≤ |Bi| * Lattice.jp k.1 ^ 2 * |t - t'| :=
    (hBi t t' k ht ht').trans (by
      have : 0 ≤ Lattice.jp k.1 ^ 2 * |t - t'| := by positivity
      nlinarith [le_abs_self Bi, mul_nonneg this (abs_nonneg Bi)])
  have hb : 0 ≤ |Bi| * Lattice.jp k.1 ^ 2 * |t - t'| := by positivity
  calc (r t s k l - r t' s k l) ^ 2 ≤ _ := h1
    _ ≤ (|Bi| * Lattice.jp k.1 ^ 2 * |t - t'|) * r s s l l := mul_le_mul_of_nonneg_right hA hC0
    _ ≤ (|Bi| * Lattice.jp k.1 ^ 2 * |t - t'|) * |Bv| := mul_le_mul_of_nonneg_left hC hb

lemma ModeKernel.tendsto (hr : ModeKernel d r) {tn sn : ℕ → ℝ} {t s : ℝ}
    (htn : ∀ n, 0 ≤ tn n) (hsn : ∀ n, 0 ≤ sn n) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (h1 : Tendsto tn atTop (𝓝 t)) (h2 : Tendsto sn atTop (𝓝 s)) (k l : NonzeroLattice d) :
    Tendsto (fun n => r (tn n) (sn n) k l) atTop (𝓝 (r t s k l)) := by
  obtain ⟨Bv, hBv⟩ := hr.var
  obtain ⟨Bi, hBi⟩ := hr.inc
  have e1 : ∀ n, |r (tn n) (sn n) k l - r t (sn n) k l| ≤
      Real.sqrt (|Bi| * Lattice.jp k.1 ^ 2 * |tn n - t| * |Bv|) :=
    fun n => hr.abs_diff_le hBv hBi (htn n) ht (hsn n) k l
  have e2 : ∀ n, |r t (sn n) k l - r t s k l| ≤
      Real.sqrt (|Bi| * Lattice.jp l.1 ^ 2 * |sn n - s| * |Bv|) := by
    intro n
    rw [hr.symm t (sn n) k l, hr.symm t s k l]
    exact hr.abs_diff_le hBv hBi (hsn n) hs ht l k
  have hlim : ∀ (c : ℝ) (u : ℕ → ℝ) (u0 : ℝ), Tendsto u atTop (𝓝 u0) →
      Tendsto (fun n => Real.sqrt (c * |u n - u0|)) atTop (𝓝 0) := by
    intro c u u0 hu
    have : Tendsto (fun n => |u n - u0|) atTop (𝓝 0) := by
      simpa using (hu.sub_const u0).abs
    have h := (this.const_mul c)
    have h' := (Real.continuous_sqrt.tendsto _).comp h
    simp only [Function.comp_def, mul_zero, Real.sqrt_zero] at h'
    exact h'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (g := fun n => Real.sqrt (|Bi| * Lattice.jp k.1 ^ 2 * |Bv| * |tn n - t|) +
      Real.sqrt (|Bi| * Lattice.jp l.1 ^ 2 * |Bv| * |sn n - s|)) ?_
  · rw [Real.norm_eq_abs]
    calc |r (tn n) (sn n) k l - r t s k l|
        = |(r (tn n) (sn n) k l - r t (sn n) k l) + (r t (sn n) k l - r t s k l)| := by ring_nf
      _ ≤ |r (tn n) (sn n) k l - r t (sn n) k l| + |r t (sn n) k l - r t s k l| := abs_add_le _ _
      _ ≤ _ := by
        refine add_le_add ((e1 n).trans (le_of_eq ?_)) ((e2 n).trans (le_of_eq ?_)) <;>
          (congr 1; ring)
  · have := (hlim (|Bi| * Lattice.jp k.1 ^ 2 * |Bv|) tn t h1).add
      (hlim (|Bi| * Lattice.jp l.1 ^ 2 * |Bv|) sn s h2)
    simpa using this

end HRS.Q41
