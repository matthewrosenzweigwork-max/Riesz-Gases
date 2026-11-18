import HRS.MS.S21G2_S15b
import HRS.MS.S21F_S14
import HRS.Prob.Gaussian

/-!
# S21H2 S15c part A -- finite-stage Gaussian tilt for the iid quadratic partial sums (R26-T3.S15c)

Finite stage: for `Q_N = ½ ∑_{j<N} λ_j (ξ_j² - 1)` under an iid standard Gaussian sequence,
`E exp(-c Q_N) = exp(½ ∑_{j<N} (cλ_j - log (1+cλ_j)))` (integrable), and for `n ≤ N` the law of the first `n`
coordinates under the tilt by `γ Q_N` is the product of the centred Gaussians of variances `(1+γλ_j)⁻¹`.
Helper names carry the prefix `s21h2_s15c_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS
open Contr

/-- The partial sums `½ ∑_{j<n} λ_j (ξ_j² - 1)`. -/
def s21h2_s15c_Qn {Ω : Type*} (ξ : ℕ → Ω → ℝ) (lam : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (1/2) * ∑ j ∈ Finset.range n, lam j * (ξ j ω ^ 2 - 1)

section Fin

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

theorem s21h2_s15c_Qn_eq (lam : ℕ → ℝ) (N : ℕ) (c : ℝ) (ω : Ω) :
    -(c * s21h2_s15c_Qn ξ lam N ω) =
      -((c / 2) * ∑ j : Fin N, lam j * (Zvec ξ N ω j ^ 2 - 1)) := by
  unfold s21h2_s15c_Qn
  rw [Finset.sum_range]
  simp only [Zvec]
  ring

theorem s21h2_s15c_Eexp (hξ : IsStdGaussianSeq P ξ) (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    Integrable (fun ω => Real.exp (-(c * s21h2_s15c_Qn ξ lam N ω))) P ∧
    ∫ ω, Real.exp (-(c * s21h2_s15c_Qn ξ lam N ω)) ∂P =
      Real.exp ((1/2) * ∑ j ∈ Finset.range N, (c * lam j - Real.log (1 + c * lam j))) := by
  have hcont : Continuous fun x : Fin N → ℝ =>
      Real.exp (-((c / 2) * ∑ j : Fin N, lam j * (x j ^ 2 - 1))) := by fun_prop
  have h1 := (r26t3_finite_gaussian_tilt N (fun j : Fin N => lam j) (fun j => hlam j) c hc).1
  have e1 : ∀ x : Fin N → ℝ, Real.exp (-(c / 2) * ∑ j : Fin N, lam j * (x j ^ 2 - 1)) =
      Real.exp (-((c / 2) * ∑ j : Fin N, lam j * (x j ^ 2 - 1))) := fun x => by rw [neg_mul]
  simp_rw [e1] at h1
  have hform : ∫ ω, Real.exp (-(c * s21h2_s15c_Qn ξ lam N ω)) ∂P =
      Real.exp ((1/2) * ∑ j ∈ Finset.range N, (c * lam j - Real.log (1 + c * lam j))) := by
    simp_rw [s21h2_s15c_Qn_eq lam N c]
    rw [integral_comp_Zvec hξ N hcont, h1, Finset.sum_range]
  refine ⟨?_, hform⟩
  by_contra hni
  rw [integral_undef hni] at hform
  exact (Real.exp_pos _).ne hform

theorem s21h2_s15c_Eexp_le (hξ : IsStdGaussianSeq P ξ) (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam2 : Summable fun j => lam j ^ 2) {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    ∫ ω, Real.exp (-(c * s21h2_s15c_Qn ξ lam N ω)) ∂P ≤
      Real.exp ((1/2) * ∑' j, (c * lam j - Real.log (1 + c * lam j))) := by
  rw [(s21h2_s15c_Eexp hξ lam hlam hc N).2]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine (s21f_log_sub_summable hc lam hlam hlam2).sum_le_tsum _ (fun j _ => ?_)
  have hx : 0 ≤ c * lam j := mul_nonneg hc (hlam j)
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + c * lam j by linarith)
  linarith

/-- Marginal of a finite product measure on the first `n` coordinates. -/
theorem s21h2_s15c_marginal {n N : ℕ} (hn : n ≤ N) (ν : Fin N → Measure ℝ)
    [∀ j, IsProbabilityMeasure (ν j)] {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    ∫ x : Fin N → ℝ, g (fun j : Fin n => x (Fin.castLE hn j)) ∂(Measure.pi ν) =
      ∫ y : Fin n → ℝ, g y ∂(Measure.pi fun j : Fin n => ν (Fin.castLE hn j)) := by
  have hind : iIndepFun (fun (i : Fin N) (x : Fin N → ℝ) => x i) (Measure.pi ν) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hind' : iIndepFun (fun (j : Fin n) (x : Fin N → ℝ) => x (Fin.castLE hn j)) (Measure.pi ν) :=
    hind.precomp (Fin.castLE_injective hn)
  have hm : AEMeasurable (fun x : Fin N → ℝ => fun j : Fin n => x (Fin.castLE hn j)) (Measure.pi ν) :=
    (measurable_pi_iff.mpr fun j => measurable_pi_apply _).aemeasurable
  have := (iIndepFun_iff_map_fun_eq_pi_map (μ := Measure.pi ν)
    (f := fun (j : Fin n) (x : Fin N → ℝ) => x (Fin.castLE hn j))
    (fun j => (measurable_pi_apply _).aemeasurable)).1 hind'
  have hmap : ∀ j : Fin n, (Measure.pi ν).map (fun x : Fin N → ℝ => x (Fin.castLE hn j)) =
      ν (Fin.castLE hn j) := fun j => (measurePreserving_eval ν (Fin.castLE hn j)).map_eq
  simp_rw [hmap] at this
  rw [← integral_map hm hg.aestronglyMeasurable]
  exact congrArg (fun μ => ∫ y, g y ∂μ) this

theorem s21h2_s15c_aemeas_Qn (hξ : IsStdGaussianSeq P ξ) (lam : ℕ → ℝ) (N : ℕ) :
    AEMeasurable (s21h2_s15c_Qn ξ lam N) P := by
  have hj : ∀ j ∈ Finset.range N,
      AEStronglyMeasurable (fun ω => lam j * (ξ j ω ^ 2 - 1)) P := fun j _ =>
    (((hξ.aemeasurable j).pow_const 2).sub_const 1).const_mul (lam j) |>.aestronglyMeasurable
  have hs := Finset.aestronglyMeasurable_sum (Finset.range N) hj
  have h : AEStronglyMeasurable (s21h2_s15c_Qn ξ lam N) P := by
    unfold s21h2_s15c_Qn
    simpa only [Finset.sum_apply] using hs.const_mul (1/2 : ℝ)
  exact h.aemeasurable

theorem s21h2_s15c_tilt_marg (hξ : IsStdGaussianSeq P ξ) (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    {γ : ℝ} (hγ : 0 ≤ γ) {n N : ℕ} (hn : n ≤ N) {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    ∫ ω, g (fun j : Fin n => ξ j ω) ∂(r26t3_tilt P (fun ω => γ * s21h2_s15c_Qn ξ lam N ω)) =
      ∫ y : Fin n → ℝ, g y ∂(Measure.pi fun j : Fin n => gaussianReal 0 ((1 + γ * lam j)⁻¹).toNNReal) := by
  obtain ⟨hint, hval⟩ := s21h2_s15c_Eexp hξ lam hlam hγ N
  have hV : AEMeasurable (fun ω => γ * s21h2_s15c_Qn ξ lam N ω) P :=
    (s21h2_s15c_aemeas_Qn hξ lam N).const_mul γ
  rw [r26t3_tilt_integral P hV hint (fun ω => g (fun j : Fin n => ξ j ω))]
  set v : (Fin N → ℝ) → ℝ := fun x => (γ / 2) * ∑ j : Fin N, lam j * (x j ^ 2 - 1) with hv
  have hvc : Continuous v := by rw [hv]; fun_prop
  have hexp : ∀ ω, Real.exp (-(γ * s21h2_s15c_Qn ξ lam N ω)) = Real.exp (-v (Zvec ξ N ω)) := fun ω => by
    rw [s21h2_s15c_Qn_eq lam N γ]
  have hexp' : ∀ ω, Real.exp (-(γ * s21h2_s15c_Qn ξ lam N ω)) = Real.exp (-v (Zvec ξ N ω)) := hexp
  let G : (Fin N → ℝ) → ℝ := fun x => g (fun j : Fin n => x (Fin.castLE hn j))
  have hG : Continuous G := hg.comp (by fun_prop)
  have hY : ∀ ω, g (fun j : Fin n => ξ j ω) = G (Zvec ξ N ω) := fun ω => rfl
  have h2 := (r26t3_finite_gaussian_tilt N (fun j : Fin N => lam j) (fun j => hlam j) γ hγ)
  have h2' : r26t3_tilt (gpi N) v = Measure.pi (fun j : Fin N => gaussianReal 0 ((1 + γ * lam j)⁻¹).toNNReal) :=
    h2.2
  have hvint : Integrable (fun x => Real.exp (-v x)) (gpi N) := by
    have h1 := (s21h2_s15c_Eexp hξ lam hlam hγ N).1
    simp_rw [hexp'] at h1
    rw [← map_Zvec hξ N] at *
    exact (integrable_map_measure (hvc.neg.rexp.aestronglyMeasurable) (aemeasurable_Zvec hξ N)).2 h1
  have h3 := r26t3_tilt_integral (P := gpi N) (V := v) hvc.aemeasurable hvint G
  rw [h2'] at h3
  have h4 := s21h2_s15c_marginal hn (fun j : Fin N => gaussianReal 0 ((1 + γ * lam j)⁻¹).toNNReal) hg
  have hZ : ∫ x, Real.exp (-v x) ∂(gpi N) = ∫ ω, Real.exp (-(γ * s21h2_s15c_Qn ξ lam N ω)) ∂P := by
    simp_rw [hexp']
    exact (integral_comp_Zvec hξ N hvc.neg.rexp).symm
  have hGint : ∫ x, G x * Real.exp (-v x) ∂(gpi N) =
      ∫ ω, g (fun j : Fin n => ξ j ω) * Real.exp (-(γ * s21h2_s15c_Qn ξ lam N ω)) ∂P := by
    simp_rw [hexp', hY]
    exact (integral_comp_Zvec hξ N (hG.mul hvc.neg.rexp)).symm
  rw [← hGint, ← hZ, ← h3]
  rw [h4]
  rfl

end Fin

end HRS.MS.R26T3
