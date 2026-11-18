import HRS.MS.PROS13QuadraticLimit
import HRS.MS.S21T4ProdZ

/-!
# S13: an L² convergent kernel sequence is Cauchy in squared-integral distance

Works for every probability measure on Euclidean space. The entire
statement concerns actual kernels rather than a choice of orthonormal basis.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_kernel_cauchy_of_L2_approx
    (h : Euc d → Euc d → ℝ)
    (hj : ℕ → Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hhj : ∀ j, MemLp (fun z : Euc d × Euc d => hj j z.1 z.2) 2 (μ.prod μ))
    (hT : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d => hj j z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ m ≥ J, ∀ n ≥ J,
      ∫ z : Euc d × Euc d,
        (hj m z.1 z.2 - hj n z.1 z.2) ^ 2 ∂(μ.prod μ) < ε := by
  let ν := μ.prod μ
  let f : ℕ → Euc d × Euc d → ℝ :=
    fun j z => hj j z.1 z.2 - h z.1 z.2
  have hf : ∀ j, MemLp (f j) 2 ν := fun j => (hhj j).sub hh
  have hconv : Tendsto (fun j => ∫ z, (f j z) ^ 2 ∂ν) atTop (𝓝 0) :=
    s21t4_integral_sq_tendsto_zero f hf hT
  intro ε hε
  have hδ : (0 : ℝ) < ε / 8 := by positivity
  have hsmall : ∀ᶠ j in atTop, (∫ z, (f j z) ^ 2 ∂ν) < ε / 8 :=
    hconv.eventually (Iio_mem_nhds hδ)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨J, fun m hm n hn => ?_⟩
  have hfm := (hf m).integrable_sq
  have hfn := (hf n).integrable_sq
  have hdiff : Integrable (fun z => (f m z - f n z) ^ 2) ν :=
    ((hf m).sub (hf n)).integrable_sq
  have hdom : Integrable (fun z => 2 * (f m z) ^ 2 + 2 * (f n z) ^ 2) ν :=
    (hfm.const_mul 2).add (hfn.const_mul 2)
  have hle : (∫ z, (f m z - f n z) ^ 2 ∂ν) ≤
      2 * ∫ z, (f m z) ^ 2 ∂ν +
        2 * ∫ z, (f n z) ^ 2 ∂ν := by
    have hbd : ∀ z, (f m z - f n z) ^ 2 ≤
        2 * (f m z) ^ 2 + 2 * (f n z) ^ 2 := by
      intro z
      nlinarith [sq_nonneg (f m z + f n z)]
    have h := integral_mono hdiff hdom hbd
    rw [integral_add (hfm.const_mul 2) (hfn.const_mul 2),
      integral_const_mul, integral_const_mul] at h
    exact h
  have hm' := hJ m hm
  have hn' := hJ n hn
  calc
    (∫ z : Euc d × Euc d,
       (hj m z.1 z.2 - hj n z.1 z.2) ^ 2 ∂(μ.prod μ))
        = (∫ z, (f m z - f n z) ^ 2 ∂ν) := by
            apply integral_congr_ae
            exact ae_of_all _ fun z => by dsimp [f]; ring
    _ < ε := by linarith

end HRS.MS.R26T3
