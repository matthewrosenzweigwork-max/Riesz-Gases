import HRS.MS.PROS15dPhysicalRieszProjectionP21
import HRS.MS.S21H2_S14aD4

/-!
# S15d: spectral Hilbert-basis approximations in physical spatial L²

For the actual S14a eigenbasis of centered spatial L², the finite sums
of *physical representatives* converge to each centered L² observable.
This supplies the missing spatial approximation premise of the C19
Gaussian-law continuity theorem, without assuming spectral smoothness.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_physical_hilbert_spatial_projection_L2
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ j, MemLp (e j) 2 μ)
    (b : HilbertBasis ℕ ℝ (s21h2_V μ))
    (hb : ∀ j, ((b j : s21h2_V μ) : Lp ℝ 2 μ) =
      (he j).toLp (e j))
    (v : s21h2_V μ) :
    Tendsto (fun n =>
      ∫ x, ((∑ j ∈ Finset.range n, inner ℝ (b j) v * e j x) -
        (((v : s21h2_V μ) : Lp ℝ 2 μ) x)) ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  let s : ℕ → s21h2_V μ := fun n =>
    ∑ j ∈ Finset.range n, inner ℝ (b j) v • b j
  let f : HRS.Euc d → ℝ := fun x =>
    (((v : s21h2_V μ) : Lp ℝ 2 μ) x)
  let u : ℕ → HRS.Euc d → ℝ := fun n x =>
    ∑ j ∈ Finset.range n, inner ℝ (b j) v * e j x
  have hf : MemLp f 2 μ := Lp.memLp _
  have hu : ∀ n, MemLp (u n) 2 μ := by
    intro n
    exact memLp_finsetSum _ (fun j _ => (he j).const_mul _)
  have hSum : ∀ n, ((s n : s21h2_V μ) : Lp ℝ 2 μ) =ᵐ[μ] u n := by
    intro n
    have hsame :
        ((s n : s21h2_V μ) : Lp ℝ 2 μ) =
          ∑ j ∈ Finset.range n, inner ℝ (b j) v •
            ((b j : s21h2_V μ) : Lp ℝ 2 μ) := by
      simp only [s, Submodule.coe_sum, Submodule.coe_smul]
    rw [hsame]
    have hbasis : ∀ j, (((b j : s21h2_V μ) : Lp ℝ 2 μ) :
        HRS.Euc d → ℝ) =ᵐ[μ] e j := by
      intro j
      rw [hb j]
      exact (he j).coeFn_toLp
    filter_upwards [
      s21h2_coeFn_finsum
        (fun j => inner ℝ (b j) v)
        (fun j => ((b j : s21h2_V μ) : Lp ℝ 2 μ))
        (Finset.range n),
      ae_all_iff.2 hbasis] with x h1 h2
    simp only [u] at *
    rw [h1]
    exact Finset.sum_congr rfl (fun j hj => by rw [h2 j])
  have hLp : ∀ n, (hu n).toLp (u n) =
      ((s n : s21h2_V μ) : Lp ℝ 2 μ) := by
    intro n
    apply Lp.ext
    filter_upwards [(hu n).coeFn_toLp, hSum n] with x h1 h2
    exact h1.trans h2.symm
  have hD : ∀ n, MemLp (fun x => u n x - f x) 2 μ :=
    fun n => (hu n).sub hf
  have hDiff : ∀ n,
      (hD n).toLp (fun x => u n x - f x) =
        (((s n - v : s21h2_V μ) : Lp ℝ 2 μ)) := by
    intro n
    change (hD n).toLp (fun x => u n x - f x) =
      (((s n : s21h2_V μ) : Lp ℝ 2 μ) -
        ((v : s21h2_V μ) : Lp ℝ 2 μ))
    apply Lp.ext
    filter_upwards [
      (hD n).coeFn_toLp,
      Lp.coeFn_sub ((s n : s21h2_V μ) : Lp ℝ 2 μ)
        ((v : s21h2_V μ) : Lp ℝ 2 μ),
      hSum n] with x h1 h2 h3
    simp only [Pi.sub_apply] at *
    rw [h1, h2, h3]
  have hSq : ∀ n,
      (∫ x, (u n x - f x) ^ 2 ∂μ) =
        ‖s n - v‖ ^ 2 := by
    intro n
    calc
      (∫ x, (u n x - f x) ^ 2 ∂μ) =
          inner ℝ ((hD n).toLp (fun x => u n x - f x))
            ((hD n).toLp (fun x => u n x - f x)) := by
              rw [s21h2_L2_inner (hD n) (hD n)]
              apply integral_congr_ae
              exact ae_of_all _ (fun x => by ring)
      _ = ‖s n - v‖ ^ 2 := by
            rw [hDiff, real_inner_self_eq_norm_sq]
            rfl
  have hHas : HasSum
      (fun j => inner ℝ (b j) v • b j) v := by
    simpa only [b.repr_apply_apply] using b.hasSum_repr v
  have hT : Tendsto s atTop (𝓝 v) := by
    simpa only [s] using hHas.tendsto_sum_nat
  have hNorm : Tendsto (fun n => ‖s n - v‖ ^ 2)
      atTop (𝓝 0) := by
    have ht := (hT.sub (tendsto_const_nhds (x := v))).norm
    have hpow := ht.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using hpow
  simpa only [hSq, u, f] using hNorm

#print axioms s15d_physical_hilbert_spatial_projection_L2
end HRS.MS.R26T3
