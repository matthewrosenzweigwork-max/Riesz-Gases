import HRS.MC.SEdgeB8bAux8

/-!
# Packet B8b, helper file 9: the Hilbert-space bridge (covariances and Hilbert-Schmidt pairings)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

open HRS HRS.Sec7 HRS.Q08 HRS.ResponseAux InnerProductSpace

section Bridge

variable {d : ℕ} (D : Q08Data d)

theorem b8b_memLp_phi (a : Fin D.p) : MemLp (D.φ a) 2 (withDensityReal D.ρ) := by
  have : IsProbabilityMeasure (withDensityReal D.ρ) := isProbabilityMeasure_dens D.hρ.density
  obtain ⟨hm, M, hM⟩ := D.hφ a
  exact MemLp.of_bound hm.aestronglyMeasurable M (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hM x)

theorem b8b_inner_sum_sum (L : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (E U : ℕ → H) (w w' : H) :
    inner ℝ (∑ k ∈ Finset.range L, inner ℝ (E k) w • E k)
        (∑ l ∈ Finset.range L, inner ℝ (E l) w' • U l) =
      ∑ k ∈ Finset.range L, ∑ l ∈ Finset.range L,
        inner ℝ (E k) w * inner ℝ (E l) w' * inner ℝ (E k) (U l) := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem b8b_CL_tendsto (a b : Fin D.p) :
    Tendsto (fun L => b8b_CL (fun a k => D.coef a k) (fun i j => D.Cmat i j) L a b) atTop
      (𝓝 (susceptibilityCov (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.φ a) (D.φ b))) := by
  have A := q08s_abs D
  have hφa := b8b_memLp_phi D a
  have hφb := b8b_memLp_phi D b
  obtain ⟨hu0, hueq⟩ := b8b_resp_hyp D hφb
  have hX := b8b_Pi_proj_tendsto A (E := q08s_E D) (U := q08s_U D) (hφa.toLp (D.φ a))
  have hY := b8b_Y_tendsto A hu0 hueq (E := q08s_E D) (U := q08s_U D) (w := hφb.toLp (D.φ b))
  have h := Filter.Tendsto.inner (𝕜 := ℝ) hX hY
  rw [b8b_cov_eq D hφa hφb]
  refine h.congr fun L => ?_
  unfold b8b_Pi b8b_Y b8b_CL
  rw [b8b_inner_sum_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← b8b_coef_eq D hφa k, ← b8b_coef_eq D hφb l, ← q08s_Cmat_eq D k l]
  rfl

theorem b8b_coe_comb (L : ℕ) (t : ℕ → ℝ) :
    ⇑(∑ i ∈ Finset.range L, t i • q08s_E D i) =ᵐ[withDensityReal D.ρ]
      fun x => ∑ i ∈ Finset.range L, t i * D.e i x := by
  have h1 := Lp.coeFn_finsetSum (Finset.range L) (fun i => t i • q08s_E D i)
  have h4 : ∀ᵐ x ∂(withDensityReal D.ρ), ∀ i, ((t i • q08s_E D i : Lp ℝ 2 (withDensityReal D.ρ)) :
      Torus d → ℝ) x = t i * D.e i x := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (t i) (q08s_E D i), q08s_E_coe D i] with x a b
    rw [a]; simp [b]
  filter_upwards [h1, h4] with x a b
  rw [a]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => b i

theorem b8b_Hf_comb (L : ℕ) (t t' : ℕ → ℝ) :
    b8b_Hf (withDensityReal D.ρ) D.h (⇑(∑ i ∈ Finset.range L, t i • q08s_E D i))
        (⇑(∑ j ∈ Finset.range L, t' j • q08s_E D j)) =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, D.Hmat i j * t i * t' j := by
  have : IsProbabilityMeasure (withDensityReal D.ρ) := isProbabilityMeasure_dens D.hρ.density
  rw [b8b_Hf_congr (b8b_coe_comb D L t) (b8b_coe_comb D L t')]
  unfold b8b_Hf
  have hk := q08s_h_memLp D
  have hint : ∀ i j, Integrable (fun z : Torus d × Torus d => D.h z.1 z.2 * D.e i z.1 * D.e j z.2)
      ((withDensityReal D.ρ).prod (withDensityReal D.ρ)) := fun i j =>
    q08s_kernel_tensor_int D D.h hk i j
  have e1 : ∀ z : Torus d × Torus d, D.h z.1 z.2 * (∑ i ∈ Finset.range L, t i * D.e i z.1) *
      (∑ j ∈ Finset.range L, t' j * D.e j z.2) = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        (t i * t' j) * (D.h z.1 z.2 * D.e i z.1 * D.e j z.2) := by
    intro z
    conv_lhs => arg 1; rw [Finset.mul_sum]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e1]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_prod _ (hint i j)]
  unfold Q08Data.Hmat
  rw [show D.μ = withDensityReal D.ρ from rfl]
  ring

theorem b8b_Theta_tendsto (b c : Fin D.p) :
    Tendsto (fun L => b8b_Theta (fun a k => D.coef a k) (fun i j => D.Cmat i j)
        (fun i j => D.Hmat i j) L b c) atTop
      (𝓝 (∫ x, ∫ y, D.h x y *
          responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.φ b) x *
          responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.φ c) y
          ∂(withDensityReal D.ρ) ∂(withDensityReal D.ρ))) := by
  have : IsProbabilityMeasure (withDensityReal D.ρ) := isProbabilityMeasure_dens D.hρ.density
  have A := q08s_abs D
  have hφb := b8b_memLp_phi D b
  have hφc := b8b_memLp_phi D c
  obtain ⟨hub0, hubeq⟩ := b8b_resp_hyp D hφb
  obtain ⟨huc0, huceq⟩ := b8b_resp_hyp D hφc
  have hvb := b8b_PiY_tendsto A hub0 hubeq (E := q08s_E D) (U := q08s_U D) (w := hφb.toLp (D.φ b))
  have hvc := b8b_PiY_tendsto A huc0 huceq (E := q08s_E D) (U := q08s_U D) (w := hφc.toLp (D.φ c))
  have h := b8b_Hf_tendsto (μ := withDensityReal D.ρ) (k := D.h) (q08s_h_memLp D) hvb hvc
  have hT : ∀ (e : Fin D.p) (he : MemLp (D.φ e) 2 (withDensityReal D.ρ)) (L i : ℕ),
      inner ℝ (b8b_Pi (q08s_E D) L (he.toLp (D.φ e))) (q08s_U D i) =
        b8b_T (fun a k => D.coef a k) (fun i j => D.Cmat i j) L e i := by
    intro e he L i
    unfold b8b_Pi b8b_T
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, ← b8b_coef_eq D he k, ← q08s_Cmat_eq D k i]
    rfl
  have e1 : ∀ L, b8b_Hf (withDensityReal D.ρ) D.h
      (⇑(∑ i ∈ Finset.range L, inner ℝ (b8b_Pi (q08s_E D) L (hφb.toLp (D.φ b))) (q08s_U D i) •
        q08s_E D i)) (⇑(∑ i ∈ Finset.range L, inner ℝ (b8b_Pi (q08s_E D) L (hφc.toLp (D.φ c)))
          (q08s_U D i) • q08s_E D i)) =
      b8b_Theta (fun a k => D.coef a k) (fun i j => D.Cmat i j) (fun i j => D.Hmat i j) L b c := by
    intro L
    rw [b8b_Hf_comb]
    simp_rw [hT b hφb, hT c hφc]
    unfold b8b_Theta
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rfl
  simp_rw [e1] at h
  have hrb := (b8b_resp D hφb).1
  have hrc := (b8b_resp D hφc).1
  have e2 : b8b_Hf (withDensityReal D.ρ) D.h
      (⇑((b8b_resp D hφb).1.toLp _ : Lp ℝ 2 (withDensityReal D.ρ)))
      (⇑((b8b_resp D hφc).1.toLp _ : Lp ℝ 2 (withDensityReal D.ρ))) =
      ∫ x, ∫ y, D.h x y *
          responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.φ b) x *
          responseInverse (periodicRiesz d D.s) (withDensityReal D.ρ) D.β (D.φ c) y
          ∂(withDensityReal D.ρ) ∂(withDensityReal D.ρ) := by
    rw [b8b_Hf_congr hrb.coeFn_toLp hrc.coeFn_toLp]
    unfold b8b_Hf
    have hk : MemLp (fun z : Torus d × Torus d => D.h z.1 z.2) 2
        ((withDensityReal D.ρ).prod (withDensityReal D.ρ)) := q08s_h_memLp D
    rw [integral_prod _ (b8b_Hf_int hk hrb hrc)]
  rw [← e2]
  exact h

end Bridge
