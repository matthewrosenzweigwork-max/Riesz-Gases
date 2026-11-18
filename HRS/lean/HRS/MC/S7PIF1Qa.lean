import HRS.Energy.Commutator.AbsConv
import HRS.Energy.Modulated

/-!
# Packet piF1 (F2), part a: termwise expansion of the modulated energy

For a kernel `G ∈ L¹(𝕋^d; ℝ^d)` and a measure `μ = ρ dx` with bounded density, a family of pair kernels `u_k` with
`|u_k(x,y)| ≤ w_k ‖G(x - y)‖`, `∑ w_k < ∞`, and `∑_k u_k(x,y) = U(x,y)` pointwise, the modulated energy is
expanded termwise: `F^U_N(X,μ) = ∑_k F^{u_k}_N(X,μ)` (`S7PIF1_modEnergy_hasSum`), and `|F^h_N| ≤ A Γ` if `|h| ≤ A ‖G(x - y)‖`
(`S7PIF1_modEnergy_bound`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF1

open HRS

variable {d : ℕ} {G : Torus d → Euc d}

/-- `μ = ρ dx` integrates `‖G(c - ·)‖` and `‖G(· - c)‖`, with the bound `B ∫‖G‖`. -/
theorem S7PIF1_normG_mu {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B)
    (hG : Integrable G) (c : Torus d) :
    Integrable (fun y => ‖G (c - y)‖) (withDensityReal ρ) ∧
    Integrable (fun y => ‖G (y - c)‖) (withDensityReal ρ) ∧
    ∫ y, ‖G (c - y)‖ ∂(withDensityReal ρ) ≤ B * ∫ z, ‖G z‖ := by
  have h1 : Integrable (fun y => ‖G (c - y)‖) (volume : Measure (Torus d)) := hG.norm.comp_sub_left c
  have h2 : Integrable (fun y => ‖G (y - c)‖) (volume : Measure (Torus d)) := hG.norm.comp_sub_right c
  refine ⟨HRS.Commutator.absConv_integrable_mu hB h1, HRS.Commutator.absConv_integrable_mu hB h2, ?_⟩
  have := HRS.Commutator.absConv_integral_mu_le hB hB0 (g := fun y => ‖G (c - y)‖) (fun y => norm_nonneg _) h1
  rwa [integral_sub_left_eq_self (fun z => ‖G z‖) (volume : Measure (Torus d)) c] at this

section Fibre

variable {ρ : Torus d → ℝ} {B : ℝ} {h : Torus d → Torus d → ℝ} {A : ℝ}

/-- Fibre integrability and bounds for a pair kernel dominated by `A ‖G(x - y)‖`. -/
theorem S7PIF1_fibre (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B) (hG : Integrable G) (hA : 0 ≤ A)
    (hm : Measurable (fun p : Torus d × Torus d => h p.1 p.2))
    (hb : ∀ x y, |h x y| ≤ A * ‖G (x - y)‖) :
    (∀ x, Integrable (h x) (withDensityReal ρ)) ∧
    (∀ c, Integrable (fun x => h x c) (withDensityReal ρ)) ∧
    (∀ x, ∫ y, ‖h x y‖ ∂(withDensityReal ρ) ≤ A * (B * ∫ z, ‖G z‖)) := by
  refine ⟨fun x => ?_, fun c => ?_, fun x => ?_⟩
  · refine Integrable.mono' ((S7PIF1_normG_mu hB hB0 hG x).1.const_mul A) hm.of_uncurry_left.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    simpa [Real.norm_eq_abs] using hb x y
  · refine Integrable.mono' ((S7PIF1_normG_mu hB hB0 hG c).2.1.const_mul A)
      hm.of_uncurry_right.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    simpa [Real.norm_eq_abs] using hb y c
  · have hi : Integrable (fun y => ‖h x y‖) (withDensityReal ρ) := by
      refine Integrable.mono' ((S7PIF1_normG_mu hB hB0 hG x).1.const_mul A)
        hm.of_uncurry_left.aestronglyMeasurable.norm (Filter.Eventually.of_forall fun y => ?_)
      simpa [Real.norm_eq_abs] using hb x y
    calc ∫ y, ‖h x y‖ ∂(withDensityReal ρ) ≤ ∫ y, A * ‖G (x - y)‖ ∂(withDensityReal ρ) :=
          integral_mono hi ((S7PIF1_normG_mu hB hB0 hG x).1.const_mul A) fun y => by
            simpa [Real.norm_eq_abs] using hb x y
      _ = A * ∫ y, ‖G (x - y)‖ ∂(withDensityReal ρ) := integral_const_mul _ _
      _ ≤ A * (B * ∫ z, ‖G z‖) :=
          mul_le_mul_of_nonneg_left (S7PIF1_normG_mu hB hB0 hG x).2.2 hA

/-- The inner integral `x ↦ ∫ h x y dμ(y)` is measurable and bounded by `A K`. -/
theorem S7PIF1_inner (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B) (hG : Integrable G) (hA : 0 ≤ A)
    (hm : Measurable (fun p : Torus d × Torus d => h p.1 p.2))
    (hb : ∀ x y, |h x y| ≤ A * ‖G (x - y)‖) :
    StronglyMeasurable (fun x => ∫ y, h x y ∂(withDensityReal ρ)) ∧
    ∀ x, |∫ y, h x y ∂(withDensityReal ρ)| ≤ A * (B * ∫ z, ‖G z‖) := by
  refine ⟨?_, fun x => ?_⟩
  · have : IsFiniteMeasure (withDensityReal ρ) := HRS.Commutator.absConv_isFiniteMeasure hB
    exact (hm.stronglyMeasurable).integral_prod_right' (ν := withDensityReal ρ)
  · have h3 := (S7PIF1_fibre hB hB0 hG hA hm hb).2.2 x
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans h3

end Fibre

section Energy

variable {ρ : Torus d → ℝ} {B : ℝ} {N : ℕ}

/-- The constant of the bound `|F^h_N(X,μ)| ≤ A Γ` for `|h| ≤ A ‖G(x - y)‖`. -/
def S7PIF1_Gamma (G : Torus d → Euc d) (B : ℝ) (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖G (X i - X j)‖
    + (B * ∫ z, ‖G z‖) + (1 / 2) * ((B * ∫ z, ‖G z‖) * (withDensityReal ρ).real Set.univ)

theorem S7PIF1_Gamma_nonneg (hB0 : 0 ≤ B) (X : Config d N) : 0 ≤ S7PIF1_Gamma G B ρ X := by
  unfold S7PIF1_Gamma
  have h1 : 0 ≤ ∫ z, ‖G z‖ := integral_nonneg fun z => norm_nonneg _
  have h2 : 0 ≤ (withDensityReal ρ).real Set.univ := measureReal_nonneg
  positivity

/-- `|F^h_N(X,μ)| ≤ A Γ` for a pair kernel dominated by `A ‖G(x - y)‖`. -/
theorem S7PIF1_modEnergy_bound (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B) (hG : Integrable G) {A : ℝ}
    (hA : 0 ≤ A) {h : Torus d → Torus d → ℝ}
    (hm : Measurable (fun p : Torus d × Torus d => h p.1 p.2))
    (hb : ∀ x y, |h x y| ≤ A * ‖G (x - y)‖) (X : Config d N) :
    |modulatedEnergy h X (withDensityReal ρ)| ≤ A * S7PIF1_Gamma G B ρ X := by
  have hfin : IsFiniteMeasure (withDensityReal ρ) := HRS.Commutator.absConv_isFiniteMeasure hB
  obtain ⟨hsm, hI⟩ := S7PIF1_inner hB hB0 hG hA hm hb
  set K : ℝ := B * ∫ z, ‖G z‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg hB0 (integral_nonneg fun z => norm_nonneg _)
  have t1 : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)|
      ≤ A * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖G (X i - X j)‖) := by
    have hc : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
    rw [abs_mul, abs_of_nonneg hc]
    have : |∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)|
        ≤ A * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖G (X i - X j)‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hb _ _
    calc 1 / (2 * (N : ℝ) ^ 2) * |∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)|
        ≤ 1 / (2 * (N : ℝ) ^ 2) * (A * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖G (X i - X j)‖) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have t2 : |(1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ)| ≤ A * K := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp; positivity
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have : |∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ)| ≤ N * (A * K) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |∫ y, h (X i) y ∂(withDensityReal ρ)| ≤ ∑ _i : Fin N, (A * K) :=
              Finset.sum_le_sum fun i _ => hI (X i)
          _ = N * (A * K) := by simp
      calc 1 / (N : ℝ) * |∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ)| ≤ 1 / (N : ℝ) * (N * (A * K)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = A * K := by field_simp
  have t3 : |(1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)|
      ≤ A * ((1 / 2) * (K * (withDensityReal ρ).real Set.univ)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have : ‖∫ x, ∫ y, h x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)‖
        ≤ (A * K) * (withDensityReal ρ).real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hI x)
    rw [Real.norm_eq_abs] at this
    calc 1 / 2 * |∫ x, ∫ y, h x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)|
        ≤ 1 / 2 * ((A * K) * (withDensityReal ρ).real Set.univ) :=
          mul_le_mul_of_nonneg_left this (by norm_num)
      _ = _ := by ring
  unfold modulatedEnergy S7PIF1_Gamma
  calc _ ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)|
          + |(1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ)|
          + |(1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by
        refine (add_le_add (add_le_add t1 t2) t3).trans (le_of_eq ?_)
        rw [← hK]; ring

end Energy

section Series

variable {ρ : Torus d → ℝ} {B : ℝ} {N : ℕ} {ι : Type*} [Countable ι]

/-- Termwise expansion of the modulated energy along a pointwise absolutely dominated series of pair kernels. -/
theorem S7PIF1_modEnergy_hasSum (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B) (hG : Integrable G)
    (u : ι → Torus d → Torus d → ℝ) (U : Torus d → Torus d → ℝ) (w : ι → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hw : Summable w)
    (hum : ∀ k, Measurable (fun p : Torus d × Torus d => u k p.1 p.2))
    (hub : ∀ k x y, |u k x y| ≤ w k * ‖G (x - y)‖)
    (hUs : ∀ x y, HasSum (fun k => u k x y) (U x y)) (X : Config d N) :
    HasSum (fun k => modulatedEnergy (u k) X (withDensityReal ρ)) (modulatedEnergy U X (withDensityReal ρ)) := by
  have hfin : IsFiniteMeasure (withDensityReal ρ) := HRS.Commutator.absConv_isFiniteMeasure hB
  set μ := withDensityReal ρ with hμ
  set K : ℝ := B * ∫ z, ‖G z‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg hB0 (integral_nonneg fun z => norm_nonneg _)
  have hfib := fun k => S7PIF1_fibre hB hB0 hG (hw0 k) (hum k) (hub k)
  have hinn := fun k => S7PIF1_inner hB hB0 hG (hw0 k) (hum k) (hub k)
  -- inner integrals
  have step2 : ∀ x, HasSum (fun k => ∫ y, u k x y ∂μ) (∫ y, U x y ∂μ) := by
    intro x
    have hsum : Summable fun k => ∫ y, ‖u k x y‖ ∂μ :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
        (fun k => (hfib k).2.2 x) (hw.mul_right K)
    have := hasSum_integral_of_summable_integral_norm (μ := μ) (F := fun k y => u k x y)
      (fun k => (hfib k).1 x) hsum
    have e : ∀ y, ∑' k, u k x y = U x y := fun y => (hUs x y).tsum_eq
    simpa only [e] using this
  -- outer integrals
  have step3 : HasSum (fun k => ∫ x, ∫ y, u k x y ∂μ ∂μ) (∫ x, ∫ y, U x y ∂μ ∂μ) := by
    have hint : ∀ k, Integrable (fun x => ∫ y, u k x y ∂μ) μ := fun k =>
      Integrable.mono' (integrable_const (w k * K)) (hinn k).1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hinn k).2 x)
    have hsum : Summable fun k => ∫ x, ‖∫ y, u k x y ∂μ‖ ∂μ := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
        (fun k => ?_) (hw.mul_right (K * μ.real Set.univ))
      calc ∫ x, ‖∫ y, u k x y ∂μ‖ ∂μ ≤ ∫ _x, w k * K ∂μ :=
            integral_mono (hint k).norm (integrable_const _) fun x => by
              rw [Real.norm_eq_abs]; exact (hinn k).2 x
        _ = w k * (K * μ.real Set.univ) := by
            rw [integral_const, smul_eq_mul]; ring
    have := hasSum_integral_of_summable_integral_norm (μ := μ) (F := fun k x => ∫ y, u k x y ∂μ) hint hsum
    have e : ∀ x, ∑' k, ∫ y, u k x y ∂μ = ∫ y, U x y ∂μ := fun x => (step2 x).tsum_eq
    simpa only [e] using this
  -- the three terms
  have h1 : HasSum (fun k => (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, u k (X i) (X j))
      ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, U (X i) (X j)) :=
    (hasSum_sum fun i _ => hasSum_sum fun j _ => hUs (X i) (X j)).mul_left _
  have h2 : HasSum (fun k => (1 / (N : ℝ)) * ∑ i, ∫ y, u k (X i) y ∂μ)
      ((1 / (N : ℝ)) * ∑ i, ∫ y, U (X i) y ∂μ) :=
    (hasSum_sum fun i _ => step2 (X i)).mul_left _
  have h3 := step3.mul_left (1 / 2 : ℝ)
  exact (h1.sub h2).add h3

end Series

end HRS.MC.Sec7.S7PIF1

end
