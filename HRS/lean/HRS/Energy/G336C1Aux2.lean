import HRS.Energy.G336C1Aux1
import HRS.Energy.Commutator.AbsConv

/-!
# G336C1, helper file 2: the commutator quantity along a `GoodKernel` family

For `GoodKernel`s `G_n → G` (pointwise off `0`, same constant `C`), a Lipschitz field `v` and a bounded density
`ρ ≤ Λ`, `commQuantityWith G_n v X (ρ) → commQuantityWith G v X ρ` for a collision-free `X` (dominated
convergence), and `|commQuantityWith G v X ρ| ≤ B` with `B` depending only on `d, s, C, L, Λ, N` and a lower bound `a`
for `‖X i - X j‖`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- Domination of the symmetrised kernel by a function of `x - y`. -/
def g336c1_W (s C L : ℝ) (d : ℕ) (z : Torus d) : ℝ := L * C * (‖z‖ ^ (-s) + d)

theorem g336c1_W_nonneg {s C L : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (z : Torus d) : 0 ≤ g336c1_W s C L d z := by
  unfold g336c1_W
  have := Real.rpow_nonneg (norm_nonneg z) (-s)
  positivity

theorem g336c1_W_integrable {s C L : ℝ} (hd : 1 ≤ d) (hsd : s < d) :
    Integrable (g336c1_W s C L d) (volume : Measure (Torus d)) := by
  unfold g336c1_W
  exact ((KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const _)).const_mul _

theorem g336c1_commKernel_le {s C L : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    {v : Torus d → Euc d} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (x y : Torus d) :
    |commKernel G v x y| ≤ g336c1_W s C L d (x - y) := by
  by_cases hxy : x = y
  · subst hxy
    unfold commKernel
    rw [if_pos rfl, abs_zero]
    exact g336c1_W_nonneg hL hG.hC0 _
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    unfold commKernel
    rw [if_neg hxy]
    calc |inner ℝ (v x - v y) (G (x - y))| ≤ ‖v x - v y‖ * ‖G (x - y)‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * KernelGrad.tdist x y) * ‖G (x - y)‖ := by
          gcongr; exact hv x y
      _ = L * (KernelGrad.tdist (x - y) 0 * ‖G (x - y)‖) := by
          rw [KernelGrad.tdist_eq_sub_zero]; ring
      _ ≤ L * (C * (‖x - y‖ ^ (-s) + d)) :=
          mul_le_mul_of_nonneg_left (hG.norm_mul_tdist_le _ hz) hL
      _ = g336c1_W s C L d (x - y) := by unfold g336c1_W; ring

theorem g336c1_measurable_commKernel {G : Torus d → Euc d} (hG : Measurable G) {v : Torus d → Euc d}
    (hv : Continuous v) : Measurable (fun p : Torus d × Torus d => commKernel G v p.1 p.2) := by
  unfold commKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.inner ?_ ?_
  · exact (hv.measurable.comp measurable_fst).sub (hv.measurable.comp measurable_snd)
  · exact hG.comp (measurable_fst.sub measurable_snd)

theorem g336c1_abs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (B : ℝ) (h : ∀ i ∈ s, |f i| ≤ B) :
    |∑ i ∈ s, f i| ≤ (s.card : ℝ) * B := by
  calc |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum h
    _ = (s.card : ℝ) * B := by simp

section Limit

variable {s C L Λ : ℝ} {Gn : ℕ → Torus d → Euc d} {G : Torus d → Euc d}
  {v : Torus d → Euc d} {ρ : Torus d → ℝ}

/-- Row integrals converge. -/
theorem g336c1_row_tendsto (hd : 1 ≤ d) (hGn : ∀ n, KernelGrad.GoodKernel d s C (Gn n))
    (hG : KernelGrad.GoodKernel d s C G)
    (hlim : ∀ z : Torus d, z ≠ 0 → Tendsto (fun n => Gn n z) atTop (𝓝 (G z)))
    (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (hρΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    Tendsto (fun n => ∫ y, commKernel (Gn n) v x y ∂(withDensityReal ρ)) atTop
      (𝓝 (∫ y, commKernel G v x y ∂(withDensityReal ρ))) := by
  have hvc : Continuous v := Commutator.IsLipschitzVF.continuous hL hv
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hρΛ x).trans (le_max_left _ _)
  have hW := g336c1_W_integrable (s := s) (C := C) (L := L) hd hG.hsd
  have hW' : Integrable (fun y => g336c1_W s C L d (x - y)) volume := hW.comp_sub_left x
  have hsing : (withDensityReal ρ) {x} = 0 := withDensityReal_singleton hd ρ x
  have hae : ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := by
    have := measure_eq_zero_iff_ae_notMem.1 hsing
    filter_upwards [this] with y hy
    simpa using hy
  refine tendsto_integral_of_dominated_convergence (fun y => g336c1_W s C L d (x - y))
    (fun n => ((g336c1_measurable_commKernel (hGn n).meas hvc).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Commutator.absConv_integrable_mu hΛB hW') (fun n => ?_) ?_
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact g336c1_commKernel_le (hGn n) hL hv x y
  · filter_upwards [hae] with y hy
    have hxy : x ≠ y := fun h => hy h.symm
    simp only [commKernel, if_neg hxy]
    exact tendsto_const_nhds.inner (hlim (x - y) (sub_ne_zero.mpr hxy))


/-- A uniform bound for the row integrals. -/
theorem g336c1_row_bound (hd : 1 ≤ d) (hG : KernelGrad.GoodKernel d s C G)
    (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (hρΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    ‖∫ y, commKernel G v x y ∂(withDensityReal ρ)‖ ≤ max Λ 0 * ∫ z, g336c1_W s C L d z := by
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hρΛ x).trans (le_max_left _ _)
  have hW := g336c1_W_integrable (s := s) (C := C) (L := L) hd hG.hsd
  have hW' : Integrable (fun y => g336c1_W s C L d (x - y)) volume := hW.comp_sub_left x
  have h1 := norm_integral_le_of_norm_le (Commutator.absConv_integrable_mu hΛB hW')
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact g336c1_commKernel_le hG hL hv x y)
  refine h1.trans ?_
  have h2 := Commutator.absConv_integral_mu_le hΛB (le_max_right _ _)
    (fun y => g336c1_W_nonneg hL hG.hC0 _) hW'
  have h3 : ∫ y : Torus d, g336c1_W s C L d (x - y) = ∫ z, g336c1_W s C L d z :=
    integral_sub_left_eq_self (fun z : Torus d => g336c1_W s C L d z) volume x
  rw [h3] at h2
  exact h2

theorem g336c1_comm_tendsto (hd : 1 ≤ d) (hGn : ∀ n, KernelGrad.GoodKernel d s C (Gn n))
    (hG : KernelGrad.GoodKernel d s C G)
    (hlim : ∀ z : Torus d, z ≠ 0 → Tendsto (fun n => Gn n z) atTop (𝓝 (G z)))
    (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (hρΛ : ∀ x, ρ x ≤ Λ)
    (X : Config d N) (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => commQuantityWith (Gn n) v X (withDensityReal ρ)) atTop
      (𝓝 (commQuantityWith G v X (withDensityReal ρ))) := by
  have hvc : Continuous v := Commutator.IsLipschitzVF.continuous hL hv
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hρΛ x).trans (le_max_left _ _)
  haveI := Commutator.absConv_isFiniteMeasure hΛB
  unfold commQuantityWith offDiagPairing
  refine Tendsto.add (Tendsto.sub ?_ ?_) ?_
  · refine Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j hj => ?_)
    have hij : X i ≠ X j := fun h => hX ⟨i, j, (Finset.mem_erase.mp hj).1.symm, h⟩
    simp only [commKernel, if_neg hij]
    exact tendsto_const_nhds.inner (hlim (X i - X j) (sub_ne_zero.mpr hij))
  · exact Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ =>
      g336c1_row_tendsto hd hGn hG hlim hL hv hρΛ (X i))
  · refine tendsto_integral_of_dominated_convergence (fun _ => max Λ 0 * ∫ z, g336c1_W s C L d z)
      (fun n => ?_) (integrable_const _) (fun n => ?_) ?_
    · exact ((g336c1_measurable_commKernel (hGn n).meas hvc).stronglyMeasurable.integral_prod_right'
        (ν := withDensityReal ρ)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => g336c1_row_bound hd (hGn n) hL hv hρΛ x
    · exact Filter.Eventually.of_forall fun x => g336c1_row_tendsto hd hGn hG hlim hL hv hρΛ x

/-- The bound for the commutator quantity, depending on `d, s, C, L, Λ, a` only. -/
def g336c1_commB (d : ℕ) (s C L Λ a : ℝ) : ℝ :=
  L * C * (a ^ (-s) + d) + 3 * (max Λ 0 * ∫ z : Torus d, g336c1_W s C L d z)

theorem g336c1_comm_bound (hd : 1 ≤ d) (hG : KernelGrad.GoodKernel d s C G)
    (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ)
    {a : ℝ} (ha : 0 < a) (hN : 0 < N) (X : Config d N)
    (hXa : ∀ i j, i ≠ j → a ≤ ‖X i - X j‖) :
    |commQuantityWith G v X (withDensityReal ρ)| ≤ g336c1_commB d s C L Λ a := by
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hρΛ x).trans (le_max_left _ _)
  haveI := Commutator.absConv_isFiniteMeasure hΛB
  haveI := isProb_withDensityReal hρ
  set J : ℝ := ∫ z : Torus d, g336c1_W s C L d z with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun z => g336c1_W_nonneg hL hG.hC0 z
  have hΛ0 : 0 ≤ max Λ 0 := le_max_right _ _
  set W0 : ℝ := L * C * (a ^ (-s) + d) with hW0
  have hW00 : 0 ≤ W0 := by
    have := Real.rpow_nonneg ha.le (-s)
    have := hG.hC0
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 := hG.hs0
  -- T1
  have hk : ∀ i j, i ≠ j → |commKernel G v (X i) (X j)| ≤ W0 := by
    intro i j hij
    refine (g336c1_commKernel_le hG hL hv _ _).trans ?_
    unfold g336c1_W
    have hz : a ^ (-s) ≥ ‖X i - X j‖ ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos ha (hXa i j hij) (by linarith)
    have := hG.hC0
    have h2 : ‖X i - X j‖ ^ (-s) + d ≤ a ^ (-s) + d := by linarith
    exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hL this)
  have hT1 : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, commKernel G v (X i) (X j)| ≤ W0 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have hs := g336c1_abs_sum_le (Finset.univ : Finset (Fin N))
      (fun i => ∑ j ∈ Finset.univ.erase i, commKernel G v (X i) (X j)) ((N : ℝ) * W0) (fun i _ => by
        refine (g336c1_abs_sum_le _ _ W0 (fun j hj => hk i j (Finset.mem_erase.mp hj).1.symm)).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hW00
        have : (Finset.univ.erase i).card ≤ N := by
          simpa using Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
        exact_mod_cast this)
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, commKernel G v (X i) (X j)|
        ≤ 1 / (N : ℝ) ^ 2 * ((N : ℝ) * ((N : ℝ) * W0)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = W0 := by field_simp
  have hT2 : |(2 / (N : ℝ)) * ∑ i, ∫ y, commKernel G v (X i) y ∂(withDensityReal ρ)|
      ≤ 2 * (max Λ 0 * J) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have hs := g336c1_abs_sum_le (Finset.univ : Finset (Fin N))
      (fun i => ∫ y, commKernel G v (X i) y ∂(withDensityReal ρ)) (max Λ 0 * J) (fun i _ => by
        have := g336c1_row_bound hd hG hL hv hρΛ (X i)
        rwa [Real.norm_eq_abs] at this)
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    calc 2 / (N : ℝ) * |∑ i, ∫ y, commKernel G v (X i) y ∂(withDensityReal ρ)|
        ≤ 2 / (N : ℝ) * ((N : ℝ) * (max Λ 0 * J)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * (max Λ 0 * J) := by field_simp
  have hT3 : |∫ x, ∫ y, commKernel G v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)|
      ≤ max Λ 0 * J := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
      (f := fun x => ∫ y, commKernel G v x y ∂(withDensityReal ρ)) (C := max Λ 0 * J)
      (Filter.Eventually.of_forall fun x => g336c1_row_bound hd hG hL hv hρΛ x)
    rw [Real.norm_eq_abs] at this
    simpa using this
  unfold commQuantityWith offDiagPairing g336c1_commB
  have h12 := abs_sub (((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, commKernel G v (X i) (X j)))
    ((2 / (N : ℝ)) * ∑ i, ∫ y, commKernel G v (X i) y ∂(withDensityReal ρ))
  have h123 := abs_add_le (((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, commKernel G v (X i) (X j)) -
    ((2 / (N : ℝ)) * ∑ i, ∫ y, commKernel G v (X i) y ∂(withDensityReal ρ)))
    (∫ x, ∫ y, commKernel G v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ))
  have hprod : 0 ≤ max Λ 0 * J := mul_nonneg hΛ0 hJ0
  linarith

end Limit

end HRS
