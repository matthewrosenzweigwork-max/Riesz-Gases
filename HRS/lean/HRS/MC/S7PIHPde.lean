import HRS.MC.S7PIH9Pde

/-!
# Packet piH: `s7_PIH_heat_pde_proof` (backward heat equation for the finite Gaussian heat function)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

/-- **H1a (backward heat equation for `G ∈ C_b²`)**.  Let `S u = S b + ∫_{(u,b]} A` on `[a,b]` with `A` entrywise
continuous and PSD on `[a,b]` and `S b` PSD.  Then for every `c`, `r ↦ gaussHeat S G r c` is differentiable on `[a,b]`
(within `[a,b]`) with derivative `-(1/2) ∑_{ij} A(r)_{ij} E D²G(c + X_r)(e_i,e_j)`, `X_r ~ N(0, S r)`. -/
theorem s7_PIH_heat_pde_proof {q : ℕ} (a b : ℝ) (hab : a ≤ b)
    (A S : ℝ → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 2 G) (c : EuclideanSpace ℝ (Fin q)) :
    ∀ r ∈ Set.Icc a b, HasDerivWithinAt (fun s => gaussHeat S G s c)
      (-(1 / 2) * ∑ i, ∑ j, A r i j *
        ∫ x, iteratedFDeriv ℝ 2 G (c + x) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
          ∂(multivariateGaussian 0 (S r))) (Set.Icc a b) r := by
  intro r hr
  set dd : Fin q → Fin q → ℝ → ℝ := fun i j s =>
    iteratedFDeriv ℝ 2 (gaussHeat S G s) c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
    with hdd
  have hdeq : ∀ i j s, dd i j s = ∫ x, iteratedFDeriv ℝ 2 G (c + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(multivariateGaussian 0 (S s)) :=
    fun i j s => S7PIH_heat_D2_eval (multivariateGaussian 0 (S s)) hG c _
  have hrew : (∑ i, ∑ j, A r i j * ∫ x, iteratedFDeriv ℝ 2 G (c + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(multivariateGaussian 0 (S r))) =
      ∑ i, ∑ j, A r i j * dd i j r :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hdeq]
  rw [hrew, hasDerivWithinAt_iff_tendsto_slope]
  set ℱ : Filter ℝ := nhdsWithin r (Set.Icc a b \ {r}) with hℱ
  -- the remainder
  set Rem : ℝ → ℝ → ℝ := fun lo hi =>
    (gaussHeat S G lo c - gaussHeat S G hi c - (1 / 2) * ∑ i, ∑ j, (S lo - S hi) i j *
      dd i j hi) / (hi - lo) with hRem
  have hmem_min : ∀ s ∈ Set.Icc a b, min r s ∈ Set.Icc a b := fun s hs =>
    ⟨le_min hr.1 hs.1, (min_le_left _ _).trans hr.2⟩
  have hmem_max : ∀ s ∈ Set.Icc a b, max r s ∈ Set.Icc a b := fun s hs =>
    ⟨hr.1.trans (le_max_left _ _), max_le hr.2 hs.2⟩
  have hdist_min : ∀ s, |min r s - r| ≤ |s - r| := fun s => by
    rcases le_total r s with h | h
    · rw [min_eq_left h]; simp
    · rw [min_eq_right h]
  have hdist_max : ∀ s, |max r s - r| ≤ |s - r| := fun s => by
    rcases le_total r s with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h]; simp
  -- (T1) the remainder tends to 0
  have hT1 : Tendsto (fun s => Rem (min r s) (max r s)) ℱ (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨η, hη, hest⟩ := S7PIH_pair_est hab hA hApsd hSb hS hG c hr (half_pos hε)
    refine ⟨η, hη, fun s hs hsd => ?_⟩
    have hne : s ≠ r := hs.2
    have hlh : min r s < max r s := min_lt_max.2 (Ne.symm hne)
    have h1 := hest (min r s) (max r s) (hmem_min s hs.1) (hmem_max s hs.1) hlh
      (lt_of_le_of_lt (hdist_min s) (by simpa [Real.dist_eq] using hsd))
      (lt_of_le_of_lt (hdist_max s) (by simpa [Real.dist_eq] using hsd))
    have hwpos : 0 < max r s - min r s := sub_pos.2 hlh
    rw [Real.dist_eq, sub_zero]
    simp only [hRem]
    rw [abs_div, abs_of_pos hwpos, div_lt_iff₀ hwpos]
    simp only [hdd] at h1 ⊢
    linarith [mul_pos hε hwpos]
  -- (T2) averages of A
  have hT2 : ∀ i j, Tendsto (fun s => (∫ v in Set.Ioc (min r s) (max r s), A v i j) /
      (max r s - min r s)) ℱ (𝓝 (A r i j)) := by
    intro i j
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨η, hη, havg⟩ := S7PIH_avg_close (hA i j) hr (half_pos hε)
    refine ⟨η, hη, fun s hs hsd => ?_⟩
    have hne : s ≠ r := hs.2
    have hlh : min r s < max r s := min_lt_max.2 (Ne.symm hne)
    have hw : max r s - min r s < η := by
      have : max r s - min r s = |s - r| := by
        rcases le_total r s with h | h
        · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.2 h)]
        · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.2 h)]; ring
      rw [this]; simpa [Real.dist_eq] using hsd
    have := havg (min r s) (max r s) (hmem_min s hs.1).1 (hmem_max s hs.1).2 hlh
      (min_le_left _ _) (le_max_left _ _) hw
    rw [Real.dist_eq]
    linarith
  -- (T3) the Hessian entries are continuous in the time
  have hT3 : ∀ i j, Tendsto (fun s => dd i j (max r s)) ℱ (𝓝 (dd i j r)) := by
    intro i j
    have hcont := S7PIH_heat_cont_ab hab hA hApsd hSb hS hG (le_refl 2)
    have hmaps : Set.MapsTo (fun s : ℝ => (s, c)) (Set.Icc a b)
        (Set.Icc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin q)))) :=
      fun s hs => ⟨hs, Set.mem_univ _⟩
    have hpair : Continuous fun s : ℝ => (s, c) := by fun_prop
    have hct := hcont.comp hpair.continuousOn hmaps
    have hcd0 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin q)) ℝ
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]).continuous.comp_continuousOn hct
    have hcd : ContinuousOn (fun s => dd i j s) (Set.Icc a b) :=
      hcd0.congr (fun s _ => by simp [hdd])
    have hmax : Tendsto (fun s => max r s) ℱ (nhdsWithin r (Set.Icc a b)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun s => max r s) (𝓝 r) (𝓝 (max r r)) :=
          (continuous_const.max continuous_id).tendsto r
        rw [max_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun s hs => hmem_max s hs.1
    exact (hcd r hr).tendsto.comp hmax
  -- the identity for the slope
  have hslope : ∀ s ∈ Set.Icc a b \ {r}, slope (fun s => gaussHeat S G s c) r s =
      -(1 / 2) * ∑ i, ∑ j, ((∫ v in Set.Ioc (min r s) (max r s), A v i j) /
        (max r s - min r s)) * dd i j (max r s) - Rem (min r s) (max r s) := by
    intro s hs
    have hne : s ≠ r := hs.2
    have hlh : min r s < max r s := min_lt_max.2 (Ne.symm hne)
    have hwpos : 0 < max r s - min r s := sub_pos.2 hlh
    have hlo := hmem_min s hs.1
    have hhi := hmem_max s hs.1
    have hsl : slope (fun s => gaussHeat S G s c) r s =
        (gaussHeat S G (max r s) c - gaussHeat S G (min r s) c) / (max r s - min r s) := by
      rw [slope_def_field]
      rcases lt_or_gt_of_ne hne with h | h
      · rw [max_eq_left h.le, min_eq_right h.le]
        rw [← neg_div_neg_eq]; congr 1 <;> ring
      · rw [max_eq_right h.le, min_eq_left h.le]
    rw [hsl]
    have hΔ : ∀ i j, (S (min r s) - S (max r s)) i j =
        ∫ v in Set.Ioc (min r s) (max r s), A v i j := fun i j => by
      simpa using S7PIH_cov_sub hA hS hlo hhi hlh.le i j
    simp only [hRem, hΔ]
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    field_simp
    ring
  have hlim : Tendsto (fun s => -(1 / 2) * ∑ i, ∑ j, ((∫ v in Set.Ioc (min r s) (max r s), A v i j) /
        (max r s - min r s)) * dd i j (max r s) - Rem (min r s) (max r s)) ℱ
      (𝓝 (-(1 / 2) * ∑ i, ∑ j, A r i j * dd i j r - 0)) := by
    refine Tendsto.sub (Tendsto.const_mul _ ?_) hT1
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => (hT2 i j).mul (hT3 i j)
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs using (hslope s hs).symm

end HRS.MC.Sec7.S7PIH

end
