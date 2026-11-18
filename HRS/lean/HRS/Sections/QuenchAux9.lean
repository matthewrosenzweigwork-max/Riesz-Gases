import HRS.Sections.QuenchAux8

/-!
# Packet QUENCH (Q27), part 9: limits along the grid

`h_m N_m(t) → t`, slopes of the exponential, pathwise convergence of the innovation sums.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

lemma tendsto_gh : Tendsto gh atTop (𝓝 0) := by
  unfold gh
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa using this

lemma tendsto_gh_ne : Tendsto gh atTop (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_gh, Eventually.of_forall fun m => (gh_pos m).ne'⟩

lemma tendsto_gN_mul {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun m : ℕ => (gN m t : ℝ) * gh m) atTop (𝓝 t) := by
  have hle : ∀ m, (gN m t : ℝ) * gh m ≤ t := by
    intro m
    have h1 : (gN m t : ℝ) ≤ t * ((m : ℝ) + 1) := Nat.floor_le (by positivity)
    unfold gh
    rw [← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hge : ∀ m, t - gh m ≤ (gN m t : ℝ) * gh m := by
    intro m
    have h1 : t * ((m : ℝ) + 1) < (gN m t : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : t < ((gN m t : ℝ) + 1) * gh m := by
      unfold gh
      rw [← div_eq_mul_one_div, lt_div_iff₀ (by positivity)]
      linarith
    nlinarith
  have h3 : Tendsto (fun m : ℕ => t - gh m) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub tendsto_gh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h3 tendsto_const_nhds hge hle

lemma tendsto_slope_exp (a : ℝ) :
    Tendsto (fun m : ℕ => (Real.exp (a * gh m) - 1) / gh m) atTop (𝓝 a) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (a * s)) a 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul a).exp
    simpa using this
  have := (hasDerivAt_iff_tendsto_slope_zero.1 hd)
  have h2 := this.comp tendsto_gh_ne
  refine h2.congr fun m => ?_
  simp only [Function.comp_apply, zero_add, smul_eq_mul, mul_zero, Real.exp_zero]
  rw [inv_mul_eq_div]

lemma sum_galpha_sq (σ : ℝ) (m : ℕ) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ) :
    ∑ k ∈ Finset.range (gK m ts), galpha σ m ts c k ^ 2 =
      (1 / σ ^ 2) * ∑ i, ∑ i', c i * c i' * (min (gN m (ts i)) (gN m (ts i')) : ℕ) := by
  have hle : ∀ i, gN m (ts i) ≤ gK m ts := fun i =>
    Finset.single_le_sum (f := fun i => gN m (ts i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have e1 : ∀ k, galpha σ m ts c k ^ 2 = ∑ i, ∑ i', (if k < gN m (ts i) ∧ k < gN m (ts i') then
      c i / σ * (c i' / σ) else 0) := by
    intro k
    unfold galpha
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    by_cases h1 : k < gN m (ts i) <;> by_cases h2 : k < gN m (ts i') <;> simp [h1, h2]
  simp_rw [e1]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range _) (t := Finset.univ)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.range (gK m ts)).filter (fun k => k < gN m (ts i) ∧ k < gN m (ts i')) =
      Finset.range (min (gN m (ts i)) (gN m (ts i'))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    have := hle i
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by omega, h⟩
  rw [this, Finset.card_range]
  ring

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {lam v vY : ℝ} {Y : Ω → ℝ} {G : ℝ → Ω → ℝ}

/-- The exact variance of the approximant. -/
def vApp (lam vY : ℝ) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ) (c₀ : ℝ) (m : ℕ) : ℝ :=
  c₀ ^ 2 * vY + (1 - Real.exp (-lam * gh m) ^ 2) / (2 * lam) *
    ∑ i, ∑ i', c i * c i' * (min (gN m (ts i)) (gN m (ts i')) : ℕ)

theorem Vapp_sq_eq (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ)
    (c₀ : ℝ) (m : ℕ) :
    ∫ ω, Vapp lam σ G Y ts c c₀ m ω ^ 2 ∂P = vApp lam vY ts c c₀ m := by
  rw [Vapp_sq hN ts c c₀ m, sum_galpha_sq]
  unfold vApp
  have hσ0 : σ ^ 2 ≠ 0 := by rw [hσ]; positivity
  rw [hσ]
  field_simp

theorem Vapp_law (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ)
    (c₀ : ℝ) (m : ℕ) :
    P.map (Vapp lam σ G Y ts c c₀ m) = gaussianReal 0 (vApp lam vY ts c c₀ m).toNNReal := by
  have hg := Vapp_gauss hN (σ := σ) ts hts c c₀ m
  rw [hg.map_eq_gaussianReal, Vapp_mean hN ts c c₀ m,
    variance_of_integral_eq_zero hg.aemeasurable (Vapp_mean hN ts c c₀ m),
    Vapp_sq_eq hN hv hlam hσ ts c c₀ m]

lemma tendsto_vApp {lam : ℝ} (hlam : 0 < lam) (vY : ℝ) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i)
    (c : ι → ℝ) (c₀ : ℝ) :
    Tendsto (fun m => vApp lam vY ts c c₀ m) atTop
      (𝓝 (c₀ ^ 2 * vY + ∑ i, ∑ i', c i * c i' * min (ts i) (ts i'))) := by
  have hq : Tendsto (fun m : ℕ => (1 - Real.exp (-lam * gh m) ^ 2) / (2 * lam * gh m)) atTop (𝓝 1) := by
    have h1 := (tendsto_slope_exp (-(2 * lam))).neg.div_const (2 * lam)
    have e : ∀ m : ℕ, (1 - Real.exp (-lam * gh m) ^ 2) / (2 * lam * gh m) =
        (-((Real.exp (-(2 * lam) * gh m) - 1) / gh m)) / (2 * lam) := by
      intro m
      have : Real.exp (-lam * gh m) ^ 2 = Real.exp (-(2 * lam) * gh m) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [this]
      have := (gh_pos m).ne'
      field_simp
      ring
    simp_rw [e]
    have e2 : (-(-(2 * lam))) / (2 * lam) = 1 := by field_simp
    rw [e2] at h1
    exact h1
  have hmin : ∀ i i', Tendsto (fun m : ℕ => ((min (gN m (ts i)) (gN m (ts i')) : ℕ) : ℝ) * gh m) atTop
      (𝓝 (min (ts i) (ts i'))) := by
    intro i i'
    have e : ∀ m : ℕ, ((min (gN m (ts i)) (gN m (ts i')) : ℕ) : ℝ) * gh m =
        min ((gN m (ts i) : ℝ) * gh m) ((gN m (ts i') : ℝ) * gh m) := by
      intro m
      rw [Nat.cast_min, min_mul_of_nonneg _ _ (gh_pos m).le]
    simp_rw [e]
    exact (tendsto_gN_mul (hts i)).min (tendsto_gN_mul (hts i'))
  have hsum : Tendsto (fun m : ℕ => ∑ i, ∑ i', c i * c i' * (((min (gN m (ts i)) (gN m (ts i')) : ℕ) : ℝ) * gh m))
      atTop (𝓝 (∑ i, ∑ i', c i * c i' * min (ts i) (ts i'))) := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun i' _ => ?_
    exact (hmin i i').const_mul _
  have h2 := (hq.mul hsum).const_add (c₀ ^ 2 * vY)
  simp only [one_mul] at h2
  refine h2.congr fun m => ?_
  unfold vApp
  have hh := (gh_pos m).ne'
  have hs : ∑ i, ∑ i', c i * c i' * (((min (gN m (ts i)) (gN m (ts i')) : ℕ) : ℝ) * gh m) =
      gh m * ∑ i, ∑ i', c i * c i' * ((min (gN m (ts i)) (gN m (ts i')) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    ring
  have hA : (1 - Real.exp (-lam * gh m) ^ 2) / (2 * lam * gh m) * gh m =
      (1 - Real.exp (-lam * gh m) ^ 2) / (2 * lam) := by field_simp
  rw [hs, ← mul_assoc, hA]

end Law

lemma xi_sum_tendsto {Ω : Type*} (G : ℝ → Ω → ℝ) (ω : Ω) (lam : ℝ)
    (hc : Continuous fun u : ℝ => G (max u 0) ω) (h0 : G 0 ω = 0) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range (gN m t), xi G (gh m) (Real.exp (-lam * gh m)) k ω) atTop
      (𝓝 (G t ω + lam * ∫ u in Set.Icc (0 : ℝ) t, G u ω)) := by
  set g : ℝ → ℝ := fun u => G (max u 0) ω with hg
  have hgG : ∀ u : ℝ, 0 ≤ u → g u = G u ω := fun u hu => by simp [hg, max_eq_left hu]
  have hnn : ∀ (m k : ℕ), 0 ≤ (k : ℝ) * gh m := fun m k => by have := gh_pos m; positivity
  -- telescoping
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range (gN m t), xi G (gh m) (Real.exp (-lam * gh m)) k ω =
      G ((gN m t : ℝ) * gh m) ω - G 0 ω +
      (1 - Real.exp (-lam * gh m)) / gh m *
        (gh m * ∑ k ∈ Finset.range (gN m t), g ((k : ℝ) * gh m)) := by
    intro m
    have hh := (gh_pos m).ne'
    have e : ∀ k : ℕ, xi G (gh m) (Real.exp (-lam * gh m)) k ω =
        (G (((k + 1 : ℕ) : ℝ) * gh m) ω - G ((k : ℝ) * gh m) ω) +
        (1 - Real.exp (-lam * gh m)) * g ((k : ℝ) * gh m) := by
      intro k
      unfold xi
      rw [hgG _ (hnn m k)]
      push_cast
      ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun k : ℕ => G ((k : ℝ) * gh m) ω)]
    simp only [Nat.cast_zero, zero_mul]
    rw [← Finset.mul_sum]
    field_simp
  have h1 : Tendsto (fun m : ℕ => G ((gN m t : ℝ) * gh m) ω) atTop (𝓝 (G t ω)) := by
    have := (hc.tendsto t).comp (tendsto_gN_mul ht)
    rw [hg] at this
    simp only [Function.comp_def, max_eq_left ht] at this
    refine this.congr fun m => ?_
    rw [max_eq_left (hnn m _)]
  have h2 : Tendsto (fun m : ℕ => (1 - Real.exp (-lam * gh m)) / gh m) atTop (𝓝 lam) := by
    have := (tendsto_slope_exp (-lam)).neg
    simp only [neg_neg] at this
    refine this.congr fun m => ?_
    rw [neg_div', neg_sub]
  have h3 : Tendsto (fun m : ℕ => gh m * ∑ k ∈ Finset.range (gN m t), g ((k : ℝ) * gh m)) atTop
      (𝓝 (∫ u in Set.Icc (0 : ℝ) t, g u)) := by
    have := riemann_sum hc ht
    refine this.congr fun m => ?_
    unfold gh gN
    congr 2
    funext k
    rw [div_eq_mul_one_div]
  have hint : ∫ u in Set.Icc (0 : ℝ) t, g u = ∫ u in Set.Icc (0 : ℝ) t, G u ω := by
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => hgG u hu.1
  rw [hint] at h3
  have h4 := (h1.sub (tendsto_const_nhds (x := G 0 ω))).add (h2.mul h3)
  have h5 : G t ω - G 0 ω + lam * ∫ u in Set.Icc (0 : ℝ) t, G u ω =
      G t ω + lam * ∫ u in Set.Icc (0 : ℝ) t, G u ω := by rw [h0]; ring
  rw [h5] at h4
  exact h4.congr fun m => (htel m).symm

end Qch

end HRS
