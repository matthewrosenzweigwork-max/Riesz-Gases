import HRS.MC.S7PIH5Cov

/-!
# Packet piH, part 6: regularity of the finite-dimensional heat function
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ}

/-- `C^k` regularity of a Gaussian average of a `C_b^k` function, `k ≥ 1`. -/
theorem S7PIH_heat_contDiff (ν : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure ν]
    {G : EuclideanSpace ℝ (Fin q) → ℝ} {k : ℕ} (hk : 1 ≤ k) (hG : MemCb k G) :
    ContDiff ℝ k (fun y => ∫ x, G (y + x) ∂ν) := by
  have hGc : ∀ m : ℕ, m ≤ k → Continuous (iteratedFDeriv ℝ m G) := fun m hm =>
    hG.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
  have hcd : ∀ z : EuclideanSpace ℝ (Fin q), ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (fun y => G (y + z)) :=
    fun z => by
      have := hG.1.comp (contDiff_id.add (contDiff_const (c := z)))
      simpa [Function.comp_def] using this
  have key := contDiff_integral_dominated (B := EuclideanSpace ℝ (Fin q)) ν
    (fun z y => G (y + z)) k hk hcd
    (fun x => by
      have hGcont : Continuous G := by simpa using hG.1.continuous
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖) ?_ ?_
      · exact (hGcont.comp (by fun_prop : Continuous fun z => x + z)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun z => ?_
        have := S7PIS3_cb_bound hG (j := 0) (Nat.zero_le _) (x + z)
        simpa using this)
    (fun m hm x => by
      have h : (fun z => iteratedFDeriv ℝ m (fun y => G (y + z)) x) =
          fun z => iteratedFDeriv ℝ m G (x + z) := by
        funext z; exact iteratedFDeriv_comp_add_right m z x
      rw [h]
      exact ((hGc m hm).comp (by fun_prop : Continuous fun z => x + z)).aestronglyMeasurable)
    (fun m _ => ⨆ z, ‖iteratedFDeriv ℝ m G z‖) (fun m _ _ => integrable_const _)
    (fun m _ hmj z x => by
      rw [iteratedFDeriv_comp_add_right]
      exact S7PIS3_cb_bound hG hmj _)
  exact key.1

theorem S7PIH_cb_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ} {k l : ℕ}
    (hG : MemCb k G) (hl : l ≤ k) : MemCb l G :=
  ⟨hG.1.of_le (by exact_mod_cast hl), fun j hj => hG.2 j (hj.trans hl)⟩

/-- The Hessian entries of a Gaussian average are the Gaussian averages of the Hessian entries. -/
theorem S7PIH_heat_D2_eval (ν : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure ν]
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) (c : EuclideanSpace ℝ (Fin q))
    (m : Fin 2 → EuclideanSpace ℝ (Fin q)) :
    iteratedFDeriv ℝ 2 (fun y => ∫ x, G (y + x) ∂ν) c m =
      ∫ x, iteratedFDeriv ℝ 2 G (c + x) m ∂ν := by
  rw [S7PIS3_heat_deriv ν hG le_rfl c]
  have hint : Integrable (fun x => iteratedFDeriv ℝ 2 G (c + x)) ν := by
    have hcont : Continuous (iteratedFDeriv ℝ 2 G) := hG.1.continuous_iteratedFDeriv (by norm_num)
    refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 2 G z‖) ?_ ?_
    · exact (hcont.comp (by fun_prop : Continuous fun z => c + z)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => S7PIS3_cb_bound hG le_rfl _
  exact ContinuousMultilinearMap.integral_apply hint m

/-- Bounds: `|F| ≤ C0` and `‖D²F‖ ≤ C2`. -/
theorem S7PIH_heat_bounds (ν : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure ν]
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) (y : EuclideanSpace ℝ (Fin q)) :
    |∫ x, G (y + x) ∂ν| ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => ∫ x, G (y + x) ∂ν) y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ 2 G z‖ := by
  constructor
  · have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => G (y + x))
      (C := ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖) (Filter.Eventually.of_forall fun x => by
        have := S7PIS3_cb_bound hG (j := 0) (Nat.zero_le _) (y + x)
        simpa using this)
    simpa using this
  · rw [S7PIS3_heat_deriv ν hG le_rfl y]
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => iteratedFDeriv ℝ 2 G (y + x))
      (C := ⨆ z, ‖iteratedFDeriv ℝ 2 G z‖) (Filter.Eventually.of_forall fun x =>
        S7PIS3_cb_bound hG le_rfl (y + x))
    simpa using this

/-- Joint continuity of the derivatives of the heat function on `[a,b] × ℝ^q`. -/
theorem S7PIH_heat_cont_ab {a b : ℝ} (hab : a ≤ b) {A S : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} {k : ℕ} (hG : MemCb k G) {j : ℕ} (hj : j ≤ k) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin q) => iteratedFDeriv ℝ j (gaussHeat S G p.1) p.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  have hsh : ∀ i j, ContinuousOn (fun u => S (a + u) i j) (Set.Icc 0 (b - a)) := fun i j =>
    (S7PIH_S_cont hA hab hS i j).comp (continuousOn_const.add continuousOn_id) (fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hpsd : ∀ u ∈ Set.Icc 0 (b - a), (S (a + u)).PosSemidef := fun u hu =>
    S7PIH_S_psd hA hApsd hSb hS ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have := s7_PIH_heat_cont_proof (b - a) (fun u => S (a + u)) hsh hpsd G k hG j hj
  have hmaps : Set.MapsTo (fun p : ℝ × EuclideanSpace ℝ (Fin q) => (p.1 - a, p.2))
      (Set.Icc a b ×ˢ Set.univ) (Set.Icc 0 (b - a) ×ˢ Set.univ) := fun p hp =>
    ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, Set.mem_univ _⟩
  have hc := this.comp (by fun_prop : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin q) => (p.1 - a, p.2)).continuousOn hmaps
  refine hc.congr fun p _ => ?_
  have e : gaussHeat (fun u => S (a + u)) G (p.1 - a) = gaussHeat S G p.1 := by
    funext c
    simp [gaussHeat]
  simp only [Function.comp_def, e]

end HRS.MC.Sec7.S7PIH

end
