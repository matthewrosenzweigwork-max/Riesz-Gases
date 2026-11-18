import HRS.MS.R2WinErrAux11

/-!
# S10.4 packet E1c: the window feature is `C^k` with bound `B θ_b(r)`

`s104_window_feature`: from the orbit bounds of S10.3 (`R2OrbitGrad` for the terminal tests `φ_α` and `L_tφ_α`, with the common summable amplitude
`Cs b_α` and rate `c`), the bound on `∂_aφ_α` itself, and the `u`-measurability of the orbit slot, the feature `Γ_{b,r,a}` of
`r2WindowFeature` is `C^k` in `x` with `‖D^jΓ‖ ≤ (2 + d^k √T) (Cs Σ b_α) θ_b(r)` for every `b ≥ 0`, `r ≥ 0` (S L8330-8334, `W:r2:window-feature-bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

theorem s104_window_feature (hd1 : 1 ≤ d) (C : WholeCoeff d) (k : ℕ) (m T cdec Cs : ℝ) (hT : 0 ≤ T)
    (hcd : 0 ≤ cdec) (hCs : 0 ≤ Cs) (bα : MultiIndex d → ℝ) (hb0 : ∀ α, 0 ≤ bα α) (hbS : Summable bα)
    (hG : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * bα α) cdec)
    (hG' : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * bα α) cdec)
    (hφ : ∀ α a, ContDiff ℝ k (fun x => gradComp a (oscTestFun m α) x) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤ Cs * bα α)
    {b r : ℝ} (hb : 0 ≤ b) (hr0 : 0 ≤ r) (a : Fin d)
    (hmeasU : ∀ α x, AEStronglyMeasurable (fun u => if r < b + u then gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x else 0) (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ContDiff ℝ k (fun x => r2WindowFeature C m T (gradComp a) b r x) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => r2WindowFeature C m T (gradComp a) b r x) x‖ ≤
        (2 + (d : ℝ) ^ k * Real.sqrt T) * (Cs * ∑' α, bα α) * s104_theta cdec b r := by
  set θ : ℝ := s104_theta cdec b r with hθ
  have hθ0 : 0 < θ := s104_theta_pos cdec b r
  set c : MultiIndex d → ℝ := fun α => Cs * bα α * θ with hc
  have hcs : Summable c := (hbS.mul_left Cs).mul_right θ
  have hcnn : ∀ α, 0 ≤ c α := fun α => by have := hb0 α; positivity
  have hmax : Real.exp (-cdec * (max b r - r)) = θ := by
    rw [hθ]; unfold s104_theta
    by_cases h : r < b
    · rw [if_pos h, max_eq_left h.le]
    · rw [if_neg h, max_eq_right (not_lt.1 h)]; simp
  -- slots
  set gA : MultiIndex d → Euc d → ℝ := fun α x =>
    gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x with hgA
  set gB : MultiIndex d → Euc d → ℝ := fun α x => if b ≤ r then gradComp a (oscTestFun m α) x else 0 with hgB
  set v : MultiIndex d → ℝ → Euc d → ℝ := fun α u x =>
    if u ∈ Set.Icc (0 : ℝ) T then (if r < b + u then gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x else 0) else 0 with hv
  have hA : ∀ α, ContDiff ℝ k (gA α) ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (gA α) x‖ ≤ c α := by
    intro α
    have hA0 : 0 ≤ Cs * bα α := mul_nonneg hCs (hb0 α)
    obtain ⟨h1, h2⟩ := s104_gradComp_bound C hA0 (hG α (max b r) (by positivity)) (r := r)
      ⟨hr0, le_max_right _ _⟩ a
    refine ⟨h1, fun j hj x => (h2 j hj x).trans (le_of_eq ?_)⟩
    rw [hmax]
  have hB : ∀ α, ContDiff ℝ k (gB α) ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (gB α) x‖ ≤ c α := by
    intro α
    by_cases h : b ≤ r
    · have e : gB α = fun x => gradComp a (oscTestFun m α) x := by funext x; simp [hgB, h]
      rw [e]
      refine ⟨(hφ α a).1, fun j hj x => ((hφ α a).2 j hj x).trans (le_of_eq ?_)⟩
      have : θ = 1 := by rw [hθ]; unfold s104_theta; rw [if_neg (not_lt.2 h)]
      rw [hc]; simp [this]
    · have e : gB α = fun _ => (0 : ℝ) := by funext x; simp [hgB, h]
      rw [e]
      exact ⟨contDiff_const, fun j hj x => by
        rcases j with _ | j
        · simpa using hcnn α
        · rw [iteratedFDeriv_const_of_ne (by omega)]; simpa using hcnn α⟩
  have hV : ∀ α u, ContDiff ℝ k (v α u) ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (v α u) x‖ ≤ c α := by
    intro α u
    by_cases hu : u ∈ Set.Icc (0 : ℝ) T ∧ r < b + u
    · have e : v α u = fun x => gradComp a (propagatorW C r (b + u)
          (generatorW C (b + u) (oscTestFun m α))) x := by
        funext x; simp only [hv]; rw [if_pos hu.1, if_pos hu.2]
      rw [e]
      have hA0 : 0 ≤ Cs * bα α := mul_nonneg hCs (hb0 α)
      obtain ⟨h1, h2⟩ := s104_gradComp_bound C hA0 (hG' α (b + u) (by linarith [hu.1.1])) (r := r)
        ⟨hr0, hu.2.le⟩ a
      refine ⟨h1, fun j hj x => (h2 j hj x).trans ?_⟩
      have hexp : Real.exp (-cdec * (b + u - r)) ≤ θ := by
        rw [hθ]; unfold s104_theta
        by_cases h : r < b
        · rw [if_pos h]
          apply Real.exp_le_exp.2
          nlinarith [hu.1.1]
        · rw [if_neg h]
          rw [Real.exp_le_one_iff]
          nlinarith [hu.2]
      rw [hc]
      exact mul_le_mul_of_nonneg_left hexp hA0
    · have e : v α u = fun _ => (0 : ℝ) := by
        funext x
        by_cases h1 : u ∈ Set.Icc (0 : ℝ) T
        · have : ¬ r < b + u := fun h => hu ⟨h1, h⟩
          simp only [hv]; rw [if_pos h1, if_neg this]
        · simp only [hv]; rw [if_neg h1]
      rw [e]
      exact ⟨contDiff_const, fun j hj x => by
        rcases j with _ | j
        · simpa using hcnn α
        · rw [iteratedFDeriv_const_of_ne (by omega)]; simpa using hcnn α⟩
  have hmeas : ∀ x α, AEStronglyMeasurable (fun u => v α u x) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    intro x α
    have e : (fun u => v α u x) = (Set.Icc (0 : ℝ) T).indicator (fun u => if r < b + u then
        gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x else 0) := by
      funext u
      by_cases h : u ∈ Set.Icc (0 : ℝ) T
      · simp only [hv]; rw [if_pos h, Set.indicator_of_mem h]
      · simp only [hv]; rw [if_neg h, Set.indicator_of_notMem h]
    rw [e, aestronglyMeasurable_indicator_iff measurableSet_Icc]
    exact (hmeasU α x).mono_measure (Measure.restrict_le_self)
  obtain ⟨hcdiff, hbd⟩ := s104_K_features hd1 k m T c c c hcs hcs hcs gA gB v (fun α => (hA α).1)
    (fun α => (hA α).2) (fun α => (hB α).1) (fun α => (hB α).2) (fun α u => (hV α u).1)
    (fun α u => (hV α u).2) hmeas
  have hfun : (fun x => r2WindowFeature C m T (gradComp a) b r x) = fun x =>
      (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
        (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2
          (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else 0)
        (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T) :=
    funext fun x => s104_window_feature_eq C m T b r a x
  rw [hfun]
  refine ⟨hcdiff, fun j hj x => (hbd j hj x).trans (le_of_eq ?_)⟩
  have hsum : ∑' α, c α = Cs * (∑' α, bα α) * θ := by
    rw [hc]; simp only
    rw [tsum_mul_right, tsum_mul_left]
  have hmu : ((volume.restrict (Set.Icc (0 : ℝ) T)) Set.univ).toReal = T := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]
  rw [hmu, hsum, ← Real.sqrt_eq_rpow]
  ring

end HRS.MS.R2WinErr
