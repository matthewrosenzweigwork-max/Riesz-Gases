import HRS.MS.R2WinErrTie
import HRS.MS.S111TermB3

/-!
# S11.1 continuation, B02 (part 1): `ℓ²`-versions of the `𝒦`-valued window feature estimates

`s104_K_features`/`s104_window_feature` are stated with `ℓ¹` amplitudes `Σ b_α`; here the coordinates are `ℓ²`-summable
(`Σ b_α² ≤ S`), which is what the quantitative window contract `window_feature_bounds` needs.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr

variable {d : ℕ}

lemma s111k2_aesm_ellVec2 {μ : Measure ℝ} {m : ℝ} (v : MultiIndex d → ℝ → ℝ)
    (hv : ∀ α, AEStronglyMeasurable (v α) μ) (hsum : ∀ t, Summable fun α => v α t ^ 2) :
    AEStronglyMeasurable (fun t => ellVec (d := d) m (fun α => v α t)) μ := by
  set ι : ∀ α : MultiIndex d, ℝ →L[ℝ] OscDual d m := fun α =>
    lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : MultiIndex d => ℝ) 2 α with hι
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (MultiIndex d)))
    (f := fun (s : Finset (MultiIndex d)) (t : ℝ) => ∑ α ∈ s, ι α (v α t)) ?_ ?_
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s fun α _ => (ι α).continuous.comp_aestronglyMeasurable (hv α)
  · refine Eventually.of_forall fun t => ?_
    have h : Memℓp (fun α => v α t) 2 := by
      rw [memℓp_two_iff]; exact hsum t
    have h2 : HasSum (fun α => (lp.single 2 α (v α t) : lp (fun _ : MultiIndex d => ℝ) 2))
        (ellVec (d := d) m (fun α => v α t) : lp (fun _ : MultiIndex d => ℝ) 2) := by
      rw [s55f_ellVec_eq (m := m) h]
      exact lp.hasSum_single (by norm_num) ⟨fun α => v α t, h⟩
    exact h2

theorem s111k2_K_features2 (hd1 : 1 ≤ d) (k : ℕ) (m T : ℝ)
    (cA cV cB : MultiIndex d → ℝ) (hcA : Summable fun α => cA α ^ 2) (hcV : Summable fun α => cV α ^ 2) (hcB : Summable fun α => cB α ^ 2)
    (gA gB : MultiIndex d → Euc d → ℝ) (v : MultiIndex d → ℝ → Euc d → ℝ)
    (hgA : ∀ α, ContDiff ℝ k (gA α))
    (hbA : ∀ α, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (gA α) x‖ ≤ cA α)
    (hgB : ∀ α, ContDiff ℝ k (gB α))
    (hbB : ∀ α, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (gB α) x‖ ≤ cB α)
    (hv : ∀ α u, ContDiff ℝ k (v α u))
    (hbv : ∀ α u, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (v α u) x‖ ≤ cV α)
    (hmeas : ∀ x α, AEStronglyMeasurable (fun u => v α u x) (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ContDiff ℝ k (fun x : Euc d => (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2
        (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else 0)
      (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T)) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x : Euc d => (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2
        (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else 0)
      (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T)) x‖ ≤
      Real.sqrt (∑' α, cA α ^ 2) + (d : ℝ) ^ k * (Real.sqrt (∑' α, cV α ^ 2) * ((volume.restrict (Set.Icc (0 : ℝ) T)) Set.univ).toReal ^ (1 / 2 : ℝ))
        + Real.sqrt (∑' α, cB α ^ 2) := by
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hbaseA := s101_ell2_contDiff (d := d) (m := m) k gA cA hcA hgA hbA
  have hbaseB := s101_ell2_contDiff (d := d) (m := m) k gB cB hcB hgB hbB
  set Bs : ℝ := Real.sqrt (∑' α, cV α ^ 2) with hBs
  set Fv : ℝ → Euc d → OscDual d m := fun u x => ellVec (d := d) m (fun α => v α u x) with hFv
  have hFsm : ∀ u, ContDiff ℝ k (Fv u) ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (Fv u) x‖ ≤ Bs := fun u =>
    s101_ell2_contDiff (d := d) (m := m) k (fun α x => v α u x) cV hcV (fun α => hv α u)
      (fun α j hj x => hbv α u j hj x)
  have hv0 : ∀ x α u, |v α u x| ≤ cV α := by
    intro x α u
    have := hbv α u 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hmeasF : ∀ x, AEStronglyMeasurable (fun u => Fv u x) μ := fun x =>
    s111k2_aesm_ellVec2 (m := m) (fun α u => v α u x) (hmeas x) (fun u =>
      Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => by
        have := abs_le.1 (hv0 x α u)
        exact sq_le_sq' this.1 this.2) hcV)
  have hFb0 : ∀ u x, ‖Fv u x‖ ≤ Bs := fun u x => by
    have := (hFsm u).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hmem : ∀ x, MemLp (fun u => Fv u x) 2 μ := fun x =>
    s55f_memLp_of_bound μ (hmeasF x) (B := Bs) (fun u => hFb0 u x)
  have hBs0 : 0 ≤ Bs := Real.sqrt_nonneg _
  obtain ⟨hWc, hWb⟩ := s55f_L2_contDiff μ hd1 k Fv Bs (fun u => (hFsm u).1)
    (fun u j hj x => (hFsm u).2 j hj x) hmeasF hmem
  have hid : ∀ x, (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2 μ then
        h.toLp _ else 0) (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T) =
      s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x)) +
        s104ΦB m T (ellVec (d := d) m (fun α => gB α x)) := by
    intro x
    rw [← s104_mk_eq]
    congr 1
    exact dif_pos (hmem x)
  have hfun : (fun x : Euc d => (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2 μ then
        h.toLp _ else 0) (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T)) = fun x =>
      s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x)) +
        s104ΦB m T (ellVec (d := d) m (fun α => gB α x)) := funext hid
  rw [hfun]
  have cdA := (s104ΦA m T).contDiff.comp hbaseA.1
  have cdW := (s55fΦ₂ m T).contDiff.comp hWc
  have cdB := (s104ΦB m T).contDiff.comp hbaseB.1
  refine ⟨(cdA.add cdW).add cdB, fun j hj x => ?_⟩
  have hjk : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hj
  have hadd1 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j) (cdA.of_le hjk).contDiffAt
    (cdW.of_le hjk).contDiffAt (x := x)
  have hadd2 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j) ((cdA.add cdW).of_le hjk).contDiffAt
    (cdB.of_le hjk).contDiffAt (x := x)
  have e1 := (s104ΦA m T).norm_iteratedFDeriv_comp_left hbaseA.1.contDiffAt (x := x) (n := j) hjk
  have e2 := (s55fΦ₂ m T).norm_iteratedFDeriv_comp_left hWc.contDiffAt (x := x) (n := j) hjk
  have e3 := (s104ΦB m T).norm_iteratedFDeriv_comp_left hbaseB.1.contDiffAt (x := x) (n := j) hjk
  have hF1 : iteratedFDeriv ℝ j (fun x => s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x))) x =
      iteratedFDeriv ℝ j (s104ΦA m T ∘ fun x => ellVec (d := d) m (fun α => gA α x)) x +
        iteratedFDeriv ℝ j (s55fΦ₂ m T ∘ fun x => (hmem x).toLp (fun u => Fv u x)) x := hadd1
  have hF2 : iteratedFDeriv ℝ j (fun x => s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x)) +
        s104ΦB m T (ellVec (d := d) m (fun α => gB α x))) x =
      iteratedFDeriv ℝ j (fun x => s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x))) x +
        iteratedFDeriv ℝ j (s104ΦB m T ∘ fun x => ellVec (d := d) m (fun α => gB α x)) x := hadd2
  rw [hF2, hF1]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  have hb1 := hbaseA.2 j hj x
  have hb2 := hWb j hj x
  have hb3 := hbaseB.2 j hj x
  have hn1 := s104ΦA_norm (d := d) m T
  have hn2 := s55fΦ₂_norm (d := d) m T
  have hn3 := s104ΦB_norm (d := d) m T
  have hdj : (d : ℝ) ^ j ≤ (d : ℝ) ^ k := pow_le_pow_right₀ hd1' hj
  have hX : 0 ≤ Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by positivity
  have h1 : ‖s104ΦA (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gA α x)) x‖ ≤
      Real.sqrt (∑' α, cA α ^ 2) := by
    calc _ ≤ 1 * Real.sqrt (∑' α, cA α ^ 2) := mul_le_mul hn1 hb1 (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have h3 : ‖s104ΦB (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gB α x)) x‖ ≤
      Real.sqrt (∑' α, cB α ^ 2) := by
    calc _ ≤ 1 * Real.sqrt (∑' α, cB α ^ 2) := mul_le_mul hn3 hb3 (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have h2 : ‖s55fΦ₂ (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun u => Fv u x)) x‖ ≤
      (d : ℝ) ^ k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) :=
    calc _ ≤ 1 * ((d : ℝ) ^ j * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) :=
          mul_le_mul hn2 hb2 (norm_nonneg _) (by norm_num)
      _ ≤ (d : ℝ) ^ k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right hdj hX
  calc _ ≤ ‖s104ΦA (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gA α x)) x‖ +
        ‖s55fΦ₂ (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun u => Fv u x)) x‖ +
        ‖s104ΦB (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gB α x)) x‖ :=
        add_le_add (add_le_add e1 e2) e3
    _ ≤ _ := by linarith


theorem s111k2_window_feature2 (hd1 : 1 ≤ d) (C : WholeCoeff d) (k : ℕ) (m T cdec Cs : ℝ) (hT : 0 ≤ T)
    (hcd : 0 ≤ cdec) (hCs : 0 ≤ Cs) (bα : MultiIndex d → ℝ) (hb0 : ∀ α, 0 ≤ bα α) (hbS : Summable fun α => bα α ^ 2)
    (hG : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * bα α) cdec)
    (hG' : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * bα α) cdec)
    (hφ : ∀ α a, ContDiff ℝ k (fun x => gradComp a (oscTestFun m α) x) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤ Cs * bα α)
    {b r : ℝ} (hb : 0 ≤ b) (hr0 : 0 ≤ r) (a : Fin d)
    (hmeasU : ∀ α x, AEStronglyMeasurable (fun u => if r < b + u then gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x else 0) (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ContDiff ℝ k (fun x => r2WindowFeature C m T (gradComp a) b r x) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => r2WindowFeature C m T (gradComp a) b r x) x‖ ≤
        (2 + (d : ℝ) ^ k * Real.sqrt T) * (Cs * Real.sqrt (∑' α, bα α ^ 2)) * s104_theta cdec b r := by
  set θ : ℝ := s104_theta cdec b r with hθ
  have hθ0 : 0 < θ := s104_theta_pos cdec b r
  set c : MultiIndex d → ℝ := fun α => Cs * bα α * θ with hc
  have hcs : Summable fun α => c α ^ 2 := by
    have : (fun α => c α ^ 2) = fun α => (Cs * θ) ^ 2 * bα α ^ 2 := by
      funext α; simp only [hc]; ring
    rw [this]; exact hbS.mul_left _
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
  obtain ⟨hcdiff, hbd⟩ := s111k2_K_features2 hd1 k m T c c c hcs hcs hcs gA gB v (fun α => (hA α).1)
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
  have hsum : Real.sqrt (∑' α, c α ^ 2) = Cs * Real.sqrt (∑' α, bα α ^ 2) * θ := by
    have : (∑' α, c α ^ 2) = (Cs * θ) ^ 2 * ∑' α, bα α ^ 2 := by
      rw [← tsum_mul_left]; refine tsum_congr fun α => ?_; simp only [hc]; ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hCs hθ0.le)]; ring
  have hmu : ((volume.restrict (Set.Icc (0 : ℝ) T)) Set.univ).toReal = T := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]
  rw [hmu, hsum, ← Real.sqrt_eq_rpow]
  ring


lemma s111k2_gradComp_eq_fderiv (a : Fin d) (g : Euc d → ℝ) (x : Euc d) :
    gradComp a g x = fderiv ℝ g x (EuclideanSpace.single a (1 : ℝ)) := by
  unfold gradComp gradient
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single a (1 : ℝ))
    (y := fderiv ℝ g x)
  rw [← this, EuclideanSpace.inner_single_right]
  simp

lemma s111k2_quotient_tendsto (a : Fin d) (g : Euc d → ℝ) (x : Euc d) (hg : DifferentiableAt ℝ g x) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * (g (x + (1 / ((k : ℝ) + 1)) • EuclideanSpace.single a (1 : ℝ)) - g x))
      atTop (𝓝 (gradComp a g x)) := by
  set e : Euc d := EuclideanSpace.single a (1 : ℝ) with he
  have h1 : HasDerivAt (fun s : ℝ => x + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • e) := by
    simpa using hg.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have h4 := h3.tendsto_slope_zero_right
  have h5 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => by
        show (0 : ℝ) < _
        positivity⟩
  have h6 := h4.comp h5
  rw [s111k2_gradComp_eq_fderiv]
  refine h6.congr fun k => ?_
  simp only [Function.comp, zero_add, smul_eq_mul, one_div, inv_inv]
  simp [he]

theorem s111k2_hmeasU {C : WholeCoeff d} (φ : Euc d → ℝ) (T b r : ℝ) (hr : 0 ≤ r) (a : Fin d) (x : Euc d)
    (hcl : ∀ t : ℝ, 0 ≤ t → ∃ f, IsClassicalAdjointW C t (generatorW C t φ) f)
    (hder : ∀ t, r ≤ t → ∀ y, HasDerivWithinAt (fun s => propagatorW C r s φ y)
      (propagatorW C r t (generatorW C t φ) y) (Ici r) t) :
    AEStronglyMeasurable (fun u : ℝ => if r < b + u then
      gradComp a (propagatorW C r (b + u) (generatorW C (b + u) φ)) x else 0)
      (volume.restrict (Icc 0 T)) := by
  classical
  set D : Euc d → ℝ → ℝ := fun y t => derivWithin (fun s => propagatorW C r s φ y) (Ici t) t with hD
  have hDm : ∀ y, Measurable (D y) := fun y => measurable_derivWithin_Ici _
  have hDeq : ∀ t, r ≤ t → ∀ y, D y t = propagatorW C r t (generatorW C t φ) y := by
    intro t ht y
    have := (hder t ht y).mono (Ici_subset_Ici.2 ht)
    exact this.derivWithin (uniqueDiffWithinAt_Ici t)
  have hdiff : ∀ t, r ≤ t → DifferentiableAt ℝ (propagatorW C r t (generatorW C t φ)) x := by
    intro t ht
    have hex := hcl t (hr.trans ht)
    have hp : propagatorW C r t (generatorW C t φ) = hex.choose r := by
      unfold propagatorW; rw [dif_pos hex]
    rw [hp]
    exact ((hex.choose_spec.c2 r ⟨hr, ht⟩).differentiable (by norm_num)) x
  set e : Euc d := EuclideanSpace.single a (1 : ℝ) with he
  set g : ℕ → ℝ → ℝ := fun k u => if r < b + u then
    ((k : ℝ) + 1) * (D (x + (1 / ((k : ℝ) + 1)) • e) (b + u) - D x (b + u)) else 0 with hg
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) ?_ measurable_const
    exact measurable_const.mul (((hDm _).comp (by fun_prop : Measurable fun u : ℝ => b + u)).sub
      ((hDm _).comp (by fun_prop : Measurable fun u : ℝ => b + u)))
  have hlim : Tendsto g atTop (𝓝 fun u : ℝ => if r < b + u then
      gradComp a (propagatorW C r (b + u) (generatorW C (b + u) φ)) x else 0) := by
    refine tendsto_pi_nhds.2 fun u => ?_
    by_cases hu : r < b + u
    · simp only [hg, if_pos hu]
      have := s111k2_quotient_tendsto a (propagatorW C r (b + u) (generatorW C (b + u) φ)) x (hdiff _ hu.le)
      refine this.congr fun k => ?_
      rw [hDeq _ hu.le, hDeq _ hu.le]
    · simp only [hg, if_neg hu]
      exact tendsto_const_nhds
  exact (measurable_of_tendsto_metrizable hgm hlim).aestronglyMeasurable


/-- The forcing-age profile (Pro `age`). -/
def s111k2_age (c u v : ℝ) : ℝ := Real.exp (-c * max (u - v) 0)

/-- Precisely the S10.3/E04/E07 orbit data consumed by the window estimates (Pro `WindowOrbitInput`). -/
structure S111k2WindowOrbitInput {d : ℕ} (C : WholeCoeff d) (m c0 : ℝ)
    (r : ℕ) (b : MultiIndex d → ℝ) : Prop where
  nonneg : ∀ alpha, 0 ≤ b alpha
  classical : ∀ alpha t, 0 ≤ t →
    (∃ f, IsClassicalAdjointW C t (oscTestFun m alpha) f) ∧
    ∃ f, IsClassicalAdjointW C t (generatorW C t (oscTestFun m alpha)) f
  grad : ∀ alpha t, 0 ≤ t →
    R2OrbitGrad C r t (oscTestFun m alpha) (b alpha) c0 ∧
    R2OrbitGrad C r t (generatorW C t (oscTestFun m alpha)) (b alpha) c0
  terminal_derivative : ∀ alpha v t, 0 ≤ v → v ≤ t → ∀ x,
    HasDerivWithinAt (fun a => propagatorW C v a (oscTestFun m alpha) x)
      (propagatorW C v t (generatorW C t (oscTestFun m alpha)) x)
      (Set.Ici v) t
  orbit : ∀ H : ℝ, 0 < H → R2OrbitSummable C m H r
  linear : ∀ v t : ℝ, 0 ≤ v → v ≤ t →
    ∀ phi psi : Euc d → ℝ, ∀ a : ℝ,
      IsR2DualCombo m phi → IsR2DualCombo m psi →
      propagatorW C v t (phi + a • psi) =
        propagatorW C v t phi + a • propagatorW C v t psi

lemma s111k2_theta_eq_age (c u v : ℝ) : s104_theta c u v = s111k2_age c u v := by
  unfold s104_theta s111k2_age
  by_cases h : v < u
  · rw [if_pos h, max_eq_left (by linarith)]
  · rw [if_neg h, max_eq_right (by linarith)]; simp

/-- **B02 (window feature bounds).** -/
theorem s111k2_window_feature_bounds (d r : ℕ) (m T S c0 : ℝ)
    (hT : 0 < T) (hS : 0 ≤ S) (hc0 : 0 < c0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ C : WholeCoeff d,
      ∀ b : MultiIndex d → ℝ, Summable (fun alpha => b alpha ^ 2) →
      (∑' alpha, b alpha ^ 2) ≤ S → S111k2WindowOrbitInput C m c0 r b →
      ∀ u : ℝ, 0 ≤ u → ∀ v ∈ Set.Icc 0 (u + T), ∀ i : Fin d,
        let G := fun x => r2WindowFeature C m T
          (fun f x => gradient f x i) u v x
        ContDiff ℝ r G ∧
          ∀ j : ℕ, j ≤ r → ∀ x, ‖iteratedFDeriv ℝ j G x‖ ≤ K * s111k2_age c0 u v := by
  refine ⟨(2 + (d : ℝ) ^ r * Real.sqrt T) * Real.sqrt S, mul_nonneg (by positivity) (Real.sqrt_nonneg _), ?_⟩
  intro C b hbS hbSS hW u hu v hv i
  have hd1 : 1 ≤ d := i.pos
  have hb0 : ∀ α, 0 ≤ b α := hW.nonneg
  have hG : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C r t (oscTestFun m α) (1 * b α) c0 := by
    intro α t ht; rw [one_mul]; exact (hW.grad α t ht).1
  have hG' : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C r t (generatorW C t (oscTestFun m α)) (1 * b α) c0 := by
    intro α t ht; rw [one_mul]; exact (hW.grad α t ht).2
  have hφ : ∀ α a, ContDiff ℝ r (fun x => gradComp a (oscTestFun m α) x) ∧ ∀ j ≤ r, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤ 1 * b α := by
    intro α a
    have hex := (hW.classical α 0 le_rfl).1
    have hp : propagatorW C 0 0 (oscTestFun m α) = oscTestFun m α := by
      unfold propagatorW; rw [dif_pos hex]; exact hex.choose_spec.terminal
    have := s104_gradComp_bound C (mul_nonneg zero_le_one (hb0 α)) (hG α 0 le_rfl)
      (r := 0) ⟨le_rfl, le_rfl⟩ a
    rw [hp] at this
    simpa using this
  have hmeasU : ∀ α x, AEStronglyMeasurable (fun w => if v < u + w then gradComp i (propagatorW C v (u + w)
      (generatorW C (u + w) (oscTestFun m α))) x else 0) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    intro α x
    exact s111k2_hmeasU (oscTestFun m α) T u v hv.1 i x (fun t ht => (hW.classical α t ht).2)
      (fun t htv y => hW.terminal_derivative α v t hv.1 htv y)
  obtain ⟨h1, h2⟩ := s111k2_window_feature2 hd1 C r m T c0 1 hT.le hc0.le zero_le_one b hb0 hbS
    hG hG' hφ hu hv.1 i hmeasU
  refine ⟨h1, fun j hj x => (h2 j hj x).trans ?_⟩
  rw [s111k2_theta_eq_age]
  have hsq : Real.sqrt (∑' α, b α ^ 2) ≤ Real.sqrt S := Real.sqrt_le_sqrt hbSS
  have hage : 0 ≤ s111k2_age c0 u v := (Real.exp_pos _).le
  have hc : 0 ≤ 2 + (d : ℝ) ^ r * Real.sqrt T := by positivity
  calc (2 + (d : ℝ) ^ r * Real.sqrt T) * (1 * Real.sqrt (∑' α, b α ^ 2)) * s111k2_age c0 u v
      ≤ (2 + (d : ℝ) ^ r * Real.sqrt T) * (1 * Real.sqrt S) * s111k2_age c0 u v := by
        gcongr
    _ = (2 + (d : ℝ) ^ r * Real.sqrt T) * Real.sqrt S * s111k2_age c0 u v := by ring


end HRS.MS.S111K2
