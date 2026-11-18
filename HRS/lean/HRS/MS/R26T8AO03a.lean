import HRS.MS.R26T8AD02

/-!
# S8.2 observed-time layer, packet T8A.O03a: common positive-jet difference quotients from FeatureOrbits

For the orbit data `r26t8a_FeatureOrbits`, the quotient `h⁻¹(G_j(v+h) - G_j(v)) - G_{j+1}(v)` of the `j`-th age test
(`j ≤ 1`) tends to zero in `testSizeE (testOrder d)` as `h → 0` inside `[0,∞)`. The proof is a mean-value estimate
for each positive derivative order and point `x`, using the derivative clause of `FeatureOrbits` and the norm
continuity of the `(j+1)`-st orbit (uniform in `x` through `testSizeE`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- a bound on all positive derivatives of order at most `k` gives a bound on `testSizeE` -/
theorem r26t8a_o03a_testSize_le {k : ℕ} (f : Euc d → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k → ∀ x, ‖iteratedFDeriv ℝ ℓ f x‖ ≤ ε) :
    testSizeE k f ≤ ENNReal.ofReal ε := by
  unfold testSizeE
  refine iSup_le fun j => iSup_le fun x => ?_
  have hj := j.isLt
  exact ENNReal.ofReal_le_ofReal (h ((j : ℕ) + 1) (by omega) (by omega) x)

/-- a `testSizeE` bound controls each positive derivative at each point -/
theorem r26t8a_o03a_le_testSize {k : ℕ} (f : Euc d → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : testSizeE k f ≤ ENNReal.ofReal ε) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ ℓ f x‖ ≤ ε := by
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ (ℓ' + 1) f x‖ ≤ testSizeE k f :=
    le_iSup₂_of_le (⟨ℓ', by omega⟩ : Fin k) x le_rfl
  exact (ENNReal.ofReal_le_ofReal_iff hε).1 (h2.trans hb)

/-- mean-value estimate for a one-parameter family in a normed space -/
theorem r26t8a_o03a_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P P' : ℝ → E)
    (v h ε : ℝ) (hv : 0 ≤ v) (hvh : 0 ≤ v + h)
    (hP : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt P (P' s) (Set.Ici 0) s)
    (hb : ∀ s ∈ Set.Icc (min v (v + h)) (max v (v + h)), ‖P' s - P' v‖ ≤ ε) :
    ‖P (v + h) - P v - h • P' v‖ ≤ ε * ‖h‖ := by
  have hlo0 : 0 ≤ min v (v + h) := le_min hv hvh
  have hvmem : v ∈ Set.Icc (min v (v + h)) (max v (v + h)) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hvhmem : v + h ∈ Set.Icc (min v (v + h)) (max v (v + h)) :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  have hgd : ∀ s ∈ Set.Icc (min v (v + h)) (max v (v + h)),
      HasDerivWithinAt (fun s => P s - P v - (s - v) • P' v) (P' s - P' v)
        (Set.Icc (min v (v + h)) (max v (v + h))) s := by
    intro s hs
    have h1 : HasDerivWithinAt P (P' s) (Set.Icc (min v (v + h)) (max v (v + h))) s :=
      (hP s (le_trans hlo0 hs.1)).mono fun y hy => le_trans hlo0 hy.1
    have h2 : HasDerivAt (fun s : ℝ => (s - v) • P' v) (P' v) s := by
      have := ((hasDerivAt_id s).sub_const v).smul_const (P' v)
      simpa using this
    exact (h1.sub_const (P v)).sub h2.hasDerivWithinAt
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hgd (fun s hs => hb s hs)
    (convex_Icc _ _) hvmem hvhmem
  have hg0 : (fun s : ℝ => P s - P v - (s - v) • P' v) v = 0 := by simp
  have e : (fun s : ℝ => P s - P v - (s - v) • P' v) (v + h) = P (v + h) - P v - h • P' v := by
    simp
  simp only [hg0, e, sub_zero, add_sub_cancel_left] at key
  exact key

theorem r26t8a_age_difference_quotient (a beta m Cf c : ℝ) (rho : Euc d → ℝ)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (j : ℕ) (hj : j ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) :
    Tendsto (fun h => testSizeE (testOrder d) (fun x =>
      h⁻¹ * (r26t8a_ageTest a beta m rho alpha j (v + h) x - r26t8a_ageTest a beta m rho alpha j v x) -
        r26t8a_ageTest a beta m rho alpha (j + 1) v x))
      (𝓝[({h : ℝ | 0 ≤ v + h} ∩ {0}ᶜ)] 0) (𝓝 0) := by
  have hj2 : j + 1 ≤ 2 := by omega
  rw [ENNReal.tendsto_nhds_zero]
  intro ε0 hε0
  rcases eq_or_ne ε0 ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  have hepos : 0 < ε0.toReal := ENNReal.toReal_pos hε0.ne' hεt
  have hεe : ENNReal.ofReal ε0.toReal = ε0 := ENNReal.ofReal_toReal hεt
  rw [← hεe]
  set e := ε0.toReal with he
  -- uniform continuity of the `(j+1)`-st orbit at `v`, in `testSizeE`
  have hev : ∀ᶠ s in 𝓝[Set.Ici 0] v,
      testSizeE (testOrder d) (r26t8a_ageTest a beta m rho alpha (j + 1) s -
        r26t8a_ageTest a beta m rho alpha (j + 1) v) ≤ ENNReal.ofReal e :=
    (ENNReal.tendsto_nhds_zero.1 (horb.continuity alpha (j + 1) hj2 v hv)) (ENNReal.ofReal e)
      (ENNReal.ofReal_pos.2 hepos)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδ'⟩ := hev
  refine eventually_nhdsWithin_iff.2 ?_
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun {h} hh hS => ?_⟩
  have hvh : 0 ≤ v + h := hS.1
  have hh0 : h ≠ 0 := hS.2
  have hhδ : |h| < δ := by simpa [Real.dist_eq] using hh
  apply r26t8a_o03a_testSize_le _ e hepos.le
  intro ℓ hℓ1 hℓk x
  have hC : ∀ s : ℝ, 0 ≤ s → ∀ i : ℕ, i ≤ 2 →
      ContDiff ℝ ∞ (r26t8a_ageTest a beta m rho alpha i s) :=
    fun s hs i hi => (horb.bound alpha s hs i hi).1
  have hlo : v - |h| ≤ min v (v + h) :=
    le_min (by linarith [abs_nonneg h]) (by linarith [neg_abs_le h])
  have hhi : max v (v + h) ≤ v + |h| :=
    max_le (by linarith [abs_nonneg h]) (by linarith [le_abs_self h])
  -- derivative bound of the `(j+1)`-st orbit, uniform in `x`, on the segment
  have hb : ∀ s ∈ Set.Icc (min v (v + h)) (max v (v + h)),
      ‖iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha (j + 1) s) x -
        iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha (j + 1) v) x‖ ≤ e := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (le_min hv hvh) hs.1
    have hsv : |s - v| ≤ |h| := by
      rw [abs_le]
      constructor
      · linarith [hs.1]
      · linarith [hs.2]
    have hdist : dist s v < δ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt hsv hhδ
    have hts := hδ' hdist hs0
    have h3 := r26t8a_o03a_le_testSize _ e hepos.le hts ℓ hℓ1 hℓk x
    rw [iteratedFDeriv_sub_apply ((hC s hs0 (j + 1) hj2).contDiffAt.of_le
      (by first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hC v hv (j + 1) hj2).contDiffAt.of_le
      (by first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))] at h3
    exact h3
  have hmean := r26t8a_o03a_mean
    (fun s => iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha j s) x)
    (fun s => iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha (j + 1) s) x) v h e hv hvh
    (fun s hs0 => horb.derivative alpha j hj ℓ hℓk s hs0 x) hb
  -- the derivative of the quotient is the normalized mean-value remainder
  have hcd : ∀ s : ℝ, 0 ≤ s → ∀ i : ℕ, i ≤ 2 → ContDiffAt ℝ (ℓ : WithTop ℕ∞)
      (r26t8a_ageTest a beta m rho alpha i s) x := fun s hs i hi =>
    ((hC s hs i hi).contDiffAt).of_le (by first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hA := hcd (v + h) hvh j (by omega)
  have hB := hcd v hv j (by omega)
  have hCc := hcd v hv (j + 1) hj2
  have hQf : (fun y : Euc d => h⁻¹ * (r26t8a_ageTest a beta m rho alpha j (v + h) y -
      r26t8a_ageTest a beta m rho alpha j v y) - r26t8a_ageTest a beta m rho alpha (j + 1) v y) =
      (h⁻¹ • (r26t8a_ageTest a beta m rho alpha j (v + h) - r26t8a_ageTest a beta m rho alpha j v)) -
        r26t8a_ageTest a beta m rho alpha (j + 1) v := by
    funext y
    simp [smul_eq_mul]
  have hX : h • (h⁻¹ • (iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha j (v + h)) x -
      iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha j v) x) -
        iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha (j + 1) v) x) =
      (iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha j (v + h)) x -
        iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha j v) x) -
        h • iteratedFDeriv ℝ ℓ (r26t8a_ageTest a beta m rho alpha (j + 1) v) x := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hh0, one_smul]
  have hpos : 0 < ‖h‖ := norm_pos_iff.2 hh0
  have hnorm : ‖h‖ * ‖iteratedFDeriv ℝ ℓ (fun y : Euc d => h⁻¹ * (r26t8a_ageTest a beta m rho alpha j (v + h) y -
      r26t8a_ageTest a beta m rho alpha j v y) - r26t8a_ageTest a beta m rho alpha (j + 1) v y) x‖ ≤
      ‖h‖ * e := by
    have hAB : ContDiffAt ℝ (ℓ : WithTop ℕ∞)
        (r26t8a_ageTest a beta m rho alpha j (v + h) - r26t8a_ageTest a beta m rho alpha j v) x :=
      hA.sub hB
    have hsm : ContDiffAt ℝ (ℓ : WithTop ℕ∞)
        (h⁻¹ • (r26t8a_ageTest a beta m rho alpha j (v + h) - r26t8a_ageTest a beta m rho alpha j v)) x :=
      hAB.const_smul h⁻¹
    rw [hQf, iteratedFDeriv_sub_apply hsm hCc, iteratedFDeriv_const_smul_apply hAB,
      iteratedFDeriv_sub_apply hA hB]
    rw [← norm_smul, hX]
    rw [mul_comm]
    exact hmean
  exact le_of_mul_le_mul_left hnorm hpos

end HRS.MS.R26T8A

end
