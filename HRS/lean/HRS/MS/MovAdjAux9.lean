import HRS.MS.MovAdjAux8

/-!
# S6.7 (packet P2, part 4): the bridge identity

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_bridge`: for a classical adjoint solution `f` (stationary coefficient, terminal datum `φ` at `t`), `0 ≤ r ≤ t`, and `v₀ ∈ L²_0` in the
Schwartz core, `∫ f_r √ρ v₀ = ∫ φ √ρ (T(t-r) v₀)`: the function `g(σ) = ⟨f_{r+σ}√ρ, T(σ)v₀⟩` is continuous on `[0,t-r]` with right derivative `0`
on `(0,t-r)` (`s67a_hasDeriv`, `s67_T_deriv`, the duality identity `s67_duality`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The derivative of `g` at a point of `(0,t-r)` vanishes. -/
theorem s67_g_deriv (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f) (ht : 0 ≤ t)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {φ₀ : 𝓢R} {v₀ : MovL2Zero ρ}
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v₀ x = φ₀ x)
    (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d))) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (t - r)) :
    HasDerivWithinAt (fun τ => inner ℝ ((s67a_memLp hf ht r hgL τ).toLp (s67a f ρ r t τ))
      ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))) 0 (Set.Ici σ) σ := by
  have hσ0 : 0 ≤ σ := hσ.1.le
  have hr1 : 0 < r + σ := by linarith [hr.1, hσ.1]
  have hr2 : r + σ < t := by linarith [hσ.2]
  have hr'mem : r + σ ∈ Set.Icc (0 : ℝ) t := ⟨hr1.le, hr2.le⟩
  obtain ⟨φ', hφ', w, hw, hwd⟩ := s67_T_deriv H ψ0 hψ0 hv hσ0
  obtain ⟨a', ha', ha'def, hAd⟩ := s67a_hasDeriv H hf ht hr hgL hσ
  have hb : HasDerivWithinAt (fun τ => ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
      (-(w : Lp ℝ 2 (volume : Measure (Euc d)))) (Set.Ici σ) σ := by
    have h := (Submodule.subtypeL (MovL2Zero ρ)).hasFDerivAt.comp_hasDerivWithinAt σ hwd
    exact h.congr_deriv (by simp)
  have hpair := hAd.inner ℝ hb
  have hclσ : s67clamp r t σ = r + σ := s67clamp_eq hr1.le hr2.le
  have hu : MemCb 2 (f (r + σ)) := hf.isC12TestRd.memCb hr'mem
  have hdual := s67_duality H hu φ' (r + σ)
  refine hpair.congr_deriv ?_
  have hw' : (w : Lp ℝ 2 (volume : Measure (Euc d))) =ᵐ[volume] fun x => movS d s β ρ (⇑φ') x := hw
  have hφ'' : ((mov2d_T H ψ0 hψ0 σ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) =ᵐ[volume]
      fun x => φ' x := hφ'
  have t1 : inner ℝ ((s67a_memLp hf ht r hgL σ).toLp (s67a f ρ r t σ)) (-(w : Lp ℝ 2 (volume : Measure (Euc d)))) =
      -∫ x, f (r + σ) x * (Real.sqrt (ρ x) * movS d s β ρ (⇑φ') x) := by
    rw [inner_neg_right, s67_inner_toLp_left, neg_inj]
    refine integral_congr_ae ?_
    filter_upwards [hw'] with x hx
    unfold s67a
    rw [hclσ, hx]; ring
  have t2 : inner ℝ (ha'.toLp a') ((mov2d_T H ψ0 hψ0 σ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) =
      -∫ x, generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * φ' x) := by
    rw [s67_inner_toLp_left, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hφ''] with x hx
    rw [hx, ha'def x]
    ring
  rw [t1, t2, hdual]
  ring

set_option maxHeartbeats 1600000 in
/-- The bridge (the identity for a fixed `v₀` of the Schwartz core). -/
theorem s67_bridge (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {φ₀ : 𝓢R} {v₀ : MovL2Zero ρ}
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v₀ x = φ₀ x) :
    ∫ x, f r x * (Real.sqrt (ρ x) * movFun v₀ x) =
      ∫ x, φ x * (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 (t - r) v₀) x) := by
  have ht : 0 ≤ t := hr.1.trans hr.2
  have hTs := mov2d_isSemigroup H ψ0 hψ0
  rcases eq_or_lt_of_le hr.2 with hrt | hrt
  · subst hrt
    rw [sub_self, mov2d_T_zero H ψ0 hψ0, hf.terminal]
    rfl
  have hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  have hρ := mnb_rhoData H
  have hσ1 : (0 : ℝ) < t - r := sub_pos.2 hrt
  set g : ℝ → ℝ := fun τ => inner ℝ ((s67a_memLp hf ht r hgL τ).toLp (s67a f ρ r t τ))
      ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) with hg
  have hAc := (s67a_cont hf ht r hgL hρ.smooth.continuous).mono (Set.subset_univ (Set.Icc 0 (t - r)))
  have hbc : ContinuousOn (fun τ => ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
      (Set.Icc 0 (t - r)) := by
    have h := (mov2d_T_cont H ψ0 hψ0 v₀).mono (fun τ (hτ : τ ∈ Set.Icc (0 : ℝ) (t - r)) => hτ.1)
    exact continuous_subtype_val.comp_continuousOn h
  have hgc : ContinuousOn g (Set.Icc 0 (t - r)) := hAc.inner hbc
  have hconst : ∀ ε ∈ Set.Ioo (0 : ℝ) (t - r), g (t - r) = g ε := by
    intro ε hε
    have hc : ContinuousOn g (Set.Icc ε (t - r)) := hgc.mono (Set.Icc_subset_Icc hε.1.le le_rfl)
    exact constant_of_has_deriv_right_zero hc
      (fun σ hσ => s67_g_deriv H ψ0 hψ0 hf ht hr hv hgL ⟨hε.1.trans_le hσ.1, hσ.2⟩)
      (t - r) ⟨hε.2.le, le_rfl⟩
  have h0 : g 0 = g (t - r) := by
    have hlim : Tendsto g (𝓝[Set.Ioo (0 : ℝ) (t - r)] 0) (𝓝 (g 0)) :=
      ((hgc 0 ⟨le_rfl, hσ1.le⟩).mono (Set.Ioo_subset_Icc_self)).tendsto
    have hlim2 : Tendsto g (𝓝[Set.Ioo (0 : ℝ) (t - r)] 0) (𝓝 (g (t - r))) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact hconst ε hε)
    haveI : (𝓝[Set.Ioo (0 : ℝ) (t - r)] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot hσ1
    exact tendsto_nhds_unique hlim hlim2
  have hg0 : g 0 = ∫ x, f r x * (Real.sqrt (ρ x) * movFun v₀ x) := by
    show inner ℝ ((s67a_memLp hf ht r hgL 0).toLp (s67a f ρ r t 0))
      ((mov2d_T H ψ0 hψ0 0 v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = _
    rw [s67_inner_toLp_left]
    have hcl0 : s67clamp r t 0 = r := by
      rw [s67clamp_eq (by simpa using hr.1) (by simpa using hr.2)]; ring
    rw [mov2d_T_zero H ψ0 hψ0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    unfold s67a
    rw [hcl0]
    show f r x * Real.sqrt (ρ x) * ((v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) x = _
    unfold movFun
    ring
  have hgt : g (t - r) = ∫ x, φ x * (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 (t - r) v₀) x) := by
    show inner ℝ ((s67a_memLp hf ht r hgL (t - r)).toLp (s67a f ρ r t (t - r)))
      ((mov2d_T H ψ0 hψ0 (t - r) v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = _
    rw [s67_inner_toLp_left]
    have hclt : s67clamp r t (t - r) = t := by
      rw [s67clamp_eq (by linarith) (by linarith)]; ring
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    unfold s67a
    rw [hclt, hf.terminal]
    unfold movFun
    ring
  rw [← hg0, ← hgt, h0]

end HRS.MS.MovAdj
