import HRS.MS.Mov63FAux6

/-!
# S6.3, packet N9 (part 1): plan and the three conversions from `MovInitialClass`

Namespace `HRS.MS.Mov63`, prefix `mnh_`.

## Plan: `mov_nonlinear_proof : type_of% @HRS.Whole.mov_nonlinear`

Given `hd hs0 hsd hβ hq`, `j ≥ 1`, `m > d/2 + j + 6`, `ρ₀` thermal.  `H : Mov2dTh d s β q ρ₀ := ⟨hd,hs0,hsd,hβ,hq,hρ⟩`.
`mov63_decay_f0 H hj` (N8, `Mov63GAux19`) gives `c₁ > 0` and, for this `m`, constants `ε_*, r, c, C₀` with
`0 < ε_* ≤ 1/4`, `0 < r`, `0 < c`, `0 ≤ C₀`.  The constants of `mov_nonlinear` are `(ε_*, r, c₀ := c₁/2, c, C := max C₀ 2)`.

For `f0` with `MovInitialClass ρ₀ j m ε_* f0` (fields `cb : MemCb (j+1) f0`, `osc`, `mean`, `small`):

* hypotheses of `mov63_decay_f0` on `f0`:
  - `ContDiff ℝ 3 f0` (for `j = 1`, `MemCb 2` gives only `C²`): `mnh_contDiff3`: `√ρ f0 ∈ Σ^m`, `3 + d/2 < m`, so `√ρ f0` has a `C³`
    representative (`mn_sobolev_emb_gen`), equal to `√ρ f0` everywhere because both are continuous (`mn_ae_eq_cont`; `f0` is
    continuous by `cb`), and `f0 = g/√ρ` with `√ρ > 0` smooth;
  - `MemCb (j+1) f0` and `MemOsc` are the fields `cb`, `osc`;
  - `MovMassZero ρ₀ _ (ofFun (√ρ f0))`: `mnh_massZero`: `⟨√ρ, √ρ f0⟩_{L²} = ∫ ρ f0 = 0` (`mean`);
  - `movInitialNorm ρ₀ j m f0 ≤ ε_*`: the field `small` (definitional);
* conclusions: the N5-N7-N8 solution `ρ_t = mneP d ρ₀ hm3 v` gives
  - `MovInSmallClass .. r (c₁/2) f0 ρ_t`  (conjunct 1);
  - `IsProbDensity (ρ_t)`: the `density` field of `solution` (`T := t`); `0 < ρ_t x` from `ρ₀/2 ≤ ρ_t`, `ρ₀ > 0` (conjunct 2);
  - `C⁻¹ρ₀ ≤ ρ_t ≤ Cρ₀` from `ρ₀/2 ≤ ρ_t ≤ 2ρ₀` and `C ≥ 2` (conjunct 3);
  - both `MovDecayBounds` with constant `C₀`, enlarged to `C ≥ C₀` by `mnh_decay_mono_C` (needs `K ≥ 0`: `ε_* > 0` and
    `movInitialNorm ≥ 0`, `mnh_initialNorm_nonneg`) (conjuncts 4, 5);
  - the `lintegral` bound of `mov63_decay_f0` (conjunct 6);
  - uniqueness: `mov_nl_unique_conjunct` (N4) applied to the class membership (conjunct 7).
* the `ψ`-class conjunct: `mnh_psi_class`: `ψ ∈ C_c^∞`, `∫ψρ₀ = 0`: `MemCb (j+1) (εψ)` (smooth, compact support), `√ρ₀ ψ` is smooth with compact
  support hence Schwartz (`memOsc_schwartz`), `∫ (εψ) ρ₀ = 0`, and `small` by homogeneity of `cbNorm`/`oscNorm`
  with `ε₀ := ε_*/(A+1)`, `A = cbNorm (j+1) ψ + oscNorm m (√ρ₀ ψ)`.

No conjunct is false and no hypothesis is insufficient: `ρ₀` is smooth and positive by `Mov2dTh`
(`mnc_rho_smooth`, `mnb_rhoData`), which is what makes the `f0 ∈ C³` derivation and the `ψ`-class conjunct work.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Initial

variable {j m : ℕ} {εstar : ℝ}

/-- `f0 ∈ C³` from `cb` (continuity) and `osc` (`√ρ f0 ∈ Σ^m`, `m > d/2 + 3`). -/
lemma mnh_contDiff3 (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m) {f0 : Euc d → ℝ}
    (hcb : MemCb (j + 1) f0) (hj : 1 ≤ j) (hosc : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) :
    ContDiff ℝ 3 f0 := by
  have hn : ((3 : ℕ) : ℝ) + d / 2 < m := by push_cast; linarith
  obtain ⟨C, -, hC⟩ := mn_sobolev_emb_gen 3 m hn
  obtain ⟨g, hg, hfg, -⟩ := hC _ hosc
  have hf0c : Continuous f0 := hcb.1.continuous
  have hRD := mnb_rhoData H
  have hsc : Continuous (fun x => Real.sqrt (ρ x)) := hRD.sqrt_smooth.continuous
  have heq : (fun x => Real.sqrt (ρ x) * f0 x) = g :=
    mn_ae_eq_cont (hsc.mul hf0c) hg.continuous hfg
  have hf : f0 = fun x => g x / Real.sqrt (ρ x) := by
    funext x
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hRD.pos x)
    rw [← heq]
    field_simp
  rw [hf]
  have h1 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ x)) :=
    hRD.sqrt_smooth.of_le (by simp)
  have h2 := hg.div h1 (fun x => (Real.sqrt_pos.2 (hRD.pos x)).ne')
  exact_mod_cast h2

/-- The mean-zero condition `∫ f0 ρ = 0` is `MovMassZero` of `ofFun (√ρ f0)`. -/
lemma mnh_massZero (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m) {f0 : Euc d → ℝ}
    (hosc : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) (hmean : ∫ x, f0 x * ρ x = 0) :
    MovMassZero ρ (mnd_m_nonneg hm) (OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) := by
  have hL2 : MemLp (fun x => Real.sqrt (ρ x) * f0 x) 2 (volume : Measure (Euc d)) :=
    (mo_mono (mnd_m_nonneg hm) hosc).1.1
  unfold MovMassZero
  rw [mov2d_j_ofFun (mnd_m_nonneg hm) hosc, mov2d_Phi_ofFun hL2, mnb_inner_sqrt H hL2]
  have hRD := mnb_rhoData H
  have : (fun x => Real.sqrt (ρ x) * (Real.sqrt (ρ x) * f0 x)) = fun x => f0 x * ρ x := by
    funext x
    have h0 : 0 ≤ ρ x := (hRD.pos x).le
    rw [← mul_assoc, Real.mul_self_sqrt h0, mul_comm]
  rw [this]
  exact hmean

lemma mnh_initialNorm_nonneg (f0 : Euc d → ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) :
    0 ≤ movInitialNorm ρ₀ j m f0 := by
  unfold movInitialNorm cbNorm
  have h1 : 0 ≤ ∑ i ∈ Finset.range (j + 1 + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ i f0 z‖ :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ oscNorm (m : ℝ) (fun x => Real.sqrt (ρ₀ x) * f0 x) := Real.sqrt_nonneg _
  linarith

/-- Monotonicity of `MovDecayBounds` in the constant `C` (for amplitude `K ≥ 0`). -/
lemma mnh_decay_mono_C {j m : ℕ} {c C C' K : ℝ} {ρ₁ : ℝ → Euc d → ℝ} (hK : 0 ≤ K) (hC : C ≤ C')
    (h : MovDecayBounds d s q β ρ j m c C K ρ₁) : MovDecayBounds d s q β ρ j m c C' K ρ₁ := by
  intro t ht
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h t ht
  have hm : C * K * Real.exp (-c * t) ≤ C' * K * Real.exp (-c * t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hK) (Real.exp_pos _).le
  exact ⟨⟨h1, h2.trans hm⟩, h3, h4, h5.trans (ENNReal.ofReal_le_ofReal hm)⟩

end Initial

/-! ### The `ψ`-class conjunct -/

section Psi

variable {j m : ℕ}

lemma mnh_cb_smul {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (k : ℕ) (ε : ℝ) :
    MemCb k (fun x => ε * ψ x) := by
  have hsm : ContDiff ℝ (k : WithTop ℕ∞) ψ := hψ.of_le (by exact_mod_cast le_top)
  refine ⟨contDiff_const.mul hsm, fun i hi => ?_⟩
  have hbd : BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ i ψ x‖) := by
    have hcont : Continuous fun x => ‖iteratedFDeriv ℝ i ψ x‖ :=
      (hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    exact hcont.bddAbove_range_of_hasCompactSupport (hc.iteratedFDeriv i).norm
  obtain ⟨M, hM⟩ := hbd
  refine ⟨|ε| * M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hEq : (fun x => ε * ψ x) = ε • ψ := by funext x; simp
  have hd : ContDiffAt ℝ (i : WithTop ℕ∞) ψ x :=
    (hψ.of_le (by exact_mod_cast le_top)).contDiffAt
  show ‖iteratedFDeriv ℝ i (fun x => ε * ψ x) x‖ ≤ |ε| * M
  rw [hEq, iteratedFDeriv_const_smul_apply hd, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM ⟨x, rfl⟩) (abs_nonneg _)

lemma mnh_cbNorm_smul {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (k : ℕ) (ε : ℝ) :
    cbNorm k (fun x => ε * ψ x) = |ε| * cbNorm k ψ := by
  unfold cbNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hbd : BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ i ψ x‖) := by
    have hcont : Continuous fun x => ‖iteratedFDeriv ℝ i ψ x‖ :=
      (hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    exact hcont.bddAbove_range_of_hasCompactSupport (hc.iteratedFDeriv i).norm
  have hEq : (fun x => ε * ψ x) = ε • ψ := by funext x; simp
  have : ∀ x, ‖iteratedFDeriv ℝ i (fun x => ε * ψ x) x‖ = |ε| * ‖iteratedFDeriv ℝ i ψ x‖ := fun x => by
    have hd : ContDiffAt ℝ (i : WithTop ℕ∞) ψ x :=
      (hψ.of_le (by exact_mod_cast le_top)).contDiffAt
    rw [hEq, iteratedFDeriv_const_smul_apply hd, norm_smul, Real.norm_eq_abs]
  simp_rw [this]
  exact (Real.mul_iSup_of_nonneg (abs_nonneg ε) _).symm

lemma mnh_sqrt_psi_schwartz (H : Mov2dTh d s β q ρ) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) : ∃ Φ : SchwartzMap (Euc d) ℝ, (⇑Φ : Euc d → ℝ) = fun x => Real.sqrt (ρ x) * ψ x := by
  have hRD := mnb_rhoData H
  exact ⟨(hc.mul_left (f := fun x => Real.sqrt (ρ x))).toSchwartzMap (hRD.sqrt_smooth.mul hψ), rfl⟩

lemma mnh_osc_smul (H : Mov2dTh d s β q ρ) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (μ : ℝ) :
    MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * (μ * ψ x)) := by
  obtain ⟨Φ, hΦ⟩ := mnh_sqrt_psi_schwartz H hψ hc
  have : (fun x => Real.sqrt (ρ x) * (μ * ψ x)) = ⇑(μ • Φ) := by
    funext x
    have := congrFun hΦ x
    simp only [smul_apply, smul_eq_mul, this]
    ring
  rw [this]
  exact memOsc_schwartz _ _

lemma mnh_oscNorm_smul {ψ : Euc d → ℝ} (μ : ℝ) :
    oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * (μ * ψ x)) = |μ| * oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ x) := by
  rw [← oscNorm_const_mul]
  congr 1
  funext x
  ring

/-- The `ψ`-class conjunct of `mov_nonlinear`. -/
theorem mnh_psi_class (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m) {εstar : ℝ} (hε : 0 < εstar)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hmean : ∫ x, ψ x * ρ x = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| < ε₀ → MovInitialClass ρ j m εstar (fun x => ε * ψ x) := by
  set A : ℝ := cbNorm (j + 1) ψ + oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ x) with hA
  have hA0 : 0 ≤ A := by
    have h1 : 0 ≤ cbNorm (j + 1) ψ := by
      unfold cbNorm
      exact Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * ψ x) := Real.sqrt_nonneg _
    rw [hA]; linarith
  refine ⟨εstar / (A + 1), by positivity, fun ε hε' => ⟨mnh_cb_smul hψ hc _ ε, mnh_osc_smul H hψ hc ε, ?_, ?_⟩⟩
  · have : (fun x => ε * ψ x * ρ x) = fun x => ε * (ψ x * ρ x) := by funext x; ring
    rw [this, integral_const_mul, hmean, mul_zero]
  · rw [mnh_cbNorm_smul hψ hc, mnh_oscNorm_smul, ← mul_add]
    rw [← hA]
    have h1 : |ε| * (A + 1) ≤ εstar := by
      rw [lt_div_iff₀ (by positivity)] at hε'
      linarith
    nlinarith [abs_nonneg ε]

end Psi

end HRS.MS.Mov63

end
