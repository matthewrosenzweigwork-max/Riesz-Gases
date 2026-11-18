import HRS.MS.UniqC3d

/-!
# Packet C3, part 5: the bundle `FlowBundle` and the theorem `c3_flow_bundle`

Setting: `IsAdvectingDrift m Cb t b` (`HRS/Whole/AppendixBKernel.lean:61`; by `UniqC2.c2_isAdvectingDrift` for
`b σ = meanFieldDriftW D (ρ (t-σ))`), `IsNegDriftFlow t b Ψ` (with `bij`), a cutoff pair `IsCutoffPair χ χh`,
`1 ≤ d`, `1 ≤ m`, `0 < t`.  Write `L = e^{Cb t}`, `Φ_τ = Function.invFun (Ψ τ)` and
`ς_c^τ = (advCutoff χ Ψ τ c)^2` (`varsigma`).  The constant `K` depends only on `(d,m,Cb,t,χ,χh)`.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open HRS HRS.Whole

namespace HRS.MS.UniqC3

variable {d : ℕ}

/-- The packaged flow and advected-cutoff facts needed by the energy estimate.  All statements are for
`τ ∈ [0,t]` and all centres `c ∈ ℝ^d` unless a lattice is named. -/
structure FlowBundle (d m : ℕ) (Cb t : ℝ) (χ χh : Euc d → ℝ) (b : ℝ → Euc d → Euc d)
    (Ψ : ℝ → Euc d → Euc d) (K : ℝ) : Prop where
  /-- inverse identities, Lipschitz bounds `e^{Cb τ}`, regularity and joint continuity of `Ψ`, `Φ`, `DΨ`, `DΦ` -/
  flow : FlowFacts m Cb t Ψ
  /-- (i) `0 ≤ ς ≤ 1` -/
  range : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c x : Euc d, 0 ≤ varsigma χ Ψ τ c x ∧ varsigma χ Ψ τ c x ≤ 1
  /-- (ii) `ς` is `C^2` with `‖∇ς‖, ‖∇²ς‖ ≤ K` uniformly in `c, τ` -/
  contDiff : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d, ContDiff ℝ 2 (varsigma χ Ψ τ c)
  fderiv_le : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c x : Euc d, ‖fderiv ℝ (varsigma χ Ψ τ c) x‖ ≤ K
  gradient_le : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c x : Euc d, ‖gradient (varsigma χ Ψ τ c) x‖ ≤ K
  hess_le : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c x : Euc d, ‖fderiv ℝ (fderiv ℝ (varsigma χ Ψ τ c)) x‖ ≤ K
  /-- (iii) `tsupport ς ⊆ B̄(Ψ_τ c, 2L)` -/
  supp : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d,
    tsupport (varsigma χ Ψ τ c) ⊆ Metric.closedBall (Ψ τ c) (2 * Real.exp (Cb * t))
  compact_supp : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d, HasCompactSupport (varsigma χ Ψ τ c)
  /-- (iv) `ς = 1` on `B̄(Ψ_τ c, 1/L)` -/
  one_on : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d,
    ∀ x ∈ Metric.closedBall (Ψ τ c) (1 / Real.exp (Cb * t)), varsigma χ Ψ τ c x = 1
  /-- (v) `∂_τ ς = b · ∇ς`, with jointly continuous right side (and `ς`, `∇ς` jointly continuous) -/
  deriv : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c x : Euc d,
    HasDerivWithinAt (fun τ' => varsigma χ Ψ τ' c x)
      (inner ℝ (b τ x) (gradient (varsigma χ Ψ τ c) x)) (Icc 0 t) τ
  cont : ∀ c : Euc d, ContinuousOn (fun p : ℝ × Euc d => varsigma χ Ψ p.1 c p.2)
    (Icc (0 : ℝ) t ×ˢ univ)
  cont_fderiv : ∀ c : Euc d, ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (varsigma χ Ψ p.1 c) p.2)
    (Icc (0 : ℝ) t ×ˢ univ)
  cont_deriv : ∀ c : Euc d, ContinuousOn
    (fun p : ℝ × Euc d => inner ℝ (b p.1 p.2) (gradient (varsigma χ Ψ p.1 c) p.2))
    (Icc (0 : ℝ) t ×ˢ univ)
  /-- (vi) the partner cutoff `advCutoff χh`: values in `[0,1]`, `= 1` on `B̄(Ψ_τ c, 6/L)`, support in
  `B̄(Ψ_τ c, 8L)`, and `1 - advCutoff χh` vanishes at distance `≥ 4 e^{-Kτ}` from `tsupport ς`
  (`FlowD.sep_iii`) -/
  partner_range : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c x : Euc d,
    advCutoff χh Ψ τ c x ∈ Icc (0 : ℝ) 1
  partner_one : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d,
    ∀ x ∈ Metric.closedBall (Ψ τ c) (6 / Real.exp (Cb * t)), advCutoff χh Ψ τ c x = 1
  partner_supp : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d,
    tsupport (advCutoff χh Ψ τ c) ⊆ Metric.closedBall (Ψ τ c) (8 * Real.exp (Cb * t))
  sep : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c x y : Euc d, x ∈ tsupport (varsigma χ Ψ τ c) →
    y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ c y) → 4 * Real.exp (-(K * τ)) ≤ ‖x - y‖
  /-- (vii) multiplicity `N0 = (4⌈√d⌉+1)^d` over the centres `cellPt d z = ⌈√d⌉⁻¹ • ℤ^d` (repaired lattice) and
  `5^d` over the unit lattice `ℤ^d` (`latticePt`, the lattice of `flowCell`) -/
  mult_cell : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
    {z : Fin d → ℤ | x ∈ tsupport (varsigma χ Ψ τ (cellPt d z))}.encard ≤ ((multN d : ℕ) : ℕ∞)
  mult_unit : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
    {z : Fin d → ℤ | x ∈ tsupport (varsigma χ Ψ τ (latticePt z))}.encard ≤ ((5 ^ d : ℕ) : ℕ∞)
  /-- a closed ball of radius `r` meets at most `N(r)` of the supports -/
  ball_cell : ∀ τ ∈ Icc (0 : ℝ) t, ∀ (e : Euc d) (r : ℝ), 0 ≤ r →
    {z : Fin d → ℤ | (Metric.closedBall e r ∩ tsupport (varsigma χ Ψ τ (cellPt d z))).Nonempty}.encard ≤
      ((⌊(2 * ((2 + Real.exp (Cb * t) * r) * (cellScale d : ℝ)) + 1) ^ d⌋₊ : ℕ) : ℕ∞)
  ball_unit : ∀ τ ∈ Icc (0 : ℝ) t, ∀ (e : Euc d) (r : ℝ), 0 ≤ r →
    {z : Fin d → ℤ | (Metric.closedBall e r ∩ tsupport (varsigma χ Ψ τ (latticePt z))).Nonempty}.encard ≤
      ((⌊(2 * (2 + Real.exp (Cb * t) * r) + 1) ^ d⌋₊ : ℕ) : ℕ∞)
  /-- covering in integral form (centres `cellPt`): `∫ G ≤ ∑_z ∫ ς_z G` and `∑_z ∫ ς_z G ≤ N0 ∫ G` -/
  cover_lower : ∀ τ ∈ Icc (0 : ℝ) t, ∀ G : Euc d → ℝ≥0∞, Measurable G →
    ∫⁻ x, G x ≤ ∑' z : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) * G x
  cover_upper : ∀ τ ∈ Icc (0 : ℝ) t, ∀ G : Euc d → ℝ≥0∞, Measurable G →
    ∑' z : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) * G x ≤
      (multN d : ℝ≥0∞) * ∫⁻ x, G x
  /-- energy equivalence with `ulocNormE 0 χ` (`BilipV.uloc_bilip_proof` (v), `m = 0`) -/
  energy_le : ∀ τ ∈ Icc (0 : ℝ) t, ∀ F : Euc d → ℝ,
    (⨆ c : Euc d, eLpNorm (fun x => advCutoff χ Ψ τ c x * F x) 2 volume) ≤
      ENNReal.ofReal (K * Real.exp (K * d * τ)) * AppendixA.ulocNormE 0 χ F
  energy_ge : ∀ τ ∈ Icc (0 : ℝ) t, ∀ F : Euc d → ℝ,
    ENNReal.ofReal (K⁻¹ * Real.exp (-(K * d * τ))) * AppendixA.ulocNormE 0 χ F ≤
      ⨆ c : Euc d, eLpNorm (fun x => advCutoff χ Ψ τ c x * F x) 2 volume
  energy_sq_le : ∀ τ ∈ Icc (0 : ℝ) t, ∀ F : Euc d → ℝ, AEStronglyMeasurable F volume →
    (⨆ c : Euc d, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * F x ^ 2)) ≤
      ENNReal.ofReal (K * Real.exp (K * d * τ)) ^ 2 * AppendixA.ulocNormE 0 χ F ^ 2
  energy_sq_ge : ∀ τ ∈ Icc (0 : ℝ) t, ∀ F : Euc d → ℝ, AEStronglyMeasurable F volume →
    ENNReal.ofReal (K⁻¹ * Real.exp (-(K * d * τ))) ^ 2 * AppendixA.ulocNormE 0 χ F ^ 2 ≤
      ⨆ c : Euc d, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * F x ^ 2)


section Assembly

variable {m : ℕ} {Cb t : ℝ} {Ψ : ℝ → Euc d → Euc d} {χ : Euc d → ℝ}

theorem mult_cell_aux (hd : 1 ≤ d) (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ)
    (hCb : 0 ≤ Cb) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (x : Euc d) :
    {z : Fin d → ℤ | x ∈ tsupport (varsigma χ Ψ τ (cellPt d z))}.encard ≤ ((multN d : ℕ) : ℕ∞) := by
  have hκ : (0 : ℝ) < (cellScale d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast cellScale_pos hd)
  have := mult_scaled hχ hF hCb hκ hτ x
  rw [floor_cell hd] at this
  simpa only [cellPt_eq_scaledPt] using this

theorem mult_unit_aux (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ)
    (hCb : 0 ≤ Cb) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (x : Euc d) :
    {z : Fin d → ℤ | x ∈ tsupport (varsigma χ Ψ τ (latticePt z))}.encard ≤ ((5 ^ d : ℕ) : ℕ∞) := by
  have := mult_scaled hχ hF hCb one_pos hτ x
  have e : (2 * (2 / (1 : ℝ)) + 1) = ((5 : ℕ) : ℝ) := by norm_num
  rw [e, ← Nat.cast_pow, Nat.floor_natCast] at this
  simpa only [latticePt_eq_scaledPt] using this

theorem ball_cell_aux (hd : 1 ≤ d) (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ)
    (hCb : 0 ≤ Cb) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (e : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    {z : Fin d → ℤ | (Metric.closedBall e r ∩ tsupport (varsigma χ Ψ τ (cellPt d z))).Nonempty}.encard ≤
      ((⌊(2 * ((2 + Real.exp (Cb * t) * r) * (cellScale d : ℝ)) + 1) ^ d⌋₊ : ℕ) : ℕ∞) := by
  have hκ : (0 : ℝ) < (cellScale d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast cellScale_pos hd)
  have := ball_scaled hχ hF hCb hκ hτ e hr
  rw [div_inv_eq_mul] at this
  simpa only [cellPt_eq_scaledPt] using this

theorem ball_unit_aux (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ)
    (hCb : 0 ≤ Cb) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (e : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    {z : Fin d → ℤ | (Metric.closedBall e r ∩ tsupport (varsigma χ Ψ τ (latticePt z))).Nonempty}.encard ≤
      ((⌊(2 * (2 + Real.exp (Cb * t) * r) + 1) ^ d⌋₊ : ℕ) : ℕ∞) := by
  have := ball_scaled hχ hF hCb one_pos hτ e hr
  rw [div_one] at this
  simpa only [latticePt_eq_scaledPt] using this

/-- **Packet C3.**  For `1 ≤ d`, `1 ≤ m`, `0 < t`, a cutoff pair `(χ,χh)`, there is `K > 0` (depending only on
`d,m,Cb,t,χ,χh`) such that for every advecting drift `b` and every flow `Ψ` of `-b` the facts of `FlowBundle` hold. -/
theorem c3_flow_bundle (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (Cb t : ℝ) (ht : 0 < t)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb t b → IsNegDriftFlow t b Ψ → FlowBundle d m Cb t χ χh b Ψ K := by
  have hU : AppendixA.IsUlocCutoff χ := hχ.1
  have hR : AppendixALemmas.IsCutoffRad 6 8 χh :=
    ⟨hχ.2.1, hχ.2.2.1, hχ.2.2.2.1, fun x => ⟨(hχ.2.2.2.2.1 x).1, (hχ.2.2.2.2.1 x).2⟩,
      hχ.2.2.2.2.2⟩
  obtain ⟨Kd, hKd, hderiv⟩ := uc3_deriv_bounds m hm Cb t ht χ χh hU hR
  obtain ⟨Ke, hKe, hen⟩ := uc3_energy m Cb t ht χ χh hU hR
  obtain ⟨Ks, hKs, hens⟩ := uc3_energy_sq m Cb t ht χ χh hU hR
  have hKd' : Kd ≤ max (max Kd (max Ke Ks)) Cb := (le_max_left _ _).trans (le_max_left _ _)
  have hKe' : Ke ≤ max (max Kd (max Ke Ks)) Cb :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hKs' : Ks ≤ max (max Kd (max Ke Ks)) Cb :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hKC : Cb ≤ max (max Kd (max Ke Ks)) Cb := le_max_right _ _
  refine ⟨max (max Kd (max Ke Ks)) Cb, lt_of_lt_of_le hKd hKd', fun b Ψ hb hΨ => ?_⟩
  set K : ℝ := max (max Kd (max Ke Ks)) Cb with hKdef
  have hT := ht.le
  have hCb := uc3_Cb_nonneg hT hb
  have hF := uc3_flowFacts hT hb hΨ
  have hL : ∀ τ ∈ Icc (0 : ℝ) t, Real.exp (Cb * τ) ≤ Real.exp (Cb * t) := fun τ hτ =>
    Real.exp_le_exp.2 (by nlinarith [hτ.2])
  have hχ0 : ∀ w : Euc d, χ w ^ 2 ≠ 0 → ‖w‖ < 2 := fun w hw => by
    have : χ w ≠ 0 := fun h0 => hw (by simp [h0])
    simpa using hU.2.2.1 (subset_closure this)
  have hχh0 : ∀ w : Euc d, χh w ≠ 0 → ‖w‖ < 8 := fun w hw => by
    simpa using hχ.2.2.2.1 (subset_closure hw)
  have hsupp : ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d, tsupport (varsigma χ Ψ τ c) ⊆
      Metric.closedBall (Ψ τ c) (2 * Real.exp (Cb * t)) := fun τ hτ c =>
    (tsupport_sub_closedBall hF hτ c (fun y => χ y ^ 2) (r := 2) (by norm_num) hχ0).trans
      (Metric.closedBall_subset_closedBall
        (mul_le_mul_of_nonneg_left (hL τ hτ) (by norm_num)))
  refine
  { flow := hF
    range := fun τ _ c x => varsigma_range hU τ c x
    contDiff := fun τ hτ c => varsigma_contDiff hU hm hF hτ c
    fderiv_le := fun τ hτ c x => ((hderiv b Ψ hb hΨ τ hτ c).1 x).trans hKd'
    gradient_le := fun τ hτ c x => by
      have h1 := ((hderiv b Ψ hb hΨ τ hτ c).1 x).trans hKd'
      show ‖(InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (varsigma χ Ψ τ c) x)‖ ≤ K
      rwa [LinearIsometryEquiv.norm_map]
    hess_le := fun τ hτ c x => ((hderiv b Ψ hb hΨ τ hτ c).2 x).trans hKd'
    supp := hsupp
    compact_supp := fun τ hτ c =>
      (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hsupp τ hτ c)
    one_on := fun τ hτ c x hx => by
      have := eq_one_of_mem_ball hF hCb hτ c (fun y => χ y ^ 2) (r := 1)
        (fun w hw => by simp [hU.2.2.2.2 w (by rwa [mem_closedBall_zero_iff])]) hx
      exact this
    deriv := fun τ hτ c x => varsigma_hasDerivWithinAt hT hb hΨ hU c x hτ
    cont := fun c => (varsigma_cont hb hU hm hF c).1
    cont_fderiv := fun c => (varsigma_cont hb hU hm hF c).2.1
    cont_deriv := fun c => (varsigma_cont hb hU hm hF c).2.2
    partner_range := fun τ _ c x => hχ.2.2.2.2.1 _
    partner_one := fun τ hτ c x hx =>
      eq_one_of_mem_ball hF hCb hτ c χh (r := 6) (fun w hw => hχ.2.2.2.2.2 w
        (by rwa [mem_closedBall_zero_iff])) hx
    partner_supp := fun τ hτ c =>
      (tsupport_sub_closedBall hF hτ c χh (r := 8) (by norm_num) hχh0).trans
        (Metric.closedBall_subset_closedBall
          (mul_le_mul_of_nonneg_left (hL τ hτ) (by norm_num)))
    sep := fun τ hτ c x y hx hy => by
      have hsub : Function.support (varsigma χ Ψ τ c) ⊆
          Function.support (fun x => χ (Function.invFun (Ψ τ) x - c)) :=
        fun x hx h0 => hx (by simp [varsigma, advCutoff, h0])
      have hx' : x ∈ tsupport (fun x => χ (Function.invFun (Ψ τ) x - c)) := closure_mono hsub hx
      exact HRS.MS.FlowD.sep_iii Cb K hKC χ χh hU hR (fun τ => Function.invFun (Ψ τ)) Ψ τ hτ.1
        (hF.lip_inv τ hτ) c x y hx' hy
    mult_cell := fun τ hτ x => mult_cell_aux hd hU hF hCb hτ x
    mult_unit := fun τ hτ x => mult_unit_aux hU hF hCb hτ x
    ball_cell := fun τ hτ e r hr => ball_cell_aux hd hU hF hCb hτ e hr
    ball_unit := fun τ hτ e r hr => ball_unit_aux hU hF hCb hτ e hr
    cover_lower := fun τ hτ G hG => cover_lower hd hU hF hτ G hG
    cover_upper := fun τ hτ G hG => cover_upper hd hU hF hCb hτ G hG
    energy_le := fun τ hτ F => (hen K hKe' b Ψ hb hΨ τ hτ F).2
    energy_ge := fun τ hτ F => (hen K hKe' b Ψ hb hΨ τ hτ F).1
    energy_sq_le := fun τ hτ F hFm => (hens K hKs' b Ψ hb hΨ τ hτ F hFm).2
    energy_sq_ge := fun τ hτ F hFm => (hens K hKs' b Ψ hb hΨ τ hτ F hFm).1 }

end Assembly

end HRS.MS.UniqC3
