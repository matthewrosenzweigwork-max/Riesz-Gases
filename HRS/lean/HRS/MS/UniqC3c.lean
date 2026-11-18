import HRS.MS.UniqC3b

/-!
# Packet C3, part 3: covering by the weights `ς_c^τ` over a lattice of centres

For the scaled lattice `a • ℤ^d`: the multiplicity of the supports `tsupport ς_{c}` over the centres, the number of
supports meeting a ball, and (for the repaired lattice `cellPt d z = ⌈√d⌉⁻¹ • ℤ^d`, whose closed balls of radius `1/2`
cover `ℝ^d`) the integral comparison `∫ G ≤ ∑_z ∫ ς_z G` and `∑_z ∫ ς_z G ≤ N0 ∫ G`.
All counts depend on the flow only through the Lipschitz constant of `Ψ_τ^{-1}`.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open HRS HRS.Whole

namespace HRS.MS.UniqC3

variable {d : ℕ}

/-- The scaled lattice `a • ℤ^d`. -/
def scaledPt (a : ℝ) (z : Fin d → ℤ) : Euc d := a • latticePt z

/-- `⌈√d⌉` as a natural number. -/
def cellScale (d : ℕ) : ℕ := ⌈Real.sqrt d⌉₊

/-- Multiplicity bound `N0 = (4⌈√d⌉+1)^d` for the lattice `cellPt`. -/
def multN (d : ℕ) : ℕ := (4 * cellScale d + 1) ^ d

theorem cellPt_eq_scaledPt (z : Fin d → ℤ) : cellPt d z = scaledPt ((cellScale d : ℝ)⁻¹) z := by
  unfold cellPt scaledPt cellScale
  rw [← Int.natCast_ceil_eq_ceil (Real.sqrt_nonneg _)]
  push_cast
  rfl

theorem latticePt_eq_scaledPt (z : Fin d → ℤ) : latticePt z = scaledPt 1 z := by
  simp [scaledPt]

/-- Lattice points of `a • ℤ^d` within distance `r` of `w`: a finset of at most `(2r/a+1)^d`. -/
theorem count_scaled {a : ℝ} (ha : 0 < a) (w : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    ∃ F : Finset (Fin d → ℤ), (∀ z, ‖w - scaledPt a z‖ ≤ r → z ∈ F) ∧
      (F.card : ℝ) ≤ (2 * (r / a) + 1) ^ d := by
  obtain ⟨F, hF1, hF2⟩ := HRS.MS.FlowD.box_finset (fun i => w i / a) (r / a) (by positivity)
  refine ⟨F, fun z hz => hF1 z fun i => ?_, hF2⟩
  have h1 : |w i - a * (z i : ℝ)| ≤ r := by
    have := PiLp.norm_apply_le (w - scaledPt a z) i
    have e : (w - scaledPt a z) i = w i - a * (z i : ℝ) := by
      simp [scaledPt, HRS.MS.FlowD.latticePt_apply]
    rw [e, Real.norm_eq_abs] at this
    exact this.trans hz
  have e2 : (z i : ℝ) - w i / a = -((w i - a * (z i : ℝ)) / a) := by field_simp; ring
  rw [e2, abs_neg, abs_div, abs_of_pos ha]
  exact (div_le_div_iff_of_pos_right ha).2 h1

/-- Every point is within `1/2` of a point of the lattice `cellPt` (`d ≥ 1`). -/
theorem exists_cellPt_near (hd : 1 ≤ d) (w : Euc d) : ∃ z : Fin d → ℤ, ‖w - cellPt d z‖ ≤ 1 / 2 := by
  set κ : ℝ := (⌈Real.sqrt d⌉ : ℝ) with hκ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hκ1 : Real.sqrt d ≤ κ := Int.le_ceil _
  have hκ0 : 0 < κ := lt_of_lt_of_le (Real.sqrt_pos.2 hd0) hκ1
  have hκ2 : (d : ℝ) ≤ κ ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hκ1 2
    rwa [Real.sq_sqrt hd0.le] at this
  refine ⟨fun i => round (κ * w i), ?_⟩
  have hi : ∀ i, (w - cellPt d (fun i => round (κ * w i))) i ^ 2 ≤ (1 / (2 * κ)) ^ 2 := by
    intro i
    have e : (w - cellPt d (fun i => round (κ * w i))) i = w i - κ⁻¹ * (round (κ * w i) : ℝ) := by
      simp [cellPt, hκ, HRS.MS.FlowD.latticePt_apply]
    rw [e]
    have h1 : |κ * w i - (round (κ * w i) : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have e2 : w i - κ⁻¹ * (round (κ * w i) : ℝ) = κ⁻¹ * (κ * w i - (round (κ * w i) : ℝ)) := by
      field_simp
    rw [e2]
    have : |κ⁻¹ * (κ * w i - (round (κ * w i) : ℝ))| ≤ 1 / (2 * κ) := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hκ0)]
      calc κ⁻¹ * |κ * w i - (round (κ * w i) : ℝ)| ≤ κ⁻¹ * (1 / 2) :=
            mul_le_mul_of_nonneg_left h1 (inv_pos.2 hκ0).le
        _ = 1 / (2 * κ) := by field_simp
    exact (sq_le_sq' (by linarith [abs_le.1 this]) (by linarith [abs_le.1 this]))
  have hsum : ‖w - cellPt d (fun i => round (κ * w i))‖ ^ 2 ≤ (1 / 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, (w - cellPt d (fun i => round (κ * w i))) i ^ 2 ≤ ∑ _i : Fin d, (1 / (2 * κ)) ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = d * (1 / (2 * κ)) ^ 2 := by simp
      _ ≤ (1 / 2) ^ 2 := by
          rw [show (1 / (2 * κ)) ^ 2 = 1 / (4 * κ ^ 2) by field_simp; ring, mul_one_div,
            div_le_iff₀ (by positivity)]
          nlinarith
  exact abs_le_of_sq_le_sq' hsum (by norm_num) |>.2

section Covering

variable {m : ℕ} {Cb t : ℝ} {Ψ : ℝ → Euc d → Euc d} {χ : Euc d → ℝ}

/-- `tsupport ς_c ⊆ {x | ‖Ψ_τ^{-1} x - c‖ ≤ 2}`, and `ς_c x ≠ 0 → ‖Ψ_τ^{-1} x - c‖ < 2`. -/
theorem varsigma_ne_zero (hχ : AppendixA.IsUlocCutoff χ) (τ : ℝ) (c x : Euc d)
    (h : varsigma χ Ψ τ c x ≠ 0) : ‖Function.invFun (Ψ τ) x - c‖ < 2 := by
  have h1 : χ (Function.invFun (Ψ τ) x - c) ≠ 0 := fun h0 => h (by simp [varsigma, advCutoff, h0])
  have h2 : Function.invFun (Ψ τ) x - c ∈ tsupport χ := subset_closure h1
  simpa using hχ.2.2.1 h2

theorem tsupport_varsigma_sub (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ)
    (hCb : 0 ≤ Cb) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (c : Euc d) :
    tsupport (varsigma χ Ψ τ c) ⊆ {x | ‖Function.invFun (Ψ τ) x - c‖ ≤ 2} := by
  have hc : Continuous (Function.invFun (Ψ τ)) :=
    HRS.MS.FlowD.continuous_of_lip _ (Real.exp_pos _).le _ (hF.lip_inv τ hτ)
  refine closure_minimal (fun x hx => ?_) (isClosed_le (by fun_prop) continuous_const)
  exact (varsigma_ne_zero hχ τ c x hx).le

/-- Multiplicity of the supports over the lattice `a • ℤ^d`. -/
theorem mult_scaled (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ) (hCb : 0 ≤ Cb)
    {a : ℝ} (ha : 0 < a) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (x : Euc d) :
    {z : Fin d → ℤ | x ∈ tsupport (varsigma χ Ψ τ (scaledPt a z))}.encard ≤
      ((⌊(2 * (2 / a) + 1) ^ d⌋₊ : ℕ) : ℕ∞) := by
  obtain ⟨F, hF1, hF2⟩ := count_scaled ha (Function.invFun (Ψ τ) x) (r := 2) (by norm_num)
  have hsub : {z : Fin d → ℤ | x ∈ tsupport (varsigma χ Ψ τ (scaledPt a z))} ⊆ ↑F := by
    intro z hz
    refine hF1 z ?_
    have : ‖Function.invFun (Ψ τ) x - scaledPt a z‖ ≤ 2 :=
      tsupport_varsigma_sub hχ hF hCb hτ (scaledPt a z) hz
    exact this
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast Nat.le_floor hF2

/-- Number of supports meeting a closed ball. -/
theorem ball_scaled (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ) (hCb : 0 ≤ Cb)
    {a : ℝ} (ha : 0 < a) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (e : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    {z : Fin d → ℤ | (Metric.closedBall e r ∩ tsupport (varsigma χ Ψ τ (scaledPt a z))).Nonempty}.encard ≤
      ((⌊(2 * ((2 + Real.exp (Cb * t) * r) / a) + 1) ^ d⌋₊ : ℕ) : ℕ∞) := by
  have hE : Real.exp (Cb * τ) ≤ Real.exp (Cb * t) := Real.exp_le_exp.2 (by nlinarith [hτ.2])
  obtain ⟨F, hF1, hF2⟩ := count_scaled ha (Function.invFun (Ψ τ) e) (r := 2 + Real.exp (Cb * t) * r)
    (by positivity)
  have hsub : {z : Fin d → ℤ |
      (Metric.closedBall e r ∩ tsupport (varsigma χ Ψ τ (scaledPt a z))).Nonempty} ⊆ ↑F := by
    rintro z ⟨x, hxb, hxs⟩
    refine hF1 z ?_
    have h1 : ‖Function.invFun (Ψ τ) x - scaledPt a z‖ ≤ 2 :=
      tsupport_varsigma_sub hχ hF hCb hτ (scaledPt a z) hxs
    have h2 := hF.lip_inv τ hτ x e
    rw [Metric.mem_closedBall, dist_eq_norm] at hxb
    calc ‖Function.invFun (Ψ τ) e - scaledPt a z‖
        ≤ ‖Function.invFun (Ψ τ) e - Function.invFun (Ψ τ) x‖ +
          ‖Function.invFun (Ψ τ) x - scaledPt a z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Real.exp (Cb * t) * r + 2 := by
          refine add_le_add ?_ h1
          rw [norm_sub_rev]
          calc _ ≤ Real.exp (Cb * τ) * ‖x - e‖ := h2
            _ ≤ Real.exp (Cb * t) * r := by
                gcongr
      _ = 2 + Real.exp (Cb * t) * r := add_comm _ _
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast Nat.le_floor hF2

end Covering

end HRS.MS.UniqC3
