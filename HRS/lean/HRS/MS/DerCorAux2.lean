import HRS.MS.DerCorAux1
import HRS.MS.ThCorrDilAux2

/-!
# S4.8 `derivative_corrector`, part 2: perturbed references, the derivative-only Poisson solve, the frozen row

Namespace `HRS.MS.S48`; helper lemmas carry the prefix `s48_`.  No existing file is edited.

* `s48_poisson_deriv`: `affine_poisson_deriv_proof` (S4.8b) with constants uniform for `q ∈ [qm, qp]`
  (the dilation `λ = √(qm/q) ≤ 1`, as in `HRS.MS.TcQ`).
* `s48_L_deriv`, `s48_tilt`, `s48_ref_data`: the compact relative perturbations `(1+εψ)ρ_*` of S4.7 satisfy the same
  reference data (`TcRef` to any order, drift `B_ε = B_* + ε∇ψ/(1+εψ) ∈ C_b^m`, second moment) as the thermal density,
  with constants independent of `ε` (only `|ε| |ψ| ≤ 1/2` is used; a smooth cut-off equal to `(1+u)⁻¹` on `[-1/2, 1/2]`
  and the Faà di Bruno bound `norm_iteratedFDeriv_comp_le` give the derivative bounds).
* `derivative_corrector_proof : type_of% @HRS.Whole.derivative_corrector` (tie in `DerCorTie.lean`).

No statement was adjusted.  The integer `J` is chosen `> k + 2 + d/2` (hence `J > k + 1 + d/2`), so that the
derivative-only resolvent representative is `C^{k+2}` and the Poisson solve `L_μ χ = a_φ` runs at regularity `k + 2`,
as the frozen conclusion `ContDiff ℝ (k + 2) χ` requires; `a_φ = γ⁻¹ r` for the continuous representative `r`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.MS.S48

open HRS HRS.Whole

variable {d : ℕ}

/-! ### The derivative-only Poisson solve, uniform for `q ∈ [qm, qp]` (dilation `λ = √(qm/q) ≤ 1`) -/

theorem s48_poisson_deriv (hd : 1 ≤ d) (qm qp Mb m₂ : ℝ) (hqm : 0 < qm) (m : ℕ) (hm : 2 ≤ m) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ q ∈ Set.Icc qm qp, ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ μ : Measure (Euc d), IsInvariantMeasure (fun x => -q • x + B x) μ →
      Integrable (fun x => ‖x‖ ^ 2) μ → ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ →
      ∀ r : Euc d → ℝ, ContDiff ℝ m r → ∀ D : ℝ,
        (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) → ∫ x, r x ∂μ = 0 →
        ∃ χ : Euc d → ℝ, ContDiff ℝ m χ ∧ Integrable χ μ ∧ ∫ x, χ x ∂μ = 0 ∧
          (∀ x, poissonOp (fun x => -q • x + B x) χ x = r x) ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ Cm * D := by
  obtain ⟨Cm0, h⟩ := PoisFinal.affine_poisson_deriv_proof hd qm Mb (qp / qm * m₂) hqm m hm
  set Λ : ℝ := Real.sqrt (qp / qm) with hΛdef
  refine ⟨Λ ^ m * |Cm0|, by positivity, fun q hq B hB μ hμ hμ2 hm2 r hr D hD hrc => ?_⟩
  have hq0 : 0 < q := hqm.trans_le hq.1
  have hqpq : 0 < qp := hq0.trans_le hq.2
  have hΛsq : Λ ^ 2 = qp / qm := Real.sq_sqrt (by positivity)
  obtain ⟨lam, hlam, hl1, hqe, hΛ⟩ : ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ qm = lam ^ 2 * q ∧ lam⁻¹ ≤ Λ := by
    refine ⟨Real.sqrt (qm / q), Real.sqrt_pos.2 (by positivity), ?_, ?_, ?_⟩
    · rw [Real.sqrt_le_one]; exact (div_le_one hq0).2 hq.1
    · rw [Real.sq_sqrt (by positivity)]; field_simp
    · rw [← Real.sqrt_inv, inv_div]
      exact Real.sqrt_le_sqrt (by gcongr; exact hq.2)
  have hl0 : lam ≠ 0 := hlam.ne'
  have hc : lam⁻¹ ≠ 0 := inv_ne_zero hl0
  have hc1 : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam).2 hl1
  have hΛ1 : 1 ≤ Λ := hc1.trans hΛ
  have hcΛ : lam⁻¹ ^ 2 ≤ qp / qm := hΛsq ▸ pow_le_pow_left₀ (inv_nonneg.2 hlam.le) hΛ 2
  have hmap : ∀ y : Euc d, lam • lam⁻¹ • y = y := fun y => by
    rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have hm20 : 0 ≤ m₂ := (integral_nonneg fun x => by positivity).trans hm2
  have hBt := TcQ.tcq_hasCb_dil hB hlam.le hl1
  have hinv := TcQ.tcq_invariant hlam hqe hμ
  have hsq : (fun x : Euc d => ‖lam⁻¹ • x‖ ^ 2) = fun x => lam⁻¹ ^ 2 * ‖x‖ ^ 2 := by
    ext x; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) (μ.map fun x => lam⁻¹ • x) := by
    rw [TcQ.tcq_integrable_map hc, hsq]; exact hμ2.const_mul _
  have hmom : ∫ x, ‖x‖ ^ 2 ∂(μ.map fun x => lam⁻¹ • x) ≤ qp / qm * m₂ := by
    rw [TcQ.tcq_integral_map hc, hsq, integral_const_mul]
    have h0 : 0 ≤ ∫ x, ‖x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
    calc lam⁻¹ ^ 2 * ∫ x, ‖x‖ ^ 2 ∂μ ≤ (qp / qm) * ∫ x, ‖x‖ ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_right hcΛ h0
      _ ≤ qp / qm * m₂ := mul_le_mul_of_nonneg_left hm2 (by positivity)
  have hrs : ContDiff ℝ m (fun y : Euc d => lam ^ 2 * r (lam • y)) :=
    contDiff_const.mul (hr.comp (contDiff_const_smul lam))
  have hrmean : ∫ y, lam ^ 2 * r (lam • y) ∂(μ.map fun x => lam⁻¹ • x) = 0 := by
    rw [TcQ.tcq_integral_map hc]
    have : (fun x : Euc d => lam ^ 2 * r (lam • lam⁻¹ • x)) = fun x => lam ^ 2 * r x := by
      ext x; rw [hmap]
    rw [this, integral_const_mul, hrc, mul_zero]
  have hrD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ y, ‖iteratedFDeriv ℝ j (fun y : Euc d => lam ^ 2 * r (lam • y)) y‖ ≤ D := by
    intro j hj1 hjm y
    have h1 := TcQ.tcq_norm_iter_dil hr (n := m) hjm (lam ^ 2) lam y
    simp only [smul_eq_mul] at h1
    have hl : |lam| ^ j ≤ 1 := by rw [abs_of_nonneg hlam.le]; exact pow_le_one₀ hlam.le hl1
    have ha : |lam ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (n := 2) hlam.le hl1
    have hDy := hD j hj1 hjm (lam • y)
    have hn := norm_nonneg (iteratedFDeriv ℝ j r (lam • y))
    calc _ ≤ |lam ^ 2| * |lam| ^ j * ‖iteratedFDeriv ℝ j r (lam • y)‖ := h1
      _ ≤ 1 * 1 * D := by gcongr
      _ = D := by ring
  obtain ⟨χ, hcd, hχi, hχ0, heq, hder⟩ := h _ hBt _ hinv hint2 hmom _ hrs D hrD hrmean
  refine ⟨fun x => χ (lam⁻¹ • x), hcd.comp (contDiff_const_smul lam⁻¹),
    (TcQ.tcq_integrable_map hc).1 hχi, ?_, ?_, ?_⟩
  · rw [← TcQ.tcq_integral_map hc]; exact hχ0
  · intro x
    have hχ2 : ContDiff ℝ 2 χ := hcd.of_le (by exact_mod_cast hm)
    have hpo := heq (lam⁻¹ • x)
    unfold poissonOp at hpo ⊢
    rw [TcQ.tcq_laplacian_dil hχ2, TcQ.tcq_gradient_dil _ _ (hχ2.differentiable (by simp)).differentiableAt]
    beta_reduce at hpo ⊢
    rw [hmap] at hpo
    simp only [inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real, hqe] at hpo ⊢
    generalize Laplacian.laplacian χ (lam⁻¹ • x) = L at hpo ⊢
    generalize inner ℝ x (gradient χ (lam⁻¹ • x)) = X at hpo ⊢
    generalize inner ℝ (B x) (gradient χ (lam⁻¹ • x)) = Y at hpo ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hl0)
    rw [← hpo]
    field_simp
  · intro j hj1 hjm x
    have h1 := TcQ.tcq_norm_iter_dil hcd (n := m) (i := j) hjm 1 lam⁻¹ x
    simp only [one_smul, abs_one, one_mul] at h1
    refine h1.trans ?_
    rw [abs_of_nonneg (inv_nonneg.2 hlam.le)]
    have hΛj : lam⁻¹ ^ j ≤ Λ ^ m :=
      calc lam⁻¹ ^ j ≤ Λ ^ j := pow_le_pow_left₀ (inv_nonneg.2 hlam.le) hΛ _
        _ ≤ Λ ^ m := pow_le_pow_right₀ hΛ1 hjm
    have hd1 := hder j hj1 hjm (lam⁻¹ • x)
    have hn := norm_nonneg (iteratedFDeriv ℝ j χ (lam⁻¹ • x))
    calc lam⁻¹ ^ j * ‖iteratedFDeriv ℝ j χ (lam⁻¹ • x)‖ ≤ Λ ^ m * (Cm0 * D) := by
          calc lam⁻¹ ^ j * ‖iteratedFDeriv ℝ j χ (lam⁻¹ • x)‖
              ≤ Λ ^ m * ‖iteratedFDeriv ℝ j χ (lam⁻¹ • x)‖ := mul_le_mul_of_nonneg_right hΛj hn
            _ ≤ Λ ^ m * (Cm0 * D) := mul_le_mul_of_nonneg_left hd1 (by positivity)
      _ ≤ Λ ^ m * (|Cm0| * D) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD j hj1 hjm 0)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hD0
      _ = Λ ^ m * |Cm0| * D := by ring

/-! ### Perturbations `(1 + εψ) ρ₀`: uniform derivative bounds for `ε ∇ψ/(1+εψ)` -/

/-- a smooth compactly supported function equal to `(1+u)⁻¹` on `[-1/2, 1/2]`. -/
theorem s48_inv_cutoff : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
    ∀ u : ℝ, |u| ≤ 1 / 2 → g u = (1 + u)⁻¹ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  refine ⟨fun u => b u * (1 + u)⁻¹, ?_, b.hasCompactSupport.mul_right, fun u hu => ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun u => ?_
    by_cases h : 1 + u = 0
    · have hu : u = -1 := by linarith
      subst hu
      refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : ℝ)) ?_
      have : ∀ᶠ v in 𝓝 (-1 : ℝ), dist v (-1) < 1 / 4 := Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [this] with v hv
      have hv' : (b.rOut : ℝ) ≤ dist v 0 := by
        show (3 / 4 : ℝ) ≤ dist v 0
        rw [Real.dist_eq] at hv ⊢
        rw [abs_lt] at hv
        rw [sub_zero]
        rw [abs_of_neg (by linarith)]
        linarith
      simp [b.zero_of_le_dist hv']
    · exact b.contDiffAt.mul ((contDiffAt_const.add contDiffAt_id).inv h)
  · have : b u = 1 := b.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]; show |u| ≤ 1 / 2; exact hu |> fun h => by simpa using h)
    simp [this]

theorem s48_eps_bound {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (i : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (ε : ℝ) (x : Euc d), (∀ y, |ε| * |ψ y| ≤ 1 / 2) →
      |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ E := by
  by_cases h : ∃ x₀, ψ x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h
    obtain ⟨C, hC0, hC⟩ := hc.exists_bound_iteratedFDeriv hψ i
    have hp : 0 < |ψ x₀| := abs_pos.2 hx₀
    refine ⟨C / (2 * |ψ x₀|), by positivity, fun ε x hε => ?_⟩
    have h1 : |ε| ≤ 1 / (2 * |ψ x₀|) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hε x₀]
    calc |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ (1 / (2 * |ψ x₀|)) * C :=
          mul_le_mul h1 (hC i le_rfl x) (norm_nonneg _) (by positivity)
      _ = C / (2 * |ψ x₀|) := by ring
  · push_neg at h
    refine ⟨0, le_rfl, fun ε x _ => ?_⟩
    have : ψ = 0 := funext h
    subst this
    simp

/-- the correction `B_ε - B₀ = ε ∇ψ/(1+εψ) = ∇ log(1+εψ)` of the drift. -/
def s48_L (ψ : Euc d → ℝ) (ε : ℝ) : Euc d → Euc d := fun x => (ε * (1 + ε * ψ x)⁻¹) • gradient ψ x

/-- ED15R: the uniform core of `s48_L_deriv`: the constant depends only on `m` and a bound `Es` for the finitely many
quantities `|ε| ‖D^i ψ‖` (`i ≤ m + 1`), not on `ψ`. -/
theorem s48_L_deriv_core (m : ℕ) (Es : ℝ) (hEs0 : 0 ≤ Es) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → ∀ ε : ℝ, (∀ y, |ε| * |ψ y| ≤ 1 / 2) →
      (∀ i ≤ m + 1, ∀ x, |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ Es) →
      ContDiff ℝ ∞ (s48_L ψ ε) ∧ ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j (s48_L ψ ε) x‖ ≤ C := by
  obtain ⟨g, hg, hgc, hgeq⟩ := s48_inv_cutoff
  obtain ⟨Cg, hCg0, hCg⟩ := hgc.exists_bound_iteratedFDeriv hg m
  set D : ℝ := 1 + Es with hD
  have hD1 : 1 ≤ D := by linarith
  refine ⟨2 ^ m * ((m.factorial : ℝ) * Cg * D ^ m * Es), by positivity, fun ψ hψ ε hε hEb => ?_⟩
  have hgrad : ContDiff ℝ ∞ (gradient ψ) := contDiff_infty.2 fun n => HRS.MS.Gap.gap1_contDiff_gradient hψ n
  set u : Euc d → ℝ := fun x => ε * ψ x with hu
  have hus : ContDiff ℝ ∞ u := contDiff_const.mul hψ
  set w : Euc d → ℝ := fun x => g (u x) with hw
  have hws : ContDiff ℝ ∞ w := hg.comp hus
  have hwe : ∀ x, w x = (1 + ε * ψ x)⁻¹ := fun x => by
    simp only [hw, hu]
    refine hgeq _ ?_
    rw [abs_mul]; exact hε x
  have hLe : s48_L ψ ε = fun x => (ε * w x) • gradient ψ x := by
    funext x; simp only [s48_L, hwe]
  have hf : ContDiff ℝ ∞ (fun x => ε * w x) := contDiff_const.mul hws
  refine ⟨?_, fun n hn x => ?_⟩
  · rw [hLe]; exact hf.smul hgrad
  rw [hLe]
  refine (norm_iteratedFDeriv_smul_le hf hgrad x (n := n) (by exact_mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => ε * w x) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (gradient ψ) x‖ ≤ (n.choose i : ℝ) * ((m.factorial : ℝ) * Cg * D ^ m * Es) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have e1 : iteratedFDeriv ℝ i (fun x => ε * w x) x = ε • iteratedFDeriv ℝ i w x := by
      have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := ε) (f := w) (i := i) (x := x)
        (hws.of_le (by exact_mod_cast le_top)).contDiffAt
      simpa [smul_eq_mul] using this
    have e2 : ‖iteratedFDeriv ℝ (n - i) (gradient ψ) x‖ = ‖iteratedFDeriv ℝ (n - i + 1) ψ x‖ :=
      HRS.MS.Gap.gap1_norm_iter_gradient _ _
    have e3 : ‖iteratedFDeriv ℝ i w x‖ ≤ (i.factorial : ℝ) * Cg * D ^ i := by
      refine norm_iteratedFDeriv_comp_le (hg := hg) (hf := hus) (n := i) (N := ∞)
        (by exact_mod_cast le_top) x (C := Cg) (D := D) (fun i' hi'' => hCg i' (by omega) _) ?_
      intro i' h1 h2
      have : iteratedFDeriv ℝ i' u x = ε • iteratedFDeriv ℝ i' ψ x := by
        have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := ε) (f := ψ) (i := i') (x := x)
          (hψ.of_le (by exact_mod_cast le_top)).contDiffAt
        simpa [smul_eq_mul] using this
      rw [this, norm_smul, Real.norm_eq_abs]
      calc |ε| * ‖iteratedFDeriv ℝ i' ψ x‖ ≤ Es := hEb i' (by omega) x
        _ ≤ D := by linarith
        _ ≤ D ^ i' := le_self_pow₀ hD1 (by omega)
    have e4 : |ε| * ‖iteratedFDeriv ℝ (n - i + 1) ψ x‖ ≤ Es :=
      hEb _ (by omega) x
    rw [e1, norm_smul, Real.norm_eq_abs, e2]
    have hfac : (i.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le (by omega)
    have hDi : D ^ i ≤ D ^ m := pow_le_pow_right₀ hD1 (by omega)
    have hn1 := norm_nonneg (iteratedFDeriv ℝ i w x)
    have hn2 := norm_nonneg (iteratedFDeriv ℝ (n - i + 1) ψ x)
    have hD0 : 0 ≤ D := by linarith
    calc (n.choose i : ℝ) * (|ε| * ‖iteratedFDeriv ℝ i w x‖) * ‖iteratedFDeriv ℝ (n - i + 1) ψ x‖
        = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i w x‖ * (|ε| * ‖iteratedFDeriv ℝ (n - i + 1) ψ x‖)) := by ring
      _ ≤ (n.choose i : ℝ) * (((i.factorial : ℝ) * Cg * D ^ i) * Es) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul e3 e4 (by positivity) (by positivity)
      _ ≤ (n.choose i : ℝ) * (((m.factorial : ℝ) * Cg * D ^ m) * Es) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ hEs0
          exact mul_le_mul (mul_le_mul_of_nonneg_right hfac hCg0) hDi (by positivity) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, show (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n by
    exact_mod_cast Nat.sum_range_choose n]
  have h0 : 0 ≤ (m.factorial : ℝ) * Cg * D ^ m * Es := by positivity
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) h0

theorem s48_L_deriv {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, (∀ y, |ε| * |ψ y| ≤ 1 / 2) → ContDiff ℝ ∞ (s48_L ψ ε) ∧
      ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j (s48_L ψ ε) x‖ ≤ C := by
  have hE : ∀ i : ℕ, ∃ E : ℝ, 0 ≤ E ∧ ∀ (ε : ℝ) (x : Euc d), (∀ y, |ε| * |ψ y| ≤ 1 / 2) →
      |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ E := fun i => s48_eps_bound hψ hc i
  choose E hE0 hEb using hE
  set Es : ℝ := ∑ i ∈ Finset.range (m + 2), E i with hEs
  have hEs0 : 0 ≤ Es := Finset.sum_nonneg fun i _ => hE0 i
  have hEle : ∀ i ≤ m + 1, E i ≤ Es := fun i hi =>
    Finset.single_le_sum (f := E) (fun i _ => hE0 i) (Finset.mem_range.2 (by omega))
  obtain ⟨C, hC0, hC⟩ := s48_L_deriv_core (d := d) m Es hEs0
  exact ⟨C, hC0, fun ε hε => hC ψ hψ ε hε (fun i hi x => (hEb i ε x hε).trans (hEle i hi))⟩

theorem s48_hasCb_add {m : ℕ} {M1 M2 : ℝ} {B : Euc d → Euc d} {L : Euc d → Euc d}
    (hB : HasCbBound m M1 B) (hL : ContDiff ℝ ∞ L) (hLb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j L x‖ ≤ M2) :
    HasCbBound m (M1 + M2) (fun x => B x + L x) := by
  refine ⟨hB.1.add (hL.of_le (by exact_mod_cast le_top)), fun j hj x => ?_⟩
  have hA : ContDiffAt ℝ j B x := (hB.1.of_le (by exact_mod_cast hj)).contDiffAt
  have hA' : ContDiffAt ℝ j L x := (hL.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : iteratedFDeriv ℝ j (fun x => B x + L x) x = iteratedFDeriv ℝ j B x + iteratedFDeriv ℝ j L x :=
    iteratedFDeriv_add_apply hA hA'
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hB.2 j hj x) (hLb j hj x))

/-- ED15R: the uniform core of `s48_tilt`: `L` depends only on `(N, m, Es)`, where `Es` bounds `|ε| ‖D^i ψ‖` for
`i ≤ N + m + 1`; it is chosen before `ψ`. -/
theorem s48_tilt_core (N m : ℕ) (Es : ℝ) (hEs0 : 0 ≤ Es) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (ψ : Euc d → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ (ρ₀ : Euc d → ℝ) (B₀ : Euc d → Euc d) (q M₀ c S Mb m₂ ε : ℝ),
      HRS.MS.TcDefs.TcRef d ρ₀ M₀ c S N → HRS.MS.Gap.GapRef d ρ₀ q B₀ → HasCbBound m Mb B₀ →
      ∫ x, ‖x‖ ^ 2 * ρ₀ x ≤ m₂ → (∀ y, |ε| * |ψ y| ≤ 1 / 2) →
      (∀ i ≤ N + m + 1, ∀ x, |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ Es) → ∫ x, ψ x * ρ₀ x = 0 →
        HRS.MS.TcDefs.TcRef d (perturbedDensity ρ₀ ε ψ) (3 / 2 * M₀) c (L * S) N ∧
        (∃ B : Euc d → Euc d, HRS.MS.Gap.GapRef d (perturbedDensity ρ₀ ε ψ) q B ∧
          HasCbBound m (Mb + L) B) ∧
        ∫ x, ‖x‖ ^ 2 * perturbedDensity ρ₀ ε ψ x ≤ 3 / 2 * m₂ := by
  obtain ⟨L2, hL20, hL2⟩ := s48_L_deriv_core (d := d) m Es hEs0
  set F : ℝ := 3 / 2 + Es with hF
  have hF0 : 0 ≤ F := by positivity
  refine ⟨2 ^ N * F + L2, by positivity, fun ψ hψ hc ρ₀ B₀ q M₀ c S Mb m₂ ε hρ hR hB hm2 hε hEb hmean => ?_⟩
  obtain ⟨Cψ, hCψ⟩ : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C := by
    obtain ⟨C, -, hC⟩ := hc.exists_bound_iteratedFDeriv hψ 0
    exact ⟨C, fun y => by simpa using hC 0 le_rfl y⟩
  set f : Euc d → ℝ := fun x => 1 + ε * ψ x with hf
  have hfs : ContDiff ℝ ∞ f := contDiff_const.add (contDiff_const.mul hψ)
  have hlow : ∀ x, 1 / 2 ≤ f x := fun x => by
    have h := hε x
    have : -(|ε| * |ψ x|) ≤ ε * ψ x := by rw [← abs_mul]; exact neg_abs_le _
    simp only [hf]; linarith
  have hup : ∀ x, f x ≤ 3 / 2 := fun x => by
    have h := hε x
    have : ε * ψ x ≤ |ε| * |ψ x| := by rw [← abs_mul]; exact le_abs_self _
    simp only [hf]; linarith
  have hfpos : ∀ x, 0 < f x := fun x => by linarith [hlow x]
  have hρe : perturbedDensity ρ₀ ε ψ = fun x => f x * ρ₀ x := rfl
  have hρ0 : ∀ x, 0 < ρ₀ x := hR.pos
  have hS : 0 ≤ S := HRS.MS.Tc5.tc5_S_nonneg hρ
  have hρ₀s : ContDiff ℝ ∞ ρ₀ := hR.smooth
  have hρs : ContDiff ℝ ∞ (fun x => f x * ρ₀ x) := hfs.mul hρ₀s
  have hρc : Continuous (fun x => f x * ρ₀ x) := hρs.continuous
  have hψρ : Integrable (fun x => ψ x * ρ₀ x) := by
    refine (hR.integrable.const_mul Cψ).mono' (hψ.continuous.mul hρ₀s.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hρ0 x)]
    have := hCψ x
    rw [Real.norm_eq_abs] at this
    nlinarith [hρ0 x]
  have hint : Integrable (fun x => f x * ρ₀ x) := by
    refine (hR.integrable.const_mul (3 / 2)).mono' hρc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hfpos x), abs_of_pos (hρ0 x)]
    nlinarith [hup x, hρ0 x]
  have hone : ∫ x, f x * ρ₀ x = 1 := by
    have e : ∀ x, f x * ρ₀ x = ρ₀ x + ε * (ψ x * ρ₀ x) := fun x => by simp only [hf]; ring
    simp_rw [e]
    rw [integral_add hR.integrable (hψρ.const_mul ε), integral_const_mul, hmean, hR.integral_one]
    ring
  have hmom : Integrable (fun x : Euc d => ‖x‖ ^ 2 * (f x * ρ₀ x)) := by
    refine (hR.moment2.const_mul (3 / 2)).mono' ((continuous_norm.pow 2).mul hρc).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hfpos x; have := hρ0 x; positivity)]
    have := mul_le_mul_of_nonneg_right (hup x) (hρ0 x).le
    nlinarith [sq_nonneg ‖x‖]
  refine ⟨?_, ?_, ?_⟩
  · -- TcRef
    refine ⟨⟨fun x => (mul_pos (hfpos x) (hρ0 x)).le, hρc.measurable, hone⟩,
      fun x => mul_pos (hfpos x) (hρ0 x), hρs, fun x => ?_, fun k hk x => ?_⟩
    · have h1 := hρ.gauss x
      have h2 : f x * ρ₀ x ≤ 3 / 2 * ρ₀ x := mul_le_mul_of_nonneg_right (hup x) (hρ0 x).le
      show f x * ρ₀ x ≤ 3 / 2 * M₀ * Real.exp (-c * ‖x‖ ^ 2)
      nlinarith
    · have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := ρ₀) (N := (∞ : ℕ∞ω)) hfs hρ₀s x
        (n := k) (by exact_mod_cast le_top)
      show ‖iteratedFDeriv ℝ k (fun x => f x * ρ₀ x) x‖ ≤ _
      refine h1.trans ?_
      have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      have hexp := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
      have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (k - i) ρ₀ x‖ ≤ (k.choose i : ℝ) * (F * (S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2))) := by
        intro i hi
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have e1 : ‖iteratedFDeriv ℝ i f x‖ ≤ F := by
          rcases Nat.eq_zero_or_pos i with h0 | h0
          · subst h0
            rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hfpos x)]
            linarith [hup x]
          · have e : iteratedFDeriv ℝ i f x = ε • iteratedFDeriv ℝ i ψ x := by
              have hA : ContDiffAt ℝ i (fun _ : Euc d => (1 : ℝ)) x := contDiffAt_const
              have hB' : ContDiffAt ℝ i (fun x => ε * ψ x) x :=
                (contDiff_const.mul (hψ.of_le (by exact_mod_cast le_top))).contDiffAt
              have e1 : f = (fun _ : Euc d => (1 : ℝ)) + fun x => ε * ψ x := rfl
              rw [e1, iteratedFDeriv_add_apply hA hB', iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply,
                zero_add]
              have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := ε) (f := ψ) (i := i) (x := x)
                (hψ.of_le (by exact_mod_cast le_top)).contDiffAt
              simpa [smul_eq_mul] using this
            rw [e, norm_smul, Real.norm_eq_abs]
            calc |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ Es := hEb i (by omega) x
              _ ≤ F := by simp only [hF]; linarith
        have e2 := hρ.deriv (k - i) (by omega) x
        have e3 : (1 + ‖x‖) ^ (k - i) ≤ (1 + ‖x‖) ^ k := pow_le_pow_right₀ hx1 (by omega)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) ρ₀ x‖
            ≤ F * (S * (1 + ‖x‖) ^ (k - i) * Real.exp (-c * ‖x‖ ^ 2)) :=
              mul_le_mul e1 e2 (norm_nonneg _) hF0
          _ ≤ F * (S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ hF0
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e3 hS) hexp
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul, show (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k by
        exact_mod_cast Nat.sum_range_choose k]
      have h6 : 0 ≤ F * (S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by positivity
      have h7 : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hk
      have h8 : 0 ≤ F * (S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := h6
      calc 2 ^ k * (F * (S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)))
          ≤ 2 ^ N * (F * (S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2))) := mul_le_mul_of_nonneg_right h7 h8
        _ ≤ (2 ^ N * F + L2) * S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2) := by
            have : 0 ≤ L2 * (S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by positivity
            nlinarith
  · -- GapRef and the drift bound
    obtain ⟨hLs, hLb⟩ := hL2 ψ hψ ε hε (fun i hi x => hEb i (by omega) x)
    refine ⟨fun x => B₀ x + s48_L ψ ε x, ?_, ?_⟩
    · refine ⟨fun x => mul_pos (hfpos x) (hρ0 x), hρs, hint, hone, hmom, fun x => ?_, fun m' => ?_⟩
      · -- the gradient identity
        have hρd : DifferentiableAt ℝ ρ₀ x := (hρ₀s.differentiable (by simp)) x
        have hψd : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
        have hfd : HasFDerivAt f (ε • fderiv ℝ ψ x) x :=
          (hψd.hasFDerivAt.const_mul ε).const_add 1
        have hprod : HasFDerivAt (fun y => f y * ρ₀ y)
            (f x • fderiv ℝ ρ₀ x + ρ₀ x • (ε • fderiv ℝ ψ x)) x := hfd.mul hρd.hasFDerivAt
        refine ext_inner_left ℝ fun v => ?_
        show inner ℝ v (gradient (fun x => f x * ρ₀ x) x) = _
        rw [HRS.MS.PoisKolm.kl_inner_gradient, hprod.fderiv]
        have g0 := HRS.MS.PoisKolm.kl_inner_gradient ρ₀ x v
        rw [hR.grad x, inner_smul_right] at g0
        have g1 := HRS.MS.PoisKolm.kl_inner_gradient ψ x v
        have hne : f x ≠ 0 := (hfpos x).ne'
        have hsplit : -q • x + (B₀ x + s48_L ψ ε x) =
            (-q • x + B₀ x) + (ε * (f x)⁻¹) • gradient ψ x := by
          simp only [s48_L, hf]; abel
        have hrhs : inner ℝ v ((perturbedDensity ρ₀ ε ψ x) • (-q • x + (B₀ x + s48_L ψ ε x))) =
            f x * ρ₀ x * (inner ℝ v (-q • x + B₀ x) + ε * (f x)⁻¹ * fderiv ℝ ψ x v) := by
          rw [inner_smul_right, hsplit, inner_add_right, inner_smul_right, g1]
          rfl
        rw [hrhs]
        simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul]
        rw [← g0]
        field_simp
      · obtain ⟨Mb', hMb'⟩ := hR.cb m'
        obtain ⟨C', -, hC'⟩ := s48_L_deriv hψ hc m'
        obtain ⟨hLs', hLb'⟩ := hC' ε hε
        exact ⟨Mb' + C', s48_hasCb_add hMb' hLs' hLb'⟩
    · have h := s48_hasCb_add hB hLs hLb
      refine ⟨h.1, fun j hj x => (h.2 j hj x).trans ?_⟩
      have : 0 ≤ 2 ^ N * F := by positivity
      linarith
  · -- second moment
    have hmono : ∫ x, ‖x‖ ^ 2 * (f x * ρ₀ x) ≤ ∫ x, 3 / 2 * (‖x‖ ^ 2 * ρ₀ x) := by
      refine integral_mono hmom (hR.moment2.const_mul _) fun x => ?_
      have := mul_le_mul_of_nonneg_right (hup x) (hρ0 x).le
      nlinarith [sq_nonneg ‖x‖]
    rw [integral_const_mul] at hmono
    show ∫ x, ‖x‖ ^ 2 * (f x * ρ₀ x) ≤ _
    nlinarith

/-- **The compact relative perturbation `(1+εψ) ρ₀`.**  If `ρ₀` is a reference (`TcRef` up to order `N`, drift
`B₀ ∈ C_b^m` bounded by `Mb`, second moment `≤ m₂`) and `ψ ∈ C_c^∞`, `|ε||ψ| ≤ 1/2`, `∫ ψ ρ₀ = 0`, then `(1+εψ)ρ₀` is a
reference of the same type with constants `(3/2) M₀`, `L S`, `Mb + L`, `(3/2) m₂`, where `L` depends only on `ψ, N, m`
(not on `ε`, `ρ₀`, `q`). -/
theorem s48_tilt {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (N m : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (ρ₀ : Euc d → ℝ) (B₀ : Euc d → Euc d) (q M₀ c S Mb m₂ ε : ℝ),
      HRS.MS.TcDefs.TcRef d ρ₀ M₀ c S N → HRS.MS.Gap.GapRef d ρ₀ q B₀ → HasCbBound m Mb B₀ →
      ∫ x, ‖x‖ ^ 2 * ρ₀ x ≤ m₂ → (∀ y, |ε| * |ψ y| ≤ 1 / 2) → ∫ x, ψ x * ρ₀ x = 0 →
        HRS.MS.TcDefs.TcRef d (perturbedDensity ρ₀ ε ψ) (3 / 2 * M₀) c (L * S) N ∧
        (∃ B : Euc d → Euc d, HRS.MS.Gap.GapRef d (perturbedDensity ρ₀ ε ψ) q B ∧
          HasCbBound m (Mb + L) B) ∧
        ∫ x, ‖x‖ ^ 2 * perturbedDensity ρ₀ ε ψ x ≤ 3 / 2 * m₂ := by
  have hE : ∀ i : ℕ, ∃ E : ℝ, 0 ≤ E ∧ ∀ (ε : ℝ) (x : Euc d), (∀ y, |ε| * |ψ y| ≤ 1 / 2) →
      |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ E := fun i => s48_eps_bound hψ hc i
  choose E hE0 hEb using hE
  set Es : ℝ := ∑ i ∈ Finset.range (N + m + 2), E i with hEs
  have hEs0 : 0 ≤ Es := Finset.sum_nonneg fun i _ => hE0 i
  have hEle : ∀ i ≤ N + m + 1, E i ≤ Es := fun i hi =>
    Finset.single_le_sum (f := E) (fun i _ => hE0 i) (Finset.mem_range.2 (by omega))
  obtain ⟨L, hL0, hL⟩ := s48_tilt_core (d := d) N m Es hEs0
  exact ⟨L, hL0, fun ρ₀ B₀ q M₀ c S Mb m₂ ε hρ hR hB hm2 hε hmean =>
    hL ψ hψ hc ρ₀ B₀ q M₀ c S Mb m₂ ε hρ hR hB hm2 hε
      (fun i hi x => (hEb i ε x hε).trans (hEle i hi)) hmean⟩

/-- ED15R: if `ψ ∈ C_c^∞` and `‖εψ‖_{C_b^K} ≤ ε_*`, then `|ε| ‖D^i ψ x‖ ≤ ε_*` for `i ≤ K`. -/
theorem s48_cbu_bound {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (ε εstar : ℝ) (K : ℕ)
    (h : HRS.cbNorm K (fun x => ε * ψ x) ≤ εstar) : ∀ i ≤ K, ∀ x, |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ εstar := by
  intro i hi x
  have hf : ContDiff ℝ ∞ (fun x => ε * ψ x) := contDiff_const.mul hψ
  have hfc : HasCompactSupport (fun x => ε * ψ x) := hc.mul_left
  obtain ⟨C, -, hC⟩ := hfc.exists_bound_iteratedFDeriv hf i
  have hbdd : BddAbove (Set.range fun z : Euc d => ‖iteratedFDeriv ℝ i (fun x => ε * ψ x) z‖) :=
    ⟨C, by rintro _ ⟨z, rfl⟩; exact hC i le_rfl z⟩
  have e : iteratedFDeriv ℝ i (fun x => ε * ψ x) x = ε • iteratedFDeriv ℝ i ψ x := by
    have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := ε) (f := ψ) (i := i) (x := x)
      (hψ.of_le (by exact_mod_cast le_top)).contDiffAt
    simpa [smul_eq_mul] using this
  have h1 : |ε| * ‖iteratedFDeriv ℝ i ψ x‖ = ‖iteratedFDeriv ℝ i (fun x => ε * ψ x) x‖ := by
    rw [e, norm_smul, Real.norm_eq_abs]
  rw [h1]
  refine le_trans ?_ h
  refine le_trans (le_ciSup hbdd x) ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => ε * ψ x) z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))

/-! ### The reference package and its uniform constants -/

/-- The data of a static reference `ρ` consumed by the derivative-corrector proof: `TcRef` up to order `N`, a drift
`B ∈ C_b^m` (bounded by `Mb`) with `∇ρ = ρ(-q x + B)`, and a second-moment bound. -/
structure S48Pkg (d : ℕ) (ρ : Euc d → ℝ) (q M₀ c S Mb m₂ : ℝ) (N m : ℕ) : Prop where
  ref : HRS.MS.TcDefs.TcRef d ρ M₀ c S N
  drift : ∃ B : Euc d → Euc d, HRS.MS.Gap.GapRef d ρ q B ∧ HasCbBound m Mb B
  moment : ∫ x, ‖x‖ ^ 2 * ρ x ≤ m₂

theorem s48_pkg_mono {ρ : Euc d → ℝ} {q M₀ c S Mb m₂ M₀' S' Mb' m₂' : ℝ} {N m : ℕ}
    (h : S48Pkg d ρ q M₀ c S Mb m₂ N m) (h1 : M₀ ≤ M₀') (h2 : S ≤ S') (h3 : Mb ≤ Mb') (h4 : m₂ ≤ m₂') :
    S48Pkg d ρ q M₀' c S' Mb' m₂' N m := by
  refine ⟨⟨h.ref.prob, h.ref.pos, h.ref.smooth, fun x => ?_, fun k hk x => ?_⟩, ?_, h.moment.trans h4⟩
  · exact (h.ref.gauss x).trans (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
  · refine (h.ref.deriv k hk x).trans ?_
    have : 0 ≤ (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2) := by positivity
    nlinarith
  · obtain ⟨B, hB, hcb⟩ := h.drift
    exact ⟨B, hB, hcb.1, fun j hj x => (hcb.2 j hj x).trans h3⟩

/-- **Uniform reference data.**  For `a, β` in compact positive intervals and `ρ` the thermal density or a compact
relative perturbation `(1+εψ)ρ_*` (`ψ` fixed), the packages have constants `c, M₀, m₂` independent of everything,
`S` depending on the order `N`, and `Mb` on `m`. -/
theorem s48_ref_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp : ℝ} (ham : 0 < am)
    (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) (ψ : Euc d → ℝ) :
    ∃ c M₀ m₂ : ℝ, 0 < c ∧ 0 < M₀ ∧ ∀ N m : ℕ, ∃ S Mb : ℝ, ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      ∀ ρ : Euc d → ℝ, IsStaticReference d s a β ψ ρ → S48Pkg d ρ (a * β) M₀ c S Mb m₂ N m := by
  obtain ⟨c, M₀, m₂, hc, hM₀, hS, hMb⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd ham hβm hap hβp
  refine ⟨c, 3 / 2 * M₀, 3 / 2 * |m₂|, hc, by positivity, fun N m => ?_⟩
  obtain ⟨S, hS0, hSρ⟩ := hS N
  obtain ⟨Mb, hMb0, hMbρ⟩ := hMb m
  have hth : ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      S48Pkg d (thermalDensity d s a β) (a * β) M₀ c S Mb m₂ N m := by
    intro a β h1 h2 h3 h4
    have hdr := hMbρ a β h1 h2 h3 h4
    obtain ⟨B, hB, hcb⟩ := hdr.gap
    exact ⟨hSρ a β h1 h2 h3 h4, ⟨B, by rwa [mul_comm] at hB, hcb⟩, hdr.moment⟩
  by_cases hψ : ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ
  · obtain ⟨L, hL0, hL⟩ := s48_tilt hψ.1 hψ.2 N m
    refine ⟨(L + 1) * S, Mb + L, fun a β h1 h2 h3 h4 ρ hρ => ?_⟩
    have hp := hth a β h1 h2 h3 h4
    have hm20 : 0 ≤ m₂ := (integral_nonneg fun x => by
      have := hp.ref.pos x; positivity).trans hp.moment
    cases hρ with
    | thermal =>
      refine s48_pkg_mono hp (by linarith) ?_ (by linarith) (by
        have := le_abs_self m₂; linarith [abs_nonneg m₂])
      nlinarith
    | perturbed ε hε =>
      obtain ⟨B₀, hB₀, hcb₀⟩ := hp.drift
      obtain ⟨t1, t2, t3⟩ := hL _ B₀ (a * β) M₀ c S Mb m₂ ε hp.ref hB₀ hcb₀ hp.moment hε.small hε.meanZero
      refine s48_pkg_mono ⟨t1, t2, t3⟩ le_rfl ?_ (by linarith) (by linarith [le_abs_self m₂])
      nlinarith
  · refine ⟨S, Mb, fun a β h1 h2 h3 h4 ρ hρ => ?_⟩
    have hp := hth a β h1 h2 h3 h4
    cases hρ with
    | thermal =>
      refine s48_pkg_mono hp (by linarith) le_rfl le_rfl ?_
      have := hp.moment
      have hm20 : 0 ≤ m₂ := (integral_nonneg fun x => by
        have := hp.ref.pos x; positivity).trans this
      linarith [abs_nonneg m₂, le_abs_self m₂]
    | perturbed ε hε => exact absurd ⟨hε.smooth, hε.compactSupport⟩ hψ

/-! ### ED15R: the references uniform over the tilt class `‖εψ‖_{C_b^{100d+1001}} ≤ ε_*` -/

/-- The references uniform in `(ε, ψ)`: the thermal density, or `(1+εψ)ρ_*` with `IsTiltData` and
`‖εψ‖_{C_b^{100d+1001}} ≤ ε_*` (the class of the repaired S4.7). -/
def UnifRef (d : ℕ) (s a β εstar : ℝ) (ρ : Euc d → ℝ) : Prop :=
  ρ = thermalDensity d s a β ∨ ∃ (ε : ℝ) (ψ : Euc d → ℝ), IsTiltData d s a β ψ ε ∧
    HRS.cbNorm (100 * d + 1001) (fun x => ε * ψ x) ≤ εstar ∧
    ρ = perturbedDensity (thermalDensity d s a β) ε ψ

/-- **Reference data, uniform over the tilt class** (the order restriction `N + m + 1 ≤ 100 d + 1001` only encodes the
finitely many `C_b` seminorms controlled by `ε_*`). -/
theorem s48_ref_data_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp : ℝ} (ham : 0 < am)
    (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) (εstar : ℝ) :
    ∃ c M₀ m₂ : ℝ, 0 < c ∧ 0 < M₀ ∧ ∀ N m : ℕ, N + m + 1 ≤ 100 * d + 1001 → ∃ S Mb : ℝ,
      ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      ∀ ρ : Euc d → ℝ, UnifRef d s a β εstar ρ → S48Pkg d ρ (a * β) M₀ c S Mb m₂ N m := by
  obtain ⟨c, M₀, m₂, hc, hM₀, hS, hMb⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd ham hβm hap hβp
  refine ⟨c, 3 / 2 * M₀, 3 / 2 * |m₂|, hc, by positivity, fun N m hNm => ?_⟩
  obtain ⟨S, hS0, hSρ⟩ := hS N
  obtain ⟨Mb, hMb0, hMbρ⟩ := hMb m
  have hth : ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      S48Pkg d (thermalDensity d s a β) (a * β) M₀ c S Mb m₂ N m := by
    intro a β h1 h2 h3 h4
    have hdr := hMbρ a β h1 h2 h3 h4
    obtain ⟨B, hB, hcb⟩ := hdr.gap
    exact ⟨hSρ a β h1 h2 h3 h4, ⟨B, by rwa [mul_comm] at hB, hcb⟩, hdr.moment⟩
  obtain ⟨L, hL0, hL⟩ := s48_tilt_core (d := d) N m (max εstar 0) (le_max_right _ _)
  refine ⟨(L + 1) * S, Mb + L, fun a β h1 h2 h3 h4 ρ hρ => ?_⟩
  have hp := hth a β h1 h2 h3 h4
  have hp' := hp
  have hm20 : 0 ≤ m₂ := (integral_nonneg fun x => by
    have := (hp'.ref).pos x; positivity).trans hp'.moment
  rcases hρ with rfl | ⟨ε, ψ, hε, hcb, rfl⟩
  · refine s48_pkg_mono hp (by linarith) ?_ (by linarith) (by
      have := le_abs_self m₂; linarith [abs_nonneg m₂])
    nlinarith
  · obtain ⟨B₀, hB₀, hcb₀⟩ := hp.drift
    have hEb := s48_cbu_bound hε.smooth hε.compactSupport ε εstar _ hcb
    obtain ⟨t1, t2, t3⟩ := hL ψ hε.smooth hε.compactSupport _ B₀ (a * β) M₀ c S Mb m₂ ε hp.ref hB₀ hcb₀
      hp.moment hε.small (fun i hi x => (hEb i (by omega) x).trans (le_max_left _ _)) hε.meanZero
    refine s48_pkg_mono ⟨t1, t2, t3⟩ le_rfl ?_ (by linarith) (by linarith [le_abs_self m₂])
    nlinarith

/-- every fixed `ψ` has a bound `ε_*` with `‖εψ‖_{C_b^{100d+1001}} ≤ ε_*` for all admissible `ε`. -/
theorem s48_tilt_cb_star (ψ : Euc d → ℝ) :
    ∃ εstar : ℝ, ∀ (s a β ε : ℝ), IsTiltData d s a β ψ ε →
      HRS.cbNorm (100 * d + 1001) (fun x => ε * ψ x) ≤ εstar := by
  by_cases hψ : ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ
  · have hE : ∀ i : ℕ, ∃ E : ℝ, 0 ≤ E ∧ ∀ (ε : ℝ) (x : Euc d), (∀ y, |ε| * |ψ y| ≤ 1 / 2) →
        |ε| * ‖iteratedFDeriv ℝ i ψ x‖ ≤ E := fun i => s48_eps_bound hψ.1 hψ.2 i
    choose E hE0 hEb using hE
    refine ⟨∑ i ∈ Finset.range (100 * d + 1001 + 1), E i, fun s a β ε hε => ?_⟩
    unfold HRS.cbNorm
    refine Finset.sum_le_sum fun j _ => ciSup_le fun z => ?_
    have e : iteratedFDeriv ℝ j (fun x => ε * ψ x) z = ε • iteratedFDeriv ℝ j ψ z := by
      have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := ε) (f := ψ) (i := j) (x := z)
        (hψ.1.of_le (by exact_mod_cast le_top)).contDiffAt
      simpa [smul_eq_mul] using this
    rw [e, norm_smul, Real.norm_eq_abs]
    exact hEb j ε z hε.small
  · exact ⟨0, fun s a β ε hε => absurd ⟨hε.smooth, hε.compactSupport⟩ hψ⟩

/-- every fixed `ψ` has a bound `ε_*` making its static references (all admissible `ε`) members of the uniform class. -/
theorem s48_static_to_unif (ψ : Euc d → ℝ) :
    ∃ εstar : ℝ, ∀ (s a β : ℝ) (ρ : Euc d → ℝ), IsStaticReference d s a β ψ ρ → UnifRef d s a β εstar ρ := by
  obtain ⟨εstar, h⟩ := s48_tilt_cb_star (d := d) ψ
  refine ⟨εstar, fun s a β ρ hρ => ?_⟩
  cases hρ with
  | thermal => exact Or.inl rfl
  | perturbed ε hε => exact Or.inr ⟨ε, ψ, hε, h s a β ε hε, rfl⟩

/-! ### The frozen row -/

theorem s48_hasCb_mono {m J : ℕ} {Mb : ℝ} {B : Euc d → Euc d} (h : m ≤ J) (hB : HasCbBound J Mb B) :
    HasCbBound m Mb B :=
  ⟨hB.1.of_le (by exact_mod_cast h), fun j hj x => hB.2 j (hj.trans h) x⟩

/-- Lipschitz functions are in `L²(μ)` when `‖x‖²` is `μ`-integrable. -/
theorem s48_memLp_lip {μ : Measure (Euc d)} [IsFiniteMeasure μ] (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ)
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 1 χ) {L : ℝ} (hL : ∀ y, ‖fderiv ℝ χ y‖ ≤ L) : MemLp χ 2 μ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hlip : ∀ x, ‖χ x‖ ≤ ‖χ 0‖ + L * ‖x‖ := fun x => by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := χ) (s := Set.univ) (x := 0) (y := x)
      (fun y _ => (hχ.differentiable (by norm_num)) y) (fun y _ => hL y) convex_univ trivial trivial
    rw [sub_zero] at this
    calc ‖χ x‖ = ‖χ 0 + (χ x - χ 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖χ 0‖ + ‖χ x - χ 0‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [memLp_two_iff_integrable_sq hχ.continuous.aestronglyMeasurable]
  refine ((integrable_const (2 * χ 0 ^ 2)).add (hint2.const_mul (2 * L ^ 2))).mono'
    (hχ.continuous.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := hlip x
  have h2 : ‖χ x‖ ^ 2 ≤ (‖χ 0‖ + L * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : χ x ^ 2 = ‖χ x‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h4 : χ 0 ^ 2 = ‖χ 0‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have key : χ x ^ 2 ≤ 2 * χ 0 ^ 2 + 2 * L ^ 2 * ‖x‖ ^ 2 := by
    rw [h3, h4]
    nlinarith [sq_nonneg (‖χ 0‖ - L * ‖x‖), mul_pow L ‖x‖ 2]
  exact key

/-- **S4.8** `derivative_corrector`. -/
theorem derivative_corrector_proof : type_of% @HRS.Whole.derivative_corrector := by
  intro d s hd hs0 hsd k am ap βm βp γm γp ham hβm hγm ψ
  by_cases hint : am ≤ ap ∧ βm ≤ βp
  swap
  · refine ⟨⌊(k : ℝ) + 1 + d / 2⌋₊ + 1, by push_cast; exact Nat.lt_floor_add_one _, 0, fun a ha β hβ => ?_⟩
    exact absurd ⟨ha.1.trans ha.2, hβ.1.trans hβ.2⟩ hint
  obtain ⟨hap, hβp⟩ := hint
  have hd1 : 1 ≤ d := by omega
  have hα : 0 < (d : ℝ) - s := by linarith
  set m : ℕ := k + 2 with hm
  set J : ℕ := ⌈(m : ℝ) + d / 2⌉₊ + 1 with hJdef
  have hJ : (m : ℝ) + d / 2 < J := by
    have := Nat.le_ceil ((m : ℝ) + d / 2)
    rw [hJdef]; push_cast; linarith
  have hJk : (k : ℝ) + 1 + d / 2 < J := by
    have : (k : ℝ) + 1 ≤ m := by rw [hm]; push_cast; linarith
    linarith
  have hmJ : m ≤ J := by
    have : (m : ℝ) < J := by have : (0 : ℝ) ≤ d / 2 := by positivity
                             linarith
    exact_mod_cast this.le
  set M : ℕ := ⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ + 1 with hMdef
  have hMs : (m : ℝ) + d / 2 < M * ((d : ℝ) - s) := HRS.MS.Tc5.tc5_M_spec hsd m
  set N : ℕ := J + ⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ + 1 with hNdef
  have hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N := by
    have h1 := Nat.le_ceil ((M : ℝ) * ((d : ℝ) - s) + d)
    have : (J : ℝ) + ((⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℕ) : ℝ) + 1 ≤ N := by
      rw [hNdef]; push_cast; linarith
    linarith
  obtain ⟨c, M₀, m₂, hc, hM₀, hpk⟩ := s48_ref_data hd hs0 hsd ham hβm hap hβp ψ
  obtain ⟨S, Mb, hpkS⟩ := hpk N J
  have hqm : 0 < am * βm := mul_pos ham hβm
  obtain ⟨Cr, hCr0, hCr⟩ := s48_resolvent hs0 hsd m J M hmJ hJ hMs γp (ap * βp) Mb M₀ c S hc N hN
  obtain ⟨Cm, hCm0, hCm⟩ := s48_poisson_deriv hd1 (am * βm) (ap * βp) Mb (3 / 2 * |m₂|) hqm m (by omega)
  refine ⟨J, hJk, (k + 1 : ℝ) * (γm⁻¹ * Cr) * (1 + Cm), fun a ha β hβ γ hγ ρ hρ φ hφ => ?_⟩
  have ha0 : 0 < a := ham.trans_le ha.1
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hγ0 : 0 < γ := hγm.trans_le hγ.1
  have hqa : am * βm ≤ a * β := mul_le_mul ha.1 hβ.1 hβm.le ha0.le
  have hqb : a * β ≤ ap * βp := mul_le_mul ha.2 hβ.2 hβ0.le (ham.le.trans hap)
  have hqabs : |a * β| ≤ ap * βp := by rw [abs_of_pos (mul_pos ha0 hβ0)]; exact hqb
  have hp := hpkS a β ha.1 ha.2 hβ.1 hβ.2 ρ hρ
  obtain ⟨B, hR, hcb⟩ := hp.drift
  obtain ⟨r₀, r, hr0, hreq, hrcd, hrder, hrae⟩ :=
    hCr (a * β) hqabs ρ B hp.ref hR hcb γ hγ0 hγ.2 φ hφ
  obtain ⟨hprob, hint2, hmom⟩ := HRS.MS.Gap.gap_moment hR
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set Q := s48_Q μ J φ with hQ
  have hQ0 : 0 ≤ Q := s48_Q_nonneg μ J φ
  -- the response
  set aφ : Euc d → ℝ := fun x => γ⁻¹ * r x with haφ
  have haφae : aφ =ᵐ[μ] fun x => γ⁻¹ * r₀ x := by
    filter_upwards [hrae] with x hx
    simp only [haφ, hx]
  have haφ0 : HRS.Whole.MemL2Zero μ aφ := by
    have h1 : HRS.Whole.MemL2Zero μ (fun x => γ⁻¹ * r₀ x) :=
      ⟨hr0.1.const_mul _, by rw [integral_const_mul, hr0.2, mul_zero]⟩
    exact ⟨h1.1.ae_eq haφae.symm, by rw [integral_congr_ae haφae]; exact h1.2⟩
  have hresp : HRS.Whole.IsResponse (rieszKernel d s) μ γ φ aφ := by
    refine ⟨haφ0, ?_⟩
    have hk : HRS.Whole.Kop (rieszKernel d s) μ aφ = HRS.Whole.Kop (rieszKernel d s) μ (fun x => γ⁻¹ * r₀ x) :=
      HRS.MS.S98.s98_kop_congr_ae haφae
    filter_upwards [hreq, haφae] with x h1 h2
    rw [hk, HRS.MS.S98.s98_kop_smul, h2]
    have : γ ≠ 0 := hγ0.ne'
    have h3 : r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) μ r₀ x = γ * HRS.Whole.projMean μ φ x := h1
    calc γ⁻¹ * r₀ x + γ * (γ⁻¹ * HRS.Whole.Kop (rieszKernel d s) μ r₀ x)
        = γ⁻¹ * (r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) μ r₀ x) := by field_simp
      _ = _ := by rw [h3]; field_simp
  -- smoothness and derivative bounds of `aφ`
  have haφs : ContDiff ℝ m aφ := contDiff_const.mul hrcd
  set D : ℝ := γm⁻¹ * Cr * Q with hD
  have hD0 : 0 ≤ D := by positivity
  have haφder : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j aφ x‖ ≤ D := by
    intro j hj1 hjm x
    have e : iteratedFDeriv ℝ j aφ x = γ⁻¹ • iteratedFDeriv ℝ j r x := by
      have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := γ⁻¹) (f := r) (i := j) (x := x)
        (hrcd.of_le (by exact_mod_cast hjm)).contDiffAt
      simpa [smul_eq_mul, haφ] using this
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hγ0)]
    have h1 := hrder j hj1 hjm x
    have h2 : γ⁻¹ ≤ γm⁻¹ := inv_anti₀ hγm hγ.1
    calc γ⁻¹ * ‖iteratedFDeriv ℝ j r x‖ ≤ γm⁻¹ * (Cr * Q) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = D := by rw [hD]; ring
  -- the Poisson solve
  obtain ⟨χ, hχcd, hχi, hχ0, hχeq, hχder⟩ := hCm (a * β) ⟨hqa, hqb⟩ B (s48_hasCb_mono hmJ hcb) μ
    (HRS.MS.Gap.gap_invariant hR) hint2 (by
      rw [hmom]
      have h0 : 0 ≤ ∫ x, ‖x‖ ^ 2 * ρ x := integral_nonneg fun x => by have := hR.pos x; positivity
      calc ∫ x, ‖x‖ ^ 2 * ρ x ≤ m₂ := hp.moment
        _ ≤ 3 / 2 * |m₂| := by linarith [le_abs_self m₂, abs_nonneg m₂]) aφ haφs D haφder haφ0.2
  have hχL : ∀ y, ‖fderiv ℝ χ y‖ ≤ Cm * D := fun y => by
    rw [← norm_iteratedFDeriv_one]; exact hχder 1 le_rfl (by omega) y
  have hχ1 : ContDiff ℝ 1 χ := hχcd.of_le (by exact_mod_cast (by omega : 1 ≤ m))
  have hχL2 := s48_memLp_lip hint2 hχ1 hχL
  refine ⟨aφ, hresp, haφs.of_le (by exact_mod_cast (by omega : k + 1 ≤ m)), ?_, χ,
    hχcd.of_le (by rw [hm]; exact le_rfl), ⟨hχL2, hχ0⟩, ?_, ?_⟩
  · intro x
    have hQe : ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ ((j : ℕ) + 1) aφ (x j)‖ ≤ (k + 1 : ℝ) * D := by
      calc ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ ((j : ℕ) + 1) aφ (x j)‖ ≤ ∑ _j : Fin (k + 1), D :=
            Finset.sum_le_sum fun j _ => haφder _ (by omega) (by have := j.2; omega) _
        _ = (k + 1 : ℝ) * D := by simp
    refine hQe.trans ?_
    show (k + 1 : ℝ) * D ≤ _ * Q
    have : (k + 1 : ℝ) * (γm⁻¹ * Cr) * (1 + Cm) * Q = (k + 1 : ℝ) * D * (1 + Cm) := by rw [hD]; ring
    rw [this]
    have h1 : 0 ≤ (k + 1 : ℝ) * D := by positivity
    nlinarith
  · intro x
    have hgl := HRS.MS.Gap.gap_gradient_log hR x
    show -Laplacian.laplacian χ x - inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient χ x) = aφ x
    rw [hgl]
    have := hχeq x
    unfold poissonOp at this
    exact this
  · intro x
    have hbd : ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ (j : ℕ) (gradient χ) (x j)‖ ≤ (k + 1 : ℝ) * (Cm * D) := by
      calc ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ (j : ℕ) (gradient χ) (x j)‖
          ≤ ∑ _j : Fin (k + 1), Cm * D := Finset.sum_le_sum fun j _ => by
            rw [HRS.MS.Gap.gap1_norm_iter_gradient]
            exact hχder _ (by omega) (by have := j.2; omega) _
        _ = (k + 1 : ℝ) * (Cm * D) := by simp
    refine hbd.trans ?_
    show (k + 1 : ℝ) * (Cm * D) ≤ _ * Q
    have : (k + 1 : ℝ) * (γm⁻¹ * Cr) * (1 + Cm) * Q = (k + 1 : ℝ) * D * (1 + Cm) := by rw [hD]; ring
    rw [this]
    have h1 : 0 ≤ (k + 1 : ℝ) * D := by positivity
    nlinarith

end HRS.MS.S48
