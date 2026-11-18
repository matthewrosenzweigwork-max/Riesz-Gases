import HRS.MS.PoisHighAux3
import HRS.MS.PoisInvAux2
import HRS.MS.PoisLipAux3

/-!
# POIS-RESOLVENT, part 1: Lipschitz (unbounded) data for the semigroup

The merged semigroup bounds (`pois_shorttime`, `pois_longtime`, `pois_centered_decay`) need a bound on
`‖r‖_∞`.  The Poisson right-hand side `r` of the derivative row is only Lipschitz, so everything is
transferred by the truncations `r_N = N ψ(r/N)` (`ψ(s) = s·bump(s)`): `r_N = r` near every point with
`|r| < N`, `‖D^i r_N‖ ≤ K ‖D^i r‖`-type bounds linear in the derivative bound `D` for `N ≥ max D 1`
(`rf_tr_deriv`, `rf_tr_bounds`).  Main results:
* `rf_iterated_integral`: differentiation under the integral with integrable dominating functions;
* `rf_sg_contDiff`: `P_t r ∈ C^m` with `D^j P_t r = E D^j (r ∘ flow)` for `r` with bounded
  derivatives of orders `1..m` only (`r` of linear growth);
* `rf_tr_tendsto`: `D^j P_t r_N → D^j P_t r` pointwise;
* `rf_deriv_bound`: `‖D^j P_t r‖ ≤ Kd D e^{-c0(t-1)}` for all `t ≥ 0`;
* `rf_decay`: `|P_t r(x)| ≤ κ⁻¹ K D e^{-c0 t}(|x| + √m₂)` for centered `r`.
Helper lemmas carry the prefix `rf_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.PoisRes

variable {d : ℕ}

/-! ### The truncation `r_N = N ψ(r/N)` -/

/-- bump on `ℝ`, `1` on `[-1,1]`, supported in `[-2,2]` -/
def rfBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `ψ s = s · bump s`: smooth, compactly supported, `ψ s = s` for `|s| ≤ 1`. -/
def rfPsi (s : ℝ) : ℝ := s * rfBump s

theorem rf_psi_contDiff : ContDiff ℝ ∞ rfPsi := contDiff_id.mul rfBump.contDiff

theorem rf_psi_eq {s : ℝ} (hs : |s| ≤ 1) : rfPsi s = s := by
  unfold rfPsi
  have h1 : rfBump.rIn = 1 := rfl
  rw [rfBump.one_of_mem_closedBall (by simpa [abs_le, mem_closedBall_zero_iff, Real.norm_eq_abs, h1] using hs)]
  ring

theorem rf_psi_zero {s : ℝ} (hs : 2 ≤ |s|) : rfPsi s = 0 := by
  unfold rfPsi
  have h1 : rfBump.rOut = 2 := rfl
  rw [rfBump.zero_of_le_dist (by simpa [dist_zero_right, Real.norm_eq_abs, h1] using hs)]
  ring

theorem rf_psi_abs_le (s : ℝ) : |rfPsi s| ≤ |s| := by
  unfold rfPsi
  rw [abs_mul, abs_of_nonneg rfBump.nonneg]
  exact mul_le_of_le_one_right (abs_nonneg _) rfBump.le_one

theorem rf_psi_abs_le_two (s : ℝ) : |rfPsi s| ≤ 2 := by
  rcases le_or_gt 2 |s| with h | h
  · rw [rf_psi_zero h]; simp
  · exact (rf_psi_abs_le s).trans h.le

theorem rf_psi_support : HasCompactSupport rfPsi := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) (fun s hs => ?_)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, not_le] at hs
  exact rf_psi_zero hs.le

theorem rf_psi_bound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ n, ∀ s, ‖iteratedFDeriv ℝ k rfPsi s‖ ≤ C := by
  have h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖iteratedFDeriv ℝ k rfPsi s‖ ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := (rf_psi_contDiff.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (rf_psi_support.iteratedFDeriv k)
    exact ⟨max C 0, le_max_right _ _, fun s => (hC s).trans (le_max_left _ _)⟩
  choose C hC0 hC using h
  refine ⟨∑ k ∈ Finset.range (n + 1), C k, Finset.sum_nonneg fun k _ => hC0 k, fun k hk s => ?_⟩
  exact (hC k s).trans (Finset.single_le_sum (f := C) (fun k _ => hC0 k) (Finset.mem_range.2 (by omega)))

/-- The truncation `r_N = N ψ(r/N)`. -/
def rfTr (N : ℝ) (r : Euc d → ℝ) (y : Euc d) : ℝ := N * rfPsi (r y / N)

theorem rf_tr_contDiff {N : ℝ} {k : ℕ} {r : Euc d → ℝ} (hr : ContDiff ℝ (k : WithTop ℕ∞) r) :
    ContDiff ℝ (k : WithTop ℕ∞) (rfTr N r) := by
  unfold rfTr
  exact contDiff_const.mul ((rf_psi_contDiff.of_le (by exact_mod_cast le_top)).comp (hr.div_const N))

theorem rf_tr_abs_le {N : ℝ} (hN : 0 < N) (r : Euc d → ℝ) (y : Euc d) : |rfTr N r y| ≤ |r y| := by
  unfold rfTr
  rw [abs_mul, abs_of_pos hN]
  have := rf_psi_abs_le (r y / N)
  rw [abs_div, abs_of_pos hN] at this
  calc N * |rfPsi (r y / N)| ≤ N * (|r y| / N) := mul_le_mul_of_nonneg_left this hN.le
    _ = |r y| := by field_simp

theorem rf_tr_abs_le_two {N : ℝ} (hN : 0 < N) (r : Euc d → ℝ) (y : Euc d) : |rfTr N r y| ≤ 2 * N := by
  unfold rfTr
  rw [abs_mul, abs_of_pos hN]
  nlinarith [rf_psi_abs_le_two (r y / N)]

theorem rf_tr_eventuallyEq {N : ℝ} (hN : 0 < N) {r : Euc d → ℝ} (hr : Continuous r) {y : Euc d}
    (hy : |r y| < N) : rfTr N r =ᶠ[𝓝 y] r := by
  have h1 : ∀ᶠ z in 𝓝 y, |r z| < N := by
    have : IsOpen {z | |r z| < N} := isOpen_lt (hr.abs) continuous_const
    exact this.mem_nhds hy
  filter_upwards [h1] with z hz
  unfold rfTr
  rw [rf_psi_eq (by rw [abs_div, abs_of_pos hN, div_le_one hN]; exact hz.le)]
  field_simp


theorem rf_tr_deriv {n : ℕ} (hn : 1 ≤ n) {r : Euc d → ℝ} (hr : ContDiff ℝ (n : WithTop ℕ∞) r)
    {D N : ℝ} (hD : 0 ≤ D) (hN1 : 1 ≤ N) (hND : D ≤ N) {C : ℝ}
    (hC : ∀ k ≤ n, ∀ s, ‖iteratedFDeriv ℝ k rfPsi s‖ ≤ C) (x : Euc d)
    (hx : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i r x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (rfTr N r) x‖ ≤ (n.factorial : ℝ) * C * D := by
  have hN0 : 0 < N := by linarith
  set f : Euc d → ℝ := fun y => N⁻¹ * r y with hf
  have hfc : ContDiff ℝ (n : WithTop ℕ∞) f := contDiff_const.mul hr
  set δ : ℝ := D / N with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hD hN0.le
  have hδ1 : δ ≤ 1 := (div_le_one hN0).2 hND
  set Δ : ℝ := δ ^ ((n : ℝ)⁻¹) with hΔ
  have hΔ0 : 0 ≤ Δ := Real.rpow_nonneg hδ0 _
  have hΔn : Δ ^ n = δ := Real.rpow_inv_natCast_pow hδ0 (by omega)
  have hΔ1 : Δ ≤ 1 := by
    by_contra h
    push Not at h
    have := one_lt_pow₀ h (show n ≠ 0 by omega)
    linarith
  have hfd : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ Δ ^ i := by
    intro i hi1 hin
    have e : iteratedFDeriv ℝ i f x = N⁻¹ • iteratedFDeriv ℝ i r x := by
      have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := N⁻¹) (f := r) (x := x) (i := i)
        ((hr.of_le (by exact_mod_cast hin)).contDiffAt)
      simpa [hf, smul_eq_mul] using this
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hN0.le]
    have h1 : N⁻¹ * ‖iteratedFDeriv ℝ i r x‖ ≤ δ := by
      rw [hδ, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hx i hi1 hin) (inv_nonneg.2 hN0.le)
    refine h1.trans ?_
    rw [← hΔn]
    exact pow_le_pow_of_le_one hΔ0 hΔ1 hin
  have hcomp := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := rfPsi) (f := f) (N := (n : WithTop ℕ∞))
    (rf_psi_contDiff.of_le (by exact_mod_cast le_top)) hfc le_rfl x (C := C) (D := Δ)
    (fun i hi => hC i hi _) hfd
  have e2 : rfTr N r = N • (rfPsi ∘ f) := by
    funext y
    simp only [rfTr, hf, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    congr 2
    field_simp
  have hcd : ContDiffAt ℝ (n : WithTop ℕ∞) (rfPsi ∘ f) x :=
    ((rf_psi_contDiff.of_le (by exact_mod_cast le_top)).comp hfc).contDiffAt
  rw [e2, iteratedFDeriv_const_smul_apply hcd, norm_smul, Real.norm_of_nonneg hN0.le]
  calc N * ‖iteratedFDeriv ℝ n (rfPsi ∘ f) x‖ ≤ N * ((n.factorial : ℝ) * C * Δ ^ n) :=
        mul_le_mul_of_nonneg_left hcomp hN0.le
    _ = (n.factorial : ℝ) * C * D := by
        rw [hΔn, hδ]; field_simp


/-! ### Differentiation under the integral sign with integrable (not constant) bounds -/

open HRS.MS.PoisSg in
/-- Generalisation of `sg_iteratedFDeriv_integral`: the derivatives of order `1..k` are dominated by
integrable functions `bd i` (instead of constants), and the order `0` only needs integrability at each
point. -/
theorem rf_iterated_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : Ω → Euc d → F) (k : ℕ) (hk : 1 ≤ k) (hG : ∀ a, ContDiff ℝ (k : WithTop ℕ∞) (G a))
    (bd : ℕ → Ω → ℝ) (hbdint : ∀ i, 1 ≤ i → i ≤ k → Integrable (bd i) μ)
    (hbd : ∀ i, 1 ≤ i → i ≤ k → ∀ᵐ a ∂μ, ∀ x, ‖iteratedFDeriv ℝ i (G a) x‖ ≤ bd i a)
    (hint0 : ∀ x, Integrable (fun a => G a x) μ)
    (hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ i (G a) x) μ) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun x => ∫ a, G a x ∂μ) ∧
      ∀ i ≤ k, ∀ x, iteratedFDeriv ℝ i (fun x => ∫ a, G a x ∂μ) x =
        ∫ a, iteratedFDeriv ℝ i (G a) x ∂μ := by
  have hint : ∀ i ≤ k, ∀ x, Integrable (fun a => iteratedFDeriv ℝ i (G a) x) μ := by
    intro i hi x
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have e : (fun a => iteratedFDeriv ℝ 0 (G a) x) =
          fun a => (continuousMultilinearCurryFin0 ℝ (Euc d) F).symm (G a x) := by
        funext a; rw [iteratedFDeriv_zero_eq_comp]; rfl
      rw [e]
      exact (continuousMultilinearCurryFin0 ℝ (Euc d) F).symm.toContinuousLinearEquiv.integrable_comp_iff.2
        (hint0 x)
    · refine (hbdint i h0 hi).mono' (hmeas i hi x) ?_
      filter_upwards [hbd i h0 hi] with a ha using ha x
  have step : ∀ i < k, ∀ x, HasFDerivAt (fun x => ∫ a, iteratedFDeriv ℝ i (G a) x ∂μ)
      (∫ a, fderiv ℝ (iteratedFDeriv ℝ i (G a)) x ∂μ) x := by
    intro i hi x
    have hF'meas : AEStronglyMeasurable (fun a => fderiv ℝ (iteratedFDeriv ℝ i (G a)) x) μ := by
      have e : (fun a => fderiv ℝ (iteratedFDeriv ℝ i (G a)) x) = fun a =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F
            (iteratedFDeriv ℝ (i + 1) (G a) x) := by
        funext a; rw [iteratedFDeriv_succ_eq_comp_left]; simp
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F).continuous.comp_aestronglyMeasurable (hmeas (i + 1) hi x)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x a => iteratedFDeriv ℝ i (G a) x)
      (F' := fun x a => fderiv ℝ (iteratedFDeriv ℝ i (G a)) x) (s := Set.univ)
      (bound := bd (i + 1)) Filter.univ_mem (Eventually.of_forall fun y => hmeas i hi.le y)
      (hint i hi.le x) hF'meas ?_ (hbdint (i + 1) (by omega) hi) ?_
    · filter_upwards [hbd (i + 1) (by omega) hi] with a ha y _
      have e : fderiv ℝ (iteratedFDeriv ℝ i (G a)) y =
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F
            (iteratedFDeriv ℝ (i + 1) (G a) y) := by
        rw [iteratedFDeriv_succ_eq_comp_left]; simp
      rw [e, LinearIsometryEquiv.norm_map]; exact ha y
    · exact Eventually.of_forall fun a y _ =>
        (((hG a).differentiable_iteratedFDeriv (by exact_mod_cast hi)) y).hasFDerivAt
  have hS : ∀ i ≤ k, iteratedFDeriv ℝ i (fun x => ∫ a, G a x ∂μ) =
      fun x => ∫ a, iteratedFDeriv ℝ i (G a) x ∂μ := by
    intro i
    induction i with
    | zero =>
      intro _
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp]
      have : ∀ a, iteratedFDeriv ℝ 0 (G a) x =
          (continuousMultilinearCurryFin0 ℝ (Euc d) F).symm (G a x) := fun a => by
        rw [iteratedFDeriv_zero_eq_comp]; rfl
      simp_rw [this]
      exact ((continuousMultilinearCurryFin0 ℝ (Euc d) F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ i ih =>
      intro hi
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp, ih (Nat.le_of_succ_le hi),
        (step i hi x).fderiv]
      have : ∀ a, iteratedFDeriv ℝ (i + 1) (G a) x =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F).symm
            (fderiv ℝ (iteratedFDeriv ℝ i (G a)) x) := fun a => by
        rw [iteratedFDeriv_succ_eq_comp_left]; rfl
      simp_rw [this]
      exact (sg_integral_curryLeft i _).symm
  refine ⟨?_, fun i hi x => by rw [hS i hi]⟩
  have hk' : ∀ i ≤ k, Continuous fun x => ∫ a, iteratedFDeriv ℝ i (G a) x ∂μ := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      exact continuous_iff_continuousAt.2 fun x => (step 0 (by omega) x).continuousAt
    · exact continuous_of_dominated (bound := bd i) (fun y => hmeas i hi y)
        (fun y => by filter_upwards [hbd i h0 hi] with a ha using ha y) (hbdint i h0 hi)
        (Eventually.of_forall fun a => (hG a).continuous_iteratedFDeriv (by exact_mod_cast hi))
  have key : ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun x => ∫ a, G a x ∂μ) := by
    refine contDiff_iff_continuous_differentiable.2 ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : i ≤ k := by exact_mod_cast hi
      rw [hS i hi']; exact hk' i hi'
    · have hi' : i < k := by exact_mod_cast hi
      rw [hS i hi'.le]
      exact fun x => (step i hi' x).differentiableAt
  exact_mod_cast key


/-! ### The semigroup of a Lipschitz (unbounded) function: smoothness and the derivative formula -/

section Sg

open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm
  HRS.MS.PoisHigh HRS.MS.PoisLip HRS.MS.PoisMax

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem rf_D_nonneg {m : ℕ} (hm : 1 ≤ m) {r : Euc d → ℝ} {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) : 0 ≤ D :=
  (norm_nonneg _).trans (hD 1 le_rfl hm 0)

theorem rf_fderiv_bound {m : ℕ} (hm : 1 ≤ m) {r : Euc d → ℝ} {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) (y : Euc d) :
    ‖fderiv ℝ r y‖ ≤ D := by
  have := hD 1 le_rfl hm y
  rwa [norm_iteratedFDeriv_one] at this

theorem rf_fderiv2_bound {m : ℕ} (hm : 2 ≤ m) {r : Euc d → ℝ} {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) (y : Euc d) :
    ‖fderiv ℝ (fderiv ℝ r) y‖ ≤ D := by
  rw [kl_norm_fderiv_fderiv']; exact hD 2 (by norm_num) hm y

theorem rf_lin_growth {m : ℕ} (hm : 2 ≤ m) {r : Euc d → ℝ} (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) (y : Euc d) :
    |r y| ≤ |r 0| + D * ‖y‖ := by
  have h := ld_lip_of_fderiv (hr.of_le (by exact_mod_cast hm)) (rf_fderiv_bound (by omega) hD) y 0
  rw [sub_zero] at h
  have := abs_sub_abs_le_abs_sub (r y) (r 0)
  linarith

/-- Integrability of `r ∘ X` for `r` of linear growth and `X` with finite second moment. -/
theorem rf_integrable_comp [IsProbabilityMeasure P] {m : ℕ} (hm : 2 ≤ m) {r : Euc d → ℝ}
    (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) {X : Ω → Euc d}
    (hX : Measurable X) (hX2 : Integrable (fun o => ‖X o‖ ^ 2) P) :
    Integrable (fun o => r (X o)) P :=
  kl_integrable_lin P (hr.continuous.measurable) (a := |r 0|) (a' := D) (rf_D_nonneg (by omega) hD)
    (rf_lin_growth hm hr hD) hX hX2

/-- **Smoothness of `P_t r` for `r` with bounded derivatives of orders `1..m` (no bound on `r`), and the
integral formula for its derivatives.** -/
theorem rf_sg_contDiff [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ} (hq : 0 < q)
    {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {r : Euc d → ℝ}
    (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (m : WithTop ℕ∞) (sg P W q B t r) ∧
      ∀ j ≤ m, ∀ x, iteratedFDeriv ℝ j (sg P W q B t r) x =
        ∫ o, iteratedFDeriv ℝ j (fun y => r (flowMap q B (fun s => W s o) t y)) x ∂P := by
  have hn := sgNoise_of_brownian hW
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  obtain ⟨C0, hC0, hflow⟩ := pois_flow (d := d) q Mb hq m hm t ht
  obtain ⟨Cs, hCs0, hCs⟩ := sg_second_moment.{u} (d := d) q Mb hq t ht
  set Df : ℝ := max 1 C0 with hDf
  have hDf1 : 1 ≤ Df := le_max_left _ _
  have hfl := fun o => hflow B hB (fun s => W s o) (hn.cont o) (hn.zero o)
  set G : Ω → Euc d → ℝ := fun o y => r (flowMap q B (fun s => W s o) t y) with hG
  have hGc : ∀ o, ContDiff ℝ (m : WithTop ℕ∞) (G o) := fun o => hr.comp ((hfl o).2 t ⟨ht, le_rfl⟩).1
  have hmeasF := sg_measurable_flowMap hn hq.le (by omega : 1 ≤ m) hB ht
  have hGm : StronglyMeasurable (fun p : Ω × Euc d => G p.1 p.2) :=
    (hr.continuous.measurable.comp hmeasF).stronglyMeasurable
  have hbdpt : ∀ i, 1 ≤ i → i ≤ m → ∀ o x, ‖iteratedFDeriv ℝ i (G o) x‖ ≤
      (i.factorial : ℝ) * D * Df ^ i := by
    intro i hi1 him o x
    have hle : (i : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast him
    have := hs_comp_deriv_only hi1 (hr.of_le hle) (((hfl o).2 t ⟨ht, le_rfl⟩).1.of_le hle) x hD0
      (fun j h1 h2 => hD j h1 (h2.trans him) _)
      (fun j h1 h2 => (((hfl o).2 t ⟨ht, le_rfl⟩).2 j h1 (h2.trans him) x).trans
        ((le_max_right _ _).trans (le_self_pow₀ hDf1 (by omega))))
    exact this
  have hint0 : ∀ x, Integrable (fun o => G o x) P := by
    intro x
    have h1 := hmeasF.comp (measurable_id.prodMk (measurable_const (a := x)))
    have h2 := (hCs P ℱ W hW m (by omega) B hB t ⟨ht, le_rfl⟩ x).1
    exact rf_integrable_comp (X := fun o => flowMap q B (fun s => W s o) t x) hm hr hD h1 h2
  have hmeas : ∀ i ≤ m, ∀ x, AEStronglyMeasurable (fun o => iteratedFDeriv ℝ i (G o) x) P := by
    intro i hi x
    have := sg_stronglyMeasurable_iteratedFDeriv G hGm i
      (fun o => (hGc o).of_le (by exact_mod_cast hi))
    exact (this.comp_measurable (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable
  obtain ⟨h1, h2⟩ := rf_iterated_integral (μ := P) G m (by omega) hGc
    (fun i => fun _ => (i.factorial : ℝ) * D * Df ^ i) (fun i _ _ => integrable_const _)
    (fun i hi1 him => Eventually.of_forall fun o x => hbdpt i hi1 him o x) hint0 hmeas
  exact ⟨h1, h2⟩

/-- uniform pathwise bounds on the derivatives of `r ∘ flow` (only derivatives of `r` of order `≥ 1`). -/
theorem rf_comp_bound (q Mb : ℝ) (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    ∃ Df : ℝ, 1 ≤ Df ∧ ∀ (B : Euc d → Euc d), HasCbBound m Mb B → ∀ w : ℝ≥0 → Fin d → ℝ,
      Continuous w → w 0 = 0 → ContDiff ℝ (m : WithTop ℕ∞) (flowMap q B w t) ∧
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ D : ℝ, 0 ≤ D →
        (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) →
        ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ x, ‖iteratedFDeriv ℝ i (fun y => r (flowMap q B w t y)) x‖ ≤
          (i.factorial : ℝ) * D * Df ^ i := by
  obtain ⟨C0, hC0, hflow⟩ := pois_flow (d := d) q Mb hq m hm t ht
  refine ⟨max 1 C0, le_max_left _ _, fun B hB w hw hw0 => ?_⟩
  have hfl := hflow B hB w hw hw0
  have hfc := ((hfl.2 t ⟨ht, le_rfl⟩).1)
  refine ⟨hfc, fun r hr D hD0 hD i hi1 him x => ?_⟩
  have hle : (i : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast him
  exact hs_comp_deriv_only hi1 (hr.of_le hle) (hfc.of_le hle) x hD0
    (fun j h1 h2 => hD j h1 (h2.trans him) _)
    (fun j h1 h2 => ((hfl.2 t ⟨ht, le_rfl⟩).2 j h1 (h2.trans him) x).trans
      ((le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))))

theorem rf_meas_iter [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ} (hq : 0 < q)
    {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {t : ℝ} (ht : 0 ≤ t)
    {g : Euc d → ℝ} (hg : ContDiff ℝ (m : WithTop ℕ∞) g) (i : ℕ) (hi : i ≤ m) (x : Euc d) :
    AEStronglyMeasurable (fun o => iteratedFDeriv ℝ i
      (fun y => g (flowMap q B (fun s => W s o) t y)) x) P := by
  have hn := sgNoise_of_brownian hW
  obtain ⟨Df, hDf, hfl⟩ := rf_comp_bound (d := d) q Mb hq hm ht
  have hmeasF := sg_measurable_flowMap hn hq.le (by omega : 1 ≤ m) hB ht
  have hGm : StronglyMeasurable (fun p : Ω × Euc d =>
      g (flowMap q B (fun s => W s p.1) t p.2)) :=
    (hg.continuous.measurable.comp hmeasF).stronglyMeasurable
  have := sg_stronglyMeasurable_iteratedFDeriv
    (fun o y => g (flowMap q B (fun s => W s o) t y)) hGm i
    (fun o => (hg.comp (hfl B hB (fun s => W s o) (hn.cont o) (hn.zero o)).1).of_le
      (by exact_mod_cast hi))
  exact (this.comp_measurable (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable

/-- uniform derivative bounds of the truncations -/
theorem rf_tr_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {r : Euc d → ℝ}, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ {D N : ℝ}, 0 ≤ D →
      1 ≤ N → D ≤ N → (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) →
      ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ x, ‖iteratedFDeriv ℝ i (rfTr N r) x‖ ≤ K * D := by
  obtain ⟨C, hC0, hC⟩ := rf_psi_bound m
  refine ⟨(m.factorial : ℝ) * C, by positivity, fun {r} hr D N hD hN1 hND hDr i hi1 him x => ?_⟩
  have := rf_tr_deriv hi1 (hr.of_le (by exact_mod_cast him)) hD hN1 hND
    (fun k hk s => hC k (hk.trans him) s) x (fun j h1 h2 => hDr j h1 (h2.trans him) x)
  refine this.trans ?_
  have hf : (i.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le him
  calc (i.factorial : ℝ) * C * D ≤ (m.factorial : ℝ) * C * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf hC0) hD
    _ = _ := by ring


/-- Convergence of the truncations: `D^j P_t r_N (x) → D^j P_t r (x)`. -/
theorem rf_tr_tendsto [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ} (hq : 0 < q)
    {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {r : Euc d → ℝ}
    (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {j : ℕ} (hj : j ≤ m) (x : Euc d) :
    Tendsto (fun N : ℕ => iteratedFDeriv ℝ j (sg P W q B t (rfTr (N : ℝ) r)) x) atTop
      (𝓝 (iteratedFDeriv ℝ j (sg P W q B t r) x)) := by
  have hn := sgNoise_of_brownian hW
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  obtain ⟨K, hK0, hK⟩ := rf_tr_bounds (d := d) m (by omega)
  obtain ⟨Df, hDf1, hfl⟩ := rf_comp_bound (d := d) q Mb hq hm ht
  obtain ⟨Cs, hCs0, hCs⟩ := sg_second_moment.{u} (d := d) q Mb hq t ht
  have hmeasF := sg_measurable_flowMap hn hq.le (by omega : 1 ≤ m) hB ht
  have hflx : ∀ o, ContDiff ℝ (m : WithTop ℕ∞) (flowMap q B (fun s => W s o) t) := fun o =>
    (hfl B hB (fun s => W s o) (hn.cont o) (hn.zero o)).1
  have hrx : Integrable (fun o => r (flowMap q B (fun s => W s o) t x)) P := by
    have h1 := hmeasF.comp (measurable_id.prodMk (measurable_const (a := x)))
    have h2 := (hCs P ℱ W hW m (by omega) B hB t ⟨ht, le_rfl⟩ x).1
    exact rf_integrable_comp (X := fun o => flowMap q B (fun s => W s o) t x) hm hr hD h1 h2
  have hev : ∀ᶠ N : ℕ in atTop, (D ≤ (N : ℝ) ∧ 1 ≤ (N : ℝ)) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop D).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop 1)
  have hform : ∀ᶠ N : ℕ in atTop, iteratedFDeriv ℝ j (sg P W q B t (rfTr (N : ℝ) r)) x =
      ∫ o, iteratedFDeriv ℝ j (fun y => rfTr (N : ℝ) r (flowMap q B (fun s => W s o) t y)) x ∂P := by
    filter_upwards [hev] with N hN
    refine (rf_sg_contDiff hW hq hm hB (rf_tr_contDiff hr) (D := K * D) ?_ ht).2 j hj x
    exact fun i h1 h2 y => hK hr hD0 hN.2 hN.1 hD i h1 h2 y
  rw [(rf_sg_contDiff hW hq hm hB hr hD ht).2 j hj x]
  refine Tendsto.congr' (EventuallyEq.symm (hform.mono fun N hN => hN)) ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (fun o => ‖r (flowMap q B (fun s => W s o) t x)‖ + (j.factorial : ℝ) * (K * D) * Df ^ j)
    (hev.mono fun N hN => rf_meas_iter hW hq hm hB ht (rf_tr_contDiff hr) j hj x)
    (hev.mono fun N hN => Eventually.of_forall fun o => ?_) (hrx.norm.add (integrable_const _))
    (Eventually.of_forall fun o => ?_)
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [norm_iteratedFDeriv_zero]
      have := rf_tr_abs_le (d := d) (N := (N : ℝ)) (by linarith [hN.2]) r
        (flowMap q B (fun s => W s o) t x)
      rw [Real.norm_eq_abs]
      have h2 : 0 ≤ (K * D) * Df ^ 0 := by positivity
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one] at h2 ⊢
      linarith [abs_nonneg (r (flowMap q B (fun s => W s o) t x)), Real.norm_eq_abs (r (flowMap q B (fun s => W s o) t x))]
    · have := (hfl B hB (fun s => W s o) (hn.cont o) (hn.zero o)).2 (rfTr (N : ℝ) r)
        (rf_tr_contDiff hr) (K * D) (by positivity)
        (fun i h1 h2 y => hK hr hD0 hN.2 hN.1 hD i h1 h2 y) j h0 hj x
      linarith [norm_nonneg (r (flowMap q B (fun s => W s o) t x))]
  · have hlim : ∀ᶠ N : ℕ in atTop, iteratedFDeriv ℝ j
        (fun y => rfTr (N : ℝ) r (flowMap q B (fun s => W s o) t y)) x =
        iteratedFDeriv ℝ j (fun y => r (flowMap q B (fun s => W s o) t y)) x := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop
        (|r (flowMap q B (fun s => W s o) t x)|), hev] with N hN1 hN2
      have h1 := rf_tr_eventuallyEq (d := d) (N := (N : ℝ)) (by linarith [hN2.2]) hr.continuous hN1
      have h2 := h1.comp_tendsto (hflx o).continuous.continuousAt.tendsto
      exact (h2.iteratedFDeriv ℝ j).self_of_nhds
    exact tendsto_const_nhds.congr' (hlim.mono fun N hN => hN.symm)

theorem rf_c0_pos (q Mb : ℝ) (hq : 0 < q) : 0 < pm_c0 q Mb :=
  mul_pos (Real.exp_pos _) (lt_min one_pos (by linarith))

/-- value convergence of the truncations (order `0`) -/
theorem rf_tr_tendsto_val [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {r : Euc d → ℝ}
    (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (x : Euc d) :
    Tendsto (fun N : ℕ => sg P W q B t (rfTr (N : ℝ) r) x) atTop (𝓝 (sg P W q B t r x)) := by
  have h := rf_tr_tendsto hW hq hm hB hr hD ht (Nat.zero_le m) x
  have h2 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ
    (0 : Fin 0 → Euc d)).continuous.tendsto _).comp h
  simpa [Function.comp_def, iteratedFDeriv_zero_apply] using h2

/-- order-`j` derivative bound of `P_t r` for a Lipschitz `r`, `j` fixed. -/
theorem rf_deriv_bound_j (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (j : ℕ)
    (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ D : ℝ,
      (∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ x, ‖iteratedFDeriv ℝ i r x‖ ≤ D) → ∀ t : ℝ, 0 ≤ t → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ Kd * D * Real.exp (-(pm_c0 q Mb) * (t - 1)) := by
  obtain ⟨Cs, hCs0, hCs⟩ := pois_shorttime.{u} (d := d) q Mb hq m hm j hj1 hjm
  obtain ⟨Cl, hCl0, hCl⟩ := pois_longtime.{u} (d := d) q Mb hq hMb m hm j hj1 hjm
  obtain ⟨K, hK0, hK⟩ := rf_tr_bounds (d := d) m (by omega)
  refine ⟨Cs * j * K + Cl * K, by positivity, fun {Ω} {mΩ} P _ ℱ W hW B hB r hr D hD t ht x => ?_⟩
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  have hc0 := rf_c0_pos q Mb hq
  have hev : ∀ᶠ N : ℕ in atTop, (D ≤ (N : ℝ) ∧ 1 ≤ (N : ℝ)) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop D).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop 1)
  refine le_of_tendsto (rf_tr_tendsto hW hq hm hB hr hD ht hjm x).norm (hev.mono fun N hN => ?_)
  set M : ℕ → ℝ := fun i => if i = 0 then 2 * (N : ℝ) else K * D with hMdef
  have hM : ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i (rfTr (N : ℝ) r) y‖ ≤ M i := by
    intro i hi y
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      simp only [hMdef, if_true, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact rf_tr_abs_le_two (by linarith [hN.2]) r y
    · simp only [hMdef, Nat.pos_iff_ne_zero.1 h0, ite_false]
      exact hK hr hD0 hN.2 hN.1 hD i h0 hi y
  have hrN := rf_tr_contDiff (N := (N : ℝ)) hr
  have hex : 0 ≤ Real.exp (-(pm_c0 q Mb) * (t - 1)) := (Real.exp_pos _).le
  have hKD : 0 ≤ K * D := mul_nonneg hK0 hD0
  rcases le_or_gt t 1 with h1 | h1
  · have h := hCs P ℱ W hW B hB _ hrN M hM t ht h1 x
    have hsum : ∑ i ∈ Finset.Icc 1 j, M i = j * (K * D) := by
      rw [Finset.sum_congr rfl (g := fun _ => K * D) (fun i hi => by
        have h1 := (Finset.mem_Icc.1 hi).1
        simp only [hMdef]
        rw [if_neg (by omega)])]
      simp
    rw [hsum] at h
    have he : 1 ≤ Real.exp (-(pm_c0 q Mb) * (t - 1)) :=
      Real.one_le_exp (by nlinarith)
    refine h.trans ?_
    have : Cs * (j * (K * D)) ≤ Cs * (j * (K * D)) * Real.exp (-(pm_c0 q Mb) * (t - 1)) :=
      le_mul_of_one_le_right (by positivity) he
    nlinarith [mul_nonneg (mul_nonneg hCl0 hKD) hex]
  · have h := hCl P ℱ W hW B hB _ hrN M hM t h1.le x
    have hM1 : M 1 = K * D := by simp [hMdef]
    rw [hM1] at h
    refine h.trans ?_
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCs0 (Nat.cast_nonneg j)) hKD) hex]

theorem rf_deriv_bound (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ D : ℝ,
      (∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ x, ‖iteratedFDeriv ℝ i r x‖ ≤ D) → ∀ t : ℝ, 0 ≤ t →
      ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ Kd * D * Real.exp (-(pm_c0 q Mb) * (t - 1)) := by
  have h : ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ (1 ≤ j → j ≤ m → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ D : ℝ,
      (∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ x, ‖iteratedFDeriv ℝ i r x‖ ≤ D) → ∀ t : ℝ, 0 ≤ t → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ K * D * Real.exp (-(pm_c0 q Mb) * (t - 1))) := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ m
    · obtain ⟨K, hK0, hK⟩ := rf_deriv_bound_j (d := d) q Mb hq hMb m hm j hj.1 hj.2
      exact ⟨K, hK0, fun _ _ => hK⟩
    · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose K hK0 hK using h
  refine ⟨∑ j ∈ Finset.range (m + 1), K j, Finset.sum_nonneg fun j _ => hK0 j,
    fun {Ω} {mΩ} P _ ℱ W hW B hB r hr D hD t ht j hj1 hjm x => ?_⟩
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  refine (hK j hj1 hjm P ℱ W hW B hB r hr D hD t ht x).trans ?_
  have : K j ≤ ∑ j ∈ Finset.range (m + 1), K j :=
    Finset.single_le_sum (f := K) (fun j _ => hK0 j) (Finset.mem_range.2 (by omega))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hD0) (Real.exp_pos _).le

theorem rf_iter_sub_const {f : Euc d → ℝ} {i : ℕ} (hf : ContDiff ℝ (i : WithTop ℕ∞) f) (hi : 1 ≤ i)
    (c : ℝ) (x : Euc d) :
    iteratedFDeriv ℝ i (fun y => f y - c) x = iteratedFDeriv ℝ i f x := by
  have e1 : (fun y => f y - c) = f - fun _ => c := rfl
  rw [e1, iteratedFDeriv_sub_apply hf.contDiffAt contDiff_const.contDiffAt,
    iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem rf_sg_sub_const [IsProbabilityMeasure P] {q : ℝ} {B : Euc d → Euc d} {t : ℝ} {g : Euc d → ℝ}
    (hg : ∀ x, Integrable (fun o => g (flowMap q B (fun s => W s o) t x)) P) (c : ℝ) (x : Euc d) :
    sg P W q B t (fun y => g y - c) x = sg P W q B t g x - c := by
  unfold sg
  rw [integral_sub (hg x) (integrable_const c)]
  simp

theorem rf_cN_tendsto {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ) {m2 : ℝ} (hm2 : ∫ y, ‖y‖ ^ 2 ∂μ ≤ m2)
    {m : ℕ} (hm : 2 ≤ m) {r : Euc d → ℝ} (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) :
    Tendsto (fun N : ℕ => ∫ y, rfTr (N : ℝ) r y ∂μ) atTop (𝓝 (∫ y, r y ∂μ)) := by
  obtain ⟨hi1, -⟩ := ld_first_moment hμ2 hm2
  refine tendsto_integral_of_dominated_convergence (fun y => |r 0| + D * ‖y‖) (fun N => ?_)
    ((integrable_const _).add (hi1.const_mul D)) (fun N => ?_) ?_
  · exact ((rf_tr_contDiff (k := 0) (N := (N : ℝ)) (hr.of_le (by exact_mod_cast Nat.zero_le m))).continuous).aestronglyMeasurable
  · have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      refine Eventually.of_forall fun y => ?_
      simp only [rfTr, Nat.cast_zero, zero_mul, norm_zero]
      positivity
    · refine Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs]
      exact (rf_tr_abs_le (by exact_mod_cast h0) r y).trans (rf_lin_growth hm hr hD y)
  · refine Eventually.of_forall fun y => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (|r y|)] with N h1
    have := rf_tr_eventuallyEq (d := d) (N := (N : ℝ)) (lt_of_le_of_lt (abs_nonneg _) h1)
      hr.continuous h1
    exact (this.self_of_nhds).symm

/-- Pointwise decay of `P_t r` for a centered Lipschitz `r` (no bound on `r`). -/
theorem rf_decay (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ μ : Measure (Euc d), IsInvariantMeasure (fun x => -q • x + B x) μ →
      Integrable (fun y : Euc d => ‖y‖ ^ 2) μ → ∀ m2 : ℝ, ∫ y, ‖y‖ ^ 2 ∂μ ≤ m2 →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ D : ℝ,
      (∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ x, ‖iteratedFDeriv ℝ i r x‖ ≤ D) → ∫ y, r y ∂μ = 0 →
      ∀ t : ℝ, 0 ≤ t → ∀ x, |sg P W q B t r x| ≤
        (pm_kappa q Mb)⁻¹ * (K * D) * Real.exp (-(pm_c0 q Mb) * t) * (‖x‖ + Real.sqrt m2) := by
  obtain ⟨K, hK0, hK⟩ := rf_tr_bounds (d := d) m (by omega)
  refine ⟨K, hK0, fun {Ω} {mΩ} P _ ℱ W hW B hB μ hμ hμ2 m2 hm2 r hr D hD hcen t ht x => ?_⟩
  haveI : IsProbabilityMeasure μ := hμ.1
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  have hn := sgNoise_of_brownian hW
  have hev : ∀ᶠ N : ℕ in atTop, (D ≤ (N : ℝ) ∧ 1 ≤ (N : ℝ)) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop D).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop 1)
  have hlim : Tendsto (fun N : ℕ => |sg P W q B t (rfTr (N : ℝ) r) x - ∫ y, rfTr (N : ℝ) r y ∂μ|)
      atTop (𝓝 |sg P W q B t r x|) := by
    have h1 := rf_tr_tendsto_val hW hq hm hB hr hD ht x
    have h2 := rf_cN_tendsto hμ2 hm2 hm hr hD
    rw [hcen] at h2
    simpa using (h1.sub h2).abs
  refine le_of_tendsto hlim (hev.mono fun N hN => ?_)
  set rN : Euc d → ℝ := rfTr (N : ℝ) r with hrN
  set c : ℝ := ∫ y, rN y ∂μ with hc
  have hN0 : 0 < (N : ℝ) := by linarith [hN.2]
  have hrNc : ContDiff ℝ (m : WithTop ℕ∞) rN := rf_tr_contDiff hr
  have hrN2 : ContDiff ℝ 2 rN := hrNc.of_le (by exact_mod_cast hm)
  have hg2 : ContDiff ℝ 2 (fun y => rN y - c) := hrN2.sub contDiff_const
  have hDN : ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ y, ‖iteratedFDeriv ℝ i rN y‖ ≤ K * D :=
    fun i h1 h2 y => hK hr hD0 hN.2 hN.1 hD i h1 h2 y
  have hM1 : ∀ y, ‖fderiv ℝ (fun y => rN y - c) y‖ ≤ K * D := by
    intro y
    rw [fderiv_sub_const]
    have := hDN 1 le_rfl (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 (fun y => rN y - c) y‖ ≤ K * D := by
    intro y
    rw [rf_iter_sub_const hrN2 (by norm_num)]
    exact hDN 2 (by norm_num) hm y
  have hM0 : ∀ y, ‖rN y - c‖ ≤ 2 * (N : ℝ) + |c| := by
    intro y
    rw [Real.norm_eq_abs]
    have := rf_tr_abs_le_two hN0 r y
    have h2 := abs_sub (rN y) c
    simp only [hrN] at h2 ⊢
    linarith
  have hrNi : Integrable rN μ :=
    Integrable.of_bound hrNc.continuous.aestronglyMeasurable (2 * (N : ℝ)) (Eventually.of_forall
      fun y => by rw [Real.norm_eq_abs]; exact rf_tr_abs_le_two hN0 r y)
  have hcen' : ∫ y, (rN y - c) ∂μ = 0 := by
    rw [integral_sub hrNi (integrable_const c)]; simp [hc]
  have hinv := (HRS.MS.PoisInv.pois_inv hq hm hB hW hμ hμ2 hg2 hM1 hM2).2 t ht
  have hdec := pois_centered_decay hq hm hB hW hg2 hM0 hM1 hM2 μ hμ2 hm2 hcen' ht hinv.2.2 x
  have hint : ∀ y, Integrable (fun o => rN (flowMap q B (fun s => W s o) t y)) P := by
    intro y
    refine Integrable.of_bound ?_ (2 * (N : ℝ)) (Eventually.of_forall fun o => ?_)
    · have h1 := (sg_measurable_flowMap hn hq.le (by omega : 1 ≤ m) hB ht).comp
        (measurable_id.prodMk (measurable_const (a := y)))
      exact (hrNc.continuous.measurable.comp h1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact rf_tr_abs_le_two hN0 r _
  rw [rf_sg_sub_const hint c x] at hdec
  have := (le_min_iff.1 hdec).2
  calc _ ≤ _ := this
    _ = _ := by ring

end Sg

end HRS.MS.PoisRes
