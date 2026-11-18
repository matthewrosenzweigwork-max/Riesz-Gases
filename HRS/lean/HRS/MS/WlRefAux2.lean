import HRS.MS.WlRefAux1

/-!
# HRS.MS.WlRefAux2 -- calibrated reference marginal for S3.5, part 2: insertion defect, cavity total variation,
Minkowski bounds for the tail kernel (WL-9b, first half)

Packet WL-9b of `docs/WR_LOG_PLAN.md` (Step 11 of the proof of `r2_log_static`).  Infrastructure lemmas, not
manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl9_`.  Port of `WrRefMargAux2`
(`wr13e_cavD`, `wr13e_event_pi_nu`, `wr13e_cv_L2`) to the field ensembles `fieldLaw V ψ λ n` with a weak pair kernel
`q` (here `q = q_M`) and an arbitrary one-body field `ψ` with `IsField μ ψ M M₁` (here `ψ = ψ_R`).

* `wl9_defect_abs`: abstract exponential-family bound `0 ≤ cgf X P 1 - P[X] ≤ W` from a variance bound along the
  tilts (`EF.ef_main`, `EF.ef_cgf_ge`); no derivative is taken, so there is no junk value of `derivWithin`.
* `wl9_pole_evar`, `wl9_pole_var`: the pole ensemble `P^{x,t} = fieldLaw V (ψ - tλ q(·,x)) λ n` has
  `Var(∑ q(Y_k, x)) ≤ 2 n e^{M+Λ} ∫ q(y,x)² dμ(y)` (`wl5_resampling_w`, Wu's inequality with the weight `0`).
* `wl9_defect`: `0 ≤ D(x) = A_x(1) - E_{P_n^0} X_x ≤ (β/N)² 2 n e^{M_f + M_{1f} + 1} C₂` (so `≤ C/N`), TeX
  `eq:r2-log-resampling` for `q_M` (`q_M² ≤ K²`).
* `wl9_cavity_tv`: `|π(S) - ν(S)| ≤ wlPinC/N` for the first marginals `π, ν` of the ensembles with `n+1` and `n`
  particles and the SAME field (`wl_pin_tv_removed` with no pins): the cavity total variation with the calibration
  field held fixed.
* `wl9_conv_L2`, `wl9_cv_L2`: `‖q w‖_{L²(μ)} ≤ C ‖w‖_{L¹(μ)}` and `‖q(P - Q)‖_{L²(μ)} ≤ 2 C tv(P,Q)` for every
  measurable symmetric kernel `0 ≤ q ≤ K` (the analogue of `eq:r2-log-TV-convolution` for `q_M`; copies of
  `wl8_conv_L2`, `wl8_cv_L2` with `K` replaced by `q`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

/-! ### Abstract defect bound -/

section Abs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

/-- `0 ≤ cgf X P 1 - P[X] ≤ W` for `X ≤ 0` integrable, if `Var[X; P.tilted (t X)] ≤ W` for `t ∈ (0,1]`. -/
lemma wl9_defect_abs (hXm : Measurable X) (hb : ∀ ω, X ω ≤ 0) (hXi : Integrable X P) {W : ℝ}
    (hW : 0 ≤ W) (hvar : ∀ t ∈ Set.Ioc (0 : ℝ) 1, Var[X; P.tilted (fun ω => t * X ω)] ≤ W) :
    0 ≤ cgf X P 1 - ∫ ω, X ω ∂P ∧ cgf X P 1 - ∫ ω, X ω ∂P ≤ W := by
  have hw : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Var[X; P.tilted (fun ω => t * X ω)]) ≤
      (fun _ : ℝ => ENNReal.ofReal W) t := fun t ht => ENNReal.ofReal_le_ofReal (hvar t ht)
  have hWfin : ∫⁻ _t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal W ≠ ∞ := by simp
  obtain ⟨h1, -⟩ := HRS.MarginalAux.EF.ef_main hXm hb hXi (fun _ => ENNReal.ofReal W) hw hWfin
  have hint : (∫⁻ _t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal W).toReal = W := by simp [hW]
  rw [hint] at h1
  have hge := HRS.MarginalAux.EF.ef_cgf_ge hXm hb hXi
  exact ⟨by linarith, h1⟩

end Abs

/-! ### The pole ensembles of a field ensemble -/

section Pole

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma wl9_hrow_of {V : WeakPotential μ} (hV : V.q = q) (hq : EWeakKernel μ a q) (ha : 0 ≤ a) :
    ∀ x, ∫ y, V.q x y ∂μ ≤ a := fun x => by rw [hV]; exact hq.wr1_rowInt_le ha x

lemma wl9_measurable_q_left (V : WeakPotential μ) (x : E) : Measurable (fun y => V.q y x) :=
  V.measurable_q.comp (measurable_id.prodMk measurable_const)

/-- **Wu's inequality for the pole ensemble**: `Var(∑ q(Y_k, x)) ≤ 2 n e^{M_f + M_{1f} + β a} ∫ q(y,x)² dμ(y)`
under `P^{x,t}_n = fieldLaw V (ψ - tλ q(·,x)) λ n`, `λ = β/N`, `t ∈ [0,1]`, `n ≤ N`, Dobrushin smallness `hs`. -/
lemma wl9_pole_evar (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {ψ : E → ℝ} {M M₁ : ℝ} (hψ : IsField μ ψ M M₁)
    {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N) (hn : n ≤ N) [NeZero n] (V : WeakPotential μ)
    (hV : V.q = q) {Mf M1f : ℝ} (hMf : M ≤ Mf) (hM1f : M₁ + β / N * a ≤ M1f)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1)))) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : E) :
    evariance (fun Y : Fin n → E => ∑ i, V.q (Y i) x)
        (wl6_law μ V.q (wl6_pole V.q ψ (t * (β / N)) x) (β / N) n) ≤
      2 * n * (ENNReal.ofReal (Real.exp (Mf + (M1f + β * a))) * ∫⁻ y, ‖V.q y x‖ₑ ^ 2 ∂μ) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hc : 0 ≤ t * (β / N) := mul_nonneg ht0 hlam
  have hrow := wl9_hrow_of hV hq ha
  have hφ := wl6_isField_pole V hψ hc hrow x
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlaa : t * (β / N) * a ≤ β / N * a := mul_le_mul_of_nonneg_right
    (by nlinarith [div_nonneg hβ hNpos.le]) ha
  have hs' : β * a ≤ min 1 (1 / (16 * Real.exp (M + (M₁ + t * (β / N) * a) + 1))) := by
    refine le_min (hs.trans (min_le_left _ _)) (hs.trans ((min_le_right _ _).trans ?_))
    refine one_div_le_one_div_of_le (by positivity) ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    linarith
  have hκ := (wl_kappa_lt_half hq ha hφ hβ hs').le
  have hfm := wl9_measurable_q_left V x
  have hΛ : M₁ + t * (β / N) * a + β / N * n * a ≤ M1f + β * a := by
    have h1 : β / N * (n : ℝ) ≤ β := by
      have : (n : ℝ) ≤ N := by exact_mod_cast hn
      calc β / N * n ≤ β / N * N := by gcongr
        _ = β := by field_simp
    have h2 : β / N * n * a ≤ β * a := mul_le_mul_of_nonneg_right h1 ha
    linarith
  have h := wl5_resampling_w hq ha hφ hβ hN0 hn hκ V hV (M₀ := M) (w := fun _ => (0 : ℝ))
    (fun z => by simpa using hφ.le z) hΛ (fun y => V.q y x) hfm
  refine h.trans ?_
  simp only [neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  refine mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl)
  linarith

/-- The variance of the pole exponent `X_x = -λ ∑ q(Y_k, x)` under `P^{x,t}`. -/
lemma wl9_pole_var (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {ψ : E → ℝ} {M M₁ : ℝ} (hψ : IsField μ ψ M M₁)
    {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N) (hn : n ≤ N) [NeZero n] (V : WeakPotential μ)
    (hV : V.q = q) {Mf M1f : ℝ} (hMf : M ≤ Mf) (hM1f : M₁ + β / N * a ≤ M1f)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1)))) {C2 : ℝ} (hC2 : 0 ≤ C2)
    (hq2 : ∀ x, ∫⁻ y, ‖V.q y x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : E) :
    Var[wl7_poleExp V.q (β / N) x (n := n); wl6_law μ V.q (wl6_pole V.q ψ (t * (β / N)) x) (β / N) n] ≤
      (β / N) ^ 2 * (2 * n * (Real.exp (Mf + (M1f + β * a)) * C2)) := by
  have hev := wl9_pole_evar hq ha hψ hβ hN0 hn V hV hMf hM1f hs ht0 ht1 x
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set P := wl6_law μ V.q (wl6_pole V.q ψ (t * (β / N)) x) (β / N) n with hP
  have hvar : Var[wl7_poleExp V.q (β / N) x (n := n); P] =
      (β / N) ^ 2 * (evariance (fun Y : Fin n → E => ∑ i, V.q (Y i) x) P).toReal := by
    have := variance_const_mul (-(β / N)) (fun Y : Fin n → E => ∑ i, V.q (Y i) x) P
    rw [neg_sq] at this
    exact this
  rw [hvar]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hE : ENNReal.ofReal (Real.exp (Mf + (M1f + β * a))) * ∫⁻ y, ‖V.q y x‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal (Real.exp (Mf + (M1f + β * a)) * C2) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul' le_rfl (hq2 x)
  have hb : evariance (fun Y : Fin n → E => ∑ i, V.q (Y i) x) P ≤
      ENNReal.ofReal (2 * n * (Real.exp (Mf + (M1f + β * a)) * C2)) := by
    refine hev.trans ?_
    have : ENNReal.ofReal (2 * (n : ℝ) * (Real.exp (Mf + (M1f + β * a)) * C2)) =
        2 * (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Mf + (M1f + β * a)) * C2) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      simp
    rw [this]
    exact mul_le_mul' le_rfl hE
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans
    (by rw [ENNReal.toReal_ofReal (by positivity)])

/-- **The insertion defect is `O(1/N)`** (TeX `eq:r2-log-resampling` for `q_M`): for the field ensemble with
`n = m + 1` cavity particles, `n ≤ N`, `0 ≤ D(x) ≤ (β/N)² 2 n e^{M_f + M_{1f} + β a} C₂`. -/
theorem wl9_defect (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {ψ : E → ℝ} {M M₁ : ℝ} (hψ : IsField μ ψ M M₁)
    {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN0 : 0 < N) (m : ℕ) (hn : m + 1 ≤ N) (V : WeakPotential μ)
    (hV : V.q = q) {Mf M1f : ℝ} (hMf : M ≤ Mf) (hM1f : M₁ + β / N * a ≤ M1f)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1)))) {C2 : ℝ} (hC2 : 0 ≤ C2)
    (hq2 : ∀ x, ∫⁻ y, ‖V.q y x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C2) (x : E) :
    0 ≤ wl9_D μ V.q ψ (β / N) (m + 1) x ∧ wl9_D μ V.q ψ (β / N) (m + 1) x ≤
      (β / N) ^ 2 * (2 * ((m + 1 : ℕ) : ℝ) * (Real.exp (Mf + (M1f + β * a)) * C2)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hrow := wl9_hrow_of hV hq ha
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  haveI : IsProbabilityMeasure (wl6_law μ V.q ψ (β / N) (m + 1)) :=
    (fieldSpec (V := V) hψ hlam (m + 1)).isProb
  have hXm := wl7_poleExp_measurable V (β / N) x (m + 1)
  have hb := wl7_poleExp_le_zero V hlam x (n := m + 1)
  have hfm := wl9_measurable_q_left V x
  have hfi : Integrable (fun y : E => V.q y x) μ :=
    (V.integrable_q x).congr (Filter.Eventually.of_forall fun y => V.q_symm x y)
  have hXi : Integrable (wl7_poleExp V.q (β / N) x (n := m + 1)) (wl6_law μ V.q ψ (β / N) (m + 1)) := by
    refine (integrable_finsetSum _ fun j _ => ?_).const_mul _
    exact wl7_integrable_coord V hψ hlam hrow m hfm hfi j
  have hW : 0 ≤ (β / N) ^ 2 * (2 * ((m + 1 : ℕ) : ℝ) * (Real.exp (Mf + (M1f + β * a)) * C2)) := by positivity
  have hvar : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Var[wl7_poleExp V.q (β / N) x (n := m + 1);
        (wl6_law μ V.q ψ (β / N) (m + 1)).tilted (fun ω => t * wl7_poleExp V.q (β / N) x ω)] ≤
        (β / N) ^ 2 * (2 * ((m + 1 : ℕ) : ℝ) * (Real.exp (Mf + (M1f + β * a)) * C2)) := by
    intro t ht
    have hc : 0 ≤ t * (β / N) := mul_nonneg ht.1.le hlam
    have h1 := wl7_pole_eq_tilted V hψ hlam hrow hc (m + 1) x
    have hfun : (fun ω : Fin (m + 1) → E => t * wl7_poleExp V.q (β / N) x ω) =
        wl7_poleExp V.q (t * (β / N)) x := by
      funext Y; unfold wl7_poleExp; ring
    rw [hfun, ← h1]
    exact wl9_pole_var hq ha hψ hβ hN0 hn V hV hMf hM1f hs hC2 hq2 ht.1.le ht.2 x
  exact wl9_defect_abs hXm hb hXi hW hvar

/-- **Cavity total variation with the field held fixed**: for the first marginals `π` of the ensemble with `m + 2`
particles and `ν` of the ensemble with `m + 1` particles (same field `ψ`, `N = m + 2`),
`|π(S) - ν(S)| ≤ wlPinC/N`. -/
theorem wl9_cavity_tv (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {ψ : E → ℝ} {M M₁ : ℝ} (hψ : IsField μ ψ M M₁)
    {β : ℝ} (hβ : 0 ≤ β) (V : WeakPotential μ) (hV : V.q = q) (m : ℕ)
    (hs : β * a ≤ min 1 (1 / (16 * Real.exp (M + M₁ + 1)))) {S : Set E} (hS : MeasurableSet S) :
    |((fieldLaw V ψ (β / ((m + 2 : ℕ) : ℝ)) (m + 2)).map (fun Y => Y 0)).real S -
        ((fieldLaw V ψ (β / ((m + 2 : ℕ) : ℝ)) (m + 1)).map (fun Y => Y 0)).real S| ≤
      wlPinC a M M₁ β / ((m + 2 : ℕ) : ℝ) := by
  have h := wl_pin_tv_removed (B := Empty) hq ha hψ hβ (N := m + 2) (n := m + 1) (Nat.succ_pos _)
    (by simp) (fun e : Empty => e.elim) hs (Fin.last (m + 1)) ⟨0, Nat.succ_pos m⟩ hS
  rw [wl5_pinnedLaw_empty, wl5_pinnedLaw_empty] at h
  have e : (Fin.last (m + 1)).succAbove (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = (0 : Fin (m + 2)) := by
    ext; simp [Fin.succAbove, Fin.lt_def]
  rw [e] at h
  have e1 : fieldLaw (wlPot hq ha hψ) (wlPot hq ha hψ).φ (β / ((m + 2 : ℕ) : ℝ)) (m + 2) =
      fieldLaw V ψ (β / ((m + 2 : ℕ) : ℝ)) (m + 2) :=
    wl5_fieldLaw_congr_q (by rw [hV]; rfl) ψ _ _
  have e2 : fieldLaw (wlPot hq ha hψ) (wlPot hq ha hψ).φ (β / ((m + 2 : ℕ) : ℝ)) (m + 1) =
      fieldLaw V ψ (β / ((m + 2 : ℕ) : ℝ)) (m + 1) :=
    wl5_fieldLaw_congr_q (by rw [hV]; rfl) ψ _ _
  rw [e1, e2] at h
  exact h

end Pole

/-! ### Minkowski bounds for a kernel dominated by `K` -/

section Conv

variable {d : ℕ}

/-- **`‖q w‖_{L²(μ)} ≤ C ‖w‖_{L¹(μ)}`** for every measurable symmetric kernel `0 ≤ q ≤ K` (copy of `wl8_conv_L2`
with `K` replaced by `q`; `C` depends on `d, A` only). -/
theorem wl9_conv_L2 (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ qq : Euc d → Euc d → ℝ,
      Measurable (fun p : Euc d × Euc d => qq p.1 p.2) → (∀ x y, qq x y = qq y x) → (∀ x y, 0 ≤ qq x y) →
      (∀ x y, qq x y ≤ sphericalLogKernel x y) → ∀ w : Euc d → ℝ, Measurable w →
      Integrable w (HRS.Whole.withDensityReal ρ) →
      Measurable (fun x => ∫ y, qq x y * w y ∂(HRS.Whole.withDensityReal ρ)) ∧
      eLpNorm (fun x => ∫ y, qq x y * w y ∂(HRS.Whole.withDensityReal ρ)) 2 (HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C * ∫ y, |w y| ∂(HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨C2, hC20, hC2⟩ := wl_row_pow hd A 2
  refine ⟨Real.sqrt C2, Real.sqrt_nonneg _, fun ρ hρ hA qq hqm hqs hq0 hqK w hwm hwi => ?_⟩
  have := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hFm : Measurable fun x : Euc d => ∫ y, qq x y * w y ∂μ :=
    RefMarg.measurable_integral_kernel
      (F := fun p : Euc d × Euc d => qq p.1 p.2 * w p.2) (hqm.mul (hwm.comp measurable_snd))
  refine ⟨hFm, ?_⟩
  set m : ℝ := ∫ y, |w y| ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => abs_nonneg _
  set G : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |w y| with hGdef
  have hG : Measurable G := hwm.abs.ennreal_ofReal
  have hGint : ∫⁻ y, G y ∂μ = ENNReal.ofReal m :=
    (ofReal_integral_eq_lintegral_ofReal hwi.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  set h : Euc d → Euc d → ℝ≥0∞ := fun x y => ENNReal.ofReal (qq x y) with hh
  have hhm : Measurable (fun p : Euc d × Euc d => h p.1 p.2) := hqm.ennreal_ofReal
  have hrow : ∀ x, ∫⁻ y, h x y ^ 2 ∂μ ≤ ENNReal.ofReal C2 := by
    intro x
    obtain ⟨hi, hle⟩ := hC2 ρ hρ hA x
    calc ∫⁻ y, h x y ^ 2 ∂μ ≤ ∫⁻ y, ENNReal.ofReal (sphericalLogKernel x y ^ 2) ∂μ :=
          lintegral_mono fun y => by
            simp only [hh]
            rw [← ENNReal.ofReal_pow (hq0 x y)]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq0 x y) (hqK x y) 2)
      _ = ENNReal.ofReal (∫ y, sphericalLogKernel x y ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hle
  have hmk := wl8_minkowski_lintegral (μ := μ) hhm (fun x y => by simp only [hh]; rw [hqs]) hrow hG
  have hpt : ∀ x, ‖∫ y, qq x y * w y ∂μ‖ₑ ≤ ∫⁻ y, h x y * G y ∂μ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
    simp only [hh, hGdef]
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hq0 x y), ENNReal.ofReal_mul (hq0 x y)]
  have hs0 : 0 ≤ Real.sqrt C2 * m := mul_nonneg (Real.sqrt_nonneg _) hm0
  refine wl8_eLpNorm_two_le hFm.aestronglyMeasurable ?_
  calc ∫⁻ x, ‖∫ y, qq x y * w y ∂μ‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, (∫⁻ y, h x y * G y ∂μ) ^ 2 ∂μ :=
        lintegral_mono fun x => pow_le_pow_left' (hpt x) 2
    _ ≤ ENNReal.ofReal C2 * (∫⁻ y, G y ∂μ) ^ 2 := hmk
    _ = ENNReal.ofReal (Real.sqrt C2 * m) ^ 2 := by
        rw [hGint, ← ENNReal.ofReal_pow hm0, ← ENNReal.ofReal_pow hs0, ← ENNReal.ofReal_mul hC20,
          mul_pow, Real.sq_sqrt hC20]

/-- **`‖q(P - Q)‖_{L²(μ)} ≤ 2 C tv(P,Q)`** for probability measures `P, Q ≤ Cb μ` and a measurable symmetric kernel
`0 ≤ q ≤ K` (copy of `wl8_cv_L2`; `C` depends on `d, A` only, not on `Cb`, `q`). -/
theorem wl9_cv_L2 (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ qq : Euc d → Euc d → ℝ,
      Measurable (fun p : Euc d × Euc d => qq p.1 p.2) → (∀ x y, qq x y = qq y x) → (∀ x y, 0 ≤ qq x y) →
      (∀ x y, qq x y ≤ sphericalLogKernel x y) → ∀ Cb : ℝ, 0 ≤ Cb →
      ∀ P Q : Measure (Euc d), IsProbabilityMeasure P → IsProbabilityMeasure Q →
        P ≤ ENNReal.ofReal Cb • HRS.Whole.withDensityReal ρ →
        Q ≤ ENNReal.ofReal Cb • HRS.Whole.withDensityReal ρ → ∀ ε : ℝ, tvDist P Q ≤ ε →
          Measurable (fun x => ∫ y, qq x y ∂P - ∫ y, qq x y ∂Q) ∧
          eLpNorm (fun x => ∫ y, qq x y ∂P - ∫ y, qq x y ∂Q) 2 (HRS.Whole.withDensityReal ρ) ≤
            ENNReal.ofReal (C * (2 * ε)) := by
  obtain ⟨C, hC0, hC⟩ := wl9_conv_L2 hd A
  obtain ⟨C1, hC10, hC1⟩ := wl8_K_row_integrable hd A
  refine ⟨C, hC0, fun ρ hρ hA qq hqm hqs hq0 hqK Cb hCb P Q hP hQ hPle hQle ε hε => ?_⟩
  have := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hpm, hp0, hpi, hPeq, hPint⟩ := wl8_density_of_le hPle
  obtain ⟨hqm', hq0', hqi, hQeq, hQint⟩ := wl8_density_of_le hQle
  set p : Euc d → ℝ := fun y => (P.rnDeriv μ y).toReal with hp
  set q : Euc d → ℝ := fun y => (Q.rnDeriv μ y).toReal with hq
  set w : Euc d → ℝ := fun y => p y - q y with hw
  have hwm : Measurable w := hpm.sub hqm'
  have hwi : Integrable w μ := hpi.sub hqi
  have hqx : ∀ x, Measurable (qq x) := fun x => Measurable.of_uncurry_left (f := qq) hqm
  have hqint : ∀ x, Integrable (qq x) μ := fun x =>
    (hC1 ρ hρ hA x).1.mono' (hqx x).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 x y)]; exact hqK x y)
  have hid : ∀ x, ∫ y, qq x y ∂P - ∫ y, qq x y ∂Q = ∫ y, qq x y * w y ∂μ := by
    intro x
    obtain ⟨h1, e1⟩ := hPint (hqint x)
    obtain ⟨h2, e2⟩ := hQint (hqint x)
    rw [e1, e2, ← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hw, hp, hq]
    ring
  have hfun : (fun x => ∫ y, qq x y ∂P - ∫ y, qq x y ∂Q) = fun x => ∫ y, qq x y * w y ∂μ := funext hid
  obtain ⟨hmeas, hnorm⟩ := hC ρ hρ hA qq hqm hqs hq0 hqK w hwm hwi
  rw [hfun]
  refine ⟨hmeas, hnorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hbdd : BddAbove (Set.range fun E : {E : Set (Euc d) // MeasurableSet E} =>
      |(P E.1).toReal - (Q E.1).toReal|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨E, rfl⟩
    have h1 : (P E.1).toReal ≤ 1 := by
      have := prob_le_one (μ := P) (s := E.1)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h2 : (Q E.1).toReal ≤ 1 := by
      have := prob_le_one (μ := Q) (s := E.1)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    rw [abs_le]
    constructor <;> linarith [ENNReal.toReal_nonneg (a := P E.1), ENNReal.toReal_nonneg (a := Q E.1)]
  have hset : ∀ A' : Set (Euc d), MeasurableSet A' → |P.real A' - Q.real A'| ≤ ε := by
    intro A' hA'
    refine le_trans ?_ hε
    unfold tvDist
    exact le_ciSup hbdd (⟨A', hA'⟩ : {E : Set (Euc d) // MeasurableSet E})
  have hint : ∫ y, |p y - q y| ∂μ ≤ 2 * ε := by
    refine RefMarg.integral_abs_sub_le hpm hqm' hp0 hq0' hpi hqi (fun A' hA' => ?_)
    rw [← hPeq, ← hQeq]
    exact hset A' hA'
  have : ∫ y, |w y| ∂μ ≤ 2 * ε := hint
  exact mul_le_mul_of_nonneg_left this hC0

end Conv

end HRS.MS.Wl
