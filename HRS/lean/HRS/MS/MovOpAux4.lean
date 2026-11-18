import HRS.MS.MovOpAux1
import HRS.MS.MovForceTie
import HRS.MS.ThCorrSob
import HRS.MS.MovOscAux9

/-!
# MOV-C2 (1): Sobolev bookkeeping, `B1` for bounded multipliers, weights

Namespace `HRS.MS.MovC2`, helper prefix `movc2_`.  Infrastructure for S6.1 (`docs/MOV_PLAN.md`, step 10); not
manuscript rows.  **Depends on the MOV-C1 file `MovOpAux1`** (merged before this file): Gaussian class `MovcG`,
`movc1_sob_sup`, `movc1_sob_mono_norm`, triangle inequality in `Σ^m`.

* `movc2_SB t E u`: `u ∈ H^t`, `‖u‖_{H^t} ≤ E`; sums (Minkowski via `mova3b2_minkowski`), scalars, monotone in `t`.
* `movc2_B1`: `B1` for a multiplier of class `C_b^{⌈r⌉}` (not only Gaussian): `‖om v‖_{H^r} ≤ C A ‖v‖_{Σ^r}` on Schwartz `v`,
  `r ≥ 0` (duality with `mo_bridge2` at `N = 0`; the proof of `movc1_B1` with `A` in place of the Gaussian decay).
* `movc2_br`, `movc2_br_Q`: `(1+‖x‖²)^{-K}` as a decaying multiplier of order `2K` for `mo_bridge2`.
* `movc2_mon`, `movc2_WB`: monomial weights `x^w` (words) and weighted Sobolev bounds; `movc2_WB_Qpow` (`Q^K = (1+‖x‖²)^K`).
* `movc2_loc_wt`: **weighted local gain**: `x^w ((θ g) * u)` for `|w| ≤ n` (Leibniz for convolution, kernels `x^{w'}θ g` again
  of the form `θ' g`, `θ' ∈ C_c^∞`, then `tc3_riesz_loc_sobolev_gain`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC2

open HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0 HRS.MS.MovForce HRS.MS.MovC1 HRS.PDE.ToolboxRd
  HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-! ### Sobolev bookkeeping -/

/-- `u ∈ H^t` with `‖u‖_{H^t} ≤ E`. -/
def movc2_SB (t E : ℝ) (u : Euc d → ℝ) : Prop :=
  HRS.PDE.ToolboxRd.MemSobolev t u ∧ Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq t u) ≤ E

lemma movc2_SB_nonneg {t E : ℝ} {u : Euc d → ℝ} (h : movc2_SB t E u) : 0 ≤ E :=
  (Real.sqrt_nonneg _).trans h.2

lemma movc2_SB_mono_E {t E E' : ℝ} {u : Euc d → ℝ} (h : movc2_SB t E u) (hE : E ≤ E') :
    movc2_SB t E' u := ⟨h.1, h.2.trans hE⟩

lemma movc2_SB_add {t E1 E2 : ℝ} {u v : Euc d → ℝ} (hu : movc2_SB t E1 u) (hv : movc2_SB t E2 v) :
    movc2_SB t (E1 + E2) (fun x => u x + v x) := by
  have hF := aestronglyMeasurable_fourierL2 hu.1.1
  have hG := aestronglyMeasurable_fourierL2 hv.1.1
  obtain ⟨hI, hn⟩ := mova3b2_minkowski t hF hG hu.1.2 hv.1.2
  have hae := fourierL2_add hu.1.1 hv.1.1
  have hmem : MemLp (fun x => u x + v x) 2 volume := hu.1.1.add hv.1.1
  have hI' : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t *
      ‖fourierL2 (fun x => u x + v x) ξ‖ ^ 2) volume := by
    refine hI.congr ?_
    filter_upwards [hae] with ξ h
    rw [h]; rfl
  refine ⟨⟨hmem, hI'⟩, ?_⟩
  have e : HRS.PDE.ToolboxRd.sobolevNormSq t (fun x => u x + v x) = ∫ ξ, mova3b1_W ξ ^ t * ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ξ h
    rw [h]; rfl
  rw [e]
  exact hn.trans (add_le_add hu.2 hv.2)

lemma movc2_SB_zero (t : ℝ) : movc2_SB t 0 (fun _ : Euc d => (0 : ℝ)) := by
  have h0 : fourierL2 (fun _ : Euc d => (0 : ℝ)) =ᵐ[volume] fun _ => (0 : ℂ) := by
    have := fourierL2_smul (d := d) (MemLp.zero : MemLp (fun _ : Euc d => (0 : ℝ)) 2 volume) 0
    filter_upwards [this] with ξ h
    simpa using h
  have hI : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t *
      ‖fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ‖ ^ 2) volume := by
    refine (integrable_zero (Euc d) ℝ volume).congr ?_
    filter_upwards [h0] with ξ h
    rw [h]; simp
  refine ⟨⟨MemLp.zero, hI⟩, ?_⟩
  have e : HRS.PDE.ToolboxRd.sobolevNormSq t (fun _ : Euc d => (0 : ℝ)) = 0 := by
    have : HRS.PDE.ToolboxRd.sobolevNormSq t (fun _ : Euc d => (0 : ℝ)) =
        ∫ ξ : Euc d, (0 : ℝ) := by
      refine integral_congr_ae ?_
      filter_upwards [h0] with ξ h
      show mova3b1_W ξ ^ t * ‖fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ‖ ^ 2 = 0
      rw [h]; simp
    rw [this]; simp
  rw [e]; simp

lemma movc2_SB_sum {ι : Type*} (t : ℝ) (S : Finset ι) {u : ι → Euc d → ℝ} {E : ι → ℝ}
    (h : ∀ i ∈ S, movc2_SB t (E i) (u i)) :
    movc2_SB t (∑ i ∈ S, E i) (fun x => ∑ i ∈ S, u i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using movc2_SB_zero (d := d) t
  | insert a S ha ih =>
    have h1 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h2 := movc2_SB_add (h a (Finset.mem_insert_self _ _)) h1
    simpa [Finset.sum_insert ha] using h2

lemma movc2_SB_smul {t E : ℝ} (c : ℝ) {u : Euc d → ℝ} (hu : movc2_SB t E u) :
    movc2_SB t (|c| * E) (fun x => c * u x) := by
  have hae := fourierL2_smul hu.1.1 c
  have hmem : MemLp (fun x => c * u x) 2 volume := hu.1.1.const_mul c
  have hI : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t *
      ‖fourierL2 (fun x => c * u x) ξ‖ ^ 2) volume := by
    have := hu.1.2.const_mul (c ^ 2)
    refine this.congr ?_
    filter_upwards [hae] with ξ h
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  refine ⟨⟨hmem, hI⟩, ?_⟩
  have e : HRS.PDE.ToolboxRd.sobolevNormSq t (fun x => c * u x) =
      c ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq t u := by
    show ∫ ξ, mova3b1_W ξ ^ t * ‖fourierL2 (fun x => c * u x) ξ‖ ^ 2 =
      c ^ 2 * ∫ ξ, mova3b1_W ξ ^ t * ‖fourierL2 u ξ‖ ^ 2
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ξ h
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  exact mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)

lemma movc2_SB_mono_t {σ τ E : ℝ} (hστ : σ ≤ τ) {u : Euc d → ℝ} (hu : movc2_SB τ E u) :
    movc2_SB σ E u := by
  refine ⟨memSobolev_mono hστ hu.1, ?_⟩
  exact (Real.sqrt_le_sqrt (movc1_sob_mono_norm hστ hu.1)).trans hu.2

/-! ### `B1` for bounded multipliers (every real index `r ≥ 0`) -/

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- **`B1` for a `C_b^{⌈r⌉}` multiplier on Schwartz functions** (duality with `mo_bridge2`, `N = 0`, `-r ≤ 0`):
`‖om v‖_{H^r} ≤ C A ‖v‖_{Σ^r}` for `r ≥ 0`, `om` smooth of temperate growth with all coordinate partial derivatives of
order `≤ ⌈r⌉` bounded by `A` (`mova3b2_Q ⌈r⌉ 0 A om`). -/
theorem movc2_B1 {r : ℝ} (hr : 0 ≤ r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (om : Euc d → ℝ),
    om.HasTemperateGrowth → mova3b2_Q ⌈r⌉₊ 0 A om → ∀ v : 𝓢R,
      movc2_SB r (C * A * oscNorm r v) (fun x => om x * v x) := by
  obtain ⟨C2, hC2, hB2⟩ := mo_bridge2 (d := d) (-r) 0 (by simpa using hr)
  refine ⟨C2, hC2, fun A hA0 om htg hA v => ?_⟩
  have hA' : mova3b2_Q (max 0 ⌈-(-r)⌉₊) 0 A om := by
    rw [neg_neg, max_eq_right (Nat.zero_le _)]; exact hA
  set F : 𝓢R := SchwartzMap.smulLeftCLM ℝ om v with hF
  have hFe : (fun x => om x * v x) = ⇑F := by
    funext x; rw [hF, SchwartzMap.smulLeftCLM_apply_apply htg]; rfl
  rw [hFe]
  have hv : MemOsc r (⇑v) := memOsc_schwartz r v
  have hK : 0 ≤ C2 * A * oscNorm r v := mul_nonneg (mul_nonneg hC2 hA0) (Real.sqrt_nonneg _)
  refine movc1_sob_sup F r _ hK (fun φ => ?_)
  have hφ := movc1_memSob_schwartz φ (-r)
  obtain ⟨hm, hn⟩ := hB2 A hA0 om htg hA' (⇑φ) hφ
  have hv' : MemOsc (-(-r)) (⇑v) := by rw [neg_neg]; exact hv
  have hd := mo_dual_le (-r) hv' hm
  rw [neg_neg] at hd
  have hint : ∫ x, F x * φ x = ∫ x, v x * (om x * φ x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : F x = om x * v x := by rw [hF, SchwartzMap.smulLeftCLM_apply_apply htg]; rfl
    simp only [this]; ring
  rw [hint]
  calc |∫ x, v x * (om x * φ x)| ≤ oscNorm r (⇑v) * oscNorm (-r) (fun x => om x * φ x) := hd
    _ ≤ oscNorm r (⇑v) * (C2 * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (-r) (⇑φ))) :=
        mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
    _ = _ := by ring

/-! ### The multipliers `(1+‖x‖²)^{-K}` -/

/-- `x ↦ (1+‖x‖²)^r`. -/
def movc2_br (r : ℝ) (x : Euc d) : ℝ := (1 + ‖x‖ ^ 2) ^ r

lemma movc2_br_pos (r : ℝ) (x : Euc d) : 0 < movc2_br r x := by
  unfold movc2_br; positivity

lemma movc2_br_contDiff (r : ℝ) : ContDiff ℝ ∞ (movc2_br r : Euc d → ℝ) := by
  unfold movc2_br
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
    (fun x => (by positivity : (1 + ‖x‖ ^ 2) ≠ 0)))

lemma movc2_br_tg (r : ℝ) : (movc2_br r : Euc d → ℝ).HasTemperateGrowth :=
  Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euc d) r

lemma movc2_Dj_br (r : ℝ) (j : Fin d) (x : Euc d) :
    mova3b1_Dj j (movc2_br r) x = (2 * r) * (x j * movc2_br (r - 1) x) := by
  have h1 : HasFDerivAt (fun y : Euc d => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_add 1
  have hpos : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
  have h2 := h1.rpow_const (p := r) (Or.inl hpos)
  unfold mova3b1_Dj
  have e : (movc2_br r : Euc d → ℝ) = fun y => (1 + ‖y‖ ^ 2) ^ r := rfl
  rw [e, h2.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  have : inner ℝ x (EuclideanSpace.single j (1 : ℝ)) = x j := by
    simp [EuclideanSpace.inner_single_right]
  rw [this]
  unfold movc2_br
  have hr : (1 + ‖x‖ ^ 2) ^ (r - 1) * (1 + ‖x‖ ^ 2) = (1 + ‖x‖ ^ 2) ^ r := by
    rw [← Real.rpow_add_one hpos]; congr 1; ring
  ring

/-- Scalar multiples preserve the decay classes. -/
lemma movc2_Q_smul (c : ℝ) : ∀ {K m : ℕ} {A : ℝ} {b : Euc d → ℝ}, ContDiff ℝ ∞ b →
    mova3b2_Q K m A b → mova3b2_Q K m (|c| * A) (fun x => c * b x) := by
  intro K
  induction K with
  | zero =>
    intro m A b hb h x
    rw [abs_mul]
    calc |c| * |b x| * (1 + ‖x‖) ^ m = |c| * (|b x| * (1 + ‖x‖) ^ m) := by ring
      _ ≤ |c| * A := mul_le_mul_of_nonneg_left (h x) (abs_nonneg _)
  | succ K ih =>
    intro m A b hb h
    refine ⟨fun x => ?_, fun j => ?_⟩
    · rw [abs_mul]
      calc |c| * |b x| * (1 + ‖x‖) ^ m = |c| * (|b x| * (1 + ‖x‖) ^ m) := by ring
        _ ≤ |c| * A := mul_le_mul_of_nonneg_left (h.1 x) (abs_nonneg _)
    · have e : mova3b1_Dj j (fun x => c * b x) = fun x => c * mova3b1_Dj j b x := by
        funext x
        exact mova3b1_Dj_const_mul j c ((hb.differentiable (by simp)) x)
      rw [e]
      exact ih (mova3b2_contDiff_Dj j hb) (h.2 j)

lemma movc2_br_Q : ∀ (n : ℕ) (K m : ℕ), m ≤ 2 * K → ∃ A : ℝ, 0 ≤ A ∧
    mova3b2_Q n m A (movc2_br (-(K : ℝ)) : Euc d → ℝ) := by
  intro n
  induction n with
  | zero =>
    intro K m hm
    refine ⟨2 ^ K, by positivity, fun x => ?_⟩
    have hpos := movc2_br_pos (-(K : ℝ)) x
    rw [abs_of_pos hpos]
    unfold movc2_br
    have h1 : (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) ^ (2 * K) :=
      pow_le_pow_right₀ (by linarith [norm_nonneg x]) hm
    have h2 : (1 + ‖x‖) ^ (2 * K) ≤ 2 ^ K * (1 + ‖x‖ ^ 2) ^ K := by
      rw [pow_mul, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ K
      nlinarith [sq_nonneg (1 - ‖x‖)]
    have h3 : (1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) * (1 + ‖x‖ ^ 2) ^ K = 1 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]
    calc (1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) * (1 + ‖x‖) ^ m
        ≤ (1 + ‖x‖ ^ 2) ^ (-(K : ℝ)) * (2 ^ K * (1 + ‖x‖ ^ 2) ^ K) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = 2 ^ K := by rw [← mul_assoc, mul_comm _ ((2 : ℝ) ^ K), mul_assoc, h3]; ring
  | succ n ih =>
    intro K m hm
    obtain ⟨A0, hA0, hQ0⟩ := ih K m hm
    obtain ⟨A1, hA1, hQ1⟩ := ih (K + 1) (m + 1) (by omega)
    have hQx : ∀ j : Fin d, mova3b2_Q n m (|2 * (-(K : ℝ))| * (((n : ℝ) + 1) * A1))
        (mova3b1_Dj j (movc2_br (-(K : ℝ)))) := by
      intro j
      have e : mova3b1_Dj j (movc2_br (-(K : ℝ))) =
          fun x => (2 * (-(K : ℝ))) * (x j * movc2_br (-((K + 1 : ℕ) : ℝ)) x) := by
        funext x
        rw [movc2_Dj_br]
        congr 3
        push_cast; ring
      rw [e]
      have hx := mova3b2_Q_xmul j hA1 (movc2_br_contDiff _) hQ1
      exact movc2_Q_smul _ ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.mul (movc2_br_contDiff _)) hx
    refine ⟨max A0 (|2 * (-(K : ℝ))| * (((n : ℝ) + 1) * A1)), le_max_of_le_left hA0, ?_, fun j => ?_⟩
    · exact fun x => (mova3b2_Q_top hQ0 x).trans (le_max_left _ _)
    · exact mova3b2_Q_mono_A (le_max_right _ _) (hQx j)

/-! ### Monomial weights -/

/-- The monomial `x_{j₁} ⋯ x_{j_k}` attached to a word. -/
def movc2_mon : List (Fin d) → Euc d → ℝ
  | [], _ => 1
  | j :: w, x => x j * movc2_mon w x

lemma movc2_mon_nil (x : Euc d) : movc2_mon ([] : List (Fin d)) x = 1 := rfl

lemma movc2_mon_cons (j : Fin d) (w : List (Fin d)) (x : Euc d) :
    movc2_mon (j :: w) x = x j * movc2_mon w x := rfl

/-- `u` has weighted Sobolev bounds `‖x^w u‖_{H^t} ≤ E` for all words `w` of length `≤ n`. -/
def movc2_WB (n : ℕ) (t E : ℝ) (u : Euc d → ℝ) : Prop :=
  ∀ w : List (Fin d), w.length ≤ n → movc2_SB t E (fun x => movc2_mon w x * u x)

lemma movc2_WB_zero {t E : ℝ} {u : Euc d → ℝ} (h : movc2_WB 0 t E u) : movc2_SB t E u := by
  have := h [] (by simp)
  simpa [movc2_mon_nil] using this

lemma movc2_WB_of_SB {t E : ℝ} {u : Euc d → ℝ} (h : movc2_SB t E u) : movc2_WB 0 t E u := by
  intro w hw
  have : w = [] := List.length_eq_zero_iff.1 (by omega)
  subst this
  simpa [movc2_mon_nil] using h

lemma movc2_WB_mono_n {n n' : ℕ} (hn : n' ≤ n) {t E : ℝ} {u : Euc d → ℝ} (h : movc2_WB n t E u) :
    movc2_WB n' t E u := fun w hw => h w (hw.trans hn)

lemma movc2_WB_mono_t {σ τ E : ℝ} (hστ : σ ≤ τ) {n : ℕ} {u : Euc d → ℝ} (h : movc2_WB n τ E u) :
    movc2_WB n σ E u := fun w hw => movc2_SB_mono_t hστ (h w hw)

lemma movc2_WB_mono_E {n : ℕ} {t E E' : ℝ} (hE : E ≤ E') {u : Euc d → ℝ} (h : movc2_WB n t E u) :
    movc2_WB n t E' u := fun w hw => movc2_SB_mono_E (h w hw) hE

/-- Shifting a weight onto the function. -/
lemma movc2_WB_shift {n : ℕ} {t E : ℝ} {u : Euc d → ℝ} (h : movc2_WB (n + 1) t E u) (j : Fin d) :
    movc2_WB n t E (fun x => x j * u x) := by
  intro w hw
  have := h (j :: w) (by simp; omega)
  refine (show (fun x => movc2_mon w x * (x j * u x)) = fun x => movc2_mon (j :: w) x * u x from ?_) ▸ this
  funext x; rw [movc2_mon_cons]; ring

lemma movc2_WB_add {n : ℕ} {t E1 E2 : ℝ} {u v : Euc d → ℝ} (hu : movc2_WB n t E1 u)
    (hv : movc2_WB n t E2 v) : movc2_WB n t (E1 + E2) (fun x => u x + v x) := by
  intro w hw
  have := movc2_SB_add (hu w hw) (hv w hw)
  refine (show (fun x => movc2_mon w x * u x + movc2_mon w x * v x) =
    fun x => movc2_mon w x * (u x + v x) from ?_) ▸ this
  funext x; ring

/-- `Q = 1 + ‖x‖²` raises the weight by two. -/
lemma movc2_WB_Q {n : ℕ} {t E : ℝ} {u : Euc d → ℝ} (h : movc2_WB (n + 2) t E u) :
    movc2_WB n t (((d : ℝ) + 1) * E) (fun x => (1 + ‖x‖ ^ 2) * u x) := by
  intro w hw
  have hE : 0 ≤ E := movc2_SB_nonneg (h [] (by simp))
  have h1 : movc2_WB n t E u := movc2_WB_mono_n (by omega) h
  have h2 : ∀ j : Fin d, movc2_WB n t E (fun x => x j * (x j * u x)) := fun j =>
    movc2_WB_shift (movc2_WB_shift h j : movc2_WB (n + 1) t E (fun x => x j * u x)) j
  have hs := movc2_SB_add (h1 w hw) (movc2_SB_sum t (Finset.univ : Finset (Fin d))
    (u := fun j x => movc2_mon w x * (x j * (x j * u x))) (E := fun _ => E) (fun j _ => h2 j w hw))
  have e : (fun x => movc2_mon w x * u x + ∑ j : Fin d, movc2_mon w x * (x j * (x j * u x))) =
      fun x => movc2_mon w x * ((1 + ‖x‖ ^ 2) * u x) := by
    funext x
    rw [← Finset.mul_sum]
    have : ∑ j : Fin d, x j * (x j * u x) = ‖x‖ ^ 2 * u x := by
      rw [EuclideanSpace.norm_sq_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Real.norm_eq_abs, sq_abs]; ring
    rw [← mul_add, this]; ring
  rw [e] at hs
  refine movc2_SB_mono_E hs ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

lemma movc2_WB_Qpow (K : ℕ) : ∀ {n : ℕ} {t E : ℝ} {u : Euc d → ℝ}, movc2_WB (n + 2 * K) t E u →
    movc2_WB n t (((d : ℝ) + 1) ^ K * E) (fun x => (1 + ‖x‖ ^ 2) ^ K * u x) := by
  induction K with
  | zero =>
    intro n t E u h
    simpa using h
  | succ K ih =>
    intro n t E u h
    have h1 : movc2_WB (n + 2 * K + 2) t E u := by
      have : n + 2 * (K + 1) = n + 2 * K + 2 := by ring
      rwa [this] at h
    have h2 := movc2_WB_Q h1
    have h3 := ih h2
    refine (show (fun x => (1 + ‖x‖ ^ 2) ^ K * ((1 + ‖x‖ ^ 2) * u x)) =
      fun x => (1 + ‖x‖ ^ 2) ^ (K + 1) * u x from ?_) ▸ ?_
    · funext x; ring
    · refine movc2_WB_mono_E (le_of_eq ?_) h3
      ring

/-! ### Weights and the local kernel -/

/-- `u` and its weights up to length `n` are continuous and bounded. -/
def movc2_Reg (n : ℕ) (u : Euc d → ℝ) : Prop :=
  ∀ w : List (Fin d), w.length ≤ n →
    Continuous (fun x => movc2_mon w x * u x) ∧ ∃ B : ℝ, ∀ x, |movc2_mon w x * u x| ≤ B

lemma movc2_Reg_mono {n n' : ℕ} (hn : n' ≤ n) {u : Euc d → ℝ} (h : movc2_Reg n u) : movc2_Reg n' u :=
  fun w hw => h w (hw.trans hn)

lemma movc2_Reg_shift {n : ℕ} {u : Euc d → ℝ} (h : movc2_Reg (n + 1) u) (j : Fin d) :
    movc2_Reg n (fun x => x j * u x) := by
  intro w hw
  obtain ⟨h1, B, hB⟩ := h (j :: w) (by simp; omega)
  have e : ∀ x, movc2_mon w x * (x j * u x) = movc2_mon (j :: w) x * u x := fun x => by
    rw [movc2_mon_cons]; ring
  exact ⟨by simp only [e]; exact h1, B, fun x => by simp only [e]; exact hB x⟩

/-- Leibniz rule for a weight and a convolution. -/
lemma movc2_xmul_conv (j : Fin d) {k u : Euc d → ℝ} (hk : Integrable k volume)
    (hk' : Integrable (fun z => z j * k z) volume) (hu : Continuous u) (hB : ∃ B : ℝ, ∀ y, |u y| ≤ B)
    (hu' : Continuous (fun y => y j * u y)) (hB' : ∃ B : ℝ, ∀ y, |y j * u y| ≤ B) (x : Euc d) :
    x j * HRS.Whole.convFun k u x = HRS.Whole.convFun (fun z => z j * k z) u x +
      HRS.Whole.convFun k (fun y => y j * u y) x := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B', hB'⟩ := hB'
  have i1 : Integrable (fun z => (z j * k z) * u (x - z)) volume :=
    hk'.mul_bdd (hu.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (c := B) (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB (x - z))
  have i2 : Integrable (fun z => k z * ((x - z) j * u (x - z))) volume :=
    hk.mul_bdd (hu'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (c := B') (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB' (x - z))
  simp only [mv1_convFun_eq]
  rw [← integral_add i1 i2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [PiLp.sub_apply]
  ring

variable {s : ℝ}

/-- **Weighted local gain.**  For a `C_c^∞` cutoff `θ`, convolution with `θ g` maps weighted `H^t` bounds
(`x^w u ∈ H^t`, `|w| ≤ n`) to weighted `H^{t+d-s}` bounds; `C` depends on `(n, θ)` only. -/
theorem movc2_loc_wt (hs0 : 0 ≤ s) (hsd : s < d) (n : ℕ) : ∀ θ : Euc d → ℝ, ContDiff ℝ ∞ θ →
    HasCompactSupport θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (t E : ℝ) (u : Euc d → ℝ), movc2_Reg n u → movc2_WB n t E u →
      movc2_WB n (t + ((d : ℝ) - s)) (C * E)
        (HRS.Whole.convFun (fun z => θ z * rieszKernel d s z) u) := by
  induction n with
  | zero =>
    intro θ hθ hc
    obtain ⟨C, hC, hgain⟩ := HRS.MS.Tc3.tc3_riesz_loc_sobolev_gain hθ hc hs0 hsd
    refine ⟨C, hC.le, fun t E u _ hu => ?_⟩
    have hu0 := movc2_WB_zero hu
    obtain ⟨h1, h2⟩ := hgain t u hu0.1
    refine movc2_WB_of_SB ⟨h1, ?_⟩
    calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (t + ((d : ℝ) - s))
            (HRS.Whole.convFun (fun x => θ x * rieszKernel d s x) u))
        ≤ Real.sqrt (C ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq t u) := Real.sqrt_le_sqrt h2
      _ = C * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq t u) := by
          rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]
      _ ≤ C * E := mul_le_mul_of_nonneg_left hu0.2 hC.le
  | succ n ih =>
    intro θ hθ hc
    -- constants for the shifted cutoffs
    have hθj : ∀ j : Fin d, ContDiff ℝ ∞ (fun z : Euc d => z j * θ z) := fun j =>
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.mul hθ
    have hcj : ∀ j : Fin d, HasCompactSupport (fun z : Euc d => z j * θ z) := fun j =>
      hc.mul_left
    choose Cj hCj0 hCj using fun j : Fin d => ih (fun z => z j * θ z) (hθj j) (hcj j)
    obtain ⟨C0, hC00, hC0⟩ := ih θ hθ hc
    obtain ⟨Cb, hCb, hgain⟩ := HRS.MS.Tc3.tc3_riesz_loc_sobolev_gain hθ hc hs0 hsd
    set Ctot : ℝ := Cb + ∑ j : Fin d, Cj j + C0 with hCtot
    have hCtot0 : 0 ≤ Ctot := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hCj0 j)
      have := hCb.le; positivity
    refine ⟨Ctot, hCtot0, fun t E u hr hu => ?_⟩
    intro w hw
    cases w with
    | nil =>
      have hu0 := movc2_WB_zero (movc2_WB_mono_n (Nat.zero_le _) hu)
      obtain ⟨h1, h2⟩ := hgain t u hu0.1
      have hE : 0 ≤ E := movc2_SB_nonneg hu0
      have hs : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (t + ((d : ℝ) - s))
            (HRS.Whole.convFun (fun x => θ x * rieszKernel d s x) u)) ≤ Cb * E :=
        calc _ ≤ Real.sqrt (Cb ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq t u) := Real.sqrt_le_sqrt h2
          _ = Cb * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq t u) := by
            rw [Real.sqrt_mul (sq_nonneg Cb), Real.sqrt_sq hCb.le]
          _ ≤ Cb * E := mul_le_mul_of_nonneg_left hu0.2 hCb.le
      refine ⟨by simpa [movc2_mon_nil] using h1, ?_⟩
      simp only [movc2_mon_nil, one_mul]
      refine hs.trans (mul_le_mul_of_nonneg_right ?_ hE)
      have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hCj0 j)
      linarith
    | cons j w' =>
      have hw' : w'.length ≤ n := by simpa using hw
      have hrn : movc2_Reg n u := movc2_Reg_mono (Nat.le_succ n) hr
      have hr1 := movc2_Reg_shift hr j
      have hr0 := hr [] (by simp)
      have hr0' := hr [j] (by simp)
      have hun : movc2_WB n t E u := movc2_WB_mono_n (Nat.le_succ n) hu
      have hu1 := movc2_WB_shift hu j
      have hA := hCj j t E u hrn hun
      have hB := hC0 t E (fun y => y j * u y) hr1 hu1
      have hker : ∀ θ' : Euc d → ℝ, ContDiff ℝ ∞ θ' → HasCompactSupport θ' →
          Integrable (fun z => θ' z * rieszKernel d s z) volume := fun θ' h1 h2 =>
        HRS.MS.Tc3.tc3_Gloc_integrable h1.continuous h2 hs0 hsd
      have hbdd := movc2_xmul_conv (d := d) j (k := fun z => θ z * rieszKernel d s z)
        (u := u) (hker θ hθ hc)
        (by simpa [mul_assoc] using hker _ (hθj j) (hcj j))
        (by simpa [movc2_mon_nil] using hr0.1) (by simpa [movc2_mon_nil] using hr0.2)
        (by simpa [movc2_mon_cons, movc2_mon_nil] using hr0'.1)
        (by simpa [movc2_mon_cons, movc2_mon_nil] using hr0'.2)
      have hsum := movc2_WB_add hA hB
      have hS := hsum w' hw'
      have e : (fun x => movc2_mon (j :: w') x *
          HRS.Whole.convFun (fun z => θ z * rieszKernel d s z) u x) =
          fun x => movc2_mon w' x * (HRS.Whole.convFun (fun z => (z j * θ z) * rieszKernel d s z) u x +
            HRS.Whole.convFun (fun z => θ z * rieszKernel d s z) (fun y => y j * u y) x) := by
        funext x
        rw [movc2_mon_cons]
        have := hbdd x
        simp only [mul_assoc] at this ⊢
        linear_combination (movc2_mon w' x) * this
      rw [e]
      refine movc2_SB_mono_E hS ?_
      have hE : 0 ≤ E := movc2_SB_nonneg (hu [] (by simp) |> fun h => by simpa [movc2_mon_nil] using h)
      have hle : Cj j + C0 ≤ Ctot := by
        have := Finset.single_le_sum (f := fun j => Cj j) (fun j _ => hCj0 j) (Finset.mem_univ j)
        have := hCb.le
        simp only at *
        linarith
      calc Cj j * E + C0 * E = (Cj j + C0) * E := by ring
        _ ≤ Ctot * E := mul_le_mul_of_nonneg_right hle hE

end HRS.MS.MovC2
