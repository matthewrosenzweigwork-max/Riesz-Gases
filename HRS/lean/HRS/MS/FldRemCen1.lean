import HRS.MS.FldRemAux4

/-!
# S5.3 (`field_remainder_centered`), part 1: stationary second moments, the mean functional `ℓ`

Under a stationary process (`law (X_r) = law (X_0)`) with the variance bound
`N Var[D_μ(h_f)(X_0)] ≤ C_A δ_N (sup‖D²f‖)²` for every `f ∈ C_b²`:
* `D f (X_r)` is square integrable, with mean `ℓ f` independent of `r` (`s53_mean_eq`);
* `ℓ` is linear on `C_b²`, and bounded: `|ℓ f| ≤ C_m cbNorm 2 f` (`s53_mean_bound`, a gliding-hump argument: otherwise
  `∑ 2^{-n} g_n ∈ C_b²` with `ℓ g_n ≥ 4^n` would have a pathwise convergent `D`-series with divergent mean part).

Helper names carry the prefix `s53_`, namespace `HRS.MS.S53`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole

variable {d N : ℕ}

/-- The stationary variance hypotheses of `field_remainder_centered`, for a measurable process `X'`. -/
structure S53Var (s : ℝ) (ρ : Euc d → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X' : ℝ≥0 → Ω → EucConfig d N) (T CA δ : ℝ) : Prop where
  meas : ∀ t, Measurable (X' t)
  stat : ∀ t ∈ Set.Icc (0 : ℝ) T, P.map (X' (Real.toNNReal t)) = P.map (X' 0)
  var : ∀ f : Euc d → ℝ, MemCb 2 f →
    (N : ℝ≥0∞) * evariance (fun ζ => s53_Dk s ρ f (X' 0 ζ)) P ≤
      ENNReal.ofReal (CA * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2)

section Basic

variable {s : ℝ} {ρ : Euc d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X' : ℝ≥0 → Ω → EucConfig d N} {T CA δ : ℝ}

lemma s53_Dk_meas_config {f : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hf : ContDiff ℝ 1 f) :
    Measurable fun Y : EucConfig d N => s53_Dk s ρ f Y := by
  have h : Measurable fun p : ℝ × EucConfig d N => s53_Dk s ρ ((fun _ : ℝ => f) p.1) p.2 :=
    s53_Dk_measurable (N := N) (s := s) hρ (F := fun _ => f) ((s53_gradient_measurable hf).comp measurable_snd)
  have hpr : Measurable fun Y : EucConfig d N => ((0 : ℝ), Y) := measurable_const.prodMk measurable_id
  have h2 := h.comp hpr
  exact h2

lemma s53_memLp [IsProbabilityMeasure P] (hρ : HRS.Whole.IsProbDensity ρ) (hN : 0 < N)
    (H : S53Var s ρ P X' T CA δ) {f : Euc d → ℝ} (hf : MemCb 2 f) :
    MemLp (fun ζ => s53_Dk s ρ f (X' 0 ζ)) 2 P := by
  have hm : Measurable fun ζ => s53_Dk s ρ f (X' 0 ζ) :=
    (s53_Dk_meas_config hρ (hf.1.of_le (by norm_num))).comp (H.meas 0)
  refine (evariance_lt_top_iff_memLp hm.aestronglyMeasurable).1 ?_
  have h1 := H.var f hf
  have h2 : (N : ℝ≥0∞) * evariance (fun ζ => s53_Dk s ρ f (X' 0 ζ)) P < ⊤ :=
    lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  by_contra hcon
  have : evariance (fun ζ => s53_Dk s ρ f (X' 0 ζ)) P = ⊤ := not_lt_top_iff.1 hcon
  rw [this, ENNReal.mul_top (by exact_mod_cast hN.ne')] at h2
  exact lt_irrefl _ h2

/-- the mean functional -/
def s53_ell (s : ℝ) (ρ : Euc d → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X' : ℝ≥0 → Ω → EucConfig d N) (f : Euc d → ℝ) : ℝ := ∫ ζ, s53_Dk s ρ f (X' 0 ζ) ∂P

lemma s53_stat_lintegral (H : S53Var s ρ P X' T CA δ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {g : EucConfig d N → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ζ, g (X' (Real.toNNReal r) ζ) ∂P = ∫⁻ ζ, g (X' 0 ζ) ∂P := by
  rw [← lintegral_map hg (H.meas _), ← lintegral_map hg (H.meas 0), H.stat r hr]

lemma s53_mean_eq (H : S53Var s ρ P X' T CA δ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T)
    {g : EucConfig d N → ℝ} (hg : Measurable g) :
    ∫ ζ, g (X' (Real.toNNReal r) ζ) ∂P = ∫ ζ, g (X' 0 ζ) ∂P := by
  rw [← integral_map (H.meas _).aemeasurable hg.aestronglyMeasurable,
    ← integral_map (H.meas 0).aemeasurable hg.aestronglyMeasurable, H.stat r hr]

end Basic


/-! ### Algebra of `C_b²` and of `D` -/

section Alg

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ}

lemma s53_memCb_add {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g) :
    MemCb 2 (fun x => f x + g x) := by
  have h := HRS.MS.Fcau.fcau_memCb_sub hf (s53_memCb_const_mul (-1) hg)
  have e : (fun x => f x + g x) = fun x => f x - (-1 * g x) := by funext x; ring
  rw [e]; exact h

lemma s53_Dk_add (ctx : S53Ctx s ρ Mρ) {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g)
    (X : EucConfig d N) : s53_Dk s ρ (fun x => f x + g x) X = s53_Dk s ρ f X + s53_Dk s ρ g X := by
  have e : (fun x => f x + g x) = fun x => f x - (-1 * g x) := by funext x; ring
  rw [e, s53_Dk_sub ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hf (s53_memCb_const_mul (-1) hg),
    s53_Dk_const_mul (-1) (hg.1.of_le (by norm_num))]
  ring

lemma s53_p_le_cb {f : Euc d → ℝ} (hf : MemCb 2 f) :
    (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ≤ cbNorm 2 f := by
  unfold cbNorm
  have h2 := hf.2 2 le_rfl
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i f z‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num : 2 < 2 + 1)))
  exact le_rfl

lemma s53_cb_const_mul_le (c : ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) :
    cbNorm 2 (fun x => c * f x) ≤ |c| * cbNorm 2 f := by
  unfold cbNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj2 : j ≤ 2 := by have := Finset.mem_range.1 hj; omega
  have hbdd := hf.2 j hj2
  refine ciSup_le fun x => ?_
  have e : iteratedFDeriv ℝ j (fun x => c * f x) x = c • iteratedFDeriv ℝ j f x := by
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := j) (a := c) (f := f) (x := x)
      (hf.1.of_le (by exact_mod_cast hj2)).contDiffAt
    have e2 : (fun x => c * f x) = c • f := by funext x; simp
    rw [e2]; exact this
  rw [e, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (le_ciSup hbdd x) (abs_nonneg _)

lemma s53_cb_nonneg (f : Euc d → ℝ) : 0 ≤ cbNorm 2 f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

end Alg


lemma s53_tsum_memCb {u : ℕ → Euc d → ℝ} (hu : ∀ n, MemCb 2 (u n)) {v : ℕ → ℝ} (hv : Summable v)
    (hb : ∀ n, ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (u n) x‖ ≤ v n) :
    MemCb 2 (fun x => ∑' n, u n x) ∧
      ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (fun x => ∑' n, u n x) x‖ ≤ ∑' n, v n := by
  have hcd : ∀ n, ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) (u n) := fun n => by
    simpa using (hu n).1
  have hsum : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → Summable (fun n => v n) := fun _ _ => hv
  have hbd : ∀ (k : ℕ) (n : ℕ) (x : Euc d), (k : ℕ∞) ≤ 2 → ‖iteratedFDeriv ℝ k (u n) x‖ ≤ v n :=
    fun k n x hk => hb n k (by exact_mod_cast hk) x
  have hcdF := contDiff_tsum (𝕜 := ℝ) (f := u) (v := fun _ n => v n) (N := 2) hcd hsum hbd
  have hit : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ k (fun x => ∑' n, u n x) x‖ ≤ ∑' n, v n := by
    intro k hk x
    rw [iteratedFDeriv_tsum (𝕜 := ℝ) (f := u) (v := fun _ n => v n) (N := 2) hcd hsum hbd hk]
    exact tsum_of_norm_bounded hv.hasSum fun n => hbd k n x hk
  refine ⟨⟨by simpa using hcdF, fun j hj => ⟨∑' n, v n, ?_⟩⟩, fun k hk x => hit k (by exact_mod_cast hk) x⟩
  rintro _ ⟨x, rfl⟩
  exact hit j (by exact_mod_cast hj) x

/-! ### The mean functional is bounded (gliding hump) -/

section Mean

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X' : ℝ≥0 → Ω → EucConfig d N} {T CA δ : ℝ}

lemma s53_ell_const_mul (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) :
    s53_ell s ρ P X' (fun x => c * f x) = c * s53_ell s ρ P X' f := by
  unfold s53_ell
  simp only [s53_Dk_const_mul c hf]
  exact integral_const_mul _ _

lemma s53_Dk_zero_of_cb (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) {f : Euc d → ℝ} (hf : MemCb 2 f)
    (h0 : cbNorm 2 f = 0) (X : EucConfig d N) : s53_Dk s ρ f X = 0 := by
  have h1 := s53_Dk_bound ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hf X
  have h2 := s53_p_le_cb hf
  have h3 : (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) = 0 :=
    le_antisymm (h2.trans h0.le) (s53_cbSup_nonneg f)
  rw [h3] at h1
  simpa using h1


lemma s53_hump_seq (ctx : S53Ctx s ρ Mρ) (hN : 0 < N)
    (hcon : ∀ C : ℝ, 0 ≤ C → ∃ f : Euc d → ℝ, MemCb 2 f ∧ C * cbNorm 2 f < |s53_ell s ρ P X' f|) :
    ∃ g : ℕ → Euc d → ℝ, (∀ n, MemCb 2 (g n)) ∧ (∀ n, cbNorm 2 (g n) ≤ 1) ∧
      ∀ n, (4 : ℝ) ^ n < s53_ell s ρ P X' (g n) := by
  choose f hf hfl using fun n : ℕ => hcon ((4 : ℝ) ^ n) (by positivity)
  have hq : ∀ n, 0 < cbNorm 2 (f n) := fun n => by
    refine lt_of_le_of_ne (s53_cb_nonneg _) fun h0 => ?_
    have hz : s53_ell s ρ P X' (f n) = 0 := by
      unfold s53_ell
      simp only [s53_Dk_zero_of_cb ctx hN (hf n) h0.symm]
      simp
    have := hfl n
    rw [hz, ← h0] at this
    simp at this
  set ε : ℕ → ℝ := fun n => if 0 < s53_ell s ρ P X' (f n) then 1 else -1 with hε
  have hε1 : ∀ n, |ε n| = 1 := fun n => by simp only [hε]; split_ifs <;> simp
  set g : ℕ → Euc d → ℝ := fun n x => (ε n / cbNorm 2 (f n)) * f n x with hg
  refine ⟨g, fun n => s53_memCb_const_mul _ (hf n), fun n => ?_, fun n => ?_⟩
  · refine (s53_cb_const_mul_le _ (hf n)).trans ?_
    rw [abs_div, hε1, abs_of_pos (hq n)]
    rw [div_mul_cancel₀ _ (hq n).ne']
  · have e : s53_ell s ρ P X' (g n) = (ε n / cbNorm 2 (f n)) * s53_ell s ρ P X' (f n) :=
      s53_ell_const_mul _ ((hf n).1.of_le (by norm_num))
    rw [e]
    have h1 : ε n * s53_ell s ρ P X' (f n) = |s53_ell s ρ P X' (f n)| := by
      simp only [hε]
      split_ifs with h
      · rw [one_mul, abs_of_pos h]
      · rw [abs_of_nonpos (not_lt.1 h)]; ring
    rw [div_mul_eq_mul_div, h1, lt_div_iff₀ (hq n)]
    exact hfl n

lemma s53_iter_const_mul_le (c : ℝ) {g : Euc d → ℝ} (hg : MemCb 2 g) (hcb : cbNorm 2 g ≤ 1) {k : ℕ}
    (hk : k ≤ 2) (x : Euc d) : ‖iteratedFDeriv ℝ k (fun x => c * g x) x‖ ≤ |c| := by
  have hbdd := hg.2 k hk
  have e : iteratedFDeriv ℝ k (fun x => c * g x) x = c • iteratedFDeriv ℝ k g x := by
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := k) (a := c) (f := g) (x := x)
      (hg.1.of_le (by exact_mod_cast hk)).contDiffAt
    have e2 : (fun x => c * g x) = c • g := by funext x; simp
    rw [e2]; exact this
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 : ‖iteratedFDeriv ℝ k g x‖ ≤ 1 := by
    refine (le_ciSup hbdd x).trans ?_
    refine le_trans ?_ hcb
    unfold cbNorm
    exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i g z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  calc |c| * ‖iteratedFDeriv ℝ k g x‖ ≤ |c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    _ = |c| := mul_one _

lemma s53_finsum_Dk (ctx : S53Ctx s ρ Mρ) {u : ℕ → Euc d → ℝ} (hu : ∀ n, MemCb 2 (u n)) (M : ℕ)
    (X : EucConfig d N) :
    MemCb 2 (fun x => ∑ n ∈ Finset.range M, u n x) ∧
      s53_Dk s ρ (fun x => ∑ n ∈ Finset.range M, u n x) X = ∑ n ∈ Finset.range M, s53_Dk s ρ (u n) X := by
  induction M with
  | zero =>
    have h0 := s53_memCb_const_mul 0 (hu 0)
    have e : (fun x : Euc d => ∑ n ∈ Finset.range 0, u n x) = fun x => 0 * u 0 x := by
      funext x; simp
    rw [e]
    refine ⟨h0, ?_⟩
    rw [s53_Dk_const_mul 0 ((hu 0).1.of_le (by norm_num))]
    simp
  | succ M ih =>
    obtain ⟨ihm, ihD⟩ := ih
    have e : (fun x : Euc d => ∑ n ∈ Finset.range (M + 1), u n x) =
        fun x => (∑ n ∈ Finset.range M, u n x) + u M x := by
      funext x; rw [Finset.sum_range_succ]
    rw [e]
    refine ⟨s53_memCb_add ihm (hu M), ?_⟩
    rw [s53_Dk_add ctx ihm (hu M), ihD, Finset.sum_range_succ]

end Mean

end HRS.MS.S53
