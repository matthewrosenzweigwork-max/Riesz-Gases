import HRS.MC.S7FCF5Defs
import HRS.MC.S7FCF5A2
import HRS.MC.S7FCF5A3
import HRS.MC.S7FCF5DA4
import HRS.MC.S7FCW3F1
import HRS.MC.S7FCW3F2

/-!
# Block C1a of packet `fcf5`: the `L^q` bound of the time-integrated drift of one mode

Proof of `fcf5_C1a_drift_Lq` (`S7FCF5Plan.lean`), statement copied verbatim.  Route:

* pointwise, for `u ∈ [a, a+T]` (so `max u 0 = u`), `‖drift u ω‖ₑ ≤ ‖η^u(G_u)‖ₑ + ‖N F^{h}(X_u, μ^u)‖ₑ`
  (triangle inequality and `|N^{-1/2}| ≤ 1`), with `G_u = fcGen R u e_k`;
* `(x+y)^q ≤ 2^{q-1}(x^q+y^q)`, then Hölder in `u` over the window (`S7FCF5H_holder`), then Tonelli
  (`lintegral_lintegral_swap`), with joint measurability from A3, A4a, A4b;
* for each `u`, the `ω`-moments: the mode statistic by F1 (`s7fcw3_core`, whose constant does not depend on the
  bound `|G_u| ≤ M`, applied after scaling by `M`), the commutator by F2 (`s7_FC_F2_B_proof`);
* the bound `|G_u| ≤ C₀ ⟨k⟩²` is A2 (`fcf5_A2_gen_bound_proof`).

Namespace `HRS.MC.Sec7.S7FCF5H`, helpers prefixed `S7FCF5H_`, the theorem `fcf5_C1a_drift_Lq_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5H

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- Linearity of the mean in the test function (no integrability needed). -/
theorem S7FCF5H_pair_const_mul (μ : Measure (Torus d)) (c : ℝ) (φ : Torus d → ℝ) :
    pair μ (fun x => c * φ x) = c * pair μ φ := by
  unfold pair
  exact integral_const_mul c φ

theorem S7FCF5H_pair_scale (μ : Measure (Torus d)) {M : ℝ} (hM : M ≠ 0) (φ : Torus d → ℝ) :
    pair μ φ = M * pair μ (fun x => M⁻¹ * φ x) := by
  rw [← S7FCF5H_pair_const_mul]
  congr 1
  funext x
  rw [← mul_assoc, mul_inv_cancel₀ hM, one_mul]

theorem S7FCF5H_eta_scale {Ω : Type} {N : ℕ} (R : Regime d) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (ω : Ω)
    {M : ℝ} (hM : M ≠ 0) (φ : Torus d → ℝ) :
    fcf5Eta R X φ t ω = M * fcf5Eta R X (fun x => M⁻¹ * φ x) t ω := by
  unfold fcf5Eta
  rw [S7FCF5H_pair_scale (empirical (X t.toNNReal ω)) hM φ,
    S7FCF5H_pair_scale (withDensityReal (R.ρ t)) hM φ]
  ring

theorem S7FCF5H_sq_rpow (x : ℝ) (hx : 0 ≤ x) (q : ℝ) : (x ^ 2) ^ q = x ^ (2 * q) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- From a moment bound of `|g|^q` to a lintegral bound of `‖g‖ₑ^q`. -/
theorem S7FCF5H_lint_enorm_rpow {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {q : ℝ} (hq : 0 ≤ q)
    {g : Ω → ℝ} (hint : Integrable (fun ω => |g ω| ^ q) P) {C : ℝ} (hC : ∫ ω, |g ω| ^ q ∂P ≤ C) :
    ∫⁻ ω, ‖g ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C := by
  have hnn : 0 ≤ᵐ[P] (fun ω => |g ω| ^ q) := ae_of_all _ fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have heq : ∀ ω, ‖g ω‖ₑ ^ q = ENNReal.ofReal (|g ω| ^ q) := fun ω => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq]
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal hC

/-- Hölder on a measure space: `(∫ f)^q ≤ μ(univ)^{q-1} ∫ f^q` for `q ≥ 1`. -/
theorem S7FCF5H_holder {α : Type} [MeasurableSpace α] (μ : Measure α) {q : ℝ} (hq : 1 ≤ q)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, f a ∂μ) ^ q ≤ (μ Set.univ) ^ (q - 1) * ∫⁻ a, f a ^ q ∂μ := by
  rcases eq_or_lt_of_le hq with h1 | h1
  · subst h1
    simp
  · have hpq := Real.HolderConjugate.conjExponent h1
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] at h
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hqne : q ≠ 0 := (lt_trans zero_lt_one h1).ne'
    have hq1 : q - 1 ≠ 0 := (sub_pos.2 h1).ne'
    have hr : (1 / Real.conjExponent q) * q = q - 1 := by
      unfold Real.conjExponent
      field_simp
    calc (∫⁻ a, f a ∂μ) ^ q
        ≤ ((∫⁻ a, f a ^ q ∂μ) ^ (1 / q) * (μ Set.univ) ^ (1 / Real.conjExponent q)) ^ q :=
          ENNReal.rpow_le_rpow h hq0
      _ = ((∫⁻ a, f a ^ q ∂μ) ^ (1 / q)) ^ q * ((μ Set.univ) ^ (1 / Real.conjExponent q)) ^ q :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0
      _ = (∫⁻ a, f a ^ q ∂μ) * (μ Set.univ) ^ (q - 1) := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel hqne, ENNReal.rpow_one, hr]
      _ = (μ Set.univ) ^ (q - 1) * ∫⁻ a, f a ^ q ∂μ := mul_comm _ _

/-- The `ω`-moment of the mode statistic for a bounded test function, with the constant of F1 (`C0`) and the
bound `M` entering only through `M^q`: scaling by `M` reduces to test functions bounded by `1`. -/
theorem S7FCF5H_eta_Lq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} (R : Regime d)
    (X : ℝ≥0 → Ω → Config d N) (t : ℝ) {q : ℝ} (hq : 0 ≤ q) {C0 : ℝ}
    (hb : ∀ b : Torus d → ℝ, Measurable b → (∀ x, |b x| ≤ 1) →
      Integrable (fun ω => |fcf5Eta R X b t ω| ^ q) P ∧ ∫ ω, |fcf5Eta R X b t ω| ^ q ∂P ≤ C0)
    (a : Torus d → ℝ) (ha : Measurable a) {M : ℝ} (hM : 0 < M) (haM : ∀ x, |a x| ≤ M) :
    ∫⁻ ω, ‖fcf5Eta R X a t ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (M ^ q * C0) := by
  have hMne : M ≠ 0 := hM.ne'
  have hb1 : Measurable (fun x => M⁻¹ * a x) := measurable_const.mul ha
  have hb2 : ∀ x, |(fun x => M⁻¹ * a x) x| ≤ 1 := by
    intro x
    show |M⁻¹ * a x| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.2 hM)]
    calc M⁻¹ * |a x| ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (haM x) (inv_nonneg.2 hM.le)
      _ = 1 := inv_mul_cancel₀ hMne
  have hsc : ∀ ω, |fcf5Eta R X a t ω| ^ q
      = M ^ q * |fcf5Eta R X (fun x => M⁻¹ * a x) t ω| ^ q := by
    intro ω
    rw [S7FCF5H_eta_scale R X t ω hMne a, abs_mul, abs_of_pos hM, Real.mul_rpow hM.le (abs_nonneg _)]
  have hint : Integrable (fun ω => |fcf5Eta R X a t ω| ^ q) P := by
    simp_rw [hsc]
    exact (hb _ hb1 hb2).1.const_mul _
  have hC : ∫ ω, |fcf5Eta R X a t ω| ^ q ∂P ≤ M ^ q * C0 := by
    simp_rw [hsc]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hb _ hb1 hb2).2 (Real.rpow_nonneg hM.le _)
  exact S7FCF5H_lint_enorm_rpow (g := fun ω => fcf5Eta R X a t ω) P hq hint hC

/-- The time-window `L^q` bound: `E (∫_S F(u,·) du)^q ≤ μ(S)^{q-1} · V · μ(S)` when `E F(u,·)^q ≤ V` for all `u`. -/
theorem S7FCF5H_time_Lq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set ℝ} (hS : MeasurableSet S) {q : ℝ} (hq : 1 ≤ q) {F : ℝ × Ω → ℝ≥0∞} (hF : Measurable F)
    {V : ℝ≥0∞} (hV : ∀ u, ∫⁻ ω, F (u, ω) ^ q ∂P ≤ V) :
    ∫⁻ ω, (∫⁻ u in S, F (u, ω)) ^ q ∂P ≤ (volume S) ^ (q - 1) * (V * volume S) := by
  have hFq : Measurable (fun p : ℝ × Ω => F p ^ q) := hF.pow_const q
  have hmeas : Measurable (fun ω => ∫⁻ u in S, F (u, ω) ^ q) := hFq.lintegral_prod_left'
  have hY : ∀ ω, (∫⁻ u in S, F (u, ω)) ^ q ≤ (volume S) ^ (q - 1) * ∫⁻ u in S, F (u, ω) ^ q := by
    intro ω
    have hm : Measurable (fun u : ℝ => F (u, ω)) := hF.comp (measurable_id.prodMk measurable_const)
    have := S7FCF5H_holder (volume.restrict S) hq hm
    rwa [Measure.restrict_apply_univ] at this
  have hswap : ∫⁻ ω, (∫⁻ u in S, F (u, ω) ^ q) ∂P = ∫⁻ u in S, ∫⁻ ω, F (u, ω) ^ q ∂P := by
    refine lintegral_lintegral_swap ?_
    exact (hFq.comp measurable_swap).aemeasurable
  calc ∫⁻ ω, (∫⁻ u in S, F (u, ω)) ^ q ∂P
      ≤ ∫⁻ ω, (volume S) ^ (q - 1) * (∫⁻ u in S, F (u, ω) ^ q) ∂P := lintegral_mono hY
    _ = (volume S) ^ (q - 1) * ∫⁻ ω, (∫⁻ u in S, F (u, ω) ^ q) ∂P := lintegral_const_mul _ hmeas
    _ = (volume S) ^ (q - 1) * ∫⁻ u in S, ∫⁻ ω, F (u, ω) ^ q ∂P := by rw [hswap]
    _ ≤ (volume S) ^ (q - 1) * ∫⁻ u in S, V :=
        mul_le_mul_of_nonneg_left (setLIntegral_mono' hS fun u _ => hV u) zero_le'
    _ = (volume S) ^ (q - 1) * (V * volume S) := by rw [setLIntegral_const]

/-- The mode-statistic integrand of the window: `‖η^{max u 0}(G_{max u 0})‖ₑ` as a function of `(u, ω)`. -/
def S7FCF5H_F1 {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (R : Regime d) (X : ℝ≥0 → Ω → Config d N)
    (k : NonzeroLattice d) : ℝ × Ω → ℝ≥0∞ :=
  fun p => ‖fcf5Eta R X (fcGen R (max p.1 0) (Torus.realMode k)) (max p.1 0) p.2‖ₑ

/-- The commutator integrand of the window: `‖N F^{h_{e_k}}(X_{max u 0}, μ^{max u 0})‖ₑ`. -/
def S7FCF5H_F2 {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (R : Regime d) (X : ℝ≥0 → Ω → Config d N)
    (k : NonzeroLattice d) : ℝ × Ω → ℝ≥0∞ :=
  fun p => ‖fcf5Comm R X (Torus.realMode k) (max p.1 0) p.2‖ₑ

theorem fcf5_C1a_drift_Lq_proof (R : Regime d) (T : ℝ) (hT : 0 < T) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      FCPrepared R P X₀ W X → ∀ a : ℝ, 0 ≤ a → ∀ k : NonzeroLattice d,
        ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ) ^ q ∂P ≤
          ENNReal.ofReal (C * Lattice.jp k.1 ^ (2 * q)) := by
  obtain ⟨C0, hC0, hcore⟩ := HRS.MC.Sec7.S7FCW3.s7fcw3_core R q hq
  obtain ⟨C2, hC2⟩ := HRS.MC.Sec7.S7FCW3.s7_FC_F2_B_proof R q hq
  obtain ⟨Cg, hCg, hA2⟩ := HRS.MC.Sec7.S7FCF5A.fcf5_A2_gen_bound_proof R
  have hq0 : (0 : ℝ) ≤ q := by linarith
  refine ⟨2 ^ (q - 1) * (T ^ (q - 1) * (T * (C0 * (Cg + 1) ^ q + max C2 0))), ?_⟩
  intro N hN Ω _ P _ X₀ W X hprep a ha k
  have hsN : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ N))
  have hjp0 : 0 < Lattice.jp k.1 := Torus.jp_pos _
  have hJ : 0 ≤ Lattice.jp k.1 ^ (2 * q) := Real.rpow_nonneg hjp0.le _
  have hA3 := HRS.MC.Sec7.S7FCF5A.fcf5_A3_gen_meas_proof R (HRS.FieldSingAux.isSmooth_realMode k)
  have hA4a := HRS.MC.Sec7.S7FCF5D.fcf5_A4a_eta_meas_proof R P X₀ W X hprep
    (fun u x => fcGen R (max u 0) (Torus.realMode k) x) hA3 (Cg * Lattice.jp k.1 ^ 2)
    (fun u x => hA2 (max u 0) (le_max_right _ _) k x)
  have hA4b := HRS.MC.Sec7.S7FCF5D.fcf5_A4b_comm_meas_proof R P X₀ W X hprep
    (HRS.FieldSingAux.isSmooth_realMode k)
  have hE : Measurable (fun p : ℝ × Ω => fcf5Eta R X (fcGen R (max p.1 0) (Torus.realMode k))
      (max p.1 0) p.2) := by
    have e : ∀ u : ℝ, max (max u 0) 0 = max u 0 := fun u => max_eq_left (le_max_right _ _)
    simpa only [e] using hA4a
  have hF1 : Measurable (S7FCF5H_F1 (Ω := Ω) R X k) := hE.enorm
  have hF2 : Measurable (S7FCF5H_F2 (Ω := Ω) R X k) := hA4b.enorm
  have hcomm : ∀ c : ℝ, ‖(Real.sqrt N)⁻¹ * c‖ₑ ≤ ‖c‖ₑ := by
    intro c
    rw [enorm_mul]
    have h1 : ‖(Real.sqrt N)⁻¹‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      exact ENNReal.ofReal_le_one.2 (inv_le_one_of_one_le₀ hsN)
    calc ‖(Real.sqrt N)⁻¹‖ₑ * ‖c‖ₑ ≤ 1 * ‖c‖ₑ := by gcongr
      _ = ‖c‖ₑ := one_mul _
  -- pointwise drift bound on the window
  have hpt : ∀ u ∈ Set.Icc a (a + T), ∀ ω : Ω,
      ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ ≤ S7FCF5H_F1 R X k (u, ω) + S7FCF5H_F2 R X k (u, ω) := by
    intro u hu ω
    have hmax : max u 0 = u := max_eq_left (le_trans ha hu.1)
    show ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ
      ≤ ‖fcf5Eta R X (fcGen R (max u 0) (Torus.realMode k)) (max u 0) ω‖ₑ
        + ‖fcf5Comm R X (Torus.realMode k) (max u 0) ω‖ₑ
    rw [hmax]
    calc ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ
        = ‖fcf5Eta R X (fcGen R u (Torus.realMode k)) u ω
            - (Real.sqrt N)⁻¹ * fcf5Comm R X (Torus.realMode k) u ω‖ₑ := rfl
      _ ≤ ‖fcf5Eta R X (fcGen R u (Torus.realMode k)) u ω‖ₑ
            + ‖(Real.sqrt N)⁻¹ * fcf5Comm R X (Torus.realMode k) u ω‖ₑ := enorm_sub_le
      _ ≤ ‖fcf5Eta R X (fcGen R u (Torus.realMode k)) u ω‖ₑ
            + ‖fcf5Comm R X (Torus.realMode k) u ω‖ₑ := add_le_add le_rfl (hcomm _)
  have hF1ω : ∀ ω : Ω, Measurable (fun u : ℝ => S7FCF5H_F1 R X k (u, ω)) := fun ω =>
    hF1.comp (measurable_id.prodMk measurable_const)
  have hXY : ∀ ω : Ω, ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ
      ≤ (∫⁻ u in Set.Icc a (a + T), S7FCF5H_F1 R X k (u, ω))
        + ∫⁻ u in Set.Icc a (a + T), S7FCF5H_F2 R X k (u, ω) := by
    intro ω
    calc ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ
        ≤ ∫⁻ u in Set.Icc a (a + T), (S7FCF5H_F1 R X k (u, ω) + S7FCF5H_F2 R X k (u, ω)) :=
          setLIntegral_mono' measurableSet_Icc (fun u hu => hpt u hu ω)
      _ = _ := lintegral_add_left (hF1ω ω) _
  have hY1m : Measurable (fun ω : Ω => ∫⁻ u in Set.Icc a (a + T), S7FCF5H_F1 R X k (u, ω)) :=
    hF1.lintegral_prod_left'
  have hmodeA : ∀ u : ℝ, ∫⁻ ω, S7FCF5H_F1 R X k (u, ω) ^ q ∂P
      ≤ ENNReal.ofReal (C0 * (Cg + 1) ^ q * Lattice.jp k.1 ^ (2 * q)) := by
    intro u
    have hu0 : 0 ≤ max u 0 := le_max_right _ _
    have hpu : Measurable (fun x : Torus d => ((u, x) : ℝ × Torus d)) :=
      measurable_const.prodMk measurable_id
    have hbm : Measurable (fun x : Torus d => fcGen R (max u 0) (Torus.realMode k) x) := by
      have h := hA3.comp hpu
      exact h
    have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
    have hM : 0 < (Cg + 1) * Lattice.jp k.1 ^ 2 := mul_pos (by linarith) (pow_pos hjp 2)
    have hbd : ∀ x, |fcGen R (max u 0) (Torus.realMode k) x| ≤ (Cg + 1) * Lattice.jp k.1 ^ 2 :=
      fun x => (hA2 (max u 0) hu0 k x).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
    have hb : ∀ b : Torus d → ℝ, Measurable b → (∀ x, |b x| ≤ 1) →
        Integrable (fun ω => |fcf5Eta R X b (max u 0) ω| ^ q) P ∧
          ∫ ω, |fcf5Eta R X b (max u 0) ω| ^ q ∂P ≤ C0 :=
      fun b hb1 hb2 => hcore N hN P X₀ W X hprep (max u 0) hu0 b hb1 hb2
    have key := S7FCF5H_eta_Lq P R X (max u 0) hq0 hb _ hbm hM hbd
    have hexp : ((Cg + 1) * Lattice.jp k.1 ^ 2) ^ q * C0
        = C0 * (Cg + 1) ^ q * Lattice.jp k.1 ^ (2 * q) := by
      rw [Real.mul_rpow (show (0 : ℝ) ≤ Cg + 1 by linarith) (sq_nonneg (Lattice.jp k.1)),
        S7FCF5H_sq_rpow _ hjp.le]
      ring
    calc ∫⁻ ω, S7FCF5H_F1 R X k (u, ω) ^ q ∂P
        = ∫⁻ ω, ‖fcf5Eta R X (fcGen R (max u 0) (Torus.realMode k)) (max u 0) ω‖ₑ ^ q ∂P := rfl
      _ ≤ ENNReal.ofReal (((Cg + 1) * Lattice.jp k.1 ^ 2) ^ q * C0) := key
      _ = ENNReal.ofReal (C0 * (Cg + 1) ^ q * Lattice.jp k.1 ^ (2 * q)) := by rw [hexp]
  have hmodeB : ∀ u : ℝ, ∫⁻ ω, S7FCF5H_F2 R X k (u, ω) ^ q ∂P
      ≤ ENNReal.ofReal (max C2 0 * Lattice.jp k.1 ^ (2 * q)) := by
    intro u
    have hu0 : 0 ≤ max u 0 := le_max_right _ _
    obtain ⟨hint, hC⟩ := hC2 N hN P X₀ W X hprep (max u 0) hu0 k
    calc ∫⁻ ω, S7FCF5H_F2 R X k (u, ω) ^ q ∂P
        = ∫⁻ ω, ‖fcf5Comm R X (Torus.realMode k) (max u 0) ω‖ₑ ^ q ∂P := rfl
      _ ≤ ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (2 * q)) :=
          S7FCF5H_lint_enorm_rpow (g := fun ω => fcf5Comm R X (Torus.realMode k) (max u 0) ω) P hq0 hint hC
      _ ≤ ENNReal.ofReal (max C2 0 * Lattice.jp k.1 ^ (2 * q)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hJ)
  have hvol : volume (Set.Icc a (a + T)) = ENNReal.ofReal T := by
    rw [Real.volume_Icc, add_sub_cancel_left]
  have hne2 : (2 : ℝ≥0∞) ^ (q - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ (q - 1) = ENNReal.ofReal (2 ^ (q - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  calc ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ) ^ q ∂P
      ≤ ∫⁻ ω, 2 ^ (q - 1) * ((∫⁻ u in Set.Icc a (a + T), S7FCF5H_F1 R X k (u, ω)) ^ q
          + (∫⁻ u in Set.Icc a (a + T), S7FCF5H_F2 R X k (u, ω)) ^ q) ∂P := by
        refine lintegral_mono fun ω => ?_
        exact (ENNReal.rpow_le_rpow (hXY ω) hq0).trans (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq)
    _ = 2 ^ (q - 1) * (∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), S7FCF5H_F1 R X k (u, ω)) ^ q ∂P
          + ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), S7FCF5H_F2 R X k (u, ω)) ^ q ∂P) := by
        rw [lintegral_const_mul' _ _ hne2, lintegral_add_left (hY1m.pow_const q)]
    _ ≤ 2 ^ (q - 1) * ((volume (Set.Icc a (a + T))) ^ (q - 1)
          * (ENNReal.ofReal (C0 * (Cg + 1) ^ q * Lattice.jp k.1 ^ (2 * q)) * volume (Set.Icc a (a + T)))
        + (volume (Set.Icc a (a + T))) ^ (q - 1)
          * (ENNReal.ofReal (max C2 0 * Lattice.jp k.1 ^ (2 * q)) * volume (Set.Icc a (a + T)))) :=
        mul_le_mul_of_nonneg_left (add_le_add (S7FCF5H_time_Lq P measurableSet_Icc hq hF1 hmodeA)
          (S7FCF5H_time_Lq P measurableSet_Icc hq hF2 hmodeB)) zero_le'
    _ = ENNReal.ofReal (2 ^ (q - 1) * (T ^ (q - 1) * (T * (C0 * (Cg + 1) ^ q + max C2 0)))
          * Lattice.jp k.1 ^ (2 * q)) := by
        rw [hvol, h2, ENNReal.ofReal_rpow_of_pos hT]
        simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add]
        ring

end HRS.MC.Sec7.S7FCF5H
