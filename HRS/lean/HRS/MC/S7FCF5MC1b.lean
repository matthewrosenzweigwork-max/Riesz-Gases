import HRS.MC.S7FCF5MU
import HRS.MC.S7FCF5BB1
import HRS.MC.S7FCW7F3

/-!
# Block C1b of packet `fcf5`: the `L^q` bound of the window supremum of one mode

Proof of `fcf5_C1b_mode_sup` (`S7FCF5Plan.lean`), statement copied verbatim.  Route (with `f = e_k`, `E_t = η^t(f)`,
`M` and `ℱ` from F3, `D_u` the drift, `I_{a,τ} = ∫_a^τ D_u du`, `Z = ∫⁻_{[a,a+T]} ‖D_u‖ₑ`):

* a.s., for `τ ∈ [a, a+T]`: `E_τ - E_a = (M_τ - M_a) + I_{a,τ}` (F3), and `‖I_{a,τ}‖ₑ ≤ Z` (`S7FCF5M_int_enorm_le`);
* `Y := sup_{t ∈ a+ℚ∩[0,T]} ‖M_t - M_a‖ₑ` (countable, measurable) and `S := sup_{t ∈ a+ℚ∩[0,T]} ‖E_t‖ₑ`, so
  `S ≤ ‖E_a‖ₑ + Y + Z` a.s.; `Y ≤ sup_{[a,a+T]}‖M_s - M_a‖ₑ` (B1 applies to the latter);
* `‖M_{a+T} - M_a‖ₑ ≤ ‖E_{a+T}‖ₑ + ‖E_a‖ₑ + Z` a.s.;
* exponent `p = 2q`: the three-term split (`S7FCF5M_split3`), the moments of `E` (F1, `S7FCF5M_realMode_moment`) and of
  `Z` (C1a at `p`), then B1 at `p` gives `E Y^p`, Lyapunov gives `E Y^q ≤ (E Y^p)^{q/p}` (`S7FCF5M_lyap`), which is
  `O(⟨k⟩^{2q})` (the `⟨k⟩`-powers are `2p·(q/p) = 2q`);
* the final split at exponent `q` with C1a at `q` gives `E S^q ≤ C ⟨k⟩^{2q}`.

Namespace `HRS.MC.Sec7.S7FCF5M`, theorem `fcf5_C1b_mode_sup_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5M

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The two-factor combination `c (c (x + y) + z)` in `ℝ≥0∞` (for nonnegative reals). -/
theorem S7FCF5M_ofReal_lin {c x y z : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ENNReal.ofReal c * (ENNReal.ofReal c * (ENNReal.ofReal x + ENNReal.ofReal y) + ENNReal.ofReal z)
      = ENNReal.ofReal (c * (c * (x + y) + z)) := by
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_add (mul_nonneg hc (add_nonneg hx hy)) hz, ← ENNReal.ofReal_mul hc]

theorem fcf5_C1b_mode_sup_proof (R : Regime d) (T : ℝ) (hT : 0 < T) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      FCPrepared R P X₀ W X → ∀ a : ℝ, 0 ≤ a → ∀ k : NonzeroLattice d,
        ∫⁻ ω, (⨆ t ∈ fcf5Rat a T, ‖fcf5Eta R X (Torus.realMode k) t ω‖ₑ) ^ q ∂P ≤
          ENNReal.ofReal (C * Lattice.jp k.1 ^ (2 * q)) := by
  -- the exponent of the auxiliary moments
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 2 * q := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by linarith
  have hp1 : 1 < p := by rw [hpdef]; linarith
  have hqp : q ≤ p := by rw [hpdef]; linarith
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hq0' : 0 < q := by linarith
  -- inputs independent of `N`, the realisation, `a` and `k`
  obtain ⟨Ax, hAx0, hAx⟩ := S7FCF5M_realMode_moment R hq
  obtain ⟨Ap, hAp0, hAp⟩ := S7FCF5M_realMode_moment R hp1.le
  obtain ⟨Czq, hCzq⟩ := HRS.MC.Sec7.S7FCF5H.fcf5_C1a_drift_Lq_proof R T hT q hq
  obtain ⟨Czp, hCzp⟩ := HRS.MC.Sec7.S7FCF5H.fcf5_C1a_drift_Lq_proof R T hT p hp1.le
  -- constants (real numbers, nonnegative)
  obtain ⟨Lp, hLp⟩ : ∃ L : ℝ, L = (2 : ℝ) ^ (p - 1) * ((2 : ℝ) ^ (p - 1) * (Ap + Ap) + max Czp 0) :=
    ⟨_, rfl⟩
  have hLp0 : 0 ≤ Lp := by
    rw [hLp]
    exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by positivity) (add_nonneg hAp0 hAp0))
      (le_max_right _ _))
  obtain ⟨Fp, hFp⟩ : ∃ F : ℝ, F = (p / (p - 1)) ^ p * Lp := ⟨_, rfl⟩
  have hK0 : 0 ≤ (p / (p - 1)) ^ p :=
    Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hFp0 : 0 ≤ Fp := by rw [hFp]; exact mul_nonneg hK0 hLp0
  obtain ⟨Ly, hLy⟩ : ∃ L : ℝ, L = Fp ^ (q / p) := ⟨_, rfl⟩
  have hLy0 : 0 ≤ Ly := by rw [hLy]; exact Real.rpow_nonneg hFp0 _
  obtain ⟨Cfin, hCfin⟩ : ∃ C : ℝ, C = (2 : ℝ) ^ (q - 1) * ((2 : ℝ) ^ (q - 1) * (Ax + Ly) + max Czq 0) :=
    ⟨_, rfl⟩
  refine ⟨Cfin, ?_⟩
  intro N hN Ω _ P _ X₀ W X hprep a ha k
  -- the time-`a+T` and `a` moments are in the `q`- and `p`-form
  have hJ1 : (1 : ℝ) ≤ Lattice.jp k.1 := Torus.jp_ge_one k.1
  have hJ0 : (0 : ℝ) ≤ Lattice.jp k.1 := by linarith
  have hJq : (1 : ℝ) ≤ Lattice.jp k.1 ^ (2 * q) := Real.one_le_rpow hJ1 (by linarith)
  have hJp : (1 : ℝ) ≤ Lattice.jp k.1 ^ (2 * p) := Real.one_le_rpow hJ1 (by linarith)
  have hJpn : (0 : ℝ) ≤ Lattice.jp k.1 ^ (2 * p) := Real.rpow_nonneg hJ0 _
  have hJqn : (0 : ℝ) ≤ Lattice.jp k.1 ^ (2 * q) := Real.rpow_nonneg hJ0 _
  have haT : (0 : ℝ) ≤ a + T := by linarith
  -- the mode identity (F3) and the martingale
  have hmeas_k : Measurable (Torus.realMode k : Torus d → ℝ) :=
    (HRS.FieldSingAux.continuous_realMode k).measurable
  obtain ⟨ℱ, W', -, M, hMart, -, hMc, hid⟩ :=
    HRS.MC.Sec7.S7FCW7.s7_FC_F3_mode_identity_proof R hN P X₀ W X hprep (Torus.realMode k)
      (HRS.FieldSingAux.isSmooth_realMode k)
  have hMm : ∀ s : ℝ, Measurable fun ω => M s ω := fun s => ((hMart.1 s).mono (ℱ.le s)).measurable
  have hid' : ∀ᵐ ω ∂P, ∀ τ : ℝ, a ≤ τ → τ ≤ a + T →
      fcf5Eta R X (Torus.realMode k) τ ω - fcf5Eta R X (Torus.realMode k) a ω
        = (M τ ω - M a ω) + ∫ u in a..τ, fcf5Drift R X (Torus.realMode k) u ω := by
    filter_upwards [hid] with ω hω
    intro τ hτa _
    exact hω a τ ha hτa
  have hIbd : ∀ ω : Ω, ∀ τ : ℝ, a ≤ τ → τ ≤ a + T →
      ‖∫ u in a..τ, fcf5Drift R X (Torus.realMode k) u ω‖ₑ
        ≤ ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ :=
    fun ω τ hτa hτT => S7FCF5M_int_enorm_le (fun u => fcf5Drift R X (Torus.realMode k) u ω) hτa hτT
  -- measurability
  have hEa : Measurable fun ω => ‖fcf5Eta R X (Torus.realMode k) a ω‖ₑ :=
    S7FCF5M_fixed_meas R P X₀ W X hprep (Torus.realMode k) hmeas_k (Real.sqrt 2)
      (fun x => Torus.abs_realMode_le k x) ha
  have hET : Measurable fun ω => ‖fcf5Eta R X (Torus.realMode k) (a + T) ω‖ₑ :=
    S7FCF5M_fixed_meas R P X₀ W X hprep (Torus.realMode k) hmeas_k (Real.sqrt 2)
      (fun x => Torus.abs_realMode_le k x) haT
  have hZm : Measurable fun ω => ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ :=
    S7FCF5M_window_meas R P X₀ W X hprep k ha T
  haveI : Countable (fcf5Rat a T) := (S7FCF5M_rat_countable a T).to_subtype
  have hYm : Measurable fun ω => ⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ :=
    Measurable.iSup fun t : fcf5Rat a T => ((((hMm t.1).sub (hMm a)).enorm))
  -- pointwise (almost sure) bounds
  have hS : ∀ᵐ ω ∂P, (⨆ t ∈ fcf5Rat a T, ‖fcf5Eta R X (Torus.realMode k) t ω‖ₑ)
      ≤ ‖fcf5Eta R X (Torus.realMode k) a ω‖ₑ + (⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ)
        + ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ := by
    filter_upwards [hid'] with ω hω
    refine iSup₂_le fun t ht => ?_
    have hmem := S7FCF5M_rat_mem ht
    have hY : ‖M t ω - M a ω‖ₑ ≤ ⨆ s : fcf5Rat a T, ‖M s ω - M a ω‖ₑ :=
      le_iSup (fun s : fcf5Rat a T => ‖M s ω - M a ω‖ₑ) ⟨t, ht⟩
    calc ‖fcf5Eta R X (Torus.realMode k) t ω‖ₑ
        ≤ ‖fcf5Eta R X (Torus.realMode k) a ω‖ₑ + ‖M t ω - M a ω‖ₑ
            + ‖∫ u in a..t, fcf5Drift R X (Torus.realMode k) u ω‖ₑ :=
          (S7FCF5M_pt _ _ _ _ _ (hω t hmem.1 hmem.2)).1
      _ ≤ _ := add_le_add (add_le_add le_rfl hY) (hIbd ω t hmem.1 hmem.2)
  have hF : ∀ᵐ ω ∂P, ‖M (a + T) ω - M a ω‖ₑ
      ≤ ‖fcf5Eta R X (Torus.realMode k) (a + T) ω‖ₑ + ‖fcf5Eta R X (Torus.realMode k) a ω‖ₑ
        + ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ := by
    filter_upwards [hid'] with ω hω
    exact (S7FCF5M_pt _ _ _ _ _ (hω (a + T) (by linarith) le_rfl)).2.trans
      (add_le_add (add_le_add le_rfl le_rfl) (hIbd ω (a + T) (by linarith) le_rfl))
  have hYle : ∀ ω : Ω, (⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ)
      ≤ ⨆ t ∈ Set.Icc a (a + T), ‖M t ω - M a ω‖ₑ := fun ω =>
    iSup_le fun t => le_iSup₂_of_le (f := fun s _ => ‖M s ω - M a ω‖ₑ) t.1
      (S7FCF5M_rat_mem t.2) le_rfl
  -- moments
  have mAq : ∫⁻ ω, ‖fcf5Eta R X (Torus.realMode k) a ω‖ₑ ^ q ∂P
      ≤ ENNReal.ofReal (Ax * Lattice.jp k.1 ^ (2 * q)) :=
    (hAx k N hN P X₀ W X hprep a ha).trans
      (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hAx0 hJq))
  have mAp_a : ∫⁻ ω, ‖fcf5Eta R X (Torus.realMode k) a ω‖ₑ ^ p ∂P
      ≤ ENNReal.ofReal (Ap * Lattice.jp k.1 ^ (2 * p)) :=
    (hAp k N hN P X₀ W X hprep a ha).trans
      (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hAp0 hJp))
  have mAp_T : ∫⁻ ω, ‖fcf5Eta R X (Torus.realMode k) (a + T) ω‖ₑ ^ p ∂P
      ≤ ENNReal.ofReal (Ap * Lattice.jp k.1 ^ (2 * p)) :=
    (hAp k N hN P X₀ W X hprep (a + T) haT).trans
      (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hAp0 hJp))
  have mZp : ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ) ^ p ∂P
      ≤ ENNReal.ofReal (max Czp 0 * Lattice.jp k.1 ^ (2 * p)) :=
    (hCzp N hN P X₀ W X hprep a ha k).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hJpn))
  have mZq : ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ) ^ q ∂P
      ≤ ENNReal.ofReal (max Czq 0 * Lattice.jp k.1 ^ (2 * q)) :=
    (hCzq N hN P X₀ W X hprep a ha k).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hJqn))
  -- the endpoint moment at exponent `p`: `E ‖M_{a+T} - M_a‖ₑ^p ≤ L_p J^{2p}`
  have hPF : ∫⁻ ω, ‖M (a + T) ω - M a ω‖ₑ ^ p ∂P
      ≤ ENNReal.ofReal (Lp * Lattice.jp k.1 ^ (2 * p)) := by
    have h1 := S7FCF5M_split3 P (r := p) hp1.le hET hEa hZm hF
    refine h1.trans ?_
    rw [S7FCF5M_two_rpow]
    have e1 : ∫⁻ ω, (‖fcf5Eta R X (Torus.realMode k) (a + T) ω‖ₑ) ^ p ∂P
        ≤ ENNReal.ofReal (Ap * Lattice.jp k.1 ^ (2 * p)) := mAp_T
    have e2 : ∫⁻ ω, (‖fcf5Eta R X (Torus.realMode k) a ω‖ₑ) ^ p ∂P
        ≤ ENNReal.ofReal (Ap * Lattice.jp k.1 ^ (2 * p)) := mAp_a
    have e3 : ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ) ^ p ∂P
        ≤ ENNReal.ofReal (max Czp 0 * Lattice.jp k.1 ^ (2 * p)) := mZp
    calc _ ≤ ENNReal.ofReal ((2:ℝ) ^ (p - 1)) * (ENNReal.ofReal ((2:ℝ) ^ (p - 1)) *
            (ENNReal.ofReal (Ap * Lattice.jp k.1 ^ (2 * p)) + ENNReal.ofReal (Ap * Lattice.jp k.1 ^ (2 * p)))
          + ENNReal.ofReal (max Czp 0 * Lattice.jp k.1 ^ (2 * p))) := by
          gcongr
      _ = ENNReal.ofReal ((2:ℝ) ^ (p - 1) * ((2:ℝ) ^ (p - 1) * (Ap * Lattice.jp k.1 ^ (2 * p)
            + Ap * Lattice.jp k.1 ^ (2 * p)) + max Czp 0 * Lattice.jp k.1 ^ (2 * p))) :=
          S7FCF5M_ofReal_lin (by positivity) (mul_nonneg hAp0 hJpn) (mul_nonneg hAp0 hJpn)
            (mul_nonneg (le_max_right _ _) hJpn)
      _ ≤ ENNReal.ofReal (Lp * Lattice.jp k.1 ^ (2 * p)) :=
          ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hLp]; ring))
  -- the window supremum of the endpoint-free sup `Y` at exponent `p`, and at exponent `q`
  have hYp : ∫⁻ ω, (⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ) ^ p ∂P
      ≤ ENNReal.ofReal (Fp * Lattice.jp k.1 ^ (2 * p)) := by
    have hB1 := HRS.MC.Sec7.S7FCF5B.fcf5_B1_shifted_doob_proof P ℱ M hMart hMc p hp1 a hT.le
    calc ∫⁻ ω, (⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ) ^ p ∂P
        ≤ ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖M t ω - M a ω‖ₑ) ^ p ∂P :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow (hYle ω) (by linarith)
      _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ‖M (a + T) ω - M a ω‖ₑ ^ p ∂P := hB1
      _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) * ENNReal.ofReal (Lp * Lattice.jp k.1 ^ (2 * p)) :=
          by gcongr
      _ = ENNReal.ofReal (Fp * Lattice.jp k.1 ^ (2 * p)) := by
          rw [← ENNReal.ofReal_mul hK0, hFp]
          congr 1
          ring
  have hYq : ∫⁻ ω, (⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ) ^ q ∂P
      ≤ ENNReal.ofReal (Ly * Lattice.jp k.1 ^ (2 * q)) := by
    calc ∫⁻ ω, (⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ) ^ q ∂P
        ≤ (∫⁻ ω, (⨆ t : fcf5Rat a T, ‖M t ω - M a ω‖ₑ) ^ p ∂P) ^ (q / p) :=
          S7FCF5M_lyap P hq hqp hYm
      _ ≤ (ENNReal.ofReal (Fp * Lattice.jp k.1 ^ (2 * p))) ^ (q / p) :=
          ENNReal.rpow_le_rpow hYp (div_nonneg hq0 hp0.le)
      _ = ENNReal.ofReal ((Fp * Lattice.jp k.1 ^ (2 * p)) ^ (q / p)) :=
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hFp0 hJpn) (div_nonneg hq0 hp0.le)
      _ = ENNReal.ofReal (Ly * Lattice.jp k.1 ^ (2 * q)) := by
          congr 1
          rw [hLy, Real.mul_rpow hFp0 hJpn, ← Real.rpow_mul hJ0, show 2 * p * (q / p) = 2 * q by
            field_simp]
  -- the final split at exponent `q`
  have hSq := S7FCF5M_split3 P (r := q) hq hEa hYm hZm hS
  refine hSq.trans ?_
  rw [S7FCF5M_two_rpow]
  calc _ ≤ ENNReal.ofReal ((2:ℝ) ^ (q - 1)) * (ENNReal.ofReal ((2:ℝ) ^ (q - 1)) *
          (ENNReal.ofReal (Ax * Lattice.jp k.1 ^ (2 * q)) + ENNReal.ofReal (Ly * Lattice.jp k.1 ^ (2 * q)))
        + ENNReal.ofReal (max Czq 0 * Lattice.jp k.1 ^ (2 * q))) := by
        gcongr
    _ = ENNReal.ofReal ((2:ℝ) ^ (q - 1) * ((2:ℝ) ^ (q - 1) * (Ax * Lattice.jp k.1 ^ (2 * q)
          + Ly * Lattice.jp k.1 ^ (2 * q)) + max Czq 0 * Lattice.jp k.1 ^ (2 * q))) :=
        S7FCF5M_ofReal_lin (by positivity) (mul_nonneg hAx0 hJqn) (mul_nonneg hLy0 hJqn)
          (mul_nonneg (le_max_right _ _) hJqn)
    _ = ENNReal.ofReal (Cfin * Lattice.jp k.1 ^ (2 * q)) := by
        congr 1
        rw [hCfin]
        ring

end HRS.MC.Sec7.S7FCF5M

end
