import HRS.Commutator.Torus.NRSTAux29

/-!
# NRS-T, part 30: the Riesz transform bound on the torus (transference)
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_toReal_inv_ofReal {p : ℝ} (hp : 0 < p) :
    ((ENNReal.ofReal p)⁻¹).toReal = 1 / p := by
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, one_div]

set_option maxHeartbeats 400000 in
/-- Per-scale inequality. -/
lemma nrstr_riesz_step (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (mm : 𝔼 → ℂ) {r c : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hc : 0 < c) (hφ : ∀ y : 𝔼, ‖y‖ ≤ r → c ≤ ‖nrstr_phi (d := d) y‖)
    {CU : ℝ} (hUp : ∀ (M : ℕ) {G : Torus d → ℂ}, Continuous G →
      eLpNorm (fun y : 𝔼 => nrstr_phi (d := d) ((((d : ℝ) * ((M : ℝ) + 1) / r)⁻¹) • y) *
        G (Torus.mk y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CU * (ENNReal.ofReal ((((d : ℝ) * ((M : ℝ) + 1) / r)) ^ d)) ^ (1 / p) *
          eLpNorm G (ENNReal.ofReal p) volume)
    {Cx : ℝ≥0∞} (f : NRST.TPA d) (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth)
    (hθf : ∀ k ∈ f.coeff.support,
      θ (Lattice.toEuc k) = mm (Lattice.toEuc k))
    (hRs : ∀ N : ℝ, ∀ hN : 1 ≤ N, ∃ Rs : SchwartzMap 𝔼 ℂ,
      (∀ x, Rs x = nrstg_T θ (nrstr_W f N (by linarith)) x) ∧
        eLpNorm (⇑Rs) (ENNReal.ofReal p) volume ≤
          Cx * eLpNorm (⇑(nrstr_W f N (by linarith))) (ENNReal.ofReal p) volume) :
    ∃ CE : ℝ, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ M : ℕ,
      ENNReal.ofReal c * ENNReal.ofReal ((r / d) ^ d) ^ (1 / p) *
        eLpNorm (NRST.ev (NRST.mulSeq (fun k => mm (Lattice.toEuc k)) f))
          (ENNReal.ofReal p) volume ≤
      Cx * ENNReal.ofReal CU * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume +
        ENNReal.ofReal (CE / ((d : ℝ) * ((M : ℝ) + 1) / r)) * B := by
  classical
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hPt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set Gf : NRST.TPA d := NRST.mulSeq (fun k => mm (Lattice.toEuc k)) f
    with hGf
  obtain ⟨K, hK⟩ := leibt_wt_finite (d := d) (ENNReal.ofReal p)
  have hKfin := hK K le_rfl
  obtain ⟨CE0, kk, hCE0, herr⟩ := nrstg_error_bound θ hθ (nrstr_phi (d := d)) K
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑' i, ‖f.coeff i‖ * (1 + ‖Lattice.toEuc i‖) ^ kk := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; exact tsum_nonneg fun i => by positivity
  have hsupp0 : ∀ i, i ∉ f.coeff.support → f.coeff i = 0 := fun i hi => by simpa using hi
  have hsum : ∀ n : ℕ, Summable fun i => ‖f.coeff i‖ * (1 + ‖Lattice.toEuc i‖) ^ n := fun n =>
    summable_of_ne_finset_zero (s := f.coeff.support) fun i hi => by simp [hsupp0 i hi]
  have hGsum : ∀ y : 𝔼, HasSum (fun i => f.coeff i * θ (Lattice.toEuc i) * leibt_e (Lattice.toEuc i) y)
      (NRST.ev Gf (Torus.mk y)) := by
    intro y
    have e : NRST.ev Gf (Torus.mk y) = ∑ k ∈ f.coeff.support,
        f.coeff k * θ (Lattice.toEuc k) * leibt_e (Lattice.toEuc k) y := by
      unfold NRST.ev
      rw [Finsupp.sum_of_support_subset _ (NRST.supp_mulSeq_subset _ f) _ (fun i _ => by simp)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [NRST.coeff_mulSeq, nrstr_mode_eq, hθf k hk]
      ring
    rw [e]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    simp [hsupp0 k hk]
  refine ⟨CE0 * T, eLpNorm (leibt_wt d K) (ENNReal.ofReal p) volume, hKfin.ne, fun M => ?_⟩
  set N : ℝ := (d : ℝ) * ((M : ℝ) + 1) / r with hN
  have hN1 : 1 ≤ N := by
    rw [hN, le_div_iff₀ hr]
    have : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    nlinarith
  have hN0 : 0 < N := by linarith
  obtain ⟨Rs, hRsval, hRsle⟩ := hRs N hN1
  set W : SchwartzMap 𝔼 ℂ := nrstr_W f N hN0 with hW
  have hpt : ∀ x : 𝔼, ‖Rs x - nrstr_phi (d := d) (N⁻¹ • x) * NRST.ev Gf (Torus.mk x)‖ ≤
      (CE0 * T * N⁻¹) * leibt_wt d K (N⁻¹ • x) := by
    intro x
    have := herr f.coeff Lattice.toEuc hsum (fun y => NRST.ev Gf (Torus.mk y)) (⇑W) W rfl hGsum hN1
      (fun y => by exact nrstr_W_hasSum f N hN0 y) x
    rw [← hT] at this
    rw [hRsval x, mul_comm (nrstr_phi _) _]
    simpa [leibt_wt, mul_assoc] using this
  have hcontG : Continuous fun x : 𝔼 => nrstr_phi (d := d) (N⁻¹ • x) * NRST.ev Gf (Torus.mk x) := by
    have hφc : Continuous (nrstr_phi (d := d)) := (nrstr_phi (d := d)).continuous
    have hmk : Continuous (Torus.mk : 𝔼 → Torus d) := HRS.Torus.continuous_mk
    have hev : Continuous (NRST.ev Gf) := NRST.continuous_ev Gf
    have hsm : Continuous fun x : 𝔼 => N⁻¹ • x := by fun_prop
    exact (hφc.comp hsm).mul (hev.comp hmk)
  have herrL : eLpNorm (fun x : 𝔼 => Rs x - nrstr_phi (d := d) (N⁻¹ • x) * NRST.ev Gf (Torus.mk x))
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (CE0 * T * N⁻¹) * (ENNReal.ofReal (N ^ d) ^ (1 / p) *
        eLpNorm (leibt_wt d K) (ENNReal.ofReal p) volume) := by
    have h1 : eLpNorm (fun x : 𝔼 => Rs x - nrstr_phi (d := d) (N⁻¹ • x) * NRST.ev Gf (Torus.mk x))
        (ENNReal.ofReal p) volume ≤
        eLpNorm ((CE0 * T * N⁻¹) • (fun x : 𝔼 => leibt_wt d K (N⁻¹ • x))) (ENNReal.ofReal p) volume := by
      refine eLpNorm_mono (Rs.continuous.sub hcontG).aestronglyMeasurable fun x => ?_
      refine (hpt x).trans ?_
      show _ ≤ ‖(CE0 * T * N⁻¹) * leibt_wt d K (N⁻¹ • x)‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ CE0 * T * N⁻¹)
        (leibt_wt_nonneg K _))]
    refine h1.trans (le_of_eq ?_)
    rw [eLpNorm_const_smul, leibt_wt_dilate_le K hN0, Real.enorm_eq_ofReal (by positivity),
      nrstr_toReal_inv_ofReal hp0]
  -- lower bound
  have hlow := nrstr_lower_bound hd hr hc hφ hP0 hPt M (G := NRST.ev Gf) (NRST.continuous_ev Gf)
  rw [ENNReal.toReal_ofReal hp0.le] at hlow
  -- triangle
  have htri : eLpNorm (fun y : 𝔼 => nrstr_phi (d := d) (N⁻¹ • y) * NRST.ev Gf (Torus.mk y))
      (ENNReal.ofReal p) volume ≤
      eLpNorm (⇑Rs) (ENNReal.ofReal p) volume +
        eLpNorm (fun x : 𝔼 => Rs x - nrstr_phi (d := d) (N⁻¹ • x) * NRST.ev Gf (Torus.mk x))
          (ENNReal.ofReal p) volume := by
    have e : (fun y : 𝔼 => nrstr_phi (d := d) (N⁻¹ • y) * NRST.ev Gf (Torus.mk y)) =
        (⇑Rs) - (fun x : 𝔼 => Rs x - nrstr_phi (d := d) (N⁻¹ • x) * NRST.ev Gf (Torus.mk x)) := by
      funext x; simp
    rw [e]
    exact eLpNorm_sub_le hP1
  -- upper bound for W
  have hWup : eLpNorm (⇑W) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal CU * ENNReal.ofReal (N ^ d) ^ (1 / p) *
        eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume := by
    have := hUp M (NRST.continuous_ev f)
    refine le_trans (le_of_eq ?_) this
    congr 1
    funext y
    rw [hW, nrstr_W_apply, mul_comm]
    rfl
  -- comparison of scale factors
  set Λ : ℝ≥0∞ := ENNReal.ofReal (N ^ d) ^ (1 / p) with hΛ
  have hΛ0 : Λ ≠ 0 := by
    rw [hΛ]
    refine (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_ne_top).ne'
  have hΛt : Λ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hscale : ENNReal.ofReal ((r / d) ^ d) ^ (1 / p) * Λ ≤
      ENNReal.ofReal ((2 * ((M : ℝ) + 1 / 2)) ^ d) ^ (1 / p) := by
    rw [hΛ, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by positivity)
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have : r / d * N = (M : ℝ) + 1 := by
      rw [hN]; field_simp
    rw [this]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hmain : ENNReal.ofReal c * (ENNReal.ofReal ((r / d) ^ d) ^ (1 / p) * Λ) *
      eLpNorm (NRST.ev Gf) (ENNReal.ofReal p) volume ≤
      Λ * (Cx * ENNReal.ofReal CU * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume +
        ENNReal.ofReal (CE0 * T * N⁻¹) * eLpNorm (leibt_wt d K) (ENNReal.ofReal p) volume) := by
    calc ENNReal.ofReal c * (ENNReal.ofReal ((r / d) ^ d) ^ (1 / p) * Λ) *
          eLpNorm (NRST.ev Gf) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal c * ENNReal.ofReal ((2 * ((M : ℝ) + 1 / 2)) ^ d) ^ (1 / p) *
          eLpNorm (NRST.ev Gf) (ENNReal.ofReal p) volume := by gcongr
      _ ≤ _ := hlow
      _ ≤ eLpNorm (⇑Rs) (ENNReal.ofReal p) volume + _ := htri
      _ ≤ Cx * (ENNReal.ofReal CU * Λ * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume) +
          ENNReal.ofReal (CE0 * T * N⁻¹) * (Λ * eLpNorm (leibt_wt d K) (ENNReal.ofReal p) volume) := by
          gcongr
          exact hRsle.trans (by gcongr)
      _ = _ := by ring
  have hmain' : Λ * (ENNReal.ofReal c * ENNReal.ofReal ((r / d) ^ d) ^ (1 / p) *
      eLpNorm (NRST.ev Gf) (ENNReal.ofReal p) volume) ≤
      Λ * (Cx * ENNReal.ofReal CU * eLpNorm (NRST.ev f) (ENNReal.ofReal p) volume +
        ENNReal.ofReal (CE0 * T * N⁻¹) * eLpNorm (leibt_wt d K) (ENNReal.ofReal p) volume) := by
    refine le_trans (le_of_eq ?_) hmain
    ring
  have := (ENNReal.mul_le_mul_iff_right hΛ0 hΛt).1 hmain'
  simpa [div_eq_mul_inv] using this

end HRS.Commutator.TorusNote
