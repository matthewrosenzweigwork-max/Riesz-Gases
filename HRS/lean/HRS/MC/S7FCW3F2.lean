import HRS.MC.S7FCW3F1
import HRS.MC.S7S7bAux1
import HRS.MD.EQRemStatic
import HRS.Equilibrium.LocalDivTaylor
import HRS.Energy.StaticLimitGauss
import HRS.Equilibrium.FieldSingAux
import HRS.Sections.Q38bAux1
import HRS.PDE.EnergyR2Fn

/-!
# FC-F2 (moments of the commutator modes `N F_N^{h_{∇e_k}}`), packet `S7FCW3`

Proves `s7_FC_F2_B_proof` (copied verbatim into `S7FCPlan.lean` by the Tie file).  Route: item 3 of `alltime_Lp`
(exponential pair estimate under `Q_t`) applied to `h/M` with `M = (K·d·3√2+1)⟨k⟩²` (scaling gives the `⟨k⟩^{2}`
growth), `y^s ≤ 1 + n! e^y`, item 1 (density of the law of `X_t` in `L^p(Q_t)`) and Hölder.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

theorem s7fcw3_expbound {y s : ℝ} (hy : 0 ≤ y) (hs : 0 ≤ s) (n : ℕ) (hn : s ≤ (n : ℝ)) :
    y ^ s ≤ 1 + (n.factorial : ℝ) * Real.exp y := by
  have h1 := s7fcw3_rpow_le hy hs n hn
  have h2 : y ^ n / (n.factorial : ℝ) ≤ Real.exp y := Real.pow_div_factorial_le_exp y hy n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h3 : y ^ n ≤ (n.factorial : ℝ) * Real.exp y := by
    have := (div_le_iff₀ hf).1 h2
    linarith [mul_comm (Real.exp y) (n.factorial : ℝ)]
  linarith

theorem s7fcw3_pt2 {x a y q s : ℝ} (hy : 0 ≤ y) (hxy : x = a * y) (ha : 0 ≤ a) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (n : ℕ) (hn : q * s ≤ (n : ℝ)) :
    ENNReal.ofReal (x ^ q) ^ s ≤ ENNReal.ofReal (a ^ (q * s)) +
      ENNReal.ofReal (a ^ (q * s) * (n.factorial : ℝ)) * ENNReal.ofReal (Real.exp y) := by
  have hx : 0 ≤ x := by rw [hxy]; exact mul_nonneg ha hy
  have hpow : x ^ (q * s) ≤ a ^ (q * s) + a ^ (q * s) * (n.factorial : ℝ) * Real.exp y := by
    rw [hxy, Real.mul_rpow ha hy]
    have := s7fcw3_expbound hy (mul_nonneg hq hs) n hn
    have hA := Real.rpow_nonneg ha (q * s)
    nlinarith
  calc ENNReal.ofReal (x ^ q) ^ s = ENNReal.ofReal (x ^ (q * s)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hx _) hs, Real.rpow_mul hx]
    _ ≤ ENNReal.ofReal (a ^ (q * s) + a ^ (q * s) * (n.factorial : ℝ) * Real.exp y) :=
        ENNReal.ofReal_le_ofReal hpow
    _ = ENNReal.ofReal (a ^ (q * s)) + ENNReal.ofReal (a ^ (q * s) * (n.factorial : ℝ)) *
          ENNReal.ofReal (Real.exp y) := by
        rw [ENNReal.ofReal_add (Real.rpow_nonneg ha _)
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg ha _) (Nat.cast_nonneg _)) (Real.exp_pos y).le),
          ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg ha _) (Nat.cast_nonneg _))]

theorem s7fcw3_rpow_split {u K q s : ℝ} (hu : 0 ≤ u) (hK : 0 ≤ K) (hs : 0 < s) :
    (u ^ (q * s) * K) ^ (1 / s) = u ^ q * K ^ (1 / s) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hu _) hK, ← Real.rpow_mul hu]
  have h : q * s * (1 / s) = q := by field_simp
  rw [h]

theorem s7fcw3_chain1 {Y : Type*} [MeasurableSpace Y] (Law Q : Measure Y)
    [Measure.HaveLebesgueDecomposition Law Q] {p p' : ℝ} (hpq : p.HolderConjugate p') (hLQ : Law ≪ Q)
    {A : ℝ≥0∞} (hA : (∫⁻ y, Law.rnDeriv Q y ^ p ∂Q) ^ (1 / p) ≤ A)
    (G : Y → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y, G y ∂Law ≤ A * (∫⁻ y, G y ^ p' ∂Q) ^ (1 / p') := by
  have hm1 : Measurable (Law.rnDeriv Q) := Measure.measurable_rnDeriv _ _
  calc ∫⁻ y, G y ∂Law = ∫⁻ y, Law.rnDeriv Q y * G y ∂Q :=
        (lintegral_rnDeriv_mul hLQ hG.aemeasurable).symm
    _ ≤ (∫⁻ y, Law.rnDeriv Q y ^ p ∂Q) ^ (1 / p) * (∫⁻ y, G y ^ p' ∂Q) ^ (1 / p') :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq Q hpq hm1.aemeasurable hG.aemeasurable
    _ ≤ A * (∫⁻ y, G y ^ p' ∂Q) ^ (1 / p') := mul_le_mul' hA le_rfl

theorem s7fcw3_me_smul {N : ℕ} (c : ℝ) (h : Torus d → Torus d → ℝ) (X : Config d N)
    (μ : Measure (Torus d)) :
    modulatedEnergy (fun x y => c * h x y) X μ = c * modulatedEnergy h X μ := by
  unfold modulatedEnergy
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

theorem s7fcw3_me_meas {N : ℕ} (h : Torus d → Torus d → ℝ) (hh : Measurable (Function.uncurry h))
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] :
    Measurable (fun X : Config d N => modulatedEnergy h X μ) := by
  have h1 : Measurable fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => by
      have hc : Measurable (fun X : Config d N => (X i, X j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact hh.comp hc
  have hI : Measurable fun x : Torus d => ∫ y, h x y ∂μ :=
    (hh.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have h2 : Measurable fun X : Config d N => ∑ i, ∫ y, h (X i) y ∂μ :=
    Finset.measurable_sum _ fun i _ => hI.comp (measurable_pi_apply i)
  unfold modulatedEnergy
  exact ((measurable_const.mul h1).sub (measurable_const.mul h2)).add measurable_const

theorem s7fcw3_hT_q66 {s : ℝ} {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    hTransport d s φ = Q66.q66_hv d s (fun j => Torus.partialDeriv j φ) := by
  funext x y
  rw [HRS.LocalDivAux.hTransport_eq s φ hφ]
  rfl

theorem s7fcw3_hT_meas_symm {s : ℝ} (hsd : s < d) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (Function.uncurry (hTransport d s φ)) ∧
      ∀ x y, hTransport d s φ x y = hTransport d s φ y x := by
  rw [s7fcw3_hT_q66 hφ]
  exact ⟨Q66.q66_hv_measurable hsd fun j => HRS.StaticLimitAux.continuous_of_smooth
    (HRS.LocalDivAux.isSmooth_partialDeriv hφ j), Q66.q66_hv_symm hsd _⟩

/-- Envelope of the transport kernel of a mode, with an explicit `⟨k⟩²` growth. -/
theorem s7fcw3_hT_env {s K0 c : ℝ} (hK0 : 0 ≤ K0) (k : NonzeroLattice d)
    (henv : ∀ (v : Fin d → Torus d → ℝ) (L : Fin d → ℝ), (∀ j, 0 ≤ L j) →
      (∀ j, HRS.KernelGrad.IsLipschitz (L j) (v j)) → ∀ x y : Torus d,
      |Q66.q66_hv d s v x y| ≤ K0 * (∑ j, L j) * (periodicRiesz d s (x - y) + c))
    (x y : Torus d) (hg : 0 ≤ periodicRiesz d s (x - y) + c) :
    |hTransport d s (Torus.realMode k) x y| ≤
      (K0 * d * (3 * Real.sqrt 2) + 1) * Lattice.jp k.1 ^ 2 * (periodicRiesz d s (x - y) + c) := by
  rw [s7fcw3_hT_q66 (HRS.FieldSingAux.isSmooth_realMode k)]
  have hck : Torus.IsCk 2 (Torus.realMode k : Torus d → ℝ) := HRS.q38b_isCk_realMode k 2
  have hL := henv (fun j => Torus.partialDeriv j (Torus.realMode k : Torus d → ℝ))
    (fun _ => Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ))
    (fun _ => HRS.MD.EQRem.eqrem_cbNorm_nonneg 2 _)
    (fun j => HRS.PDE.R2Aux.isLipschitz_partialDeriv hck j) x y
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hL
  have hcb := HRS.MD.EQRem.eqrem_realMode_cb k
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hj2 : 0 ≤ Lattice.jp k.1 ^ 2 := sq_nonneg _
  have e1 : K0 * (d * Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ)) ≤
      K0 * d * (3 * Real.sqrt 2 * Lattice.jp k.1 ^ 2) := by
    have := mul_le_mul_of_nonneg_left hcb (mul_nonneg hK0 hd0)
    nlinarith
  have e2 : K0 * d * (3 * Real.sqrt 2 * Lattice.jp k.1 ^ 2) ≤
      (K0 * d * (3 * Real.sqrt 2) + 1) * Lattice.jp k.1 ^ 2 := by
    nlinarith
  calc _ ≤ K0 * (↑d * Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ)) *
        (periodicRiesz d s (x - y) + c) := hL
    _ ≤ (K0 * d * (3 * Real.sqrt 2) + 1) * Lattice.jp k.1 ^ 2 * (periodicRiesz d s (x - y) + c) :=
        mul_le_mul_of_nonneg_right (e1.trans e2) hg

theorem s7fcw3_core2 (R : Regime d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
          Integrable (fun ω => |(N : ℝ) * modulatedEnergy (hTransport d R.D.s (Torus.realMode k))
            (X t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q) P ∧
          ∫ ω, |(N : ℝ) * modulatedEnergy (hTransport d R.D.s (Torus.realMode k))
            (X t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q ∂P ≤ C0 * Lattice.jp k.1 ^ (2 * q) := by
  obtain ⟨p, hp1, C1, hC1⟩ := movfin_alltime_item1 R
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
  have hp'0 : 0 ≤ p.conjExponent := hpq.symm.nonneg
  have hp'pos : 0 < p.conjExponent := hpq.symm.pos
  have hp0 : 0 < p := by linarith
  obtain ⟨K0, c, hK0, hc0, hwc, henv⟩ := HRS.MC.Sec7.S7b.s7b_envelope R.hd (alltime_hs0 R) R.hs
  obtain ⟨cB, CB, hcB, hI3⟩ := alltime_item3 R c hwc 1
  set n : ℕ := ⌈q * p.conjExponent⌉₊ with hn
  set A : ℝ := K0 * d * (3 * Real.sqrt 2) + 1 with hA
  have hA0 : 0 < A := by
    have : 0 ≤ K0 * d * (3 * Real.sqrt 2) := by positivity
    linarith
  refine ⟨max C1 0 * (A / cB) ^ q * (1 + (n.factorial : ℝ) * max CB 0) ^ (1 / p.conjExponent),
    mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (div_nonneg hA0.le hcB.le) _))
      (Real.rpow_nonneg (by have := le_max_right CB 0; positivity) _), ?_⟩
  intro N hN Ω _ P _ X₀ W X hprep t ht k
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hρ : IsProbDensity (R.ρ t) := (alltime_traj R t).mf.density t ⟨ht, le_rfl⟩
  haveI : IsProbabilityMeasure (withDensityReal (R.ρ t)) := isProb_withDensityReal hρ
  obtain ⟨m₀, M₀, hm₀, hbdR⟩ := R.bounds
  haveI hQprob : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d R.D.s) N R.β
      (withDensityReal (R.ρ t))) :=
    HRS.Q32c.q32c_Q_isProb (d := d) (by have := R.hd; omega) (alltime_hs0 R) (alltime_hsd R) R.hβ
      (Λ := max 1 M₀) (le_max_left _ _) hρ (fun x => (hbdR t ht x).2.trans (le_max_right _ _))
      (by omega)
  obtain ⟨hac, hdens⟩ := hC1 N hN P X₀ W X hprep t ht
  have hXm : Measurable (X t.toNNReal) := (hprep.solution t).adapted t.toNNReal
  -- the mode and its scaled version
  set jk : ℝ := Lattice.jp k.1 with hjk
  have hjk1 : 1 ≤ jk := Torus.jp_ge_one k.1
  set M : ℝ := A * jk ^ 2 with hM
  have hM0 : 0 < M := by positivity
  set h : Torus d → Torus d → ℝ := hTransport d R.D.s (Torus.realMode k) with hh
  have hhm : Measurable (Function.uncurry h) :=
    (s7fcw3_hT_meas_symm (alltime_hsd R) (HRS.FieldSingAux.isSmooth_realMode k)).1
  have hhs : ∀ x y, h x y = h y x :=
    (s7fcw3_hT_meas_symm (alltime_hsd R) (HRS.FieldSingAux.isSmooth_realMode k)).2
  have hbd : ∀ x y : Torus d, x ≠ y → |h x y| ≤ M * (periodicRiesz d R.D.s (x - y) + c) := fun x y hxy =>
    s7fcw3_hT_env hK0 k henv x y (by linarith [hwc (x - y) (sub_ne_zero.2 hxy)])
  set h' : Torus d → Torus d → ℝ := fun x y => (1 / M) * h x y with hh'
  have hh'm : Measurable (Function.uncurry h') := by
    have e : Function.uncurry h' = fun p => (1 / M) * Function.uncurry h p := by
      funext p; rfl
    rw [e]
    exact measurable_const.mul hhm
  have hh's : ∀ x y, h' x y = h' y x := fun x y => by
    simp only [hh']
    rw [hhs x y]
  have hh'b : ∀ x y, x ≠ y → |h' x y| ≤ 1 * (periodicRiesz d R.D.s (x - y) + c) := by
    intro x y hxy
    have h1 := hbd x y hxy
    simp only [hh']
    rw [abs_mul, abs_of_pos (one_div_pos.2 hM0)]
    calc 1 / M * |h x y| ≤ 1 / M * (M * (periodicRiesz d R.D.s (x - y) + c)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 * (periodicRiesz d R.D.s (x - y) + c) := by field_simp
  set μ : Measure (Torus d) := withDensityReal (R.ρ t) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set Q : Measure (Config d N) := modulatedGibbs (periodicRiesz d R.D.s) N R.β μ with hQ
  haveI : IsProbabilityMeasure Q := hQprob
  have hrel : ∀ X : Config d N, modulatedEnergy h X μ = M * modulatedEnergy h' X μ := by
    intro X
    have e : h = fun x y => M * h' x y := by
      funext x y
      simp only [hh']
      field_simp
    rw [e]
    exact s7fcw3_me_smul M h' X μ
  set a : ℝ := M / cB with ha_def
  have ha0 : 0 ≤ a := div_nonneg hM0.le hcB.le
  have hcB' : cB ≠ 0 := hcB.ne'
  have hF : ∀ X : Config d N, |(N : ℝ) * modulatedEnergy h X μ| =
      a * (cB * N * |modulatedEnergy h' X μ|) := by
    intro X
    rw [hrel X, show (N : ℝ) * (M * modulatedEnergy h' X μ) = M * N * modulatedEnergy h' X μ by ring,
      abs_mul, abs_mul, abs_of_pos hM0, abs_of_pos hNpos, ha_def]
    field_simp
  have hnq : q * p.conjExponent ≤ (n : ℝ) := Nat.le_ceil _
  have hGm : Measurable (fun Y : Config d N => ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h Y μ| ^ q)) :=
    ((continuous_abs.measurable.comp ((s7fcw3_me_meas h hhm μ).const_mul (N : ℝ))).pow_const q).ennreal_ofReal
  have hpt : ∀ X : Config d N, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h X μ| ^ q) ^ p.conjExponent ≤
      ENNReal.ofReal (a ^ (q * p.conjExponent)) + ENNReal.ofReal (a ^ (q * p.conjExponent) * (n.factorial : ℝ)) *
        ENNReal.ofReal (Real.exp (cB * N * |modulatedEnergy h' X μ|)) := fun X =>
    s7fcw3_pt2 (by positivity) (hF X) ha0 (by linarith) hp'0 n hnq
  have hint1 : ∫⁻ X, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h X μ| ^ q) ^ p.conjExponent ∂Q ≤
      ENNReal.ofReal (a ^ (q * p.conjExponent) * (1 + (n.factorial : ℝ) * max CB 0)) := by
    have hI : ∫⁻ X, ENNReal.ofReal (Real.exp (cB * N * |modulatedEnergy h' X μ|)) ∂Q ≤
        ENNReal.ofReal (max CB 0) :=
      (hI3 N hN t ht h' hh'm hh's hh'b).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    calc ∫⁻ X, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h X μ| ^ q) ^ p.conjExponent ∂Q
        ≤ ∫⁻ X, (ENNReal.ofReal (a ^ (q * p.conjExponent)) + ENNReal.ofReal (a ^ (q * p.conjExponent) *
            (n.factorial : ℝ)) * ENNReal.ofReal (Real.exp (cB * N * |modulatedEnergy h' X μ|))) ∂Q :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (a ^ (q * p.conjExponent)) + ENNReal.ofReal (a ^ (q * p.conjExponent) *
            (n.factorial : ℝ)) * ∫⁻ X, ENNReal.ofReal (Real.exp (cB * N * |modulatedEnergy h' X μ|)) ∂Q := by
          rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (a ^ (q * p.conjExponent)) + ENNReal.ofReal (a ^ (q * p.conjExponent) *
            (n.factorial : ℝ)) * ENNReal.ofReal (max CB 0) :=
          add_le_add le_rfl (mul_le_mul' le_rfl hI)
      _ = ENNReal.ofReal (a ^ (q * p.conjExponent) * (1 + (n.factorial : ℝ) * max CB 0)) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg ha0 _) (Nat.cast_nonneg _)),
            ← ENNReal.ofReal_add (Real.rpow_nonneg ha0 _)
              (mul_nonneg (mul_nonneg (Real.rpow_nonneg ha0 _) (Nat.cast_nonneg _)) (le_max_right _ _))]
          congr 1
          ring
  -- density of the law
  have hA_ : (∫⁻ y, (Measure.map (X t.toNNReal) P).rnDeriv Q y ^ p ∂Q) ^ (1 / p) ≤
      ENNReal.ofReal (max C1 0) := by
    have h := hdens
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne'
      ENNReal.ofReal_ne_top (Measure.measurable_rnDeriv _ _).aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hchain := s7fcw3_chain1 (Measure.map (X t.toNNReal) P) Q hpq hac hA_
    (fun Y : Config d N => ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h Y μ| ^ q)) hGm
  have hKc : 0 ≤ 1 + (n.factorial : ℝ) * max CB 0 := by
    have := le_max_right CB 0
    positivity
  have hjq : (Lattice.jp k.1 ^ 2) ^ q = Lattice.jp k.1 ^ (2 * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ Lattice.jp k.1)]
    norm_num
  have ha_split : a ^ q = (A / cB) ^ q * Lattice.jp k.1 ^ (2 * q) := by
    rw [ha_def, hM, show A * Lattice.jp k.1 ^ 2 / cB = (A / cB) * Lattice.jp k.1 ^ 2 by ring,
      Real.mul_rpow (div_nonneg hA0.le hcB.le) (sq_nonneg _), hjq]
  have hfin : ∫⁻ Y, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h Y μ| ^ q)
      ∂(Measure.map (X t.toNNReal) P) ≤
      ENNReal.ofReal ((max C1 0 * (A / cB) ^ q * (1 + (n.factorial : ℝ) * max CB 0) ^ (1 / p.conjExponent)) *
        Lattice.jp k.1 ^ (2 * q)) := by
    refine hchain.trans ?_
    calc ENNReal.ofReal (max C1 0) * (∫⁻ Y, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h Y μ| ^ q) ^ p.conjExponent ∂Q) ^ (1 / p.conjExponent)
        ≤ ENNReal.ofReal (max C1 0) * (ENNReal.ofReal (a ^ (q * p.conjExponent) * (1 + (n.factorial : ℝ) * max CB 0))) ^ (1 / p.conjExponent) :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hint1 (one_div_nonneg.2 hp'0))
      _ = ENNReal.ofReal (max C1 0 * ((a ^ (q * p.conjExponent) * (1 + (n.factorial : ℝ) * max CB 0)) ^ (1 / p.conjExponent))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg ha0 _) hKc) (one_div_nonneg.2 hp'0),
            ENNReal.ofReal_mul (le_max_right _ _)]
      _ = ENNReal.ofReal ((max C1 0 * (A / cB) ^ q * (1 + (n.factorial : ℝ) * max CB 0) ^ (1 / p.conjExponent)) *
            Lattice.jp k.1 ^ (2 * q)) := by
          congr 1
          rw [s7fcw3_rpow_split ha0 hKc hp'pos, ha_split]
          ring
  have hFm' : Measurable (fun Y : Config d N => |(N : ℝ) * modulatedEnergy h Y μ| ^ q) :=
    (continuous_abs.measurable.comp ((s7fcw3_me_meas h hhm μ).const_mul (N : ℝ))).pow_const q
  have hPfin : ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h (X t.toNNReal ω) μ| ^ q) ∂P ≤
      ENNReal.ofReal ((max C1 0 * (A / cB) ^ q * (1 + (n.factorial : ℝ) * max CB 0) ^ (1 / p.conjExponent)) *
        Lattice.jp k.1 ^ (2 * q)) := by
    calc ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h (X t.toNNReal ω) μ| ^ q) ∂P
        = ∫⁻ Y, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy h Y μ| ^ q) ∂(Measure.map (X t.toNNReal) P) :=
          (lintegral_map hGm hXm).symm
      _ ≤ _ := hfin
  have hC0 : 0 ≤ (max C1 0 * (A / cB) ^ q * (1 + (n.factorial : ℝ) * max CB 0) ^ (1 / p.conjExponent)) *
      Lattice.jp k.1 ^ (2 * q) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (div_nonneg hA0.le hcB.le) _))
      (Real.rpow_nonneg hKc _)) (Real.rpow_nonneg (by linarith) _)
  have hnn : 0 ≤ᵐ[P] (fun ω => |(N : ℝ) * modulatedEnergy h (X t.toNNReal ω) μ| ^ q) :=
    ae_of_all _ fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hmeasω : AEStronglyMeasurable (fun ω => |(N : ℝ) * modulatedEnergy h (X t.toNNReal ω) μ| ^ q) P :=
    (hFm'.comp hXm).aestronglyMeasurable
  refine ⟨⟨hmeasω, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hPfin ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeasω]
    exact ENNReal.toReal_le_of_le_ofReal hC0 hPfin

theorem s7_FC_F2_B_proof (R : Regime d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
          Integrable (fun ω => |(N : ℝ) * modulatedEnergy (hTransport d R.D.s (Torus.realMode k))
            (X t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q) P ∧
          ∫ ω, |(N : ℝ) * modulatedEnergy (hTransport d R.D.s (Torus.realMode k))
            (X t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q ∂P ≤ C * Lattice.jp k.1 ^ (2 * q)
  := by
  obtain ⟨C0, hC0, hcore⟩ := s7fcw3_core2 R q hq
  exact ⟨C0, fun N hN Ω _ P _ X₀ W X hprep t ht k => hcore N hN P X₀ W X hprep t ht k⟩

end HRS.MC.Sec7.S7FCW3

end
