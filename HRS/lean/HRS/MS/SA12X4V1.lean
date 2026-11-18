import HRS.MS.SA12X4V0
import HRS.MS.SA12X4W4

/-!
# S.A.12 (SA12X4) V1: the moving weighted cell energy versus the continuous weighted jet energy

With `Z_m(u)(x) = ∑_{n ≤ m} C(m,n) ∑_{idx} (∂^{idx}u(x))²` and `J_m(u) = ∫ ϖ Z_m(u)`, `ϖ = ⟨x⟩^{-(d+3)}`:
`∑_y ω_y 𝓕_y(τ) = ∫ Z_m(u) ∑_y ω_y (χ_y^τ)²` (`sa12x4_W_eq`), hence `c J_m(u) ≤ ∑_y ω_y 𝓕_y(τ)`
(`sa12x4_J_le_W`, by the growth of the flow) and, at `τ = 0`, `∑_y ω_y 𝓕_y(0) ≤ K J_m(u)` (`sa12x4_W0_le_J`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The jet density `Z_m(u)(x) = ∑_{n ≤ m} C(m,n) ∑_{idx} (∂^{idx}u(x))²`. -/
def sa12x4_Z (m : ℕ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), (Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2

/-- The continuous weighted jet energy `∫ ϖ Z_m(u)`. -/
def sa12x4_J (m : ℕ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (sa12x4_Z m u x)

theorem sa12x4_Z_nonneg (m : ℕ) (u : Euc d → ℝ) (x : Euc d) : 0 ≤ sa12x4_Z m u x :=
  Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun idx _ => sq_nonneg _)

theorem sa12x4_Z_meas (m : ℕ) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) : Measurable (sa12x4_Z m u) := by
  unfold sa12x4_Z
  refine Finset.measurable_sum _ fun n _ => ?_
  refine Measurable.const_mul (Finset.measurable_sum _ fun idx _ => ?_) _
  exact ((sa12z3_pd_contDiff_inf hu idx).continuous.measurable).pow_const 2

/-- The cell energy as an integral. -/
theorem sa12x4_cellEnergy_eq (m : ℕ) (w u : Euc d → ℝ)
    (hint : ∀ {n : ℕ} (idx : Fin n → Fin d), Integrable (fun x => (w x * partialDeriv idx u x) ^ 2)) :
    jetSq m w u = ∫ x, w x ^ 2 * sa12x4_Z m u x := by
  unfold jetSq sa12x4_Z
  have h1 : ∀ n : ℕ, ∫ x, w x ^ 2 * ((Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2) =
      (Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, ∫ x, (w x * partialDeriv idx u x) ^ 2 := by
    intro n
    have : ∀ x, w x ^ 2 * ((Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2) =
        (Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, (w x * partialDeriv idx u x) ^ 2 := by
      intro x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun idx _ => ?_
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_finset_sum _ fun idx _ => hint idx]
  rw [show (fun x => w x ^ 2 * ∑ n ∈ Finset.range (m + 1), (Nat.choose m n : ℝ) *
      ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2) = fun x => ∑ n ∈ Finset.range (m + 1),
        w x ^ 2 * ((Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2) from
    funext fun x => Finset.mul_sum _ _ _]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun n _ => (h1 n).symm
  · intro n _
    have : ∀ x, w x ^ 2 * ((Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2) =
        (Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d, (w x * partialDeriv idx u x) ^ 2 := by
      intro x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun idx _ => ?_
      ring
    simp_rw [this]
    exact (integrable_finset_sum _ fun idx _ => hint idx).const_mul _


theorem sa12x4_W_eq (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ)
    (hci : Continuous (Function.invFun (Ψ τ))) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u)
    (hint : ∀ (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
      Integrable (fun x => (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx u x) ^ 2)) :
    ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d y) u) =
      ∫⁻ x, ENNReal.ofReal (sa12x4_Z m u x) *
        ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) := by
  have hadv : ∀ y : Fin d → ℤ, Measurable (fun x => advCutoff χ Ψ τ (cellPt d y) x) := fun y => by
    unfold advCutoff
    exact hχ.1.continuous.measurable.comp ((hci.sub continuous_const).measurable)
  have hZ := sa12x4_Z_meas m hu
  have hE : ∀ y, ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d y) u) =
      ∫⁻ x, ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) * ENNReal.ofReal (sa12x4_Z m u x) := by
    intro y
    unfold cellEnergy
    rw [sa12x4_cellEnergy_eq m _ u (fun {n} idx => hint y idx)]
    have hi : Integrable (fun x => advCutoff χ Ψ τ (cellPt d y) x ^ 2 * sa12x4_Z m u x) := by
      have : (fun x => advCutoff χ Ψ τ (cellPt d y) x ^ 2 * sa12x4_Z m u x) = fun x =>
          ∑ n ∈ Finset.range (m + 1), (Nat.choose m n : ℝ) * ∑ idx : Fin n → Fin d,
            (advCutoff χ Ψ τ (cellPt d y) x * partialDeriv idx u x) ^ 2 := by
        funext x
        unfold sa12x4_Z
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun idx _ => ?_
        ring
      rw [this]
      exact integrable_finset_sum _ fun n _ => (integrable_finset_sum _ fun idx _ => hint y idx).const_mul _
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (sa12x4_Z_nonneg m u x))]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
  simp_rw [hE]
  have hm1 : ∀ y, Measurable (fun x => ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) *
      ENNReal.ofReal (sa12x4_Z m u x)) := fun y =>
    (ENNReal.measurable_ofReal.comp ((hadv y).pow_const 2)).mul (ENNReal.measurable_ofReal.comp hZ)
  have : ∀ y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
      ∫⁻ x, ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) * ENNReal.ofReal (sa12x4_Z m u x) =
      ∫⁻ x, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        (ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2) * ENNReal.ofReal (sa12x4_Z m u x)) := by
    intro y
    rw [lintegral_const_mul _ (hm1 y)]
  simp_rw [this]
  rw [← lintegral_tsum fun y => ((hm1 y).const_mul _).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  ring

theorem sa12x4_J_le_W (hd : 1 ≤ d) {m : ℕ} {Cb T : ℝ} (hT : 0 ≤ T) {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T)
    {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u)
    (hint : ∀ (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
      Integrable (fun x => (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx u x) ^ 2)) :
    ENNReal.ofReal ((4 * Real.exp (Cb * τ)) ^ (-((d : ℝ) + 3))) * sa12x4_J m u ≤
      ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d y) u) := by
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have hci : Continuous (Function.invFun (Ψ τ)) := (hfl.contDiff_inv τ hτ).continuous
  rw [sa12x4_W_eq m χ hχ Ψ τ hci hu hint, sa12x4_J, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  obtain ⟨y0, hy0⟩ := HRS.MS.UniqC3.exists_cellPt_near hd (Function.invFun (Ψ τ) x)
  have hadv1 : advCutoff χ Ψ τ (cellPt d y0) x = 1 := by
    unfold advCutoff
    exact hχ.2.2.2.2 _ (by rw [mem_closedBall_zero_iff]; linarith [hy0])
  have hle : ENNReal.ofReal ((4 * Real.exp (Cb * τ)) ^ (-p)) * ENNReal.ofReal (jbracket x ^ (-p)) ≤
      ENNReal.ofReal (jbracket (cellPt d y0) ^ (-p)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hj : ∀ v : Euc d, 1 ≤ jbracket v := fun v => HRS.MS.Lc.lc2_jb_ge_one v
    have hjp : ∀ v : Euc d, 0 < jbracket v := fun v => lt_of_lt_of_le one_pos (hj v)
    have hg := (sa12x4_flow_growth hT hb hΨ hτ (Function.invFun (Ψ τ) x)).2
    rw [hfl.inv_right τ hτ x] at hg
    -- `⟨cellPt y0⟩ ≤ 4 e^{Cb τ} ⟨x⟩`
    have hnorm : ‖cellPt d y0‖ ≤ ‖Function.invFun (Ψ τ) x‖ + 1 / 2 := by
      calc ‖cellPt d y0‖ = ‖Function.invFun (Ψ τ) x - (Function.invFun (Ψ τ) x - cellPt d y0)‖ := by congr 1; abel
        _ ≤ ‖Function.invFun (Ψ τ) x‖ + ‖Function.invFun (Ψ τ) x - cellPt d y0‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hle1 : jbracket (cellPt d y0) ≤ 1 + ‖cellPt d y0‖ := by
      unfold jbracket
      rw [show (1 + ‖cellPt d y0‖) = Real.sqrt ((1 + ‖cellPt d y0‖) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (cellPt d y0)])
    have hx2 := HRS.MS.Lc.lc2_le_jb x
    have hE0 : 0 < Real.exp (Cb * τ) := Real.exp_pos _
    have hA : jbracket (cellPt d y0) ≤ 4 * Real.exp (Cb * τ) * jbracket x := by
      calc jbracket (cellPt d y0) ≤ 1 + ‖cellPt d y0‖ := hle1
        _ ≤ 2 * (1 + ‖Function.invFun (Ψ τ) x‖) := by linarith [norm_nonneg (Function.invFun (Ψ τ) x)]
        _ ≤ 2 * ((1 + ‖x‖) * Real.exp (Cb * τ)) := by linarith
        _ ≤ 2 * (2 * jbracket x * Real.exp (Cb * τ)) := by
            gcongr
        _ = 4 * Real.exp (Cb * τ) * jbracket x := by ring
    have h2 : (jbracket (cellPt d y0)) ^ p ≤ (4 * Real.exp (Cb * τ) * jbracket x) ^ p :=
      Real.rpow_le_rpow (hjp _).le hA hp0
    rw [Real.mul_rpow (by positivity) (hjp x).le] at h2
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (hjp x).le, Real.rpow_neg (hjp _).le]
    have hP1 : 0 < (4 * Real.exp (Cb * τ)) ^ p := Real.rpow_pos_of_pos (by positivity) p
    have hP2 : 0 < jbracket x ^ p := Real.rpow_pos_of_pos (hjp x) p
    have hP3 : 0 < jbracket (cellPt d y0) ^ p := Real.rpow_pos_of_pos (hjp _) p
    rw [← one_div, ← one_div, ← one_div, one_div_mul_one_div, div_le_div_iff₀ (by positivity) hP3]
    nlinarith [h2]
  calc ENNReal.ofReal ((4 * Real.exp (Cb * τ)) ^ (-p)) *
        (ENNReal.ofReal (jbracket x ^ (-p)) * ENNReal.ofReal (sa12x4_Z m u x))
      = (ENNReal.ofReal ((4 * Real.exp (Cb * τ)) ^ (-p)) * ENNReal.ofReal (jbracket x ^ (-p))) *
          ENNReal.ofReal (sa12x4_Z m u x) := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal (jbracket (cellPt d y0) ^ (-p)) * ENNReal.ofReal (sa12x4_Z m u x) := by gcongr
    _ ≤ _ := by
        rw [mul_comm]
        gcongr
        calc ENNReal.ofReal (jbracket (cellPt d y0) ^ (-p)) =
            ENNReal.ofReal (jbracket (cellPt d y0) ^ (-p)) * ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y0) x ^ 2) := by
              rw [hadv1]; simp
          _ ≤ _ := ENNReal.le_tsum (f := fun y => ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) *
              ENNReal.ofReal (advCutoff χ Ψ τ (cellPt d y) x ^ 2)) y0


/-- The unadvected weighted cutoff sum is bounded by the weight: `∑_y ω_y χ(x - y)² ≤ K ϖ(x)`. -/
theorem sa12x4_cover_sum_le (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Euc d, ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
      ENNReal.ofReal (χ (x - cellPt d y) ^ 2) ≤ ENNReal.ofReal K * ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3))) := by
  classical
  obtain ⟨N, hN⟩ := sa12x4_lattice_count hd 2
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set Cw : ℝ := (Real.sqrt 2 * Real.sqrt (1 + (2 : ℝ) ^ 2)) ^ p with hCw
  have hCw0 : 0 ≤ Cw := Real.rpow_nonneg (by positivity) _
  refine ⟨N * Cw, by positivity, fun x => ?_⟩
  obtain ⟨S, hSc, hS⟩ := hN x
  have hzero : ∀ y ∉ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) * ENNReal.ofReal (χ (x - cellPt d y) ^ 2) = 0 := by
    intro y hy
    have hfar : ¬ ‖cellPt d y - x‖ ≤ 2 := fun h => hy (hS y h)
    have : χ (x - cellPt d y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hχ.2.2.1 hmem
      rw [mem_ball_zero_iff, norm_sub_rev] at this
      exact hfar this.le
    rw [this]; simp
  rw [tsum_eq_sum hzero]
  have hterm : ∀ y ∈ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) * ENNReal.ofReal (χ (x - cellPt d y) ^ 2) ≤
      ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p)) := by
    intro y _
    by_cases hnear : ‖x - cellPt d y‖ ≤ 2
    · have hc := sa12x4_varpi_comp p hp0 2 x (cellPt d y) hnear
      have hχ1 : χ (x - cellPt d y) ^ 2 ≤ 1 := by
        have h := hχ.2.2.2.1 (x - cellPt d y)
        nlinarith [h.1, h.2]
      calc ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) * ENNReal.ofReal (χ (x - cellPt d y) ^ 2)
          ≤ ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) * 1 := by
            gcongr
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hχ1
        _ = ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) := mul_one _
        _ ≤ ENNReal.ofReal (Cw * jbracket x ^ (-p)) := ENNReal.ofReal_le_ofReal hc
        _ = _ := ENNReal.ofReal_mul hCw0
    · have : χ (x - cellPt d y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχ.2.2.1 hmem
        rw [mem_ball_zero_iff] at this
        exact hnear this.le
      rw [this]; simp
  calc ∑ y ∈ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) * ENNReal.ofReal (χ (x - cellPt d y) ^ 2)
      ≤ ∑ _y ∈ S, ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p)) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p))) := by simp
    _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p))) := by
        gcongr
    _ = ENNReal.ofReal (N * Cw) * ENNReal.ofReal (jbracket x ^ (-p)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

theorem sa12x4_W0_le_J (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d}, IsNegDriftFlow T b Ψ →
      ∀ {u : Euc d → ℝ}, ContDiff ℝ ∞ u →
      (∀ (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
        Integrable (fun x => (advCutoff χ Ψ 0 (cellPt d z) x * partialDeriv idx u x) ^ 2)) →
      ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (cellEnergy m χ Ψ 0 (cellPt d y) u) ≤ ENNReal.ofReal K * sa12x4_J m u := by
  obtain ⟨K, hK0, hK⟩ := sa12x4_cover_sum_le hd χ hχ
  refine ⟨K, hK0, fun {T b Ψ} hΨ {u} hu hint => ?_⟩
  have hci : Continuous (Function.invFun (Ψ 0)) := by
    have : Function.invFun (Ψ 0) = id := by
      funext x
      have h := Function.invFun_eq (f := Ψ 0) ⟨x, hΨ.init x⟩
      rw [hΨ.init] at h
      exact h
    rw [this]; exact continuous_id
  rw [sa12x4_W_eq m χ hχ Ψ 0 hci hu hint, sa12x4_J, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  have hinv : ∀ y, advCutoff χ Ψ 0 (cellPt d y) x = χ (x - cellPt d y) := by
    intro y
    unfold advCutoff
    have : Function.invFun (Ψ 0) x = x := by
      have h := Function.invFun_eq (f := Ψ 0) ⟨x, hΨ.init x⟩
      rw [hΨ.init] at h
      exact h
    rw [this]
  simp_rw [hinv]
  calc ENNReal.ofReal (sa12x4_Z m u x) * ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (χ (x - cellPt d y) ^ 2)
      ≤ ENNReal.ofReal (sa12x4_Z m u x) * (ENNReal.ofReal K * ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3)))) := by
        gcongr; exact hK x
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12X4
