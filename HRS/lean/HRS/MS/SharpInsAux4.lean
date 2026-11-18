import HRS.MS.SharpInsAux3

/-!
# HRS.MS.SharpInsAux4 -- S7.6 `sharp_insertion_radius`: the diagonal integral `I_L` and arithmetic

Packet S76, namespace `HRS.MS.S76`, helper prefix `s76_`.  No frozen file is edited.

* `s76_IL`: `I_L(x) = ∫_{|u|<L} k_s(u) ρ(x - c u) du`; `s76_IL_ofReal` (link with the `lintegral` of
  `s76_diag_lintegral`), `s76_IL_bounds` (`0 ≤ I_L ≤ 2 A_{d,s} M`), `s76_IL_approx`
  (`|I_L - 2A ρ(x)| ≤ 2A Λ c L + M C_k L^{d-2s}` for a `Λ`-Lipschitz density, `c > 0`, `L > 0`);
* `s76_sqrt_prod`, `s76_arith`: the powers of `λ = β/N`, `L` and `t` in the core estimate `s76_core`
  (`2s > d`, so `J_s(u) = 1 + u^{p-2}`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.S76

open HRS.Whole (rieszKernel EucConfig)

variable {d : ℕ} {s : ℝ}

/-! ### The compensated kernel -/

theorem s76_kk_facts (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) :
    (∀ u : Euc d, 0 ≤ HRS.Whole.Q34.kk (‖u‖ ^ (-s))) ∧
      Integrable (fun u : Euc d => HRS.Whole.Q34.kk (‖u‖ ^ (-s))) ∧
      ∫ u : Euc d, HRS.Whole.Q34.kk (‖u‖ ^ (-s)) = 2 * HRS.Whole.biasConst d s := by
  obtain ⟨h1, -, h3, h4, -⟩ := HRS.Whole.compensated_kernel hd hs hsd
  exact ⟨h1, h3, h4⟩

/-- `I_L(x) = ∫_{|u|<L} k_s(u) ρ(x - c u) du`. -/
def s76_IL (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (c L : ℝ) (x : Euc d) : ℝ :=
  ∫ u in ball (0 : Euc d) L, HRS.Whole.Q34.kk (‖u‖ ^ (-s)) * ρ (x - c • u)

theorem s76_IL_integrable (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (c : ℝ) (x : Euc d) :
    Integrable (fun u : Euc d => HRS.Whole.Q34.kk (‖u‖ ^ (-s)) * ρ (x - c • u)) := by
  obtain ⟨hk0, hkint, -⟩ := s76_kk_facts hd hs hsd
  refine Integrable.mono' (hkint.mul_const M) ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact ((HRS.Whole.Q34.measurable_kk_norm_rpow (d := d) s).mul
      (hρ.measurable.comp (measurable_const.sub (measurable_const_smul c)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 u) (hρ.nonneg _))]
    exact mul_le_mul_of_nonneg_left (hM _) (hk0 u)

theorem s76_IL_ofReal (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (c L : ℝ) (x : Euc d) :
    ENNReal.ofReal (s76_IL d s ρ c L x) =
      ∫⁻ u in ball (0 : Euc d) L, ENNReal.ofReal (ρ (x - c • u)) *
        ENNReal.ofReal (HRS.Whole.Q34.kk (‖u‖ ^ (-s))) := by
  obtain ⟨hk0, -, -⟩ := s76_kk_facts hd hs hsd
  have hI := (s76_IL_integrable hd hs hsd hρ hM c x).integrableOn (s := ball (0 : Euc d) L)
  unfold s76_IL
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun u => mul_nonneg (hk0 u) (hρ.nonneg _))]
  refine lintegral_congr fun u => ?_
  rw [ENNReal.ofReal_mul (hk0 u), mul_comm]

theorem s76_IL_bounds (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (c L : ℝ) (x : Euc d) :
    0 ≤ s76_IL d s ρ c L x ∧
      s76_IL d s ρ c L x ≤ M * (2 * HRS.Whole.biasConst d s) := by
  obtain ⟨hk0, hkint, hK⟩ := s76_kk_facts hd hs hsd
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hI := (s76_IL_integrable hd hs hsd hρ hM c x).integrableOn (s := ball (0 : Euc d) L)
  refine ⟨setIntegral_nonneg measurableSet_ball fun u _ => mul_nonneg (hk0 u) (hρ.nonneg _), ?_⟩
  unfold s76_IL
  calc ∫ u in ball (0 : Euc d) L, HRS.Whole.Q34.kk (‖u‖ ^ (-s)) * ρ (x - c • u)
      ≤ ∫ u in ball (0 : Euc d) L, HRS.Whole.Q34.kk (‖u‖ ^ (-s)) * M := by
        refine setIntegral_mono hI (hkint.mul_const M).integrableOn fun u => ?_
        exact mul_le_mul_of_nonneg_left (hM _) (hk0 u)
    _ ≤ ∫ u : Euc d, HRS.Whole.Q34.kk (‖u‖ ^ (-s)) * M :=
        setIntegral_le_integral (hkint.mul_const M)
          (Filter.Eventually.of_forall fun u => mul_nonneg (hk0 u) hM0)
    _ = M * (2 * HRS.Whole.biasConst d s) := by
        rw [integral_mul_const, hK]; ring

theorem s76_IL_approx (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {Λ : ℝ≥0}
    (hΛ : LipschitzWith Λ ρ) {c : ℝ} (hc : 0 < c) {L : ℝ} (hL : 0 < L) {Ck : ℝ}
    (hCk : ∀ L : ℝ, 0 < L → ∫ u in {u : Euc d | L ≤ ‖u‖}, HRS.Whole.Q34.kk (‖u‖ ^ (-s)) ≤
      Ck * L ^ ((d : ℝ) - 2 * s)) (x : Euc d) :
    |s76_IL d s ρ c L x - 2 * HRS.Whole.biasConst d s * ρ x| ≤
      2 * HRS.Whole.biasConst d s * (Λ * c * L) + M * (Ck * L ^ ((d : ℝ) - 2 * s)) := by
  obtain ⟨hk0, hkint, hK⟩ := s76_kk_facts hd hs hsd
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  set k : Euc d → ℝ := fun u => HRS.Whole.Q34.kk (‖u‖ ^ (-s)) with hkdef
  set B : Set (Euc d) := ball (0 : Euc d) L with hB
  have hBm : MeasurableSet B := measurableSet_ball
  have hBc : Bᶜ = {u : Euc d | L ≤ ‖u‖} := by
    ext u; simp [hB, not_lt]
  have hsplit := integral_add_compl hBm hkint
  have hIB : IntegrableOn k B := hkint.integrableOn
  have hIBc : IntegrableOn k Bᶜ := hkint.integrableOn
  have hint1 : IntegrableOn (fun u => k u * ρ (x - c • u)) B :=
    (s76_IL_integrable hd hs hsd hρ hM c x).integrableOn
  have hint2 : IntegrableOn (fun u => k u * ρ x) B := hIB.mul_const _
  have hint3 : IntegrableOn (fun u => k u * (ρ (x - c • u) - ρ x)) B :=
    (hint1.sub hint2).congr_fun (fun u _ => by simp only [Pi.sub_apply]; ring) hBm
  have e1 : s76_IL d s ρ c L x - 2 * HRS.Whole.biasConst d s * ρ x =
      (∫ u in B, k u * (ρ (x - c • u) - ρ x)) - ρ x * ∫ u in Bᶜ, k u := by
    have h1 : ∫ u in B, k u * (ρ (x - c • u) - ρ x) =
        (∫ u in B, k u * ρ (x - c • u)) - ∫ u in B, k u * ρ x := by
      rw [← integral_sub hint1 hint2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      ring
    rw [h1, integral_mul_const, ← hK, ← hsplit]
    unfold s76_IL
    ring
  rw [e1]
  have hLip : ∀ u : Euc d, |ρ (x - c • u) - ρ x| ≤ Λ * (c * ‖u‖) := by
    intro u
    have := hΛ.dist_le_mul (x - c • u) x
    rw [Real.dist_eq, dist_eq_norm] at this
    have e : x - c • u - x = -(c • u) := by abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hc.le] at this
    exact this
  have hfirst : |∫ u in B, k u * (ρ (x - c • u) - ρ x)| ≤ 2 * HRS.Whole.biasConst d s * (Λ * c * L) := by
    have hpt : ∀ u ∈ B, ‖k u * (ρ (x - c • u) - ρ x)‖ ≤ k u * (Λ * c * L) := by
      intro u hu
      have hu' : ‖u‖ < L := by simpa [hB] using hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 u)]
      refine mul_le_mul_of_nonneg_left ((hLip u).trans ?_) (hk0 u)
      have : c * ‖u‖ ≤ c * L := mul_le_mul_of_nonneg_left hu'.le hc.le
      calc (Λ : ℝ) * (c * ‖u‖) ≤ Λ * (c * L) := mul_le_mul_of_nonneg_left this (NNReal.coe_nonneg Λ)
        _ = Λ * c * L := by ring
    calc |∫ u in B, k u * (ρ (x - c • u) - ρ x)|
        = ‖∫ u in B, k u * (ρ (x - c • u) - ρ x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ u in B, ‖k u * (ρ (x - c • u) - ρ x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in B, k u * (Λ * c * L) :=
          setIntegral_mono_on hint3.norm (hIB.mul_const _) hBm hpt
      _ = (∫ u in B, k u) * (Λ * c * L) := integral_mul_const _ _
      _ ≤ (2 * HRS.Whole.biasConst d s) * (Λ * c * L) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← hK]
          exact setIntegral_le_integral hkint (Filter.Eventually.of_forall hk0)
  have hsecond : |ρ x * ∫ u in Bᶜ, k u| ≤ M * (Ck * L ^ ((d : ℝ) - 2 * s)) := by
    rw [abs_mul, abs_of_nonneg (hρ.nonneg x),
      abs_of_nonneg (setIntegral_nonneg hBm.compl fun u _ => hk0 u)]
    refine mul_le_mul (hM x) ?_ (setIntegral_nonneg hBm.compl fun u _ => hk0 u) hM0
    rw [hBc]
    exact hCk L hL
  calc |(∫ u in B, k u * (ρ (x - c • u) - ρ x)) - ρ x * ∫ u in Bᶜ, k u|
      ≤ |∫ u in B, k u * (ρ (x - c • u) - ρ x)| + |ρ x * ∫ u in Bᶜ, k u| := abs_sub _ _
    _ ≤ _ := add_le_add hfirst hsecond

/-! ### Arithmetic -/

theorem s76_sqrt_prod {K1 K2 A u v x y : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hA : 0 ≤ A)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hy : 0 ≤ y) (hxu : x ≤ K1 * A * u ^ 2)
    (hyv : y ≤ K2 * A * v ^ 2) :
    Real.sqrt (x * y) ≤ Real.sqrt (K1 * K2) * (A * (u * v)) := by
  have hx : 0 ≤ x ∨ x < 0 := le_or_gt 0 x
  have h1 : x * y ≤ (K1 * K2) * (A * (u * v)) ^ 2 := by
    rcases hx with hx | hx
    · calc x * y ≤ (K1 * A * u ^ 2) * (K2 * A * v ^ 2) := mul_le_mul hxu hyv hy (by positivity)
        _ = (K1 * K2) * (A * (u * v)) ^ 2 := by ring
    · have : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx.le hy
      exact this.trans (by positivity)
  calc Real.sqrt (x * y) ≤ Real.sqrt ((K1 * K2) * (A * (u * v)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (K1 * K2) * (A * (u * v)) := by
        rw [Real.sqrt_mul (mul_nonneg hK1 hK2), Real.sqrt_sq (by positivity)]

/-- `K₁ = (C₀ + C₀²) (M|S|/(d-s))²`. -/
def s76_K1 (d : ℕ) (s C0 M : ℝ) : ℝ := (C0 + C0 ^ 2) * (M * HRS.sphereArea d / ((d : ℝ) - s)) ^ 2

/-- `K₂ = C_v M|S|/(2s-d)`. -/
def s76_K2 (d : ℕ) (s Cv M : ℝ) : ℝ := Cv * (M * HRS.sphereArea d / (2 * s - (d : ℝ)))

/-- `K₄ = C_v C_r (β^{2-p} + 1)`. -/
def s76_K4 (d : ℕ) (s β Cv Cr : ℝ) : ℝ := Cv * Cr * (β ^ (2 - (d : ℝ) / s) + 1)

/-- `K₃ = 2 √(K₄ K₂)`. -/
def s76_K3 (d : ℕ) (s β M Cv Cr : ℝ) : ℝ :=
  2 * Real.sqrt (s76_K4 d s β Cv Cr * s76_K2 d s Cv M)

theorem s76_arith (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hds : (d : ℝ) < 2 * s)
    {β M C0 Cv Cr : ℝ} (hβ : 0 < β) (hM0 : 0 ≤ M) (hC0 : 0 ≤ C0) (hCv : 0 ≤ Cv) (hCr : 0 ≤ Cr)
    {lam L t n J : ℝ} (hlam : 0 < lam) (hlamβ : lam ≤ β) (hL : 1 ≤ L) (ht : 0 < t) (ht1 : t ≤ 1)
    (hn : 0 ≤ n) (hJ : J = 1 + (t * lam) ^ ((d : ℝ) / s - 2)) :
    n ^ 2 * (C0 * (M * lam * (HRS.sphereArea d * ((lam ^ (1 / s) * L) ^ ((d : ℝ) - s) /
          ((d : ℝ) - s)))) ^ 2 +
        (C0 * (M * lam * (HRS.sphereArea d * ((lam ^ (1 / s) * L) ^ ((d : ℝ) - s) /
          ((d : ℝ) - s))))) ^ 2) +
      Cv * n * (M * lam ^ 2 * (HRS.sphereArea d * ((lam ^ (1 / s) * L) ^ ((d : ℝ) - 2 * s) /
          (2 * s - (d : ℝ))))) +
      2 * Real.sqrt (Cv * n * (lam ^ 2 * (Cr * J)) *
        (Cv * n * (M * lam ^ 2 * (HRS.sphereArea d * ((lam ^ (1 / s) * L) ^ ((d : ℝ) - 2 * s) /
          (2 * s - (d : ℝ))))))) ≤
    s76_K1 d s C0 M * (n ^ 2 * ((lam ^ ((d : ℝ) / s)) ^ 2 * (L ^ ((d : ℝ) - s)) ^ 2)) +
      s76_K2 d s Cv M * (n * lam ^ ((d : ℝ) / s) * L ^ ((d : ℝ) - 2 * s)) +
      s76_K3 d s β M Cv Cr * (n * lam ^ ((d : ℝ) / s) * L ^ (((d : ℝ) - 2 * s) / 2) *
        t ^ (((d : ℝ) / s - 2) / 2)) := by
  have hL0 : 0 < L := by linarith
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have h2m : 0 < 2 * s - (d : ℝ) := by linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hs0]; linarith
  have hp2 : p < 2 := by rw [hp, div_lt_iff₀ hs0]; linarith
  set S : ℝ := HRS.sphereArea d with hS
  have hlp : 0 ≤ lam ^ p := Real.rpow_nonneg hlam.le _
  have hLs : 0 ≤ L ^ ((d : ℝ) - s) := Real.rpow_nonneg hL0.le _
  have hLs2 : 0 ≤ L ^ ((d : ℝ) - 2 * s) := Real.rpow_nonneg hL0.le _
  -- G and BT
  have hG : M * lam * (S * ((lam ^ (1 / s) * L) ^ ((d : ℝ) - s) / ((d : ℝ) - s))) =
      (M * S / ((d : ℝ) - s)) * (lam ^ p * L ^ ((d : ℝ) - s)) := by
    rw [← s76_pow1 hs0 hlam hL0]
    field_simp
  have hBT : M * lam ^ 2 * (S * ((lam ^ (1 / s) * L) ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))) =
      (M * S / (2 * s - (d : ℝ))) * (lam ^ p * L ^ ((d : ℝ) - 2 * s)) := by
    rw [← s76_pow2 hs0 hlam hL0]
    field_simp
  rw [hG, hBT]
  -- first term
  have e1 : n ^ 2 * (C0 * ((M * S / ((d : ℝ) - s)) * (lam ^ p * L ^ ((d : ℝ) - s))) ^ 2 +
      (C0 * ((M * S / ((d : ℝ) - s)) * (lam ^ p * L ^ ((d : ℝ) - s)))) ^ 2) =
      s76_K1 d s C0 M * (n ^ 2 * ((lam ^ p) ^ 2 * (L ^ ((d : ℝ) - s)) ^ 2)) := by
    unfold s76_K1; ring
  have e2 : Cv * n * ((M * S / (2 * s - (d : ℝ))) * (lam ^ p * L ^ ((d : ℝ) - 2 * s))) =
      s76_K2 d s Cv M * (n * lam ^ p * L ^ ((d : ℝ) - 2 * s)) := by
    unfold s76_K2; ring
  -- the square-root term
  set q : ℝ := (p - 2) / 2 with hq
  set u : ℝ := t ^ q with hu
  set v : ℝ := L ^ (((d : ℝ) - 2 * s) / 2) with hv
  have hu0 : 0 ≤ u := Real.rpow_nonneg ht.le _
  have hv0 : 0 ≤ v := Real.rpow_nonneg hL0.le _
  have hu2 : u ^ 2 = t ^ (p - 2) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1; rw [hq]; push_cast; ring
  have hv2 : v ^ 2 = L ^ ((d : ℝ) - 2 * s) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1; push_cast; ring
  have hK2 : 0 ≤ s76_K2 d s Cv M := by
    unfold s76_K2; positivity
  have hK4 : 0 ≤ s76_K4 d s β Cv Cr := by
    unfold s76_K4; positivity
  -- bound on `lam² J`
  have hJ0 : 0 ≤ J := by rw [hJ]; have := Real.rpow_nonneg (mul_nonneg ht.le hlam.le) (p - 2); linarith
  have hlamJ : lam ^ 2 * J ≤ (β ^ (2 - p) + 1) * lam ^ p * t ^ (p - 2) := by
    have h1 : (t * lam) ^ (p - 2) = t ^ (p - 2) * lam ^ (p - 2) := Real.mul_rpow ht.le hlam.le
    have h2 : lam ^ 2 * lam ^ (p - 2) = lam ^ p := by
      rw [← Real.rpow_two, ← Real.rpow_add hlam]; congr 1; ring
    have h3 : lam ^ 2 = lam ^ (2 - p) * lam ^ p := by
      rw [← Real.rpow_add hlam, ← Real.rpow_two]; congr 1; ring
    have h4 : lam ^ (2 - p) ≤ β ^ (2 - p) := Real.rpow_le_rpow hlam.le hlamβ (by linarith)
    have h5 : 1 ≤ t ^ (p - 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
    have h6 : lam ^ 2 ≤ β ^ (2 - p) * lam ^ p := by
      rw [h3]; exact mul_le_mul_of_nonneg_right h4 hlp
    have h7 : lam ^ 2 * J = lam ^ 2 + lam ^ p * t ^ (p - 2) := by
      rw [hJ, h1]
      calc lam ^ 2 * (1 + t ^ (p - 2) * lam ^ (p - 2)) = lam ^ 2 + t ^ (p - 2) * (lam ^ 2 * lam ^ (p - 2)) := by ring
        _ = lam ^ 2 + lam ^ p * t ^ (p - 2) := by rw [h2]; ring
    rw [h7]
    have hb0 : 0 ≤ β ^ (2 - p) * lam ^ p := mul_nonneg (Real.rpow_nonneg hβ.le _) hlp
    have h8 : β ^ (2 - p) * lam ^ p ≤ β ^ (2 - p) * lam ^ p * t ^ (p - 2) := by
      calc β ^ (2 - p) * lam ^ p = β ^ (2 - p) * lam ^ p * 1 := by ring
        _ ≤ β ^ (2 - p) * lam ^ p * t ^ (p - 2) := mul_le_mul_of_nonneg_left h5 hb0
    calc lam ^ 2 + lam ^ p * t ^ (p - 2) ≤ β ^ (2 - p) * lam ^ p * t ^ (p - 2) + lam ^ p * t ^ (p - 2) := by
          linarith
      _ = (β ^ (2 - p) + 1) * lam ^ p * t ^ (p - 2) := by ring
  have hvS : Cv * n * (lam ^ 2 * (Cr * J)) ≤ s76_K4 d s β Cv Cr * (n * lam ^ p) * u ^ 2 := by
    rw [hu2]
    have : Cv * n * (lam ^ 2 * (Cr * J)) = Cv * Cr * n * (lam ^ 2 * J) := by ring
    rw [this]
    unfold s76_K4
    calc Cv * Cr * n * (lam ^ 2 * J) ≤ Cv * Cr * n * ((β ^ (2 - p) + 1) * lam ^ p * t ^ (p - 2)) :=
          mul_le_mul_of_nonneg_left hlamJ (by positivity)
      _ = Cv * Cr * (β ^ (2 - p) + 1) * (n * lam ^ p) * t ^ (p - 2) := by ring
  have hvT : Cv * n * ((M * S / (2 * s - (d : ℝ))) * (lam ^ p * L ^ ((d : ℝ) - 2 * s))) =
      s76_K2 d s Cv M * (n * lam ^ p) * v ^ 2 := by
    rw [hv2]; unfold s76_K2; ring
  have hy0 : 0 ≤ Cv * n * ((M * S / (2 * s - (d : ℝ))) * (lam ^ p * L ^ ((d : ℝ) - 2 * s))) := by
    positivity
  have hsq := s76_sqrt_prod hK4 hK2 (mul_nonneg hn hlp) hu0 hv0 hy0 hvS (le_of_eq hvT)
  have e3 : 2 * Real.sqrt (Cv * n * (lam ^ 2 * (Cr * J)) *
      (Cv * n * ((M * S / (2 * s - (d : ℝ))) * (lam ^ p * L ^ ((d : ℝ) - 2 * s))))) ≤
      s76_K3 d s β M Cv Cr * (n * lam ^ p * v * u) := by
    unfold s76_K3
    calc 2 * Real.sqrt (Cv * n * (lam ^ 2 * (Cr * J)) *
          (Cv * n * ((M * S / (2 * s - (d : ℝ))) * (lam ^ p * L ^ ((d : ℝ) - 2 * s)))))
        ≤ 2 * (Real.sqrt (s76_K4 d s β Cv Cr * s76_K2 d s Cv M) * (n * lam ^ p * (u * v))) := by
          gcongr
      _ = _ := by ring
  linarith [e1, e2, e3]

end HRS.MS.S76
