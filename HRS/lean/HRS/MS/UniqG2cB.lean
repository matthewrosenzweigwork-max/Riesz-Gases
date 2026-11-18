import HRS.MS.UniqG2cA
import HRS.MS.UniqC3e

/-!
# G2c, part B: from the mollified local-energy decay to `z = 0`

`g2c_zero`: if `z τ` has uniformly bounded local `L²` mass and the mollification `z_ε = η_ε * z τ` satisfies
`∫ ς_c^τ z_ε² ≤ C0 ε` for all centres `c` and `0 < ε ≤ 1`, then `z τ = 0` a.e. for every `τ ∈ [0,t]`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqG2c

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1 HRS.MS.UniqC3

variable {d : ℕ}

/-- A compact set is covered by finitely many closed balls of radius `r` with centres in the range of a
surjective map. -/
theorem g2c_cover {f : Euc d → Euc d} (hf : Function.Surjective f) {r : ℝ} (hr : 0 < r)
    {K : Set (Euc d)} (hK : IsCompact K) :
    ∃ s : Finset (Euc d), K ⊆ ⋃ c ∈ s, closedBall (f c) r := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact hK hr
  refine ⟨ht.toFinset.image (Function.surjInv hf), fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
  refine Set.mem_iUnion₂.2 ⟨Function.surjInv hf x, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨x, by simpa using hx, rfl⟩
  · rw [Function.surjInv_eq hf]; exact ball_subset_closedBall hyx

/-- The energy of `m` on a finite union of balls where `ς_c = 1`. -/
theorem g2c_energy_union {m : Euc d → ℝ} {w : Euc d → Euc d → ℝ} (s : Finset (Euc d))
    (e : Euc d → Euc d) (r : ℝ) (hone : ∀ c ∈ s, ∀ x ∈ closedBall (e c) r, w c x = 1)
    (Q : ℝ) (hQ : ∀ c ∈ s, ∫⁻ x, ENNReal.ofReal (w c x * m x ^ 2) ≤ ENNReal.ofReal Q) :
    ∫⁻ x in ⋃ c ∈ s, closedBall (e c) r, ENNReal.ofReal (m x ^ 2) ≤ s.card * ENNReal.ofReal Q := by
  calc ∫⁻ x in ⋃ c ∈ s, closedBall (e c) r, ENNReal.ofReal (m x ^ 2)
      ≤ ∑ c ∈ s, ∫⁻ x in closedBall (e c) r, ENNReal.ofReal (m x ^ 2) := by
        rw [show (⋃ c ∈ s, closedBall (e c) r) = ⋃ c : s, closedBall (e (c : Euc d)) r by ext; simp]
        refine (lintegral_iUnion_le _ _).trans ?_
        rw [tsum_fintype]
        exact (Finset.sum_coe_sort s fun c => ∫⁻ x in closedBall (e c) r, ENNReal.ofReal (m x ^ 2)).le
    _ ≤ ∑ c ∈ s, ENNReal.ofReal Q := by
        refine Finset.sum_le_sum fun c hc => ?_
        calc ∫⁻ x in closedBall (e c) r, ENNReal.ofReal (m x ^ 2)
            = ∫⁻ x in closedBall (e c) r, ENNReal.ofReal (w c x * m x ^ 2) := by
              refine setLIntegral_congr_fun measurableSet_closedBall fun x hx => ?_
              rw [hone c hc x hx, one_mul]
          _ ≤ ∫⁻ x, ENNReal.ofReal (w c x * m x ^ 2) := setLIntegral_le_lintegral _ _
          _ ≤ _ := hQ c hc
    _ = _ := by simp

/-- Real form of the energy bound. -/
theorem g2c_energy_real {m : Euc d → ℝ} (hm : Continuous m) {U : Set (Euc d)} {n : ℕ} {Q : ℝ} (hQ0 : 0 ≤ Q)
    (h : ∫⁻ x in U, ENNReal.ofReal (m x ^ 2) ≤ n * ENNReal.ofReal Q) :
    ∫ x in U, m x ^ 2 ≤ n * Q := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
    ((hm.pow 2).aestronglyMeasurable)]
  have : (n : ℝ≥0∞) * ENNReal.ofReal Q = ENNReal.ofReal (n * Q) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [this] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- `L¹` mass on a compact set from the `L²` mass (AM-GM). -/
theorem g2c_mid {m φ : Euc d → ℝ} (hm : Continuous m) (hφ : Continuous φ) {U : Set (Euc d)}
    (hU : IsCompact U) (hφs : ∀ x, x ∉ U → φ x = 0) {M : ℝ} (hM : ∀ x, |φ x| ≤ M) {Q δ : ℝ}
    (hδ : 0 < δ) (hQ : ∫ x in U, m x ^ 2 ≤ Q) :
    |∫ x, m x * φ x| ≤ M * (δ / 2 * (volume U).toReal + Q / (2 * δ)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hUm : MeasurableSet U := hU.isClosed.measurableSet
  have hUfin : volume U < ⊤ := hU.measure_lt_top
  have hi1 : IntegrableOn (fun x => |m x|) U volume :=
    (hm.abs.continuousOn).integrableOn_compact hU
  have hi2 : IntegrableOn (fun x => m x ^ 2) U volume :=
    ((hm.pow 2).continuousOn).integrableOn_compact hU
  have hi3 : IntegrableOn (fun x => δ / 2 + m x ^ 2 / (2 * δ)) U volume :=
    (integrableOn_const hUfin.ne).add (hi2.div_const _)
  have step1 : ∫ x in U, |m x| ≤ δ / 2 * (volume U).toReal + Q / (2 * δ) := by
    calc ∫ x in U, |m x| ≤ ∫ x in U, (δ / 2 + m x ^ 2 / (2 * δ)) := by
          refine setIntegral_mono_on hi1 hi3 hUm fun x _ => ?_
          rw [← sub_nonneg]
          have e : m x ^ 2 = |m x| ^ 2 := (sq_abs _).symm
          have : δ / 2 + m x ^ 2 / (2 * δ) - |m x| = (|m x| - δ) ^ 2 / (2 * δ) := by
            rw [e]; field_simp; ring
          rw [this]; positivity
      _ = δ / 2 * (volume U).toReal + (∫ x in U, m x ^ 2) / (2 * δ) := by
          have hc : Integrable (fun _ : Euc d => δ / 2) (volume.restrict U) := integrableOn_const hUfin.ne
          have hq : Integrable (fun x => m x ^ 2 / (2 * δ)) (volume.restrict U) := hi2.div_const _
          rw [integral_add hc hq, integral_div (2 * δ) (fun x => m x ^ 2), setIntegral_const]
          simp only [Measure.real, smul_eq_mul]
          ring
      _ ≤ _ := by gcongr
  have hφi : Integrable (fun x => m x * φ x) volume := by
    have hcs : HasCompactSupport φ :=
      HasCompactSupport.of_support_subset_isCompact hU (fun x hx => by
        by_contra h; exact hx (hφs x h))
    exact (hm.mul hφ).integrable_of_hasCompactSupport (hcs.mul_left)
  have hind : Integrable (fun x => U.indicator (fun x => M * |m x|) x) volume :=
    (integrable_indicator_iff hUm).2 (hi1.const_mul M)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hind (Eventually.of_forall fun x => ?_)).trans ?_
  · by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)
    · simp [Set.indicator_of_notMem hx, hφs x hx]
  · rw [integral_indicator hUm, integral_const_mul]
    exact mul_le_mul_of_nonneg_left step1 hM0

/-- Pairing with a fixed smooth compactly supported test function vanishes. -/
theorem g2c_pairing_zero (hd : 1 ≤ d) {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ}
    {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K)
    {z : ℝ → Euc d → ℝ} {B : ℝ} (hzB : ∀ τ ∈ Set.Icc (0:ℝ) t, LocMass B (z τ)) (C0 : ℝ)
    (hE : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ c : Euc d,
      ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * moll d ε (z τ) x ^ 2) ≤ ENNReal.ofReal (C0 * ε))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) t) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) : ∫ x, z τ x * φ x = 0 := by
  have hz := hzB τ hτ
  set L : ℝ := Real.exp (Cb * t) with hL
  have hLpos : 0 < 1 / L := by positivity
  have hsurj : Function.Surjective (Ψ τ) := fun y => ⟨Function.invFun (Ψ τ) y, hF.flow.inv_right τ hτ y⟩
  obtain ⟨s, hs⟩ := g2c_cover hsurj hLpos hφc.isCompact
  set U : Set (Euc d) := ⋃ c ∈ s, closedBall (Ψ τ c) (1 / L) with hU
  have hUc : IsCompact U := s.isCompact_biUnion fun c _ => isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨A, hA0, hA⟩ := g2c_mollTest_close hφ hφc
  set V : ℝ := (volume U).toReal with hV
  set C1 : ℝ := max C0 0 with hC1
  have hC1nn : 0 ≤ C1 := le_max_right _ _
  set n : ℕ := s.card with hn
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |∫ x, z τ x * φ x| ≤
      A * |B| * ε + M * (Real.sqrt ε / 2 * V + n * C1 * Real.sqrt ε / 2) := by
    intro ε hε hε1
    have hmc : Continuous (moll d ε (z τ)) := (moll_contDiff hε hz.locallyIntegrable).continuous
    have hQ : ∀ c ∈ s, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * moll d ε (z τ) x ^ 2) ≤
        ENNReal.ofReal (C1 * ε) := fun c _ =>
      (hE ε hε hε1 τ hτ c).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_max_left _ _) hε.le))
    have hU2 := g2c_energy_union (m := moll d ε (z τ)) (w := varsigma χ Ψ τ) s (Ψ τ) (1 / L)
      (fun c _ x hx => hF.one_on τ hτ c x hx) (C1 * ε) hQ
    have hU3 := g2c_energy_real hmc (by positivity) hU2
    have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hmid := g2c_mid (φ := φ) hmc hφ.continuous hUc
      (fun x hx => by
        by_contra h
        exact hx (hs (subset_tsupport _ h)))
      (M := M) (fun x => by simpa using hM x) hsq hU3
    have h1 := hA B (z τ) hz ε hε hε1
    have e : (n : ℝ) * (C1 * ε) / (2 * Real.sqrt ε) = n * C1 * Real.sqrt ε / 2 := by
      field_simp
      rw [Real.sq_sqrt hε.le]
    rw [e] at hmid
    calc |∫ x, z τ x * φ x| = |((∫ x, z τ x * φ x) - ∫ x, moll d ε (z τ) x * φ x) +
          ∫ x, moll d ε (z τ) x * φ x| := by rw [sub_add_cancel]
      _ ≤ |(∫ x, z τ x * φ x) - ∫ x, moll d ε (z τ) x * φ x| + |∫ x, moll d ε (z τ) x * φ x| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add h1 hmid
  set f : ℝ → ℝ := fun ε => A * |B| * ε + M * (Real.sqrt ε / 2 * V + n * C1 * Real.sqrt ε / 2) with hf
  have hfc : Continuous f := by
    rw [hf]; fun_prop
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := (hfc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |∫ x, z τ x * φ x| ≤ f ε := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact key ε hε.1 hε.2
  have h0 : |∫ x, z τ x * φ x| ≤ f 0 := ge_of_tendsto hlim hev
  have : f 0 = 0 := by simp [hf]
  rw [this] at h0
  exact abs_nonpos_iff.1 h0

theorem g2c_zero (hd : 1 ≤ d) {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K) {z : ℝ → Euc d → ℝ}
    {B : ℝ} (hzB : ∀ τ ∈ Set.Icc (0:ℝ) t, LocMass B (z τ)) (C0 : ℝ)
    (hE : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ c : Euc d,
      ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * moll d ε (z τ) x ^ 2) ≤ ENNReal.ofReal (C0 * ε)) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, z τ =ᵐ[MeasureTheory.volume] 0 := by
  intro τ hτ
  have h := isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := (volume : Measure (Euc d))) (f := z τ)
    ((hzB τ hτ).locallyIntegrable.locallyIntegrableOn _) (fun g hg hgc _ => by
      simp only [smul_eq_mul]
      have := g2c_pairing_zero hd hF hzB C0 hE hτ hg hgc
      simpa [mul_comm] using this)
  filter_upwards [h] with x hx
  exact hx (Set.mem_univ x)

end HRS.MS.UniqG2c
