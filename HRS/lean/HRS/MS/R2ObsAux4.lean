import HRS.MS.R2SeAux11
import HRS.PDE.MeanFieldPairSeries

/-!
# S9.10 path row, packet 4: linearity of the response over a `C_b^J`-summable series

Worker S910, namespace `HRS.MS.R2Obs`.  For `ψ ∈ C_b^{J1}` write `a_ψ = responseRepW ψ` (`S99.aRep`).

* `s910_resp_add`, `s910_resp_smul`: `a_{ψ₁+ψ₂} = a_{ψ₁}+a_{ψ₂}`, `a_{cψ} = c a_ψ` pointwise (uniqueness of the response, `s98_resp_unique`, and
  the a.e. additivity of `K` on `L²_0`, `tc5_kop_sub_ae`);
* `s910_resp_sup`: `|a_ψ(x)| ≤ K ‖ψ‖_{C_b^{J1}}` with `K` independent of `ψ` (from `s99_chi`);
* `s910_cb_tsum`: a series of `C_b^J` functions with summable norms is `C_b^J`, `‖∑ φ_n‖ ≤ (J+1) ∑ v_n`;
* `s910_resp_series`: `g = ∑ c_n f_n` pointwise, `|c_n| ≤ B`, `∑ ‖f_n‖_{C_b^{J1}} < ∞` gives `g ∈ C_b^{J1}` and `a_g(x) = ∑ c_n a_{f_n}(x)`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s910_norm_iter_le_cb {k : ℕ} {Φ : Euc d → ℝ} (hΦ : MemCb k Φ) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ cbNorm k Φ := s99_norm_iter_le_cb hΦ hj x

theorem s910_cb_tsum (φ : ℕ → Euc d → ℝ) (J : ℕ) (hφ : ∀ n, MemCb J (φ n)) (v : ℕ → ℝ) (hv : Summable v)
    (hb : ∀ n, cbNorm J (φ n) ≤ v n) :
    MemCb J (fun x => ∑' n, φ n x) ∧ cbNorm J (fun x => ∑' n, φ n x) ≤ ((J : ℝ) + 1) * ∑' n, v n := by
  have h := HRS.PDE.MFPair.cd_tsum_ps φ J (fun n => (hφ n).1) v hv
    (fun i k hk x => (s99_norm_iter_le_cb (hφ i) hk x).trans (hb i))
  refine ⟨⟨h.1, fun j hj => ⟨∑' n, v n, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact h.2.2 j hj x
  · unfold cbNorm
    calc ∑ j ∈ Finset.range (J + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => ∑' n, φ n x) z‖
        ≤ ∑ j ∈ Finset.range (J + 1), ∑' n, v n := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact ciSup_le fun z => h.2.2 j (by simpa [Nat.lt_succ_iff] using hj) z
      _ = ((J : ℝ) + 1) * ∑' n, v n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring

section Resp

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ)

include hd hs0 hsd ha hβ hγ

theorem s910_resp_smul {ψ : Euc d → ℝ} (hψ : MemCb (J1 d) ψ) (c : ℝ) (x : Euc d) :
    aRep d s a β γ (fun y => c * ψ y) x = c * aRep d s a β γ ψ x := by
  obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hU, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a) (βm := β)
    (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hSρ⟩ := hU 0
  have hTc := hSρ a β le_rfl le_rfl le_rfl le_rfl
  have hmem : ∀ i : ℕ, MemCb (J1 d) (if i = 0 then ψ else fun y => c * ψ y) := fun i => by
    by_cases hi : i = 0
    · simp only [hi, ite_true]; exact hψ
    · simp only [hi, ite_false]; exact (HRS.MS.Tc5.tc5_cb_smul c hψ).1
  obtain ⟨F'⟩ := s99_famData hd hs0 hsd ha hβ hγ (φ := fun i : ℕ => if i = 0 then ψ else fun y => c * ψ y) hmem
  have r0 := F'.resp 0
  have r1 := F'.resp 1
  have a0 := F'.amem 0
  have a1 := F'.amem 1
  simp only [ite_true, ite_false, one_ne_zero] at r0 r1 a0 a1
  have hc : HRS.Whole.IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ (fun y => c * ψ y)
      (fun y => c * aRep d s a β γ ψ y) := by
    refine ⟨⟨r0.1.1.const_mul c, by rw [integral_const_mul, r0.1.2, mul_zero]⟩, ?_⟩
    filter_upwards [r0.2] with y hy
    have h1 := HRS.MS.S98.s98_kop_smul (rieszKernel d s) (thermalMeasure d s a β) c (aRep d s a β γ ψ) y
    have h2 : HRS.Whole.projMean (thermalMeasure d s a β) (fun y => c * ψ y) y =
        c * HRS.Whole.projMean (thermalMeasure d s a β) ψ y := by
      unfold HRS.Whole.projMean HRS.Whole.pair
      rw [integral_const_mul]; ring
    rw [h1, h2, ← hy]; ring
  have hae := HRS.MS.S98.s98_resp_unique (by omega : 1 ≤ d) hs0 hsd hc₀ hTc hγ r1 hc
  have hvol : ∀ᵐ y ∂(volume : Measure (Euc d)), aRep d s a β γ (fun y => c * ψ y) y =
      c * aRep d s a β γ ψ y := by
    have hmeas : Measurable fun x => ENNReal.ofReal (thermalDensity d s a β x) :=
      ENNReal.measurable_ofReal.comp hTc.smooth.continuous.measurable
    have := (ae_withDensity_iff hmeas).1 hae
    filter_upwards [this] with y hy
    exact hy (by simpa using hTc.pos y)
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) a1.1.continuous
    (continuous_const.mul a0.1.continuous)).1 hvol) x

theorem s910_resp_add {ψ₁ ψ₂ : Euc d → ℝ} (h₁ : MemCb (J1 d) ψ₁) (h₂ : MemCb (J1 d) ψ₂) (x : Euc d) :
    aRep d s a β γ (fun y => ψ₁ y + ψ₂ y) x = aRep d s a β γ ψ₁ x + aRep d s a β γ ψ₂ x := by
  obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hU, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a) (βm := β)
    (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hSρ⟩ := hU 0
  have hTc := hSρ a β le_rfl le_rfl le_rfl le_rfl
  have hprob : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hsum : MemCb (J1 d) (fun y => ψ₁ y + ψ₂ y) := (HRS.MS.Tc5.tc5_cb_add h₁ h₂).1
  have hmem : ∀ i : ℕ, MemCb (J1 d) (if i = 0 then ψ₁ else if i = 1 then ψ₂ else fun y => ψ₁ y + ψ₂ y) :=
    fun i => by
      by_cases hi : i = 0
      · simp only [hi, ite_true]; exact h₁
      · by_cases hi1 : i = 1
        · simp only [hi, hi1, ite_true, ite_false]; exact h₂
        · simp only [hi, hi1, ite_false]; exact hsum
  obtain ⟨F'⟩ := s99_famData hd hs0 hsd ha hβ hγ
    (φ := fun i : ℕ => if i = 0 then ψ₁ else if i = 1 then ψ₂ else fun y => ψ₁ y + ψ₂ y) hmem
  have r0 := F'.resp 0
  have r1 := F'.resp 1
  have r2 := F'.resp 2
  have a0 := F'.amem 0
  have a1 := F'.amem 1
  have a2 := F'.amem 2
  simp only [ite_true, ite_false, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at r0 r1 r2 a0 a1 a2
  have hu : HRS.Whole.MemL2Zero (thermalMeasure d s a β) (aRep d s a β γ ψ₁) := r0.1
  have hv : HRS.Whole.MemL2Zero (thermalMeasure d s a β) (fun y => (-1 : ℝ) * aRep d s a β γ ψ₂ y) :=
    ⟨r1.1.1.const_mul (-1), by rw [integral_const_mul, r1.1.2, mul_zero]⟩
  have hK := HRS.MS.Tc5.tc5_kop_sub_ae hs0 hsd M₀ c₀ S hc₀ 0 hTc hu hv
  have hKeq : (fun y => aRep d s a β γ ψ₁ y - (-1 : ℝ) * aRep d s a β γ ψ₂ y) =
      fun y => aRep d s a β γ ψ₁ y + aRep d s a β γ ψ₂ y := funext fun y => by ring
  rw [hKeq] at hK
  have hc : HRS.Whole.IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ (fun y => ψ₁ y + ψ₂ y)
      (fun y => aRep d s a β γ ψ₁ y + aRep d s a β γ ψ₂ y) := by
    refine ⟨⟨r0.1.1.add r1.1.1, ?_⟩, ?_⟩
    · rw [integral_add (r0.1.1.integrable (by norm_num)) (r1.1.1.integrable (by norm_num)), r0.1.2, r1.1.2, add_zero]
    · filter_upwards [r0.2, r1.2, hK] with y hy0 hy1 hyK
      have h1 := HRS.MS.S98.s98_kop_smul (rieszKernel d s) (thermalMeasure d s a β) (-1) (aRep d s a β γ ψ₂) y
      have hi1 : Integrable ψ₁ (thermalMeasure d s a β) :=
        (HRS.MS.Tc5.tc5_memLp_of_cb h₁).integrable (by norm_num)
      have hi2 : Integrable ψ₂ (thermalMeasure d s a β) :=
        (HRS.MS.Tc5.tc5_memLp_of_cb h₂).integrable (by norm_num)
      have h2 : HRS.Whole.projMean (thermalMeasure d s a β) (fun y => ψ₁ y + ψ₂ y) y =
          HRS.Whole.projMean (thermalMeasure d s a β) ψ₁ y + HRS.Whole.projMean (thermalMeasure d s a β) ψ₂ y := by
        unfold HRS.Whole.projMean HRS.Whole.pair
        rw [integral_add hi1 hi2]; ring
      have hyK' : HRS.Whole.Kop (rieszKernel d s) (thermalMeasure d s a β)
          (fun y => aRep d s a β γ ψ₁ y + aRep d s a β γ ψ₂ y) y =
          HRS.Whole.Kop (rieszKernel d s) (thermalMeasure d s a β) (aRep d s a β γ ψ₁) y -
            HRS.Whole.Kop (rieszKernel d s) (thermalMeasure d s a β)
              (fun y => (-1 : ℝ) * aRep d s a β γ ψ₂ y) y := hyK
      rw [h2, hyK', h1]
      linear_combination hy0 + hy1
  have hae := HRS.MS.S98.s98_resp_unique (by omega : 1 ≤ d) hs0 hsd hc₀ hTc hγ r2 hc
  have hvol : ∀ᵐ y ∂(volume : Measure (Euc d)), aRep d s a β γ (fun y => ψ₁ y + ψ₂ y) y =
      aRep d s a β γ ψ₁ y + aRep d s a β γ ψ₂ y := by
    have hmeas : Measurable fun x => ENNReal.ofReal (thermalDensity d s a β x) :=
      ENNReal.measurable_ofReal.comp hTc.smooth.continuous.measurable
    have := (ae_withDensity_iff hmeas).1 hae
    filter_upwards [this] with y hy
    exact hy (by simpa using hTc.pos y)
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) a2.1.continuous
    (a0.1.continuous.add a1.1.continuous)).1 hvol) x

theorem s910_resp_sup : ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ : Euc d → ℝ, MemCb (J1 d) ψ → ∀ x : Euc d,
    |aRep d s a β γ ψ x| ≤ K * cbNorm (J1 d) ψ := by
  obtain ⟨K, hK0, hK⟩ := s99_chi hd hs0 hsd (k0 d) (k0_ge_one d) a β γ ha hβ hγ (J1 d) (k0_lt_J1 d)
  refine ⟨K, hK0, fun ψ hψ x => ?_⟩
  obtain ⟨χ, -, -, -, -, hmem, hnorm⟩ := hK ψ hψ
  have h1 := HRS.MS.Tc5.tc5_cb_sup_le hmem x
  rw [Real.norm_eq_abs] at h1
  exact (h1.trans hnorm)

/-- finite combinations -/
theorem s910_resp_finsum {f : ℕ → Euc d → ℝ} (hf : ∀ n, MemCb (J1 d) (f n)) (c : ℕ → ℝ) (N : ℕ) :
    MemCb (J1 d) (fun x => ∑ n ∈ Finset.range N, c n * f n x) ∧ ∀ x : Euc d,
      aRep d s a β γ (fun y => ∑ n ∈ Finset.range N, c n * f n y) x =
        ∑ n ∈ Finset.range N, c n * aRep d s a β γ (f n) x := by
  induction N with
  | zero =>
    have h0 : (fun x : Euc d => ∑ n ∈ Finset.range 0, c n * f n x) = fun _ => (0 : ℝ) := by
      funext x; simp
    have h1 := s910_resp_smul hd hs0 hsd ha hβ hγ (hf 0) 0
    refine ⟨?_, fun x => ?_⟩
    · rw [h0]
      have := (HRS.MS.Tc5.tc5_cb_smul (0 : ℝ) (hf 0)).1
      simpa using this
    · rw [h0]
      have := h1 x
      simpa using this
  | succ N ih =>
    obtain ⟨ihm, ihr⟩ := ih
    have hs := s910_resp_smul hd hs0 hsd ha hβ hγ (hf N) (c N)
    have hm1 : MemCb (J1 d) (fun x => c N * f N x) := (HRS.MS.Tc5.tc5_cb_smul (c N) (hf N)).1
    have e : (fun x : Euc d => ∑ n ∈ Finset.range (N + 1), c n * f n x) =
        fun x => (∑ n ∈ Finset.range N, c n * f n x) + c N * f N x := funext fun x => by
      rw [Finset.sum_range_succ]
    refine ⟨?_, fun x => ?_⟩
    · rw [e]; exact (HRS.MS.Tc5.tc5_cb_add ihm hm1).1
    · rw [e, s910_resp_add hd hs0 hsd ha hβ hγ ihm hm1, ihr x, hs x, Finset.sum_range_succ]

theorem s910_resp_series {f : ℕ → Euc d → ℝ} (hf : ∀ n, MemCb (J1 d) (f n))
    (hsum : Summable fun n => cbNorm (J1 d) (f n)) (c : ℕ → ℝ) {B : ℝ} (hB : ∀ n, |c n| ≤ B)
    {g : Euc d → ℝ} (hg : ∀ x, HasSum (fun n => c n * f n x) (g x)) :
    MemCb (J1 d) g ∧ ∀ x, HasSum (fun n => c n * aRep d s a β γ (f n) x) (aRep d s a β γ g x) := by
  obtain ⟨K, hK0, hK⟩ := s910_resp_sup hd hs0 hsd ha hβ hγ
  set w : ℕ → ℝ := fun n => cbNorm (J1 d) (f n) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => HRS.MS.Tc5.tc5_cb_nonneg (J1 d) (f n)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  -- the tails
  have htail : ∀ N : ℕ, MemCb (J1 d) (fun x => ∑' n, c (n + N) * f (n + N) x) ∧
      cbNorm (J1 d) (fun x => ∑' n, c (n + N) * f (n + N) x) ≤
        ((J1 d : ℝ) + 1) * ∑' n, B * w (n + N) := by
    intro N
    have hsN : Summable fun n => B * w (n + N) :=
      ((summable_nat_add_iff N).2 hsum).mul_left B
    refine s910_cb_tsum (fun n x => c (n + N) * f (n + N) x) (J1 d)
      (fun n => (HRS.MS.Tc5.tc5_cb_smul (c (n + N)) (hf (n + N))).1) (fun n => B * w (n + N)) hsN
      (fun n => ?_)
    refine (HRS.MS.Tc5.tc5_cb_smul (c (n + N)) (hf (n + N))).2.trans ?_
    exact mul_le_mul (hB _) le_rfl (hw0 _) hB0
  -- the decomposition g = partial sum + tail
  have hdec : ∀ (N : ℕ) (x : Euc d), g x = (∑ n ∈ Finset.range N, c n * f n x) +
      ∑' n, c (n + N) * f (n + N) x := fun N x => by
    rw [← (hg x).tsum_eq]
    exact ((hg x).summable.sum_add_tsum_nat_add N).symm
  have hg0 : MemCb (J1 d) g := by
    have h0 := (htail 0).1
    have e : g = fun x => ∑' n, c (n + 0) * f (n + 0) x := funext fun x => by
      simp only [add_zero]; exact (hg x).tsum_eq.symm
    rw [e]; exact h0
  refine ⟨hg0, fun x => ?_⟩
  -- the response of the tail is small
  have hbd : ∀ n, |c n * aRep d s a β γ (f n) x| ≤ B * K * w n := fun n => by
    rw [abs_mul]
    calc |c n| * |aRep d s a β γ (f n) x| ≤ B * (K * w n) :=
          mul_le_mul (hB n) (hK (f n) (hf n) x) (abs_nonneg _) hB0
      _ = B * K * w n := by ring
  have hsumA : Summable fun n => c n * aRep d s a β γ (f n) x :=
    Summable.of_norm_bounded (hsum.mul_left (B * K)) (fun n => by rw [Real.norm_eq_abs]; exact hbd n)
  refine hsumA.hasSum_iff_tendsto_nat.2 ?_
  have herr : Tendsto (fun N : ℕ => ((J1 d : ℝ) + 1) * K * ∑' n, B * w (n + N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ∑' n, B * w (n + N)) atTop (𝓝 0) := by
      have := tendsto_sum_nat_add (fun n => B * w n)
      exact this
    simpa using h1.const_mul (((J1 d : ℝ) + 1) * K)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun N => dist_nonneg) (fun N => ?_) herr)
  rw [Real.dist_eq]
  -- partial sum of responses vs response of g
  obtain ⟨hpm, hpr⟩ := s910_resp_finsum hd hs0 hsd ha hβ hγ hf c N
  have hgN : g = fun y => (∑ n ∈ Finset.range N, c n * f n y) + ∑' n, c (n + N) * f (n + N) y :=
    funext (hdec N)
  have hadd := s910_resp_add hd hs0 hsd ha hβ hγ hpm (htail N).1 x
  have hmain : aRep d s a β γ g x = (∑ n ∈ Finset.range N, c n * aRep d s a β γ (f n) x) +
      aRep d s a β γ (fun y => ∑' n, c (n + N) * f (n + N) y) x := by
    rw [hgN, hadd, hpr x]
  rw [hmain]
  have := hK _ (htail N).1 x
  have h3 : |aRep d s a β γ (fun y => ∑' n, c (n + N) * f (n + N) y) x| ≤
      K * (((J1 d : ℝ) + 1) * ∑' n, B * w (n + N)) :=
    this.trans (mul_le_mul_of_nonneg_left (htail N).2 hK0)
  calc |(∑ n ∈ Finset.range N, c n * aRep d s a β γ (f n) x) -
        ((∑ n ∈ Finset.range N, c n * aRep d s a β γ (f n) x) +
          aRep d s a β γ (fun y => ∑' n, c (n + N) * f (n + N) y) x)|
      = |aRep d s a β γ (fun y => ∑' n, c (n + N) * f (n + N) y) x| := by
        rw [sub_add_cancel_left, abs_neg]
    _ ≤ K * (((J1 d : ℝ) + 1) * ∑' n, B * w (n + N)) := h3
    _ = ((J1 d : ℝ) + 1) * K * ∑' n, B * w (n + N) := by ring

end Resp

end HRS.MS.R2Obs

end
