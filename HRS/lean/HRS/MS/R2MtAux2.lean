import HRS.MS.R2MtAux1
import HRS.MS.PrepStat

/-!
# HRS.MS.R2MtAux2 -- Step B of `round2_moment_transfer` (S9.2): change of measure, `R2ActualFBound`, linear bound

Packet S92, namespace `HRS.MS.R2Mt`, helper prefix `s92_`.

* `s92_eLpNorm_le_of_moment`: `‖X‖_{L^t(Q)} ≤ (∫|X|^n dQ)^{1/n}` for a probability measure and `t ≤ n`.
* `s92_transfer`: `‖dP/dQ‖_{L^p(Q)} ≤ K` gives `‖X‖_{L^r(P)} ≤ K^{1/r} ‖X‖_{L^{r p'}(Q)}`.
* `s92_Q_to_pi`: `‖X‖_{L^r(Q)} ≤ e^{3 C/(2r)} ‖X‖_{L^{2r}(μ^{⊗N})}` (`dQ/dμ^N ∈ L²(μ^N)` uniformly).
* `s92_centered_le`: centering changes an `L^r(P)` norm by at most a factor `2` (`r ≥ 1`, `P` a probability measure).
* `s92_F_bound`: both bounds of `R2ActualFBound` with a constant `C(d,s,M,L,b,p,K,B,r)`.
* `s92_lin_pi`: Hoeffding: `‖√N(μ_N(a) - μ(a))‖_{L^n(μ^{⊗N})} ≤ C_n A`.
* `s92_linear_bound`: `R2ActualLinearBound` for one law.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.R2Mt

open HRS.Whole HRS.MS.Wr HRS.MS.PrepStat

variable {d N : ℕ}

/-! ### From moments to `eLpNorm` -/

theorem s92_eLpNorm_le_of_moment {α : Type*} [MeasurableSpace α] (Q : Measure α) [IsProbabilityMeasure Q]
    {X : α → ℝ} (hX : Measurable X) {t : ℝ} (ht : 0 < t) (n : ℕ) (htn : t ≤ n) {C : ℝ} (hC : 0 ≤ C)
    (hm : ∫⁻ x, ‖X x‖ₑ ^ n ∂Q ≤ ENNReal.ofReal C) :
    eLpNorm X (ENNReal.ofReal t) Q ≤ ENNReal.ofReal (C ^ (1 / (n : ℝ))) := by
  have hn : 0 < n := by
    have : (0 : ℝ) < n := lt_of_lt_of_le ht htn
    exact_mod_cast this
  have h1 : eLpNorm X (ENNReal.ofReal t) Q ≤ eLpNorm X (n : ℝ≥0∞) Q :=
    eLpNorm_le_eLpNorm_of_exponent_le (by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal htn)
  refine h1.trans ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hn.ne') (by simp) hX.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast]
  calc (∫⁻ x, ‖X x‖ₑ ^ n ∂Q) ^ (1 / (n : ℝ)) ≤ (ENNReal.ofReal C) ^ (1 / (n : ℝ)) :=
        ENNReal.rpow_le_rpow hm (by positivity)
    _ = ENNReal.ofReal (C ^ (1 / (n : ℝ))) := ENNReal.ofReal_rpow_of_nonneg hC (by positivity)

/-! ### Change of measure `Q → P` -/

theorem s92_transfer {Ω : Type*} [MeasurableSpace Ω] (Q P : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) {p K : ℝ} (hp : 1 < p) (hK : 0 ≤ K)
    (hdens : eLpNorm (fun x => (P.rnDeriv Q x).toReal) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal K)
    {X : Ω → ℝ} (hX : Measurable X) {r : ℝ} (hr : 0 < r) {Bq : ℝ}
    (hB : eLpNorm X (ENNReal.ofReal (r * Real.conjExponent p)) Q ≤ ENNReal.ofReal Bq) :
    eLpNorm X (ENNReal.ofReal r) P ≤ ENNReal.ofReal (K ^ (1 / r) * Bq) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hψ : Measurable (P.rnDeriv Q) := Measure.measurable_rnDeriv P Q
  have hlint : (∫⁻ x, (P.rnDeriv Q x) ^ p ∂Q) ^ (1 / p) ≤ ENNReal.ofReal K := by
    refine le_trans (le_of_eq ?_) hdens
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
      (hψ.ennreal_toReal.aestronglyMeasurable), ENNReal.toReal_ofReal hp0.le]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top P Q] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  have h := s92_eLpNorm_withDensity_le_real Q hψ hX hr hp hK hlint hB
  rwa [Measure.withDensity_rnDeriv_eq P Q hPQ] at h

/-! ### Change of measure `μ^{⊗N} → Q` -/

theorem s92_Q_to_pi {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) {b A0 : ℝ} (hW : GibbsWellDefined G N b μ)
    (hW2 : GibbsWellDefined G N (2 * b) μ) (h1 : |Real.log (pairNormalizer G N b μ)| ≤ A0)
    (h2 : |Real.log (pairNormalizer G N (2 * b) μ)| ≤ A0)
    {X : EucConfig d N → ℝ} (hX : Measurable X) {r : ℝ} (hr : 0 < r) {B : ℝ}
    (hB : eLpNorm X (ENNReal.ofReal (2 * r)) (Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal B) :
    eLpNorm X (ENNReal.ofReal r) (pairGibbs G N b μ) ≤ ENNReal.ofReal (Real.exp (3 * A0 / 2) ^ (1 / r) * B) := by
  rw [s92_pairGibbs_eq hGm hW]
  have hψ : Measurable (s92_dens G N b μ) := s92_dens_meas hGm b
  have hsq : (∫⁻ X, (s92_dens G N b μ X) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin N => μ)) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Real.exp (3 * A0 / 2)) := by
    have e : ∀ X, (s92_dens G N b μ X) ^ (2 : ℝ) = (s92_dens G N b μ X) ^ 2 := fun X => ENNReal.rpow_two _
    simp_rw [e]
    rw [s92_dens_sq_lintegral hW hW2]
    have hle := s92_psi_sq_le hW.normalizer_pos hW2.normalizer_pos h1 h2
    calc _ ≤ (ENNReal.ofReal (Real.exp (3 * A0))) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hle (by norm_num)
      _ = ENNReal.ofReal (Real.exp (3 * A0 / 2)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
        congr 2; ring
  have hc : Real.conjExponent (2 : ℝ) = 2 := by
    rw [Real.conjExponent]; norm_num
  refine s92_eLpNorm_withDensity_le_real _ hψ hX hr (by norm_num : (1 : ℝ) < 2) (Real.exp_pos _).le hsq ?_
  rw [hc, mul_comm r 2]
  exact hB

/-! ### Centering -/

theorem s92_centered_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) {r : ℝ} (hr : 1 ≤ r) {C : ℝ} (hC0 : 0 ≤ C) (hC : eLpNorm X (ENNReal.ofReal r) P ≤ ENNReal.ofReal C) :
    eLpNorm (fun x => X x - ∫ y, X y ∂P) (ENNReal.ofReal r) P ≤ ENNReal.ofReal (2 * C) := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
  have hsub := eLpNorm_sub_le (μ := P) (f := X) (g := fun _ : Ω => ∫ y, X y ∂P) hr1
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hconst : eLpNorm (fun _ : Ω => ∫ y, X y ∂P) (ENNReal.ofReal r) P = ‖∫ y, X y ∂P‖ₑ := by
    rw [eLpNorm_const _ hp0 (NeZero.ne P)]
    simp
  have hl1 : ‖∫ y, X y ∂P‖ₑ ≤ eLpNorm X (ENNReal.ofReal r) P := by
    calc ‖∫ y, X y ∂P‖ₑ ≤ ∫⁻ y, ‖X y‖ₑ ∂P := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm X 1 P := (eLpNorm_one_eq_lintegral_enorm hX.aestronglyMeasurable).symm
      _ ≤ eLpNorm X (ENNReal.ofReal r) P := eLpNorm_le_eLpNorm_of_exponent_le hr1
  calc eLpNorm (fun x => X x - ∫ y, X y ∂P) (ENNReal.ofReal r) P
      ≤ eLpNorm X (ENNReal.ofReal r) P + eLpNorm (fun _ : Ω => ∫ y, X y ∂P) (ENNReal.ofReal r) P := hsub
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := by
        rw [hconst]; exact add_le_add hC (hl1.trans hC)
    _ = ENNReal.ofReal (2 * C) := by
        rw [← ENNReal.ofReal_add hC0 hC0]; congr 1; ring

/-! ### `R2ActualFBound` -/

theorem s92_isProb_Q {s : ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {b : ℝ}
    (hW : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N b μ) :
    IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) := by
  rw [← pairGibbs_diff]; exact wr9_gibbs_prob hW

theorem s92_F_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b p K B r : ℝ)
    (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ h : Euc d → Euc d → ℝ,
      IsBoundedPairKernel s B h → ∀ N : ℕ, 2 ≤ N → ∀ P : Measure (EucConfig d N),
      HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) P →
      eLpNorm (fun X => (N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ)) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal C ∧
      eLpNorm (fun X => (N : ℝ) * (pairEnergy h X (HRS.Whole.withDensityReal ρ) -
        ∫ Y, pairEnergy h Y (HRS.Whole.withDensityReal ρ) ∂P)) (ENNReal.ofReal r) P ≤ ENNReal.ofReal C := by
  have hcp : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp).symm.lt
  set t : ℝ := r * Real.conjExponent p with ht
  have ht0 : 0 < t := mul_pos (by linarith) (by linarith)
  set n : ℕ := ⌈t⌉₊ with hn
  obtain ⟨Cn, hCn0, hCn⟩ := s92_moment_Q hd hs0 hs M L b B hb n
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L b (2 * b) hb (by linarith)
  set K' : ℝ := max K 0 with hK'
  set Cb : ℝ := K' ^ (1 / r) * Cn ^ (1 / (n : ℝ)) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨2 * Cb, by positivity, fun ρ hρ h hh N hN P hP => ?_⟩
  haveI := s92_isProb_mu hρ.prob
  haveI hPprob : IsProbabilityMeasure P := hP.1
  have hW := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).1
  haveI hQ := s92_isProb_Q (N := N) hW
  have hXm : Measurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ)) :=
    measurable_const.mul (wr9_measurable_pairEnergy hh.measurable)
  have hQb := s92_eLpNorm_le_of_moment (HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ))
    hXm ht0 n (Nat.le_ceil t) hCn0 (hCn ρ hρ h hh N hN)
  have hdens : eLpNorm (fun X => ((P.rnDeriv (HRS.Whole.modulatedGibbs (rieszKernel d s) N b
      (HRS.Whole.withDensityReal ρ))) X).toReal) (ENNReal.ofReal p)
      (HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal K' :=
    hP.2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hPb := s92_transfer _ P hP.2.1 hp (le_max_right _ _) hdens hXm (by linarith : 0 < r) hQb
  have hcen := s92_centered_le P hXm hr hCb0 hPb
  have e : (fun X : EucConfig d N => (N : ℝ) * (pairEnergy h X (HRS.Whole.withDensityReal ρ) -
        ∫ Y, pairEnergy h Y (HRS.Whole.withDensityReal ρ) ∂P)) =
      fun X => (N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ) -
        ∫ Y, (N : ℝ) * pairEnergy h Y (HRS.Whole.withDensityReal ρ) ∂P := by
    funext X
    rw [integral_const_mul, mul_sub]
  refine ⟨hPb.trans (ENNReal.ofReal_le_ofReal (by linarith)), ?_⟩
  rw [e]
  exact hcen

/-! ### Hoeffding under `μ^{⊗N}` -/

theorem s92_lin_pi {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : Euc d → ℝ} (ha : Measurable a)
    {A : ℝ} (hA : 0 < A) (hAa : ∀ x, |a x| ≤ A) (hN : 0 < N) (n : ℕ) :
    ∫⁻ X : EucConfig d N, ‖Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a)‖ₑ ^ n
        ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal ((n.factorial : ℝ) / (1 / A) ^ n * (2 * Real.exp (1 / 2))) := by
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  set Ψ : EucConfig d N → ℝ := fun X => ∑ i, (a (X i) - ∫ x, a x ∂μ) with hΨ
  have hΨm : Measurable Ψ :=
    Finset.measurable_sum _ fun i _ => ((ha.comp (measurable_pi_apply i)).sub_const _)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  set lam : ℝ := 1 / (A * Real.sqrt N) with hlamdef
  have hlam : 0 < lam := by positivity
  have hA' : (N : ℝ) * A ^ 2 * lam ^ 2 / 2 = 1 / 2 := by
    rw [hlamdef, div_pow, mul_pow, hsq2, one_pow]
    field_simp
  have hp : ∫⁻ X, ENNReal.ofReal (Real.exp (lam * Ψ X)) ∂π ≤ ENNReal.ofReal (Real.exp (1 / 2)) := by
    have := s32_mgf_bound (d := d) (N := N) (μ := μ) ha hAa lam
    rwa [hA'] at this
  have hm : ∫⁻ X, ENNReal.ofReal (Real.exp (-(lam * Ψ X))) ∂π ≤ ENNReal.ofReal (Real.exp (1 / 2)) := by
    have := s32_mgf_bound (d := d) (N := N) (μ := μ) ha hAa (-lam)
    have e : ((-lam) ^ 2) = lam ^ 2 := by ring
    rw [e, hA'] at this
    simpa only [hΨ, neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib] using this
  have hZ := wr9_lintegral_exp_abs π hΨm hlam hp hm
  have hrel : ∀ X : EucConfig d N,
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a) = Ψ X / Real.sqrt N := by
    intro X
    rw [s32_linear_stat X ha hN]
    simp only [hΨ]
    field_simp
    rw [hsq2]
  have hexp : ∀ X : EucConfig d N, lam * |Ψ X| = (1 / A) * |Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a)| := by
    intro X
    rw [hrel X, abs_div, abs_of_pos hsq, hlamdef]
    field_simp
  have hZ' : ∫⁻ X, ENNReal.ofReal (Real.exp ((1 / A) * |Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a)|)) ∂π ≤
      ENNReal.ofReal (2 * Real.exp (1 / 2)) := by
    simp_rw [← hexp]; exact hZ
  exact s92_moment_of_lexp π (by positivity) hZ' n

/-! ### `R2ActualLinearBound` for one law -/

theorem s92_linear_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b p K r : ℝ)
    (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ P : Measure (EucConfig d N), HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) P →
      ∀ (a : Euc d → ℝ) (A : ℝ), Measurable a → (∀ x, |a x| ≤ A) →
        eLpNorm (fun X : EucConfig d N => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) a))
          (ENNReal.ofReal r) P ≤ ENNReal.ofReal (C * A) := by
  have hcp : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp).symm.lt
  set t : ℝ := r * Real.conjExponent p with ht
  have ht0 : 0 < t := mul_pos (by linarith) (by linarith)
  set n : ℕ := ⌈2 * t⌉₊ with hn
  have hn1 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_lt_of_le (by linarith) (Nat.le_ceil (2 * t))
    exact_mod_cast this
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L b (2 * b) hb (by linarith)
  set K' : ℝ := max K 0 with hK'
  set Lin : ℝ := ((n.factorial : ℝ) * (2 * Real.exp (1 / 2))) ^ (1 / (n : ℝ)) with hLin
  set Cc : ℝ := K' ^ (1 / r) * (Real.exp (3 * C0 / 2) ^ (1 / t) * Lin) with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨Cc, hCc0, fun ρ hρ N hN P hP a A ha hAa => ?_⟩
  haveI := s92_isProb_mu hρ.prob
  haveI hPprob : IsProbabilityMeasure P := hP.1
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hAa 0)
  have hN0 : 0 < N := by omega
  have hXm : Measurable (fun X : EucConfig d N => Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) a)) := by
    have : ∀ X : EucConfig d N, HRS.Whole.pair (HRS.Whole.empirical X) a = (N : ℝ)⁻¹ * ∑ i, a (X i) :=
      fun X => s32_pair_empirical X ha
    simp_rw [this]
    exact measurable_const.mul ((measurable_const.mul
      (Finset.measurable_sum _ fun i _ => ha.comp (measurable_pi_apply i))).sub measurable_const)
  rcases hA0.eq_or_lt with hA | hA
  · have ha0 : a = fun _ => 0 := by
      funext x
      have := hAa x
      rw [← hA] at this
      exact abs_nonpos_iff.1 this
    subst ha0
    simp [HRS.Whole.pair]
  · have hW := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).1
    have hW2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).1
    have hl1 := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).2
    have hl2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).2
    haveI hQ := s92_isProb_Q (N := N) hW
    have hmom := s92_lin_pi (μ := HRS.Whole.withDensityReal ρ) ha hA hAa hN0 n
    have hE : 0 ≤ (n.factorial : ℝ) / (1 / A) ^ n * (2 * Real.exp (1 / 2)) := by positivity
    have hpi := s92_eLpNorm_le_of_moment (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) hXm
      (by linarith : 0 < 2 * t) n (Nat.le_ceil (2 * t)) hE hmom
    have hrw : ((n.factorial : ℝ) / (1 / A) ^ n * (2 * Real.exp (1 / 2))) ^ (1 / (n : ℝ)) = A * Lin := by
      have : (n.factorial : ℝ) / (1 / A) ^ n * (2 * Real.exp (1 / 2)) =
          A ^ n * ((n.factorial : ℝ) * (2 * Real.exp (1 / 2))) := by
        rw [one_div, inv_pow, div_inv_eq_mul]; ring
      rw [this, Real.mul_rpow (by positivity) (by positivity), hLin]
      congr 1
      rw [one_div, Real.pow_rpow_inv_natCast hA0 hn1.ne']
    rw [hrw] at hpi
    have hQeq : HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ) =
        pairGibbs (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ) := rfl
    have hQb : eLpNorm (fun X : EucConfig d N => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) a))
        (ENNReal.ofReal t) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal (Real.exp (3 * C0 / 2) ^ (1 / t) * (A * Lin)) := by
      rw [hQeq]
      exact s92_Q_to_pi (wr9_rieszKernel_pair_meas s) hW hW2 hl1 hl2 hXm ht0 hpi
    have hdens : eLpNorm (fun X => ((P.rnDeriv (HRS.Whole.modulatedGibbs (rieszKernel d s) N b
        (HRS.Whole.withDensityReal ρ))) X).toReal) (ENNReal.ofReal p)
        (HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal K' :=
      hP.2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hPb := s92_transfer _ P hP.2.1 hp (le_max_right _ _) hdens hXm (by linarith : 0 < r) hQb
    refine hPb.trans (le_of_eq ?_)
    congr 1
    rw [hCc]; ring

end HRS.MS.R2Mt
