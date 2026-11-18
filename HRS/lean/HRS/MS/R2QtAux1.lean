import HRS.MS.R2MtAux3
import HRS.MS.PrepStat

/-!
# HRS.MS.R2QtAux1 -- `round2_quench_transfer` (S9.3)

Packet S92, namespace `HRS.MS.R2Mt`, helper prefix `s92_`.

* `s92_markov_Lp`: `L^p` contraction of an invariant Markov kernel on densities (Jensen for the kernel, Hoelder duality
  against truncated powers of the density, monotone convergence): `‖d(Rκ)/dQ‖_{L^p(Q)} ≤ ‖dR/dQ‖_{L^p(Q)}` when `Qκ = Q`.
* `s92_tilt_power`: exact identity `∫ (dQ_{b₀}/dQ_b)^p dQ_b = K_b^{p-1} K_{b'} / K_{b₀}^p`, `b' = b + p(b₀-b) = p b₀ - (p-1) b`.
* `s92_quench_density`: with `p = 1 + b₀/(2(b+b₀))` (so `b' ≥ b₀/2 > 0`) and the two-sided pressure bound
  (`s92_normalizer_bounds`), `HasR2ActualDensity s b p K μ (Q_{N,b₀} κ)` for every Markov `κ` preserving `Q_{N,b}`.
* `round2_quench_transfer_proof : type_of% @HRS.Whole.round2_quench_transfer`: the conclusions of S9.2
  (`s92_F_bound`, `s92_linear_bound`, `s92_tail` for the family indexed by `t ≥ 0`) with this `p`, `K`.
  Statement unchanged; tie in `HRS/MS/R2Tie.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Mt

open HRS.Whole HRS.MS.Wr HRS.MS.PrepStat

variable {d N : ℕ}

/-! ### Jensen and duality for Markov kernels -/

/-- Jensen for a probability measure in `ℝ≥0∞`: `(∫ g)^q ≤ ∫ g^q`. -/
theorem s92_jensen_enn {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {g : α → ℝ≥0∞} (hg : Measurable g) {q : ℝ} (hq : 1 < q) :
    (∫⁻ x, g x ∂ν) ^ q ≤ ∫⁻ x, g x ^ q ∂ν := by
  have hpq : q.HolderConjugate (Real.conjExponent q) := Real.HolderConjugate.conjExponent hq
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg.aemeasurable
    (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have hq0 : 0 < q := by linarith
  calc (∫⁻ x, g x ∂ν) ^ q ≤ ((∫⁻ x, g x ^ q ∂ν) ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow (by simpa using h) hq0.le
    _ = ∫⁻ x, g x ^ q ∂ν := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]

/-- Duality inequality for the push-forward of a density along an invariant Markov kernel. -/
theorem s92_dual {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (hinv : Q.bind κ = Q) {f : Ω → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂((Q.withDensity f).bind κ) ≤
      (∫⁻ x, f x ^ p ∂Q) ^ (1 / p) * (∫⁻ x, g x ^ Real.conjExponent p ∂Q) ^ (1 / Real.conjExponent p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  set q := Real.conjExponent p with hqdef
  have hq1 : 1 < q := hpq.symm.lt
  have hKg : Measurable (fun a => ∫⁻ x, g x ∂(κ a)) := hg.lintegral_kernel
  rw [Measure.lintegral_bind κ.measurable.aemeasurable hg.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul Q hf hKg]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq Q hpq hf.aemeasurable hKg.aemeasurable).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by positivity))
  calc ∫⁻ a, (∫⁻ x, g x ∂(κ a)) ^ q ∂Q ≤ ∫⁻ a, ∫⁻ x, g x ^ q ∂(κ a) ∂Q :=
        lintegral_mono fun a => s92_jensen_enn (κ a) hg hq1
    _ = ∫⁻ x, g x ^ q ∂(Q.bind κ) :=
        (Measure.lintegral_bind κ.measurable.aemeasurable (hg.pow_const q).aemeasurable).symm
    _ = ∫⁻ x, g x ^ q ∂Q := by rw [hinv]

theorem s92_self_bound {A c : ℝ≥0∞} {p q : ℝ} (hpq : p.HolderConjugate q) (hA : A ≠ ⊤)
    (h : A ≤ c * A ^ (1 / q)) : A ^ (1 / p) ≤ c := by
  by_cases h0 : A = 0
  · rw [h0, ENNReal.zero_rpow_of_pos (by have := hpq.pos; positivity)]
    exact bot_le
  · have hq0 : 0 < q := hpq.symm.pos
    have e : A ^ (1 / p) * A ^ (1 / q) = A := by
      rw [← ENNReal.rpow_add _ _ h0 hA, one_div, one_div, hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
    have hne0 : A ^ (1 / q) ≠ 0 := by
      intro hz
      rcases ENNReal.rpow_eq_zero_iff.1 hz with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h0 h1
      · have : (0 : ℝ) < 1 / q := by positivity
        linarith
    have hnetop : A ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hA
    have h' : A ^ (1 / p) * A ^ (1 / q) ≤ c * A ^ (1 / q) := by rw [e]; exact h
    calc A ^ (1 / p) = A ^ (1 / p) * A ^ (1 / q) * (A ^ (1 / q))⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hne0 hnetop, mul_one]
      _ ≤ c * A ^ (1 / q) * (A ^ (1 / q))⁻¹ := by gcongr
      _ = c := by rw [mul_assoc, ENNReal.mul_inv_cancel hne0 hnetop, mul_one]

/-- **`L^p` contraction of an invariant Markov kernel on densities** (Jensen/duality): if `Q` is a probability
measure invariant under the Markov kernel `κ` and `R = f Q` is a probability measure, then `R κ ≪ Q` and
`‖d(Rκ)/dQ‖_{L^p(Q)} ≤ ‖f‖_{L^p(Q)}`. -/
theorem s92_markov_Lp {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (hinv : Q.bind κ = Q) {f : Ω → ℝ≥0∞} (hf : Measurable f)
    [IsProbabilityMeasure (Q.withDensity f)] {p : ℝ} (hp : 1 < p) :
    ((Q.withDensity f).bind κ ≪ Q) ∧
      ∫⁻ x, (((Q.withDensity f).bind κ).rnDeriv Q x) ^ p ∂Q ≤ ∫⁻ x, f x ^ p ∂Q := by
  set R := Q.withDensity f with hR
  set Rk := R.bind κ with hRk
  haveI hRprob : IsProbabilityMeasure Rk :=
    ⟨by rw [hRk, Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]; simp⟩
  have hac : Rk ≪ Q := by
    refine Measure.AbsolutelyContinuous.mk fun A hA hQA => ?_
    rw [hRk, Measure.bind_apply hA κ.measurable.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul Q hf (κ.measurable_coe hA)]
    have h0 : ∫⁻ a, κ a A ∂Q = 0 := by
      have := Measure.bind_apply hA κ.measurable.aemeasurable (m := Q)
      rw [hinv] at this
      rw [← this]; exact hQA
    have h1 : (fun a => κ a A) =ᵐ[Q] 0 := (lintegral_eq_zero_iff (κ.measurable_coe hA)).1 h0
    have h2 : (f * fun a => κ a A) =ᵐ[Q] 0 := by
      filter_upwards [h1] with a ha
      simp [Pi.mul_apply, ha]
    rw [lintegral_congr_ae h2]; simp
  refine ⟨hac, ?_⟩
  set u := Rk.rnDeriv Q with hu
  have hum : Measurable u := Measure.measurable_rnDeriv _ _
  have hRu : Q.withDensity u = Rk := Measure.withDensity_rnDeriv_eq Rk Q hac
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  set q := Real.conjExponent p with hqdef
  have hp0 : 0 < p := by linarith
  set F := ∫⁻ x, f x ^ p ∂Q with hF
  have hn : ∀ n : ℕ, ∫⁻ x, (min (u x) (n : ℝ≥0∞)) ^ p ∂Q ≤ F := by
    intro n
    have hunm : Measurable (fun x => min (u x) (n : ℝ≥0∞)) := hum.min measurable_const
    set g : Ω → ℝ≥0∞ := fun x => (min (u x) (n : ℝ≥0∞)) ^ (p - 1) with hg
    have hgm : Measurable g := hunm.pow_const _
    have hdual := s92_dual Q κ hinv hf hp hgm
    have hgq : ∀ x, g x ^ q = (min (u x) (n : ℝ≥0∞)) ^ p := by
      intro x
      simp only [hg]
      rw [← ENNReal.rpow_mul]
      congr 1
      rw [hqdef, Real.conjExponent]
      have : p - 1 ≠ 0 := by linarith
      field_simp
    have hlhs : ∫⁻ x, g x ∂(Rk) = ∫⁻ x, (u * g) x ∂Q := by
      rw [← hRu]; exact lintegral_withDensity_eq_lintegral_mul Q hum hgm
    have hle : ∀ x, (min (u x) (n : ℝ≥0∞)) ^ p ≤ (u * g) x := by
      intro x
      show (min (u x) (n : ℝ≥0∞)) ^ p ≤ u x * (min (u x) (n : ℝ≥0∞)) ^ (p - 1)
      calc (min (u x) (n : ℝ≥0∞)) ^ p = (min (u x) (n : ℝ≥0∞)) ^ ((1 : ℝ) + (p - 1)) := by
            congr 1; ring
        _ = (min (u x) (n : ℝ≥0∞)) ^ (1 : ℝ) * (min (u x) (n : ℝ≥0∞)) ^ (p - 1) :=
            ENNReal.rpow_add_of_nonneg 1 (p - 1) (by norm_num) (by linarith)
        _ = (min (u x) (n : ℝ≥0∞)) * (min (u x) (n : ℝ≥0∞)) ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ ≤ u x * (min (u x) (n : ℝ≥0∞)) ^ (p - 1) := by gcongr; exact min_le_left _ _
    set A := ∫⁻ x, (min (u x) (n : ℝ≥0∞)) ^ p ∂Q with hA
    have hAfin : A ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _x, (n : ℝ≥0∞) ^ p ∂Q) ?_ ?_
      · rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top n)
      · exact lintegral_mono fun x => ENNReal.rpow_le_rpow (min_le_right _ _) hp0.le
    have hAle : A ≤ F ^ (1 / p) * A ^ (1 / q) := by
      calc A ≤ ∫⁻ x, (u * g) x ∂Q := lintegral_mono hle
        _ = ∫⁻ x, g x ∂(Rk) := hlhs.symm
        _ ≤ F ^ (1 / p) * (∫⁻ x, g x ^ q ∂Q) ^ (1 / q) := hdual
        _ = F ^ (1 / p) * A ^ (1 / q) := by rw [lintegral_congr hgq]
    have h1 := s92_self_bound hpq hAfin hAle
    calc A = (A ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
      _ ≤ (F ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h1 hp0.le
      _ = F := by rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have hmono : Monotone (fun (n : ℕ) (x : Ω) => (min (u x) (n : ℝ≥0∞)) ^ p) := by
    intro n m hnm x
    exact ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hnm)) hp0.le
  have hsup : ∀ x, ⨆ n : ℕ, (min (u x) (n : ℝ≥0∞)) ^ p = (u x) ^ p := by
    intro x
    have h1 : Tendsto (fun n : ℕ => min (u x) (n : ℝ≥0∞)) atTop (𝓝 (u x)) := by
      have := (tendsto_const_nhds (x := u x)).min ENNReal.tendsto_nat_nhds_top
      simpa using this
    have h2 : Tendsto (fun n : ℕ => (min (u x) (n : ℝ≥0∞)) ^ p) atTop (𝓝 ((u x) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h1
    exact (tendsto_nhds_unique (tendsto_atTop_iSup (fun n m hnm => hmono hnm x)) h2)
  calc ∫⁻ x, u x ^ p ∂Q = ∫⁻ x, ⨆ n : ℕ, (min (u x) (n : ℝ≥0∞)) ^ p ∂Q := by simp_rw [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, (min (u x) (n : ℝ≥0∞)) ^ p ∂Q :=
        lintegral_iSup (fun n => (hum.min measurable_const).pow_const _) hmono
    _ ≤ F := iSup_le hn

/-! ### The density of the preparation against `Q_{N,b}` -/

theorem s92_tilt_power {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) {b b0 p : ℝ} (hp : 0 < p)
    (hWb : GibbsWellDefined G N b μ) (hW0 : GibbsWellDefined G N b0 μ)
    (hW' : GibbsWellDefined G N (b + p * (b0 - b)) μ) :
    ∫⁻ X, (ENNReal.ofReal (pairNormalizer G N b μ / pairNormalizer G N b0 μ *
        Real.exp ((-b0 * N - -b * N) * pairEnergy G X μ))) ^ p ∂(pairGibbs G N b μ) =
      ENNReal.ofReal ((pairNormalizer G N b μ / pairNormalizer G N b0 μ) ^ p *
        (pairNormalizer G N b μ)⁻¹ * pairNormalizer G N (b + p * (b0 - b)) μ) := by
  have hKb := hWb.normalizer_pos
  have hK0 := hW0.normalizer_pos
  have hc : 0 ≤ pairNormalizer G N b μ / pairNormalizer G N b0 μ := (div_pos hKb hK0).le
  have e1 : ∀ X : EucConfig d N, (ENNReal.ofReal (pairNormalizer G N b μ / pairNormalizer G N b0 μ *
        Real.exp ((-b0 * N - -b * N) * pairEnergy G X μ))) ^ p =
      ENNReal.ofReal ((pairNormalizer G N b μ / pairNormalizer G N b0 μ) ^ p) *
        ENNReal.ofReal (Real.exp (p * ((-b0 * N - -b * N) * pairEnergy G X μ))) := by
    intro X
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc (Real.exp_pos _).le) hp.le,
      Real.mul_rpow hc (Real.exp_pos _).le, ← Real.exp_mul, ENNReal.ofReal_mul (Real.rpow_nonneg hc _)]
    congr 3; ring
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hΨm : Measurable (fun X : EucConfig d N => p * ((-b0 * N - -b * N) * pairEnergy G X μ)) :=
    measurable_const.mul (measurable_const.mul (wr9_measurable_pairEnergy hGm))
  have ht := wr9_tilt hGm (b := b) (Ψ := fun X : EucConfig d N => p * ((-b0 * N - -b * N) * pairEnergy G X μ))
    (W2 := fun X => -(b + p * (b0 - b)) * N * pairEnergy G X μ) hΨm (fun X => by ring)
  rw [ht, wr9_partition hW', ← ENNReal.ofReal_inv_of_pos hKb, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hc _) (inv_nonneg.2 hKb.le))]

theorem s92_power_const_le {K Kb K0 K' C0 p : ℝ} (hp : 1 < p) (hKb : 0 < Kb) (hK0 : 0 < K0) (hK' : 0 < K')
    (h1 : |Real.log Kb| ≤ C0) (h2 : |Real.log K0| ≤ C0) (h3 : |Real.log K'| ≤ C0) (hK : K = Kb) :
    (Kb / K0) ^ p * Kb⁻¹ * K' ≤ Real.exp (2 * p * C0) := by
  subst hK
  have hpos : 0 < (K / K0) ^ p * K⁻¹ * K' :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (div_pos hKb hK0) _) (inv_pos.2 hKb)) hK'
  rw [← Real.exp_log hpos]
  refine Real.exp_le_exp.2 ?_
  rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos (div_pos hKb hK0) _) (inv_pos.2 hKb)).ne' hK'.ne',
    Real.log_mul (Real.rpow_pos_of_pos (div_pos hKb hK0) _).ne' (inv_pos.2 hKb).ne', Real.log_rpow (div_pos hKb hK0),
    Real.log_div hKb.ne' hK0.ne', Real.log_inv]
  have := abs_le.1 h1
  have := abs_le.1 h2
  have := abs_le.1 h3
  nlinarith

/-- **Density of the quenched laws against `Q_{N,b}`**: with `p = 1 + b₀/(2(b+b₀))` and `b' = p b₀ - (p-1) b > 0`,
`‖d(Q_{N,b₀} κ)/dQ_{N,b}‖_{L^p(Q_{N,b})} ≤ e^{2 C₀}` for every Markov kernel `κ` preserving `Q_{N,b}`. -/
theorem s92_quench_density (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b b₀ : ℝ)
    (hb : 0 < b) (hb₀ : 0 < b₀) :
    ∃ p K : ℝ, 1 < p ∧ 0 ≤ K ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ κ : Kernel (EucConfig d N) (EucConfig d N), IsMarkovKernel κ →
      (HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ)).bind κ =
        HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ) →
      HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ)
        ((HRS.Whole.modulatedGibbs (rieszKernel d s) N b₀ (HRS.Whole.withDensityReal ρ)).bind κ) := by
  set η : ℝ := b₀ / (2 * (b + b₀)) with hη
  have hη0 : 0 < η := by positivity
  have hηe : η * (b + b₀) = b₀ / 2 := by rw [hη]; field_simp
  set p : ℝ := 1 + η with hpdef
  have hp1 : 1 < p := by linarith
  set bm : ℝ := min b (b₀ / 2) with hbm
  set bp : ℝ := max b (2 * b₀) + 1 with hbp
  have hbm0 : 0 < bm := lt_min hb (by linarith)
  have hbmp : bm < bp := by
    have : bm ≤ b := min_le_left _ _
    have : b ≤ max b (2 * b₀) := le_max_left _ _
    linarith
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L bm bp hbm0 hbmp
  refine ⟨p, Real.exp (2 * C0), hp1, (Real.exp_pos _).le, fun ρ hρ N hN κ hκ hinv => ?_⟩
  haveI := s92_isProb_mu hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set b' : ℝ := b + p * (b₀ - b) with hb'
  have hηb : η * b ≤ b₀ / 2 := by nlinarith
  have hηb0 : η * b₀ ≤ b₀ / 2 := by nlinarith
  have hb'lo : b₀ / 2 ≤ b' := by rw [hb', hpdef]; nlinarith
  have hb'hi : b' ≤ 3 * b₀ / 2 := by rw [hb', hpdef]; nlinarith
  have hmem_b : b ∈ Set.Icc bm bp := ⟨min_le_left _ _, by linarith [le_max_left b (2 * b₀)]⟩
  have hmem_b0 : b₀ ∈ Set.Icc bm bp := ⟨by linarith [min_le_right b (b₀ / 2)], by linarith [le_max_right b (2 * b₀)]⟩
  have hmem_b' : b' ∈ Set.Icc bm bp :=
    ⟨by linarith [min_le_right b (b₀ / 2)], by linarith [le_max_right b (2 * b₀)]⟩
  obtain ⟨hWb, hlb⟩ := hnorm ρ hρ N hN b hmem_b
  obtain ⟨hW0, hl0⟩ := hnorm ρ hρ N hN b₀ hmem_b0
  obtain ⟨hW', hl'⟩ := hnorm ρ hρ N hN b' hmem_b'
  have hGm := wr9_rieszKernel_pair_meas (d := d) s
  have hQeq : ∀ β : ℝ, HRS.Whole.modulatedGibbs (rieszKernel d s) N β μ =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N β μ := fun β => rfl
  unfold HasR2ActualDensity
  rw [hQeq b] at hinv ⊢
  rw [hQeq b₀]
  haveI hQprob : IsProbabilityMeasure (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) := wr9_gibbs_prob hWb
  haveI hQ0prob : IsProbabilityMeasure (pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ) := wr9_gibbs_prob hW0
  have ht := s32_tilt (G := fun x y => rieszKernel d s (x - y)) (N := N) (μ := μ) (a := b₀) (b := b) hGm hW0 hWb
  set φ0 : EucConfig d N → ℝ≥0∞ := fun X => ENNReal.ofReal
    (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b μ /
      pairNormalizer (fun x y => rieszKernel d s (x - y)) N b₀ μ *
      Real.exp ((-b₀ * N - -b * N) * pairEnergy (fun x y => rieszKernel d s (x - y)) X μ)) with hφ0
  have hφ0m : Measurable φ0 :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (wr9_measurable_pairEnergy hGm))))
  haveI hprobW : IsProbabilityMeasure ((pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ).withDensity φ0) := by
    rw [ht]; exact hQ0prob
  obtain ⟨hac, hLp⟩ := s92_markov_Lp (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) κ hinv hφ0m (by linarith : 1 < p)
  rw [ht] at hac hLp
  have hpow := s92_tilt_power (N := N) hGm (b0 := b₀) (by linarith : 0 < p) hWb hW0 hW'
  have hconst := s92_power_const_le (K := pairNormalizer (fun x y => rieszKernel d s (x - y)) N b μ) hp1 hWb.normalizer_pos
    hW0.normalizer_pos hW'.normalizer_pos hlb hl0 hl' rfl
  have hint : ∫⁻ X, φ0 X ^ p ∂(pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) ≤
      ENNReal.ofReal (Real.exp (2 * p * C0)) := by
    refine (le_of_eq hpow).trans (ENNReal.ofReal_le_ofReal hconst)
  have hP : IsProbabilityMeasure
      ((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ) :=
    ⟨by rw [Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]; simp⟩
  refine ⟨hP, hac, ?_⟩
  have hψ : Measurable (((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ).rnDeriv
      (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ)) := Measure.measurable_rnDeriv _ _
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    (hψ.ennreal_toReal.aestronglyMeasurable), ENNReal.toReal_ofReal hp0.le]
  have h1 : ∫⁻ X, ‖(((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ).rnDeriv
      (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) X).toReal‖ₑ ^ p
        ∂(pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) =
      ∫⁻ X, (((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ).rnDeriv
        (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) X) ^ p
        ∂(pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ((pairGibbs (fun x y => rieszKernel d s (x - y)) N b₀ μ).bind κ)
      (pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ)] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [h1]
  calc _ ≤ (ENNReal.ofReal (Real.exp (2 * p * C0))) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (hLp.trans hint) (by positivity)
    _ = ENNReal.ofReal (Real.exp (2 * C0)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
        congr 2; field_simp

/-- **Corollary S9.3** (`HRS.Whole.round2_quench_transfer`). -/
theorem round2_quench_transfer_proof : type_of% @HRS.Whole.round2_quench_transfer := by
  intro d hd s hs0 hs M L b b₀ B hb hb₀ r hr
  obtain ⟨p, Kq, hp, hKq, hdens⟩ := s92_quench_density hd hs0 hs M L b b₀ hb hb₀
  obtain ⟨CF, hCF0, hCF⟩ := s92_F_bound hd hs0 hs M L b p Kq B r hb hp hr
  obtain ⟨CL, hCL0, hCL⟩ := s92_linear_bound hd hs0 hs M L b p Kq r hb hp hr
  refine ⟨max CF CL, fun ρ hρ K hK hinv => ?_⟩
  intro P
  have hP : ∀ (t : ℝ≥0) (N : ℕ), 2 ≤ N →
      HasR2ActualDensity s b p Kq (HRS.Whole.withDensityReal ρ) (P t N) :=
    fun t N hN => hdens ρ hρ N hN (K N t) ((hK N).markov t) (hinv N hN t)
  refine ⟨fun h hh => ?_, ?_, fun C₁ h hj hh ha => ?_⟩
  · intro i N hN
    obtain ⟨h1, h2⟩ := hCF ρ hρ h hh N hN (P i N) (hP i N hN)
    exact ⟨h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      h2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  · intro i N hN a A ha hA
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
    exact (hCL ρ hρ N hN (P i N) (hP i N hN) a A ha hA).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0))
  · exact s92_tail (ι := ℝ≥0) hd hs0 hs M L b p Kq B r C₁ hb hp hr hρ hP hh ha

end HRS.MS.R2Mt
