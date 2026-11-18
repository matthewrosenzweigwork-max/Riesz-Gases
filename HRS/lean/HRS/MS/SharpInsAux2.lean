import HRS.MS.SharpInsAux1
import HRS.MS.CondDens
import HRS.MS.StaticInput
import HRS.MS.WrInsAux2

/-!
# HRS.MS.SharpInsAux2 -- S7.6 `sharp_insertion_radius`, the core variance estimate at one `t`

Packet S76, namespace `HRS.MS.S76`, helper prefix `s76_`.  No frozen file is edited.

With `μ = ρ dx`, `λ = β/N`, `r > 0` and `x ∈ ℝ^d`, the pole exponent splits as
`λ g(x - y) = ψ(y) + χ(y)` with `ψ = λ g 1_{|x-y| < r}` ("in") and `χ = λ g 1_{|x-y| ≥ r}` ("out").

* `s76_lint_psi`, `s76_lint_chi_sq`: `∫ ψ dμ ≤ M λ |S| r^{d-s}/(d-s)` and
  `∫ χ² dμ ≤ M λ² |S| r^{d-2s}/(2s-d)` (`2s > d`), through `Q34.lintegral_conv_le`;
* `s76_c1`, `s76_c2`: the one- and two-particle moments of `ψ` under the pole law from the density
  bounds of `static_input`;
* `s76_var_of_evar`: an extended-variance bound gives `L²` and a real variance bound;
* `s76_core`: for an exchangeable probability law `Q` on `(ℝ^d)^n` with the static inputs,
  `|Var Σ(ψ+χ)(Y_i) - n E ψ(Y_0)²| ≤ n²(C₀G² + (C₀G)²) + v_T + 2√(v_S v_T)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.S76

open HRS.Whole (rieszKernel EucConfig)

variable {d : ℕ} {s : ℝ}

/-! ### The in/out split of the pole exponent -/

/-- `ψ(y) = λ |x-y|^{-s} 1_{|x-y| < r}`. -/
def s76_psi (d : ℕ) (s lam r : ℝ) (x y : Euc d) : ℝ :=
  if ‖x - y‖ < r then lam * ‖x - y‖ ^ (-s) else 0

/-- `χ(y) = λ |x-y|^{-s} 1_{|x-y| ≥ r}`. -/
def s76_chi (d : ℕ) (s lam r : ℝ) (x y : Euc d) : ℝ :=
  if r ≤ ‖x - y‖ then lam * ‖x - y‖ ^ (-s) else 0

theorem s76_meas_g (x : Euc d) : Measurable (fun y : Euc d => ‖x - y‖ ^ (-s)) :=
  (measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _

theorem s76_psi_meas (lam r : ℝ) (x : Euc d) : Measurable (s76_psi d s lam r x) := by
  unfold s76_psi
  exact Measurable.ite (measurableSet_lt (measurable_norm.comp (measurable_const.sub measurable_id))
    measurable_const) (measurable_const.mul (s76_meas_g x)) measurable_const

theorem s76_chi_meas (lam r : ℝ) (x : Euc d) : Measurable (s76_chi d s lam r x) := by
  unfold s76_chi
  exact Measurable.ite (measurableSet_le measurable_const
    (measurable_norm.comp (measurable_const.sub measurable_id)))
    (measurable_const.mul (s76_meas_g x)) measurable_const

theorem s76_psi_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (r : ℝ) (x y : Euc d) :
    0 ≤ s76_psi d s lam r x y := by
  unfold s76_psi
  split_ifs
  · exact mul_nonneg hlam (Real.rpow_nonneg (norm_nonneg _) _)
  · exact le_rfl

theorem s76_chi_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (r : ℝ) (x y : Euc d) :
    0 ≤ s76_chi d s lam r x y := by
  unfold s76_chi
  split_ifs
  · exact mul_nonneg hlam (Real.rpow_nonneg (norm_nonneg _) _)
  · exact le_rfl

theorem s76_psi_add_chi (hs0 : 0 < s) (lam r : ℝ) (x y : Euc d) :
    s76_psi d s lam r x y + s76_chi d s lam r x y = lam * rieszKernel d s (x - y) := by
  unfold s76_psi s76_chi
  rw [HRS.Whole.Q34.rieszKernel_eq hs0.ne']
  by_cases h : ‖x - y‖ < r
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

theorem s76_psi_le {lam : ℝ} (hlam : 0 ≤ lam) (r : ℝ) (x y : Euc d) :
    s76_psi d s lam r x y ≤ lam * ‖x - y‖ ^ (-s) := by
  unfold s76_psi
  split_ifs
  · exact le_rfl
  · exact mul_nonneg hlam (Real.rpow_nonneg (norm_nonneg _) _)

theorem s76_sq_rpow (w : Euc d) : (‖w‖ ^ (-s)) ^ 2 = ‖w‖ ^ (-(2 * s)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1; push_cast; ring

/-! ### Ball and tail integrals against a bounded density -/

theorem s76_lint_psi (hd : 1 ≤ d) (hsd : s < d) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {M : ℝ} (hM : ∀ x, ρ x ≤ M) {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 < r) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (s76_psi d s lam r x y) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (M * lam * (HRS.sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s)))) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  set H : Euc d → ℝ≥0∞ :=
    (ball (0 : Euc d) r).indicator (fun w => ENNReal.ofReal (lam * ‖w‖ ^ (-s))) with hH
  have hHm : Measurable H :=
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (measurable_norm.pow_const _))).indicator measurableSet_ball
  have hpt : ∀ y, ENNReal.ofReal (s76_psi d s lam r x y) = H (x - y) := by
    intro y
    by_cases h : ‖x - y‖ < r
    · simp [s76_psi, hH, h]
    · simp [s76_psi, hH, h]
  simp_rw [hpt]
  refine (HRS.Whole.Q34.lintegral_conv_le hρ hM H hHm x).trans ?_
  have hI : ∫⁻ w, H w =
      ENNReal.ofReal lam *
        ENNReal.ofReal (HRS.sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
    rw [hH, lintegral_indicator measurableSet_ball]
    simp_rw [ENNReal.ofReal_mul hlam]
    rw [lintegral_const_mul (ENNReal.ofReal lam) (f := fun w : Euc d => ENNReal.ofReal (‖w‖ ^ (-s)))
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))]
    rw [HRS.Whole.Q34.lintegral_ball_rpow hd hr (by linarith)]
  rw [hI, ← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul hM0, mul_assoc]

theorem s76_lint_chi_sq (hd : 1 ≤ d) (hds : (d : ℝ) < 2 * s) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {lam r : ℝ} (hr : 0 < r) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (s76_chi d s lam r x y ^ 2) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (M * lam ^ 2 *
        (HRS.sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ))))) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  set H : Euc d → ℝ≥0∞ := {w : Euc d | r ≤ ‖w‖}.indicator
    (fun w => ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (‖w‖ ^ (-(2 * s)))) with hH
  have hset : MeasurableSet {w : Euc d | r ≤ ‖w‖} := measurableSet_le measurable_const measurable_norm
  have hHm : Measurable H :=
    (measurable_const.mul
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))).indicator hset
  have hpt : ∀ y, ENNReal.ofReal (s76_chi d s lam r x y ^ 2) = H (x - y) := by
    intro y
    by_cases h : r ≤ ‖x - y‖
    · have : s76_chi d s lam r x y ^ 2 = lam ^ 2 * ‖x - y‖ ^ (-(2 * s)) := by
        simp only [s76_chi, h, if_true, mul_pow, s76_sq_rpow]
      rw [this, ENNReal.ofReal_mul (sq_nonneg _)]
      simp [hH, h]
    · simp [s76_chi, hH, h]
  simp_rw [hpt]
  refine (HRS.Whole.Q34.lintegral_conv_le hρ hM H hHm x).trans ?_
  have hI : ∫⁻ w, H w =
      ENNReal.ofReal (lam ^ 2) *
        ENNReal.ofReal (HRS.sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))) := by
    rw [hH, lintegral_indicator hset]
    rw [lintegral_const_mul (ENNReal.ofReal (lam ^ 2))
      (f := fun w : Euc d => ENNReal.ofReal (‖w‖ ^ (-(2 * s))))
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))]
    rw [HRS.Whole.Q34.lintegral_compl_rpow hd hr hds]
  rw [hI, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hM0, mul_assoc]

/-! ### Moments under the pole law -/

theorem s76_c1 {n : ℕ} (hn : 0 < n) {Q : Measure (EucConfig d n)} {μ : Measure (Euc d)} {C0 : ℝ}
    (hfirst : HRS.Whole.firstMarginal Q ≤ ENNReal.ofReal C0 • μ) (hC0 : 0 ≤ C0)
    {f : Euc d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≤ ENNReal.ofReal G) :
    ∫ Y, f (Y ⟨0, hn⟩) ∂Q ≤ C0 * G := by
  have hfm : HRS.Whole.firstMarginal Q = Q.map (fun Y : EucConfig d n => Y ⟨0, hn⟩) := by
    unfold HRS.Whole.firstMarginal; rw [dif_pos hn]
  have hm0 : Measurable (fun Y : EucConfig d n => Y ⟨0, hn⟩) := measurable_pi_apply _
  have e1 : ∫ Y, f (Y ⟨0, hn⟩) ∂Q = ∫ y, f y ∂(HRS.Whole.firstMarginal Q) := by
    rw [hfm]
    exact (integral_map hm0.aemeasurable hf.aestronglyMeasurable).symm
  rw [e1, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 hG0) ?_
  calc ∫⁻ y, ENNReal.ofReal (f y) ∂(HRS.Whole.firstMarginal Q)
      ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(ENNReal.ofReal C0 • μ) := lintegral_mono' hfirst le_rfl
    _ = ENNReal.ofReal C0 * ∫⁻ y, ENNReal.ofReal (f y) ∂μ := lintegral_smul_measure _ _
    _ ≤ ENNReal.ofReal C0 * ENNReal.ofReal G := by gcongr
    _ = ENNReal.ofReal (C0 * G) := (ENNReal.ofReal_mul hC0).symm

theorem s76_c2 {n : ℕ} (hn : 2 ≤ n) {Q : Measure (EucConfig d n)} {μ : Measure (Euc d)} [SFinite μ]
    {C0 : ℝ} (hsec : HRS.Whole.secondMarginal Q ≤ ENNReal.ofReal C0 • μ.prod μ) (hC0 : 0 ≤ C0)
    {f : Euc d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≤ ENNReal.ofReal G) :
    ∫ Y, f (Y ⟨0, by omega⟩) * f (Y ⟨1, by omega⟩) ∂Q ≤ C0 * G ^ 2 := by
  have hsm : HRS.Whole.secondMarginal Q =
      Q.map (fun Y : EucConfig d n => (Y ⟨0, by omega⟩, Y ⟨1, by omega⟩)) := by
    unfold HRS.Whole.secondMarginal; rw [dif_pos hn]
  have hG2 : Measurable (fun p : Euc d × Euc d => f p.1 * f p.2) :=
    (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hp : Measurable (fun Y : EucConfig d n => (Y ⟨0, by omega⟩, Y ⟨1, by omega⟩)) :=
    (measurable_pi_apply (⟨0, by omega⟩ : Fin n)).prodMk (measurable_pi_apply (⟨1, by omega⟩ : Fin n))
  have e1 : ∫ Y, f (Y ⟨0, by omega⟩) * f (Y ⟨1, by omega⟩) ∂Q =
      ∫ p, f p.1 * f p.2 ∂(HRS.Whole.secondMarginal Q) := by
    rw [hsm]
    exact (integral_map hp.aemeasurable hG2.aestronglyMeasurable).symm
  rw [e1, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun p => mul_nonneg (hf0 _) (hf0 _)) hG2.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 (sq_nonneg _)) ?_
  calc ∫⁻ p, ENNReal.ofReal (f p.1 * f p.2) ∂(HRS.Whole.secondMarginal Q)
      ≤ ∫⁻ p, ENNReal.ofReal (f p.1 * f p.2) ∂(ENNReal.ofReal C0 • μ.prod μ) :=
        lintegral_mono' hsec le_rfl
    _ = ENNReal.ofReal C0 * ∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) ∂(μ.prod μ) := by
        rw [lintegral_smul_measure]
        congr 1
        refine lintegral_congr fun p => ?_
        rw [ENNReal.ofReal_mul (hf0 _)]
    _ = ENNReal.ofReal C0 * ((∫⁻ y, ENNReal.ofReal (f y) ∂μ) * ∫⁻ y, ENNReal.ofReal (f y) ∂μ) := by
        have hA : AEMeasurable (fun y => ENNReal.ofReal (f y)) μ :=
          (ENNReal.measurable_ofReal.comp hf).aemeasurable
        rw [lintegral_prod_mul (μ := μ) (ν := μ) (f := fun y => ENNReal.ofReal (f y))
          (g := fun y => ENNReal.ofReal (f y)) hA hA]
    _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal G * ENNReal.ofReal G) := by gcongr
    _ = ENNReal.ofReal (C0 * G ^ 2) := by
        rw [← ENNReal.ofReal_mul hG0, ← ENNReal.ofReal_mul hC0, sq]

/-! ### From an extended variance bound to `L²` and a real variance bound -/

theorem s76_var_of_evar {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S : Ω → ℝ} (hS : Measurable S) {B : ℝ} (hB : 0 ≤ B)
    (h : evariance S Q ≤ ENNReal.ofReal B) : MemLp S 2 Q ∧ Var[S; Q] ≤ B := by
  have hlt : evariance S Q < ∞ := h.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(evariance_lt_top_iff_memLp hS.aestronglyMeasurable).1 hlt, ?_⟩
  show (evariance S Q).toReal ≤ B
  exact ENNReal.toReal_le_of_le_ofReal hB h

theorem s76_enorm_sq (z : ℝ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

/-! ### The core estimate at one `t` -/

/-- **Core variance estimate.**  `Q` is an exchangeable probability law on `(ℝ^d)^n` (`n ≥ 2`) whose
one- and two-particle marginals are dominated by `C₀ μ`, `C₀ μ ⊗ μ`, `μ = ρ dx`, `ρ ≤ M`, and whose
sums satisfy the extended variance bound `hvar` with weight `e^{-u g(x-y)}`, `u ≥ 0`;
`hrad` is the radial bound `∫ g² e^{-u g} dμ ≤ C_r J`.  Then for the split `ψ + χ` at radius `r`,
`|Var Σ(ψ+χ)(Y_i) - n E ψ(Y_0)²| ≤ n²(C₀G² + (C₀G)²) + C_v n B_T + 2√(C_v n λ² C_r J · C_v n B_T)`,
`G = Mλ|S| r^{d-s}/(d-s)`, `B_T = Mλ²|S| r^{d-2s}/(2s-d)`. -/
theorem s76_core (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hds : (d : ℝ) < 2 * s)
    {n : ℕ} (hn : 2 ≤ n) {Q : Measure (EucConfig d n)} [IsProbabilityMeasure Q]
    (hex : HRS.External.Entropy.IsExchangeable Q)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {C0 Cv Cr J : ℝ} (hC0 : 0 ≤ C0) (hCv : 0 ≤ Cv) (hCr : 0 ≤ Cr) (hJ : 0 ≤ J)
    {lam r u : ℝ} (hlam : 0 ≤ lam) (hr : 0 < r) (hu : 0 ≤ u) (x : Euc d)
    (hfirst : HRS.Whole.firstMarginal Q ≤ ENNReal.ofReal C0 • HRS.Whole.withDensityReal ρ)
    (hsec : HRS.Whole.secondMarginal Q ≤
      ENNReal.ofReal C0 • (HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))
    (hvar : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun Y : EucConfig d n => ∑ i, f (Y i)) Q ≤
        ENNReal.ofReal (Cv * n) * ∫⁻ y, ‖f y‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-u * rieszKernel d s (x - y))) ∂(HRS.Whole.withDensityReal ρ))
    (hrad : ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) ^ 2 *
        Real.exp (-(u * rieszKernel d s (x - y)))) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (Cr * J)) :
    |Var[fun Y : EucConfig d n => ∑ i, (s76_psi d s lam r x (Y i) + s76_chi d s lam r x (Y i)); Q] -
        n * ∫ Y, s76_psi d s lam r x (Y ⟨0, by omega⟩) ^ 2 ∂Q| ≤
      (n : ℝ) ^ 2 * (C0 * (M * lam * (HRS.sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s)))) ^ 2 +
        (C0 * (M * lam * (HRS.sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))))) ^ 2) +
      Cv * n * (M * lam ^ 2 * (HRS.sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ))))) +
      2 * Real.sqrt (Cv * n * (lam ^ 2 * (Cr * J)) *
        (Cv * n * (M * lam ^ 2 * (HRS.sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ))))))) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  haveI : SFinite (HRS.Whole.withDensityReal ρ) := by unfold HRS.Whole.withDensityReal; infer_instance
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have h2m : 0 < 2 * s - (d : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpsi0 := s76_psi_nonneg (d := d) (s := s) hlam r x
  have hchi0 := s76_chi_nonneg (d := d) (s := s) hlam r x
  have hpsim := s76_psi_meas (d := d) (s := s) lam r x
  have hchim := s76_chi_meas (d := d) (s := s) lam r x
  set G : ℝ := M * lam * (HRS.sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) with hGdef
  set BT : ℝ := M * lam ^ 2 *
    (HRS.sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))) with hBTdef
  have hG0 : 0 ≤ G := by
    have : 0 ≤ r ^ ((d : ℝ) - s) := Real.rpow_nonneg hr.le _
    rw [hGdef]; positivity
  have hBT0 : 0 ≤ BT := by
    have : 0 ≤ r ^ ((d : ℝ) - 2 * s) := Real.rpow_nonneg hr.le _
    rw [hBTdef]; positivity
  have hGint := s76_lint_psi hd hsd hρ hM hlam hr x
  have hBTint := s76_lint_chi_sq hd hds hρ hM (lam := lam) hr x
  have hexpb : ∀ y : Euc d, Real.exp (-u * rieszKernel d s (x - y)) ≤ 1 := by
    intro y
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ rieszKernel d s (x - y) := by
      rw [HRS.Whole.Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  -- variance of the in-part
  set BS : ℝ := lam ^ 2 * (Cr * J) with hBSdef
  have hBS0 : 0 ≤ BS := by rw [hBSdef]; positivity
  have hS_lint : ∫⁻ y, ‖s76_psi d s lam r x y‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-u * rieszKernel d s (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal BS := by
    calc ∫⁻ y, ‖s76_psi d s lam r x y‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-u * rieszKernel d s (x - y))) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (rieszKernel d s (x - y) ^ 2 *
            Real.exp (-(u * rieszKernel d s (x - y)))) ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          rw [s76_enorm_sq, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hg : rieszKernel d s (x - y) = ‖x - y‖ ^ (-s) :=
            HRS.Whole.Q34.rieszKernel_eq hs0.ne' _
          have h1 : s76_psi d s lam r x y ^ 2 ≤ (lam * ‖x - y‖ ^ (-s)) ^ 2 :=
            pow_le_pow_left₀ (hpsi0 y) (s76_psi_le hlam r x y) 2
          rw [neg_mul, hg]
          calc s76_psi d s lam r x y ^ 2 * Real.exp (-(u * ‖x - y‖ ^ (-s)))
              ≤ (lam * ‖x - y‖ ^ (-s)) ^ 2 * Real.exp (-(u * ‖x - y‖ ^ (-s))) :=
                mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
            _ = lam ^ 2 * ((‖x - y‖ ^ (-s)) ^ 2 * Real.exp (-(u * ‖x - y‖ ^ (-s)))) := by ring
      _ = ENNReal.ofReal (lam ^ 2) * ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) ^ 2 *
            Real.exp (-(u * rieszKernel d s (x - y)))) ∂(HRS.Whole.withDensityReal ρ) := by
          rw [lintegral_const_mul]
          refine ENNReal.measurable_ofReal.comp ?_
          have hgm : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
            (HRS.Whole.Q34.measurable_rieszKernel hs0.ne').comp
              (measurable_const.sub measurable_id)
          exact (hgm.pow_const 2).mul (Real.measurable_exp.comp (measurable_const.mul hgm).neg)
      _ ≤ ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (Cr * J) := by gcongr
      _ = ENNReal.ofReal BS := by rw [hBSdef, ENNReal.ofReal_mul (sq_nonneg _)]
  have hT_lint : ∫⁻ y, ‖s76_chi d s lam r x y‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-u * rieszKernel d s (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal BT := by
    refine le_trans (lintegral_mono fun y => ?_) hBTint
    rw [s76_enorm_sq]
    calc ENNReal.ofReal (s76_chi d s lam r x y ^ 2) *
          ENNReal.ofReal (Real.exp (-u * rieszKernel d s (x - y)))
        ≤ ENNReal.ofReal (s76_chi d s lam r x y ^ 2) * 1 := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hexpb y)
      _ = _ := mul_one _
  have hCvn : 0 ≤ Cv * (n : ℝ) := mul_nonneg hCv hn0
  have hvS := hvar _ hpsim
  have hvT := hvar _ hchim
  have hSm : Measurable (fun Y : EucConfig d n => ∑ i, s76_psi d s lam r x (Y i)) :=
    Finset.measurable_sum _ fun i _ => hpsim.comp (measurable_pi_apply i)
  have hTm : Measurable (fun Y : EucConfig d n => ∑ i, s76_chi d s lam r x (Y i)) :=
    Finset.measurable_sum _ fun i _ => hchim.comp (measurable_pi_apply i)
  obtain ⟨hSmem, hSvar⟩ := s76_var_of_evar hSm (mul_nonneg hCvn hBS0)
    (hvS.trans ((mul_le_mul' le_rfl hS_lint).trans (le_of_eq (ENNReal.ofReal_mul hCvn).symm)))
  obtain ⟨hTmem, hTvar⟩ := s76_var_of_evar hTm (mul_nonneg hCvn hBT0)
    (hvT.trans ((mul_le_mul' le_rfl hT_lint).trans (le_of_eq (ENNReal.ofReal_mul hCvn).symm)))
  have hc1 := s76_c1 (by omega : 0 < n) hfirst hC0 hpsim hpsi0 hG0 hGint
  have hc2 := s76_c2 hn hsec hC0 hpsim hpsi0 hG0 hGint
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have := s76_var_compare hex ⟨0, by omega⟩ ⟨1, by omega⟩ hab hpsim hpsi0 hSmem hTmem hc1 hc2
    hSvar hTvar
  exact this

end HRS.MS.S76
