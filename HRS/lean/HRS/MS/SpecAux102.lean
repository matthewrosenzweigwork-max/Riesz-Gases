import HRS.MS.SpecAux101

/-!
# S8M: the `L⁴` bound of the frozen statement for the constructed eigenfunctions (S8.7, R5)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_L4_witness`: for the spectral datum `D`, with `e_l = s8p_E (D.φ l)`,
`‖∇e_l‖_{L⁴(μ)} ≤ C4 exp(t₀ ω_l)` (`t₀ = C₂/4 + 1`, `C4 = e^{C₁/4}`), from `s8p_L4_unif` (SpecAux100), the log-Sobolev constant of the
thermal measure (`s8p_lsi_thermal`, SpecAux87, with the two-sided Gaussian bounds of `euc_thermal_gaussian_bounds_proof`) and the
Gross-Herbst argument (`s8p_gradL4`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

local notation "𝓢R" => SchwartzMap (Euc _) ℝ

theorem s8p_norm_gradient {d : ℕ} (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _

theorem s8p_eLpNorm_four_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hint : Integrable (fun x => f x ^ 4) μ) {B : ℝ}
    (hB : ∫ x, f x ^ 4 ∂μ ≤ B) :
    eLpNorm f 4 μ ≤ ENNReal.ofReal (B ^ ((1 : ℝ) / 4)) := by
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  have hfun : (fun x => ‖f x‖ ^ (4 : ℝ≥0∞).toReal) = fun x => f x ^ 4 := funext fun x => by
    rw [h4, Real.norm_of_nonneg (h0 x)]
    norm_cast
  have hmem : MemLp f 4 μ := by
    refine (integrable_norm_rpow_iff hf.aestronglyMeasurable (by norm_num) (by norm_num)).1 ?_
    rw [hfun]; exact hint
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), hfun, h4]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnn : 0 ≤ ∫ x, f x ^ 4 ∂μ := integral_nonneg fun x => by positivity
  rw [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
  exact Real.rpow_le_rpow hnn hB (by norm_num)

theorem s8p_exp_four_aux {om : ℝ} (hom : 0 ≤ om) : (2 * om) ^ 2 ≤ Real.exp om ^ 4 := by
  have h1 : 2 * om + 1 ≤ Real.exp (2 * om) := by linarith [Real.add_one_le_exp (2 * om)]
  have h2 : Real.exp (2 * om) = Real.exp om ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : 2 * om ≤ Real.exp om ^ 2 := by linarith
  calc (2 * om) ^ 2 ≤ (Real.exp om ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem s8p_L4_witness {d : ℕ} (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {M : ℝ}
    (h : S8pRho d ((d : ℝ) / 2) ρβ M) (D : S8pEigData d ((d : ℝ) / 2) β ρβ h) :
    ∃ t₀ C4 : ℝ, 0 < t₀ ∧ ∀ l, eLpNorm (fun x => ‖gradient (s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l)) x‖) 4
      (HRS.Whole.withDensityReal ρβ) ≤ ENNReal.ofReal (C4 * Real.exp (t₀ * D.om l)) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have H : Mov2dTh d ((d : ℝ) / 2) β a ρβ := ⟨hd, by positivity, by linarith, hβ, ha, hρ⟩
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := H.hsd
  obtain ⟨hρ', hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  have hmean : ∀ n, ∫ x, Real.sqrt (ρβ x) * D.φ n x = 0 := fun n =>
    s8p_mean_zero H ψ0 hψ0 (D.v n) (D.φ n) (D.hv n)
  have hdata := s8p_spectralData_of_eig hd a β ha hβ ρβ hρ h D
  -- Gaussian comparison and the log-Sobolev constant
  have hρeq : ρβ = thermalDensity d ((d : ℝ) / 2) a β := HRS.Whole.S78.s78_eq_thermalDensity hd hs0 hsd ha hβ hρ
  obtain ⟨c, hc, C, hbd, -⟩ := HRS.MS.Poinc.euc_thermal_gaussian_bounds_proof hd hs0 hsd a β ha hβ
  have hlo : ∀ x, c * gaussianComparison d a β x ≤ ρβ x := fun x => by rw [hρeq]; exact (hbd x).1
  have hhi : ∀ x, ρβ x ≤ C * gaussianComparison d a β x := fun x => by rw [hρeq]; exact (hbd x).2
  have hγ0 : 0 < gaussianComparison d a β (0 : Euc d) := by
    unfold gaussianComparison
    have : 0 < β * a / (2 * Real.pi) := by positivity
    positivity
  have hC0 : 0 ≤ C := by
    have h1 := (hlo 0).trans (hhi 0)
    have : c ≤ C := le_of_mul_le_mul_right h1 hγ0
    linarith
  have hρm : Measurable ρβ := hρ.1.1.measurable
  have hone : ∫ x, ρβ x = 1 := hρ.1.1.integral_one
  have hLSI := s8p_lsi_thermal ha hβ hρm hc hlo hhi hone
  have hCl0 : 0 ≤ 2 * C / c / (β * a) := by positivity
  obtain ⟨C1, C2, hC10, hC20, hU⟩ := s8p_L4_unif hd1 rfl hρ' hE h hβ hCl0 hLSI D.lam_pos
  refine ⟨C2 / 4 + 1, Real.exp (C1 / 4), by positivity, fun l => ?_⟩
  haveI := mov2e_isProb hρ'
  set φ := D.φ l with hφ
  set om := D.om l with homdef
  have hom0 : 0 < om := D.lam_pos.trans_le (D.lam_le l)
  have hnorm : ∫ x, s8p_E d ((d : ℝ) / 2) β ρβ φ x * (φ x / Real.sqrt (ρβ x))
      ∂(HRS.Whole.withDensityReal ρβ) = 1 := by
    rw [s8p_orth_e hd1 hs0.le hsd hρ' hE β φ φ (hmean l), D.pair H l l]; simp
  have hW2 := s8p_W2_le hd1 hs0 hsd hρ' hE hβ φ (hmean l) hnorm
  have hgI := hdata.grad_int l l
  have hgO := hdata.grad_orth l l
  have hconv : ∀ x, inner ℝ (gradient (s8p_E d ((d : ℝ) / 2) β ρβ φ) x)
      (gradient (s8p_E d ((d : ℝ) / 2) β ρβ φ) x) = ‖fderiv ℝ (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖ ^ 2 :=
    fun x => by rw [real_inner_self_eq_norm_sq, s8p_norm_gradient]
  have hint : Integrable (fun x => ‖fderiv ℝ (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖ ^ 2)
      (HRS.Whole.withDensityReal ρβ) := by
    refine hgI.congr (Filter.Eventually.of_forall fun x => ?_)
    exact hconv x
  have hom' : ∫ x, ‖fderiv ℝ (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρβ) = om := by
    simp_rw [← hconv]
    simpa using hgO
  obtain ⟨hI4, hle⟩ := hU φ om (D.lam_le l) hW2 (D.hS l) hint hom'
  have hf : Measurable (fun x => ‖gradient (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖) := by
    have : (fun x => ‖gradient (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖) =
        fun x => ‖fderiv ℝ (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖ := funext fun x => s8p_norm_gradient _ x
    rw [this]
    exact ((s8p_E_smooth hd1 hs0.le hsd hρ' hE β φ).continuous_fderiv (by simp)).norm.measurable
  have hfe : (fun x => ‖gradient (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖ ^ 4) =
      fun x => ‖fderiv ℝ (s8p_E d ((d : ℝ) / 2) β ρβ φ) x‖ ^ 4 := funext fun x => by rw [s8p_norm_gradient]
  have hnorm4 := s8p_eLpNorm_four_le hf (fun x => norm_nonneg _) (by rw [hfe]; exact hI4)
    (B := (2 * om) ^ 2 * Real.exp (C1 + C2 * om)) (by rw [hfe]; exact hle)
  refine hnorm4.trans (ENNReal.ofReal_le_ofReal ?_)
  set Y : ℝ := Real.exp (C1 / 4) * Real.exp ((C2 / 4 + 1) * om) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hY4 : (2 * om) ^ 2 * Real.exp (C1 + C2 * om) ≤ Y ^ 4 := by
    have : Y ^ 4 = Real.exp om ^ 4 * Real.exp (C1 + C2 * om) := by
      rw [hY, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (s8p_exp_four_aux hom0.le) (Real.exp_pos _).le
  calc ((2 * om) ^ 2 * Real.exp (C1 + C2 * om)) ^ ((1 : ℝ) / 4) ≤ (Y ^ 4) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hY4 (by norm_num)
    _ = Y := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num

end HRS.MS.Spec
