import HRS.MS.S113EndAux4
import HRS.MS.R2MtAux1
import HRS.MP.RdRemainder

/-!
# S11.3 endpoint (worker S113X), part 6: the initial power moment (P3.2)

For two modulated Gibbs laws `Q_γ, Q_β` of the same probability measure, `Q_γ ≪ Q_β` and (`W:eq:r2-moving-initial-power`)
`∫(dQ_γ/dQ_β)^p dQ_β = K_β^{p-1} K_θ / K_γ^p`, `θ = pγ - (p-1)β` (the identity is proved for every `p > 1` with `K_γ, K_θ > 0`
and `Q_β` a probability measure); with `|log K| ≤ C` for the three temperatures the moment is `≤ exp((p-1)C_β + p C_γ + C_θ)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole HRS.MS.Wr
open HRS (Euc)

variable {d N : ℕ}

theorem s113x_pairGibbs_eq {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) {b : ℝ} (hK : 0 < pairNormalizer G N b μ) :
    pairGibbs G N b μ = (Measure.pi fun _ : Fin N => μ).withDensity (HRS.MS.R2Mt.s92_dens G N b μ) := by
  have hf : Measurable (fun X : EucConfig d N => ENNReal.ofReal (Real.exp (-b * N * pairEnergy G X μ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (wr9_measurable_pairEnergy hGm)))
  have e : HRS.MS.R2Mt.s92_dens G N b μ = (ENNReal.ofReal (pairNormalizer G N b μ))⁻¹ •
      (fun X : EucConfig d N => ENNReal.ofReal (Real.exp (-b * N * pairEnergy G X μ))) := by
    funext X
    simp only [HRS.MS.R2Mt.s92_dens, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hK.le), ENNReal.ofReal_inv_of_pos hK]
  rw [e, withDensity_smul _ hf]
  rfl

theorem s113x_weight_integrable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ} {b : ℝ}
    (hK : 0 < pairNormalizer G N b μ) :
    Integrable (fun X : EucConfig d N => Real.exp (-b * N * pairEnergy G X μ)) (Measure.pi fun _ : Fin N => μ) := by
  by_contra h
  have := integral_undef h
  unfold pairNormalizer at hK
  linarith

theorem s113x_initial_moment_formula {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) {β γ p : ℝ} (hp : 1 < p)
    (hWβ : GibbsWellDefined G N β μ) (hKγ : 0 < pairNormalizer G N γ μ)
    (hKθ : 0 < pairNormalizer G N (p * γ - (p - 1) * β) μ) :
    pairGibbs G N γ μ ≪ pairGibbs G N β μ ∧
      ∫⁻ Y, ENNReal.ofReal ((((pairGibbs G N γ μ).rnDeriv (pairGibbs G N β μ)) Y).toReal ^ p)
          ∂(pairGibbs G N β μ) =
        ENNReal.ofReal ((pairNormalizer G N β μ) ^ (p - 1) * pairNormalizer G N (p * γ - (p - 1) * β) μ /
          (pairNormalizer G N γ μ) ^ p) := by
  set Kβ := pairNormalizer G N β μ with hKβdef
  set Kγ := pairNormalizer G N γ μ with hKγdef
  set Kθ := pairNormalizer G N (p * γ - (p - 1) * β) μ with hKθdef
  have hKβ : 0 < Kβ := hWβ.normalizer_pos
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  set F : EucConfig d N → ℝ := fun X => pairEnergy G X μ with hF
  have hFm : Measurable F := wr9_measurable_pairEnergy hGm
  have hQprob : IsProbabilityMeasure (pairGibbs G N β μ) := HRS.MS.R2Mt.s92_isProb_gibbs hWβ
  have hψβm : Measurable (HRS.MS.R2Mt.s92_dens G N β μ) := HRS.MS.R2Mt.s92_dens_meas hGm β
  set h : EucConfig d N → ℝ≥0∞ := fun X =>
    ENNReal.ofReal ((Kβ / Kγ) * Real.exp (-(γ - β) * N * F X)) with hh
  have hhm : Measurable h :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hFm)))
  have hψ : HRS.MS.R2Mt.s92_dens G N γ μ = HRS.MS.R2Mt.s92_dens G N β μ * h := by
    funext X
    simp only [HRS.MS.R2Mt.s92_dens, Pi.mul_apply, hh, hF]
    rw [← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hKβ.le) (Real.exp_pos _).le)]
    congr 1
    have : Real.exp (-γ * N * pairEnergy G X μ) =
        Real.exp (-β * N * pairEnergy G X μ) * Real.exp (-(γ - β) * N * pairEnergy G X μ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    simp only [← hKγdef, ← hKβdef]
    field_simp
  have hf : pairGibbs G N γ μ = (pairGibbs G N β μ).withDensity h := by
    have e1 := s113x_pairGibbs_eq (N := N) hGm hKγ
    have e2 := s113x_pairGibbs_eq (N := N) hGm hKβ
    rw [e1, e2, hψ, withDensity_mul π hψβm hhm]
  have hac : pairGibbs G N γ μ ≪ pairGibbs G N β μ := by
    rw [hf]; exact withDensity_absolutelyContinuous _ _
  refine ⟨hac, ?_⟩
  have hrn : (pairGibbs G N γ μ).rnDeriv (pairGibbs G N β μ) =ᵐ[pairGibbs G N β μ] h := by
    rw [hf]; exact Measure.rnDeriv_withDensity _ hhm
  have hg0 : ∀ X, 0 ≤ (Kβ / Kγ) * Real.exp (-(γ - β) * N * F X) := fun X =>
    mul_nonneg (div_nonneg hKβ.le hKγ.le) (Real.exp_pos _).le
  have step1 : ∫⁻ Y, ENNReal.ofReal ((((pairGibbs G N γ μ).rnDeriv (pairGibbs G N β μ)) Y).toReal ^ p)
        ∂(pairGibbs G N β μ) =
      ∫⁻ Y, ENNReal.ofReal (((Kβ / Kγ) * Real.exp (-(γ - β) * N * F Y)) ^ p) ∂(pairGibbs G N β μ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hrn] with Y hY
    rw [hY, hh]
    simp only
    rw [ENNReal.toReal_ofReal (hg0 Y)]
  have hgm : Measurable (fun Y : EucConfig d N =>
      ENNReal.ofReal (((Kβ / Kγ) * Real.exp (-(γ - β) * N * F Y)) ^ p)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hFm))).pow_const p)
  have step2 : ∫⁻ Y, ENNReal.ofReal (((Kβ / Kγ) * Real.exp (-(γ - β) * N * F Y)) ^ p)
        ∂(pairGibbs G N β μ) =
      ∫⁻ Y, ENNReal.ofReal (Kβ ^ (p - 1) / Kγ ^ p * Real.exp (-(p * γ - (p - 1) * β) * N * F Y)) ∂π := by
    rw [s113x_pairGibbs_eq (N := N) hGm hKβ, lintegral_withDensity_eq_lintegral_mul _ hψβm hgm]
    refine lintegral_congr fun Y => ?_
    simp only [Pi.mul_apply, HRS.MS.R2Mt.s92_dens, hF]
    rw [← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hKβ.le) (Real.exp_pos _).le)]
    congr 1
    rw [Real.mul_rpow (div_nonneg hKβ.le hKγ.le) (Real.exp_pos _).le, Real.div_rpow hKβ.le hKγ.le,
      ← Real.exp_mul, Real.rpow_sub_one hKβ.ne']
    have : Real.exp (-β * N * pairEnergy G Y μ) * Real.exp (-(γ - β) * N * F Y * p) =
        Real.exp (-(p * γ - (p - 1) * β) * N * pairEnergy G Y μ) := by
      rw [← Real.exp_add]; congr 1; simp only [hF]; ring
    calc Kβ⁻¹ * Real.exp (-β * N * pairEnergy G Y μ) * (Kβ ^ p / Kγ ^ p * Real.exp (-(γ - β) * N * F Y * p))
        = Kβ⁻¹ * Kβ ^ p / Kγ ^ p * (Real.exp (-β * N * pairEnergy G Y μ) * Real.exp (-(γ - β) * N * F Y * p)) := by
          ring
      _ = Kβ ^ p / Kβ / Kγ ^ p * Real.exp (-(p * γ - (p - 1) * β) * N * pairEnergy G Y μ) := by
          rw [this]; field_simp
  rw [step1, step2]
  have hc0 : 0 ≤ Kβ ^ (p - 1) / Kγ ^ p :=
    div_nonneg (Real.rpow_nonneg hKβ.le _) (Real.rpow_nonneg hKγ.le _)
  have hint := s113x_weight_integrable (N := N) hKθ
  calc ∫⁻ Y, ENNReal.ofReal (Kβ ^ (p - 1) / Kγ ^ p * Real.exp (-(p * γ - (p - 1) * β) * N * F Y)) ∂π
      = ∫⁻ Y, ENNReal.ofReal (Kβ ^ (p - 1) / Kγ ^ p) *
          ENNReal.ofReal (Real.exp (-(p * γ - (p - 1) * β) * N * F Y)) ∂π := by
        refine lintegral_congr fun Y => ?_
        rw [ENNReal.ofReal_mul hc0]
    _ = ENNReal.ofReal (Kβ ^ (p - 1) / Kγ ^ p) * ENNReal.ofReal Kθ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal (Kβ ^ (p - 1) * Kθ / Kγ ^ p) := by
        rw [← ENNReal.ofReal_mul hc0]
        congr 1
        ring

theorem s113x_moment_numeric {Kβ Kγ Kθ Cβ Cγ Cθ p : ℝ} (hp : 1 < p) (hKβ : 0 < Kβ) (hKγ : 0 < Kγ) (hKθ : 0 < Kθ)
    (hβ : |Real.log Kβ| ≤ Cβ) (hγ : |Real.log Kγ| ≤ Cγ) (hθ : |Real.log Kθ| ≤ Cθ) :
    Kβ ^ (p - 1) * Kθ / Kγ ^ p ≤ Real.exp ((p - 1) * Cβ + p * Cγ + Cθ) := by
  have h1 : Kβ ^ (p - 1) ≤ Real.exp ((p - 1) * Cβ) := by
    rw [Real.rpow_def_of_pos hKβ, mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hβ) (by linarith))
  have h2 : Kθ ≤ Real.exp Cθ := by
    calc Kθ = Real.exp (Real.log Kθ) := (Real.exp_log hKθ).symm
      _ ≤ Real.exp Cθ := Real.exp_le_exp.2 (le_trans (le_abs_self _) hθ)
  have h3 : (Kγ ^ p)⁻¹ ≤ Real.exp (p * Cγ) := by
    rw [Real.rpow_def_of_pos hKγ, ← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 hγ).1
    nlinarith
  rw [div_eq_mul_inv]
  calc Kβ ^ (p - 1) * Kθ * (Kγ ^ p)⁻¹ ≤ Real.exp ((p - 1) * Cβ) * Real.exp Cθ * Real.exp (p * Cγ) := by
        gcongr
    _ = Real.exp ((p - 1) * Cβ + p * Cγ + Cθ) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem s113x_pairGibbs_zero {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (G : Euc d → Euc d → ℝ) :
    pairNormalizer G N 0 μ = 1 ∧ pairGibbs G N 0 μ = Measure.pi fun _ : Fin N => μ := by
  have h1 : pairNormalizer G N 0 μ = 1 := by
    unfold pairNormalizer
    simp
  refine ⟨h1, ?_⟩
  unfold pairGibbs
  rw [h1]
  simp

theorem s113x_measurable_G (s : ℝ) :
    Measurable (Function.uncurry fun x y : Euc d => rieszKernel d s (x - y)) :=
  (HRS.MP.RdRem.mrr_measurable_rieszKernel s).comp (measurable_fst.sub measurable_snd)

/-- Initial moment, `γ > 0`: ac and uniform bound over the round-2 densities. -/
theorem s113x_initial_moment_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L : ℝ) {β γ p₀ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hp₀ : 1 < p₀) (hθ : 0 < p₀ * γ - (p₀ - 1) * β) :
    ∃ K : ℝ, ∀ ρ0 : Euc d → ℝ, IsRound2Density d s M L ρ0 → ∀ N : ℕ, 2 ≤ N →
      HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal ρ0) ≪
        HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ0) ∧
      ∫⁻ Y, ENNReal.ofReal ((((HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal ρ0)).rnDeriv
          (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ0))) Y).toReal ^ p₀)
        ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ0)) ≤ ENNReal.ofReal K := by
  set θ : ℝ := p₀ * γ - (p₀ - 1) * β with hθdef
  set bm : ℝ := min β (min γ θ) with hbm
  set bp : ℝ := max β (max γ θ) + 1 with hbp
  have hbm0 : 0 < bm := lt_min hβ (lt_min hγ hθ)
  have hbmp : bm < bp := by
    have : bm ≤ max β (max γ θ) := (min_le_left _ _).trans (le_max_left _ _)
    linarith
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Mt.s92_normalizer_bounds hd hs0 hs M L bm bp hbm0 hbmp
  refine ⟨Real.exp ((p₀ - 1) * C + p₀ * C + C), fun ρ0 hρ0 N hN => ?_⟩
  haveI := HRS.MS.R2Mt.s92_isProb_mu hρ0.prob
  have hmem : ∀ b, bm ≤ b → b ≤ bp - 1 → b ∈ Set.Icc bm bp := fun b h1 h2 => ⟨h1, by linarith⟩
  have hβm : β ∈ Set.Icc bm bp := hmem β (min_le_left _ _) (by simp [hbp])
  have hγm : γ ∈ Set.Icc bm bp := hmem γ ((min_le_right _ _).trans (min_le_left _ _)) (by
    simp only [hbp, add_sub_cancel_right]; exact (le_max_left _ _).trans (le_max_right _ _))
  have hθm : θ ∈ Set.Icc bm bp := hmem θ ((min_le_right _ _).trans (min_le_right _ _)) (by
    simp only [hbp, add_sub_cancel_right]; exact (le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨hWβ, hlβ⟩ := hC ρ0 hρ0 N hN β hβm
  obtain ⟨hWγ, hlγ⟩ := hC ρ0 hρ0 N hN γ hγm
  obtain ⟨hWθ, hlθ⟩ := hC ρ0 hρ0 N hN θ hθm
  have hGm := s113x_measurable_G (d := d) s
  obtain ⟨hac, hform⟩ := s113x_initial_moment_formula hGm hp₀ hWβ hWγ.normalizer_pos hWθ.normalizer_pos
  refine ⟨hac, ?_⟩
  refine hform.trans_le (ENNReal.ofReal_le_ofReal ?_)
  exact s113x_moment_numeric hp₀ hWβ.normalizer_pos hWγ.normalizer_pos hWθ.normalizer_pos hlβ hlγ hlθ

/-- Initial moment, `γ = 0` (iid preparation), from bounded negative-temperature normalizers. -/
theorem s113x_initial_moment_zero (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L : ℝ) {β p₀ K₀ : ℝ}
    (hβ : 0 < β) (hp₀ : 1 < p₀) :
    ∃ K : ℝ, ∀ ρ0 : Euc d → ℝ, IsRound2Density d s M L ρ0 → ∀ N : ℕ, 2 ≤ N →
      (0 < HRS.Whole.gibbsNormalizer (rieszKernel d s) N (p₀ * 0 - (p₀ - 1) * β) (HRS.Whole.withDensityReal ρ0) ∧
        |Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N (p₀ * 0 - (p₀ - 1) * β)
          (HRS.Whole.withDensityReal ρ0))| ≤ K₀) →
      (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ0) ≪
        HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ0) ∧
      ∫⁻ Y, ENNReal.ofReal (((((Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ0)).rnDeriv
          (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ0))) Y).toReal ^ p₀)
        ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ0)) ≤ ENNReal.ofReal K := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Mt.s92_normalizer_bounds hd hs0 hs M L β (β + 1) hβ (by linarith)
  refine ⟨Real.exp ((p₀ - 1) * C + p₀ * 0 + K₀), fun ρ0 hρ0 N hN hθ => ?_⟩
  haveI := HRS.MS.R2Mt.s92_isProb_mu hρ0.prob
  obtain ⟨hWβ, hlβ⟩ := hC ρ0 hρ0 N hN β ⟨le_rfl, by linarith⟩
  have hGm := s113x_measurable_G (d := d) s
  obtain ⟨hK0, hP0⟩ := s113x_pairGibbs_zero (N := N) (μ := HRS.Whole.withDensityReal ρ0)
    (fun x y => rieszKernel d s (x - y))
  have hθ' : 0 < pairNormalizer (fun x y => rieszKernel d s (x - y)) N (p₀ * 0 - (p₀ - 1) * β)
      (HRS.Whole.withDensityReal ρ0) := hθ.1
  obtain ⟨hac, hform⟩ := s113x_initial_moment_formula hGm hp₀ hWβ (by rw [hK0]; exact one_pos) hθ'
  rw [hP0] at hac hform
  refine ⟨hac, ?_⟩
  refine hform.trans_le (ENNReal.ofReal_le_ofReal ?_)
  have := s113x_moment_numeric (Kγ := 1) (Cγ := 0) hp₀ hWβ.normalizer_pos one_pos hθ' hlβ (by simp) hθ.2
  rw [hK0]
  exact this

end HRS.MS.S113BD
