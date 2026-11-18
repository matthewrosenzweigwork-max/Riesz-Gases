import HRS.ME.FamUF7
import HRS.ME.FamUF8
import HRS.ME.FamUF9
import HRS.ME.CritUnifMode
import HRS.ME.CritUnifAssembly

/-!
# Chunk E, packet F10 (namespace `HRS.ME.FamU`): V-uniform mode forcing, single-mode bound and `Uniform417`

Originals (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`; `Bf : ℕ → ℝ` is fixed data, `V` is a bound variable):
* `HRS.ME.Crit.unif_mode_forcing` (`HRS/ME/CritUnifMode.lean:23`) becomes `unif_mode_forcingV`. The hypothesis
  `hpkg : UnifModePackage d hd V hV βm βp hβm` becomes `UnifModePackageFam d hd βm βp hβm Bf` (F8). The constant
  `C₄ * Cmax * C₈ ^ 2 * (…)` is chosen before `V`: `C₈` is the package constant, `C₄` (`mode_window_bound_proof`) and
  `CLZ` (`lz_scalar_proof`) are V-free, `Cmax` depends on `βm`, `T` only. The body is the original proof for the
  specialisation `hpkg V hV hVB`.
* `HRS.ME.Crit.unif_single_j` (`HRS/ME/CritUnifAssembly.lean:27`) becomes `unif_single_jV`. The fixed data are
  `d hd s hs0 hsd hcrit βm βp hβm T hT Bf`. The hypotheses `hdec` and `hmode` are the family shapes of `UnifDecayFam`
  (F9) and `UnifModeForcingFam` (F8) written with the general `s` (`hcrit : s = d/2` as in the original); at `s = d/2` they
  are definitionally `UnifDecayFam d hs0 hsd βm βp hβm Bf` and `∀ c, 0 < c → UnifModeForcingFam d hs0 hsd βm βp hβm c T Bf`.
  The constant `C₂ = C_B1 * C_D ^ 2 * Sg ^ 2` is chosen before `V`.
* `HRS.ME.Crit.uniform417_of_unif` (`HRS/ME/CritUnifAssembly.lean:231`) becomes `uniform417_of_unifV`:
  `UnifDecayFam` and `∀ c, 0 < c → UnifModeForcingFam` give `Uniform417Fam d hs0 hsd βm βp hβm m T Bf` (F7); the constant
  `Real.sqrt (C₂ * Ssum)` is chosen before `V`.
No new mathematics: every constant of the originals is V-free or is chosen from the family hypotheses before `V`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.FamU

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.ME HRS.ME.Crit

variable {d : ℕ}

/-- **F10.1 (V-uniform copy of `unif_mode_forcing`, family form).** The package `hpkg` is the family
`UnifModePackageFam` (chosen before `V`); the constant of the conclusion is `C₄ * Cmax * C₈ ^ 2 * (…)`, chosen before `V`. -/
theorem unif_mode_forcingV (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (Bf : ℕ → ℝ) (hpkg : UnifModePackageFam d hd βm βp hβm Bf)
    (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 ≤ T) : UnifModeForcingFam d hs0 hsd βm βp hβm c T Bf := by
  classical
  unfold UnifModePackageFam at hpkg
  unfold UnifModeForcingFam
  obtain ⟨C₈, hC₈0, hpkg⟩ := hpkg
  obtain ⟨C₄, hC₄0, hwin⟩ := mode_window_bound_proof c hc T hT
  obtain ⟨CLZ, hCLZ0, hlzS⟩ := lz_scalar_proof
  obtain ⟨Cmax, hCmax⟩ : ∃ z : ℝ, z = max 1 (max (CLZ * (1 + βm⁻¹ * T)) (8 * βm⁻¹)) := ⟨_, rfl⟩
  have hCmax1 : 1 ≤ Cmax := by rw [hCmax]; exact le_max_left _ _
  have hCmaxLZ : CLZ * (1 + βm⁻¹ * T) ≤ Cmax := by
    rw [hCmax]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCmax8 : 8 * βm⁻¹ ≤ Cmax := by
    rw [hCmax]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hCmax0 : 0 ≤ Cmax := by linarith
  refine ⟨C₄ * Cmax * C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2), ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ (((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hC₄0 hCmax0) (sq_nonneg _)) h2
  intro V hV hVB β hβ ρβ hρβ hρS hρpos
  have hpkg := hpkg V hV hVB
  intro N hN Ω _ P _ X₀ W X a ha hflow l Γ hΓ γ γ' hγ hγ' hbd
  have hβ' : 0 < β := hβm.trans_le hβ.1
  have hβinv : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ.1
  have hβinv0 : 0 ≤ β⁻¹ * T := mul_nonneg (inv_nonneg.2 hβ'.le) hT
  have hβT : β⁻¹ * T ≤ βm⁻¹ * T := mul_le_mul_of_nonneg_right hβinv hT
  have hI : 1 + β⁻¹ * T ≤ 1 + βm⁻¹ * T := by linarith
  have hCmaxLZβ : CLZ * (1 + β⁻¹ * T) ≤ Cmax := (mul_le_mul_of_nonneg_left hI hCLZ0.le).trans hCmaxLZ
  have hCmax8β : 8 * β⁻¹ ≤ Cmax := (mul_le_mul_of_nonneg_left hβinv (by norm_num : (0 : ℝ) ≤ 8)).trans hCmax8
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the single-mode data: mode package
  obtain ⟨F, G, E, hFm, hGm, hEm, hFlz, hFc, hFG, hFmean, hid, hFb, hEb, hGb, hcgs⟩ :=
    hpkg β hβ ρβ hρβ hρS hρpos N hN (Torus.realMode l) (mode417B_isSmooth l)
  -- the seminorm constant `ς₀`
  obtain ⟨hps0, hps⟩ := mode417B_ps_le (8 * d + 80) l
  obtain ⟨ς₀, hς₀⟩ : ∃ z : ℝ, z = C₈ * ((((8 * d + 80 : ℕ) : ℝ) + 1) *
      (Real.sqrt 2 * Lattice.jp l.1 ^ (8 * d + 80))) := ⟨_, rfl⟩
  have hς₀0 : 0 ≤ ς₀ := by rw [hς₀]; exact mul_nonneg hC₈0 (le_trans hps0 hps)
  have hps' : C₈ * posSeminorm (8 * d + 80) (Torus.realMode l) ≤ ς₀ := by
    rw [hς₀]; exact mul_le_mul_of_nonneg_left hps hC₈0
  have hps'0 : 0 ≤ C₈ * posSeminorm (8 * d + 80) (Torus.realMode l) := mul_nonneg hC₈0 hps0
  have hq0 : 0 ≤ ς₀ ^ 2 / N := by positivity
  have hqsq : ∀ x : ℝ, 0 ≤ x → x ≤ ς₀ → x ^ 2 / N ≤ ς₀ ^ 2 / N := fun x hx0 hxle =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hxle 2) hN0.le
  -- the constant `ς`
  obtain ⟨ς, hς⟩ : ∃ z : ℝ, z = Real.sqrt (Cmax * (ς₀ ^ 2 / N)) := ⟨_, rfl⟩
  have hς0 : 0 ≤ ς := by rw [hς]; exact Real.sqrt_nonneg _
  have hς2 : ς ^ 2 = Cmax * (ς₀ ^ 2 / N) := by
    rw [hς]; exact Real.sq_sqrt (mul_nonneg hCmax0 hq0)
  have hqς : ς₀ ^ 2 / N ≤ ς ^ 2 := by
    rw [hς2]; exact le_mul_of_one_le_left hq0 hCmax1
  have hF : ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
      ENNReal.ofReal (ς ^ 2) :=
    hFb.trans (ENNReal.ofReal_le_ofReal ((hqsq _ hps'0 hps').trans hqς))
  have hE : ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
      ENNReal.ofReal (ς ^ 2) :=
    hEb.trans (ENNReal.ofReal_le_ofReal ((hqsq _ hps'0 hps').trans hqς))
  -- the martingale part: Dynkin formula for the closed generator
  obtain ⟨hint, hcont, hmax0⟩ :=
    dynkin_closedGenerator_proof hd hs0 hsd V hV β hβ' hN P X₀ W X (a + T) hflow F G hFm hGm hFc hFG
  have hmax : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + T →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (ς ^ 2 * (t - u)) := by
    intro u t hu hut htH
    have ht0 : 0 ≤ t - u := by linarith
    have hmul0 : 0 ≤ 8 * β⁻¹ * (t - u) := mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hβ'.le)) ht0
    have hx : (C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N ≤ ς₀ ^ 2 / N :=
      hqsq _ hps'0 hps'
    have hreal : 8 * β⁻¹ * (t - u) * ((C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N) ≤
        ς ^ 2 * (t - u) := by
      have s1 := mul_le_mul_of_nonneg_left hx hmul0
      have s2 : 8 * β⁻¹ * (t - u) * (ς₀ ^ 2 / N) ≤ Cmax * (t - u) * (ς₀ ^ 2 / N) := by
        apply mul_le_mul_of_nonneg_right _ hq0
        exact mul_le_mul_of_nonneg_right hCmax8β ht0
      rw [hς2]
      nlinarith
    refine (hmax0 u t hu hut htH).trans ?_
    calc ENNReal.ofReal (8 * β⁻¹ * (t - u)) * ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2
          ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β)
        ≤ ENNReal.ofReal (8 * β⁻¹ * (t - u)) *
            ENNReal.ofReal ((C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N) :=
          by gcongr
      _ = ENNReal.ofReal (8 * β⁻¹ * (t - u) *
            ((C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N)) :=
          (ENNReal.ofReal_mul hmul0).symm
      _ ≤ ENNReal.ofReal (ς ^ 2 * (t - u)) := ENNReal.ofReal_le_ofReal hreal
  -- the Lyons-Zheng bound for `F`
  set μ := canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β with hμ
  have hFsq_int : Integrable (fun Y => F Y ^ 2) μ := hFlz.memLp.integrable_sq
  have hFsq_nn : 0 ≤ᵐ[μ] (fun Y => F Y ^ 2) :=
    Filter.Eventually.of_forall fun Y => by show (0 : ℝ) ≤ F Y ^ 2; exact sq_nonneg _
  have hA : ∫ Y, F Y ^ 2 ∂μ ≤ ς₀ ^ 2 / N := by
    refine (ENNReal.ofReal_le_ofReal_iff hq0).1 ?_
    rw [ofReal_integral_eq_lintegral_ofReal hFsq_int hFsq_nn]
    exact hFb.trans (ENNReal.ofReal_le_ofReal (hqsq _ hps'0 hps'))
  have hB_nn : 0 ≤ᵐ[μ] (fun Y => configGradSq F Y) :=
    Filter.Eventually.of_forall fun Y => by
      show (0 : ℝ) ≤ configGradSq F Y
      unfold configGradSq
      exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hB : ∫ Y, configGradSq F Y ∂μ ≤ ς₀ ^ 2 / N := by
    refine (ENNReal.ofReal_le_ofReal_iff hq0).1 ?_
    rw [ofReal_integral_eq_lintegral_ofReal hFlz.energy hB_nn]
    exact hcgs.trans (ENNReal.ofReal_le_ofReal (hqsq _ hps'0 hps'))
  have hA0 : 0 ≤ ∫ Y, F Y ^ 2 ∂μ := integral_nonneg fun Y => sq_nonneg _
  have hB0 : 0 ≤ ∫ Y, configGradSq F Y ∂μ := integral_nonneg fun Y => by
    show (0 : ℝ) ≤ configGradSq F Y
    unfold configGradSq
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hlz0 := hlzS d N hd hN ((d : ℝ) / 2) hs0 hsd V hV β hβ' T a hT ha P X₀ W X hflow F hFlz
  rw [← hμ] at hlz0
  rw [hFmean] at hlz0
  simp only [sub_zero] at hlz0
  have hLZ : ∫⁻ ω, ⨆ t ∈ ratTimes a T, ENNReal.ofReal (F (X t.toNNReal ω) ^ 2) ∂P ≤
      ENNReal.ofReal (ς ^ 2) := by
    refine hlz0.trans ?_
    have hreal : CLZ * (∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ) ≤ ς ^ 2 := by
      have h1 : ∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ ≤
          (1 + β⁻¹ * T) * (ς₀ ^ 2 / N) := by
        have m1 := mul_le_mul_of_nonneg_left hB hβinv0
        have e1 : (1 + β⁻¹ * T) * (ς₀ ^ 2 / N) = ς₀ ^ 2 / N + β⁻¹ * T * (ς₀ ^ 2 / N) := by ring
        rw [e1]
        linarith
      have h2 : CLZ * ((1 + β⁻¹ * T) * (ς₀ ^ 2 / N)) ≤ Cmax * (ς₀ ^ 2 / N) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCmaxLZβ hq0
      calc CLZ * (∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ)
          ≤ CLZ * ((1 + β⁻¹ * T) * (ς₀ ^ 2 / N)) := mul_le_mul_of_nonneg_left h1 hCLZ0.le
        _ ≤ Cmax * (ς₀ ^ 2 / N) := h2
        _ = ς ^ 2 := hς2.symm
    calc ENNReal.ofReal CLZ * (ENNReal.ofReal (∫ Y, F Y ^ 2 ∂μ) +
            ENNReal.ofReal (β⁻¹ * T) * ENNReal.ofReal (∫ Y, configGradSq F Y ∂μ))
        = ENNReal.ofReal (CLZ * (∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ)) := by
          rw [ENNReal.ofReal_mul hCLZ0.le, ENNReal.ofReal_add hA0 (mul_nonneg hβinv0 hB0),
            ENNReal.ofReal_mul hβinv0]
      _ ≤ ENNReal.ofReal (ς ^ 2) := ENNReal.ofReal_le_ofReal hreal
  -- the integrand identification: the forcing statistic equals `-G + E` along the flow
  have hsol : IsStrongSolution P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ') (a + T) X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exact absurd h1 (by omega)
  have hgood : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ a + T →
      forcingStat ((d : ℝ) / 2) V β ρβ (Torus.realMode l) (X r.toNNReal ω) =
        -G (X r.toNNReal ω) + E (X r.toNNReal ω) := by
    filter_upwards [hsol.no_collision] with ω hω r hr0 hrH
    have hcol : X r.toNNReal ω ∉ collisionSet d N := hω _ (by rw [Real.coe_toNNReal _ hr0]; exact hrH)
    exact hid _ hcol
  have hEqInt : ∀ᵐ ω ∂P,
      ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          forcingStat ((d : ℝ) / 2) V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) =
      ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2) := by
    filter_upwards [hgood] with ω hω
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    have ht0 : 0 ≤ a + t := by linarith [ht.1.1]
    have htH : a + t ≤ a + T := by linarith [ht.1.2]
    have hEq : ∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          forcingStat ((d : ℝ) / 2) V β ρβ (Torus.realMode l) (X r.toNNReal ω)
        = ∫ r in (0 : ℝ)..(a + t), γ (a + t - r) * (-G (X r.toNNReal ω) + E (X r.toNNReal ω)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le ht0] at hr
      dsimp only
      rw [hω r hr.1 (hr.2.trans htH)]
    rw [hEq]
  have hwinb := hwin hd hs0 hsd V hV β hβ' hN P X₀ W X (a + T) hflow F G E hFm hGm hEm ς Γ hς0 hΓ
    hint hcont hmax a ha le_rfl hLZ hF hE γ γ' hγ hγ' hbd
  -- the final constant
  have hς0sq : ς₀ ^ 2 = C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2) *
      Lattice.jp l.1 ^ (2 * (8 * d + 80)) := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hς₀, mul_pow, mul_pow, mul_pow, h2, ← pow_mul]
    ring
  have hfinal : C₄ * Γ ^ 2 * ς ^ 2 =
      C₄ * Cmax * C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2) * Γ ^ 2 *
        Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N := by
    rw [hς2, hς0sq]
    ring
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          forcingStat ((d : ℝ) / 2) V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) ∂P
      = ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2) ∂P := lintegral_congr_ae hEqInt
    _ ≤ ENNReal.ofReal (C₄ * Γ ^ 2 * ς ^ 2) := hwinb
    _ ≤ ENNReal.ofReal (C₄ * Cmax * C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2) * Γ ^ 2 *
          Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N) :=
        ENNReal.ofReal_le_ofReal (le_of_eq hfinal)

/-- **F10.2 (V-uniform copy of `unif_single_j`).** The constants `C_D, c_D` (from `hdec`) and `C_B1` (from `hmode c_D`) are
chosen before `V`, `β ∈ [βm, βp]` and the thermal density; `s`, `hcrit : s = d/2` as in the original. -/
theorem unif_single_jV (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (βm βp : ℝ) (hβm : 0 < βm) (T : ℝ) (hT : 0 ≤ T) (Bf : ℕ → ℝ)
    (hdec : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ (m : ℝ) (j : NonzeroLattice d) (v : ℝ), 0 ≤ v →
        Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (9 * d + 82) *
          (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
            |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
              (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
                (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|)) ∧
        ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (9 * d + 82) *
          (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
            |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
              (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
                (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|) ≤
          C * Lattice.jp j.1 ^ (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ)) * Real.exp (-c * v))
    (hmode : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V →
      (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
        (hflow : IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X)
        (l : NonzeroLattice d) (Γ : ℝ) (hΓ : 0 ≤ Γ) (γ γ' : ℝ → ℝ)
        (hγ : ∀ x, 0 ≤ x → HasDerivWithinAt γ (γ' x) (Set.Ici 0) x) (hγ' : ContinuousOn γ' (Set.Ici 0))
        (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)),
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
            ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
                forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) ∂P ≤
          ENNReal.ofReal (C * Γ ^ 2 * Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ (m : ℝ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
        (hflow : IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X) (j : NonzeroLattice d),
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
            (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ P X m j (a + t) ω ^ 2) ∂P ≤
          ENNReal.ofReal (C * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_D, c_D, hCD, hcD, hdecU⟩ := hdec
  obtain ⟨C_B1, hC_B1, hmodeU⟩ := hmode c_D hcD
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (-((d : ℝ) + 2)) :=
    ⟨_, rfl⟩
  have hsumSig : Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (-((d : ℝ) + 2))) :=
    asmD_summable_rpow (d := d) ((d : ℝ) + 2) (by linarith)
  refine ⟨C_B1 * C_D ^ 2 * Sg ^ 2, mul_nonneg (mul_nonneg hC_B1 (sq_nonneg _)) (sq_nonneg _), ?_⟩
  intro V hV hVB β hβI ρβ hρβ hρS hρpos
  have hβ : 0 < β := hβm.trans_le hβI.1
  have hdec := hdecU V hV hVB β hβI ρβ hρβ hρS hρpos
  intro m N hN Ω _ P _ X₀ W X a ha hflow j
  have hN0 : (0 : ℝ) < N := by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Lattice.jp j.1 ^ (-m + ((9 * d + 82 + d + 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.rpow_pos_of_pos (Torus.jp_pos _) _
  have hE2 : E ^ 2 = Lattice.jp j.1 ^ (2 * (-m + ((9 * d + 82 + d + 3 : ℕ) : ℝ))) := by
    rw [hE, ← Real.rpow_natCast, ← Real.rpow_mul (Torus.jp_pos j.1).le]
    congr 1
    push_cast
    ring
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = Real.sqrt (C_B1 / N) := ⟨_, rfl⟩
  have hc0nn : 0 ≤ c0 := by rw [hc0]; exact Real.sqrt_nonneg _
  have hc0sq : c0 ^ 2 = C_B1 / N := by
    rw [hc0, Real.sq_sqrt (div_nonneg hC_B1 hN0.le)]
  have hy : ∀ l : NonzeroLattice d, C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Lattice.jp l.1 ^ (8 * d + 80)
      = C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)) := by
    intro l
    have hx := Torus.jp_pos l.1
    rw [show (-((d : ℝ) + 2)) = -(((9 * d + 82 : ℕ) : ℝ) - ((8 * d + 80 : ℕ) : ℝ)) by push_cast; ring,
      asmD_rpow_neg_sub _ hx]
    ring
  have hXnn : ∀ l : NonzeroLattice d, 0 ≤ c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2))) := fun l =>
    mul_nonneg hc0nn (mul_nonneg (mul_nonneg hCD.le hE0.le) (Real.rpow_nonneg (Torus.jp_pos _).le _))
  have hSgnn : 0 ≤ Sg := by
    rw [hSg]
    exact tsum_nonneg fun l => Real.rpow_nonneg (Torus.jp_pos l.1).le _
  -- the Minkowski integrands `S_l(ω) = sup_t |J_l(a+t)(ω)|`
  obtain ⟨S, hS⟩ : ∃ S : NonzeroLattice d → Ω → ℝ≥0∞, ∀ l ω, S l ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ :=
    ⟨fun l ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖,
      fun _ _ => rfl⟩
  have hSmeas : ∀ l, AEMeasurable (S l) P := by
    intro l
    have e : S l = fun ω => ⨆ t ∈ ratTimes 0 T,
        ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ := funext (hS l)
    rw [e]
    refine AEMeasurable.biSup (ratTimes 0 T) (est4_ratTimes_countable 0 T) (fun t ht => ?_)
    have hmem := ht
    obtain ⟨⟨ht0, htT⟩, -⟩ := hmem
    have hb0 : 0 ≤ a + t := by linarith
    have hbH : a + t ≤ a + T := by linarith
    exact ((asmD_J_aemeas hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X (a + T) hflow j l
      (a + t) hb0 hbH).norm).ennreal_ofReal
  -- per-mode bound
  have hperl : ∀ l : NonzeroLattice d, ∫⁻ ω, (S l ω) ^ 2 ∂P ≤
      ENNReal.ofReal ((c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) ^ 2) := by
    intro l
    have hψ : Torus.IsSmooth (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x) :=
      asmB_sm_const_mul (HRS.FieldSingAux.isSmooth_realMode j) _
    have hreg := fourier_coeff_regular_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos _ hψ l
    have hγ : ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt (asmD_gam s hs0 hsd V β hβ ρβ m j l)
        (asmD_gam' s hs0 hsd V β hβ ρβ m j l x) (Set.Ici 0) x :=
      fun x hx => hreg.2.1 x hx
    have hγ' : ContinuousOn (asmD_gam' s hs0 hsd V β hβ ρβ m j l) (Set.Ici 0) := hreg.2.2
    have hbdl : ∀ v, 0 ≤ v → |asmD_gam s hs0 hsd V β hβ ρβ m j l v| ≤
          C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Real.exp (-c_D * v) ∧
        |asmD_gam' s hs0 hsd V β hβ ρβ m j l v| ≤
          C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Real.exp (-c_D * v) := by
      intro v hv
      have hdj := hdec m j v hv
      rw [← hE] at hdj
      exact asmD_coef_bound (d := d) (9 * d + 82) C_D c_D E hE0.le hCD.le
        (fun k => asmD_gam s hs0 hsd V β hβ ρβ m j k v) (fun k => asmD_gam' s hs0 hsd V β hβ ρβ m j k v)
        v hdj.1 hdj.2 l
    have hΓnn : 0 ≤ C_D * E / Lattice.jp l.1 ^ (9 * d + 82) :=
      div_nonneg (mul_nonneg hCD.le hE0.le) (pow_nonneg (Torus.jp_pos _).le _)
    have hmodel := hmodeU V hV hVB β hβI ρβ hρβ hρS hρpos hN P X₀ W X a ha hflow l
      (C_D * E / Lattice.jp l.1 ^ (9 * d + 82)) hΓnn
      (asmD_gam s hs0 hsd V β hβ ρβ m j l) (asmD_gam' s hs0 hsd V β hβ ρβ m j l) hγ hγ'
      (fun v hv => ⟨(hbdl v hv).1, (hbdl v hv).2⟩)
    have hpt : ∀ ω, (S l ω) ^ 2 ≤ ⨆ t ∈ ratTimes 0 T,
        ENNReal.ofReal ((asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω) ^ 2) := by
      intro ω
      rw [hS l ω]
      refine (asmD_biSup_sq _ _).trans (iSup₂_mono fun t _ => le_of_eq ?_)
      rw [← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    refine (lintegral_mono hpt).trans (hmodel.trans (le_of_eq ?_))
    congr 1
    rw [mul_pow, hc0sq, ← hy l]
    ring
  -- the `1/2`-power of each mode
  have hterm : ∀ l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) := by
    intro l
    calc (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal ((c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (hperl l) (by norm_num)
      _ = ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_sq (hXnn l)]
  have hsumX : Summable (fun l : NonzeroLattice d =>
      c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
    (hsumSig.mul_left (C_D * E)).mul_left c0
  have hsumterm : ∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c0 * (C_D * E * Sg)) := by
    calc ∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ ∑' l : NonzeroLattice d, ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' l : NonzeroLattice d, c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
          (ENNReal.ofReal_tsum_of_nonneg hXnn hsumX).symm
      _ = ENNReal.ofReal (c0 * (C_D * E * Sg)) := by
          rw [tsum_mul_left, tsum_mul_left, hSg]
  -- the good event: the pointwise bound of the supremum over `t`
  have hgoodpw := asmD_pathwise hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X (a + T) hflow j
  have hpt' : ∀ᵐ ω ∂P, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
      (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω ^ 2)) ≤
      (∑' l : NonzeroLattice d, S l ω) ^ 2 := by
    filter_upwards [hgoodpw] with ω hω
    refine iSup₂_le fun t ht => ?_
    have hmem := ht
    obtain ⟨⟨ht0, htT⟩, -⟩ := hmem
    have hb0 : 0 ≤ a + t := by linarith
    have hbH : a + t ≤ a + T := by linarith
    obtain ⟨hI, hsum⟩ := hω (a + t) hb0 hbH
    set I := integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω with hIdef
    have h1 : ENNReal.ofReal (I ^ 2) = (ENNReal.ofReal ‖I‖) ^ 2 := by
      rw [← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    have h2 : ENNReal.ofReal ‖I‖ ≤ ∑' l : NonzeroLattice d, S l ω := by
      calc ENNReal.ofReal ‖I‖
          = ENNReal.ofReal ‖∑' l : NonzeroLattice d, asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ := by
            rw [hI.tsum_eq]
        _ ≤ ENNReal.ofReal (∑' l : NonzeroLattice d, ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖) :=
            ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hsum)
        _ = ∑' l : NonzeroLattice d, ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ :=
            ENNReal.ofReal_tsum_of_nonneg (fun l => norm_nonneg _) hsum
        _ ≤ ∑' l : NonzeroLattice d, S l ω := by
            refine ENNReal.tsum_le_tsum fun l => ?_
            rw [hS l ω]
            exact le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) =>
              ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖) t ht
    rw [h1]
    exact pow_le_pow_left₀ zero_le h2 2
  have hreal : (c0 * (C_D * E * Sg)) ^ 2 =
      C_B1 * C_D ^ 2 * Sg ^ 2 * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N := by
    rw [← hE2, mul_pow, hc0sq]
    ring
  have hGsnn : 0 ≤ c0 * (C_D * E * Sg) :=
    mul_nonneg hc0nn (mul_nonneg (mul_nonneg hCD.le hE0.le) hSgnn)
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω ^ 2) ∂P
      ≤ ∫⁻ ω, (∑' l : NonzeroLattice d, S l ω) ^ 2 ∂P := lintegral_mono_ae hpt'
    _ = ((∫⁻ ω, (∑' l : NonzeroLattice d, S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
          (asmD_rpow_half_sq _).symm
    _ ≤ (∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ zero_le (lintegral_sq_tsum_le P S hSmeas) 2
    _ ≤ (ENNReal.ofReal (c0 * (C_D * E * Sg))) ^ 2 := pow_le_pow_left₀ (zero_le) hsumterm 2
    _ = ENNReal.ofReal ((c0 * (C_D * E * Sg)) ^ 2) := (ENNReal.ofReal_pow hGsnn 2).symm
    _ ≤ ENNReal.ofReal (C_B1 * C_D ^ 2 * Sg ^ 2 * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) :=
          ENNReal.ofReal_le_ofReal (le_of_eq hreal)

/-- **F10.3 (V-uniform copy of `uniform417_of_unif`, family form).** `UnifDecayFam` and `UnifModeForcingFam` (for every
`c > 0`) give `Uniform417Fam`: the constant `Real.sqrt (C₂ * Ssum)` is chosen before `V`, with `C₂` from `unif_single_jV`. -/
theorem uniform417_of_unifV (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ)
    (hβm : 0 < βm) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) (Bf : ℕ → ℝ)
    (hdec : UnifDecayFam d hs0 hsd βm βp hβm Bf)
    (hmode : ∀ c : ℝ, 0 < c → UnifModeForcingFam d hs0 hsd βm βp hβm c T Bf) :
    Uniform417Fam d hs0 hsd βm βp hβm m T Bf := by
  classical
  obtain ⟨C₂, hC₂, hsingle⟩ := unif_single_jV hd hs0 hsd rfl βm βp hβm T hT.le Bf hdec hmode
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- the exponent `2 * (-m + p + d + 3)` is `-q` with `q = 2 (m - (p + d + 3)) > d`
  have hqd : (d : ℝ) < 2 * (m - (((9 * d + 82) + d + 3 : ℕ) : ℝ)) := by
    push_cast
    linarith
  have hexp : ∀ j : NonzeroLattice d,
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ)))
        = Lattice.jp j.1 ^ (-(2 * (m - (((9 * d + 82) + d + 3 : ℕ) : ℝ)))) := fun j => by
    congr 1
    ring
  have hs1 : Summable fun j : NonzeroLattice d =>
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) :=
    (asmD_summable_rpow _ hqd).congr fun j => (hexp j).symm
  have hnn : ∀ j : NonzeroLattice d,
      0 ≤ Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) :=
    fun j => Real.rpow_nonneg (Torus.jp_pos j.1).le _
  obtain ⟨Ssum, hSsum⟩ : ∃ Ssum : ℝ, Ssum = ∑' j : NonzeroLattice d,
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hSnn : 0 ≤ Ssum := by
    rw [hSsum]
    exact tsum_nonneg hnn
  refine ⟨Real.sqrt (C₂ * Ssum), Real.sqrt_nonneg _, ?_⟩
  intro V hV hVB β hβ ρβ hρβ hρS hρpos N hN Ω _ P _ X₀ W X a ha hflow
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hCsq : Real.sqrt (C₂ * Ssum) ^ 2 = C₂ * Ssum := Real.sq_sqrt (mul_nonneg hC₂ hSnn)
  have hA : ∀ (k : NonzeroLattice d) (b : ℝ), 0 ≤ b → b ≤ a + T →
      AEMeasurable (fun ω => integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k b ω) P :=
    fun k b hb hbH => integratedCenteredForcing_aemeasurable hd hs0 hsd rfl V hV β hβ0 ρβ hρβ hρS hρpos m hN P
      X₀ W X (a + T) hflow k b hb hbH
  have hmeas : ∀ k : NonzeroLattice d, AEMeasurable (fun ω => ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2)) P := by
    intro k
    refine AEMeasurable.biSup (ratTimes 0 T) (est4_ratTimes_countable 0 T) (fun t ht => ?_)
    obtain ⟨⟨ht0, htT⟩, -⟩ := ht
    exact ((hA k (a + t) (by linarith) (by linarith)).pow_const 2).ennreal_ofReal
  have hpt : ∀ ω, (⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2))
        ≤ ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    exact ENNReal.tsum_le_tsum fun k => le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) =>
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2)) t ht
  have hnnk : ∀ k : NonzeroLattice d,
      0 ≤ C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N :=
    fun k => div_nonneg (mul_nonneg hC₂ (hnn k)) (Nat.cast_nonneg N)
  have hsumc : Summable fun k : NonzeroLattice d =>
      C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N :=
    (hs1.mul_left C₂).div_const (N : ℝ)
  have hfin : ENNReal.ofReal (Real.sqrt (C₂ * Ssum) ^ 2 / N) = ∑' k : NonzeroLattice d,
      ENNReal.ofReal (C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnnk hsumc, hCsq, tsum_div_const, tsum_mul_left, ← hSsum]
  rw [hfin]
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
        ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) ∂P
      ≤ ∫⁻ ω, ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) ∂P :=
        lintegral_mono fun ω => hpt ω
    _ = ∑' k : NonzeroLattice d, ∫⁻ ω, ⨆ t ∈ ratTimes 0 T,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) ∂P :=
        lintegral_tsum fun k => hmeas k
    _ ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal
          (C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) :=
        ENNReal.tsum_le_tsum fun k => hsingle V hV hVB β hβ ρβ hρβ hρS hρpos m hN P X₀ W X a ha hflow k

end HRS.ME.FamU

end
