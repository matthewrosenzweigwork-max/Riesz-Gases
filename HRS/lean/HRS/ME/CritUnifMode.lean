import HRS.ME.CritUnifDefs
import HRS.ME.Mode417B

/-!
# Chunk E, row 2.10 path clauses: `unif_mode_forcing` (U1)

Proof of `unif_mode_forcing`: the proof of `HRS.ME.mode_forcing_bound_proof` at `s = d/2`, with the constant of the mode
package taken from `UnifModePackage` (chosen before `β ∈ [βm, βp]`) and `β⁻¹ ≤ βm⁻¹` used in place of `β⁻¹`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME.Crit

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- (U1.) -/
theorem unif_mode_forcing (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hpkg : UnifModePackage d hd V hV βm βp hβm)
    (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 ≤ T) : UnifModeForcing d hs0 hsd V βm βp hβm c T := by
  classical
  unfold UnifModePackage at hpkg
  unfold UnifModeForcing
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
  intro β hβ ρβ hρβ hρS hρpos N hN Ω _ P _ X₀ W X a ha hflow l Γ hΓ γ γ' hγ hγ' hbd
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

end HRS.ME.Crit

end
