import HRS.MS.QMulAux9

/-!
# MS-QMUL, part 10: the weighted estimate for `u ∈ H^m` (density + Fatou)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_main (d m : ℕ) : ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ (θ : Euc d → ℝ) (A : ℝ), ContDiff ℝ m θ →
    (∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j θ x‖ ≤ A) → ∀ u : Euc d → ℝ, MemLp u 2 volume →
    ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖fourierL2 u ξ‖ ^ 2) < ⊤ →
      MemLp (fun x => θ x * u x) 2 volume ∧
      ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖fourierL2 (fun x => θ x * u x) ξ‖ ^ 2) ≤
        ENNReal.ofReal (K2 * A ^ 2) * ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖fourierL2 u ξ‖ ^ 2) := by
  obtain ⟨K2, hK2, hS⟩ := qm_stepS d m
  refine ⟨K2, hK2, fun θ A hθ hA u hu hw => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hθb : ∀ x, ‖θ x‖ ≤ A := fun x => by simpa using hA 0 (Nat.zero_le _) x
  have hθu : MemLp (fun x => θ x * u x) 2 volume :=
    hu.of_le_mul (c := A) (hθ.continuous.aestronglyMeasurable.mul hu.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hθb x) (norm_nonneg _))
  refine ⟨hθu, ?_⟩
  set v : Euc d → ℂ := fourierL2 u with hvdef
  have hv : MemLp v 2 volume := memLp_fourierL2 hu
  set S : ℝ≥0∞ := ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖v ξ‖ ^ 2) with hSdef
  set s : ℝ := S.toReal with hs
  have hSs : S = ENNReal.ofReal s := (ENNReal.ofReal_toReal hw.ne).symm
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  set e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hedef
  have he : ∀ n, 0 < e n := fun n => by simp only [hedef]; positivity
  have het : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f hf using fun n : ℕ => qm_density m hv hw (δ := (e n) ^ 2) (by have := he n; positivity)
  -- the sequences
  set g : ℕ → Euc d → ℂ := fun n x => (θ x : ℂ) * f n x with hg
  have hgQ : ∀ n, QOk m (g n) := fun n => qm_QOk_mul hθ hA (qm_schwartz_QOk m (f n))
  have hgL : ∀ n, Integrable (g n) volume ∧ MemLp (g n) 2 volume := fun n => qm_QOk_L1L2 (hgQ n)
  set Gn : ℕ → Euc d → ℂ := fun n => 𝓕 (g n) with hGn
  have hGn_ae : ∀ n, (FT d ((hgL n).2.toLp (g n)) : Euc d → ℂ) =ᵐ[volume] Gn n :=
    fun n => qm_L1L2 (hgL n).1 (hgL n).2
  have hGnL : ∀ n, MemLp (Gn n) 2 volume := fun n => (Lp.memLp _).ae_eq (hGn_ae n)
  set G : Euc d → ℂ := fourierL2 (fun x => θ x * u x) with hGdef
  have hGL : MemLp G 2 volume := memLp_fourierL2 hθu
  -- (1) bound on the weighted norms of the approximants
  have hT : ∀ n, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 (⇑(f n)) ξ‖ ^ 2) ≤
      ENNReal.ofReal ((1 + e n) * s + (e n ^ 2 + e n)) := by
    intro n
    have hm1 : AEMeasurable (fun ξ : Euc d => ENNReal.ofReal (wt ξ ^ m * ‖v ξ‖ ^ 2)) volume :=
      ((continuous_wt.pow m).aestronglyMeasurable.mul
        (hv.aestronglyMeasurable.norm.pow 2)).aemeasurable.ennreal_ofReal
    calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 (⇑(f n)) ξ‖ ^ 2)
        ≤ ∫⁻ ξ, (ENNReal.ofReal (1 + e n) * ENNReal.ofReal (wt ξ ^ m * ‖v ξ‖ ^ 2) +
            ENNReal.ofReal (1 + 1 / e n) *
              ENNReal.ofReal (wt ξ ^ m * ‖𝓕 (⇑(f n)) ξ - v ξ‖ ^ 2)) :=
          lintegral_mono fun ξ => qm_elem _ _ (he n) (by have := wt_pos (d := d) ξ; positivity)
      _ = ENNReal.ofReal (1 + e n) * S + ENNReal.ofReal (1 + 1 / e n) *
            ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 (⇑(f n)) ξ - v ξ‖ ^ 2) := by
          rw [lintegral_add_left' (hm1.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 + e n) * ENNReal.ofReal s +
            ENNReal.ofReal (1 + 1 / e n) * ENNReal.ofReal (e n ^ 2) := by
          rw [hSs]; gcongr; exact hf n
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by have := he n; positivity),
            ← ENNReal.ofReal_mul (by have := he n; positivity),
            ← ENNReal.ofReal_add (by have := he n; positivity) (by have := he n; positivity)]
          congr 1
          have := (he n).ne'
          field_simp
  -- (2) the Step S bound
  have hB : ∀ n, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖Gn n ξ‖ ^ 2) ≤
      ENNReal.ofReal (K2 * A ^ 2 * ((1 + e n) * s + (e n ^ 2 + e n))) := by
    intro n
    have := (hS θ A hθ hA (f n) (qm_schwartz_QOk m (f n))).2
    refine this.trans ?_
    rw [ENNReal.ofReal_mul (p := K2 * A ^ 2) (by positivity)]
    exact mul_le_mul_right (hT n) _
  -- (3) convergence in L²
  have hconv : Tendsto (fun n => ∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2) atTop (𝓝 0) := by
    have hbd : ∀ n, ∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2 ≤ ENNReal.ofReal (A ^ 2 * (e n) ^ 2) := by
      intro n
      set Lg := (hgL n).2.toLp (g n) with hLg
      set Lf := (f n).toLp 2 with hLf
      set U := ofRealLp hu with hU
      set ΘU := ofRealLp hθu with hΘU
      have hGfun : G = ⇑(FT d ΘU) := fourierL2_eq hθu
      have hvfun : v = ⇑(FT d U) := fourierL2_eq hu
      have s1 : ∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2 = ∫⁻ x, ‖Lg x - ΘU x‖ₑ ^ 2 := by
        rw [← qm_plancherel_Lp]
        refine lintegral_congr_ae ?_
        filter_upwards [hGn_ae n] with ξ hξ
        rw [hξ, hGfun]
      have s2 : ∫⁻ x, ‖Lg x - ΘU x‖ₑ ^ 2 ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ x, ‖Lf x - U x‖ₑ ^ 2 := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono_ae ?_
        filter_upwards [MemLp.coeFn_toLp (hgL n).2, ofRealLp_coe hθu,
          SchwartzMap.coeFn_toLp (f n) 2 volume, ofRealLp_coe hu] with x h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        have : g n x - ((θ x * u x : ℝ) : ℂ) = (θ x : ℂ) * (f n x - ((u x : ℝ) : ℂ)) := by
          simp only [hg]; push_cast; ring
        rw [this, enorm_mul, mul_pow, ← ofReal_norm, Complex.norm_real]
        gcongr
        rw [← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hθb x) 2)
      have s3 : ∫⁻ x, ‖Lf x - U x‖ₑ ^ 2 ≤ ENNReal.ofReal ((e n) ^ 2) := by
        rw [← qm_plancherel_Lp]
        have : ∫⁻ ξ, ‖(FT d Lf) ξ - (FT d U) ξ‖ₑ ^ 2 =
            ∫⁻ ξ, ‖𝓕 (⇑(f n)) ξ - v ξ‖ₑ ^ 2 := by
          refine lintegral_congr_ae ?_
          have := HRS.MS.SobMul.sobmul_FT_toLp (f n)
          filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (f n) : SchwartzMap (Euc d) ℂ) 2 volume] with ξ hξ
          rw [hLf, this, hξ, SchwartzMap.fourier_coe, hvfun]
        rw [this]
        refine le_trans (lintegral_mono fun ξ => ?_) (hf n)
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ wt ξ ^ m := one_le_pow₀ (one_le_wt ξ)
        nlinarith [sq_nonneg ‖𝓕 (⇑(f n)) ξ - v ξ‖]
      calc _ ≤ _ := s1.le.trans s2
        _ ≤ ENNReal.ofReal (A ^ 2) * ENNReal.ofReal ((e n) ^ 2) := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
    have h0 : Tendsto (fun n => ENNReal.ofReal (A ^ 2 * (e n) ^ 2)) atTop (𝓝 0) := by
      have : Tendsto (fun n => A ^ 2 * (e n) ^ 2) atTop (𝓝 0) := by
        simpa using (het.pow 2).const_mul (A ^ 2)
      simpa using ENNReal.tendsto_ofReal this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => zero_le) hbd
  -- (4) Fatou
  have hrt : Tendsto (fun n => K2 * A ^ 2 * ((1 + e n) * s + (e n ^ 2 + e n))) atTop
      (𝓝 (K2 * A ^ 2 * s)) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add het).mul_const s).add
      ((het.pow 2).add het)
    simpa using this.const_mul (K2 * A ^ 2)
  have hfat := qm_fatou m (G := G) (Gn := Gn) hGL hGnL hconv hB (ENNReal.tendsto_ofReal hrt)
  refine hfat.trans ?_
  rw [hSs, ← ENNReal.ofReal_mul (by positivity)]

end HRS.MS.QMul
