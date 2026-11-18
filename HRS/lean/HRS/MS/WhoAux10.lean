import HRS.MS.WhoAux8
import HRS.MS.WhoAux9
import HRS.MS.UlClass

/-!
# S54 part 10: a priori weighted bound for the evolution (assembly of part (a))
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Matrix

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- time continuity of the derivatives of a strongly continuous closure-valued family -/
theorem who_cont_deriv {k j : ℕ} {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (hkj : (j : ℝ) + (d : ℝ) / 2 < k)
    {τ : ℝ} {w : ℝ → Euc d → ℝ} (hw : UlReg k θ τ w) (x : Euc d) :
    ContinuousOn (fun σ => iteratedFDeriv ℝ j (w σ) x) (Icc 0 τ) := by
  intro σ₀ h0
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k j hkj θ hθ
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hw.cont σ₀ h0 (ε / (Ccb + 1)) (by positivity)
  refine ⟨δ, hδ, fun σ hσ hd => ?_⟩
  have hd' : |σ - σ₀| < δ := by simpa [Real.dist_eq] using hd
  have hdiff := hcb _ (ul4_closure_sub hθ (hw.mem σ hσ) (hw.mem σ₀ h0))
  have hs1 := (hcb _ (hw.mem σ hσ)).1
  have hs0 := (hcb _ (hw.mem σ₀ h0)).1
  have h1 := ul1_cb_deriv_le hdiff.1 (le_refl j) x
  have h2 : iteratedFDeriv ℝ j (fun x => w σ x - w σ₀ x) x =
      iteratedFDeriv ℝ j (w σ) x - iteratedFDeriv ℝ j (w σ₀) x :=
    iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) hs1.1.contDiffAt hs0.1.contDiffAt
  rw [h2] at h1
  have h3 : (ulNormE k θ (fun x => w σ x - w σ₀ x)).toReal ≤ ε / (Ccb + 1) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h σ hσ hd')
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  rw [dist_eq_norm]
  calc ‖iteratedFDeriv ℝ j (w σ) x - iteratedFDeriv ℝ j (w σ₀) x‖ ≤ cbNorm j (fun x => w σ x - w σ₀ x) := h1
    _ ≤ Ccb * (ulNormE k θ (fun x => w σ x - w σ₀ x)).toReal := hdiff.2
    _ ≤ Ccb * (ε / (Ccb + 1)) := mul_le_mul_of_nonneg_left h3 hCcb.le
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; nlinarith

/-- measurability of `σ ↦ Nsq r P (w σ)` (clamped) -/
theorem who_Nsq_meas {k r : ℕ} {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (hk : (r : ℝ) + (d : ℝ) / 2 < k)
    {τ : ℝ} (hτ : 0 < τ) {w : ℝ → Euc d → ℝ} (hw : UlReg k θ τ w) (P : ℝ) :
    Measurable fun σ => Nsq r P (w (clampT τ σ)) := by
  unfold Nsq
  refine Finset.measurable_sum _ fun j hj => ?_
  have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hkj : (j : ℝ) + (d : ℝ) / 2 < k := by
    have : (j : ℝ) ≤ r := by exact_mod_cast hjr
    linarith
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k j hkj θ hθ
  have hcd : ∀ σ, ContDiff ℝ j (w (clampT τ σ)) := fun σ =>
    (hcb _ (hw.mem _ (who_clamp_mem hτ.le σ))).1.1
  have hcont : ∀ x, Continuous fun σ => iteratedFDeriv ℝ j (w (clampT τ σ)) x := fun x =>
    (who_cont_deriv hθ hkj hw x).comp_continuous (who_clamp_cont τ) (who_clamp_mem hτ.le)
  have hsm := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun (x : Euc d) (σ : ℝ) => iteratedFDeriv ℝ j (w (clampT τ σ)) x)
    (fun σ => (hcd σ).continuous_iteratedFDeriv (by exact_mod_cast le_refl j))
    (fun x => (hcont x).stronglyMeasurable)
  have hm : Measurable (Function.uncurry fun (x : Euc d) (σ : ℝ) =>
      ENNReal.ofReal (wt P x * ‖iteratedFDeriv ℝ j (w (clampT τ σ)) x‖ ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((who_wt_meas P).comp measurable_fst).mul (hsm.norm.measurable.pow_const 2)
  exact hm.lintegral_prod_left'


theorem who_Nsq_le_bdd {r : ℕ} {P B : ℝ} {φ : Euc d → ℝ} (hB : ∀ l ≤ r, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) :
    Nsq r P φ ≤ ENNReal.ofReal (((r : ℝ) + 1) * B ^ 2) * wtMass (d := d) P := by
  unfold Nsq
  calc ∑ j ∈ Finset.range (r + 1), wSq P (fun x => ‖iteratedFDeriv ℝ j φ x‖)
      ≤ ∑ j ∈ Finset.range (r + 1), ENNReal.ofReal (B ^ 2) * wtMass (d := d) P :=
        Finset.sum_le_sum fun j hj => who_wSq_bdd fun x => by
          rw [abs_of_nonneg (norm_nonneg _)]; exact hB j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        push_cast; rfl


/-- one step of the a priori estimate -/
theorem who_step (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) (r : ℕ) :
    ∃ C2 C3 : ℝ, 0 ≤ C2 ∧ 0 ≤ C3 ∧ ∀ {τ : ℝ}, 0 < τ → τ ≤ T → ∀ {f : Euc d → ℝ}, ContDiff ℝ ∞ f →
      HasCompactSupport f → ∀ {w : ℝ → Euc d → ℝ} {B : ℝ},
      (∀ σ ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) (w σ) ∧
        ∀ l ≤ r + 3, ∀ y, ‖iteratedFDeriv ℝ l (w σ) y‖ ≤ B) →
      (∀ x, ContinuousOn (fun σ => ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x) (Set.Icc 0 τ)) →
      (∀ x, w τ x = ouSg Q ν τ f x + ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x) →
      ContDiff ℝ r (w τ) ∧ Nsq r P (w τ) ≤ ENNReal.ofReal C2 * Nsq r P f +
        ENNReal.ofReal C3 * ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * Nsq r P (w σ) := by
  have hP0 : 0 ≤ P := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
  obtain ⟨C1, hC10, hW1⟩ := who_W1 hP0 Q hν T r
  obtain ⟨Cv, hCv0, hVw⟩ := who_Vw hd hs0 hs1 M ψ hc hP Q hν T r
  refine ⟨2 * C1, 2 * ((r : ℝ) + 1) * Cv, by positivity, by positivity, ?_⟩
  intro τ hτ hτT f hf hfc w B hw hcont hmild
  obtain ⟨Bf, hBf⟩ := ul3C_bdd_upto hf hfc r
  obtain ⟨hVc, hVd⟩ := hVw hτ hτT hw hcont
  have hSc : ContDiff ℝ r (ouSg Q ν τ f) :=
    who_ouSg_smooth Q ν τ (hf.of_le (by exact_mod_cast le_top)) (B := Bf) hBf
  have hwe : w τ = fun x => ouSg Q ν τ f x + ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x :=
    funext hmild
  rw [hwe]
  refine ⟨hSc.add hVc, ?_⟩
  set V : Euc d → ℝ := fun x => ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ψ c (w σ)) x with hV
  set L : ℝ≥0∞ := ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * Nsq r P (w σ) with hL
  have hpt : ∀ i ≤ r, wSq P (fun x => ‖iteratedFDeriv ℝ i (fun x => ouSg Q ν τ f x + V x) x‖) ≤
      2 * (ENNReal.ofReal C1 * wSq P (fun x => ‖iteratedFDeriv ℝ i f x‖) +
        ENNReal.ofReal Cv * L) := by
    intro i hi
    have hsum : ∀ x, ‖iteratedFDeriv ℝ i (fun x => ouSg Q ν τ f x + V x) x‖ ≤
        ‖iteratedFDeriv ℝ i (ouSg Q ν τ f) x‖ + ‖iteratedFDeriv ℝ i V x‖ := by
      intro x
      have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := i) (f := ouSg Q ν τ f) (g := V) (x := x)
        ((hSc.of_le (by exact_mod_cast hi)).contDiffAt) ((hVc.of_le (by exact_mod_cast hi)).contDiffAt)
      have e : (fun x => ouSg Q ν τ f x + V x) = ouSg Q ν τ f + V := rfl
      rw [e, this]; exact norm_add_le _ _
    have h1 := hW1 τ ⟨hτ.le, hτT⟩ hi (hf.of_le (by exact_mod_cast le_top)) ⟨Bf, fun l hl => hBf l (by omega)⟩
    have hm1 : Measurable fun x => ‖iteratedFDeriv ℝ i (ouSg Q ν τ f) x‖ :=
      (hSc.continuous_iteratedFDeriv (by exact_mod_cast hi)).norm.measurable
    calc wSq P (fun x => ‖iteratedFDeriv ℝ i (fun x => ouSg Q ν τ f x + V x) x‖)
        ≤ wSq P (fun x => ‖iteratedFDeriv ℝ i (ouSg Q ν τ f) x‖ + ‖iteratedFDeriv ℝ i V x‖) :=
          who_wSq_mono fun x => pow_le_pow_left₀ (norm_nonneg _) (hsum x) 2
      _ ≤ 2 * (wSq P (fun x => ‖iteratedFDeriv ℝ i (ouSg Q ν τ f) x‖) +
            wSq P (fun x => ‖iteratedFDeriv ℝ i V x‖)) := who_wSq_add_le hm1
      _ ≤ _ := mul_le_mul' le_rfl (add_le_add h1 ((hVd i hi)))
  unfold Nsq
  calc ∑ i ∈ Finset.range (r + 1), wSq P (fun x => ‖iteratedFDeriv ℝ i (fun x => ouSg Q ν τ f x + V x) x‖)
      ≤ ∑ i ∈ Finset.range (r + 1), 2 * (ENNReal.ofReal C1 * wSq P (fun x => ‖iteratedFDeriv ℝ i f x‖) +
          ENNReal.ofReal Cv * L) :=
        Finset.sum_le_sum fun i hi => hpt i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    _ = ENNReal.ofReal (2 * C1) * ∑ i ∈ Finset.range (r + 1), wSq P (fun x => ‖iteratedFDeriv ℝ i f x‖) +
          ENNReal.ofReal (2 * ((r : ℝ) + 1) * Cv) * L := by
        have e1 : ENNReal.ofReal (2 * C1) = 2 * ENNReal.ofReal C1 := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
        have e2 : ENNReal.ofReal (2 * ((r : ℝ) + 1) * Cv) = 2 * ((r + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal Cv := by
          have hr1 : ENNReal.ofReal ((r : ℝ) + 1) = ((r + 1 : ℕ) : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_natCast]; push_cast; rfl
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hr1]
          simp
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, e1, e2]
        ring

theorem who_L_conv {τ : ℝ} (hτ : 0 < τ) {A : ℝ → ℝ≥0∞} {F : ℝ → ℝ} {M0 : ℝ} (hFm : Measurable F)
    (hA : ∀ σ ∈ Set.Ioo 0 τ, A σ = ENNReal.ofReal (F σ)) (hF0 : ∀ σ ∈ Set.Ioo 0 τ, 0 ≤ F σ ∧ F σ ≤ M0) :
    ∫⁻ σ in Set.Ioo 0 τ, ENNReal.ofReal ((τ - σ) ^ (-(1 / 2 : ℝ))) * A σ =
      ENNReal.ofReal (∫ σ in Set.Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ) := by
  have hint1 : IntegrableOn (fun σ => (τ - σ) ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 τ) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num) (a := 0) (b := τ)).comp_sub_left τ
    simp only [sub_self, sub_zero] at this
    exact (this.symm.1.mono_set Set.Ioo_subset_Ioc_self)
  have hint : IntegrableOn (fun σ => (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ) (Set.Ioo 0 τ) := by
    refine (hint1.const_mul (max M0 0)).mono'
      (((measurable_const.sub measurable_id).pow_const _).mul hFm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    have hu : 0 ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (sub_nonneg.2 hσ.2.le) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu (hF0 σ hσ).1)]
    calc (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) * max M0 0 :=
          mul_le_mul_of_nonneg_left ((hF0 σ hσ).2.trans (le_max_left _ _)) hu
      _ = _ := by ring
  rw [ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioo).2
    (Filter.Eventually.of_forall fun σ hσ => mul_nonneg (Real.rpow_nonneg (sub_nonneg.2 hσ.2.le) _) (hF0 σ hσ).1))]
  refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  rw [hA σ hσ, ENNReal.ofReal_mul (Real.rpow_nonneg (sub_nonneg.2 hσ.2.le) _)]

/-- **the a priori weighted bound** for a backward evolution at a large level -/
theorem who_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {θ : Euc d → ℝ}, IsUlCutoff θ → ∀ {k : ℕ}, (4 : ℝ) + (d : ℝ) / 2 < k →
      ((r + 3 : ℕ) : ℝ) + (d : ℝ) / 2 < k → ∀ {t : ℝ}, 0 ≤ t → t ≤ T → ∀ {f : Euc d → ℝ},
      ContDiff ℝ ∞ f → HasCompactSupport f → ∀ {u : ℝ → Euc d → ℝ},
      IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ψ) t f u → ∀ {Bu : ℝ},
      (∀ σ ∈ Set.Icc (0 : ℝ) t, ulNormE k θ (u σ) ≤ ENNReal.ofReal Bu) →
      ∀ r' ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ r (u r') ∧ Nsq r P (u r') ≤ ENNReal.ofReal C * Nsq r P f := by
  have hP0 : 0 ≤ P := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨C2, C3, hC20, hC30, hstep⟩ := who_step hd hs0 hs1 M ψ hc hP Q hν T r
  set C2' : ℝ := max C2 1 with hC2'
  obtain ⟨Kg, hKg0, hGr⟩ := who_gronwall (le_max_right T 0) C3 hC30
  refine ⟨Kg * C2' + 1, by positivity, ?_⟩
  intro θ hθ k hk4 hkr t ht htT f hf hfc u hev Bu hBu r' hr'
  have H : UlHyp s M ψ c ν k θ := ⟨hs0, hsd, ⟨ψ, rfl⟩, hc, hν, hk4, hθ⟩
  have hureg : UlReg k θ t u := ⟨hev.mem, hev.cont⟩
  set w : ℝ → Euc d → ℝ := fun τ => u (t - τ) with hwdef
  have hw : UlReg k θ t w := ul5_reg_flip hureg
  have hmild := ul5_mild_of_evolution H Q ht hev
  have hflip : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) t := fun σ hσ =>
    ⟨sub_nonneg.2 hσ.2, by linarith [hσ.1]⟩
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k (r + 3) hkr θ hθ
  set Bw : ℝ := Ccb * max Bu 0 with hBw
  have hwb : ∀ σ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) (w σ) ∧
      ∀ l ≤ r + 3, ∀ y, ‖iteratedFDeriv ℝ l (w σ) y‖ ≤ Bw := by
    intro σ hσ
    obtain ⟨hm, hn⟩ := hcb _ (hev.mem _ (hflip σ hσ))
    refine ⟨hm.1, fun l hl y => (ul1_cb_deriv_le hm hl y).trans (hn.trans ?_)⟩
    have h1 : (ulNormE k θ (u (t - σ))).toReal ≤ max Bu 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hBu _ (hflip σ hσ))
      rwa [ENNReal.toReal_ofReal'] at this
    exact mul_le_mul_of_nonneg_left h1 hCcb.le
  have hr'0 : t - r' ∈ Set.Icc (0 : ℝ) t := hflip r' hr'
  have hwr' : w (t - r') = u r' := by simp [hwdef]
  have hcdu : ContDiff ℝ r (u r') := by
    have := (hwb (t - r') hr'0).1
    rw [hwr'] at this
    exact this.of_le (by exact_mod_cast (by omega : r ≤ r + 3))
  refine ⟨hcdu, ?_⟩
  obtain ⟨Bf, hBf⟩ := ul3C_bdd_upto hf hfc r
  have hNf : Nsq r P f < ⊤ := who_Nsq_lt_top hP (fun j hj => ⟨Bf, fun y => hBf j hj y⟩)
  have hterm := hev.classicalSol.terminal
  rcases ht.eq_or_lt with h0 | hpos
  · have hrt : r' = t := by linarith [hr'.1, hr'.2]
    have : u r' = f := by rw [hrt]; exact hterm
    rw [this]
    refine le_mul_of_one_le_left bot_le ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hKg0 (le_trans zero_le_one (le_max_right C2 1))])
  set Nf : ℝ := (Nsq r P f).toReal with hNfdef
  have hNf0 : 0 ≤ Nf := ENNReal.toReal_nonneg
  have hNfe : Nsq r P f = ENNReal.ofReal Nf := (ENNReal.ofReal_toReal hNf.ne).symm
  have hkr' : (r : ℝ) + (d : ℝ) / 2 < k := by
    have : ((r + 3 : ℕ) : ℝ) = (r : ℝ) + 3 := by push_cast; ring
    linarith
  have hfin : ∀ σ ∈ Set.Icc (0 : ℝ) t, Nsq r P (w σ) < ⊤ := fun σ hσ =>
    lt_of_le_of_lt (who_Nsq_le_bdd (r := r) (P := P) (fun l hl y => (hwb σ hσ).2 l (by omega) y))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (who_wtMass_lt_top hP))
  set M0 : ℝ := ((r : ℝ) + 1) * Bw ^ 2 * (wtMass (d := d) P).toReal with hM0def
  have hM0 : ∀ σ ∈ Set.Icc (0 : ℝ) t, (Nsq r P (w σ)).toReal ≤ M0 := fun σ hσ => by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (who_wtMass_lt_top hP).ne)
      (who_Nsq_le_bdd (r := r) (P := P) (fun l hl y => (hwb σ hσ).2 l (by omega) y))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  set F : ℝ → ℝ := fun σ => (Nsq r P (w (clampT t σ))).toReal with hFdef
  have hFm : Measurable F := (who_Nsq_meas hθ hkr' hpos hw P).ennreal_toReal
  have hFe : ∀ σ ∈ Set.Icc (0 : ℝ) t, F σ = (Nsq r P (w σ)).toReal := fun σ hσ => by
    simp only [hFdef, who_clamp_eq hσ]
  have hF0 : ∀ σ ∈ Set.Icc (0 : ℝ) t, 0 ≤ F σ ∧ F σ ≤ M0 := fun σ hσ => by
    rw [hFe σ hσ]; exact ⟨ENNReal.toReal_nonneg, hM0 σ hσ⟩
  have hFA : ∀ σ ∈ Set.Icc (0 : ℝ) t, Nsq r P (w σ) = ENNReal.ofReal (F σ) := fun σ hσ => by
    rw [hFe σ hσ, ENNReal.ofReal_toReal (hfin σ hσ).ne]
  have hineq : ∀ τ ∈ Set.Icc (0 : ℝ) t, F τ ≤ C2' * Nf + C3 * ∫ σ in Set.Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ := by
    intro τ hτ
    have hC2'1 : 1 ≤ C2' := le_max_right _ _
    rcases hτ.1.eq_or_lt with h0' | hτpos
    · have hw0 : w 0 = f := by simp [hwdef, hterm]
      rw [← h0', hFe 0 ⟨le_rfl, ht⟩, hw0]
      simp only [Set.Ioo_self, Measure.restrict_empty, integral_zero_measure, mul_zero, add_zero]
      nlinarith
    · have hτt : τ ≤ t := hτ.2
      have hcd := hstep hτpos (hτt.trans htT) hf hfc (w := w) (B := Bw)
        (fun σ hσ => hwb σ ⟨hσ.1, hσ.2.trans hτt⟩)
        (fun x => ul4_Phi_cont hs0 hsd M ψ ⟨ψ, rfl⟩ hc Q hν hk4 hθ (le_refl τ) (ul4_reg_mono hτt hw) x)
        (fun x => hmild τ hτ x)
      have hL := who_L_conv hτpos (A := fun σ => Nsq r P (w σ)) hFm
        (fun σ hσ => hFA σ ⟨hσ.1.le, hσ.2.le.trans hτt⟩) (M0 := M0)
        (fun σ hσ => hF0 σ ⟨hσ.1.le, hσ.2.le.trans hτt⟩)
      have hLr0 : 0 ≤ ∫ σ in Set.Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ :=
        setIntegral_nonneg measurableSet_Ioo fun σ hσ =>
          mul_nonneg (Real.rpow_nonneg (sub_nonneg.2 hσ.2.le) _) (hF0 σ ⟨hσ.1.le, hσ.2.le.trans hτt⟩).1
      have h1 := hcd.2
      rw [hL, hNfe, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC30,
        ← ENNReal.ofReal_add (mul_nonneg hC20 hNf0) (mul_nonneg hC30 hLr0)] at h1
      have h2 := ENNReal.toReal_le_of_le_ofReal (add_nonneg (mul_nonneg hC20 hNf0) (mul_nonneg hC30 hLr0)) h1
      rw [hFe τ hτ]
      refine h2.trans ?_
      have : C2 * Nf ≤ C2' * Nf := mul_le_mul_of_nonneg_right (le_max_left _ _) hNf0
      linarith
  have hfinal := hGr (t := t) (a := C2' * Nf) (M := M0) (F := F) ht (htT.trans (le_max_left T 0))
    (by positivity) hFm hF0 hineq
  have hτ0 := hfinal (t - r') hr'0
  rw [hFe _ hr'0, hwr'] at hτ0
  have hfu : Nsq r P (u r') < ⊤ := by
    have := hfin _ hr'0
    rwa [hwr'] at this
  calc Nsq r P (u r') = ENNReal.ofReal (Nsq r P (u r')).toReal := (ENNReal.ofReal_toReal hfu.ne).symm
    _ ≤ ENNReal.ofReal (Kg * (C2' * Nf)) := ENNReal.ofReal_le_ofReal hτ0
    _ ≤ ENNReal.ofReal ((Kg * C2' + 1) * Nf) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg (mul_nonneg hKg0 (le_trans zero_le_one (le_max_right C2 1))) hNf0])
    _ = ENNReal.ofReal (Kg * C2' + 1) * Nsq r P f := by
        rw [hNfe, ENNReal.ofReal_mul (by positivity)]

end HRS.MS.Who
