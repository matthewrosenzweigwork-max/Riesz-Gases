import HRS.MS.UlMildAux4

/-!
# UL-4b (S5.1 infrastructure, supplement foundation packet): admissibility `G1` of the Duhamel operator, part 2

Not a manuscript row.  Proves `UlDuhamelAdm` (`ul4b_adm`) and hence the unconditional existence theorem
`ul_mild_exists` (the statement of `ul_mild_exists_of_adm` with the hypothesis `UlDuhamelAdm` removed).
Helper lemmas carry the prefix `ul4b_`.

Main declarations (`UlHyp s M ρ c ν k θ` bundles `0 ≤ s < d`, `ρ` Schwartz, `c` smooth with bounded derivatives,
`ν > 0`, `4 + d/2 < k`, `IsUlCutoff θ`):

* `ul4b_adm : UlHyp s M ρ c ν k θ → ∀ Q T, UlDuhamelAdm Q ν s M ρ c k θ T` (`G1`).
  Ingredients: `ul4b_cont_oneside` (continuity in `τ` by the translation identity `ul4b_diff`, with
  `ul4_D_bound` and the short-interval smallness `ul4b_small`), `ul4b_mem` (closure membership: the
  truncated integrals `ul4b_trunc_mem` are limits, via `ul4b_lim`, of Riemann sums `ul4b_riemann`/`ul4b_int_mem`
  in `E_k`, using `ul4b_P_pert_mem : P_t ulPert (UlClosure) ⊆ UlClosure` for `t > 0`, which rests on
  `ul4b_pert_ccc : ulPert (C_c^∞ + const) ∈ UlClosure` via the tail decay of `ulNL`).
* `ul_mild_exists` (unconditional): for `0 ≤ s < d`, `IsUlCutoff θ`, `4 + d/2 < k`, `0 ≤ T`, `0 < ν`,
  `ρ` Schwartz, `IsSmoothBounded c`: `∃ C, ∀ f, UlClosure k θ f → ∃ u, (∀ τ ∈ [0,T], UlClosure k θ (u τ) ∧
  ulNormE k θ (u τ) ≤ ofReal C * ulNormE k θ f) ∧ (strong continuity of `u` in `ulNormE k θ` on `[0,T]`) ∧
  (∀ τ ∈ [0,T], ∀ x, u τ x = ouSg Q ν τ f x + ∫ σ in 0..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (u σ)) x)`;
  no adjustment of the statement of `ul_mild_exists_of_adm` other than removing `UlDuhamelAdm`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

section Aux5
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ}
  {θ : Euc d → ℝ}

theorem ul4b_norm_zero : ulNormE k θ (fun _ : Euc d => (0 : ℝ)) = 0 := by
  simp [ulNormE, HRS.MS.UlocCut.uc_zero]

theorem ul4b_ulD_zero (Q : Matrix (Fin d) (Fin d) ℝ) (z : ℝ → Euc d → ℝ) (t0 : ℝ) (x : Euc d) :
    ulD Q ν s M ρ c z 0 t0 x = 0 := by simp [ulD]

/-- **Smallness of the Duhamel integral over short intervals.** -/
theorem ul4b_small (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) {W : ℝ}
    (hW : 0 ≤ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ {h t0 : ℝ}, 0 < h → h ≤ h0 → h ≤ t0 → t0 ≤ T → ∀ {z : ℝ → Euc d → ℝ},
      UlReg k θ h z → (∀ σ ∈ Icc 0 h, ulNormE k θ (z σ) ≤ ENNReal.ofReal W) →
      ulNormE k θ (fun x => ulD Q ν s M ρ c z h t0 x) ≤ ENNReal.ofReal ε := by
  by_cases hT : 0 ≤ T
  swap
  · exact ⟨1, one_pos, fun {h t0} hh _ hht hT0 => absurd (hh.le.trans (hht.trans hT0)) hT⟩
  obtain ⟨KG, hKG, hD⟩ := ul4_D_bound H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν H.hk H.hθ T
  obtain ⟨γ0, γ1⟩ := ul4_gam_bounds H.hsd
  have h := (ul4_Th_tendsto γ1 hT).const_mul (KG * W * Real.exp 1)
  rw [mul_zero] at h
  obtain ⟨lam, hl⟩ := ((h.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop (1 : ℝ))).exists
  have hlam : 1 ≤ lam := hl.2
  refine ⟨1 / lam, by positivity, fun {h t0} hh hh0 hht hT0 {z} hz hzb => ?_⟩
  have hex : Real.exp (lam * h) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hh0 (by linarith : (0 : ℝ) ≤ lam)
    rwa [mul_one_div_cancel (by linarith)] at this
  have hzb' : ∀ σ ∈ Icc 0 h, ulNormE k θ (z σ) ≤ ENNReal.ofReal (W * Real.exp (lam * σ)) := by
    intro σ hσ
    refine (hzb σ hσ).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 1 ≤ Real.exp (lam * σ) := Real.one_le_exp (by nlinarith [hσ.1])
    nlinarith
  refine (hD hh hht hT0 hz (lam := lam) (W := W) (by linarith) hW hzb').trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hΘ := ul4_Th_nonneg (γ := ul4gam d s) hT lam
  calc KG * W * Real.exp (lam * h) * ul4Th (ul4gam d s) T lam
      ≤ KG * W * Real.exp 1 * ul4Th (ul4gam d s) T lam :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex (by positivity)) hΘ
    _ ≤ ε := hl.1.le

/-- pointwise bound for the Duhamel integral over a short interval -/
theorem ul4b_ulD_pt (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) :
    ∃ Bp : ℝ, 0 ≤ Bp ∧ ∀ {h : ℝ} (t0 : ℝ), 0 ≤ h → ∀ {z : ℝ → Euc d → ℝ}, UlReg k θ h z → ∀ {W : ℝ},
      (∀ σ ∈ Icc 0 h, ulNormE k θ (z σ) ≤ ENNReal.ofReal W) → ∀ x,
      |ulD Q ν s M ρ c z h t0 x| ≤ Bp * max W 0 * h := by
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 H.hk θ H.hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
  refine ⟨Cp * Ccb, by positivity, fun {h} t0 hh {z} hz {W} hzb x => ?_⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
    (f := fun σ => ouSg Q ν (t0 - σ) (ulPert s M ρ c (z σ)) x) (C := Cp * Ccb * max W 0) fun σ hσ => by
      rw [uIoc_of_le hh] at hσ
      have hσ' : σ ∈ Icc (0 : ℝ) h := ⟨hσ.1.le, hσ.2⟩
      obtain ⟨hcb4, hcbn⟩ := hcb _ (hz.mem σ hσ')
      rw [Real.norm_eq_abs]
      refine (ul4_ouSg_abs_le Q ν _ (fun y => (hpcb _ hcb4).2 y) x).trans ?_
      have h2 : (ulNormE k θ (z σ)).toReal ≤ max W 0 := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top
          ((hzb σ hσ').trans (ENNReal.ofReal_le_ofReal (le_max_left W 0)))
        rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this
      calc Cp * cbNorm 4 (z σ) ≤ Cp * (Ccb * (ulNormE k θ (z σ)).toReal) :=
            mul_le_mul_of_nonneg_left hcbn hCp0
        _ ≤ Cp * (Ccb * max W 0) := by gcongr
        _ = Cp * Ccb * max W 0 := by ring
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh] at this
  unfold ulD
  linarith

/-- time translation of a strongly continuous family -/
theorem ul4b_reg_shift {a h : ℝ} (hh : 0 ≤ h) {w : ℝ → Euc d → ℝ} (hw : UlReg k θ (a + h) w) :
    UlReg k θ a (fun σ => w (σ + h)) :=
  ⟨fun σ hσ => hw.mem (σ + h) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, fun σ₀ h0 ε hε => by
    obtain ⟨δ, hδ, hd⟩ := hw.cont (σ₀ + h) ⟨by linarith [h0.1], by linarith [h0.2]⟩ ε hε
    exact ⟨δ, hδ, fun σ hσ hσδ => hd (σ + h) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
      (by rwa [add_sub_add_right_eq_sub])⟩⟩

/-- splitting the Duhamel integral at time `α` -/
theorem ul4b_tail (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {α η : ℝ} (hα : 0 ≤ α)
    (hη : 0 ≤ η) {w : ℝ → Euc d → ℝ} (hw : UlReg k θ (α + η) w) (x : Euc d) :
    ulD Q ν s M ρ c w (α + η) (α + η) x =
      ulD Q ν s M ρ c w α (α + η) x + ulD Q ν s M ρ c (fun σ y => w (σ + α) y) η η x := by
  have hΦ := ul4_Phi_cont H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν H.hk H.hθ (le_refl (α + η)) hw x
  have hint1 : IntervalIntegrable (fun σ => ouSg Q ν ((α + η) - σ) (ulPert s M ρ c (w σ)) x) volume 0 α :=
    (hΦ.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hα
  have hint2 : IntervalIntegrable (fun σ => ouSg Q ν ((α + η) - σ) (ulPert s M ρ c (w σ)) x) volume α
      (α + η) :=
    (hΦ.mono (Icc_subset_Icc hα le_rfl)).intervalIntegrable_of_Icc (by linarith)
  unfold ulD
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  congr 1
  have := intervalIntegral.integral_comp_add_right
    (fun σ => ouSg Q ν ((α + η) - σ) (ulPert s M ρ c (w σ)) x) (a := 0) (b := η) α
  rw [zero_add, add_comm η α] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only
  rw [show α + η - (σ + α) = η - σ by ring]

/-- translation identity of the Duhamel integral -/
theorem ul4b_diff (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {a h : ℝ} (ha : 0 ≤ a)
    (hh : 0 ≤ h) {w : ℝ → Euc d → ℝ} (hw : UlReg k θ (a + h) w) (x : Euc d) :
    ulD Q ν s M ρ c w (a + h) (a + h) x - ulD Q ν s M ρ c w a a x =
      ulD Q ν s M ρ c w h (a + h) x +
        ulD Q ν s M ρ c (fun σ y => w (σ + h) y - w σ y) a a x := by
  have t := ul4b_tail H Q (α := h) (η := a) hh ha (by rwa [add_comm]) x
  rw [add_comm h a] at t
  have hs := ul4_D_sub H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν H.hk H.hθ ha le_rfl
    (u := fun σ y => w (σ + h) y) (u' := w) (ul4_reg_mono (by linarith) (ul4b_reg_shift hh hw))
    (ul4_reg_mono (by linarith) hw) x
  linarith

/-- uniform continuity from one-sided continuity -/
theorem ul4b_unif_of_oneside (hθ : IsUlCutoff θ) {F : ℝ → Euc d → ℝ} {T : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b → b - a < δ →
      ulNormE k θ (fun x => F b x - F a x) ≤ ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc (0 : ℝ) T, ∀ σ' ∈ Icc (0 : ℝ) T, |σ - σ'| < δ →
      ulNormE k θ (fun x => F σ x - F σ' x) ≤ ENNReal.ofReal ε := by
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) hθ
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := h (ε / (1 + Cn)) (by positivity)
  refine ⟨δ, hδ, fun σ hσ σ' hσ' hlt => ?_⟩
  have hε1 : ε / (1 + Cn) ≤ ε := div_le_self hε.le (by linarith)
  rcases le_total σ' σ with hle | hle
  · refine (hd σ' hσ' σ hσ hle (by rw [abs_of_nonneg (by linarith)] at hlt; exact hlt)).trans
      (ENNReal.ofReal_le_ofReal hε1)
  · have e : (fun x => F σ x - F σ' x) = fun x => -(F σ' x - F σ x) := by funext x; ring
    rw [e]
    refine (hneg _).trans ?_
    have h1 := hd σ hσ σ' hσ' hle (by rw [abs_of_nonpos (by linarith)] at hlt; linarith)
    calc ENNReal.ofReal Cn * _ ≤ ENNReal.ofReal Cn * ENNReal.ofReal (ε / (1 + Cn)) := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (Cn * (ε / (1 + Cn))) := (ENNReal.ofReal_mul hCn.le).symm
      _ ≤ ENNReal.ofReal ε := by
          apply ENNReal.ofReal_le_ofReal
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith

/-- one-sided continuity of the Duhamel integral `τ ↦ ∫_0^τ P_{τ-σ} ulPert (w σ) dσ` -/
theorem ul4b_cont_oneside (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ)
    {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b → b - a < δ →
      ulNormE k θ (fun x => ulD Q ν s M ρ c w b b x - ulD Q ν s M ρ c w a a x) ≤ ENNReal.ofReal ε := by
  by_cases hT : 0 ≤ T
  swap
  · exact ⟨1, one_pos, fun a ha => absurd (ha.1.trans ha.2) hT⟩
  obtain ⟨W0, hW0⟩ := ul4_bdd H.hθ hw.toReg
  have hW1 : 0 ≤ max W0 0 := le_max_right _ _
  obtain ⟨h0, hh0, hsmall⟩ := ul4b_small H Q T hW1 (half_pos hε)
  obtain ⟨KG, hKG, hD⟩ := ul4_D_bound H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν H.hk H.hθ T
  set Θ0 : ℝ := ul4Th (ul4gam d s) T 0 with hΘ0
  have hΘ0nn : 0 ≤ Θ0 := ul4_Th_nonneg (γ := ul4gam d s) hT 0
  set ε1 : ℝ := ε / (2 * (KG * Θ0 + 1)) with hε1
  have hε10 : 0 < ε1 := by positivity
  obtain ⟨δ1, hδ1, hu⟩ := hw.unif ε1 hε10
  refine ⟨min h0 δ1, lt_min hh0 hδ1, fun a ha b hb hab hlt => ?_⟩
  obtain ⟨h, hh, rfl⟩ : ∃ h : ℝ, 0 ≤ h ∧ b = a + h := ⟨b - a, by linarith, by ring⟩
  have hh' : a + h - a = h := by ring
  rw [hh'] at hlt
  rcases hh.eq_or_lt with h00 | hpos
  · subst h00
    simp only [add_zero, sub_self]
    rw [show (fun x : Euc d => (0 : ℝ)) = fun _ => 0 from rfl, ul4b_norm_zero]; exact bot_le
  have hwa : UlReg k θ (a + h) w := ul4_reg_mono hb.2 hw.toReg
  have e : (fun x => ulD Q ν s M ρ c w (a + h) (a + h) x - ulD Q ν s M ρ c w a a x) = fun x =>
      ulD Q ν s M ρ c w h (a + h) x +
        ulD Q ν s M ρ c (fun σ y => w (σ + h) y - w σ y) a a x :=
    funext fun x => ul4b_diff H Q ha.1 hh hwa x
  rw [e]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  have hB : ulNormE k θ (fun x => ulD Q ν s M ρ c w h (a + h) x) ≤ ENNReal.ofReal (ε / 2) :=
    hsmall hpos (lt_of_lt_of_le hlt (min_le_left _ _)).le (by linarith [ha.1]) hb.2
      (ul4_reg_mono (by linarith [hb.2, ha.1]) hw.toReg)
      (fun σ hσ => (hW0 σ ⟨hσ.1, by linarith [hσ.2, hb.2, ha.1]⟩).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hA : ulNormE k θ (fun x => ulD Q ν s M ρ c (fun σ y => w (σ + h) y - w σ y) a a x) ≤
      ENNReal.ofReal (ε / 2) := by
    rcases ha.1.eq_or_lt with ha0 | hapos
    · subst ha0
      have : (fun x => ulD Q ν s M ρ c (fun σ y => w (σ + h) y - w σ y) 0 0 x) = fun _ => 0 := by
        funext x; exact ul4b_ulD_zero Q _ _ x
      rw [this, ul4b_norm_zero]; exact bot_le
    have hz : UlReg k θ a (fun σ y => w (σ + h) y - w σ y) :=
      ul4_reg_sub H.hθ (ul4b_reg_shift hh hwa) (ul4_reg_mono (by linarith) hwa)
    refine (hD hapos le_rfl ha.2 hz (lam := 0) (W := ε1) le_rfl hε10.le ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · intro σ hσ
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact hu (σ + h) ⟨by linarith [hσ.1], by linarith [hσ.2, hb.2]⟩ σ ⟨hσ.1, by linarith [hσ.2, ha.2]⟩
        (by rw [show σ + h - σ = h by ring, abs_of_nonneg hh]
            exact lt_of_lt_of_le hlt (min_le_right _ _))
    · simp only [zero_mul, Real.exp_zero, mul_one]
      rw [hε1]
      have : KG * (ε / (2 * (KG * Θ0 + 1))) * Θ0 = (KG * Θ0) * ε / (2 * (KG * Θ0 + 1)) := by
        field_simp
      rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hKG.le hΘ0nn, hε]
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hB hA
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem ul4b_sg_split (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {u : Euc d → ℝ}
    (hu : UlClosure k θ u) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ouSg Q ν (a + b) (ulPert s M ρ c u) = ouSg Q ν a (ouSg Q ν b (ulPert s M ρ c u)) := by
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 H.hk θ H.hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
  have hG := (hpcb u (hcb u hu).1).1
  obtain ⟨B, hB⟩ := ul3C_bdd_of_cb hG
  funext x
  exact ul4_semigroup Q H.hν.le ha hb hG.1.continuous hB x

/-- the truncated Duhamel integral `∫_0^{τ-η} P_{τ-σ} ulPert (w σ) dσ` lies in the closure -/
theorem ul4b_trunc_mem (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ)
    {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) {τ η : ℝ} (hη : 0 < η) (hητ : η < τ) (hτT : τ ≤ T) :
    UlClosure k θ (fun x => ulD Q ν s M ρ c w (τ - η) τ x) := by
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 H.hk θ H.hθ
  obtain ⟨K, hK, hest⟩ := ul4_pert_est H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν T k H.hk θ H.hθ
  obtain ⟨γ0, γ1⟩ := ul4_gam_bounds H.hsd
  set γ := ul4gam d s with hγ
  set Ψ : ℝ → Euc d → ℝ := fun σ x => ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) x with hΨ
  have hσT : ∀ σ ∈ Icc (0 : ℝ) (τ - η), σ ∈ Icc (0 : ℝ) T := fun σ hσ =>
    ⟨hσ.1, by linarith [hσ.2]⟩
  have hmem : ∀ σ ∈ Icc (0 : ℝ) (τ - η), UlClosure k θ (Ψ σ) := fun σ hσ =>
    ul4b_P_pert_mem H Q T (t := τ - σ) (by linarith [hσ.2]) (by linarith [hσ.1]) (hw.mem σ (hσT σ hσ))
  set A : ℝ := K * η ^ (-γ) with hA
  have hA0 : 0 ≤ A := by have := Real.rpow_nonneg hη.le (-γ); positivity
  have hreg : UlReg k θ (τ - η) Ψ := by
    refine ⟨hmem, fun σ0 h0 ε hε => ?_⟩
    have hΘ0 : UlClosure k θ (ouSg Q ν (η / 2) (ulPert s M ρ c (w σ0))) :=
      ul4b_P_pert_mem H Q T (by positivity) (by linarith) (hw.mem σ0 (hσT σ0 h0))
    obtain ⟨δ2, hδ2, h2⟩ := (ul4_P_ureg Q H.hν k θ H.hθ H.hk2 (T := T) hΘ0).unif (ε / 2) (by positivity)
    obtain ⟨δ1, hδ1, h1⟩ := hw.unif (ε / 2 / (A + 1)) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun σ hσ hlt => ?_⟩
    have hd1 : |σ - σ0| < δ1 := lt_of_lt_of_le hlt (min_le_left _ _)
    have hd2 : |σ - σ0| < δ2 := lt_of_lt_of_le hlt (min_le_right _ _)
    have hu4 : ∀ r ∈ Icc (0 : ℝ) (τ - η), MemCb 4 (w r) := fun r hr => (hcb _ (hw.mem r (hσT r hr))).1
    -- first piece
    have hP1 : ulNormE k θ (fun x => ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) x -
        ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ0)) x) ≤ ENNReal.ofReal (ε / 2) := by
      have e := ul4b_P_pert_sub H Q (τ - σ) (hu4 σ hσ) (hu4 σ0 h0)
      have e' : (fun x => ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) x -
          ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ0)) x) =
          ouSg Q ν (τ - σ) (ulPert s M ρ c (fun y => w σ y - w σ0 y)) := e.symm
      rw [e']
      refine (hest (τ - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ _
        (ul4_closure_sub H.hθ (hw.mem σ (hσT σ hσ)) (hw.mem σ0 (hσT σ0 h0)))).trans ?_
      have hr : (τ - σ) ^ (-γ) ≤ η ^ (-γ) := ul4_rpow_anti (by linarith) hη (by linarith [hσ.2])
      calc ENNReal.ofReal (K * (τ - σ) ^ (-γ)) * ulNormE k θ (fun x => w σ x - w σ0 x)
          ≤ ENNReal.ofReal A * ENNReal.ofReal (ε / 2 / (A + 1)) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hr hK.le))
              (h1 σ (hσT σ hσ) σ0 (hσT σ0 h0) hd1)
        _ = ENNReal.ofReal (A * (ε / 2 / (A + 1))) := (ENNReal.ofReal_mul hA0).symm
        _ ≤ ENNReal.ofReal (ε / 2) := by
            apply ENNReal.ofReal_le_ofReal
            rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
            nlinarith
    -- second piece
    have hsplit : ∀ r : ℝ, η ≤ r → ouSg Q ν r (ulPert s M ρ c (w σ0)) =
        ouSg Q ν (r - η / 2) (ouSg Q ν (η / 2) (ulPert s M ρ c (w σ0))) := fun r hr => by
      have := ul4b_sg_split H Q (hw.mem σ0 (hσT σ0 h0)) (a := r - η / 2) (b := η / 2)
        (by linarith) (by positivity)
      rwa [sub_add_cancel] at this
    have hP2 : ulNormE k θ (fun x => ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ0)) x -
        ouSg Q ν (τ - σ0) (ulPert s M ρ c (w σ0)) x) ≤ ENNReal.ofReal (ε / 2) := by
      have e : (fun x => ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ0)) x -
          ouSg Q ν (τ - σ0) (ulPert s M ρ c (w σ0)) x) =
          fun x => ouSg Q ν (τ - σ - η / 2) (ouSg Q ν (η / 2) (ulPert s M ρ c (w σ0))) x -
            ouSg Q ν (τ - σ0 - η / 2) (ouSg Q ν (η / 2) (ulPert s M ρ c (w σ0))) x := by
        funext x
        rw [hsplit (τ - σ) (by linarith [hσ.2]), hsplit (τ - σ0) (by linarith [h0.2])]
      rw [e]
      refine h2 (τ - σ - η / 2) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (τ - σ0 - η / 2)
        ⟨by linarith [h0.2], by linarith [h0.1]⟩ ?_
      rw [show τ - σ - η / 2 - (τ - σ0 - η / 2) = -(σ - σ0) by ring, abs_neg]; exact hd2
    have e : (fun x => Ψ σ x - Ψ σ0 x) = fun x =>
        (ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) x - ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ0)) x) +
        (ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ0)) x - ouSg Q ν (τ - σ0) (ulPert s M ρ c (w σ0)) x) := by
      funext x; simp only [hΨ]; ring
    rw [e]
    refine (ul0_ulNormE_add k θ _ _).trans ?_
    calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hP1 hP2
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hpt : ∀ x, ContinuousOn (fun σ => Ψ σ x) (Icc 0 (τ - η)) := fun x =>
    ul4_Phi_cont H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν H.hk H.hθ (τ := τ - η) (t0 := τ) (by linarith)
      (ul4_reg_mono (by linarith) hw.toReg) x
  exact ul4b_int_mem H.hk2 H.hθ (by linarith) (ul4b_unif_of_reg H.hθ hreg) hpt

/-- **Closure membership of the Duhamel integral.**  For a closure-valued, uniformly strongly continuous
family `w` on `[0,T]` and `τ ∈ [0,T]`, `x ↦ ∫_0^τ P_{τ-σ} ulPert (w σ)(x) dσ` lies in `UlClosure k θ`. -/
theorem ul4b_mem (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ)
    {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    UlClosure k θ (fun x => ulD Q ν s M ρ c w τ τ x) := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    have : (fun x => ulD Q ν s M ρ c w 0 0 x) = fun _ => 0 := funext (ul4b_ulD_zero Q _ _)
    rw [this]; exact ul4_closure_zero
  obtain ⟨W0, hW0⟩ := ul4_bdd H.hθ hw.toReg
  have hW1 : 0 ≤ max W0 0 := le_max_right _ _
  obtain ⟨Bp, hBp0, hBp⟩ := ul4b_ulD_pt H Q
  choose h0 hh0 hsmall using fun n : ℕ =>
    ul4b_small H Q T hW1 (ε := 1 / 2 ^ n) (by positivity)
  set η : ℕ → ℝ := fun n => min (h0 n) (min (τ / 2) (1 / ((n : ℝ) + 1))) with hη
  have hηpos : ∀ n, 0 < η n := fun n =>
    lt_min (hh0 n) (lt_min (by positivity) (by positivity))
  have hητ : ∀ n, η n < τ := fun n =>
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hηT : ∀ n, η n ≤ T := fun n => ((hητ n).trans_le hτ.2).le
  have hshift : ∀ n, UlReg k θ (η n) (fun σ => w (σ + (τ - η n))) := fun n => by
    have h1 : UlReg k θ (η n + (τ - η n)) w := by
      rw [show η n + (τ - η n) = τ by ring]; exact ul4_reg_mono hτ.2 hw.toReg
    exact ul4b_reg_shift (by linarith [hητ n]) h1
  have hkey : ∀ n x, ulD Q ν s M ρ c w τ τ x - ulD Q ν s M ρ c w (τ - η n) τ x =
      ulD Q ν s M ρ c (fun σ y => w (σ + (τ - η n)) y) (η n) (η n) x := by
    intro n x
    have hreg : UlReg k θ ((τ - η n) + η n) w := by
      rw [sub_add_cancel]; exact ul4_reg_mono hτ.2 hw.toReg
    have := ul4b_tail H Q (α := τ - η n) (η := η n) (by linarith [hητ n]) (hηpos n).le hreg x
    rw [sub_add_cancel] at this
    linarith
  have hzb : ∀ n, ∀ σ ∈ Icc (0 : ℝ) (η n),
      ulNormE k θ (w (σ + (τ - η n))) ≤ ENNReal.ofReal (max W0 0) := fun n σ hσ =>
    (hW0 _ ⟨by linarith [hσ.1, hητ n], by linarith [hσ.2, hτ.2]⟩).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  refine ul4b_lim H.hk2 H.hθ (a := fun n x => ulD Q ν s M ρ c w (τ - η n) τ x)
    (fun n => ul4b_trunc_mem H Q T hw (hηpos n) (hητ n) hτ.2) (fun n => ?_) (fun x => ?_)
  · have e : (fun x => ulD Q ν s M ρ c w τ τ x - ulD Q ν s M ρ c w (τ - η n) τ x) =
        fun x => ulD Q ν s M ρ c (fun σ y => w (σ + (τ - η n)) y) (η n) (η n) x := funext (hkey n)
    rw [e]
    exact hsmall n (hηpos n) (min_le_left _ _) le_rfl (hηT n) (hshift n) (hzb n)
  · set C : ℝ := Bp * max (max W0 0) 0 with hC
    have hC0 : 0 ≤ C := by positivity
    have hdist : ∀ n : ℕ, dist (ulD Q ν s M ρ c w (τ - η n) τ x) (ulD Q ν s M ρ c w τ τ x) ≤
        C * (1 / ((n : ℝ) + 1)) := by
      intro n
      rw [Real.dist_eq, abs_sub_comm, hkey n x]
      refine (hBp (η n) (hηpos n).le (hshift n) (hzb n) x).trans ?_
      exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hC0
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    rw [mul_zero] at ht
    exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg) hdist ht)

/-- **`G1`**: the Duhamel operator preserves closure-valued, uniformly strongly continuous families. -/
theorem ul4b_adm (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) :
    UlDuhamelAdm Q ν s M ρ c k θ T := fun w hw =>
  ⟨fun τ hτ => ul4b_mem H Q T hw hτ,
    ul4b_unif_of_oneside H.hθ (F := fun τ y => ulD Q ν s M ρ c w τ τ y) (T := T)
      fun _ hε => ul4b_cont_oneside H Q T hw hε⟩

end Aux5

/-- **`ul_mild_exists`** (UL-4, plan statement; `ul_mild_exists_of_adm` with `G1` discharged).
`ν > 0`, `0 ≤ s < d`, `ρ` Schwartz, `c` smooth with bounded derivatives, `θ` a uniformly local cutoff,
`4 + d/2 < k`, `T ≥ 0`: there is `C` such that every `f ∈ UlClosure k θ` has a mild solution `u` on `[0,T]`
with values in `UlClosure k θ`, `‖u τ‖_{H^k_ul} ≤ C ‖f‖_{H^k_ul}`, strongly continuous in `ulNormE k θ`, satisfying
`u τ x = ouSg Q ν τ f x + ∫_0^τ ouSg Q ν (τ - σ) (ulPert s M ρ c (u σ)) x dσ`. -/
theorem ul_mild_exists {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ)
    (k : ℕ) (hk : (4 : ℝ) + (d : ℝ) / 2 < k) (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν)
    (Q M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (c : Euc d → Euc d) (hc : IsSmoothBounded c) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, UlClosure k θ f → ∃ u : ℝ → Euc d → ℝ,
      (∀ τ ∈ Icc 0 T, UlClosure k θ (u τ) ∧
        ulNormE k θ (u τ) ≤ ENNReal.ofReal C * ulNormE k θ f) ∧
      (∀ τ₀ ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc 0 T, |τ - τ₀| < δ →
        ulNormE k θ (fun x => u τ x - u τ₀ x) ≤ ENNReal.ofReal ε) ∧
      (∀ τ ∈ Icc 0 T, ∀ x, u τ x = ouSg Q ν τ f x +
        ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (u σ)) x) :=
  ul_mild_exists_of_adm hs0 hsd θ hθ k hk T ν hT hν Q M ρ hρ c hc
    (ul4b_adm ⟨hs0, hsd, hρ, hc, hν, hk, hθ⟩ Q T)

end HRS.MS.Ul
