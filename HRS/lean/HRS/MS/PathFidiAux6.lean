import HRS.MS.PathFidiAux5

/-!
# SA26 packet P5: noise covariances, their positivity and convergence
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### Generic noise covariance matrices -/

section Sig

/-- the truncated gradient of the adjoint orbit of a coefficient `C` -/
def sa26_GC (C : WholeCoeff d) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p) :
    ℝ → Euc d → Euc d := fun r x =>
  if r ∈ Set.Icc (0 : ℝ) (ts a) then gradient (propagatorW C r (ts a) (φ a)) x else 0

theorem sa26_G_eq_GC (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) :
    sa26_G S N ts φ = sa26_GC (S.coeff N) ts φ := rfl

/-- the noise covariance matrix `(2q ∫_0^{t_a ∧ t_b} ⟨∇U_a, ∇U_b⟩ ρ)_{ab}` -/
def sa26_Sig (C : WholeCoeff d) (q : ℝ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) :
    Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => noiseCovW C q (ts a) (ts b) (φ a) (φ b)

theorem sa26_GC_meas (C : WholeCoeff d) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p)
    (h0 : 0 ≤ ts a) (hex : ∃ f, IsClassicalAdjointW C (ts a) (φ a) f) :
    Measurable fun q : ℝ × Euc d => sa26_GC C ts φ a q.1 q.2 := by
  have hf := (HRS.MS.Fcau.propagatorW_isClassical hex).isC12TestRd
  have hcont := HRS.MH.DualityRd.da3_continuous_gradient_clamp h0 hf
  have e : (fun q : ℝ × Euc d => sa26_GC C ts φ a q.1 q.2) = fun q => if q.1 ∈ Set.Icc (0 : ℝ) (ts a) then
      gradient (propagatorW C (HRS.clampTI (ts a) q.1) (ts a) (φ a)) q.2 else 0 := by
    funext q
    unfold sa26_GC
    by_cases h : q.1 ∈ Set.Icc (0 : ℝ) (ts a)
    · simp only [h, if_true, HRS.clampTI_of_mem h]
    · simp only [h, if_false]
  rw [e]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hcont.measurable measurable_const

theorem sa26_norm_grad (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [norm_iteratedFDeriv_one]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _

theorem sa26_GC_norm_le (C : WholeCoeff d) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd)
    (hb : ∀ r ∈ Set.Icc (0 : ℝ) (ts a), ∀ x, ‖iteratedFDeriv ℝ 1 (propagatorW C r (ts a) (φ a)) x‖ ≤ Bd)
    (r : ℝ) (x : Euc d) : ‖sa26_GC C ts φ a r x‖ ≤ Bd := by
  unfold sa26_GC
  by_cases h : r ∈ Set.Icc (0 : ℝ) (ts a)
  · simp only [h, if_true]
    rw [sa26_norm_grad]
    exact hb r h x
  · simp only [h, if_false, norm_zero]
    exact hBd0

theorem sa26_probDensity_integrable {ρ : Euc d → ℝ} (h : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra hi
  have := h.integral_one
  rw [integral_undef hi] at this
  exact zero_ne_one this

theorem sa26_integratedCov_eq (C : WholeCoeff d) (q : ℝ) {T : ℝ} {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) :
    integratedCov T (sa26SigBar ts (sa26_GC C ts φ) (fun r => C.ρ (HRS.MP.RdRem.mrrClamp T r)) (2 * q)) =
      sa26_Sig C q ts φ := by
  ext a b
  simp only [integratedCov, sa26SigBar, sa26_Sig, Matrix.of_apply, noiseCovW]
  have hm : min (ts a) (ts b) ≤ T := (min_le_left _ _).trans (hts a).2
  have e1 : (fun σ : ℝ => if 0 ≤ σ ∧ σ < min (ts a) (ts b) then 2 * q * ∫ x,
        inner ℝ (sa26_GC C ts φ a σ x) (sa26_GC C ts φ b σ x) * C.ρ (HRS.MP.RdRem.mrrClamp T σ) x else 0) =
      (Set.Ico (0 : ℝ) (min (ts a) (ts b))).indicator (fun σ => 2 * q * ∫ x,
        inner ℝ (sa26_GC C ts φ a σ x) (sa26_GC C ts φ b σ x) * C.ρ (HRS.MP.RdRem.mrrClamp T σ) x) := by
    funext σ
    simp only [Set.indicator, Set.mem_Ico]
  have hsub : Set.Icc (0 : ℝ) T ∩ Set.Ico 0 (min (ts a) (ts b)) = Set.Ico 0 (min (ts a) (ts b)) :=
    Set.inter_eq_right.2 (fun σ hσ => ⟨hσ.1, hσ.2.le.trans hm⟩)
  rw [e1, setIntegral_indicator measurableSet_Ico, hsub, ← integral_Icc_eq_integral_Ico,
    integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  have hra : σ ∈ Set.Icc (0 : ℝ) (ts a) := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hrb : σ ∈ Set.Icc (0 : ℝ) (ts b) := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hσT : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans hm⟩
  simp only [sa26_GC, hra, hrb, if_true, HRS.MP.RdRem.mrrClamp_of_mem hσT]

theorem sa26_Sig_psd (C : WholeCoeff d) {q : ℝ} (hq : 0 ≤ q) {T : ℝ} (hT0 : 0 ≤ T) {p : ℕ}
    (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (hex : ∀ a, ∃ f, IsClassicalAdjointW C (ts a) (φ a) f) {B : ℝ}
    (hGb : ∀ a r x, ‖sa26_GC C ts φ a r x‖ ≤ B)
    (hρtm : Measurable fun q' : ℝ × Euc d => C.ρ (HRS.MP.RdRem.mrrClamp T q'.1) q'.2)
    (hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r)) :
    (sa26_Sig C q ts φ).PosSemidef := by
  have hGm : ∀ a, Measurable fun q' : ℝ × Euc d => sa26_GC C ts φ a q'.1 q'.2 := fun a =>
    sa26_GC_meas C ts φ a (hts a).1 (hex a)
  have hρd : ∀ r, HRS.Whole.IsProbDensity (C.ρ (HRS.MP.RdRem.mrrClamp T r)) := fun r =>
    hdens _ (HRS.MP.RdRem.mrrClamp_mem hT0 r)
  have hdet := sa26_sigBar_isDet (ts := ts) (c := 2 * q) hGm hρtm hGb (fun r x => (hρd r).nonneg x)
    (fun r => sa26_probDensity_integrable (hρd r)) (fun r => (hρd r).integral_one.le) (by linarith) T
  rw [← sa26_integratedCov_eq C q ts φ hts]
  exact integratedCov_psd hdet

end Sig


/-! ### Convergence of the noise covariances -/

section SigConv

/-- the constant `∫ ⟨x⟩^{-(d+3)}` -/
def sa26_Cd (d : ℕ) : ℝ := ∫ x : Euc d, jbracket x ^ (-((d : ℝ) + 3))

theorem sa26_jb_integrable : Integrable (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3))) := by
  have hL : ((Module.finrank ℝ (Euc d) : ℕ) : ℝ) < (d : ℝ) + 3 := by
    rw [finrank_euclideanSpace_fin]; linarith
  have hL0 : (0 : ℝ) < (d : ℝ) + 3 := by positivity
  refine ((integrable_one_add_norm hL).const_mul (2 ^ (((d : ℝ) + 3) / 2))).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · have : Continuous fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3)) := by
      unfold jbracket
      refine Continuous.rpow_const (by fun_prop) fun x => Or.inl ?_
      positivity
    exact this.aestronglyMeasurable
  · have h1 := rpow_neg_one_add_norm_sq_le x hL0
    have e : jbracket x ^ (-((d : ℝ) + 3)) = ((1 : ℝ) + ‖x‖ ^ 2) ^ (-((d : ℝ) + 3) / 2) := by
      unfold jbracket
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    rw [Real.norm_of_nonneg (show 0 ≤ jbracket x ^ (-((d : ℝ) + 3)) from
      Real.rpow_nonneg (Real.sqrt_nonneg _) _), e]
    exact h1

theorem sa26_Cd_nonneg : 0 ≤ sa26_Cd d :=
  integral_nonneg fun x => Real.rpow_nonneg (by unfold jbracket; exact Real.sqrt_nonneg _) _

theorem sa26_density_diff {ρ₁ ρ₂ h : Euc d → ℝ} {δ B : ℝ} (hδ : 0 ≤ δ)
    (hρ : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |ρ₁ x - ρ₂ x| ≤ δ) (hh : ∀ x, |h x| ≤ B) :
    |∫ x, h x * (ρ₁ x - ρ₂ x)| ≤ B * (sa26_Cd d * δ) := by
  have hpt : ∀ x, ‖h x * (ρ₁ x - ρ₂ x)‖ ≤ B * (δ * jbracket x ^ (-((d : ℝ) + 3))) := by
    intro x
    have hj : 0 < jbracket x := by unfold jbracket; positivity
    have h1 : |ρ₁ x - ρ₂ x| ≤ δ * jbracket x ^ (-((d : ℝ) + 3)) := by
      rw [Real.rpow_neg hj.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hj _)]
      linarith [hρ x, mul_comm (|ρ₁ x - ρ₂ x|) (jbracket x ^ ((d : ℝ) + 3))]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hh x) h1 (abs_nonneg _) ((abs_nonneg _).trans (hh x))
  have hint : Integrable (fun x : Euc d => B * (δ * jbracket x ^ (-((d : ℝ) + 3)))) :=
    (sa26_jb_integrable.const_mul δ).const_mul B
  have := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_const_mul]
  unfold sa26_Cd
  ring

theorem sa26_F_diff {ρ₁ ρ₂ : Euc d → ℝ} (hρ₁ : HRS.Whole.IsProbDensity ρ₁)
    (hρ₂ : HRS.Whole.IsProbDensity ρ₂) {u v u' v' : Euc d → Euc d}
    (hu : Measurable u) (hv : Measurable v) (hu' : Measurable u') (hv' : Measurable v')
    {Ba Bb δa δb Δ : ℝ} (hΔ : 0 ≤ Δ) (hBa : ∀ x, ‖u x‖ ≤ Ba) (hBa' : ∀ x, ‖u' x‖ ≤ Ba)
    (hBb : ∀ x, ‖v x‖ ≤ Bb) (hBb' : ∀ x, ‖v' x‖ ≤ Bb)
    (hda : ∀ x, ‖u x - u' x‖ ≤ δa) (hdb : ∀ x, ‖v x - v' x‖ ≤ δb)
    (hρ : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |ρ₁ x - ρ₂ x| ≤ Δ) :
    |(∫ x, inner ℝ (u x) (v x) * ρ₁ x) - ∫ x, inner ℝ (u' x) (v' x) * ρ₂ x| ≤
      (δa * Bb + Ba * δb) + Ba * Bb * (sa26_Cd d * Δ) := by
  have hBa0 : 0 ≤ Ba := (norm_nonneg _).trans (hBa 0)
  have hBb0 : 0 ≤ Bb := (norm_nonneg _).trans (hBb 0)
  have hδa0 : 0 ≤ δa := (norm_nonneg _).trans (hda 0)
  have hδb0 : 0 ≤ δb := (norm_nonneg _).trans (hdb 0)
  have hi₁ := sa26_probDensity_integrable hρ₁
  have hi₂ := sa26_probDensity_integrable hρ₂
  set h₁ : Euc d → ℝ := fun x => inner ℝ (u x) (v x) with hh₁
  set h₂ : Euc d → ℝ := fun x => inner ℝ (u' x) (v' x) with hh₂
  have hh₁m : Measurable h₁ := hu.inner hv
  have hh₂m : Measurable h₂ := hu'.inner hv'
  have hb₁ : ∀ x, |h₁ x| ≤ Ba * Bb := fun x =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBa x) (hBb x) (norm_nonneg _) hBa0)
  have hb₂ : ∀ x, |h₂ x| ≤ Ba * Bb := fun x =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBa' x) (hBb' x) (norm_nonneg _) hBa0)
  have hd12 : ∀ x, |h₁ x - h₂ x| ≤ δa * Bb + Ba * δb := by
    intro x
    have e : h₁ x - h₂ x = inner ℝ (u x - u' x) (v x) + inner ℝ (u' x) (v x - v' x) := by
      simp only [hh₁, hh₂, inner_sub_left, inner_sub_right]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hda x) (hBb x) (norm_nonneg _) hδa0)
    · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBa' x) (hdb x) (norm_nonneg _) hBa0)
  have hbd1 : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖h₁ x‖ ≤ Ba * Bb :=
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb₁ x
  have hbd2 : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖h₂ x‖ ≤ Ba * Bb :=
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb₂ x
  have hbd12 : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖h₁ x - h₂ x‖ ≤ δa * Bb + Ba * δb :=
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hd12 x
  have hI1 : Integrable (fun x => h₁ x * ρ₁ x) := hi₁.bdd_mul hh₁m.aestronglyMeasurable hbd1
  have hI2 : Integrable (fun x => h₂ x * ρ₂ x) := hi₂.bdd_mul hh₂m.aestronglyMeasurable hbd2
  have hA : Integrable (fun x => (h₁ x - h₂ x) * ρ₁ x) :=
    hi₁.bdd_mul (hh₁m.sub hh₂m).aestronglyMeasurable hbd12
  have hB : Integrable (fun x => h₂ x * (ρ₁ x - ρ₂ x)) :=
    (hi₁.sub hi₂).bdd_mul hh₂m.aestronglyMeasurable hbd2
  have hsplit : (∫ x, h₁ x * ρ₁ x) - ∫ x, h₂ x * ρ₂ x =
      (∫ x, (h₁ x - h₂ x) * ρ₁ x) + ∫ x, h₂ x * (ρ₁ x - ρ₂ x) := by
    rw [← integral_sub hI1 hI2, ← integral_add hA hB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have hint : Integrable (fun x : Euc d => (δa * Bb + Ba * δb) * ρ₁ x) := hi₁.const_mul _
    have := norm_integral_le_of_norm_le (f := fun x => (h₁ x - h₂ x) * ρ₁ x) hint
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ₁.nonneg x)]
        exact mul_le_mul_of_nonneg_right (hd12 x) (hρ₁.nonneg x))
    rw [Real.norm_eq_abs, integral_const_mul, hρ₁.integral_one, mul_one] at this
    exact this
  · exact sa26_density_diff hΔ hρ hb₂

end SigConv


section SigConv2

theorem sa26_F_abs_le {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {u v : Euc d → Euc d}
    {Ba Bb : ℝ} (hBa : ∀ x, ‖u x‖ ≤ Ba) (hBb : ∀ x, ‖v x‖ ≤ Bb) :
    |∫ x, inner ℝ (u x) (v x) * ρ x| ≤ Ba * Bb := by
  have hBa0 : 0 ≤ Ba := (norm_nonneg _).trans (hBa 0)
  have hi := sa26_probDensity_integrable hρ
  have hint : Integrable (fun x : Euc d => (Ba * Bb) * ρ x) := hi.const_mul _
  have := norm_integral_le_of_norm_le (f := fun x => inner ℝ (u x) (v x) * ρ x) hint
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
      exact mul_le_mul_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hBa x) (hBb x) (norm_nonneg _) hBa0)) (hρ.nonneg x))
  rw [Real.norm_eq_abs, integral_const_mul, hρ.integral_one, mul_one] at this
  exact this

theorem sa26_Sig_tendsto (S : WholeMainData d) (L : LimitCoeffsRd d) {T : ℝ} (hT0 : 0 ≤ T) {p : ℕ}
    (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    {Bd Ks : Fin p → ℝ} (hBd0 : ∀ a, 0 ≤ Bd a) (hKs0 : ∀ a, 0 ≤ Ks a)
    {Dl : ℕ → ℝ} (hDl0 : ∀ N, 0 ≤ Dl N) (hDlt : Tendsto Dl atTop (𝓝 0))
    (hexN : ∀ N : ℕ, 1 ≤ N → ∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f)
    (hexL : ∀ a, ∃ f, IsClassicalAdjointW (L.coeff S) (ts a) (φ a) f)
    (hGN : ∀ N : ℕ, 1 ≤ N → ∀ a r x, ‖sa26_GC (S.coeff N) ts φ a r x‖ ≤ Bd a)
    (hGL : ∀ a r x, ‖sa26_GC (L.coeff S) ts φ a r x‖ ≤ Bd a)
    (hGst : ∀ᶠ N : ℕ in atTop, ∀ a r x,
      ‖sa26_GC (S.coeff N) ts φ a r x - sa26_GC (L.coeff S) ts φ a r x‖ ≤ Ks a * Dl N)
    (hρst : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x,
      jbracket x ^ ((d : ℝ) + 3) * |(S.coeff N).ρ r x - (L.coeff S).ρ r x| ≤ Dl N)
    (hqst : ∀ᶠ N : ℕ in atTop, |S.qN N - L.invβstar| ≤ Dl N)
    (hρN : ∀ N : ℕ, 1 ≤ N → ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity ((S.coeff N).ρ r))
    (hρL : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity ((L.coeff S).ρ r))
    (hρtmN : ∀ N : ℕ, 1 ≤ N → Measurable fun q : ℝ × Euc d =>
      (S.coeff N).ρ (HRS.MP.RdRem.mrrClamp T q.1) q.2)
    (hρtmL : Measurable fun q : ℝ × Euc d => (L.coeff S).ρ (HRS.MP.RdRem.mrrClamp T q.1) q.2) :
    Tendsto (fun N => sa26_Sig (S.coeff N) (S.qN N) ts φ) atTop
      (𝓝 (sa26_Sig (L.coeff S) L.invβstar ts φ)) := by
  classical
  have hq0 : 0 ≤ L.invβstar := L.hinvβstar
  refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
  set Ba := Bd a with hBa
  set Bb := Bd b with hBb
  set K1 : ℝ := (Ks a * Bb + Ba * Ks b) + Ba * Bb * sa26_Cd d with hK1
  have hK10 : 0 ≤ K1 := by
    have := sa26_Cd_nonneg (d := d)
    have := hBd0 a; have := hBd0 b; have := hKs0 a; have := hKs0 b
    positivity
  set Mc : ℝ := 2 * (Ba * Bb) + 2 * L.invβstar * K1 with hMc
  have hMc0 : 0 ≤ Mc := by
    have := hBd0 a; have := hBd0 b
    positivity
  -- uniform bounds
  set Bu : ℝ := ∑ c, Bd c with hBu
  have hBdle : ∀ c, Bd c ≤ Bu := fun c =>
    Finset.single_le_sum (f := Bd) (fun c _ => hBd0 c) (Finset.mem_univ c)
  -- measurability data
  have hGmN : ∀ N : ℕ, 1 ≤ N → ∀ c, Measurable fun q : ℝ × Euc d => sa26_GC (S.coeff N) ts φ c q.1 q.2 :=
    fun N hN c => sa26_GC_meas _ ts φ c (hts c).1 (hexN N hN c)
  have hGmL : ∀ c, Measurable fun q : ℝ × Euc d => sa26_GC (L.coeff S) ts φ c q.1 q.2 := fun c =>
    sa26_GC_meas _ ts φ c (hts c).1 (hexL c)
  have hρdN : ∀ N : ℕ, 1 ≤ N → ∀ r, HRS.Whole.IsProbDensity ((S.coeff N).ρ (HRS.MP.RdRem.mrrClamp T r)) :=
    fun N hN r => hρN N hN _ (HRS.MP.RdRem.mrrClamp_mem hT0 r)
  have hρdL : ∀ r, HRS.Whole.IsProbDensity ((L.coeff S).ρ (HRS.MP.RdRem.mrrClamp T r)) := fun r =>
    hρL _ (HRS.MP.RdRem.mrrClamp_mem hT0 r)
  set sbN : ℕ → ℝ → Matrix (Fin p) (Fin p) ℝ := fun N => sa26SigBar ts (sa26_GC (S.coeff N) ts φ)
    (fun r => (S.coeff N).ρ (HRS.MP.RdRem.mrrClamp T r)) (2 * S.qN N) with hsbN
  set sbL : ℝ → Matrix (Fin p) (Fin p) ℝ := sa26SigBar ts (sa26_GC (L.coeff S) ts φ)
    (fun r => (L.coeff S).ρ (HRS.MP.RdRem.mrrClamp T r)) (2 * L.invβstar) with hsbL
  have hSgN : ∀ N, sa26_Sig (S.coeff N) (S.qN N) ts φ a b = ∫ σ in Set.Icc (0 : ℝ) T, sbN N σ a b := by
    intro N
    rw [← sa26_integratedCov_eq (S.coeff N) (S.qN N) ts φ hts]
    rfl
  have hSgL : sa26_Sig (L.coeff S) L.invβstar ts φ a b = ∫ σ in Set.Icc (0 : ℝ) T, sbL σ a b := by
    rw [← sa26_integratedCov_eq (L.coeff S) L.invβstar ts φ hts]
    rfl
  -- integrability of the entries
  have hintN : ∀ N : ℕ, 1 ≤ N → IntegrableOn (fun σ => sbN N σ a b) (Set.Icc (0 : ℝ) T) := by
    intro N hN
    refine Integrable.mono' (g := fun _ => |2 * S.qN N| * (Bu * Bu)) (integrable_const _)
      (sa26_sigBar_entry_meas (hGmN N hN) (hρtmN N hN) a b).aestronglyMeasurable
      (Eventually.of_forall fun σ => ?_)
    rw [Real.norm_eq_abs]
    exact sa26_sigBar_entry_bound (hGmN N hN) (hρtmN N hN) (fun c r x => (hGN N hN c r x).trans (hBdle c))
      (fun r x => (hρdN N hN r).nonneg x) (fun r => sa26_probDensity_integrable (hρdN N hN r))
      (fun r => (hρdN N hN r).integral_one.le) a b σ
  have hintL : IntegrableOn (fun σ => sbL σ a b) (Set.Icc (0 : ℝ) T) := by
    refine Integrable.mono' (g := fun _ => |2 * L.invβstar| * (Bu * Bu)) (integrable_const _)
      (sa26_sigBar_entry_meas hGmL hρtmL a b).aestronglyMeasurable (Eventually.of_forall fun σ => ?_)
    rw [Real.norm_eq_abs]
    exact sa26_sigBar_entry_bound hGmL hρtmL (fun c r x => (hGL c r x).trans (hBdle c))
      (fun r x => (hρdL r).nonneg x) (fun r => sa26_probDensity_integrable (hρdL r))
      (fun r => (hρdL r).integral_one.le) a b σ
  -- the pointwise estimate
  have hpt : ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Set.Icc (0 : ℝ) T, |sbN N σ a b - sbL σ a b| ≤ Mc * Dl N := by
    filter_upwards [hGst, hρst, hqst, eventually_ge_atTop 1] with N hG hρ hq hN1 σ hσ
    have hMD : 0 ≤ Mc * Dl N := mul_nonneg hMc0 (hDl0 N)
    by_cases hc : 0 ≤ σ ∧ σ < min (ts a) (ts b)
    · have hσc := HRS.MP.RdRem.mrrClamp_of_mem hσ
      simp only [hsbN, hsbL, sa26SigBar, Matrix.of_apply, if_pos hc, hσc]
      have hF12 := sa26_F_diff (hρN N hN1 σ hσ) (hρL σ hσ)
        ((hGmN N hN1 a).comp measurable_prodMk_left) ((hGmN N hN1 b).comp measurable_prodMk_left)
        ((hGmL a).comp measurable_prodMk_left) ((hGmL b).comp measurable_prodMk_left)
        (hΔ := hDl0 N) (fun x => hGN N hN1 a σ x) (fun x => hGL a σ x) (fun x => hGN N hN1 b σ x)
        (fun x => hGL b σ x) (fun x => hG a σ x) (fun x => hG b σ x) (fun x => hρ σ hσ x)
      have hF1 := sa26_F_abs_le (hρN N hN1 σ hσ) (fun x => hGN N hN1 a σ x) (fun x => hGN N hN1 b σ x)
      set F1 := ∫ x, inner ℝ (sa26_GC (S.coeff N) ts φ a σ x) (sa26_GC (S.coeff N) ts φ b σ x) *
        (S.coeff N).ρ σ x with hF1def
      set F2 := ∫ x, inner ℝ (sa26_GC (L.coeff S) ts φ a σ x) (sa26_GC (L.coeff S) ts φ b σ x) *
        (L.coeff S).ρ σ x with hF2def
      have hK : Ks a * Dl N * Bd b + Bd a * (Ks b * Dl N) + Bd a * Bd b * (sa26_Cd d * Dl N) =
          K1 * Dl N := by
        rw [hK1, hBa, hBb]; ring
      have hdecomp : 2 * S.qN N * F1 - 2 * L.invβstar * F2 =
          2 * (S.qN N - L.invβstar) * F1 + 2 * L.invβstar * (F1 - F2) := by ring
      rw [hdecomp]
      refine (abs_add_le _ _).trans ?_
      have h1 : |2 * (S.qN N - L.invβstar) * F1| ≤ 2 * (Ba * Bb) * Dl N := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := mul_le_mul hq hF1 (abs_nonneg _) (hDl0 N)
        nlinarith [abs_nonneg (S.qN N - L.invβstar), abs_nonneg F1]
      have h2 : |2 * L.invβstar * (F1 - F2)| ≤ 2 * L.invβstar * (K1 * Dl N) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * L.invβstar)]
        exact mul_le_mul_of_nonneg_left (hF12.trans (le_of_eq hK)) (by positivity)
      calc _ ≤ 2 * (Ba * Bb) * Dl N + 2 * L.invβstar * (K1 * Dl N) := add_le_add h1 h2
        _ = Mc * Dl N := by rw [hMc]; ring
    · simp only [hsbN, hsbL, sa26SigBar, Matrix.of_apply, if_neg hc, sub_zero, abs_zero]
      exact hMD
  -- conclusion
  have hlim : Tendsto (fun N => T * (Mc * Dl N)) atTop (𝓝 0) := by
    have := (hDlt.const_mul Mc).const_mul T
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ hlim
  filter_upwards [hpt, eventually_ge_atTop 1] with N hN hN1
  rw [hSgN, hSgL, Real.dist_eq, ← integral_sub (hintN N hN1) hintL]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T)
    (f := fun σ => sbN N σ a b - sbL σ a b) (C := Mc * Dl N) (by simp [Real.volume_Icc]) (fun σ hσ => by
      rw [Real.norm_eq_abs]; exact hN σ hσ)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hT0]
  ring

end SigConv2

end HRS.MS.PathFidi
