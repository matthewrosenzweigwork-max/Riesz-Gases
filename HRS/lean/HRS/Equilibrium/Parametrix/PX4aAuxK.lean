import HRS.Equilibrium.Parametrix.PX4aAuxJ

/-!
# Packet PX4a auxiliaries K: potentials with a smooth bounded kernel (`Λ`)

`kPot d Λ g = ∫ Λ(z - w) g(X, w) dw` for `Λ` smooth with bounded derivatives is smooth in `(X, z)`
(`far_param`), its derivatives are bounded by `∫ |g|`-type constants, and a `z`-derivative can be
moved onto the source (`ibp_sing`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section FarKernel

/-- The explicit integrable majorant of the `X`-slices of a chart source. -/
def srcMaj (d : ℕ) (σ : ℝ) (b : ℕ) (A : ℝ) (w : Euc d) : ℝ :=
  (Metric.ball (0 : Euc d) (1 / 8)).indicator
    (fun w => |A| * (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b)) w

lemma srcMaj_nonneg (σ : ℝ) (b : ℕ) (A : ℝ) (w : Euc d) : 0 ≤ srcMaj d σ b A w := by
  refine Set.indicator_nonneg (fun w _ => ?_) w
  positivity

lemma srcMaj_integrable (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (b : ℕ) (A : ℝ) :
    Integrable (srcMaj d σ b A) := by
  unfold srcMaj
  rw [integrable_indicator_iff measurableSet_ball]
  refine Integrable.const_mul ?_ |A|
  exact (integrableOn_const measure_ball_lt_top.ne).add (integrableOn_rpow_log hd hσ b (by norm_num))

lemma srcMaj_bound (hd : 1 ≤ d) {σ : ℝ} {b m : ℕ} {A : ℝ}
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {j : ℕ} (hj : j ≤ m) :
    ∀ᵐ w ∂(volume : Measure (Euc d)), ∀ X, ‖iteratedFDeriv ℝ j (fun X' => g (X', w)) X‖ ≤ srcMaj d σ b A w := by
  have hae : ∀ᵐ w : Euc d, w ≠ 0 := ae_ne_zero_euc (d := d) hd
  filter_upwards [hae] with w hw0 X
  unfold srcMaj
  by_cases hw : ‖w‖ < 1 / 8
  · rw [Set.indicator_of_mem (by simpa using hw)]
    refine (h.slice_bound hj X w hw0).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
  · rw [Set.indicator_of_notMem (by simpa using hw), h.slice_zero j (by linarith [not_lt.mp hw]) X]
    simp

lemma kPot_far_FL (hd : 1 ≤ d) {Λ : Euc d → ℝ} {m : ℕ} (hΛ : ContDiff ℝ (m : WithTop ℕ∞) Λ)
    (hΛb : ∀ i ≤ m, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i Λ y‖ ≤ B) {σ : ℝ} (hσ : σ < d) {b : ℕ} {A : ℝ}
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) :
    ContDiff ℝ (m : WithTop ℕ∞) (kPot d Λ g) ∧
    (∀ j ≤ m, ∀ p : Euc d × Euc d, iteratedFDeriv ℝ j (kPot d Λ g) p =
      ∫ w, iteratedFDeriv ℝ j (fun q : Euc d × Euc d => Λ (q.2 - w) * g (q.1, w)) p) ∧
    (∀ j ≤ m, ∀ p : Euc d × Euc d, Integrable (fun w => iteratedFDeriv ℝ j
      (fun q : Euc d × Euc d => Λ (q.2 - w) * g (q.1, w)) p)) := by
  have hfar := far_param hd h.smooth hΛ hΛb
    (fun j hj => ⟨srcMaj d σ b A, srcMaj_integrable hd hσ b A, srcMaj_bound hd h hj⟩)
    (isOpen_univ : IsOpen (Set.univ : Set (Euc d × Euc d)))
  obtain ⟨hf1, hf2, hf3⟩ := hfar
  refine ⟨contDiffOn_univ.mp hf1, fun j hj p => hf2 j hj p (Set.mem_univ _),
    fun j hj p => hf3 j hj p (Set.mem_univ _)⟩

def farLPsi (d : ℕ) (g : Euc d × Euc d → ℝ) (Λ : Euc d → ℝ) (X0 z0 : Euc d) {a c : ℕ}
    (u : Fin a → Euc d) (v : Fin c → Euc d) (w : Euc d) : ℝ :=
  (iteratedFDeriv ℝ (a + c) (fun q : Euc d × Euc d => Λ (q.2 - w) * g (q.1, w)) (X0, z0)) (pat u v)

lemma farLPsi_eq {Λ : Euc d → ℝ} {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b m A g) {a c : ℕ} (hac : a + c ≤ m)
    (hΛ : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) Λ) (X0 z0 : Euc d)
    (u : Fin a → Euc d) (v : Fin c → Euc d) {w : Euc d} (hw : w ≠ 0) :
    farLPsi d g Λ X0 z0 u v w =
      (iteratedFDeriv ℝ c Λ (z0 - w)) v * (iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u := by
  have h1 : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun y : Euc d => Λ (y - w)) :=
    hΛ.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun X' : Euc d => g (X', w)) := by
    have := h.smooth.of_le (by exact_mod_cast hac : ((a + c : ℕ) : WithTop ℕ∞) ≤ m) |>.comp
      (by fun_prop : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun X' : Euc d => ((X', w) : Euc d × Euc d))).contDiffOn
      (s := Set.univ) (fun X' _ => hw)
    exact contDiffOn_univ.mp this
  unfold farLPsi
  have := iteratedFDeriv_prodpat (a + c) a c rfl _ _ h1 h2 (X0, z0) u v
  rw [this]
  have e : iteratedFDeriv ℝ c (fun y : Euc d => Λ (y - w)) z0 = iteratedFDeriv ℝ c Λ (z0 - w) :=
    iteratedFDeriv_comp_sub c w z0
  simp only [e]

/-- The derivatives of the smooth-kernel potential are bounded by `∫ srcMaj`. -/
lemma kPot_far_bound (hd : 1 ≤ d) {Λ : Euc d → ℝ} {m : ℕ} (hΛ : ContDiff ℝ (m : WithTop ℕ∞) Λ)
    (hΛb : ∀ i ≤ m, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i Λ y‖ ≤ B)
    {σ : ℝ} (hσ : σ < d) {b : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    {a c : ℕ} (hac : a + c ≤ m) {MΛ : ℝ} (hMΛ : ∀ y, ‖iteratedFDeriv ℝ c Λ y‖ ≤ MΛ)
    (X0 z0 : Euc d) (u : Fin a → Euc d) (v : Fin c → Euc d) :
    |iteratedFDeriv ℝ (a + c) (kPot d Λ g) (X0, z0) (pat u v)| ≤
      |MΛ| * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) * ∫ w, srcMaj d σ b A w := by
  obtain ⟨-, hform, hint⟩ := kPot_far_FL hd hΛ hΛb hσ h
  rw [hform (a + c) hac (X0, z0), eval_integral (hint (a + c) hac (X0, z0))]
  have hΛ' : ContDiff ℝ ((a + c : ℕ) : WithTop ℕ∞) Λ := hΛ.of_le (by exact_mod_cast hac)
  have hmaj := srcMaj_integrable hd hσ b A
  have hPu : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hPv : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  rw [← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le (hmaj.const_mul (|MΛ| * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)))
    (μ := (volume : Measure (Euc d))) (f := fun w => farLPsi d g Λ X0 z0 u v w) ?_
  · refine hb.trans (le_of_eq ?_)
    rw [integral_const_mul]
  · have hae : ∀ᵐ w : Euc d, w ≠ 0 := ae_ne_zero_euc (d := d) hd
    filter_upwards [hae, srcMaj_bound hd h (j := a) (by omega)] with w hw0 hsl
    show ‖farLPsi d g Λ X0 z0 u v w‖ ≤ |MΛ| * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) * srcMaj d σ b A w
    rw [farLPsi_eq h hac hΛ' X0 z0 u v hw0, norm_mul]
    have h1 : ‖(iteratedFDeriv ℝ c Λ (z0 - w)) v‖ ≤ |MΛ| * ∏ j, ‖v j‖ :=
      ((iteratedFDeriv ℝ c Λ (z0 - w)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((hMΛ _).trans (le_abs_self _)) hPv)
    have h2 : ‖(iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u‖ ≤ srcMaj d σ b A w * ∏ i, ‖u i‖ :=
      ((iteratedFDeriv ℝ a (fun X' => g (X', w)) X0).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (hsl X0) hPu)
    calc ‖(iteratedFDeriv ℝ c Λ (z0 - w)) v‖ * ‖(iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u‖
        ≤ (|MΛ| * ∏ j, ‖v j‖) * (srcMaj d σ b A w * ∏ i, ‖u i‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) hPv)
      _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- A `z`-derivative of the smooth-kernel potential moves onto the source. -/
lemma kPot_far_dirD (hd : 2 ≤ d) {Λ : Euc d → ℝ} {m : ℕ}
    (hΛ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Λ)
    (hΛb : ∀ i ≤ m + 1, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i Λ y‖ ≤ B)
    {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b : ℕ} {A : ℝ} (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b (m + 1) A g) (X z e : Euc d) :
    dirD ((0 : Euc d), e) (kPot d Λ g) (X, z) = kPot d Λ (dirD ((0 : Euc d), e) g) (X, z) := by
  have hd1 : 1 ≤ d := by omega
  have hσd : σ < d := by linarith
  obtain ⟨-, hform, hint⟩ := kPot_far_FL hd1 hΛ hΛb hσd h
  have hL : iteratedFDeriv ℝ (0 + 1) (kPot d Λ g) (X, z) (pat (Fin.elim0 : Fin 0 → Euc d) (fun _ : Fin 1 => e)) =
      ∫ w, farLPsi d g Λ X z (Fin.elim0 : Fin 0 → Euc d) (fun _ : Fin 1 => e) w := by
    rw [hform (0 + 1) (by omega) (X, z), eval_integral (hint (0 + 1) (by omega) (X, z))]
    rfl
  rw [iteratedFDeriv_one_pat] at hL
  rw [hL]
  obtain ⟨B0, hB0⟩ := hΛb 0 (by omega)
  obtain ⟨B1, hB1⟩ := hΛb 1 (by omega)
  have hΛ1 : ContDiff ℝ 1 Λ := hΛ.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  set φ : Euc d → ℝ := fun w => Λ (z - w) with hφ
  have hφ1 : ContDiff ℝ 1 φ := hΛ1.comp (contDiff_const.sub contDiff_id)
  have hφd : ∀ w, HasFDerivAt φ ((fderiv ℝ Λ (z - w)).comp
      (-(ContinuousLinearMap.id ℝ (Euc d)))) w := by
    intro w
    have h1 : HasFDerivAt (fun w : Euc d => z - w) (-(ContinuousLinearMap.id ℝ (Euc d))) w :=
      (hasFDerivAt_id w).const_sub z
    exact ((hΛ1.differentiable (by simp)) (z - w)).hasFDerivAt.comp w h1
  have hM : ∀ y, ‖φ y‖ ≤ max B0 B1 := fun y => by
    have := hB0 (z - y)
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_max_left _ _)
  have hM' : ∀ y, ‖fderiv ℝ φ y‖ ≤ max B0 B1 := fun y => by
    rw [(hφd y).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hB1 (z - y)
    rw [norm_iteratedFDeriv_one] at h1
    have h2 : ‖-(ContinuousLinearMap.id ℝ (Euc d))‖ ≤ 1 := by
      rw [norm_neg]; exact ContinuousLinearMap.norm_id_le
    have h0 : 0 ≤ max B0 B1 := (norm_nonneg _).trans (hM 0)
    calc _ ≤ max B0 B1 * 1 := mul_le_mul (h1.trans (le_max_right _ _)) h2 (norm_nonneg _) h0
      _ = _ := mul_one _
  have hibp := ibp_sing hd hσ hA h X e hφ1 hM hM'
  have hfd : ∀ w, fderiv ℝ φ w e = -(fderiv ℝ Λ (z - w) e) := fun w => by
    rw [(hφd w).fderiv]; simp
  simp only [hfd] at hibp
  have hae := ae_ne_zero_euc (d := d) hd1
  have e1 : ∫ w, farLPsi d g Λ X z (Fin.elim0 : Fin 0 → Euc d) (fun _ : Fin 1 => e) w =
      ∫ w, fderiv ℝ Λ (z - w) e * g (X, w) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw0
    rw [farLPsi_eq h (by omega) (hΛ.of_le (by exact_mod_cast (by omega : 0 + 1 ≤ m + 1))) X z
      Fin.elim0 (fun _ => e) hw0]
    simp [iteratedFDeriv_one_apply, iteratedFDeriv_zero_apply]
  rw [e1]
  simp only [neg_mul, integral_neg, neg_neg] at hibp
  unfold kPot
  exact hibp.symm

end FarKernel

end HRS.Parx

end
