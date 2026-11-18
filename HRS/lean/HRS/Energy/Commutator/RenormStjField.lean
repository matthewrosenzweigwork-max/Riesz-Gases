import HRS.Energy.Commutator.RenormStjMu

/-!
# Route S, packet STJ: the field term (`B3`), measure domination and the pick of the radii
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

/-- `l`-independent measure dominating `σ_{l,η} / cfl(r/4)` for `r/2 ≤ η < r` -/
def nuT (d : ℕ) (r η : ℝ) : Measure (Torus d) :=
  ENNReal.ofReal ((4 / r) ^ d) • ballT d η + sphT d η

def nuC (d : ℕ) (r η : ℝ) (a : Torus d) : Measure (Torus d) := (nuT d r η).map (fun y => y + a)

theorem smearT_le_nuT (hd : 1 ≤ d) {l r η : ℝ} (hl : 0 < l) (hr : 0 < r) (hrη : r / 2 ≤ η) :
    smearT d l η ≤ ENNReal.ofReal (cfl d l (r / 4)) • nuT d r η := by
  have hη : 0 < η := by linarith
  have hr4 : 0 < r / 4 := by positivity
  have hc1 : l * yukawa d l η ≤ cfl d l (r / 4) * (4 / r) ^ d := by
    have h1 := ball_coef_le_cfl hd hl hη
    have h2 := cfl_antitone hd hl hr4 (show r / 4 ≤ η / 2 by linarith)
    have h3 : (r / 4) ^ d ≤ (η / 2) ^ d := pow_le_pow_left₀ hr4.le (by linarith) d
    have hΓ : 0 ≤ l * yukawa d l η := mul_nonneg hl.le ((yukawa_ode hd hl).1 η hη).le
    have h4 : l * yukawa d l η * (r / 4) ^ d ≤ cfl d l (r / 4) := by
      calc l * yukawa d l η * (r / 4) ^ d ≤ l * yukawa d l η * (η / 2) ^ d :=
            mul_le_mul_of_nonneg_left h3 hΓ
        _ ≤ cfl d l (η / 2) := h1
        _ ≤ cfl d l (r / 4) := h2
    have hp : 0 < (r / 4) ^ d := pow_pos hr4 d
    rw [show (4 / r) ^ d = 1 / (r / 4) ^ d by rw [one_div, ← inv_pow]; congr 1; field_simp,
      ← mul_div_assoc, mul_one, le_div_iff₀ hp]
    exact h4
  have hc2 : cfl d l η ≤ cfl d l (r / 4) := cfl_antitone hd hl hr4 (by linarith)
  rw [smearT_eq]
  unfold nuT
  refine fun s => ?_
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have e1 : ENNReal.ofReal (cfl d l (r / 4)) * (ENNReal.ofReal ((4 / r) ^ d) * ballT d η s +
      sphT d η s) = ENNReal.ofReal (cfl d l (r / 4) * (4 / r) ^ d) * ballT d η s +
      ENNReal.ofReal (cfl d l (r / 4)) * sphT d η s := by
    have hcn : 0 ≤ cfl d l (r / 4) := (cfl_pos hd hl hr4).le
    rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hcn]
  rw [e1]
  exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hc1) le_rfl)
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hc2) le_rfl)

theorem chS_le_nuC (hd : 1 ≤ d) {l r η : ℝ} (hl : 0 < l) (hr : 0 < r) (hrη : r / 2 ≤ η) (a : Torus d) :
    chS d l η a ≤ ENNReal.ofReal (cfl d l (r / 4)) • nuC d r η a := by
  unfold chS nuC
  rw [← Measure.map_smul _ (measurable_add_const a).aemeasurable]
  exact Measure.map_mono (smearT_le_nuT hd hl hr hrη) (measurable_add_const a)

theorem lintegral_chS_le (hd : 1 ≤ d) {l r η : ℝ} (hl : 0 < l) (hr : 0 < r) (hrη : r / 2 ≤ η) (a : Torus d)
    (G : Torus d → ℝ≥0∞) :
    ∫⁻ x, G x ∂(chS d l η a) ≤ ENNReal.ofReal (cfl d l (r / 4)) * ∫⁻ x, G x ∂(nuC d r η a) := by
  calc ∫⁻ x, G x ∂(chS d l η a) ≤ ∫⁻ x, G x ∂(ENNReal.ofReal (cfl d l (r / 4)) • nuC d r η a) :=
        lintegral_mono' (chS_le_nuC hd hl hr hrη a) le_rfl
    _ = _ := lintegral_smul_measure _ _

theorem lintegral_nuC_le (hd : 1 ≤ d) {r η : ℝ} (hr : 0 < r) (hr8 : r ≤ 1 / 8) (hη0 : 0 < η) (hη : η < r)
    (a : Torus d) {G : Torus d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂(nuC d r η a) ≤ ENNReal.ofReal ((4 / r) ^ d) *
        (∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then G x else 0)) +
      (volume : Measure (Euc d)).toSphere univ * ∫⁻ x, G x ∂(chC d η a) := by
  have hGa : Measurable fun y : Torus d => G (y + a) := hG.comp (measurable_add_const a)
  unfold nuC nuT
  rw [lintegral_map hG (measurable_add_const a), lintegral_add_measure, lintegral_smul_measure,
    lintegral_ballT hGa, lintegral_sphT hGa]
  simp only [smul_eq_mul]
  refine add_le_add ?_ ?_
  · -- the ball part
    refine mul_le_mul' le_rfl ?_
    set f : Torus d → ℝ≥0∞ := fun z => if KernelGrad.tdist z 0 < r then G (z + a) else 0 with hf
    have hfm : Measurable f :=
      Measurable.ite (measurableSet_lt EnergyAux.measurable_tdist_zero measurable_const) hGa measurable_const
    have h1 : ∫⁻ z, f z = ∫⁻ w in Metric.ball (0 : Euc d) r, f (Torus.mk w) :=
      lintegral_torus_ball (by linarith) f (fun z hz => by simp only [hf]; rw [if_neg (not_lt.mpr hz)])
    have h2 : ∫⁻ w in Metric.closedBall (0 : Euc d) η, G (Torus.mk w + a) ≤
        ∫⁻ w in Metric.ball (0 : Euc d) r, G (Torus.mk w + a) :=
      lintegral_mono_set (Metric.closedBall_subset_ball hη)
    have h3 : ∫⁻ w in Metric.ball (0 : Euc d) r, G (Torus.mk w + a) =
        ∫⁻ w in Metric.ball (0 : Euc d) r, f (Torus.mk w) := by
      refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w hw => ?_
      have hw' : ‖w‖ < r := by simpa using hw
      have hy : ∀ i, |w i| ≤ 1 / 2 := fun i => by
        have h1 := PiLp.norm_apply_le w i
        have := (le_of_eq (by simp [Real.norm_eq_abs] : |w i| = ‖w i‖)).trans h1
        linarith
      simp only [hf]
      rw [KernelGrad.tdist_mk hy, if_pos hw']
    have h4 : ∫⁻ z, f z = ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then G x else 0) := by
      have := lintegral_add_right_eq_self (μ := (volume : Measure (Torus d))) (fun x : Torus d => if KernelGrad.tdist x a < r then G x else 0) a
      rw [← this]
      refine lintegral_congr fun z => ?_
      simp only [hf, EnergyAux.tdist_def (z + a) a, add_sub_cancel_right]
    calc ∫⁻ w in Metric.closedBall (0 : Euc d) η, G (Torus.mk w + a) ≤
          ∫⁻ w in Metric.ball (0 : Euc d) r, G (Torus.mk w + a) := h2
      _ = ∫⁻ z, f z := by rw [h3, h1]
      _ = _ := h4
  · -- the sphere part
    have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
    have hS0 : (volume : Measure (Euc d)).toSphere univ ≠ 0 := fun h =>
      Measure.toSphere_ne_zero _ (Measure.measure_univ_eq_zero.mp h)
    have hSt : (volume : Measure (Euc d)).toSphere univ ≠ ⊤ := measure_ne_top _ _
    rw [lintegral_chC G hG η a, ← mul_assoc, ENNReal.mul_inv_cancel hS0 hSt, one_mul]

theorem fieldT_enorm_le (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d)
    {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (hv : IsLipschitzVF L v) {F : Torus d → Euc d}
    (hF : Measurable F) :
    ENNReal.ofReal |∫ x, inner ℝ (v a - v x) (F x) ∂(chS d l η a)| ≤
      ENNReal.ofReal (L * η) * ∫⁻ x, ENNReal.ofReal ‖F x‖ ∂(chS d l η a) := by
  rw [← Real.norm_eq_abs, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsupp := chS_supp hd hl hη hη2 a
  refine lintegral_mono_ae ?_
  filter_upwards [hsupp] with x hx
  rw [← ENNReal.ofReal_mul (mul_nonneg hL hη.le), ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (norm_inner_le_norm _ _).trans ?_
  have h1 := hv a x
  have h2 : ‖v a - v x‖ ≤ L * η := by
    have : KernelGrad.tdist a x ≤ η := by rw [tdist_symm']; exact hx
    exact h1.trans (mul_le_mul_of_nonneg_left this hL)
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

instance sFinite_nuT (d : ℕ) (r η : ℝ) : SFinite (nuT d r η) := by
  unfold nuT
  infer_instance

instance sFinite_nuC (d : ℕ) (r η : ℝ) (a : Torus d) : SFinite (nuC d r η a) := by
  unfold nuC
  infer_instance

/-- measurable surrogate of `cfl` (equal to it for `l > 0`) -/
def cflm (d : ℕ) (l ρ : ℝ) : ℝ := SmearAux.kappa d - l * ∫ s in Ioc (0 : ℝ) ρ, s ^ (d - 1) * yukawa d l s

theorem cfl_eq_cflm (hd : 1 ≤ d) {l ρ : ℝ} (hl : 0 < l) (hρ : 0 < ρ) : cfl d l ρ = cflm d l ρ := by
  rw [cfl_eq_kappa hd hl hρ]; rfl

theorem measurable_cflm_l (d : ℕ) (ρ : ℝ) : Measurable fun l : ℝ => cflm d l ρ := by
  unfold cflm
  refine measurable_const.sub (measurable_id.mul ?_)
  have h : Measurable fun q : ℝ × ℝ => q.2 ^ (d - 1) * yukawa d q.1 q.2 :=
    (measurable_snd.pow_const _).mul ((measurable_yukawa_uncurry d).comp (measurable_fst.prodMk measurable_snd))
  exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) ρ))).measurable

/-- the `l`-integrated weighted field -/
def Phi (d : ℕ) (s r : ℝ) (F : ℝ → Torus d → Euc d) (x : Torus d) : ℝ≥0∞ :=
  ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
    ENNReal.ofReal ‖F l x‖

theorem measurable_Phi (d : ℕ) (s r : ℝ) {F : ℝ → Torus d → Euc d}
    (hF : Measurable fun p : ℝ × Torus d => F p.1 p.2) : Measurable (Phi d s r F) := by
  unfold Phi
  have h : Measurable fun p : ℝ × Torus d => ENNReal.ofReal (p.1 ^ (-bexp d s)) *
      ENNReal.ofReal (cflm d p.1 (r / 4)) * ENNReal.ofReal ‖F p.1 p.2‖ :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_cflm_l d (r / 4)).comp measurable_fst))).mul
      (ENNReal.measurable_ofReal.comp hF.norm)
  exact h.lintegral_prod_left'

/-- the measurable majorant of the weighted field term of the slice `l` -/
def Tmaj (d : ℕ) (s r η L : ℝ) (a : Torus d) (F : ℝ → Torus d → Euc d) (l : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (L * η) * ∫⁻ x, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
    ENNReal.ofReal ‖F l x‖ ∂(nuC d r η a)

theorem measurable_Tmaj (d : ℕ) (s r η L : ℝ) (a : Torus d) {F : ℝ → Torus d → Euc d}
    (hF : Measurable fun p : ℝ × Torus d => F p.1 p.2) : Measurable (Tmaj d s r η L a F) := by
  unfold Tmaj
  have hK : Measurable (Function.uncurry fun (l : ℝ) (x : Torus d) => ENNReal.ofReal (l ^ (-bexp d s)) *
      ENNReal.ofReal (cflm d l (r / 4)) * ENNReal.ofReal ‖F l x‖) :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_cflm_l d (r / 4)).comp measurable_fst))).mul
      (ENNReal.measurable_ofReal.comp hF.norm)
  exact (hK.lintegral_prod_right' (ν := nuC d r η a)).const_mul _

theorem T_pointwise (hd : 1 ≤ d) (s : ℝ) {r η L : ℝ} (hr : 0 < r) (hrη : r / 2 ≤ η)
    (hηr : η < r) (hη2 : η < 1 / 2) (hL : 0 ≤ L) {v : Torus d → Euc d} (hv : IsLipschitzVF L v) (a : Torus d)
    {F : ℝ → Torus d → Euc d} (hFl : ∀ l : ℝ, Measurable (F l)) {l : ℝ} (hl' : 0 < l) :
    ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal |∫ x, inner ℝ (v a - v x) (F l x) ∂(chS d l η a)| ≤ Tmaj d s r η L a F l := by
  have hη0 : 0 < η := by linarith
  have h1 := fieldT_enorm_le hd hl' hη0 hη2 a hL hv (hFl l)
  have h2 := lintegral_chS_le hd hl' hr hrη a (fun x => ENNReal.ofReal ‖F l x‖)
  unfold Tmaj
  rw [← cfl_eq_cflm hd hl' (by positivity)]
  calc ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal |∫ x, inner ℝ (v a - v x) (F l x) ∂(chS d l η a)|
      ≤ ENNReal.ofReal (l ^ (-bexp d s)) * (ENNReal.ofReal (L * η) * (ENNReal.ofReal (cfl d l (r / 4)) *
          ∫⁻ x, ENNReal.ofReal ‖F l x‖ ∂(nuC d r η a))) :=
        mul_le_mul' le_rfl (h1.trans (mul_le_mul' le_rfl h2))
    _ = ENNReal.ofReal (L * η) * ∫⁻ x, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cfl d l (r / 4)) *
          ENNReal.ofReal ‖F l x‖ ∂(nuC d r η a) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
        ring

theorem T_l_bound (hd : 1 ≤ d) (s : ℝ) {r η L : ℝ} (hr : 0 < r) (hr8 : r ≤ 1 / 8) (hrη : r / 2 ≤ η)
    (hηr : η < r) {a : Torus d}
    {F : ℝ → Torus d → Euc d} (hF : Measurable fun p : ℝ × Torus d => F p.1 p.2)
    (hpick : (∫⁻ x, Phi d s r F x ∂(chC d η a)) *
        ((volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal ((r / 2) ^ d)) ≤
      ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then Phi d s r F x else 0)) :
    ∫⁻ l in Ioi (0 : ℝ), Tmaj d s r η L a F l ≤
      ENNReal.ofReal (L * η) * (ENNReal.ofReal (2 * (4 / r) ^ d) *
        ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then Phi d s r F x else 0)) := by
  have hη0 : 0 < η := by linarith
  have hΦm := measurable_Phi d s r hF
  unfold Tmaj
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul' le_rfl ?_
  have hK : Measurable (Function.uncurry fun (l : ℝ) (x : Torus d) => ENNReal.ofReal (l ^ (-bexp d s)) *
      ENNReal.ofReal (cflm d l (r / 4)) * ENNReal.ofReal ‖F l x‖) :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_cflm_l d (r / 4)).comp measurable_fst))).mul
      (ENNReal.measurable_ofReal.comp hF.norm)
  have hswap : ∫⁻ l in Ioi (0 : ℝ), ∫⁻ x, ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
      ENNReal.ofReal ‖F l x‖ ∂(nuC d r η a) = ∫⁻ x, Phi d s r F x ∂(nuC d r η a) := by
    unfold Phi
    exact lintegral_lintegral_swap hK.aemeasurable
  rw [hswap]
  refine (lintegral_nuC_le hd hr hr8 hη0 hηr a hΦm).trans ?_
  -- the sphere part via the pick
  have hS0 : (volume : Measure (Euc d)).toSphere univ ≠ 0 := by
    have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
    exact fun h => Measure.toSphere_ne_zero _ (Measure.measure_univ_eq_zero.mp h)
  have hSt : (volume : Measure (Euc d)).toSphere univ ≠ ⊤ := measure_ne_top _ _
  have hann : ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then Phi d s r F x else 0) ≤
      ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then Phi d s r F x else 0) := by
    refine lintegral_mono fun x => ?_
    by_cases h : r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r
    · rw [if_pos h, if_pos h.2]
    · rw [if_neg h]; exact bot_le
  have hc : ENNReal.ofReal ((2 / r) ^ d) * ENNReal.ofReal ((r / 2) ^ d) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : (2 / r) ^ d * (r / 2) ^ d = 1 := by
      rw [← mul_pow, show 2 / r * (r / 2) = 1 by field_simp, one_pow]
    rw [this, ENNReal.ofReal_one]
  have hsph : (volume : Measure (Euc d)).toSphere univ * ∫⁻ x, Phi d s r F x ∂(chC d η a) ≤
      ENNReal.ofReal ((2 / r) ^ d) * ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then Phi d s r F x else 0) := by
    calc (volume : Measure (Euc d)).toSphere univ * ∫⁻ x, Phi d s r F x ∂(chC d η a)
        = ENNReal.ofReal ((2 / r) ^ d) * ((∫⁻ x, Phi d s r F x ∂(chC d η a)) *
            ((volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal ((r / 2) ^ d))) := by
          have : ENNReal.ofReal ((2 / r) ^ d) * ENNReal.ofReal ((r / 2) ^ d) = 1 := hc
          calc (volume : Measure (Euc d)).toSphere univ * ∫⁻ x, Phi d s r F x ∂(chC d η a)
              = (volume : Measure (Euc d)).toSphere univ * (∫⁻ x, Phi d s r F x ∂(chC d η a)) *
                  (ENNReal.ofReal ((2 / r) ^ d) * ENNReal.ofReal ((r / 2) ^ d)) := by rw [this, mul_one]
            _ = _ := by ring
      _ ≤ ENNReal.ofReal ((2 / r) ^ d) * ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then Phi d s r F x else 0) :=
          mul_le_mul' le_rfl hpick
      _ ≤ _ := mul_le_mul' le_rfl hann
  refine (add_le_add le_rfl hsph).trans ?_
  rw [← add_mul]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine mul_le_mul' ?_ le_rfl
  refine ENNReal.ofReal_le_ofReal ?_
  have : (2 / r) ^ d ≤ (4 / r) ^ d := pow_le_pow_left₀ (by positivity) (by gcongr; norm_num) d
  linarith

/-- Young's inequality for the ball integral of the `l`-integrated field -/
theorem Phi_B_le (hd : 1 ≤ d) (s : ℝ) {r κ : ℝ} (hr : 0 < r) (hr8 : r ≤ 1 / 8) (hκ : 0 < κ) (a : Torus d)
    {F : ℝ → Torus d → Euc d} (hF : Measurable fun p : ℝ × Torus d => F p.1 p.2) :
    ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then Phi d s r F x else 0) ≤
      ENNReal.ofReal (κ / 2) * (ENNReal.ofReal (r ^ d) * (volume : Measure (Euc d)) (Metric.ball 0 1)) *
          (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4))) +
        ENNReal.ofReal (1 / (2 * κ)) *
          ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
            (∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0)) := by
  have hBm : MeasurableSet {x : Torus d | KernelGrad.tdist x a < r} := by
    have : Measurable fun x : Torus d => KernelGrad.tdist x a := by
      have h := EnergyAux.measurable_tdist_zero (d := d)
      have e1 : (fun x : Torus d => KernelGrad.tdist x a) = fun x => KernelGrad.tdist (x - a) 0 := by
        funext x; exact EnergyAux.tdist_def x a
      rw [e1]; exact h.comp (measurable_id.sub_const _)
    exact measurableSet_lt this measurable_const
  have hFx : Measurable fun p : ℝ × Torus d => ‖F p.1 p.2‖ := hF.norm
  set K : ℝ → Torus d → ℝ≥0∞ := fun l x => ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
      (if KernelGrad.tdist x a < r then ENNReal.ofReal ‖F l x‖ else 0) with hK
  have hKm : Measurable (Function.uncurry K) := by
    refine ((ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_cflm_l d (r / 4)).comp measurable_fst))).mul ?_
    refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp hFx) measurable_const
    exact (measurableSet_lt (by
      have h := EnergyAux.measurable_tdist_zero (d := d)
      have e1 : (fun x : Torus d => KernelGrad.tdist x a) = fun x => KernelGrad.tdist (x - a) 0 := by
        funext x; exact EnergyAux.tdist_def x a
      have : Measurable fun x : Torus d => KernelGrad.tdist x a := by rw [e1]; exact h.comp (measurable_id.sub_const _)
      exact this.comp measurable_snd) measurable_const)
  have h1 : ∀ x : Torus d, (if KernelGrad.tdist x a < r then Phi d s r F x else 0) =
      ∫⁻ l in Ioi (0 : ℝ), K l x := by
    intro x
    by_cases hx : KernelGrad.tdist x a < r
    · simp only [if_pos hx, hK, Phi]
    · simp [if_neg hx, hK]
  simp_rw [h1]
  rw [lintegral_lintegral_swap (f := fun (x : Torus d) (l : ℝ) => K l x) (hKm.comp measurable_swap).aemeasurable]
  have hQm : Measurable fun x : Torus d => if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0 :=
    Measurable.ite hBm measurable_const measurable_const
  have hba := ball_ratio hd hr (by linarith) a
  have h2 : ∀ l : ℝ, ∫⁻ x : Torus d, K l x = ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
      ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal ‖F l x‖ else 0) := fun l =>
    lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  simp_rw [h2]
  have hFl : ∀ l : ℝ, Measurable (F l) := fun l => hF.comp (measurable_const.prodMk measurable_id)
  have h3 : ∀ l : ℝ, ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal ‖F l x‖ else 0) ≤
      ENNReal.ofReal (κ / 2) * (ENNReal.ofReal (r ^ d) * (volume : Measure (Euc d)) (Metric.ball 0 1)) +
        ENNReal.ofReal (1 / (2 * κ)) *
          ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0) := by
    intro l
    have hpt : ∀ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal ‖F l x‖ else 0) ≤
        ENNReal.ofReal (κ / 2) * (if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0) +
          ENNReal.ofReal (1 / (2 * κ)) * (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0) := by
      intro x
      by_cases hx : KernelGrad.tdist x a < r
      · simp only [if_pos hx]
        have hy : ‖F l x‖ ≤ κ / 2 + 1 / (2 * κ) * ‖F l x‖ ^ 2 := by
          have : 0 ≤ (‖F l x‖ - κ) ^ 2 := sq_nonneg _
          have h2κ : 0 < 2 * κ := by positivity
          rw [show κ / 2 + 1 / (2 * κ) * ‖F l x‖ ^ 2 = (κ ^ 2 + ‖F l x‖ ^ 2) / (2 * κ) by field_simp]
          rw [le_div_iff₀ h2κ]; nlinarith
        calc ENNReal.ofReal ‖F l x‖ ≤ ENNReal.ofReal (κ / 2 + 1 / (2 * κ) * ‖F l x‖ ^ 2) := ENNReal.ofReal_le_ofReal hy
          _ = ENNReal.ofReal (κ / 2) * 1 + ENNReal.ofReal (1 / (2 * κ)) * ENNReal.ofReal (‖F l x‖ ^ 2) := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity), mul_one]
      · simp [if_neg hx]
    calc ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal ‖F l x‖ else 0)
        ≤ ∫⁻ x : Torus d, (ENNReal.ofReal (κ / 2) * (if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0) +
            ENNReal.ofReal (1 / (2 * κ)) * (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0)) :=
          lintegral_mono hpt
      _ = _ := by
          rw [lintegral_add_left (hQm.const_mul _), lintegral_const_mul _ hQm, hba,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hcm : Measurable fun l : ℝ => ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_cflm_l d (r / 4)))
  have hP : ENNReal.ofReal (κ / 2) * (ENNReal.ofReal (r ^ d) * (volume : Measure (Euc d)) (Metric.ball 0 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
  calc ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
        ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal ‖F l x‖ else 0)
      ≤ ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
          (ENNReal.ofReal (κ / 2) * (ENNReal.ofReal (r ^ d) * (volume : Measure (Euc d)) (Metric.ball 0 1)) +
            ENNReal.ofReal (1 / (2 * κ)) *
              ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0)) :=
        lintegral_mono fun l => mul_le_mul' le_rfl (h3 l)
    _ = ∫⁻ l in Ioi (0 : ℝ), (ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
          (ENNReal.ofReal (κ / 2) * (ENNReal.ofReal (r ^ d) * (volume : Measure (Euc d)) (Metric.ball 0 1))) +
        ENNReal.ofReal (1 / (2 * κ)) * (ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
          ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0))) := by
        refine lintegral_congr fun l => ?_
        ring
    _ = _ := by
        rw [lintegral_add_left (hcm.mul_const _), lintegral_mul_const' _ _ hP,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring

/-! ### Bookkeeping of the powers of `r` -/

theorem rpow_bookkeeping {r : ℝ} (hr : 0 < r) (s : ℝ) :
    r * (r ^ (1 - (d : ℝ)) * r ^ ((d : ℝ) - 2 - s)) = r ^ (-s) := by
  calc r * (r ^ (1 - (d : ℝ)) * r ^ ((d : ℝ) - 2 - s)) = r ^ (1 : ℝ) * (r ^ (1 - (d : ℝ)) * r ^ ((d : ℝ) - 2 - s)) := by
        rw [Real.rpow_one]
    _ = r ^ ((1 : ℝ) + ((1 - (d : ℝ)) + ((d : ℝ) - 2 - s))) := by
        rw [← Real.rpow_add hr, ← Real.rpow_add hr]
    _ = r ^ (-s) := by congr 1; ring

theorem four_bookkeeping (s : ℝ) :
    (4 : ℝ) ^ d / (4 : ℝ) ^ ((d : ℝ) - 2 - s) = (4 : ℝ) ^ (2 + s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)]
  congr 1; ring

theorem T_alg_A {s r η κh ω Cp L N : ℝ} (hN : 0 < N) (hr : 0 < r) (hηr : η ≤ r) (hη : 0 ≤ η)
    (hκh : 0 < κh) (hL : 0 ≤ L) (hω : 0 ≤ ω) (hCp : 0 ≤ Cp) :
    L * η * (2 * (4 / r) ^ d) * ((κh * r ^ (1 - (d : ℝ)) / N / 2) * (r ^ d * ω) *
        (Cp * (r / 4) ^ ((d : ℝ) - 2 - s))) ≤
      L * ((4 ^ (2 + s) * ω * Cp) * κh * r ^ (-s) / N) := by
  have h1 : (4 / r) ^ d * r ^ d = (4 : ℝ) ^ d := by
    rw [← mul_pow]; congr 1; field_simp
  have he : (r / 4) ^ ((d : ℝ) - 2 - s) = r ^ ((d : ℝ) - 2 - s) / 4 ^ ((d : ℝ) - 2 - s) :=
    Real.div_rpow hr.le (by norm_num) _
  have h2 := rpow_bookkeeping (d := d) hr s
  have h4 := four_bookkeeping (d := d) s
  have hP : 0 ≤ r ^ (1 - (d : ℝ)) * r ^ ((d : ℝ) - 2 - s) :=
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _)
  have h4p : (0 : ℝ) < (4 : ℝ) ^ ((d : ℝ) - 2 - s) := Real.rpow_pos_of_pos (by norm_num) _
  have hlhs : L * η * (2 * (4 / r) ^ d) * ((κh * r ^ (1 - (d : ℝ)) / N / 2) * (r ^ d * ω) *
        (Cp * (r / 4) ^ ((d : ℝ) - 2 - s))) =
      (L * κh * ω * Cp / N) * (η * ((4 / r) ^ d * r ^ d)) *
        (r ^ (1 - (d : ℝ)) * (r ^ ((d : ℝ) - 2 - s) / 4 ^ ((d : ℝ) - 2 - s))) := by
    rw [he]; ring
  rw [hlhs, h1]
  have hK : 0 ≤ L * κh * ω * Cp / N := by positivity
  have e1 : (L * κh * ω * Cp / N) * (η * (4 : ℝ) ^ d) *
        (r ^ (1 - (d : ℝ)) * (r ^ ((d : ℝ) - 2 - s) / 4 ^ ((d : ℝ) - 2 - s))) =
      (L * κh * ω * Cp / N) * (4 : ℝ) ^ (2 + s) * (η * (r ^ (1 - (d : ℝ)) * r ^ ((d : ℝ) - 2 - s))) := by
    rw [← h4]; field_simp
  have e2 : L * ((4 ^ (2 + s) * ω * Cp) * κh * r ^ (-s) / N) =
      (L * κh * ω * Cp / N) * (4 : ℝ) ^ (2 + s) * (r * (r ^ (1 - (d : ℝ)) * r ^ ((d : ℝ) - 2 - s))) := by
    rw [h2]; ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right hηr hP

end HRS.Commutator.Stj
