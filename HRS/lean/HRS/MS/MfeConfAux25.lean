import HRS.MS.MfeConfAux24

/-!
# S.B.1, packet F3 (part 6): regularity in `x` and in `t` of `G_r = k * ρ_r` and of `c_r`

For an admissible kernel `k` (`Sb1KerU`) and a trajectory `H : Sb1Tr3`:

* `sb1_hasDerivAt_G`: `∂_r G_r(x) = Ġ_r(x) := ∫ A(ρ_r)(y) k(x-y) dy` for `0 < r < T`;
* `sb1_Gd_bound`: `|Ġ_r(x)| ≤ C_Gd (1+|x|)`;
* `sb1_hasDerivAt_c`: `∂_r c_r = ∫ A(ρ_r) G_r + ∫ ρ_r Ġ_r` for `0 < r < T`.

For a regular kernel (`Sb1KerR`: `C²`, even, bounded gradient): `sb1_hasFDerivAt_G`: `∇G(x) = ∫ ρ(y) ∇k(x-y) dy`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- regular kernels: `C²`, even, bounded gradient -/
structure Sb1KerR (d : ℕ) (k : Euc d → ℝ) (Lg : ℝ) : Prop where
  c2 : ContDiff ℝ 2 k
  even : ∀ z, k (-z) = k z
  gbd : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg

theorem sb1_fderiv_odd {k : Euc d → ℝ} (hk : Differentiable ℝ k) (hev : ∀ z, k (-z) = k z) (z v : Euc d) :
    fderiv ℝ k (-z) v = -(fderiv ℝ k z v) := by
  have h1 : HasFDerivAt (fun z => k (-z)) ((fderiv ℝ k (-z)).comp (-ContinuousLinearMap.id ℝ (Euc d))) z :=
    (hk (-z)).hasFDerivAt.comp z (hasFDerivAt_id z).neg
  have h2 : (fun z => k (-z)) = k := funext hev
  rw [h2] at h1
  have h3 := h1.fderiv
  have := congrArg (fun L => L v) h3
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg] at this
  linarith

namespace Sb1KerR

variable {k : Euc d → ℝ} {Lg : ℝ}

theorem diff (h : Sb1KerR d k Lg) : Differentiable ℝ k := h.c2.differentiable (by norm_num)

theorem cont_fderiv (h : Sb1KerR d k Lg) : Continuous (fderiv ℝ k) := h.c2.continuous_fderiv (by norm_num)

theorem Lg_nonneg (h : Sb1KerR d k Lg) : 0 ≤ Lg := (norm_nonneg _).trans (h.gbd 0)

end Sb1KerR

variable {s : ℝ} {k : Euc d → ℝ} {Lg : ℝ} {ρ : Euc d → ℝ} {Cρ M1 : ℝ}

theorem sb1_dG_int (hR : Sb1KerR d k Lg) (R : Sb1Rho ρ Cρ M1) (x : Euc d) :
    Integrable (fun y => ρ y • fderiv ℝ k (x - y)) := by
  refine (R.integrable.const_mul Lg).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (R.dens.measurable.smul (hR.cont_fderiv.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (R.dens.nonneg y)]
    have := mul_le_mul_of_nonneg_left (hR.gbd (x - y)) (R.dens.nonneg y)
    linarith [mul_comm Lg (ρ y)]

theorem sb1_hasFDerivAt_G (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (hR : Sb1KerR d k Lg)
    (R : Sb1Rho ρ Cρ M1) (x : Euc d) :
    HasFDerivAt (sb1G k ρ) (∫ y, ρ y • fderiv ℝ k (x - y)) x := by
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (F := fun x y => ρ y * k (x - y)) (F' := fun x y => ρ y • fderiv ℝ k (x - y)) (x₀ := x)
    (s := Set.univ) (bound := fun y => Lg * ρ y) Filter.univ_mem ?_ (sb1_rhoG_int hd hs0 hsd hk R x)
    (sb1_dG_int hR R x).aestronglyMeasurable ?_ (R.integrable.const_mul Lg) ?_
  · exact this
  · refine Eventually.of_forall fun x' => ?_
    exact (R.dens.measurable.mul (hk.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · refine Eventually.of_forall fun y x' _ => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (R.dens.nonneg y)]
    have := mul_le_mul_of_nonneg_left (hR.gbd (x' - y)) (R.dens.nonneg y)
    linarith [mul_comm Lg (ρ y)]
  · refine Eventually.of_forall fun y x' _ => ?_
    have h1 : HasFDerivAt (fun x' => k (x' - y)) (fderiv ℝ k (x' - y)) x' :=
      (hR.diff (x' - y)).hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const y)
    exact (h1.const_mul (ρ y)).congr_fderiv (by ext v; simp)

theorem sb1_fderiv_G_apply (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (hR : Sb1KerR d k Lg)
    (R : Sb1Rho ρ Cρ M1) (x v : Euc d) :
    fderiv ℝ (sb1G k ρ) x v = ∫ y, ρ y * fderiv ℝ k (x - y) v := by
  rw [(sb1_hasFDerivAt_G hd hs0 hsd hk hR R x).fderiv, ContinuousLinearMap.integral_apply (sb1_dG_int hR R x)]
  simp


/-! ### Time regularity -/

section Time

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ}

theorem Sb1Tr3.A_cont (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Continuous (sb1A D (ρ r)) :=
  (sb1_A_joint_cont H.tr).comp
    (continuous_const.prodMk continuous_id : Continuous fun y : Euc d => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), y))

/-- `C_A = d C_dJ` -/
def sb1CA (D : Whole.WholeDyn d) (B C C3 : ℝ) : ℝ := (d : ℝ) * sb1CdJ D B C C3

theorem Sb1Tr3.CA_nonneg (H : Sb1Tr3 D T C B C3 ρ) : 0 ≤ sb1CA D B C C3 :=
  mul_nonneg (Nat.cast_nonneg d) H.CdJ_nonneg

theorem Sb1Tr3.A_le (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (y : Euc d) :
    |sb1A D (ρ r) y| ≤ sb1CA D B C C3 * sb1w ((d : ℝ) + 2) y := H.A_bound hr y

theorem sb1_psiA (hd : 1 ≤ d) {a : ℝ} :
    Integrable (fun y : Euc d => a * sb1w ((d : ℝ) + 2) y) ∧
      Integrable (fun y : Euc d => a * sb1w ((d : ℝ) + 2) y * ‖y‖) := by
  refine ⟨(sb1w_int hd (p := (d : ℝ) + 2) (by linarith)).const_mul a, ?_⟩
  have := (sb1w_mom hd).const_mul a
  simpa [mul_assoc] using this

/-- `Ġ_r(x) = ∫ A(ρ_r)(y) k(x-y) dy` -/
def sb1Gd (D : Whole.WholeDyn d) (ρ : ℝ → Euc d → ℝ) (k : Euc d → ℝ) (r : ℝ) (x : Euc d) : ℝ :=
  ∫ y, sb1A D (ρ r) y * k (x - y)

/-- the constant bounding `Ġ` -/
def sb1CGd (d : ℕ) (s a : ℝ) : ℝ :=
  (∫ y : Euc d, a * sb1w ((d : ℝ) + 2) y) + (∫ y : Euc d, a * sb1w ((d : ℝ) + 2) y * ‖y‖) +
    2 * (a * sb1Isig d (sb1sig s) + ∫ y : Euc d, a * sb1w ((d : ℝ) + 2) y)

theorem sb1CGd_nonneg (s : ℝ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ sb1CGd d s a := by
  unfold sb1CGd
  have h1 : 0 ≤ ∫ y : Euc d, a * sb1w ((d : ℝ) + 2) y :=
    integral_nonneg fun y => mul_nonneg ha (sb1w_pos _ _).le
  have h2 : 0 ≤ ∫ y : Euc d, a * sb1w ((d : ℝ) + 2) y * ‖y‖ :=
    integral_nonneg fun y => mul_nonneg (mul_nonneg ha (sb1w_pos _ _).le) (norm_nonneg _)
  have h3 := sb1Isig_nonneg (d := d) (sb1sig s)
  positivity

theorem sb1_Gd_facts (H : Sb1Tr3 D T C B C3 ρ) {k : Euc d → ℝ} (hk : Sb1KerU d D.s k)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    Integrable (fun y => sb1A D (ρ r) y * k (x - y)) ∧
      |sb1Gd D ρ k r x| ≤ sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖x‖) := by
  have hd := H.tr.hd
  have hCA := H.CA_nonneg
  obtain ⟨hψi, hψ1⟩ := sb1_psiA (d := d) hd (a := sb1CA D B C C3)
  obtain ⟨hI, hIb⟩ := sb1_Om_conv hd H.tr.hs0 H.tr.hsd (ψ := fun y => sb1CA D B C C3 * sb1w ((d : ℝ) + 2) y)
    (fun y => mul_nonneg hCA (sb1w_pos _ _).le) (measurable_const.mul (sb1w_meas _)) hψi
    (Cψ := sb1CA D B C C3) (fun y => mul_le_of_le_one_right hCA (sb1w_le_one (by positivity) y)) hψ1 x
  have hint : Integrable (fun y => sb1A D (ρ r) y * k (x - y)) := by
    refine hI.mono' ((H.A_cont hr).measurable.mul (hk.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable ?_
    filter_upwards [sb1_ae_ne hd x] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (H.A_le hr y) (sb1_k_abs_le H.tr.hs0 hk (sub_ne_zero.2 (Ne.symm hy))) (abs_nonneg _)
      (mul_nonneg hCA (sb1w_pos _ _).le)
  refine ⟨hint, ?_⟩
  have h := norm_integral_le_of_norm_le hI (f := fun y => sb1A D (ρ r) y * k (x - y)) (by
    filter_upwards [sb1_ae_ne hd x] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (H.A_le hr y) (sb1_k_abs_le H.tr.hs0 hk (sub_ne_zero.2 (Ne.symm hy))) (abs_nonneg _)
      (mul_nonneg hCA (sb1w_pos _ _).le))
  rw [Real.norm_eq_abs] at h
  unfold sb1Gd sb1CGd
  have hl := sb1_log_le_norm x
  have hl0 := sb1_log_nonneg x
  have hn := norm_nonneg x
  have h1 : 0 ≤ ∫ y : Euc d, sb1CA D B C C3 * sb1w ((d : ℝ) + 2) y :=
    integral_nonneg fun y => mul_nonneg hCA (sb1w_pos _ _).le
  have h2 : 0 ≤ ∫ y : Euc d, sb1CA D B C C3 * sb1w ((d : ℝ) + 2) y * ‖y‖ :=
    integral_nonneg fun y => mul_nonneg (mul_nonneg hCA (sb1w_pos _ _).le) (norm_nonneg _)
  have h3 := sb1Isig_nonneg (d := d) (sb1sig D.s)
  nlinarith [mul_le_mul_of_nonneg_right hl h1, mul_nonneg h3 hCA, mul_nonneg h1 hn, mul_nonneg h2 hn,
    mul_nonneg (mul_nonneg h3 hCA) hn]

theorem sb1_hasDerivAt_G (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) {k : Euc d → ℝ} (hk : Sb1KerU d D.s k)
    {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) T) (x : Euc d) :
    HasDerivAt (fun r => sb1G k (ρ r) x) (sb1Gd D ρ k r₀ x) r₀ := by
  have hd := H.tr.hd
  have hI : Set.Ioo (0 : ℝ) T ∈ 𝓝 r₀ := Ioo_mem_nhds hr₀.1 hr₀.2
  have hIcc : ∀ r ∈ Set.Ioo (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.le⟩
  have hCA := H.CA_nonneg
  obtain ⟨hψi, hψ1⟩ := sb1_psiA (d := d) hd (a := sb1CA D B C C3)
  obtain ⟨hIn, -⟩ := sb1_Om_conv hd H.tr.hs0 H.tr.hsd (ψ := fun y => sb1CA D B C C3 * sb1w ((d : ℝ) + 2) y)
    (fun y => mul_nonneg hCA (sb1w_pos _ _).le) (measurable_const.mul (sb1w_meas _)) hψi
    (Cψ := sb1CA D B C C3) (fun y => mul_le_of_le_one_right hCA (sb1w_le_one (by positivity) y)) hψ1 x
  have R0 := H.rho hd (hIcc r₀ hr₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun r y => ρ r y * k (x - y)) (F' := fun r y => sb1A D (ρ r) y * k (x - y)) (x₀ := r₀)
    (s := Set.Ioo 0 T) (bound := fun y => sb1CA D B C C3 * sb1w ((d : ℝ) + 2) y * sb1Om D.s (x - y)) hI
    ?_ (sb1_rhoG_int hd H.tr.hs0 H.tr.hsd hk R0 x) ?_ ?_ hIn ?_
  · exact key.2
  · filter_upwards [hI] with r hr
    exact ((H.tr.cont (hIcc r hr)).measurable.mul (hk.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · exact ((H.A_cont (hIcc r₀ hr₀)).measurable.mul (hk.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · filter_upwards [sb1_ae_ne hd x] with y hy r hr
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (H.A_le (hIcc r hr) y) (sb1_k_abs_le H.tr.hs0 hk (sub_ne_zero.2 (Ne.symm hy))) (abs_nonneg _)
      (mul_nonneg hCA (sb1w_pos _ _).le)
  · exact Eventually.of_forall fun y r hr => (sb1_hasDerivAt H.tr hT hr y).mul_const (k (x - y))

theorem sb1_Gd_meas (H : Sb1Tr3 D T C B C3 ρ) {k : Euc d → ℝ} (hk : Sb1KerU d D.s k)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : Measurable (sb1Gd D ρ k r) :=
  sb1_meas_conv (H.A_cont hr).measurable hk.meas

theorem sb1_hasDerivAt_c (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) {k : Euc d → ℝ} (hk : Sb1KerU d D.s k)
    {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => sb1c k (ρ r))
      (∫ x, (sb1A D (ρ r₀) x * sb1G k (ρ r₀) x + ρ r₀ x * sb1Gd D ρ k r₀ x)) r₀ := by
  have hd := H.tr.hd
  have hI : Set.Ioo (0 : ℝ) T ∈ 𝓝 r₀ := Ioo_mem_nhds hr₀.1 hr₀.2
  have hIcc : ∀ r ∈ Set.Ioo (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.le⟩
  have hCA := H.CA_nonneg
  have hC3 := H.C3nn
  have R0 := H.rho hd (hIcc r₀ hr₀)
  set CGc := sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) with hCGc
  have hCGc0 : 0 ≤ CGc := sb1CG_nonneg R0
  set CGd := sb1CGd d D.s (sb1CA D B C C3) with hCGd
  have hCGd0 : 0 ≤ CGd := sb1CGd_nonneg D.s hCA
  have hw1 := sb1w_int hd (p := (d : ℝ) + 1) (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun r x => ρ r x * sb1G k (ρ r) x)
    (F' := fun r x => sb1A D (ρ r) x * sb1G k (ρ r) x + ρ r x * sb1Gd D ρ k r x) (x₀ := r₀)
    (s := Set.Ioo 0 T)
    (bound := fun x => (sb1CA D B C C3 * (1 + CGc) + C3 * CGd) * sb1w ((d : ℝ) + 1) x) hI
    ?_ (sb1_rhoGc_int hd H.tr.hs0 H.tr.hsd hk R0) ?_ ?_ (hw1.const_mul _) ?_
  · exact key.2
  · filter_upwards [hI] with r hr
    have Rr := H.rho hd (hIcc r hr)
    exact ((H.tr.cont (hIcc r hr)).measurable.mul (sb1_G_meas hk Rr)).aestronglyMeasurable
  · exact (((H.A_cont (hIcc r₀ hr₀)).measurable.mul (sb1_G_meas hk R0)).add
      ((H.tr.cont (hIcc r₀ hr₀)).measurable.mul (sb1_Gd_meas H hk (hIcc r₀ hr₀)))).aestronglyMeasurable
  · refine Eventually.of_forall fun x r hr => ?_
    have Rr := H.rho hd (hIcc r hr)
    have hG := sb1_G_abs_le hd H.tr.hs0 H.tr.hsd hk Rr x
    obtain ⟨-, hGd⟩ := sb1_Gd_facts H hk (hIcc r hr) x
    have hA := H.A_le (hIcc r hr) x
    have hρ := H.rho_le (hIcc r hr) x
    have hρ0 := H.pos r (hIcc r hr) x
    have e1 : sb1w ((d : ℝ) + 2) x * (1 + ‖x‖) = sb1w ((d : ℝ) + 1) x := by
      have := sb1w_succ ((d : ℝ) + 1) x
      rwa [show (d : ℝ) + 1 + 1 = (d : ℝ) + 2 by ring] at this
    have e2 := sb1w_32 x
    have hw2 := (sb1w_pos ((d : ℝ) + 2) x).le
    have hw3 := (sb1w_pos ((d : ℝ) + 3) x).le
    have hn := norm_nonneg x
    have hl := sb1_log_le_norm x
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hρ0]
    have b1 : |sb1A D (ρ r) x| * |sb1G k (ρ r) x| ≤ sb1CA D B C C3 * (1 + CGc) * sb1w ((d : ℝ) + 1) x := by
      refine (mul_le_mul hA (hG.trans (by nlinarith [sb1_log_nonneg x] : Real.log (1 + ‖x‖) + sb1CG d D.s C3
          (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) ≤ (1 + CGc) * (1 + ‖x‖))) (abs_nonneg _)
        (mul_nonneg hCA hw2)).trans ?_
      rw [← e1]
      nlinarith [mul_nonneg hCA hw2]
    have b2 : ρ r x * |sb1Gd D ρ k r x| ≤ C3 * CGd * sb1w ((d : ℝ) + 1) x := by
      have := mul_le_mul hρ hGd (abs_nonneg _) (mul_nonneg hC3 hw3)
      refine this.trans ?_
      have : C3 * sb1w ((d : ℝ) + 3) x * (CGd * (1 + ‖x‖)) = C3 * CGd * sb1w ((d : ℝ) + 2) x := by
        rw [← e2]; ring
      rw [this]
      have hw12 : sb1w ((d : ℝ) + 2) x ≤ sb1w ((d : ℝ) + 1) x := by
        rw [← e1]; nlinarith
      exact mul_le_mul_of_nonneg_left hw12 (mul_nonneg hC3 hCGd0)
    nlinarith [b1, b2]
  · exact Eventually.of_forall fun x r hr =>
      (sb1_hasDerivAt H.tr hT hr x).mul (sb1_hasDerivAt_G H hT hk hr x)

end Time

end HRS.MS.MfeConf
