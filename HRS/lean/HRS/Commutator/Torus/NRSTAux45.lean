import HRS.Commutator.Torus.NRSTAux44

/-!
# NRS-T, part 45: the pairing `xpair (2σ) W (v·∇W)` as a finite sum of explicit integrals
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_toEuc_neg_sub (j k : Lattice d) :
    Lattice.toEuc (-j - k) = -Lattice.toEuc j - Lattice.toEuc k := by
  ext i; simp [Lattice.toEuc]

lemma nrstr_toEuc_add3 (k j l : Lattice d) :
    Lattice.toEuc (k + j + l) = Lattice.toEuc k + Lattice.toEuc j + Lattice.toEuc l := by
  ext i; simp [Lattice.toEuc]

/-- On the support of the `k`-th bump, the shifted series collapses to one term. -/
lemma nrstr_sum_l (h : NRST.TPA d) {N : ℝ} (hN : 1 ≤ N) (k j : Lattice d) (ξ : 𝔼)
    (hk : nrstr_a h N k ξ ≠ 0) :
    ∑ l ∈ h.coeff.support, nrstr_a h N l (-ξ - Lattice.toEuc j) =
      nrstr_a h N (-j - k) (-ξ - Lattice.toEuc j) := by
  classical
  have hdis : ∀ l, nrstr_a h N l (-ξ - Lattice.toEuc j) ≠ 0 → l = -j - k := by
    intro l hl
    have h1 := nrstr_a_near hN hk
    have h2 := nrstr_a_near hN hl
    by_contra hne
    have hne' : k + j + l ≠ 0 := by
      intro h0; apply hne
      have : l = -(k + j) := eq_neg_of_add_eq_zero_right h0
      rw [this]; abel
    have h3 := nrstr_one_le_enorm hne'
    have e : Lattice.toEuc (k + j + l) =
        (Lattice.toEuc k - ξ) - (-ξ - Lattice.toEuc j - Lattice.toEuc l) := by
      rw [nrstr_toEuc_add3]; abel
    rw [e] at h3
    have h4 : ‖(Lattice.toEuc k - ξ) - (-ξ - Lattice.toEuc j - Lattice.toEuc l)‖ ≤
        ‖ξ - Lattice.toEuc k‖ + ‖-ξ - Lattice.toEuc j - Lattice.toEuc l‖ := by
      calc _ ≤ ‖Lattice.toEuc k - ξ‖ + ‖-ξ - Lattice.toEuc j - Lattice.toEuc l‖ := norm_sub_le _ _
        _ = _ := by rw [norm_sub_rev (Lattice.toEuc k) ξ]
    have h5 : 1 / (8 * N) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  by_cases hl0 : (-j - k) ∈ h.coeff.support
  · refine Finset.sum_eq_single_of_mem _ hl0 (fun l hl hne => ?_)
    by_contra hz
    exact hne (hdis l hz)
  · have hc : h.coeff (-j - k) = 0 := by simpa using hl0
    have h0 : nrstr_a h N (-j - k) (-ξ - Lattice.toEuc j) = 0 := by simp [nrstr_a, hc]
    rw [h0]
    refine Finset.sum_eq_zero (fun l hl => ?_)
    by_contra hz
    exact hl0 (hdis l hz ▸ hl)

lemma nrstr_a_continuous (h : NRST.TPA d) (N : ℝ) (k : Lattice d) : Continuous (nrstr_a h N k) := by
  unfold nrstr_a
  have : Continuous fun ξ : 𝔼 => nrstr_theta0 (d := d) (N • (ξ - Lattice.toEuc k)) :=
    (nrstr_theta0 (d := d)).continuous.comp (by fun_prop)
  exact continuous_const.mul (continuous_const.mul this)

/-- The weight `ofReal ((2π|ξ|)^{2σ})`. -/
def nrstr_w (σ : ℝ) (ξ : 𝔼) : ℂ := (((2 * Real.pi * ‖ξ‖) ^ (2 * σ) : ℝ) : ℂ)

lemma nrstr_w_continuous {σ : ℝ} (hσ : 0 < σ) : Continuous (nrstr_w (d := d) σ) := by
  unfold nrstr_w
  refine Complex.continuous_ofReal.comp ?_
  exact (Real.continuous_rpow_const (by linarith)).comp (continuous_const.mul continuous_norm)

/-- The `(k,c,j)` term. -/
def nrstr_tm (σ : ℝ) (h : NRST.TPA d) (V : Fin d → NRST.TPA d) (N : ℝ) (k : Lattice d) (c : Fin d)
    (j : Lattice d) (ξ : 𝔼) : ℂ :=
  nrstr_w σ ξ * nrstr_a h N k ξ * ((V c).coeff j *
    ((2 * Real.pi * Complex.I * ((-ξ - Lattice.toEuc j) c : ℝ)) * nrstr_a h N (-j - k) (-ξ - Lattice.toEuc j)))

lemma nrstr_tm_integrable {σ : ℝ} (hσ : 0 < σ) (h : NRST.TPA d) (V : Fin d → NRST.TPA d) {N : ℝ}
    (hN : 1 ≤ N) (k : Lattice d) (c : Fin d) (j : Lattice d) :
    Integrable (nrstr_tm σ h V N k c j) := by
  have hcont : Continuous (nrstr_tm σ h V N k c j) := by
    unfold nrstr_tm
    have h1 : Continuous fun ξ : 𝔼 => nrstr_a h N (-j - k) (-ξ - Lattice.toEuc j) :=
      (nrstr_a_continuous h N (-j - k)).comp (continuous_neg.sub continuous_const)
    have h2 : Continuous fun ξ : 𝔼 => (((-ξ - Lattice.toEuc j) c : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((EuclideanSpace.proj c : 𝔼 →L[ℝ] ℝ).continuous.comp
        (continuous_neg.sub continuous_const))
    refine ((nrstr_w_continuous hσ).mul (nrstr_a_continuous h N k)).mul (continuous_const.mul ?_)
    exact (continuous_const.mul h2).mul h1
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (Lattice.toEuc k) (1 / (8 * N))) (fun x hx => ?_)
  have : nrstr_a h N k x = 0 := by
    by_contra hne
    exact hx (mem_closedBall_iff_norm.2 (nrstr_a_near hN hne).le)
  simp [nrstr_tm, this]

lemma nrstr_pair_integrand {σ : ℝ} (V : Fin d → NRST.TPA d) (hVr : ∀ j x, (NRST.ev (V j) x).im = 0)
    (h : NRST.TPA d) {N : ℝ} (hN : 1 ≤ N) (ξ : 𝔼) :
    nrstr_w σ ξ * 𝓕 (⇑(nrstr_W h N (by linarith))) ξ *
        𝓕 (⇑(HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) (nrstr_W h N (by linarith)))) (-ξ) =
      ∑ k ∈ h.coeff.support, ∑ c, ∑ j ∈ (V c).coeff.support, nrstr_tm σ h V N k c j ξ := by
  classical
  have hN0 : 0 < N := by linarith
  rw [nrstr_FW_eq h hN0, Finset.mul_sum (s := h.coeff.support), Finset.sum_mul (s := h.coeff.support)]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : nrstr_a h N k ξ = 0
  · simp [nrstr_tm, hk]
  · rw [nrstr_fourier_xadv V hVr]
    simp_rw [nrstr_FW_eq h hN0, nrstr_sum_l h hN k _ ξ hk]
    rw [Finset.mul_sum (Finset.univ : Finset (Fin d))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum (V c).coeff.support]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [nrstr_tm]

lemma nrstr_pair_eq {σ : ℝ} (hσ : 0 < σ) (V : Fin d → NRST.TPA d) (hVr : ∀ j x, (NRST.ev (V j) x).im = 0)
    (h : NRST.TPA d) {N : ℝ} (hN : 1 ≤ N) :
    HRS.Commutator.Whole.XNRS.xpair (2 * σ) (nrstr_W h N (by linarith))
        (HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) (nrstr_W h N (by linarith))) =
      ∑ k ∈ h.coeff.support, ∑ c, ∑ j ∈ (V c).coeff.support, ∫ ξ, nrstr_tm σ h V N k c j ξ := by
  unfold HRS.Commutator.Whole.XNRS.xpair
  have e : ∫ ξ : 𝔼, (((2 * Real.pi * ‖ξ‖) ^ (2 * σ) : ℝ) : ℂ) * 𝓕 (⇑(nrstr_W h N (by linarith))) ξ *
      𝓕 (⇑(HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) (nrstr_W h N (by linarith)))) (-ξ) =
      ∫ ξ : 𝔼, ∑ k ∈ h.coeff.support, ∑ c, ∑ j ∈ (V c).coeff.support, nrstr_tm σ h V N k c j ξ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => nrstr_pair_integrand V hVr h hN ξ)
  refine e.trans ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun j _ => nrstr_tm_integrable hσ h V hN k c j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun j _ => nrstr_tm_integrable hσ h V hN k c j]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun j _ => nrstr_tm_integrable hσ h V hN k c j]

end HRS.Commutator.TorusNote
