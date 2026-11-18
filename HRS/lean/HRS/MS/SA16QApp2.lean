import HRS.MS.SA16QApp1
import HRS.MS.SA16QMorrey4
import HRS.MS.SA16StrongSL10
import HRS.MS.SA16StrongDomLp

/-!
# S.A.16 (SA16Q), E6 part 14: the regular density data, weighted `L^R` bounds, convergence

* `sa16q_reg_data`: from `IsRegularDensityW (m+3) Λ μ`: `μ ∈ C^{m+3}`, `‖D^jμ‖ ≤ Λ⁺`, and
  `|∂^r μ(x)| (1+|x|)^{d+3} ≤ 2^{d+3} Λ⁺`;
* `sa16q_unif_CZ`, `sa16q_unif_HLS`: the uniform bounds of `‖ ‖D^κ a‖ ‖D^n u‖ ‖_R` by `‖u‖_{W^{m,p}}`;
* `sa16q_conv_term`: `‖ ‖D^κ(a_n - μ)‖ ‖D^n u‖ ‖_R → 0` for the mollifications `a_n`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Reg
variable {d : ℕ}

lemma sa16q_jb_le (x : Euc d) : 1 + ‖x‖ ≤ 2 * jbracket x := by
  unfold jbracket
  have h : (1 + ‖x‖) / 2 ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  linarith

lemma sa16q_reg_data {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW (m + 3) Λ μ) :
    ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) μ ∧ (∀ j ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ max Λ 0) ∧
      ∀ k ≤ m + 3, ∀ r : Fin k → Fin d, ∀ x, |partialDeriv r μ x| * (1 + ‖x‖) ^ (d + 3) ≤
        2 ^ (d + 3) * max Λ 0 := by
  obtain ⟨hC, hcb, hsum⟩ := hμ
  have hΛ : ENNReal.ofReal (cbNorm (m + 3) μ) + weightedSupE (m + 3) ((d : ℝ) + 3) μ ≤
      ENNReal.ofReal (max Λ 0) := hsum.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hcb' : cbNorm (m + 3) μ ≤ max Λ 0 :=
    (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 (le_self_add.trans hΛ)
  refine ⟨hC, sa16y_cb_bound hcb hcb', fun k hk r x => ?_⟩
  have h1 : ENNReal.ofReal (jbracket x ^ ((d : ℝ) + 3) * |partialDeriv r μ x|) ≤
      weightedSupE (m + 3) ((d : ℝ) + 3) μ := by
    unfold weightedSupE derivSupE
    exact le_iSup_of_le ⟨k, by omega⟩ (le_iSup_of_le r (le_iSup_of_le x le_rfl))
  have h2 : jbracket x ^ ((d : ℝ) + 3) * |partialDeriv r μ x| ≤ max Λ 0 :=
    (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 (h1.trans (le_add_self.trans hΛ))
  have h3 : jbracket x ^ ((d : ℝ) + 3) = jbracket x ^ (d + 3) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [h3] at h2
  have hj : 0 ≤ jbracket x := Real.sqrt_nonneg _
  have h4 : (1 + ‖x‖) ^ (d + 3) ≤ 2 ^ (d + 3) * jbracket x ^ (d + 3) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (sa16q_jb_le x) _
  calc |partialDeriv r μ x| * (1 + ‖x‖) ^ (d + 3)
      ≤ |partialDeriv r μ x| * (2 ^ (d + 3) * jbracket x ^ (d + 3)) := by gcongr
    _ = 2 ^ (d + 3) * (jbracket x ^ (d + 3) * |partialDeriv r μ x|) := by ring
    _ ≤ 2 ^ (d + 3) * max Λ 0 := by gcongr

/-- the weight function lies in every `L^R` -/
lemma sa16q_omega_lp {R : ℝ} (hR : 1 ≤ R) :
    eLpNorm (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) (ENNReal.ofReal R) volume < ⊤ := by
  have hR0 : 0 < R := by linarith
  have hmeas : Measurable (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) :=
    (measurable_const.add measurable_norm).pow_const _
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-(((d + 3 : ℕ) : ℝ) * R))) volume := by
    refine integrable_one_add_norm ?_
    have : (d : ℝ) + 3 ≤ ((d + 3 : ℕ) : ℝ) * R := by
      push_cast
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) + 3) (sub_nonneg.2 hR)]
    simp only [finrank_euclideanSpace_fin]
    linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hR0) ENNReal.ofReal_ne_top hmeas.aestronglyMeasurable,
    ENNReal.toReal_ofReal hR0.le]
  have h1 : ∀ x : Euc d, ‖(1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))‖ₑ ^ R =
      ENNReal.ofReal ((1 + ‖x‖) ^ (-(((d + 3 : ℕ) : ℝ) * R))) := by
    intro x
    have hpos : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    rw [Real.enorm_eq_ofReal hpos, ENNReal.ofReal_rpow_of_nonneg hpos hR0.le,
      ← Real.rpow_mul (by positivity)]
    congr 2; ring
  have h2 : ∫⁻ x : Euc d, ‖(1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))‖ₑ ^ R < ⊤ := by
    simp_rw [h1]; exact hint.lintegral_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) h2.ne

end Reg

section Unif
variable {d : ℕ}

/-- the iterated-derivative norm of a Schwartz function is in every `L^R` -/
lemma sa16q_iter_memLp (u : 𝓢(Euc d, ℝ)) (n : ℕ) {R : ℝ} :
    MemLp (fun x => ‖iteratedFDeriv ℝ n u x‖) (ENNReal.ofReal R) volume := by
  have hS := sa16j_S_memLp (d := d) n R u
  refine hS.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((u.smooth'.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    unfold sa16j_S
    exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j (⇑u) x‖) (fun j _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_self n))

/-- Holder for a product of two real functions -/
lemma sa16q_holder_mul {f g : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) {R ra p : ℝ} (hR : 0 < R) (hra : 0 < ra) (hp : 0 < p)
    (h : 1 / R = 1 / ra + 1 / p) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal R) volume ≤
      eLpNorm f (ENNReal.ofReal ra) volume * eLpNorm g (ENNReal.ofReal p) volume := by
  haveI : (ENNReal.ofReal ra).HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal R) :=
    ⟨by
      rw [← ENNReal.ofReal_inv_of_pos hra, ← ENNReal.ofReal_inv_of_pos hp,
        ← ENNReal.ofReal_inv_of_pos hR, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simpa [one_div] using h.symm⟩
  have := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal ra) (q := ENNReal.ofReal p)
    (r := ENNReal.ofReal R) hf hg (μ := volume)
  have h2 : (fun x => f x * g x) = f • g := rfl
  rw [h2]
  exact this

/-- uniform bound, Calderon-Zygmund exponent `R = p` -/
lemma sa16q_unif_CZ (hd1 : 1 ≤ d) {a : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) {W : ℝ} (hW : 0 ≤ W)
    {κ n m : ℕ} (hκ : ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W) (u : 𝓢(Euc d, ℝ)) (hn : n ≤ m) {p : ℝ} :
    eLpNorm (fun x => ‖iteratedFDeriv ℝ κ a x‖ * ‖iteratedFDeriv ℝ n u x‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (W * (d : ℝ) ^ m) * eLpNorm (wJet m (⇑u)) (ENNReal.ofReal p) volume := by
  have hmeas : AEStronglyMeasurable (fun x => ‖iteratedFDeriv ℝ κ a x‖ * ‖iteratedFDeriv ℝ n u x‖) volume :=
    (((ha.continuous_iteratedFDeriv (m := κ) (by exact_mod_cast le_top)).norm).mul
      ((u.smooth'.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).norm)).aestronglyMeasurable
  refine (eLpNorm_mono_ae_real (g := fun x => W * ‖iteratedFDeriv ℝ n u x‖) hmeas
    (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_mul, norm_norm, norm_norm]
    exact mul_le_mul_of_nonneg_right (hκ x) (norm_nonneg _)
  · have : (fun x => W * ‖iteratedFDeriv ℝ n u x‖) = W • (fun x => ‖iteratedFDeriv ℝ n u x‖) := by
      funext x; simp
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hW, ENNReal.ofReal_mul hW, mul_assoc]
    exact sa16q_mul_le (sa16q_iter_lp u.smooth' hd1 p hn)

/-- uniform bound, Hardy-Littlewood-Sobolev exponent `1/R = 1/ra + 1/p` -/
lemma sa16q_unif_HLS (hd1 : 1 ≤ d) {a : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) {W : ℝ} (hW : 0 ≤ W)
    {κ n m : ℕ} (hκ : ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)))
    (u : 𝓢(Euc d, ℝ)) (hn : n ≤ m) {R ra p : ℝ} (hR : 0 < R) (hra : 0 < ra) (hp : 0 < p)
    (h : 1 / R = 1 / ra + 1 / p) :
    eLpNorm (fun x => ‖iteratedFDeriv ℝ κ a x‖ * ‖iteratedFDeriv ℝ n u x‖) (ENNReal.ofReal R) volume ≤
      ENNReal.ofReal W * eLpNorm (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) (ENNReal.ofReal ra) volume *
        (ENNReal.ofReal ((d : ℝ) ^ m) * eLpNorm (wJet m (⇑u)) (ENNReal.ofReal p) volume) := by
  have hωc : Continuous (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) :=
    (continuous_const.add continuous_norm).rpow_const (fun x => Or.inl (by positivity : (0 : ℝ) < 1 + ‖x‖).ne')
  have hGc : Continuous (fun x => ‖iteratedFDeriv ℝ n u x‖) :=
    (u.smooth'.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).norm
  have hmeas : AEStronglyMeasurable (fun x => ‖iteratedFDeriv ℝ κ a x‖ * ‖iteratedFDeriv ℝ n u x‖) volume :=
    (((ha.continuous_iteratedFDeriv (m := κ) (by exact_mod_cast le_top)).norm).mul hGc).aestronglyMeasurable
  refine (eLpNorm_mono_ae_real
    (g := fun x => (W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) * ‖iteratedFDeriv ℝ n u x‖) hmeas
    (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_mul, norm_norm, norm_norm]
    exact mul_le_mul_of_nonneg_right (hκ x) (norm_nonneg _)
  · refine (sa16q_holder_mul (f := fun x => W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)))
      (continuous_const.mul hωc).aestronglyMeasurable hGc.aestronglyMeasurable
      hR hra hp h).trans ?_
    have h1 : (fun x : Euc d => W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) =
        W • (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) := by funext x; simp
    rw [h1, eLpNorm_const_smul, Real.enorm_eq_ofReal hW]
    exact sa16q_mul_le (sa16q_iter_lp u.smooth' hd1 p hn)

lemma sa16q_pd_sub_k {f g : Euc d → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g)
    (r : Fin k → Fin d) (x : Euc d) :
    partialDeriv r (fun y => f y - g y) x = partialDeriv r f x - partialDeriv r g x := by
  unfold partialDeriv
  have := iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt (x := x)
  show (iteratedFDeriv ℝ k (f - g) x) _ = _
  rw [this]
  rfl

lemma sa16q_mol_pd_weight (N : ℕ) {μ : Euc d → ℝ} {κ : ℕ} (hμ : ContDiff ℝ κ μ) {Λ1 : ℝ}
    (hw : ∀ r : Fin κ → Fin d, ∀ x, |partialDeriv r μ x| * (1 + ‖x‖) ^ (d + 3) ≤ Λ1)
    (r : Fin κ → Fin d) (x : Euc d) :
    |partialDeriv r (sa16q_mol N μ) x| * (1 + ‖x‖) ^ (d + 3) ≤ 2 ^ (d + 3) * Λ1 := by
  have hc : Continuous (partialDeriv r μ) :=
    (sa16y_pd_contDiffN (j := κ) (r := 0) (by simpa using hμ) r).continuous
  rw [sa16q_mol_pd N hμ r]
  exact sa16q_mol_pt_weight N hc (hw r) x

/-- the mollifications converge in the weighted `L^R` sense against `‖D^n u‖` -/
lemma sa16q_conv_term {μ : Euc d → ℝ} {κ : ℕ} (hμ : ContDiff ℝ κ μ) {Λ1 : ℝ} (hΛ : 0 ≤ Λ1)
    (hw : ∀ r : Fin κ → Fin d, ∀ x, |partialDeriv r μ x| * (1 + ‖x‖) ^ (d + 3) ≤ Λ1)
    (u : 𝓢(Euc d, ℝ)) (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (fun N => eLpNorm (fun x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖ *
        ‖iteratedFDeriv ℝ n u x‖) (ENNReal.ofReal R) volume) atTop (𝓝 0) := by
  have hμc : Continuous μ := hμ.continuous
  have hmolsm : ∀ N, ContDiff ℝ ∞ (sa16q_mol N μ) := fun N => sa16y_mollify_smooth N hμc
  have hmolk : ∀ N, ContDiff ℝ κ (sa16q_mol N μ) := fun N =>
    (hmolsm N).of_le (by exact_mod_cast le_top)
  have hdiff : ∀ N, ContDiff ℝ κ (fun y => sa16q_mol N μ y - μ y) := fun N => (hmolk N).sub hμ
  have h1w : ∀ x : Euc d, (1 : ℝ) ≤ (1 + ‖x‖) ^ (d + 3) := fun x =>
    one_le_pow₀ (by linarith [norm_nonneg x])
  have hpdμ : ∀ r x, |partialDeriv r μ x| ≤ Λ1 := fun r x => by
    calc |partialDeriv r μ x| = |partialDeriv r μ x| * 1 := (mul_one _).symm
      _ ≤ |partialDeriv r μ x| * (1 + ‖x‖) ^ (d + 3) := by gcongr; exact h1w x
      _ ≤ Λ1 := hw r x
  have hpdm : ∀ N r x, |partialDeriv r (sa16q_mol N μ) x| ≤ 2 ^ (d + 3) * Λ1 := fun N r x => by
    calc |partialDeriv r (sa16q_mol N μ) x| = |partialDeriv r (sa16q_mol N μ) x| * 1 := (mul_one _).symm
      _ ≤ |partialDeriv r (sa16q_mol N μ) x| * (1 + ‖x‖) ^ (d + 3) := by gcongr; exact h1w x
      _ ≤ 2 ^ (d + 3) * Λ1 := sa16q_mol_pd_weight N hμ hw r x
  have hbd : ∀ N x, ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖ ≤
      ∑ r : Fin κ → Fin d, (2 ^ (d + 3) * Λ1 + Λ1) := fun N x => by
    refine (sa16j_norm_iter_le _ x κ).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [sa16q_pd_sub_k (hmolk N) hμ r x]
    exact (abs_sub _ _).trans (add_le_add (hpdm N r x) (hpdμ r x))
  refine sa16y_dom_lp R hR (fun N x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖)
    (fun x => ‖iteratedFDeriv ℝ n u x‖) (E0 := ∑ r : Fin κ → Fin d, (2 ^ (d + 3) * Λ1 + Λ1))
    (fun N => ((hdiff N).continuous_iteratedFDeriv le_rfl).norm) (fun N x => norm_nonneg _) hbd ?_
    (u.smooth'.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).norm
    (sa16q_iter_memLp u n)
  intro x
  have hlim : Tendsto (fun N => ∑ r : Fin κ → Fin d,
      |partialDeriv r (sa16q_mol N μ) x - partialDeriv r μ x|) atTop (𝓝 0) := by
    have : (0 : ℝ) = ∑ r : Fin κ → Fin d, (0 : ℝ) := by simp
    rw [this]
    refine tendsto_finset_sum _ fun r _ => ?_
    have h := sa16q_mol_tendsto hμ r x
    simpa using (h.sub_const (partialDeriv r μ x)).abs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun N => norm_nonneg _)
    (fun N => ?_)
  refine (sa16j_norm_iter_le _ x κ).trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
  rw [sa16q_pd_sub_k (hmolk N) hμ r x]

end Unif

end HRS.Whole.AppendixA.Phase2SA16Q
