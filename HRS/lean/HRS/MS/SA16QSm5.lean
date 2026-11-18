import HRS.MS.SA16QSm4

/-!
# S.A.16 (SA16Q), E6 part 11: the master estimate for smooth coefficients

For `a ∈ SB`, `u ∈ 𝓢`, `l ≤ m` and a coordinate tuple `idx` of length `l`:

`‖∂^idx (eucNonlocal s M a u)‖_p ≤ d² MB (C₂ N_P + C₁ N_Q)` with
`N_P = ∑_k C(l,k) ‖ ‖D^k a‖ ‖D^{l-k} u‖ ‖_r`, `N_Q = ∑_k C(l,k) ‖ ‖D^{k+1} a‖ ‖D^{l-k} u‖ ‖_q`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Norms
variable {d : ℕ}

lemma sa16q_nat_le_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

lemma sa16q_mul_le6 {a b c : ℝ≥0∞} (h : b ≤ c) : a * b ≤ a * c := mul_le_mul' le_rfl h

/-- `∑_k C(l,k) ‖ ‖D^k a‖ ‖D^{l-k}u‖ ‖_r` -/
def sa16q_NP (a u : Euc d → ℝ) (l : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) *
    eLpNorm (fun x => ‖iteratedFDeriv ℝ k a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖)
      (ENNReal.ofReal r) volume

/-- `∑_k C(l,k) ‖ ‖D^{k+1} a‖ ‖D^{l-k}u‖ ‖_r` -/
def sa16q_NQ (a u : Euc d → ℝ) (l : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) *
    eLpNorm (fun x => ‖iteratedFDeriv ℝ (k + 1) a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖)
      (ENNReal.ofReal r) volume

lemma sa16q_lp_of_pointwise {l : ℕ} {Ψ : Euc d → ℝ} (hΨ : Continuous Ψ) (c : ℕ → ℝ) (W : ℕ → Euc d → ℝ)
    (hW : ∀ k, Continuous (W k)) (hc : ∀ k, 0 ≤ c k)
    (hpt : ∀ x, |Ψ x| ≤ ∑ k ∈ Finset.range (l + 1), c k * W k x) {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm Ψ (ENNReal.ofReal r) volume ≤
      ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (c k) * eLpNorm (W k) (ENNReal.ofReal r) volume := by
  have h1r : 1 ≤ ENNReal.ofReal r := by simpa using ENNReal.ofReal_le_ofReal hr
  have hmono : eLpNorm Ψ (ENNReal.ofReal r) volume ≤
      eLpNorm (fun x => ∑ k ∈ Finset.range (l + 1), c k * W k x) (ENNReal.ofReal r) volume :=
    eLpNorm_mono_ae_real hΨ.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hpt x)
  refine hmono.trans ?_
  have hsum : (fun x => ∑ k ∈ Finset.range (l + 1), c k * W k x) =
      ∑ k ∈ Finset.range (l + 1), (c k • W k) := by
    funext x; simp [Finset.sum_apply]
  rw [hsum]
  refine (eLpNorm_sum_le h1r).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hc k)]

lemma sa16q_pd_mul_le {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {l : ℕ}
    (idx : Fin l → Fin d) (x : Euc d) :
    |partialDeriv idx (fun y => f y * g y) x| ≤ ∑ k ∈ Finset.range (l + 1),
      (l.choose k : ℝ) * (‖iteratedFDeriv ℝ k f x‖ * ‖iteratedFDeriv ℝ (l - k) g x‖) := by
  refine (sa16j_partial_le idx _ x).trans ?_
  refine (norm_iteratedFDeriv_mul_le hf hg x (n := l) (by exact_mod_cast le_top)).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  ring

lemma sa16q_norm_iter_pd_le {a : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (j : Fin d) (k : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) x‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) a x‖ := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (m := ∞) (by simp)
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ a)
    (c := (EuclideanSpace.single j (1 : ℝ) : Euc d)) (x := x) (N := ∞) (n := k)
    hf.contDiffAt (by exact_mod_cast le_top)
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  simp [EuclideanSpace.norm_single]

/-- `‖∂^idx (a u)‖_r ≤ N_P` -/
lemma sa16q_Psi_lp {a : Euc d → ℝ} (ha : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) {l : ℕ} (idx : Fin l → Fin d)
    {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm (⇑(sa16q_pdS idx (sa16q_mulS ha u))) (ENNReal.ofReal r) volume ≤ sa16q_NP a u l r := by
  have hcd : ContDiff ℝ ∞ (fun y => a y * u y) := ha.1.mul u.smooth'
  have hfun : ⇑(sa16q_pdS idx (sa16q_mulS ha u)) = partialDeriv idx (fun y => a y * u y) := by
    rw [sa16q_pdS_fun]
    congr 1
    exact funext (sa16q_mulS_apply ha u)
  rw [hfun]
  have hcont : Continuous (partialDeriv idx (fun y => a y * u y)) := by
    have := sa16j_pd_smooth hcd idx
    exact this.continuous
  refine (sa16q_lp_of_pointwise hcont (fun k => (l.choose k : ℝ))
    (fun k x => ‖iteratedFDeriv ℝ k a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖) (fun k => ?_)
    (fun k => by positivity) (fun x => sa16q_pd_mul_le ha.1 u.smooth' idx x) hr).trans le_rfl
  exact ((ha.1.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm).mul
    ((u.smooth'.continuous_iteratedFDeriv (m := l - k) (sa16q_nat_le_infty _)).norm)

/-- `‖∂^idx ((∂_j a) u)‖_r ≤ N_Q` -/
lemma sa16q_Xi_lp {a : Euc d → ℝ} (ha : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) (j : Fin d) {l : ℕ}
    (idx : Fin l → Fin d) {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm (⇑(sa16q_pdS idx (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u)))
      (ENNReal.ofReal r) volume ≤ sa16q_NQ a u l r := by
  have hb := sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))
  have hcd : ContDiff ℝ ∞ (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ)) * u y) := hb.1.mul u.smooth'
  have hfun : ⇑(sa16q_pdS idx (sa16q_mulS hb u)) =
      partialDeriv idx (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ)) * u y) := by
    rw [sa16q_pdS_fun]
    congr 1
    exact funext (sa16q_mulS_apply hb u)
  rw [hfun]
  have hcont : Continuous (partialDeriv idx
      (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ)) * u y)) :=
    (sa16j_pd_smooth hcd idx).continuous
  have hpt : ∀ x, |partialDeriv idx (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ)) * u y) x| ≤
      ∑ k ∈ Finset.range (l + 1), (l.choose k : ℝ) *
        (‖iteratedFDeriv ℝ (k + 1) a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖) := by
    intro x
    refine (sa16q_pd_mul_le hb.1 u.smooth' idx x).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (sa16q_norm_iter_pd_le ha.1 j k x) le_rfl (norm_nonneg _) (norm_nonneg _))
      (Nat.cast_nonneg _)
  refine (sa16q_lp_of_pointwise hcont (fun k => (l.choose k : ℝ))
    (fun k x => ‖iteratedFDeriv ℝ (k + 1) a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖) (fun k => ?_)
    (fun k => by positivity) hpt hr).trans le_rfl
  exact ((ha.1.continuous_iteratedFDeriv (m := k + 1) (sa16q_nat_le_infty _)).norm).mul
    ((u.smooth'.continuous_iteratedFDeriv (m := l - k) (sa16q_nat_le_infty _)).norm)

lemma sa16q_eLpNorm_dsum_le (f : Fin d → Fin d → Euc d → ℝ) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (fun x => ∑ i, ∑ j, f i j x) r volume ≤ ∑ i, ∑ j, eLpNorm (f i j) r volume := by
  have h1 : (fun x => ∑ i, ∑ j, f i j x) = ∑ i, (fun x => ∑ j, f i j x) := by
    funext x; simp [Finset.sum_apply]
  have h2 : ∀ i, (fun x => ∑ j, f i j x) = ∑ j, f i j := by
    intro i; funext x; simp [Finset.sum_apply]
  rw [h1]
  refine (eLpNorm_sum_le hr).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [h2 i]
  exact eLpNorm_sum_le hr

end Norms

section Master
variable {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

theorem sa16q_master {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ q r C1 C2 : ℝ, (1 < q ∧ q < p ∧ 1 / q = 1 / p + ((d : ℝ) - s - 1) / d) ∧
      (1 < r ∧ r ≤ p ∧ (r = p ∨ (r < p ∧ 1 / r = 1 / p + ((d : ℝ) - s - 2) / d))) ∧
      0 < C1 ∧ 0 < C2 ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ), (∀ i j, |M i j| ≤ MB) →
        ∀ {a : Euc d → ℝ} (ha : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) {l : ℕ} (idx : Fin l → Fin d),
        eLpNorm (partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u)) (ENNReal.ofReal p) volume ≤
          ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) *
            (ENNReal.ofReal C2 * sa16q_NP a u l r + ENNReal.ofReal C1 * sa16q_NQ a u l q) := by
  obtain ⟨q, C1, hq1, hqp, hq, hC1, hD1⟩ := sa16q_D1_bound hd hs hs2 hp hfar
  obtain ⟨r, C2, hr1, hrp, hC2, hr, hD2⟩ := sa16q_D2_bound hd hs hs2 hp hfar
  refine ⟨q, r, C1, C2, ⟨hq1, hqp, hq⟩, ⟨hr1, hrp, hr⟩, hC1, hC2, ?_⟩
  intro M MB hM a ha u l idx
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨A, hA⟩ : ∃ A : Fin d → Fin d → Euc d → ℝ, ∀ i j x, A i j x =
      fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
        (sa16q_pdS idx (sa16q_mulS ha u))) y (EuclideanSpace.single j (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) := ⟨fun i j x => _, fun _ _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin d → Fin d → Euc d → ℝ, ∀ i j x, B i j x =
      fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
        (sa16q_pdS idx (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u))) x
        (EuclideanSpace.single i (1 : ℝ)) := ⟨fun i j x => _, fun _ _ _ => rfl⟩
  have hfun : partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u) =
      fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * (A i j x - B i j x) := by
    funext x
    rw [sa16q_pd_F hd hs hs2 M ha u idx x]
    simp only [hA, hB]
  have hAnorm : ∀ i j, eLpNorm (A i j) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C2 * sa16q_NP a u l r := by
    intro i j
    have : A i j = fun x => fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
        (sa16q_pdS idx (sa16q_mulS ha u))) y (EuclideanSpace.single j (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) := funext (hA i j)
    rw [this]
    exact (hD2 _ i j).trans (sa16q_mul_le6 (sa16q_Psi_lp ha u idx hr1.le))
  have hBnorm : ∀ i j, eLpNorm (B i j) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C1 * sa16q_NQ a u l q := by
    intro i j
    have : B i j = fun x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
        (sa16q_pdS idx (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u))) x
        (EuclideanSpace.single i (1 : ℝ)) := funext (hB i j)
    rw [this]
    exact (hD1 _ i).trans (sa16q_mul_le6 (sa16q_Xi_lp ha u j idx hq1.le))
  have hAc : ∀ i j, AEStronglyMeasurable (A i j) volume := fun i j => by
    have : A i j = fun x => fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
        (sa16q_pdS idx (sa16q_mulS ha u))) y (EuclideanSpace.single j (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) := funext (hA i j)
    rw [this]
    exact (sa16q_cont_D2 hd hs hs2 _ i j).aestronglyMeasurable
  have hBc : ∀ i j, AEStronglyMeasurable (B i j) volume := fun i j => by
    have : B i j = fun x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
        (sa16q_pdS idx (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u))) x
        (EuclideanSpace.single i (1 : ℝ)) := funext (hB i j)
    rw [this]
    exact (sa16q_cont_D1 hd hs hs2 _ i).aestronglyMeasurable
  rw [hfun]
  refine (sa16q_eLpNorm_dsum_le (fun i j x => M j i * (A i j x - B i j x)) hp1).trans ?_
  have hterm : ∀ i j, eLpNorm (fun x => M j i * (A i j x - B i j x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal MB * (ENNReal.ofReal C2 * sa16q_NP a u l r + ENNReal.ofReal C1 * sa16q_NQ a u l q) := by
    intro i j
    have e1 : (fun x => M j i * (A i j x - B i j x)) = (M j i) • (A i j - B i j) := by
      funext x; simp
    rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |M j i| * eLpNorm (A i j - B i j) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal MB * (eLpNorm (A i j) (ENNReal.ofReal p) volume +
            eLpNorm (B i j) (ENNReal.ofReal p) volume) := by
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hM j i)) (eLpNorm_sub_le hp1)
      _ ≤ _ := sa16q_mul_le6 (add_le_add (hAnorm i j) (hBnorm i j))
  calc ∑ i : Fin d, ∑ j : Fin d, eLpNorm (fun x => M j i * (A i j x - B i j x)) (ENNReal.ofReal p) volume
      ≤ ∑ i : Fin d, ∑ j : Fin d, ENNReal.ofReal MB *
          (ENNReal.ofReal C2 * sa16q_NP a u l r + ENNReal.ofReal C1 * sa16q_NQ a u l q) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Master

end HRS.Whole.AppendixA.Phase2SA16Q
