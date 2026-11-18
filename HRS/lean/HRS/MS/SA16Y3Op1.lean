import HRS.MS.SA16Y3Sk4
import HRS.MS.SA16Y3Hk4
import HRS.MS.SA16Y3Mem2

/-!
# S.A.16 (SA16Y3) Op1: the skew operator `P^A_μ` on `C_c^∞`: linearity, smoothness, `L^p` bound of all derivatives (packet P7, Hilbert corner)

`sa16y3_PA_add/smul/smooth`; `sa16y3_pd_PA_bound`:
`‖∂^idx (P^A_μ φ)‖_p ≤ K AB Λ S_{j+2}(φ)` for `A^T = -A`, `|A_ab| ≤ AB`, `‖D^kμ‖ ≤ Λ` (`k ≤ j+2`), `1 < θ = s+2-d`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Op1
variable {d : ℕ} {s : ℝ}

lemma sa16y3_Q_smul (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : IsCcInfty f) (c : ℝ) (i : Fin d) (x : Euc d) :
    sa16y3_Q s i (c • f) x = c * sa16y3_Q s i f x := by
  unfold sa16y3_Q
  rw [sa16y3_conv_smul]
  have h1 := sa16z_conv_smooth hs0 hsd hf
  rw [fderiv_const_smul (h1.differentiable (by simp) x)]
  rfl

lemma sa16y3_PA_smooth (hs0 : 0 ≤ s) (hsd : s < d) (A : Matrix (Fin d) (Fin d) ℝ) {a ψ : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hψ : IsCcInfty ψ) : ContDiff ℝ ∞ (sa16y3_PA s A a ψ) := by
  have h : sa16y3_PA s A a ψ = fun x => ∑ i : Fin d, ∑ j : Fin d, A j i * sa16y3_Q s i (sa16z_src a ψ j) x := rfl
  rw [h]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    contDiff_const.mul (sa16y3_Q_smooth hs0 hsd (sa16z_src_cc ha hψ j) i)

theorem sa16y3_PA_add (hs0 : 0 ≤ s) (hsd : s < d) (A : Matrix (Fin d) (Fin d) ℝ) {a φ ψ : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    sa16y3_PA s A a (φ + ψ) = sa16y3_PA s A a φ + sa16y3_PA s A a ψ := by
  funext x
  simp only [sa16y3_PA, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hq : sa16y3_Q s i (fun y => sa16z_src a φ j y + sa16z_src a ψ j y) x =
      sa16y3_Q s i (sa16z_src a φ j) x + sa16y3_Q s i (sa16z_src a ψ j) x :=
    sa16y3_Q_add hs0 hsd (sa16z_src_cc ha hφ j) (sa16z_src_cc ha hψ j) i x
  rw [sa16y3_src_add hφ hψ j, hq]
  ring

theorem sa16y3_PA_smul (hs0 : 0 ≤ s) (hsd : s < d) (A : Matrix (Fin d) (Fin d) ℝ) {a φ : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hφ : IsCcInfty φ) (c : ℝ) :
    sa16y3_PA s A a (c • φ) = c • sa16y3_PA s A a φ := by
  funext x
  simp only [sa16y3_PA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sa16y3_src_smul hφ c j, sa16y3_Q_smul hs0 hsd (sa16z_src_cc ha hφ j) c i x]
  ring

theorem sa16y3_pd_PA_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p)
    (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ}, 0 ≤ AB → (∀ a b, |A a b| ≤ AB) →
      A.transpose = -A → ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (j + 2) Λ μ → ∀ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * (AB * Λ)) * sa16z_S p φ (j + 2) := by
  choose CQ hCQ0 hCQ using fun i : Fin d => sa16y3_Q_jet (s := s) hd hs0 hsd hθ1 hp i
  choose KR hKR0 hKR using fun i : Fin d => sa16y3_R_bound (s := s) hd hs0 hsd hθ1 hp i j
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have : (1 : ℝ) ≤ p := hp.le
    simpa using ENNReal.ofReal_le_ofReal this
  refine ⟨(d : ℝ) * ∑ i : Fin d, (2 * CQ i + KR i),
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by linarith [hCQ0 i, hKR0 i]), ?_⟩
  intro A AB hAB hAab hA μ φ hμ hφ Λ hΛ hCb idx
  set S := sa16z_S p φ (j + 2) with hS
  have hΛA : 0 ≤ AB * Λ := mul_nonneg hAB hΛ
  have hterm : ∀ i j' : Fin d, eLpNorm (fun x => A j' i * (sa16y3_Q s i (fun y => sa16z_dm μ j' y *
        partialDeriv idx φ y) x + sa16y3_R s i (sa16z_dm μ j') φ j idx x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((2 * CQ i + KR i) * (AB * Λ)) * S := by
    intro i j'
    have hb : ContDiff ℝ ∞ (sa16z_dm μ j') := sa16z_dm_smooth hμ j'
    have hCbb : sa16z_Cb (j + 1) Λ (sa16z_dm μ j') := sa16z_Cb_dm hμ hCb j'
    have hC0 : sa16z_Cb 0 Λ (sa16z_dm μ j') := sa16z_Cb_mono (Nat.zero_le _) hCbb
    have hC1 : sa16z_Cb 1 Λ (sa16z_dm μ j') := sa16z_Cb_mono (by omega) hCbb
    have e1 : eLpNorm (sa16y3_Q s i (fun y => sa16z_dm μ j' y * partialDeriv idx φ y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (CQ i * (Λ + Λ)) * S :=
      (hCQ i hb hφ hΛ hΛ (sa16z_Cb_abs hC0) (sa16z_Cb_fderiv hC1) idx).trans
        (by gcongr; exact sa16z_S_mono φ (by omega))
    have e2 : eLpNorm (fun x => sa16y3_R s i (sa16z_dm μ j') φ j idx x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (KR i * Λ) * S :=
      (hKR i hb hφ hΛ hCbb idx).trans (by gcongr; exact sa16z_S_mono φ (by omega))
    have hfn : (fun x => A j' i * (sa16y3_Q s i (fun y => sa16z_dm μ j' y * partialDeriv idx φ y) x +
        sa16y3_R s i (sa16z_dm μ j') φ j idx x)) =
        A j' i • ((sa16y3_Q s i (fun y => sa16z_dm μ j' y * partialDeriv idx φ y)) +
          (fun x => sa16y3_R s i (sa16z_dm μ j') φ j idx x)) := by
      funext x; simp
    rw [hfn, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |A j' i| * eLpNorm ((sa16y3_Q s i (fun y => sa16z_dm μ j' y * partialDeriv idx φ y)) +
          (fun x => sa16y3_R s i (sa16z_dm μ j') φ j idx x)) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal AB * (ENNReal.ofReal (CQ i * (Λ + Λ)) * S + ENNReal.ofReal (KR i * Λ) * S) := by
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hAab _ _)) ((eLpNorm_add_le hp1).trans (add_le_add e1 e2))
      _ = ENNReal.ofReal ((2 * CQ i + KR i) * (AB * Λ)) * S := by
          rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg (hCQ0 i) (by linarith)) (mul_nonneg (hKR0 i) hΛ),
            ← mul_assoc, ← ENNReal.ofReal_mul hAB]
          congr 2; ring
  have hfun : partialDeriv idx (sa16y3_PA s A μ φ) = -(∑ i : Fin d, ∑ j' : Fin d, fun x =>
      A j' i * (sa16y3_Q s i (fun y => sa16z_dm μ j' y * partialDeriv idx φ y) x +
        sa16y3_R s i (sa16z_dm μ j') φ j idx x)) := by
    funext x
    rw [sa16y3_PA_pd hs0 hsd hA hμ hφ idx x]
    simp [Finset.sum_apply]
  rw [hfun, eLpNorm_neg]
  refine (eLpNorm_sum_le hp1).trans ?_
  calc ∑ i : Fin d, eLpNorm (∑ j' : Fin d, fun x => A j' i * (sa16y3_Q s i (fun y => sa16z_dm μ j' y *
        partialDeriv idx φ y) x + sa16y3_R s i (sa16z_dm μ j') φ j idx x)) (ENNReal.ofReal p) volume
      ≤ ∑ i : Fin d, ∑ j' : Fin d, ENNReal.ofReal ((2 * CQ i + KR i) * (AB * Λ)) * S := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (eLpNorm_sum_le hp1).trans (Finset.sum_le_sum fun j' _ => hterm i j')
    _ = (∑ i : Fin d, ∑ j' : Fin d, ENNReal.ofReal ((2 * CQ i + KR i) * (AB * Λ))) * S := by
        simp only [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ i : Fin d, ∑ j' : Fin d, (2 * CQ i + KR i) * (AB * Λ)) * S := by
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j' _ =>
          mul_nonneg (by linarith [hCQ0 i, hKR0 i]) hΛA)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun j' _ => mul_nonneg (by linarith [hCQ0 i, hKR0 i]) hΛA)]
    _ = _ := by
        congr 2
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Op1

end HRS.Whole.AppendixA.Phase2SA16R
