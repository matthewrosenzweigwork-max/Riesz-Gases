import HRS.MS.SA16StrongSL1
import HRS.MS.SA16StrongLeib
import HRS.MS.SA16StrongNlDefs

/-!
# S.A.16 SL3: `nlCut_difference_bound`

`nlCut δ - nlCut η = lam c (fracCut δ - fracCut η)(μ u) + gamma ∑ M (oddCut δ - oddCut η)((∂_j μ) u)`.
SL1 and SL2 bound the two kinds of terms by the `W^{m+2}` resp. `W^{m+1}` norms of the Schwartz products `μ u`,
`(∂_j μ) u`; the Leibniz rule for jets (`sa16y_prod_jet_le`) bounds these by `W^{m+2} u`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section SL3
variable {d : ℕ}

lemma sa16y_wnorm_jet (n : ℕ) (p : ℝ) [Fact (2 ≤ p)] (v : 𝓢(Euc d, ℝ)) :
    wNormE n p (⇑v) = eLpNorm (wJet n (⇑v)) (ENNReal.ofReal p) volume :=
  sa16j_wNormE_eq d n p v.smooth' (sa16j_S_memLp n p v)

/-- the product of two Schwartz functions -/
def sa16y_mulS (a v : 𝓢(Euc d, ℝ)) : 𝓢(Euc d, ℝ) := SchwartzMap.smulLeftCLM ℝ (⇑a) v

lemma sa16y_mulS_apply (a v : 𝓢(Euc d, ℝ)) : ⇑(sa16y_mulS a v) = fun y => a y * v y := by
  funext y
  unfold sa16y_mulS
  rw [SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth]
  simp

lemma sa16y_mulS_wnorm (n : ℕ) (p : ℝ) [Fact (2 ≤ p)] (a v : 𝓢(Euc d, ℝ)) {B : ℝ}
    (hB : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (⇑a) x‖ ≤ B) :
    wNormE n p (⇑(sa16y_mulS a v)) ≤
      ENNReal.ofReal (B * ((d : ℝ) + 1) ^ n) * wNormE n p (⇑v) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  rw [sa16y_wnorm_jet, sa16y_wnorm_jet]
  have hmeas : AEStronglyMeasurable (wJet n (⇑(sa16y_mulS a v))) volume :=
    (sa16j_jet_cont (sa16y_mulS a v).smooth' n).aestronglyMeasurable
  have hpt : ∀ x, ‖wJet n (⇑(sa16y_mulS a v)) x‖ ≤ (B * ((d : ℝ) + 1) ^ n) * ‖wJet n (⇑v) x‖ := by
    intro x
    rw [sa16y_mulS_apply]
    exact sa16y_prod_jet_le a.smooth' v.smooth' n x (fun i hi => hB i hi x)
  refine (eLpNorm_mono_ae_real hmeas (Eventually.of_forall hpt)).trans ?_
  have : (fun x => (B * ((d : ℝ) + 1) ^ n) * ‖wJet n (⇑v) x‖) =
      (B * ((d : ℝ) + 1) ^ n) • (fun x => ‖wJet n (⇑v) x‖) := by
    funext x; simp
  rw [this, eLpNorm_const_smul, eLpNorm_norm _ (sa16j_jet_cont (show ContDiff ℝ ∞ (⇑v) from v.smooth') n).aestronglyMeasurable]
  refine le_of_eq ?_
  rw [Real.enorm_eq_ofReal (by positivity)]

lemma sa16y_wnorm_mono_level {m n : ℕ} (hmn : m ≤ n) (p : ℝ) [Fact (2 ≤ p)] (v : 𝓢(Euc d, ℝ)) :
    wNormE m p (⇑v) ≤ wNormE n p (⇑v) := by
  rw [sa16y_wnorm_jet, sa16y_wnorm_jet]
  have hv : ContDiff ℝ ∞ (⇑v) := v.smooth'
  exact eLpNorm_mono (sa16j_jet_cont hv m).aestronglyMeasurable fun x => sa16y_jet_mono hmn (⇑v) x

/-- the first coordinate derivative of a Schwartz function as a function -/
lemma sa16y_pd1_eq (μ : Euc d → ℝ) (hμ : ContDiff ℝ ∞ μ) (j : Fin d) :
    partialDeriv (fun _ : Fin 1 => j) μ =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)) ∘ (fderiv ℝ μ) := by
  funext y
  rw [sa16j_pd_succ hμ]
  have : partialDeriv (fun l : Fin 0 => (fun _ : Fin 1 => j) l.succ) μ = μ := by
    funext z; exact sa16j_pd_zero _ _ z
  rw [this]
  rfl

lemma sa16y_dpd_norm (μ : 𝓢(Euc d, ℝ)) (j : Fin d) (i : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (partialDeriv (fun _ : Fin 1 => j) (⇑μ)) x‖ ≤
      ‖iteratedFDeriv ℝ (i + 1) (⇑μ) x‖ := by
  have hμ : ContDiff ℝ ∞ (⇑μ) := μ.smooth'
  rw [sa16y_pd1_eq _ hμ j]
  have hf : ContDiff ℝ i (fderiv ℝ (⇑μ)) := hμ.fderiv_right (m := i) (by exact_mod_cast le_top)
  have h := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).norm_iteratedFDeriv_comp_left
    (hf.contDiffAt (x := x)) (n := i) (N := (i : ℕ∞ω)) le_rfl
  have hL : ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    have := f.le_opNorm (EuclideanSpace.single j (1 : ℝ) : Euc d)
    simpa [PiLp.norm_single, mul_comm] using this
  rw [norm_iteratedFDeriv_fderiv] at h
  calc _ ≤ _ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ (i + 1) (⇑μ) x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = _ := one_mul _

/-- `ofReal a * (ofReal b * X) ≤ ofReal c * X` when `a * b ≤ c` -/
lemma sa16y_ofReal_mul_le {a b c : ℝ} (ha : 0 ≤ a) (hab : a * b ≤ c) (X : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X) ≤ ENNReal.ofReal c * X := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hab) le_rfl

lemma sa16y_ofReal_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (X : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * X)) = ENNReal.ofReal (a * b * c) * X := by
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

/-- the first coordinate derivative of a Schwartz function, as a Schwartz function -/
def sa16y_dS (f : 𝓢(Euc d, ℝ)) (j : Fin d) : 𝓢(Euc d, ℝ) :=
  LineDeriv.iteratedLineDerivOp (fun _ : Fin 1 => (EuclideanSpace.single j (1 : ℝ) : Euc d)) f

lemma sa16y_dS_apply (f : 𝓢(Euc d, ℝ)) (j : Fin d) :
    ⇑(sa16y_dS f j) = partialDeriv (fun _ : Fin 1 => j) (⇑f) :=
  (sa16j_pd_schwartz f (fun _ : Fin 1 => j)).symm

/-- the core estimate: SL1 and SL2 for the two kinds of terms of `nlCut` -/
theorem sa16y_nl_core (d : ℕ) (hd : 1 ≤ d) (m : ℕ)
    (θ p lam c gamma MB : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, |M i j| ≤ MB) → ∀ f u : 𝓢(Euc d, ℝ),
      ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 →
      wNormE m p
        (fun x => nlCut d θ δ lam c gamma M f u x - nlCut d θ η lam c gamma M f u x) ≤
        ENNReal.ofReal (C * (δ ^ (2 - θ) + η ^ (2 - θ))) *
          (wNormE (m + 2) p (⇑(sa16y_mulS f u)) +
            ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS f j) u))) := by
  obtain ⟨C1, hC1, h1⟩ := fracCut_difference_bound d hd m θ p hθ0 hθ2
  obtain ⟨C2, hC2, h2⟩ := oddCut_difference_bound d hd m θ p hθ0 hθ2
  refine ⟨|lam * c| * C1 + (d : ℝ) * (|gamma| * |MB| * C2) + 1, by positivity, ?_⟩
  intro M hM f u δ η hδ hη
  set S : ℝ := δ ^ (2 - θ) + η ^ (2 - θ) with hS
  have hS0 : 0 ≤ S := add_nonneg (Real.rpow_nonneg hδ.1.le _) (Real.rpow_nonneg hη.1.le _)
  set A : ℝ≥0∞ := wNormE (m + 2) p (⇑(sa16y_mulS f u)) with hA
  set a : Fin d → ℝ≥0∞ := fun j => wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS f j) u)) with ha
  set v1 : 𝓢(Euc d, ℝ) := sa16y_mulS f u with hv1
  set v2 : Fin d → 𝓢(Euc d, ℝ) := fun j => sa16y_mulS (sa16y_dS f j) u with hv2d
  have hv2 : ∀ j, ⇑(v2 j) = fun y => partialDeriv (fun _ : Fin 1 => j) (⇑f) y * u y := by
    intro j; show ⇑(sa16y_mulS (sa16y_dS f j) u) = _; rw [sa16y_mulS_apply, sa16y_dS_apply]
  set D1 : Euc d → ℝ := fun x => fracCut d θ δ (⇑v1) x - fracCut d θ η (⇑v1) x with hD1
  set D2 : Fin d → Fin d → Euc d → ℝ := fun i j x =>
    oddCut d θ δ i (⇑(v2 j)) x - oddCut d θ η i (⇑(v2 j)) x with hD2
  have hfun : (fun x => nlCut d θ δ lam c gamma M f u x - nlCut d θ η lam c gamma M f u x) =
      fun x => (fun x => (lam * c) * D1 x) x +
        (fun x => ∑ i : Fin d, ∑ j : Fin d, (gamma * M j i) * D2 i j x) x := by
    funext x
    simp only [nlCut, hD1, hD2, hv1, sa16y_mulS_apply, hv2]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    ring
  rw [hfun]
  have T1 : wNormE m p (fun x => (lam * c) * D1 x) ≤ ENNReal.ofReal (|lam * c| * C1 * S) * A := by
    calc wNormE m p (fun x => (lam * c) * D1 x) ≤ ENNReal.ofReal |lam * c| * wNormE m p D1 :=
          sa16y_wNormE_smul_le m p (lam * c) D1
      _ ≤ ENNReal.ofReal |lam * c| * (ENNReal.ofReal (C1 * S) * A) :=
          mul_le_mul' le_rfl (h1 δ η hδ hη v1)
      _ = ENNReal.ofReal (|lam * c| * C1 * S) * A := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]
  have T2 : ∀ i j : Fin d, wNormE m p (fun x => (gamma * M j i) * D2 i j x) ≤
      ENNReal.ofReal (|gamma| * |MB| * C2 * S) * a j := by
    intro i j
    have hgM : |gamma * M j i| ≤ |gamma| * |MB| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hM j i).trans (le_abs_self _)) (abs_nonneg _)
    calc wNormE m p (fun x => (gamma * M j i) * D2 i j x)
        ≤ ENNReal.ofReal |gamma * M j i| * wNormE m p (D2 i j) :=
          sa16y_wNormE_smul_le m p _ _
      _ ≤ ENNReal.ofReal |gamma * M j i| * (ENNReal.ofReal (C2 * S) * a j) :=
          mul_le_mul' le_rfl (h2 δ η hδ hη i (v2 j))
      _ ≤ ENNReal.ofReal (|gamma| * |MB| * C2 * S) * a j := by
          refine sa16y_ofReal_mul_le (abs_nonneg _) ?_ _
          calc |gamma * M j i| * (C2 * S) ≤ (|gamma| * |MB|) * (C2 * S) :=
                mul_le_mul_of_nonneg_right hgM (by positivity)
            _ = |gamma| * |MB| * C2 * S := by ring
  have T2' : wNormE m p (fun x => ∑ i : Fin d, ∑ j : Fin d, (gamma * M j i) * D2 i j x) ≤
      ENNReal.ofReal ((d : ℝ) * (|gamma| * |MB| * C2 * S)) * ∑ j : Fin d, a j := by
    refine (sa16y_wNormE_sum_le m p Finset.univ
      (fun i x => ∑ j : Fin d, (gamma * M j i) * D2 i j x)).trans ?_
    have hin : ∀ i : Fin d, wNormE m p (fun x => ∑ j : Fin d, (gamma * M j i) * D2 i j x) ≤
        ENNReal.ofReal (|gamma| * |MB| * C2 * S) * ∑ j : Fin d, a j := fun i =>
      (sa16y_wNormE_sum_le m p Finset.univ (fun j x => (gamma * M j i) * D2 i j x)).trans
        ((Finset.sum_le_sum fun j _ => T2 i j).trans (by rw [Finset.mul_sum]))
    refine (Finset.sum_le_sum fun i _ => hin i).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine (sa16y_wNormE_add_le m p _ _).trans ?_
  refine (add_le_add T1 T2').trans ?_
  have hsA : 0 ≤ |lam * c| * C1 * S := by positivity
  have hsB : 0 ≤ (d : ℝ) * (|gamma| * |MB| * C2 * S) := by positivity
  calc ENNReal.ofReal (|lam * c| * C1 * S) * A +
        ENNReal.ofReal ((d : ℝ) * (|gamma| * |MB| * C2 * S)) * ∑ j : Fin d, a j
      ≤ ENNReal.ofReal ((|lam * c| * C1 + (d : ℝ) * (|gamma| * |MB| * C2) + 1) * S) * A +
        ENNReal.ofReal ((|lam * c| * C1 + (d : ℝ) * (|gamma| * |MB| * C2) + 1) * S) * ∑ j : Fin d, a j := by
        refine add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
          (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
        · nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (lam * c)) hC1.le) hS0,
            mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (abs_nonneg gamma)) (abs_nonneg MB))
              (mul_nonneg hC2.le hS0)]
        · nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (lam * c)) hC1.le) hS0,
            mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (abs_nonneg gamma)) (abs_nonneg MB))
              (mul_nonneg hC2.le hS0)]
    _ = ENNReal.ofReal ((|lam * c| * C1 + (d : ℝ) * (|gamma| * |MB| * C2) + 1) * S) *
          (A + ∑ j : Fin d, a j) := (mul_add _ _ _).symm

theorem nlCut_difference_bound (d : ℕ) (hd : 1 ≤ d) (m : ℕ)
    (θ p lam c gamma MB B : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, |M i j| ≤ MB) → ∀ μ : SchwartzMap (Euc d) ℝ,
      (∀ j ≤ m+2, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ B) →
      ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 →
      ∀ u : SchwartzMap (Euc d) ℝ,
      wNormE m p
        (fun x => nlCut d θ δ lam c gamma M μ u x-nlCut d θ η lam c gamma M μ u x) ≤
        ENNReal.ofReal (C*(δ^(2-θ)+η^(2-θ))) * wNormE (m+2) p u := by
  obtain ⟨C0, hC0, h0⟩ := sa16y_nl_core d hd m θ p lam c gamma MB hθ0 hθ2
  set L1 : ℝ := B * ((d : ℝ) + 1) ^ (m + 2) with hL1
  set L2 : ℝ := B * ((d : ℝ) + 1) ^ (m + 1) with hL2
  refine ⟨C0 * (|L1| + (d : ℝ) * |L2|) + 1, by positivity, ?_⟩
  intro M hM μ hμB δ η hδ hη u
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hμB 0 (Nat.zero_le _) 0)
  have hL10 : 0 ≤ L1 := by positivity
  have hL20 : 0 ≤ L2 := by positivity
  set S : ℝ := δ ^ (2 - θ) + η ^ (2 - θ) with hS
  have hS0 : 0 ≤ S := add_nonneg (Real.rpow_nonneg hδ.1.le _) (Real.rpow_nonneg hη.1.le _)
  set W : ℝ≥0∞ := wNormE (m + 2) p (⇑u) with hW
  refine (h0 M hM μ u δ η hδ hη).trans ?_
  have hA : wNormE (m + 2) p (⇑(sa16y_mulS μ u)) ≤ ENNReal.ofReal L1 * W :=
    sa16y_mulS_wnorm (m + 2) p μ u (fun i hi x => hμB i hi x)
  have ha : ∀ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS μ j) u)) ≤ ENNReal.ofReal L2 * W := by
    intro j
    have hBj : ∀ i' ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ i' (⇑(sa16y_dS μ j)) x‖ ≤ B := by
      intro i' hi' x
      rw [sa16y_dS_apply]
      exact (sa16y_dpd_norm μ j i' x).trans (hμB (i' + 1) (by omega) x)
    exact (sa16y_mulS_wnorm (m + 1) p (sa16y_dS μ j) u hBj).trans
      (mul_le_mul' le_rfl (sa16y_wnorm_mono_level (by omega) p u))
  have hsum : wNormE (m + 2) p (⇑(sa16y_mulS μ u)) +
      ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS μ j) u)) ≤
      ENNReal.ofReal (L1 + (d : ℝ) * L2) * W := by
    calc _ ≤ ENNReal.ofReal L1 * W + ∑ j : Fin d, ENNReal.ofReal L2 * W :=
          add_le_add hA (Finset.sum_le_sum fun j _ => ha j)
      _ = ENNReal.ofReal (L1 + (d : ℝ) * L2) * W := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← add_mul,
            ← ENNReal.ofReal_add hL10 (by positivity)]
  calc ENNReal.ofReal (C0 * S) * (wNormE (m + 2) p (⇑(sa16y_mulS μ u)) +
        ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS μ j) u)))
      ≤ ENNReal.ofReal (C0 * S) * (ENNReal.ofReal (L1 + (d : ℝ) * L2) * W) := mul_le_mul' le_rfl hsum
    _ ≤ ENNReal.ofReal ((C0 * (|L1| + (d : ℝ) * |L2|) + 1) * S) * W := by
        refine sa16y_ofReal_mul_le (by positivity) ?_ _
        rw [abs_of_nonneg hL10, abs_of_nonneg hL20]
        nlinarith [mul_nonneg hC0.le hS0, mul_nonneg (mul_nonneg hC0.le hS0) hL10,
          mul_nonneg (mul_nonneg hC0.le hS0) (mul_nonneg (Nat.cast_nonneg d) hL20)]

end SL3

end HRS.Whole.AppendixA.Phase2SA16
