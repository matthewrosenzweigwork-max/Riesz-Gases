import HRS.MS.S21K2_W09D
import HRS.MS.S21G2_W01

/-!
# S21K2 W09E -- local compactness of the test inclusion (R26-T3.W09), final theorem

Contract `r26t3_local_jet_compact` (verbatim from the Pro packet, qualified names).  For `IsR2Test` functions `f n` supported in
`B_L` with `weightedSobolevE r P (f n) <= 1`, a subsequence has a Cauchy jet of order `r - 2` in the weight `P + 2`.
Route: each jet coordinate has an `H^1` bound (`s21k2_w09_jet_h1`), so the W09B common Cauchy subsequence applies to the finitely
many coordinates; the jet distance is the weighted Sobolev norm of a difference (`r26t3_jet_linear`, `r26t3_jet_norm`), which
`s21k2_w09_wE_le` bounds by the coordinate `L²` distances.  Helper prefix `s21k2_w09_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators FourierTransform
noncomputable section
namespace HRS.MS.R26T3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
variable {d : ℕ}

theorem s21k2_w09_le_top (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

theorem s21k2_w09_jet_h1 {r : ℕ} {L K0 : ℝ} {f : HRS.Euc d → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hsupp : tsupport f ⊆ Metric.closedBall 0 L)
    (hK0 : ∀ j' ≤ r, ∀ idx : Fin j' → Fin d, ∫ x, (HRS.Whole.partialDeriv idx f x) ^ 2 ≤ K0)
    {j : ℕ} (hj : j + 1 ≤ r) (i : Fin j → Fin d) :
    HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) (HRS.Whole.partialDeriv i f) ∧
    ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 (HRS.Whole.partialDeriv i f) ξ‖ ^ 2
      ≤ ((d : ℝ) + 1) * K0 := by
  obtain ⟨hs, hid⟩ := s21k2_w09_sobolev (s21k2_w09_pd_smooth hf i) (s21k2_w09_pd_cs hf i hsupp)
  refine ⟨hs, ?_⟩
  rw [hid]
  have hb : ∀ k : Fin d, ∫ x, (fderiv ℝ (HRS.Whole.partialDeriv i f) x (EuclideanSpace.single k (1 : ℝ))) ^ 2 ≤ K0 := by
    intro k
    simp only [s21k2_w09_fderiv_pd hf i k]
    exact hK0 (j + 1) hj (Fin.cons k i)
  have hsum : ∑ k : Fin d, ∫ x, (fderiv ℝ (HRS.Whole.partialDeriv i f) x (EuclideanSpace.single k (1 : ℝ))) ^ 2
      ≤ (d : ℝ) * K0 := by
    calc _ ≤ ∑ _k : Fin d, K0 := Finset.sum_le_sum fun k _ => hb k
      _ = (d : ℝ) * K0 := by simp
  have h0 : ∫ x, (HRS.Whole.partialDeriv i f x) ^ 2 ≤ K0 := hK0 j (by omega) i
  exact (add_le_add h0 hsum).trans_eq (by ring)

theorem s21k2_w09_jet_dist {r : ℕ} {P L η : ℝ} (hr : 2 ≤ r) {a b : HRS.Euc d → ℝ}
    (ha : HRS.Whole.IsR2Test a) (hb : HRS.Whole.IsR2Test b)
    (hsa : tsupport a ⊆ Metric.closedBall 0 L) (hsb : tsupport b ⊆ Metric.closedBall 0 L)
    (C : ℝ) (hC : C = (∑ j ∈ Finset.range (r - 2 + 1), (d : ℝ) ^ j) * max 1 ((1 + L ^ 2) ^ (-(P + 2))))
    (hη : 0 ≤ η)
    (hd : ∀ j ≤ r - 2, ∀ i : Fin j → Fin d,
      ∫ x, (HRS.Whole.partialDeriv i a x - HRS.Whole.partialDeriv i b x) ^ 2 ≤ η) :
    dist (r26t3_jet (r - 2) (P + 2) a) (r26t3_jet (r - 2) (P + 2) b) ≤ Real.sqrt (C * η) := by
  subst hC
  have haW : HRS.Whole.IsR2WeightedTest (r - 2) (P + 2) a :=
    ⟨ha.1.of_le (s21k2_w09_le_top _), s21k2_w09_wE_fin ha.1 hsa (r - 2) (P + 2)⟩
  have hbW : HRS.Whole.IsR2WeightedTest (r - 2) (P + 2) b :=
    ⟨hb.1.of_le (s21k2_w09_le_top _), s21k2_w09_wE_fin hb.1 hsb (r - 2) (P + 2)⟩
  have hgS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a + (-1 : ℝ) • b) :=
    ha.1.add (hb.1.const_smul (-1 : ℝ))
  have hsg : tsupport (a + (-1 : ℝ) • b) ⊆ Metric.closedBall 0 L := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    by_contra hxB
    apply Function.mem_support.1 hx
    have h1 : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxB (hsa h))
    have h2 : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxB (hsb h))
    simp [h1, h2]
  have hgW : HRS.Whole.IsR2WeightedTest (r - 2) (P + 2) (a + (-1 : ℝ) • b) :=
    ⟨hgS.of_le (s21k2_w09_le_top _), s21k2_w09_wE_fin hgS hsg (r - 2) (P + 2)⟩
  have hlin := r26t3_jet_linear (d := d) (r := r - 2) (P + 2) a b haW hbW (-1 : ℝ)
  have hjg : r26t3_jet (r - 2) (P + 2) a - r26t3_jet (r - 2) (P + 2) b
      = r26t3_jet (r - 2) (P + 2) (a + (-1 : ℝ) • b) := by
    rw [hlin, neg_one_smul ℝ, sub_eq_add_neg]
  have hnorm := (r26t3_jet_norm (P + 2) (a + (-1 : ℝ) • b) hgW).2
  have hpt : ∀ j ≤ r - 2, ∀ i : Fin j → Fin d,
      ∫ x, (HRS.Whole.partialDeriv i (a + (-1 : ℝ) • b) x) ^ 2 ≤ η := by
    intro j hj i
    have e : (fun x => (HRS.Whole.partialDeriv i (a + (-1 : ℝ) • b) x) ^ 2) =
        fun x => (HRS.Whole.partialDeriv i a x - HRS.Whole.partialDeriv i b x) ^ 2 := by
      funext x
      rw [s21g2_w01_pd_lin (r := r - 2) (ha.1.of_le (s21k2_w09_le_top _))
        (hb.1.of_le (s21k2_w09_le_top _)) (-1) hj i x]
      ring
    rw [e]
    exact hd j hj i
  have hW := s21k2_w09_wE_le hgS hsg (r - 2) (P + 2) η hη hpt
  rw [dist_edist, edist_eq_enorm_sub, hjg, hnorm]
  exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (hW.trans_eq (by rw [mul_assoc]))

theorem r26t3_local_jet_compact (d r : ℕ) (P L : ℝ) (hr : 2 ≤ r) (hL : 0 < L) :
    ∀ f : ℕ → HRS.Euc d → ℝ, (∀ n, HRS.Whole.IsR2Test (f n)) →
      (∀ n, tsupport (f n) ⊆ Metric.closedBall 0 L) →
      (∀ n, HRS.Whole.weightedSobolevE r P (f n) ≤ 1) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ CauchySeq (fun n => r26t3_jet (r - 2) (P + 2) (f (σ n))) := by
  intro f hf hsupp hE
  obtain ⟨K0, hK0d⟩ : ∃ K0 : ℝ, K0 = (min 1 ((1 + L ^ 2) ^ (-P)))⁻¹ := ⟨_, rfl⟩
  have hbd : ∀ n, ∀ j' ≤ r, ∀ idx : Fin j' → Fin d,
      ∫ x, (HRS.Whole.partialDeriv idx (f n) x) ^ 2 ≤ K0 := fun n j' hj' idx => by
    rw [hK0d]
    exact s21k2_w09_l2_bound ((hf n).1.of_le (s21k2_w09_le_top _)) (hsupp n) (hE n) hj' idx
  have hK0nn : 0 ≤ K0 := by
    rw [hK0d]
    exact inv_nonneg.2 (le_of_lt (lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)))
  have hKle : K0 ≤ ((d : ℝ) + 1) * K0 := by
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hjle : ∀ i : JetIndex d (r - 2), i.1.val ≤ r := fun i => by
    have := i.1.isLt
    omega
  have hjle1 : ∀ i : JetIndex d (r - 2), i.1.val + 1 ≤ r := fun i => by
    have := i.1.isLt
    omega
  obtain ⟨σ, hσ, hc⟩ := s21k2_w09_cauchy_subseq_fin (L := L) (K := ((d : ℝ) + 1) * K0) hL.le
    (Finset.univ : Finset (JetIndex d (r - 2)))
    (fun n i => HRS.Whole.partialDeriv i.2 (f n))
    (fun n i => (s21k2_w09_pd_smooth (hf n).1 i.2).continuous)
    (fun n i => s21k2_w09_pd_cs (hf n).1 i.2 (hsupp n))
    (fun n i => s21k2_w09_supp (r := i.1.val) ((hf n).1.of_le (s21k2_w09_le_top _)) le_rfl i.2 (hsupp n))
    (fun n i => (hbd n i.1.val (hjle i) i.2).trans hKle)
    (fun n i => (s21k2_w09_jet_h1 (r := r) (L := L) (K0 := K0) (hf n).1 (hsupp n) (hbd n) (hjle1 i) i.2).1)
    (fun n i => (s21k2_w09_jet_h1 (r := r) (L := L) (K0 := K0) (hf n).1 (hsupp n) (hbd n) (hjle1 i) i.2).2)
  refine ⟨σ, hσ, ?_⟩
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = (∑ j ∈ Finset.range (r - 2 + 1), (d : ℝ) ^ j) *
      max 1 ((1 + L ^ 2) ^ (-(P + 2))) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCd]
    exact mul_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (Nat.cast_nonneg d) j)
      (le_max_of_le_left zero_le_one)
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = ε ^ 2 / (C + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδd]
    exact div_pos (pow_pos hε 2) (by linarith)
  have hCδ : C * δ < ε ^ 2 := by
    rw [hδd, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith [pow_pos hε 2]
  choose N hN using fun i : JetIndex d (r - 2) => hc i (Finset.mem_univ i) δ hδ
  refine ⟨Finset.univ.sup N, fun m hm n hn => ?_⟩
  refine (s21k2_w09_jet_dist (r := r) (P := P) (L := L) (η := δ) hr (hf (σ m)) (hf (σ n))
    (hsupp (σ m)) (hsupp (σ n)) C hCd hδ.le ?_).trans_lt ?_
  · intro j hj i
    have hi : j < r - 2 + 1 := by omega
    have h := hN ⟨⟨j, hi⟩, i⟩ m ((Finset.le_sup (Finset.mem_univ _)).trans hm)
      n ((Finset.le_sup (Finset.mem_univ _)).trans hn)
    exact h.le
  · exact (Real.sqrt_lt' hε).2 hCδ

end HRS.MS.R26T3
