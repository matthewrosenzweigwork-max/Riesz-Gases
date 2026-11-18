import HRS.MS.Fp81S21WeightedRellich15
import HRS.MS.Fp81S21WeightedRellich16

/-! The cutoff family is totally bounded in the weak weighted jet space.
Combining that finite net with the weighted exterior estimate gives a finite
net for the full strong unit ball. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- Every strong unit-ball weighted test is within `ε` of one of finitely
many weak-jet elements. The centers lie in the weak `L²` jet completion. -/
theorem fp81s21_weightedRellich_unitBall_finiteWeakNet
    {d q : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * (P + 2)) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ ρ : ℝ, 1 ≤ ρ ∧
          ∃ χ : Euc d → ℝ,
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
            (∀ x, ‖x‖ ≤ ρ → χ x = 1) ∧
            (∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0) ∧
            (∀ k ≤ q + 2, ∀ x, ‖iteratedFDeriv ℝ k χ x‖ ≤ C) ∧
            ∃ t : Finset (HRS.MS.R26T3.JetSpace d q (P + 2)),
              (∀ z ∈ t, ∃ g : Euc d → ℝ, IsR2Test g ∧
                weightedSobolevE (q + 2) P g ≤ 1 ∧
                z = HRS.MS.R26T3.r26t3_jet q (P + 2) (fun x => χ x * g x) ∧
                weightedSobolevE (q + 2) P (fun x => χ x * g x) ≤
                  ENNReal.ofReal R) ∧
              ∀ f : Euc d → ℝ, IsR2Test f →
                weightedSobolevE (q + 2) P f ≤ 1 →
                ∃ z ∈ t, dist (HRS.MS.R26T3.r26t3_jet q (P + 2) f) z < ε := by
  classical
  obtain ⟨C, K, hC0, hK, hprofile⟩ :=
    fp81s21_weightedRellich_remainder_profile_correlated (d := d) (q := q) (P := P)
  let R : ℝ :=
    ((Fintype.card (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) + 1) *
      (∑ j ∈ Finset.range (q + 3),
        ∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k))
  have hR0 : 0 ≤ R := by
    dsimp [R]
    apply mul_nonneg
    · positivity
    · refine Finset.sum_nonneg fun j hj => ?_
      exact Finset.sum_nonneg fun k hk => by positivity
  refine ⟨C, R, hC0, hR0, ?_⟩
  intro ε hε
  let δ : ℝ := ε / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  let ρ : ℝ := (N : ℝ)
  have hρ : 1 ≤ ρ := by
    have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (inv_pos.mpr hδ) hN
    have hNnat : 1 ≤ N := by
      have hNpos' : 0 < N := by exact_mod_cast hNpos
      omega
    dsimp [ρ]
    exact_mod_cast hNnat
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hmul : 1 < δ * ρ := by
    have hmul' := mul_lt_mul_of_pos_right hN hδ
    calc
      1 = δ⁻¹ * δ := by field_simp [hδ.ne']
      _ < (N : ℝ) * δ := hmul'
      _ = δ * ρ := by dsimp [ρ]; ring
  have hρinv : ρ⁻¹ < δ := by
    have hdiv : 1 / ρ < δ := (div_lt_iff₀ hρpos).2 (by simpa [mul_comm] using hmul)
    simpa [one_div] using hdiv
  have hpow : ρ ^ (-2 : ℝ) ≤ ρ ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  rw [Real.rpow_neg_one] at hpow
  have hratio : K / (K + 1) < 1 := by
    apply (div_lt_iff₀ (by linarith : 0 < K + 1)).2
    linarith
  have hsmall : K * ρ ^ (-2 : ℝ) < ε / 2 := by
    calc
      K * ρ ^ (-2 : ℝ) ≤ K * ρ⁻¹ := mul_le_mul_of_nonneg_left hpow hK
      _ ≤ K * δ := mul_le_mul_of_nonneg_left hρinv.le hK
      _ = (ε / 2) * (K / (K + 1)) := by
        dsimp [δ]
        field_simp [show (K + 1 : ℝ) ≠ 0 by linarith]
      _ < (ε / 2) * 1 := mul_lt_mul_of_pos_left hratio (by positivity)
      _ = ε / 2 := by ring
  obtain ⟨χ, hχs, hχc, hχone, hχzero, hχB, hremBound⟩ := hprofile ρ hρ
  have htb := fp81s21_weightedRellich_fixedCutoff_totallyBounded
    (d := d) (q := q) (P := P) (ρ := ρ) (C := C)
    hρ hC0 hχs hχc hχone hχzero hχB
  let S : Set (HRS.MS.R26T3.JetSpace d q (P + 2)) :=
    {z | ∃ g : Euc d → ℝ, IsR2Test g ∧
      weightedSobolevE (q + 2) P g ≤ 1 ∧
      z = HRS.MS.R26T3.r26t3_jet q (P + 2) (fun x => χ x * g x)}
  have htbS : TotallyBounded S := by simpa [S] using htb
  obtain ⟨t, htfin, hcov⟩ :=
    (Metric.totallyBounded_iff.1 htbS) (ε / 4) (by positivity)
  let tFin : Finset (HRS.MS.R26T3.JetSpace d q (P + 2)) := htfin.toFinset
  have hcover : ∀ z ∈ S, ∃ y ∈ tFin, dist z y < ε / 4 := by
    intro z hzS
    have hz : z ∈ ⋃ y ∈ t, Metric.ball y (ε / 4) := hcov hzS
    obtain ⟨y, hy, hyball⟩ := Set.mem_iUnion₂.1 hz
    have hyFin : y ∈ tFin := by simpa [tFin] using hy
    rw [Metric.mem_ball] at hyball
    exact ⟨y, hyFin, hyball⟩
  let tGood : Finset (HRS.MS.R26T3.JetSpace d q (P + 2)) :=
    tFin.filter (fun y => ∃ a ∈ S, dist a y < ε / 4)
  have hcenterExists : ∀ y ∈ tGood, ∃ a ∈ S, dist a y < ε / 4 := by
    intro y hy
    have hy' : y ∈ tFin ∧ (∃ a ∈ S, dist a y < ε / 4) := by
      simpa [tGood] using hy
    exact hy'.2
  choose center hcenterS hcenterDist using hcenterExists
  let tCenters : Finset (HRS.MS.R26T3.JetSpace d q (P + 2)) :=
    tGood.attach.image (fun y => center y.1 y.2)
  have hcoverGood : ∀ x ∈ S,
      ∃ z ∈ tCenters, z ∈ S ∧ dist x z < ε / 2 := by
    intro x hx
    obtain ⟨y, hyFin, hxy⟩ := hcover x hx
    have hclose : ∃ a ∈ S, dist a y < ε / 4 := ⟨x, hx, hxy⟩
    have hyGood : y ∈ tGood := by
      apply Finset.mem_filter.mpr
      exact ⟨hyFin, hclose⟩
    let y' : {u : HRS.MS.R26T3.JetSpace d q (P + 2) // u ∈ tGood} := ⟨y, hyGood⟩
    have hy' : y' ∈ tGood.attach := Finset.mem_attach _ _
    let z := center y'.1 y'.2
    have hzT : z ∈ tCenters := by
      exact Finset.mem_image.mpr ⟨y', hy', rfl⟩
    have hzS : z ∈ S := hcenterS y'.1 y'.2
    have hyz : dist z y < ε / 4 := hcenterDist y'.1 y'.2
    refine ⟨z, hzT, hzS, ?_⟩
    calc
      dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ < ε / 2 := by
        rw [← dist_comm z y]
        linarith
  have hcenterBound : ∀ z ∈ tCenters,
      ∃ g : Euc d → ℝ, IsR2Test g ∧
        weightedSobolevE (q + 2) P g ≤ 1 ∧
        z = HRS.MS.R26T3.r26t3_jet q (P + 2) (fun x => χ x * g x) ∧
        weightedSobolevE (q + 2) P (fun x => χ x * g x) ≤ ENNReal.ofReal R := by
    intro z hz
    obtain ⟨y, hyGood, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨g, hg, hgE, hjet⟩ := by
      simpa [S] using hcenterS y.1 y.2
    refine ⟨g, hg, hgE, hjet, ?_⟩
    have hprod := fp81s21_weightedRellich_cutoff_product_energy_le
      (d := d) (q := q) (P := P) (C := C) (χ := χ) (f := g)
      hC0 hχs hg.1 hχB
    have hprod' : weightedSobolevE (q + 2) P (fun x => χ x * g x) ≤
        ENNReal.ofReal R * weightedSobolevE (q + 2) P g := by
      simpa [R] using hprod
    calc
      weightedSobolevE (q + 2) P (fun x => χ x * g x) ≤
          ENNReal.ofReal R * weightedSobolevE (q + 2) P g := hprod'
      _ ≤ ENNReal.ofReal R * 1 := by
        simpa [mul_comm] using
          (mul_le_mul_left hgE (ENNReal.ofReal R))
      _ = ENNReal.ofReal R := by rw [mul_one]
  refine ⟨ρ, hρ, χ, hχs, hχc, hχone, hχzero, hχB,
    tCenters, hcenterBound, ?_⟩
  intro f hf hE
  let g : Euc d → ℝ := fun x => χ x * f x
  let r : Euc d → ℝ := fun x => f x - χ x * f x
  have hg : IsR2Test g := by
    refine ⟨hχs.mul hf.1, ?_⟩
    have hsupp : tsupport g ⊆ Metric.closedBall 0 (2 * ρ) := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      intro x hx
      by_contra hxball
      apply Function.mem_support.1 hx
      have hxnot : ¬ ‖x‖ ≤ 2 * ρ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hxball
      have hxnorm : 2 * ρ ≤ ‖x‖ := le_of_not_ge hxnot
      simp [g, hχzero x hxnorm]
    exact HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Euc d) (2 * ρ))
      ((subset_tsupport g).trans hsupp)
  have hr : IsR2Test r := by
    refine ⟨hf.1.sub (hχs.mul hf.1), hf.2.sub hχc.mul_right⟩
  have hWf : IsR2WeightedTest q (P + 2) f :=
    HRS.MS.ProClosureS111.weightedTestSubmodule_iff.1
      (HRS.MS.ProClosureS111.weighted_test_of_compact_smooth
        (r := q) (Pw := P + 2) hP hf)
  have hWg : IsR2WeightedTest q (P + 2) g :=
    HRS.MS.ProClosureS111.weightedTestSubmodule_iff.1
      (HRS.MS.ProClosureS111.weighted_test_of_compact_smooth
        (r := q) (Pw := P + 2) hP hg)
  have hWr : IsR2WeightedTest q (P + 2) r :=
    HRS.MS.ProClosureS111.weightedTestSubmodule_iff.1
      (HRS.MS.ProClosureS111.weighted_test_of_compact_smooth
        (r := q) (Pw := P + 2) hP hr)
  have hlin := HRS.MS.R26T3.r26t3_jet_linear (P + 2) f g hWf hWg (-1 : ℝ)
  have hfun : f + (-1 : ℝ) • g = r := by
    funext x
    change f x + (-1) * (χ x * f x) = f x - χ x * f x
    ring
  rw [hfun] at hlin
  have hdiff : HRS.MS.R26T3.r26t3_jet q (P + 2) f -
      HRS.MS.R26T3.r26t3_jet q (P + 2) g =
        HRS.MS.R26T3.r26t3_jet q (P + 2) r := by
    simpa [sub_eq_add_neg] using hlin.symm
  have hcoef0 : 0 ≤ K * ρ ^ (-2 : ℝ) :=
    mul_nonneg hK (Real.rpow_nonneg hρpos.le _)
  have hremE : weightedSobolevE q (P + 2) r ≤
      ENNReal.ofReal (K * ρ ^ (-2 : ℝ)) := by
    calc
      weightedSobolevE q (P + 2) r ≤
          ENNReal.ofReal (K * ρ ^ (-2 : ℝ)) *
            weightedSobolevE (q + 2) P f := hremBound f hf.1
      _ ≤ ENNReal.ofReal (K * ρ ^ (-2 : ℝ)) * 1 := by
        simpa [mul_comm] using
          (mul_le_mul_left hE (ENNReal.ofReal (K * ρ ^ (-2 : ℝ))))
      _ = ENNReal.ofReal (K * ρ ^ (-2 : ℝ)) := by rw [mul_one]
  have hdistE : edist
      (HRS.MS.R26T3.r26t3_jet q (P + 2) f)
      (HRS.MS.R26T3.r26t3_jet q (P + 2) g) ≤
        ENNReal.ofReal (K * ρ ^ (-2 : ℝ)) := by
    rw [edist_eq_enorm_sub, hdiff,
      (HRS.MS.R26T3.r26t3_jet_norm (P + 2) r hWr).2]
    exact hremE
  have hdist : dist
      (HRS.MS.R26T3.r26t3_jet q (P + 2) f)
      (HRS.MS.R26T3.r26t3_jet q (P + 2) g) < ε / 2 := by
    rw [dist_edist]
    exact (ENNReal.toReal_le_of_le_ofReal hcoef0 hdistE).trans_lt hsmall
  have hmemS : HRS.MS.R26T3.r26t3_jet q (P + 2) g ∈ S := by
    exact ⟨f, hf, hE, rfl⟩
  obtain ⟨z, hzt, hzS, hzg⟩ := hcoverGood _ hmemS
  refine ⟨z, hzt, ?_⟩
  calc
    dist (HRS.MS.R26T3.r26t3_jet q (P + 2) f) z ≤
        dist (HRS.MS.R26T3.r26t3_jet q (P + 2) f)
            (HRS.MS.R26T3.r26t3_jet q (P + 2) g) +
          dist (HRS.MS.R26T3.r26t3_jet q (P + 2) g) z := dist_triangle _ _ _
    _ < ε := by linarith

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_unitBall_finiteWeakNet

end HRS.Fp81.S21
