import HRS.MS.SuppU6Aux2

/-!
# U6 aux 3: volumes of chart images and the uniform counting lemma
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory Metric

namespace HRS.U6

variable {d : ℕ}

/-- `⟨x⟩ = (1+|x|²)^{1/2}` (definitionally `jbracket`). -/
def u6j (x : EuclideanSpace ℝ (Fin d)) : ℝ := u6w (‖x‖ ^ 2)

lemma u6j_eq (x : EuclideanSpace ℝ (Fin d)) : u6j x = Real.sqrt (1 + ‖x‖ ^ 2) := rfl

lemma u6j_one_le (x : EuclideanSpace ℝ (Fin d)) : 1 ≤ u6j x := u6w_one_le (by positivity)

lemma u6j_pos (x : EuclideanSpace ℝ (Fin d)) : 0 < u6j x := lt_of_lt_of_le one_pos (u6j_one_le x)

lemma u6j_sq (x : EuclideanSpace ℝ (Fin d)) : u6j x ^ 2 = 1 + ‖x‖ ^ 2 := u6w_sq (by positivity)

lemma norm_le_u6j (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ≤ u6j x := by
  have h := u6j_sq x
  have : ‖x‖ ^ 2 ≤ u6j x ^ 2 := by rw [h]; linarith
  exact le_of_sq_le_sq this (u6j_pos x).le

lemma u6j_le_add (x y : EuclideanSpace ℝ (Fin d)) : u6j x ≤ u6j y + ‖x - y‖ := by
  have h1 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    calc ‖x‖ = ‖y + (x - y)‖ := by simp
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
  have h2 : u6j x ^ 2 ≤ (u6j y + ‖x - y‖) ^ 2 := by
    rw [u6j_sq]
    have e1 : ‖x‖ ^ 2 ≤ (‖y‖ + ‖x - y‖) ^ 2 := by gcongr
    have e2 := mul_le_mul_of_nonneg_right (norm_le_u6j y) (norm_nonneg (x - y))
    nlinarith [u6j_sq y]
  exact le_of_sq_le_sq h2 (by have := u6j_pos y; positivity)

lemma u6j_le_mul (x y : EuclideanSpace ℝ (Fin d)) : u6j x ≤ (1 + ‖x - y‖) * u6j y := by
  have := u6j_le_add x y
  have h1 := u6j_one_le y
  nlinarith [norm_nonneg (x - y)]

lemma u6_vol_real (p : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (u6F p '' closedBall 0 r) =
      (1 / u6j p) * (r ^ d * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
  have h1 : u6F p '' closedBall (0 : EuclideanSpace ℝ (Fin d)) r =
      (fun v => -p + v) ⁻¹' ((u6A p) '' closedBall 0 r) := by
    rw [← Set.image_add_left]
    rw [Set.image_image]
    rfl
  rw [h1, measureReal_def, measure_preimage_add, Measure.addHaar_image_continuousLinearMap]
  have hdet := u6_det p
  have : |LinearMap.det (u6A p : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
      1 / u6j p := by
    rw [hdet]
    exact abs_of_nonneg (by have := u6j_pos p; positivity)
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := u6j_pos p; positivity),
    ← measureReal_def, Measure.addHaar_real_closedBall' volume _ hr, finrank_euclideanSpace_fin]

lemma u6_ballvol_pos : 0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_closedBall_pos volume _ one_pos).ne'
    measure_closedBall_lt_top.ne

lemma u6_not_sep_of_overlap {ρ ε : ℝ} (h1 : 2 * ρ < ε) (h2 : 2 * (2 * ρ + ρ ^ 2) < ε)
    {x y u v : EuclideanSpace ℝ (Fin d)} (hxy : u6F x u = u6F y v) (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ) :
    ¬ u6Sep ε x y := by
  intro h
  have hρ : 0 ≤ ρ := (norm_nonneg u).trans hu
  have a1 := norm_u6F_sub_le x u
  have a2 := norm_u6F_sub_le y v
  have b1 := abs_normsq_u6F x u
  have b2 := abs_normsq_u6F y v
  rw [hxy] at a1 b1
  have c1 : ‖x - y‖ ≤ 2 * ρ := by
    have : x - y = -(u6F y v - x) + (u6F y v - y) := by abel
    rw [this]
    calc _ ≤ ‖-(u6F y v - x)‖ + ‖u6F y v - y‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by rw [norm_neg]; linarith
  have c2 : |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ 2 * (2 * ρ + ρ ^ 2) := by
    have e : ‖x‖ ^ 2 - ‖y‖ ^ 2 = -(‖u6F y v‖ ^ 2 - ‖x‖ ^ 2) + (‖u6F y v‖ ^ 2 - ‖y‖ ^ 2) := by ring
    rw [e]
    have f1 : 2 * ‖u‖ + ‖u‖ ^ 2 ≤ 2 * ρ + ρ ^ 2 := by gcongr
    have f2 : 2 * ‖v‖ + ‖v‖ ^ 2 ≤ 2 * ρ + ρ ^ 2 := by gcongr
    calc _ ≤ |-(‖u6F y v‖ ^ 2 - ‖x‖ ^ 2)| + |‖u6F y v‖ ^ 2 - ‖y‖ ^ 2| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith
  rcases h with h | h <;> linarith

/-- Two charts meeting at a point: centre distance and radial-coordinate bounds. -/
lemma u6_pair_bounds {k p u w : EuclideanSpace ℝ (Fin d)} (h : u6F k u = u6F p w) :
    ‖k - p‖ ≤ ‖u‖ + ‖w‖ ∧
      |‖k‖ ^ 2 - ‖p‖ ^ 2| ≤ (2 * ‖u‖ + ‖u‖ ^ 2) + (2 * ‖w‖ + ‖w‖ ^ 2) := by
  have a1 := norm_u6F_sub_le k u
  have a2 := norm_u6F_sub_le p w
  have b1 := abs_normsq_u6F k u
  have b2 := abs_normsq_u6F p w
  rw [h] at a1 b1
  refine ⟨?_, ?_⟩
  · have : k - p = -(u6F p w - k) + (u6F p w - p) := by abel
    rw [this]
    calc _ ≤ ‖-(u6F p w - k)‖ + ‖u6F p w - p‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_neg]; linarith
  · have e : ‖k‖ ^ 2 - ‖p‖ ^ 2 = -(‖u6F p w‖ ^ 2 - ‖k‖ ^ 2) + (‖u6F p w‖ ^ 2 - ‖p‖ ^ 2) := by ring
    rw [e]
    calc _ ≤ |-(‖u6F p w‖ ^ 2 - ‖k‖ ^ 2)| + |‖u6F p w‖ ^ 2 - ‖p‖ ^ 2| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith

/-- The uniform counting lemma. -/
lemma u6_count {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : S.Pairwise (u6Sep ε)) (R R0 : ℝ) (hR : 0 ≤ R) (hR0 : 0 ≤ R0) :
    ∃ K : ℕ, ∀ (p : EuclideanSpace ℝ (Fin d)) (T : Finset (EuclideanSpace ℝ (Fin d))),
      (↑T : Set (EuclideanSpace ℝ (Fin d))) ⊆ S →
      (∀ k ∈ T, ∃ u v, ‖u‖ ≤ R ∧ ‖v‖ ≤ R0 ∧ u6F k u = u6F p v) → T.card ≤ K := by
  set ρ : ℝ := ε / 8 with hρdef
  have hρ : 0 < ρ := by positivity
  set r1 : ℝ := R + R0 with hr1
  set r2 : ℝ := (2 * R + R ^ 2) + (2 * R0 + R0 ^ 2) with hr2
  set r : ℝ := ρ + r1 with hr
  set t : ℝ := (2 * ρ + ρ ^ 2) + r2 with ht
  set R3 : ℝ := r + (t + r ^ 2) / 2 with hR3
  have hr1' : 0 ≤ r1 := by positivity
  have hr2' : 0 ≤ r2 := by positivity
  have hR3' : 0 ≤ R3 := by positivity
  refine ⟨⌈(1 + r1) * (R3 / ρ) ^ d⌉₊, fun p T hTS hTov => ?_⟩
  set V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) with hV
  have hVpos : 0 < V := u6_ballvol_pos
  let B : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun k => u6F k '' closedBall 0 ρ
  have hBcomp : ∀ k, IsCompact (B k) := fun k =>
    (isCompact_closedBall _ _).image (continuous_u6F k)
  have hdisj : Set.PairwiseDisjoint (↑T : Set (EuclideanSpace ℝ (Fin d))) B := by
    intro k hk k' hk' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨u, hu, rfl⟩ ⟨v, hv, hyv⟩
    have hu' : ‖u‖ ≤ ρ := by simpa using hu
    have hv' : ‖v‖ ≤ ρ := by simpa using hv
    exact u6_not_sep_of_overlap (ε := ε) (ρ := ρ) (by rw [hρdef]; linarith)
      (by rw [hρdef]; nlinarith) hyv.symm hu' hv' (hS (hTS hk) (hTS hk') hne)
  have hsub : ∀ k ∈ T, B k ⊆ u6F p '' closedBall 0 R3 := by
    intro k hk y hy
    obtain ⟨v, hv, rfl⟩ := hy
    have hv' : ‖v‖ ≤ ρ := by simpa using hv
    obtain ⟨u, w, hu, hw, huw⟩ := hTov k hk
    obtain ⟨q1, q2⟩ := u6_pair_bounds huw
    have a1 := norm_u6F_sub_le k v
    have b1 := abs_normsq_u6F k v
    have g1 : ‖u6F k v - p‖ ≤ r := by
      have : u6F k v - p = (u6F k v - k) + (k - p) := by abel
      rw [this]
      calc _ ≤ ‖u6F k v - k‖ + ‖k - p‖ := norm_add_le _ _
        _ ≤ r := by rw [hr, hr1]; linarith
    have g2 : |‖u6F k v‖ ^ 2 - ‖p‖ ^ 2| ≤ t := by
      have e : ‖u6F k v‖ ^ 2 - ‖p‖ ^ 2 = (‖u6F k v‖ ^ 2 - ‖k‖ ^ 2) + (‖k‖ ^ 2 - ‖p‖ ^ 2) := by ring
      rw [e]
      have f1 : 2 * ‖v‖ + ‖v‖ ^ 2 ≤ 2 * ρ + ρ ^ 2 := by gcongr
      have f2 : 2 * ‖u‖ + ‖u‖ ^ 2 ≤ 2 * R + R ^ 2 := by gcongr
      have f3 : 2 * ‖w‖ + ‖w‖ ^ 2 ≤ 2 * R0 + R0 ^ 2 := by gcongr
      calc _ ≤ |‖u6F k v‖ ^ 2 - ‖k‖ ^ 2| + |‖k‖ ^ 2 - ‖p‖ ^ 2| := abs_add_le _ _
        _ ≤ t := by rw [ht, hr2]; linarith
    refine ⟨u6Fi p (u6F k v), ?_, u6F_Fi p _⟩
    rw [mem_closedBall, dist_zero_right]
    refine (norm_u6Fi_le p _).trans ?_
    rw [hR3]
    have := norm_nonneg (u6F k v - p)
    have h5 : ‖u6F k v - p‖ ^ 2 ≤ r ^ 2 := by gcongr
    linarith
  have hunion : volume.real (⋃ k ∈ T, B k) = ∑ k ∈ T, volume.real (B k) :=
    measureReal_biUnion_finset hdisj (fun k _ => (hBcomp k).isClosed.measurableSet)
      (fun k _ => (hBcomp k).measure_lt_top.ne)
  have hBvol : ∀ k ∈ T, (1 / ((1 + r1) * u6j p)) * (ρ ^ d * V) ≤ volume.real (B k) := by
    intro k hk
    show _ ≤ volume.real (u6F k '' closedBall 0 ρ)
    rw [u6_vol_real k hρ.le]
    obtain ⟨u, w, hu, hw, huw⟩ := hTov k hk
    obtain ⟨q1, q2⟩ := u6_pair_bounds huw
    have h1 : u6j k ≤ (1 + r1) * u6j p := by
      refine (u6j_le_mul k p).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (u6j_pos p).le
      rw [hr1]; linarith
    have hpos := u6j_pos k
    have : 1 / ((1 + r1) * u6j p) ≤ 1 / u6j k := by
      apply one_div_le_one_div_of_le hpos h1
    have : 0 ≤ ρ ^ d * V := by positivity
    gcongr
  have hbig : volume.real (⋃ k ∈ T, B k) ≤ volume.real (u6F p '' closedBall 0 R3) := by
    apply measureReal_mono
    · exact Set.iUnion₂_subset (fun k hk => hsub k hk)
    · exact (((isCompact_closedBall _ _).image (continuous_u6F p)).measure_lt_top).ne
  rw [u6_vol_real p hR3'] at hbig
  have hsum : (T.card : ℝ) * ((1 / ((1 + r1) * u6j p)) * (ρ ^ d * V)) ≤
      ∑ k ∈ T, volume.real (B k) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hBvol
  have hjp := u6j_pos p
  have key : ((T.card : ℝ) * ρ ^ d) * (V / ((1 + r1) * u6j p)) ≤
      ((1 + r1) * R3 ^ d) * (V / ((1 + r1) * u6j p)) := by
    have h1 := hsum.trans (hunion ▸ hbig)
    have e1 : ((T.card : ℝ) * ρ ^ d) * (V / ((1 + r1) * u6j p)) =
        (T.card : ℝ) * ((1 / ((1 + r1) * u6j p)) * (ρ ^ d * V)) := by ring
    have e2 : ((1 + r1) * R3 ^ d) * (V / ((1 + r1) * u6j p)) =
        1 / u6j p * (R3 ^ d * V) := by
      field_simp
    rw [e1, e2]
    exact h1
  have key2 := le_of_mul_le_mul_right key (by positivity)
  have key3 : (T.card : ℝ) ≤ (1 + r1) * (R3 / ρ) ^ d := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    exact key2
  exact_mod_cast key3.trans (Nat.le_ceil _)

end HRS.U6
