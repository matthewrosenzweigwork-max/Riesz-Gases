import HRS.MC.WinJSpecDefs

/-!
# WJ1: P1 `p1_vprop_compare_op` (operator comparison of the propagators at every level `σ ≥ r`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section P1Helpers

open HRS.MC.Sec7.PIE HRS.MC.E214K HRS.MC.Sec7.S7PIDI

variable {d : ℕ}

/-- coordinates of a scaled mode vector -/
lemma p_wj1_coord_modeVec (a : ℝ) (j k : NonzeroLattice d) :
    NegSobolev.coord (modeVec a j) k = Lattice.jp k.1 ^ (-a) * (if k = j then 1 else 0) := by
  have h := HRS.MC.Sec7.S7PIDM.S7PIDM_fc_modeVec a j k
  unfold NegSobolev.fourierCoeff at h
  have hk : 0 < Lattice.jp k.1 := Torus.jp_pos k.1
  have hmm : Lattice.jp k.1 ^ (-a) * Lattice.jp k.1 ^ a = 1 := by
    rw [← Real.rpow_add hk]; simp
  calc NegSobolev.coord (modeVec a j) k
      = (Lattice.jp k.1 ^ (-a) * Lattice.jp k.1 ^ a) * NegSobolev.coord (modeVec a j) k := by
        rw [hmm, one_mul]
    _ = Lattice.jp k.1 ^ (-a) * (Lattice.jp k.1 ^ a * NegSobolev.coord (modeVec a j) k) := by ring
    _ = _ := by rw [h]

/-- **operator bound ⟹ finite-section bound of the matrix** (the converse of `pie_dual`):
if `Δ : E_a → E_a` has norm `≤ M` and `T j k = Δ(e_j)^(k)`, then `w^a T w^{-a}` has finite sections `≤ M`. -/
lemma p_wj1_finBd_of_op {a M : ℝ} (hM : 0 ≤ M) (Δ : NegSobolev d a →L[ℝ] NegSobolev d a)
    (hΔ : ‖Δ‖ ≤ M) (T : NonzeroLattice d → NonzeroLattice d → ℝ)
    (hT : ∀ j k, T j k = NegSobolev.fourierCoeff (Δ (modeVec a j)) k) :
    pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) T a) M := by
  classical
  intro K J x
  set S := pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) T a with hS
  set y : NonzeroLattice d → ℝ := fun j => ∑ k ∈ K, S j k * x k with hy
  set Y : NegSobolev d a := ∑ j ∈ J, (y j * Lattice.jp j.1 ^ a) • modeVec a j with hY
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hww : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ a * Lattice.jp k.1 ^ (-a) = 1 := fun k => by
    rw [← Real.rpow_add (hw k)]; simp
  have hcsum : ∀ (s : Finset (NonzeroLattice d)) (F : NonzeroLattice d → NegSobolev d a)
      (k : NonzeroLattice d), NegSobolev.coord (∑ i ∈ s, F i) k = ∑ i ∈ s, NegSobolev.coord (F i) k := by
    intro s F k
    induction s using Finset.induction_on with
    | empty => rfl
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl
  have hcY : ∀ i, NegSobolev.coord Y i = if i ∈ J then y i else 0 := by
    intro i
    rw [hY, hcsum]
    have h1 : ∀ j ∈ J, NegSobolev.coord ((y j * Lattice.jp j.1 ^ a) • modeVec a j) i =
        if i = j then y i else 0 := by
      intro j _
      show (y j * Lattice.jp j.1 ^ a) * NegSobolev.coord (modeVec a j) i = _
      rw [p_wj1_coord_modeVec]
      by_cases hij : i = j
      · subst hij
        simp only [ite_true]
        calc y i * Lattice.jp i.1 ^ a * (Lattice.jp i.1 ^ (-a) * 1)
            = y i * (Lattice.jp i.1 ^ a * Lattice.jp i.1 ^ (-a)) := by ring
          _ = y i := by rw [hww]; ring
      · simp [hij]
    rw [Finset.sum_congr rfl h1]
    by_cases hi : i ∈ J
    · simp [Finset.sum_ite_eq, hi]
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j hj => ?_
      have : i ≠ j := fun h => hi (h ▸ hj)
      simp [this]
  -- the norm of `Y`
  have hYn : ‖Y‖ ^ 2 = ∑ j ∈ J, y j ^ 2 := by
    obtain ⟨-, hn⟩ := NegSobolev.coord_sq Y
    rw [hn]
    have : ∀ i, NegSobolev.coord Y i ^ 2 = if i ∈ J then y i ^ 2 else 0 := fun i => by
      rw [hcY]; split_ifs <;> simp
    simp_rw [this]
    rw [tsum_eq_sum (s := J) (fun i hi => by simp [hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [hi]
  -- the coordinates of `Δ Y`
  have hcΔ : ∀ k, NegSobolev.coord (Δ Y) k = ∑ j ∈ J, y j * S j k := by
    intro k
    rw [hY, map_sum, hcsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    show (y j * Lattice.jp j.1 ^ a) * NegSobolev.coord (Δ (modeVec a j)) k = _
    have hfc : NegSobolev.coord (Δ (modeVec a j)) k =
        Lattice.jp k.1 ^ (-a) * NegSobolev.fourierCoeff (Δ (modeVec a j)) k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add (hw k)]; simp
    rw [hfc, ← hT j k, hS]
    simp only [pieWmat]
    ring
  -- duality
  set P : ℝ := ∑ j ∈ J, y j ^ 2 with hP
  set X : ℝ := ∑ k ∈ K, x k ^ 2 with hX
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hQ : P = ∑ k ∈ K, x k * NegSobolev.coord (Δ Y) k := by
    calc P = ∑ j ∈ J, y j * y j := Finset.sum_congr rfl fun j _ => sq (y j)
      _ = ∑ j ∈ J, y j * ∑ k ∈ K, S j k * x k := rfl
      _ = ∑ j ∈ J, ∑ k ∈ K, y j * (S j k * x k) := by simp_rw [Finset.mul_sum]
      _ = ∑ k ∈ K, ∑ j ∈ J, y j * (S j k * x k) := Finset.sum_comm
      _ = ∑ k ∈ K, x k * ∑ j ∈ J, y j * S j k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by simp_rw [hcΔ]
  have hC : ∑ k ∈ K, NegSobolev.coord (Δ Y) k ^ 2 ≤ M ^ 2 * P := by
    obtain ⟨hs, hn⟩ := NegSobolev.coord_sq (Δ Y)
    have h1 : ∑ k ∈ K, NegSobolev.coord (Δ Y) k ^ 2 ≤ ‖Δ Y‖ ^ 2 := by
      rw [hn]; exact hs.sum_le_tsum K (fun k _ => sq_nonneg _)
    have h2 : ‖Δ Y‖ ≤ M * ‖Y‖ := (Δ.le_opNorm Y).trans (mul_le_mul_of_nonneg_right hΔ (norm_nonneg _))
    have h3 : ‖Δ Y‖ ^ 2 ≤ (M * ‖Y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc _ ≤ ‖Δ Y‖ ^ 2 := h1
      _ ≤ (M * ‖Y‖) ^ 2 := h3
      _ = M ^ 2 * P := by rw [mul_pow, hYn]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq K x (fun k => NegSobolev.coord (Δ Y) k)
  rw [← hQ] at hCS
  have hP2 : P ^ 2 ≤ X * (M ^ 2 * P) :=
    hCS.trans (mul_le_mul_of_nonneg_left hC hX0)
  show P ≤ M ^ 2 * X
  rcases hP0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : P * P ≤ (M ^ 2 * X) * P := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- the matrix of a dual evolution applied to the mode vectors is `pieT` -/
lemma p_wj1_fc_dual {a : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (V : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a) (hdual : IsDualEvolution D ρ a V)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (j k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (V t u (modeVec a j)) k = pieT D ρ u t j k :=
  fc_vev_modeVec D ρ V hdual hu hut j k

/-- finite-section bound of the matrix `pieT` of a dual evolution from its operator norm -/
lemma p_wj1_finBd_dual {a : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (V : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a) (hdual : IsDualEvolution D ρ a V)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D ρ u t) a) ‖V t u‖ :=
  p_wj1_finBd_of_op (norm_nonneg _) (V t u) le_rfl _ fun j k => (p_wj1_fc_dual D ρ V hdual hu hut j k).symm

/-- finite-section bound of the DIFFERENCE of the matrices of two dual evolutions (same dynamics) -/
lemma p_wj1_finBd_dual_sub {a M : ℝ} (hM : 0 ≤ M) (D : DynData d) (ρ ρ' : ℝ → Torus d → ℝ)
    (V W : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a) (hV : IsDualEvolution D ρ a V)
    (hW : IsDualEvolution D ρ' a W) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (hb : ‖V t u - W t u‖ ≤ M) :
    pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => pieT D ρ u t j k - pieT D ρ' u t j k) a) M := by
  refine p_wj1_finBd_of_op hM (V t u - W t u) hb _ fun j k => ?_
  rw [ContinuousLinearMap.sub_apply, fc_sub', p_wj1_fc_dual D ρ V hV hu hut,
    p_wj1_fc_dual D ρ' W hW hu hut]

/-- interpolation of a finite-section bound between two real levels -/
lemma p_wj1_interp {T : NonzeroLattice d → NonzeroLattice d → ℝ} {j1 j2 σ A1 A2 : ℝ} (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) (h1 : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) T j1) A1)
    (h2 : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) T j2) A2) (hj : j1 < j2)
    (hs1 : j1 ≤ σ) (hs2 : σ ≤ j2) :
    ∃ A : ℝ, 0 ≤ A ∧ pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) T σ) A ∧
      (A1 = A2 → A = A1) := by
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hd : 0 < j2 - j1 := by linarith
  set θ : ℝ := (σ - j1) / (j2 - j1) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : θ ≤ 1 := (div_le_one hd).2 (by linarith)
  have hint := pie_interp hw hA1 hA2 h1 h2 hθ0 hθ1
  have hσ : (1 - θ) * j1 + θ * j2 = σ := by
    simp only [hθ]; field_simp; ring
  rw [hσ] at hint
  refine ⟨A1 ^ (1 - θ) * A2 ^ θ, mul_nonneg (Real.rpow_nonneg hA1 _) (Real.rpow_nonneg hA2 _), hint, ?_⟩
  intro h
  rw [← h, ← Real.rpow_add' hA1 (by rw [sub_add_cancel]; exact one_ne_zero)]
  simp

/-- the difference of two `V^{t,u}` is bounded on `E_σ` by the finite-section bound of the difference matrix -/
lemma p_wj1_op_of_finBd_sub {σ A A1 A2 : ℝ} (D : DynData d) (μ μ' : ℝ → Torus d → ℝ) (t u : ℝ)
    (hA : 0 ≤ A) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h1 : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) σ) A1)
    (h2 : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ' u t) σ) A2)
    (h : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => pieT D μ u t j k - pieT D μ' u t j k) σ) A) (F : NegSobolev d σ) :
    ‖Vprop D μ σ t u F - Vprop D μ' σ t u F‖ ≤ A * ‖F‖ := by
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hcoord : ∀ j, Lattice.jp j.1 ^ (-σ) * NegSobolev.fourierCoeff F j = NegSobolev.coord F j := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (hw j)]; simp
  obtain ⟨hF2, hFn⟩ := NegSobolev.coord_sq F
  have ha : Summable fun j : NonzeroLattice d =>
      (Lattice.jp j.1 ^ (-σ) * NegSobolev.fourierCoeff F j) ^ 2 :=
    hF2.congr fun j => by rw [hcoord]
  have hs1 := fun k => pie_row_summable hw h1 (fun j => NegSobolev.fourierCoeff F j) ha k
  have hs2 := fun k => pie_row_summable hw h2 (fun j => NegSobolev.fourierCoeff F j) ha k
  obtain ⟨hs, hle⟩ := pie_dual hw hA h (fun j => NegSobolev.fourierCoeff F j) ha
  have hcV : ∀ k, NegSobolev.coord (Vprop D μ σ t u F - Vprop D μ' σ t u F) k =
      Lattice.jp k.1 ^ (-σ) * ∑' j, NegSobolev.fourierCoeff F j * (pieT D μ u t j k - pieT D μ' u t j k) := by
    intro k
    have e : NegSobolev.coord (Vprop D μ σ t u F - Vprop D μ' σ t u F) k =
        NegSobolev.coord (Vprop D μ σ t u F) k - NegSobolev.coord (Vprop D μ' σ t u F) k := rfl
    rw [e, pie_Vprop_coord D μ σ t u hA1 h1 F k, pie_Vprop_coord D μ' σ t u hA2 h2 F k, ← mul_sub,
      ← Summable.tsum_sub (hs1 k) (hs2 k)]
    congr 1
    exact tsum_congr fun j => by ring
  obtain ⟨hV2, hVn⟩ := NegSobolev.coord_sq (Vprop D μ σ t u F - Vprop D μ' σ t u F)
  have h1' : ‖Vprop D μ σ t u F - Vprop D μ' σ t u F‖ ^ 2 ≤ (A * ‖F‖) ^ 2 := by
    rw [hVn, mul_pow, hFn]
    calc ∑' k, NegSobolev.coord (Vprop D μ σ t u F - Vprop D μ' σ t u F) k ^ 2
        = ∑' k, (Lattice.jp k.1 ^ (-σ) * ∑' j, NegSobolev.fourierCoeff F j *
            (pieT D μ u t j k - pieT D μ' u t j k)) ^ 2 :=
          tsum_congr fun k => by rw [hcV]
      _ ≤ A ^ 2 * ∑' j, (Lattice.jp j.1 ^ (-σ) * NegSobolev.fourierCoeff F j) ^ 2 := hle
      _ = A ^ 2 * ∑' j, NegSobolev.coord F j ^ 2 := by
          congr 1; exact tsum_congr fun j => by rw [hcoord]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hA (norm_nonneg _)) two_ne_zero).1 h1'

/-- **Core (shift `b = 0`)**: operator comparison of the prepared and stationary propagators at a real level
`σ ≥ rLvl d`, uniformly in `0 ≤ u ≤ t`. -/
theorem p_wj1_core (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (hth : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (σ : ℝ) (hσ : rLvl d ≤ σ) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F : NegSobolev d σ,
      ‖Vprop S.dyn S.ρ σ t u F - Vprop S.dyn (fun _ => ρβ) σ t u F‖ ≤
        C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) * ‖F‖ := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast S.hd
  have hrl : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hm0 : 0 ≤ (σ - 1) / 2 := by rw [hrl] at hσ; linarith
  set n : ℕ := ⌊(σ - 1) / 2⌋₊ with hn
  have hn1 : (n : ℝ) ≤ (σ - 1) / 2 := Nat.floor_le hm0
  have hn2 : (σ - 1) / 2 < n + 1 := Nat.lt_floor_add_one _
  set j1 : ℕ := 2 * n with hj1
  set j2 : ℕ := 2 * n + 4 with hj2
  have hj1r : (j1 : ℝ) = 2 * n := by rw [hj1]; push_cast; ring
  have hj2r : (j2 : ℝ) = 2 * n + 4 := by rw [hj2]; push_cast; ring
  have hj1m : (j1 : ℝ) < σ := by rw [hj1r]; linarith
  have hmj2 : σ < (j2 : ℝ) := by rw [hj2r]; linarith
  have hj1d : (d : ℝ) / 2 + 4 < j1 := by rw [hj1r]; rw [hrl] at hσ; linarith
  have hj2d : (d : ℝ) / 2 + 4 < j2 := by rw [hj2r]; rw [hrl] at hσ; linarith
  have hev1 : Even j1 := even_two_mul n
  have hev2 : Even j2 := ⟨n + 2, by rw [hj2]; ring⟩
  obtain ⟨C1, c1, κ1, hC1, hc1, hκ1, hcmp1⟩ := compare_level_at S hth (j1 : ℝ) j1 hev1 hj1d rfl
  obtain ⟨C2, c2, κ2, hC2, hc2, hκ2, hcmp2⟩ := compare_level_at S hth (j2 : ℝ) j2 hev2 hj2d rfl
  obtain ⟨VR1, Wc1, hVR1, hWc1⟩ := exists_dual S hth (j1 : ℝ)
  obtain ⟨VR2, Wc2, hVR2, hWc2⟩ := exists_dual S hth (j2 : ℝ)
  refine ⟨max C1 C2, min c1 c2, min κ1 κ2, lt_max_of_lt_left hC1, lt_min hc1 hc2, lt_min hκ1 hκ2,
    fun u t hu hut F => ?_⟩
  set M : ℝ := max C1 C2 * Real.exp (-(min c1 c2) * (t - u)) * Real.exp (-(min κ1 κ2) * u) with hM
  have hM0 : 0 ≤ M := by positivity
  have hx : 0 ≤ t - u := sub_nonneg.2 hut
  have hmono : ∀ (Ci ci κi : ℝ), 0 ≤ Ci → Ci ≤ max C1 C2 → min c1 c2 ≤ ci → min κ1 κ2 ≤ κi →
      Ci * Real.exp (-ci * (t - u)) * Real.exp (-κi * u) ≤ M := by
    intro Ci ci κi hCi hC hc hκ
    have e1 : Real.exp (-ci * (t - u)) ≤ Real.exp (-(min c1 c2) * (t - u)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have e2 : Real.exp (-κi * u) ≤ Real.exp (-(min κ1 κ2) * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul (mul_le_mul hC e1 (Real.exp_pos _).le (hCi.trans hC)) e2 (Real.exp_pos _).le
      (by positivity)
  have hb1 : ‖VR1 t u - Wc1 t u‖ ≤ M :=
    (hcmp1 u t hu hut VR1 Wc1 hVR1 hWc1).trans
      (hmono C1 c1 κ1 hC1.le (le_max_left _ _) (min_le_left _ _) (min_le_left _ _))
  have hb2 : ‖VR2 t u - Wc2 t u‖ ≤ M :=
    (hcmp2 u t hu hut VR2 Wc2 hVR2 hWc2).trans
      (hmono C2 c2 κ2 hC2.le (le_max_right _ _) (min_le_right _ _) (min_le_right _ _))
  have hj12 : (j1 : ℝ) < j2 := hj1m.trans hmj2
  -- finite-section bounds at the two integer levels
  have hd1 := p_wj1_finBd_dual_sub hM0 S.dyn S.ρ (fun _ => ρβ) VR1 Wc1 hVR1 hWc1 hu hut hb1
  have hd2' := p_wj1_finBd_dual_sub hM0 S.dyn S.ρ (fun _ => ρβ) VR2 Wc2 hVR2 hWc2 hu hut hb2
  obtain ⟨A, hA0, hA, hAe⟩ := p_wj1_interp hM0 hM0 hd1 hd2' hj12 hj1m.le hmj2.le
  have hAM : A = M := hAe rfl
  obtain ⟨A1, hA10, hA1, -⟩ := p_wj1_interp (norm_nonneg (VR1 t u)) (norm_nonneg (VR2 t u))
    (p_wj1_finBd_dual S.dyn S.ρ VR1 hVR1 hu hut) (p_wj1_finBd_dual S.dyn S.ρ VR2 hVR2 hu hut)
    hj12 hj1m.le hmj2.le
  obtain ⟨A2, hA20, hA2, -⟩ := p_wj1_interp (norm_nonneg (Wc1 t u)) (norm_nonneg (Wc2 t u))
    (p_wj1_finBd_dual S.dyn (fun _ => ρβ) Wc1 hWc1 hu hut)
    (p_wj1_finBd_dual S.dyn (fun _ => ρβ) Wc2 hWc2 hu hut) hj12 hj1m.le hmj2.le
  have := p_wj1_op_of_finBd_sub S.dyn S.ρ (fun _ => ρβ) t u hA0 hA10 hA20 hA1 hA2 hA F
  rw [hAM] at this
  exact this

end P1Helpers

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

/-- **P1**.  See `HRS/MC/WinJSpec.lean`. -/
theorem p1_vprop_compare_op (sd : StatDatum S β₀ m hE) (σ : ℝ) (hσ : rLvl d ≤ σ) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (u t : ℝ), 0 ≤ u → u ≤ t →
      ∀ F : NegSobolev d σ,
        ‖Vprop (Rp sd b hb).D (Rp sd b hb).ρ σ t u F - Vprop (Rs sd b hb).D (Rs sd b hb).ρ σ t u F‖ ≤
          C * Real.exp (-c * (t - u)) * Real.exp (-κ * (b + u)) * ‖F‖ := by
  obtain ⟨C, c, κ, hC, hc, hκ, h⟩ := p_wj1_core S (HRS.MC.E214K.regime_thermal S β₀ hE) σ hσ
  refine ⟨C, c, κ, hC, hc, hκ, fun b hb u t hu hut F => ?_⟩
  have e1 : Vprop (Rp sd b hb).D (Rp sd b hb).ρ σ t u = Vprop S.dyn S.ρ σ (b + t) (b + u) :=
    u3_vprop_shift (regime S β₀ hE) σ b hb hu hut
  have e2 : Vprop (Rs sd b hb).D (Rs sd b hb).ρ σ t u =
      Vprop S.dyn (fun _ => (regime S β₀ hE).ρβ) σ (b + t) (b + u) := by
    calc Vprop (Rs sd b hb).D (Rs sd b hb).ρ σ t u
        = Vprop (regime sd.Ss S.β sd.hEs).D (regime sd.Ss S.β sd.hEs).ρ σ (b + t) (b + u) :=
          u3_vprop_shift (regime sd.Ss S.β sd.hEs) σ b hb hu hut
      _ = _ := by rw [sd.hD, sd.hρ]; rfl
  rw [e1, e2]
  have := h (b + u) (b + t) (by linarith) (by linarith) F
  have e3 : b + t - (b + u) = t - u := by ring
  rw [e3] at this
  exact this

end HRS.MC.WinJ

end
