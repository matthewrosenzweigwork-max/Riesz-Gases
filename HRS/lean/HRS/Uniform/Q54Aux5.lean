import HRS.Uniform.Q54Aux4

/-!
# Q54, part 5: decay of the entries of the Fourier matrix of the forward generator

Coefficient hypotheses `GenHyp`: entrywise decay `‖μ̂(m)‖ ≤ Bμ ⟨m⟩^{-K}`, `‖V̂(m)‖ ≤ BV ⟨m⟩^{-(K+1)}`, `|M_{ij}| ≤ MB`,
`D.s = s`.  Then `‖genEntry D μ k l‖ ≤ A ⟨k-l⟩^{-(K-1-e)} ⟨l⟩^{1+e}`, `e = max(s-d+1, 0)`, so the order
`θ' = 1 + e = max(1, s+2-d) < 2`.
-/

noncomputable section

open Finset

namespace HRS.Uniform.Q54

open HRS HRS.PDE

variable {d : ℕ}

/-- The coefficient hypotheses. -/
structure GenHyp (d : ℕ) (s K MB Bμ BV : ℝ) (D : DynData d) (μ : Torus d → ℝ) : Prop where
  hs : D.s = s
  hM : ∀ i j, |D.M i j| ≤ MB
  hμ : ∀ m, ‖coeffOf μ m‖ ≤ Bμ * Lattice.jp m ^ (-K)
  hV : ∀ m, ‖coeffOf D.V m‖ ≤ BV * Lattice.jp m ^ (-(K + 1))

/-- the constant `c_{d,s}`-bound of `ĝ`. -/
def Cg (d : ℕ) (s : ℝ) : ℝ := |rieszConst d s| * (2 : ℝ) ^ (((d : ℝ) - s) / 2)

theorem Cg_nonneg (d : ℕ) (s : ℝ) : 0 ≤ Cg d s := by unfold Cg; positivity

theorem abs_rieszCoeff_le_jp (s : ℝ) (hsd : s < d) (k : Lattice d) :
    |rieszCoeff d s k| ≤ Cg d s * Lattice.jp k ^ (s - d) := by
  by_cases hk : k = 0
  · have : rieszCoeff d s k = 0 := by simp [rieszCoeff, hk]
    rw [this, abs_zero]
    exact mul_nonneg (Cg_nonneg d s) (Real.rpow_nonneg (Torus.jp_pos k).le _)
  · have h1 : 1 ≤ Lattice.enorm k := HRS.one_le_enorm k hk
    set r : ℝ := 2 * Real.pi * Lattice.enorm k with hr
    have hr1 : 1 ≤ r := by nlinarith [Real.pi_gt_three]
    have hr0 : 0 < r := by linarith
    have hjp : Lattice.jp k = Real.sqrt (1 + r ^ 2) := by
      unfold Lattice.jp; congr 1; rw [hr]; ring
    have hjpr : Lattice.jp k ≤ Real.sqrt 2 * r := by
      have h12 : 1 + r ^ 2 ≤ 2 * r ^ 2 := by nlinarith
      calc Lattice.jp k = Real.sqrt (1 + r ^ 2) := hjp
        _ ≤ Real.sqrt (2 * r ^ 2) := Real.sqrt_le_sqrt h12
        _ = Real.sqrt 2 * r := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hr0.le]
    have hq : s - (d : ℝ) ≤ 0 := by linarith
    have hrc : rieszCoeff d s k = rieszConst d s * r ^ (s - (d : ℝ)) := by
      simp [rieszCoeff, hk, hr]
    have hpow : r ^ (s - (d : ℝ)) ≤ (2 : ℝ) ^ (((d : ℝ) - s) / 2) * Lattice.jp k ^ (s - d) := by
      have hjk := Torus.jp_pos k
      have h2 : Lattice.jp k / Real.sqrt 2 ≤ r := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have h3 : r ^ (s - (d : ℝ)) ≤ (Lattice.jp k / Real.sqrt 2) ^ (s - (d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2 hq
      refine h3.trans (le_of_eq ?_)
      have hsq : Real.sqrt 2 ^ (s - (d : ℝ)) = (2 : ℝ) ^ ((s - (d : ℝ)) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
        congr 1; ring
      have hneg : (2 : ℝ) ^ (((d : ℝ) - s) / 2) = ((2 : ℝ) ^ ((s - (d : ℝ)) / 2))⁻¹ := by
        rw [← Real.rpow_neg (by norm_num)]
        congr 1; ring
      rw [Real.div_rpow hjk.le (by positivity), hsq, hneg]
      ring

    rw [hrc, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
    calc |rieszConst d s| * r ^ (s - (d : ℝ))
        ≤ |rieszConst d s| * ((2 : ℝ) ^ (((d : ℝ) - s) / 2) * Lattice.jp k ^ (s - d)) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = _ := by unfold Cg; ring

theorem norm_twoPiI_le (k : Lattice d) (i : Fin d) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ ≤ Lattice.jp k := by
  have h := two_pi_abs_coord_le_jp k i
  have : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ = 2 * Real.pi * |((k i : ℤ) : ℝ)| := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, Real.norm_eq_abs, Complex.norm_ofNat,
      mul_one, Complex.norm_real]
    rw [abs_of_pos Real.pi_pos]
  rw [this]; exact h

theorem norm_term_eq (a g : ℝ) (c z : ℂ) :
    ‖(a : ℂ) * (c * ((g : ℂ) * z))‖ = |a| * (‖c‖ * (|g| * ‖z‖)) := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem rpow_mono' {t : ℝ} (ht : 1 ≤ t) {a b : ℝ} (h : a ≤ b) : t ^ a ≤ t ^ b :=
  Real.rpow_le_rpow_of_exponent_le ht h

theorem drift_bound {s K MB Bμ BV : ℝ} (hsd : s < d) {D : DynData d} {μ : Torus d → ℝ}
    (h : GenHyp d s K MB Bμ BV D μ) (j : Fin d) (m : Lattice d) :
    ‖driftCoeff D μ j m‖ ≤ ((d : ℝ) * MB * Cg d s * Bμ + BV) * Lattice.jp m ^ (1 - K) := by
  have hjp := Torus.jp_pos m
  have hj1 := Torus.jp_ge_one m
  have hMB : 0 ≤ MB := le_trans (abs_nonneg _) (h.hM j j)
  have hCg := Cg_nonneg d s
  have hBμ : 0 ≤ Bμ := by
    have := h.hμ 0
    have h0 : 0 ≤ ‖coeffOf μ 0‖ := norm_nonneg _
    have hp : 0 < Lattice.jp (0 : Lattice d) ^ (-K) := Real.rpow_pos_of_pos (Torus.jp_pos _) _
    by_contra hneg
    push Not at hneg
    nlinarith
  have hBV : 0 ≤ BV := by
    have := h.hV 0
    have h0 : 0 ≤ ‖coeffOf D.V 0‖ := norm_nonneg _
    have hp : 0 < Lattice.jp (0 : Lattice d) ^ (-(K + 1)) := Real.rpow_pos_of_pos (Torus.jp_pos _) _
    by_contra hneg
    push Not at hneg
    nlinarith
  unfold driftCoeff gradRieszCoeff rieszMult derivCoeff
  have hterm : ∀ i : Fin d, ‖((D.M j i : ℝ) : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * ((m i : ℤ) : ℂ)) *
      (((rieszCoeff d D.s m : ℝ) : ℂ) * coeffOf μ m))‖ ≤ MB * Cg d s * Bμ * Lattice.jp m ^ (1 - K) := by
    intro i
    rw [norm_term_eq (D.M j i) (rieszCoeff d D.s m) _ (coeffOf μ m)]
    have h1 : |D.M j i| ≤ MB := h.hM j i
    have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I * ((m i : ℤ) : ℂ))‖ ≤ Lattice.jp m := norm_twoPiI_le m i
    have h3 : |rieszCoeff d D.s m| ≤ Cg d s * Lattice.jp m ^ (s - d) := by
      rw [h.hs]; exact abs_rieszCoeff_le_jp s hsd m
    have h4 : ‖coeffOf μ m‖ ≤ Bμ * Lattice.jp m ^ (-K) := h.hμ m
    have h5 : MB * Lattice.jp m * (Cg d s * Lattice.jp m ^ (s - d)) * (Bμ * Lattice.jp m ^ (-K)) =
        MB * Cg d s * Bμ * Lattice.jp m ^ (1 + (s - d) + (-K)) := by
      rw [Real.rpow_add hjp, Real.rpow_add hjp, Real.rpow_one]; ring
    have h6 : Lattice.jp m ^ (1 + (s - d) + (-K)) ≤ Lattice.jp m ^ (1 - K) :=
      rpow_mono' hj1 (by linarith)
    calc |D.M j i| * (‖(2 * (Real.pi : ℂ) * Complex.I * ((m i : ℤ) : ℂ))‖ *
          (|rieszCoeff d D.s m| * ‖coeffOf μ m‖))
        ≤ MB * (Lattice.jp m * ((Cg d s * Lattice.jp m ^ (s - d)) * (Bμ * Lattice.jp m ^ (-K)))) := by
          gcongr
      _ = MB * Cg d s * Bμ * Lattice.jp m ^ (1 + (s - d) + (-K)) := by rw [← h5]; ring
      _ ≤ MB * Cg d s * Bμ * Lattice.jp m ^ (1 - K) := by gcongr
  have hV' : ‖(2 * (Real.pi : ℂ) * Complex.I * ((m j : ℤ) : ℂ)) * coeffOf D.V m‖ ≤
      BV * Lattice.jp m ^ (1 - K) := by
    rw [norm_mul]
    have h2 := norm_twoPiI_le m j
    have h4 := h.hV m
    have h5 : Lattice.jp m * (BV * Lattice.jp m ^ (-(K + 1))) = BV * Lattice.jp m ^ (1 + (-(K + 1))) := by
      rw [Real.rpow_add hjp, Real.rpow_one]; ring
    have h6 : Lattice.jp m ^ (1 + (-(K + 1))) ≤ Lattice.jp m ^ (1 - K) :=
      rpow_mono' hj1 (by linarith)
    calc ‖(2 * (Real.pi : ℂ) * Complex.I * ((m j : ℤ) : ℂ))‖ * ‖coeffOf D.V m‖
        ≤ Lattice.jp m * (BV * Lattice.jp m ^ (-(K + 1))) := by gcongr
      _ = BV * Lattice.jp m ^ (1 + (-(K + 1))) := h5
      _ ≤ BV * Lattice.jp m ^ (1 - K) := by gcongr
  calc ‖(∑ i : Fin d, ((D.M j i : ℝ) : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * ((m i : ℤ) : ℂ)) *
        (((rieszCoeff d D.s m : ℝ) : ℂ) * coeffOf μ m))) -
        (2 * (Real.pi : ℂ) * Complex.I * ((m j : ℤ) : ℂ)) * coeffOf D.V m‖
      ≤ ∑ i : Fin d, MB * Cg d s * Bμ * Lattice.jp m ^ (1 - K) + BV * Lattice.jp m ^ (1 - K) := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) hV')
        exact Finset.sum_le_sum fun i _ => hterm i
    _ = ((d : ℝ) * MB * Cg d s * Bμ + BV) * Lattice.jp m ^ (1 - K) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem jp_pow_le_max (e2 : ℝ) (k l : Lattice d) :
    Lattice.jp k ^ e2 ≤ (2 : ℝ) ^ (max e2 0 / 2) * Lattice.jp (k - l) ^ (max e2 0) *
      Lattice.jp l ^ (max e2 0) := by
  rcases le_or_gt e2 0 with h | h
  · rw [max_eq_right h]
    simp only [Real.rpow_zero, zero_div, mul_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one k) h
  · rw [max_eq_left h.le]
    have := peetre_jp e2 k l
    rw [abs_of_pos h] at this
    calc Lattice.jp k ^ e2 ≤ _ := this
      _ = _ := by ring

theorem genEntry_bound (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (D : DynData d) (μ : Torus d → ℝ), GenHyp d s K MB Bμ BV D μ → ∀ k l : Lattice d,
      ‖genEntry D μ k l‖ ≤ A * Lattice.jp (k - l) ^ (-(K - 1 - max (s - d + 1) 0)) *
        Lattice.jp l ^ (1 + max (s - d + 1) 0) := by
  set e : ℝ := max (s - d + 1) 0 with he
  have he0 : 0 ≤ e := le_max_right _ _
  have hCg := Cg_nonneg d s
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨(d : ℝ) * ((d : ℝ) * MB * Cg d s * Bμ + BV) + (d : ℝ) * (d : ℝ) * MB * Cg d s * Bμ *
    (2 : ℝ) ^ (e / 2), by positivity, fun D μ h k l => ?_⟩
  have hjl := Torus.jp_pos l
  have hjl1 := Torus.jp_ge_one l
  have hjk := Torus.jp_pos k
  have hjkl := Torus.jp_pos (k - l)
  have hjkl1 := Torus.jp_ge_one (k - l)
  set X : ℝ := Lattice.jp (k - l) ^ (-(K - 1 - e)) with hX
  set Y : ℝ := Lattice.jp l ^ (1 + e) with hY
  have hX0 : 0 ≤ X := Real.rpow_nonneg hjkl.le _
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hjl.le _
  -- first term
  have hT1 : ‖∑ j : Fin d, driftCoeff D μ j (k - l) * (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ))‖ ≤
      (d : ℝ) * ((d : ℝ) * MB * Cg d s * Bμ + BV) * X * Y := by
    refine (norm_sum_le _ _).trans ?_
    have hj : ∀ j : Fin d, ‖driftCoeff D μ j (k - l) * (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ))‖ ≤
        ((d : ℝ) * MB * Cg d s * Bμ + BV) * X * Y := by
      intro j
      rw [norm_mul]
      have h1 := drift_bound hsd h j (k - l)
      have h2 := norm_twoPiI_le l j
      have h3 : Lattice.jp (k - l) ^ (1 - K) ≤ X := rpow_mono' hjkl1 (by rw [he]; linarith)
      have h4 : Lattice.jp l ≤ Y := by
        calc Lattice.jp l = Lattice.jp l ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ Y := rpow_mono' hjl1 (by linarith)
      have hB : 0 ≤ (d : ℝ) * MB * Cg d s * Bμ + BV := by positivity
      calc ‖driftCoeff D μ j (k - l)‖ * ‖(2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ))‖
          ≤ (((d : ℝ) * MB * Cg d s * Bμ + BV) * Lattice.jp (k - l) ^ (1 - K)) * Lattice.jp l :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ (((d : ℝ) * MB * Cg d s * Bμ + BV) * X) * Y := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    rfl
  -- second term
  have hT2 : ‖∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)) *
      (((rieszCoeff d D.s k : ℝ) : ℂ) * (coeffOf μ (k - l) *
        (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ)))))‖ ≤
      (d : ℝ) * (d : ℝ) * MB * Cg d s * Bμ * (2 : ℝ) ^ (e / 2) * X * Y := by
    have hij : ∀ i j : Fin d, ‖((D.M j i : ℝ) : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)) *
        (((rieszCoeff d D.s k : ℝ) : ℂ) * (coeffOf μ (k - l) *
          (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ)))))‖ ≤
        MB * Cg d s * Bμ * (2 : ℝ) ^ (e / 2) * X * Y := by
      intro i j
      rw [norm_term_eq (D.M j i) (rieszCoeff d D.s k) _ _]
      have h1 : |D.M j i| ≤ MB := h.hM j i
      have h2 := norm_twoPiI_le k i
      have h3 : |rieszCoeff d D.s k| ≤ Cg d s * Lattice.jp k ^ (s - d) := by
        rw [h.hs]; exact abs_rieszCoeff_le_jp s hsd k
      have h4 : ‖coeffOf μ (k - l) * (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ))‖ ≤
          (Bμ * Lattice.jp (k - l) ^ (-K)) * Lattice.jp l := by
        rw [norm_mul]
        exact mul_le_mul (h.hμ _) (norm_twoPiI_le l j) (norm_nonneg _) (by positivity)
      have h5 : Lattice.jp k * Lattice.jp k ^ (s - d) = Lattice.jp k ^ (s - d + 1) := by
        rw [Real.rpow_add_one hjk.ne']; ring
      have hP : Lattice.jp k ^ (s - d + 1) ≤
          (2 : ℝ) ^ (e / 2) * Lattice.jp (k - l) ^ e * Lattice.jp l ^ e :=
        jp_pow_le_max (s - d + 1) k l
      have h6 : Lattice.jp (k - l) ^ e * Lattice.jp (k - l) ^ (-K) ≤ X := by
        rw [← Real.rpow_add hjkl]
        exact rpow_mono' hjkl1 (by linarith)
      have h7 : Lattice.jp l ^ e * Lattice.jp l = Y := by
        rw [hY, show (1 + e) = e + 1 by ring, Real.rpow_add_one hjl.ne']
      have h2' : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ ≤ Lattice.jp k := h2
      have hbig : MB * (‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ *
            (|rieszCoeff d D.s k| *
              ‖coeffOf μ (k - l) * (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ))‖)) ≤
          MB * (Lattice.jp k * ((Cg d s * Lattice.jp k ^ (s - d)) *
            ((Bμ * Lattice.jp (k - l) ^ (-K)) * Lattice.jp l))) := by
        gcongr
      calc |D.M j i| * (‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ *
            (|rieszCoeff d D.s k| *
              ‖coeffOf μ (k - l) * (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ))‖))
          ≤ MB * (‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ *
            (|rieszCoeff d D.s k| *
              ‖coeffOf μ (k - l) * (2 * (Real.pi : ℂ) * Complex.I * ((l j : ℤ) : ℂ))‖)) := by
            gcongr
        _ ≤ MB * (Lattice.jp k * ((Cg d s * Lattice.jp k ^ (s - d)) *
            ((Bμ * Lattice.jp (k - l) ^ (-K)) * Lattice.jp l))) := hbig
        _ = MB * Cg d s * Bμ * (Lattice.jp k * Lattice.jp k ^ (s - d)) * Lattice.jp (k - l) ^ (-K) *
            Lattice.jp l := by ring
        _ = MB * Cg d s * Bμ * Lattice.jp k ^ (s - d + 1) * Lattice.jp (k - l) ^ (-K) *
            Lattice.jp l := by rw [h5]
        _ ≤ MB * Cg d s * Bμ * ((2 : ℝ) ^ (e / 2) * Lattice.jp (k - l) ^ e * Lattice.jp l ^ e) *
            Lattice.jp (k - l) ^ (-K) * Lattice.jp l := by gcongr
        _ = MB * Cg d s * Bμ * (2 : ℝ) ^ (e / 2) *
            (Lattice.jp (k - l) ^ e * Lattice.jp (k - l) ^ (-K)) * (Lattice.jp l ^ e * Lattice.jp l) := by
            ring
        _ ≤ MB * Cg d s * Bμ * (2 : ℝ) ^ (e / 2) * X * Y := by
            rw [h7]
            gcongr
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hij i j)).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    rfl
  -- assemble
  unfold genEntry
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add hT1 hT2).trans (le_of_eq ?_)
  ring

end HRS.Uniform.Q54
