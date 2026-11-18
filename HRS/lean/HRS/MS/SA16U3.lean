import HRS.MS.SA16CutDefs
import HRS.MS.SA16StrongSL2

/-!
# S.A.16 K3: `weighted_inner_from_outer`

Translation energy `Q w = int mu(x) |V x - V(x-w)|^2 dx`.  For `|z| <= r <= delta` and every `h` in the annulus
`2 delta < |h| < 3 delta`: `Q z <= 2 Q h + 4 Q (z-h) + 16 L^2 |h|^2 |V|_2^2` (splitting the jump and transferring the weight).
Averaging over `h` gives `Q z <= C delta^theta Out + C L^2 delta^2 |V|^2`; integrating against the inner kernel
`delta^(-theta-1) |z|^(1-d)` over the ball of radius `r` gives the claim.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv Phase2SA16

section K3
variable {d q : ℕ}

/-- translation energy -/
def sa16u_Q (μ : Euc d → ℝ) (V : Euc d → Euc q) (w : Euc d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (μ x * ‖V x - V (x - w)‖ ^ 2)

/-- the `L^2` mass -/
def sa16u_V2 (V : Euc d → Euc q) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (‖V x‖ ^ 2)

lemma sa16u_weight_step {m m' L h : ℝ} (hm : 0 ≤ m) (hm' : 0 ≤ m') (hL : 0 ≤ L)
    (hlip : Real.sqrt m ≤ Real.sqrt m' + L * h) (hh : 0 ≤ h) : m ≤ 2 * m' + 2 * (L * h) ^ 2 := by
  have h1 : m = (Real.sqrt m) ^ 2 := (Real.sq_sqrt hm).symm
  have h2 : m' = (Real.sqrt m') ^ 2 := (Real.sq_sqrt hm').symm
  have h3 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have h4 : 0 ≤ Real.sqrt m' := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (Real.sqrt m' - L * h), mul_nonneg hL hh]

lemma sa16u_pt {m m' L h A B T P S : ℝ} (hm : 0 ≤ m) (hm' : 0 ≤ m') (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hlip : Real.sqrt m ≤ Real.sqrt m' + L * h) (hT : T ≤ A + B) (hT0 : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hBP : B ^ 2 ≤ 2 * P + 2 * S) :
    m * T ^ 2 ≤ 2 * (m * A ^ 2) + 4 * (m' * B ^ 2) + 4 * L ^ 2 * h ^ 2 * (2 * P + 2 * S) := by
  have h1 := sa16u_weight_step hm hm' hL hlip hh
  have h2 : T ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B), mul_nonneg hT0 hT0]
  have h3 : T ^ 2 ≤ (A + B) ^ 2 := pow_le_pow_left₀ hT0 hT 2
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have h4 : m * T ^ 2 ≤ m * (2 * A ^ 2 + 2 * B ^ 2) := mul_le_mul_of_nonneg_left h2 hm
  have h5 : m * B ^ 2 ≤ (2 * m' + 2 * (L * h) ^ 2) * B ^ 2 := mul_le_mul_of_nonneg_right h1 hB2
  have h6 : 4 * L ^ 2 * h ^ 2 * B ^ 2 ≤ 4 * L ^ 2 * h ^ 2 * (2 * P + 2 * S) :=
    mul_le_mul_of_nonneg_left hBP (by positivity)
  nlinarith [h4, h5, h6]

lemma sa16u_Q_step {μ : Euc d → ℝ} {V : Euc d → Euc q} (hμ : Measurable μ) (hV : Measurable V)
    (hμ0 : ∀ x, 0 ≤ μ x) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |Real.sqrt (μ x) - Real.sqrt (μ y)| ≤ L * ‖x - y‖) (z h : Euc d) :
    sa16u_Q μ V z ≤ 2 * sa16u_Q μ V h + 4 * sa16u_Q μ V (z - h) +
      ENNReal.ofReal (16 * L ^ 2 * ‖h‖ ^ 2) * sa16u_V2 V := by
  set c : ℝ := 4 * L ^ 2 * ‖h‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set f1 : Euc d → ℝ≥0∞ := fun x => 2 * ENNReal.ofReal (μ x * ‖V x - V (x - h)‖ ^ 2) with hf1
  set f2 : Euc d → ℝ≥0∞ := fun x =>
    4 * ENNReal.ofReal (μ (x - h) * ‖V (x - h) - V (x - z)‖ ^ 2) with hf2
  set f3 : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal c *
    (2 * ENNReal.ofReal (‖V (x - h)‖ ^ 2) + 2 * ENNReal.ofReal (‖V (x - z)‖ ^ 2)) with hf3
  have hpt : ∀ x, ENNReal.ofReal (μ x * ‖V x - V (x - z)‖ ^ 2) ≤ f1 x + f2 x + f3 x := by
    intro x
    have hlip' := hlip x (x - h)
    rw [sub_sub_cancel] at hlip'
    have hs : Real.sqrt (μ x) ≤ Real.sqrt (μ (x - h)) + L * ‖h‖ := by
      have := (abs_le.1 hlip').2; linarith
    have hT : ‖V x - V (x - z)‖ ≤ ‖V x - V (x - h)‖ + ‖V (x - h) - V (x - z)‖ := by
      calc ‖V x - V (x - z)‖ = ‖(V x - V (x - h)) + (V (x - h) - V (x - z))‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hBP : ‖V (x - h) - V (x - z)‖ ^ 2 ≤ 2 * ‖V (x - h)‖ ^ 2 + 2 * ‖V (x - z)‖ ^ 2 := by
      have := norm_sub_le (V (x - h)) (V (x - z))
      nlinarith [norm_nonneg (V (x - h)), norm_nonneg (V (x - z)), sq_nonneg (‖V (x - h)‖ - ‖V (x - z)‖),
        norm_nonneg (V (x - h) - V (x - z))]
    have key := sa16u_pt (hμ0 x) (hμ0 (x - h)) hL (norm_nonneg h) hs hT (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hBP
    have h2 : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal (2 * a) = 2 * ENNReal.ofReal a := fun a ha => by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    have h4 : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal (4 * a) = 4 * ENNReal.ofReal a := fun a ha => by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    have hmx := hμ0 x
    have hmh := hμ0 (x - h)
    have n1 : 0 ≤ μ x * ‖V x - V (x - h)‖ ^ 2 := by positivity
    have n2 : 0 ≤ μ (x - h) * ‖V (x - h) - V (x - z)‖ ^ 2 := by positivity
    have n3 : 0 ≤ ‖V (x - h)‖ ^ 2 := by positivity
    have n4 : 0 ≤ ‖V (x - z)‖ ^ 2 := by positivity
    have e1 : ENNReal.ofReal (2 * (μ x * ‖V x - V (x - h)‖ ^ 2)) = f1 x := h2 _ n1
    have e2 : ENNReal.ofReal (4 * (μ (x - h) * ‖V (x - h) - V (x - z)‖ ^ 2)) = f2 x := h4 _ n2
    have e3 : ENNReal.ofReal (c * (2 * ‖V (x - h)‖ ^ 2 + 2 * ‖V (x - z)‖ ^ 2)) = f3 x := by
      simp only [hf3]
      rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_add (by positivity) (by positivity), h2 _ n3, h2 _ n4]
    calc ENNReal.ofReal (μ x * ‖V x - V (x - z)‖ ^ 2)
        ≤ ENNReal.ofReal (2 * (μ x * ‖V x - V (x - h)‖ ^ 2) + 4 * (μ (x - h) * ‖V (x - h) - V (x - z)‖ ^ 2) +
            c * (2 * ‖V (x - h)‖ ^ 2 + 2 * ‖V (x - z)‖ ^ 2)) := ENNReal.ofReal_le_ofReal (by
              have : 4 * L ^ 2 * ‖h‖ ^ 2 * (2 * ‖V (x - h)‖ ^ 2 + 2 * ‖V (x - z)‖ ^ 2) =
                c * (2 * ‖V (x - h)‖ ^ 2 + 2 * ‖V (x - z)‖ ^ 2) := by rw [hc]
              linarith [key])
      _ = f1 x + f2 x + f3 x := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity)
          (by positivity), e1, e2, e3]
  have m1 : Measurable f1 := by
    simp only [hf1]
    exact (((hμ.mul ((hV.sub (hV.comp (measurable_id.sub_const h))).norm.pow_const 2))).ennreal_ofReal).const_mul 2
  have m2 : Measurable f2 := by
    simp only [hf2]
    exact (((hμ.comp (measurable_id.sub_const h)).mul (((hV.comp (measurable_id.sub_const h)).sub
      (hV.comp (measurable_id.sub_const z))).norm.pow_const 2)).ennreal_ofReal).const_mul 4
  calc sa16u_Q μ V z ≤ ∫⁻ x, (f1 x + f2 x + f3 x) := lintegral_mono hpt
    _ = (∫⁻ x, f1 x) + (∫⁻ x, f2 x) + ∫⁻ x, f3 x := by
        rw [lintegral_add_left (f := fun x => f1 x + f2 x) (m1.add m2) f3, lintegral_add_left m1 f2]
    _ = _ := by
        have i1 : ∫⁻ x, f1 x = 2 * sa16u_Q μ V h := by
          simp only [hf1, sa16u_Q]
          rw [lintegral_const_mul' _ _ (by norm_num)]
        have i2 : ∫⁻ x, f2 x = 4 * sa16u_Q μ V (z - h) := by
          simp only [hf2, sa16u_Q]
          rw [lintegral_const_mul' _ _ (by norm_num)]
          congr 1
          have := lintegral_sub_right_eq_self (μ := (volume : Measure (Euc d)))
            (fun y => ENNReal.ofReal (μ y * ‖V y - V (y - (z - h))‖ ^ 2)) h
          simp only [sub_sub_sub_cancel_right] at this
          exact this
        have i3 : ∫⁻ x, f3 x = ENNReal.ofReal (16 * L ^ 2 * ‖h‖ ^ 2) * sa16u_V2 V := by
          simp only [hf3]
          have v1 : ∫⁻ x, ENNReal.ofReal (‖V (x - h)‖ ^ 2) = sa16u_V2 V :=
            lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (‖V y‖ ^ 2)) h
          have v2 : ∫⁻ x, ENNReal.ofReal (‖V (x - z)‖ ^ 2) = sa16u_V2 V :=
            lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (‖V y‖ ^ 2)) z
          have mm1 : Measurable fun x => 2 * ENNReal.ofReal (‖V (x - h)‖ ^ 2) :=
            (((hV.comp (measurable_id.sub_const h)).norm.pow_const 2).ennreal_ofReal).const_mul 2
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left mm1,
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num), v1, v2]
          rw [show (16 * L ^ 2 * ‖h‖ ^ 2 : ℝ) = c * 4 by rw [hc]; ring, ENNReal.ofReal_mul hc0]
          rw [show (2 : ℝ≥0∞) * sa16u_V2 V + 2 * sa16u_V2 V = 4 * sa16u_V2 V by
            rw [← add_mul]; norm_num]
          simp [mul_assoc]
        rw [i1, i2, i3]

lemma sa16u_Q_meas {μ : Euc d → ℝ} {V : Euc d → Euc q} (hμ : Measurable μ) (hV : Measurable V) :
    Measurable (sa16u_Q μ V) := by
  have : Measurable (fun p : Euc d × Euc d => ENNReal.ofReal (μ p.1 * ‖V p.1 - V (p.1 - p.2)‖ ^ 2)) :=
    ((hμ.comp measurable_fst).mul (((hV.comp measurable_fst).sub
      (hV.comp (measurable_fst.sub measurable_snd))).norm.pow_const 2)).ennreal_ofReal
  exact this.lintegral_prod_left'

/-- Tonelli: integrate the displacement first -/
lemma sa16u_tonelli {μ : Euc d → ℝ} {V : Euc d → Euc q} (hμ : Measurable μ) (hV : Measurable V)
    {w : Euc d → ℝ≥0∞} (hw : Measurable w) {T : Set (Euc d)} (hT : MeasurableSet T) :
    ∫⁻ x, ∫⁻ z in T, w z * ENNReal.ofReal (μ x * ‖V x - V (x - z)‖ ^ 2) =
      ∫⁻ z in T, w z * sa16u_Q μ V z := by
  have hm : Measurable (fun p : Euc d × Euc d => w p.2 * ENNReal.ofReal (μ p.1 * ‖V p.1 - V (p.1 - p.2)‖ ^ 2)) :=
    (hw.comp measurable_snd).mul (((hμ.comp measurable_fst).mul (((hV.comp measurable_fst).sub
      (hV.comp (measurable_fst.sub measurable_snd))).norm.pow_const 2)).ennreal_ofReal)
  rw [lintegral_lintegral_swap (f := fun x z => w z * ENNReal.ofReal (μ x * ‖V x - V (x - z)‖ ^ 2))
    hm.aemeasurable]
  refine lintegral_congr fun z => ?_
  unfold sa16u_Q
  rw [lintegral_const_mul]
  exact ((hμ.mul ((hV.sub (hV.comp (measurable_id.sub_const z))).norm.pow_const 2)).ennreal_ofReal)

lemma sa16u_annulus_vol (hd : 1 ≤ d) :
    ∃ cA : ℝ, 0 < cA ∧ ∀ δ : ℝ, 0 < δ →
      volume (ball (0 : Euc d) (3 * δ) \ closedBall (0 : Euc d) (2 * δ)) = ENNReal.ofReal (cA * δ ^ d) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set b : ℝ≥0∞ := volume (ball (0 : Euc d) 1) with hb
  have hbpos : 0 < b := measure_ball_pos _ _ one_pos
  have hbfin : b ≠ ⊤ := (measure_ball_lt_top).ne
  have hbr : 0 < b.toReal := ENNReal.toReal_pos hbpos.ne' hbfin
  have h23 : (2 : ℝ) ^ d < 3 ^ d := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  refine ⟨(3 ^ d - 2 ^ d) * b.toReal, mul_pos (by linarith) hbr, fun δ hδ => ?_⟩
  have hsub : closedBall (0 : Euc d) (2 * δ) ⊆ ball (0 : Euc d) (3 * δ) :=
    closedBall_subset_ball (by linarith)
  have e1 : volume (ball (0 : Euc d) (3 * δ)) = ENNReal.ofReal ((3 * δ) ^ d) * b := by
    rw [Measure.addHaar_ball _ _ (by linarith), finrank_euclideanSpace_fin]
  have e2 : volume (closedBall (0 : Euc d) (2 * δ)) = ENNReal.ofReal ((2 * δ) ^ d) * b := by
    rw [Measure.addHaar_closedBall _ _ (by linarith), finrank_euclideanSpace_fin]
  have hfin : volume (closedBall (0 : Euc d) (2 * δ)) ≠ ⊤ := by
    rw [e2]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbfin
  rw [measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet hfin, e1, e2, ← ENNReal.sub_mul (fun _ _ => hbfin),
    ← ENNReal.ofReal_sub _ (by positivity)]
  have : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbfin).symm
  conv_lhs => rw [this]
  rw [← ENNReal.ofReal_mul (by
    have : (2 * δ) ^ d ≤ (3 * δ) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    linarith)]
  congr 1
  rw [mul_pow, mul_pow]
  ring

/-- pointwise bound on the translation energy for small displacements -/
lemma sa16u_Q_bd (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (δ r L : ℝ), 0 < r → r ≤ δ → 0 ≤ L → ∀ (μ : Euc d → ℝ) (V : Euc d → Euc q),
      Measurable μ → Measurable V → (∀ x, 0 ≤ μ x) →
      (∀ x y, |Real.sqrt (μ x) - Real.sqrt (μ y)| ≤ L * ‖x - y‖) →
      ∀ z : Euc d, ‖z‖ ≤ r →
        sa16u_Q μ V z ≤ ENNReal.ofReal (C₁ * δ ^ θ) *
          (∫⁻ z in {z : Euc d | δ < ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-((d : ℝ) + θ))) * sa16u_Q μ V z) +
          ENNReal.ofReal (144 * L ^ 2 * δ ^ 2) * sa16u_V2 V := by
  obtain ⟨cA, hcA, hvol⟩ := sa16u_annulus_vol (d := d) hd
  refine ⟨6 * 4 ^ ((d : ℝ) + θ) / cA, by positivity, fun δ r L hr hrδ hL μ V hμ hV hμ0 hlip z hz => ?_⟩
  have hδ : 0 < δ := hr.trans_le hrδ
  set s : ℝ := (d : ℝ) + θ with hs
  have hs0 : 0 ≤ s := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  set S : Set (Euc d) := {z : Euc d | δ < ‖z‖} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  set Out : ℝ≥0∞ := ∫⁻ z in S, ENNReal.ofReal (‖z‖ ^ (-s)) * sa16u_Q μ V z with hOut
  have hQ : Measurable (sa16u_Q μ V) := sa16u_Q_meas hμ hV
  set A : Set (Euc d) := ball (0 : Euc d) (3 * δ) \ closedBall (0 : Euc d) (2 * δ) with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hmemA : ∀ h, h ∈ A → 2 * δ < ‖h‖ ∧ ‖h‖ < 3 * δ := by
    intro h hh
    simp only [hA, mem_diff, mem_ball, mem_closedBall, dist_zero_right, not_le] at hh
    exact ⟨hh.2, hh.1⟩
  set X : ℝ≥0∞ := ENNReal.ofReal ((4 * δ) ^ s) with hX
  set G : Euc d → ℝ≥0∞ := S.indicator (fun h => X * (ENNReal.ofReal (‖h‖ ^ (-s)) * sa16u_Q μ V h)) with hG
  have hGint : ∫⁻ h, G h = X * Out := by
    rw [hG, lintegral_indicator hS, lintegral_const_mul]
    exact (measurable_norm.pow_const _).ennreal_ofReal.mul hQ
  have hGm : Measurable G := by
    rw [hG]
    exact (((measurable_norm.pow_const _).ennreal_ofReal.mul hQ).const_mul X).indicator hS
  have hQG : ∀ h : Euc d, δ < ‖h‖ → ‖h‖ ≤ 4 * δ → sa16u_Q μ V h ≤ G h := by
    intro h h1 h2
    have hn : 0 < ‖h‖ := hδ.trans h1
    rw [hG, Set.indicator_of_mem (show h ∈ S from h1), ← mul_assoc, hX, ← ENNReal.ofReal_mul (by positivity)]
    have hge : 1 ≤ (4 * δ) ^ s * ‖h‖ ^ (-s) := by
      have h3 : ‖h‖ ^ s ≤ (4 * δ) ^ s := Real.rpow_le_rpow hn.le h2 hs0
      have h4 : ‖h‖ ^ s * ‖h‖ ^ (-s) = 1 := by rw [← Real.rpow_add hn]; simp
      have h5 : 0 ≤ ‖h‖ ^ (-s) := Real.rpow_nonneg hn.le _
      nlinarith
    calc sa16u_Q μ V h = 1 * sa16u_Q μ V h := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((4 * δ) ^ s * ‖h‖ ^ (-s)) * sa16u_Q μ V h := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hge
  -- the step inequality, integrated over the annulus
  set K : ℝ≥0∞ := ENNReal.ofReal (144 * L ^ 2 * δ ^ 2) * sa16u_V2 V with hK
  have hstep : ∀ h ∈ A, sa16u_Q μ V z ≤ 2 * sa16u_Q μ V h + 4 * sa16u_Q μ V (z - h) + K := by
    intro h hh
    obtain ⟨h1, h2⟩ := hmemA h hh
    have : 16 * L ^ 2 * ‖h‖ ^ 2 ≤ 144 * L ^ 2 * δ ^ 2 := by
      have : ‖h‖ ^ 2 ≤ 9 * δ ^ 2 := by nlinarith [norm_nonneg h]
      nlinarith [sq_nonneg L]
    exact (sa16u_Q_step hμ hV hμ0 hL hlip z h).trans
      (add_le_add_right (mul_le_mul' (ENNReal.ofReal_le_ofReal this) le_rfl) _)
  have hint1 : ∫⁻ h in A, sa16u_Q μ V h ≤ X * Out := by
    calc ∫⁻ h in A, sa16u_Q μ V h ≤ ∫⁻ h in A, G h := by
          refine setLIntegral_mono' hAm fun h hh => ?_
          obtain ⟨h1, h2⟩ := hmemA h hh
          exact hQG h (by linarith) (by linarith)
      _ ≤ ∫⁻ h, G h := setLIntegral_le_lintegral _ _
      _ = X * Out := hGint
  have hint2 : ∫⁻ h in A, sa16u_Q μ V (z - h) ≤ X * Out := by
    calc ∫⁻ h in A, sa16u_Q μ V (z - h) ≤ ∫⁻ h in A, G (z - h) := by
          refine setLIntegral_mono' hAm fun h hh => ?_
          obtain ⟨h1, h2⟩ := hmemA h hh
          have a1 : ‖h‖ ≤ ‖z‖ + ‖z - h‖ := by
            have := norm_sub_le z (z - h)
            rw [sub_sub_cancel] at this
            linarith
          have a2 : ‖z - h‖ ≤ ‖z‖ + ‖h‖ := norm_sub_le z h
          exact hQG (z - h) (by linarith) (by linarith)
      _ ≤ ∫⁻ h, G (z - h) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ h, G h := lintegral_sub_left_eq_self G z
      _ = X * Out := hGint
  have hmain : volume A * sa16u_Q μ V z ≤ 6 * (X * Out) + volume A * K := by
    have m1 : Measurable fun h => 2 * sa16u_Q μ V h := hQ.const_mul 2
    have m2 : Measurable fun h => 4 * sa16u_Q μ V (z - h) :=
      (hQ.comp (measurable_const.sub measurable_id)).const_mul 4
    have e1 : ∫⁻ h in A, (2 * sa16u_Q μ V h + 4 * sa16u_Q μ V (z - h) + K) =
        (∫⁻ h in A, 2 * sa16u_Q μ V h) + (∫⁻ h in A, 4 * sa16u_Q μ V (z - h)) + ∫⁻ _ in A, K := by
      rw [lintegral_add_left (f := fun h => 2 * sa16u_Q μ V h + 4 * sa16u_Q μ V (z - h)) (m1.add m2)
        (fun _ => K), lintegral_add_left (f := fun h => 2 * sa16u_Q μ V h) m1]
    have e2 : ∫⁻ h in A, 2 * sa16u_Q μ V h = 2 * ∫⁻ h in A, sa16u_Q μ V h :=
      lintegral_const_mul' _ _ (by norm_num)
    have e3 : ∫⁻ h in A, 4 * sa16u_Q μ V (z - h) = 4 * ∫⁻ h in A, sa16u_Q μ V (z - h) :=
      lintegral_const_mul' _ _ (by norm_num)
    have e4 : ∫⁻ _ in A, K = K * volume A := setLIntegral_const A K
    have t1 : 2 * ∫⁻ h in A, sa16u_Q μ V h ≤ 2 * (X * Out) := mul_le_mul_of_nonneg_left hint1 zero_le
    have t2 : 4 * ∫⁻ h in A, sa16u_Q μ V (z - h) ≤ 4 * (X * Out) :=
      mul_le_mul_of_nonneg_left hint2 zero_le
    have e5 : (2 : ℝ≥0∞) * (X * Out) + 4 * (X * Out) = 6 * (X * Out) := by
      rw [← add_mul]; congr 1; norm_num
    calc volume A * sa16u_Q μ V z = ∫⁻ _ in A, sa16u_Q μ V z := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ h in A, (2 * sa16u_Q μ V h + 4 * sa16u_Q μ V (z - h) + K) :=
          setLIntegral_mono' hAm hstep
      _ = (2 * ∫⁻ h in A, sa16u_Q μ V h) + (4 * ∫⁻ h in A, sa16u_Q μ V (z - h)) + K * volume A := by
          rw [e1, e2, e3, e4]
      _ ≤ 2 * (X * Out) + 4 * (X * Out) + K * volume A := add_le_add (add_le_add t1 t2) le_rfl
      _ = 6 * (X * Out) + volume A * K := by rw [e5, mul_comm K]
  have hvolA : volume A = ENNReal.ofReal (cA * δ ^ d) := hvol δ hδ
  have hpos : 0 < cA * δ ^ d := by positivity
  have hv0 : volume A ≠ 0 := by rw [hvolA]; exact (ENNReal.ofReal_pos.2 hpos).ne'
  have hvT : volume A ≠ ⊤ := by rw [hvolA]; exact ENNReal.ofReal_ne_top
  have h1 := (ENNReal.mul_le_iff_le_inv hv0 hvT).1 hmain
  have hcancel : (volume A)⁻¹ * (volume A * K) = K := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hv0 hvT, one_mul]
  have hreal : (cA * δ ^ d)⁻¹ * 6 * (4 * δ) ^ s = 6 * 4 ^ s / cA * δ ^ θ := by
    rw [Real.mul_rpow (by norm_num) hδ.le, hs, Real.rpow_add hδ, Real.rpow_natCast]
    have : δ ^ d ≠ 0 := by positivity
    field_simp
  have hcoef : (volume A)⁻¹ * (6 * (X * Out)) = ENNReal.ofReal (6 * 4 ^ ((d : ℝ) + θ) / cA * δ ^ θ) * Out := by
    rw [hvolA, ← ENNReal.ofReal_inv_of_pos hpos, ← hreal, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), hX]
    simp [mul_assoc]
  calc sa16u_Q μ V z ≤ (volume A)⁻¹ * (6 * (X * Out) + volume A * K) := h1
    _ = _ := by rw [mul_add, hcancel, hcoef]

/-- the inner kernel mass on a ball -/
lemma sa16u_inner_mass (hd : 1 ≤ d) :
    ∃ I₀ : ℝ, 0 ≤ I₀ ∧ ∀ (θ δ r : ℝ), 0 < δ → 0 < r →
      ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ))) ≤
        ENNReal.ofReal (δ ^ (-θ - 1) * (r * I₀)) := by
  obtain ⟨I₀, hI₀, hmom⟩ := sa16s_moment (d := d) hd (θ := 1) (by norm_num)
  refine ⟨I₀, hI₀, fun θ δ r hδ hr => ?_⟩
  obtain ⟨hint, hval⟩ := hmom r hr
  have hk : (fun z : Euc d => (closedBall (0 : Euc d) r).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + 1))) z) = (closedBall (0 : Euc d) r).indicator
      (fun z => ‖z‖ ^ (1 - (d : ℝ))) := by
    funext z; congr 2; funext w; congr 1; ring
  have hint' : Integrable ((closedBall (0 : Euc d) r).indicator (fun z => ‖z‖ ^ (1 - (d : ℝ)))) := by
    rw [← hk]; exact hint
  have hnn : 0 ≤ᵐ[volume] fun z : Euc d => δ ^ (-θ - 1) *
      (closedBall (0 : Euc d) r).indicator (fun z => ‖z‖ ^ (1 - (d : ℝ))) z :=
    Eventually.of_forall fun z => mul_nonneg (Real.rpow_nonneg hδ.le _)
      (Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) z)
  have hlin := ofReal_integral_eq_lintegral_ofReal (hint'.const_mul (δ ^ (-θ - 1))) hnn
  calc ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ)))
      = ∫⁻ z, (ball (0 : Euc d) r).indicator
        (fun z => ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ)))) z := by
          rw [lintegral_indicator measurableSet_ball]
    _ ≤ ∫⁻ z, ENNReal.ofReal (δ ^ (-θ - 1) *
        (closedBall (0 : Euc d) r).indicator (fun z => ‖z‖ ^ (1 - (d : ℝ))) z) := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ ball (0 : Euc d) r
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (ball_subset_closedBall hz)]
          · rw [Set.indicator_of_notMem hz]; exact zero_le
    _ = ENNReal.ofReal (∫ z, δ ^ (-θ - 1) *
        (closedBall (0 : Euc d) r).indicator (fun z => ‖z‖ ^ (1 - (d : ℝ))) z) := hlin.symm
    _ = ENNReal.ofReal (δ ^ (-θ - 1) * (r * I₀)) := by
          rw [integral_const_mul, ← hk, hval]
          congr 2
          rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

lemma sa16u_K3_meas (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ r L : ℝ, 0 < r → r ≤ δ → 0 ≤ L → ∀ μ : Euc d → ℝ,
      (∀ x, 0 ≤ μ x) → (∀ x y, |Real.sqrt (μ x) - Real.sqrt (μ y)| ≤ L * ‖x - y‖) →
      ∀ V : Euc d → Euc q, Measurable V →
      quadInner d q θ δ r μ V ≤ ENNReal.ofReal (C * r / δ) * quadOuter d q θ δ μ V +
        ENNReal.ofReal (C * L ^ 2 * r * δ ^ (1 - θ)) * sa16u_V2 V := by
  obtain ⟨C₁, hC₁, hQb⟩ := sa16u_Q_bd (q := q) hd hθ0
  obtain ⟨I₀, hI₀, hmass⟩ := sa16u_inner_mass hd
  refine ⟨I₀ * C₁ + 144 * I₀ + 1, by positivity, fun δ r L hr hrδ hL μ hμ0 hlip V hV => ?_⟩
  have hδ : 0 < δ := hr.trans_le hrδ
  have hμm : Measurable μ := by
    have hc : Continuous fun x => Real.sqrt (μ x) :=
      (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) (f := fun x => Real.sqrt (μ x))
        (fun x y => by
          have := hlip x y
          rw [Real.dist_eq, dist_eq_norm]
          exact this)).continuous
    have : μ = fun x => (Real.sqrt (μ x)) ^ 2 := by
      funext x; rw [Real.sq_sqrt (hμ0 x)]
    rw [this]
    exact hc.measurable.pow_const 2
  set s : ℝ := (d : ℝ) + θ with hs
  set S : Set (Euc d) := {z : Euc d | δ < ‖z‖} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  set Out : ℝ≥0∞ := ∫⁻ z in S, ENNReal.ofReal (‖z‖ ^ (-s)) * sa16u_Q μ V z with hOut
  have hO : quadOuter d q θ δ μ V = Out := by
    unfold quadOuter
    rw [hOut, ← sa16u_tonelli hμm hV (w := fun z => ENNReal.ofReal (‖z‖ ^ (-s)))
      (measurable_norm.pow_const _).ennreal_ofReal hS]
    refine lintegral_congr fun x => lintegral_congr fun z => ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_neg (norm_nonneg _),
      inv_mul_eq_div]
  have hI : quadInner d q θ δ r μ V = ∫⁻ z in ball (0 : Euc d) r,
      ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ))) * sa16u_Q μ V z := by
    unfold quadInner
    rw [← sa16u_tonelli hμm hV (w := fun z => ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ))))
      ((measurable_const.mul (measurable_norm.pow_const _)).ennreal_ofReal) measurableSet_ball]
    refine lintegral_congr fun x => lintegral_congr fun z => ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg (norm_nonneg _) _)),
      mul_assoc]
  set E : ℝ≥0∞ := ENNReal.ofReal (C₁ * δ ^ θ) * Out + ENNReal.ofReal (144 * L ^ 2 * δ ^ 2) * sa16u_V2 V
    with hE
  have hmassr := hmass θ δ r hδ hr
  calc quadInner d q θ δ r μ V
      = ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ))) * sa16u_Q μ V z := hI
    _ ≤ ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ))) * E := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        exact mul_le_mul_of_nonneg_left (hQb δ r L hr hrδ hL μ V hμm hV hμ0 hlip z
          (mem_ball_zero_iff.1 hz).le) zero_le
    _ = (∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal (δ ^ (-θ - 1) * ‖z‖ ^ (1 - (d : ℝ)))) * E := by
        rw [lintegral_mul_const]
        exact (measurable_const.mul (measurable_norm.pow_const _)).ennreal_ofReal
    _ ≤ ENNReal.ofReal (δ ^ (-θ - 1) * (r * I₀)) * E := mul_le_mul_of_nonneg_right hmassr zero_le
    _ = ENNReal.ofReal (δ ^ (-θ - 1) * (r * I₀) * (C₁ * δ ^ θ)) * Out +
        ENNReal.ofReal (δ ^ (-θ - 1) * (r * I₀) * (144 * L ^ 2 * δ ^ 2)) * sa16u_V2 V := by
        rw [hE, mul_add, ← mul_assoc (ENNReal.ofReal _) (ENNReal.ofReal _) Out,
          ← mul_assoc (ENNReal.ofReal _) (ENNReal.ofReal _) (sa16u_V2 V),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        rw [hO]
        have e1 : δ ^ (-θ - 1) * δ ^ θ = δ⁻¹ := by
          rw [← Real.rpow_add hδ, show -θ - 1 + θ = -1 by ring, Real.rpow_neg_one]
        have e2 : δ ^ (-θ - 1) * δ ^ 2 = δ ^ (1 - θ) := by
          rw [← Real.rpow_natCast δ 2, ← Real.rpow_add hδ]; congr 1; push_cast; ring
        have c1 : δ ^ (-θ - 1) * (r * I₀) * (C₁ * δ ^ θ) = I₀ * C₁ * r / δ := by
          have := e1
          calc δ ^ (-θ - 1) * (r * I₀) * (C₁ * δ ^ θ) = (δ ^ (-θ - 1) * δ ^ θ) * (r * I₀ * C₁) := by ring
            _ = I₀ * C₁ * r / δ := by rw [this]; field_simp
        have c2 : δ ^ (-θ - 1) * (r * I₀) * (144 * L ^ 2 * δ ^ 2) = 144 * I₀ * L ^ 2 * r * δ ^ (1 - θ) := by
          calc δ ^ (-θ - 1) * (r * I₀) * (144 * L ^ 2 * δ ^ 2) = (δ ^ (-θ - 1) * δ ^ 2) * (144 * I₀ * L ^ 2 * r) := by ring
            _ = _ := by rw [e2]; ring
        rw [c1, c2]
        refine add_le_add (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
        · rw [div_le_div_iff_of_pos_right hδ]
          nlinarith [mul_nonneg hI₀ hC₁.le, hr]
        · have h2 : 0 ≤ L ^ 2 * r * δ ^ (1 - θ) := by positivity
          nlinarith [mul_nonneg hI₀ h2, h2]

lemma sa16u_congr_V {V V' : Euc d → Euc q} (h : V =ᵐ[volume] V') (θ δ r : ℝ) (μ : Euc d → ℝ) :
    quadInner d q θ δ r μ V = quadInner d q θ δ r μ V' ∧ quadOuter d q θ δ μ V = quadOuter d q θ δ μ V' ∧
    (∫⁻ x, ENNReal.ofReal ‖V x‖ ^ 2) = ∫⁻ x, ENNReal.ofReal ‖V' x‖ ^ 2 := by
  have hz : ∀ x : Euc d, ∀ᵐ z ∂(volume : Measure (Euc d)), V (x - z) = V' (x - z) := fun x =>
    ((volume : Measure (Euc d)).measurePreserving_sub_left x).quasiMeasurePreserving.ae h
  refine ⟨?_, ?_, ?_⟩
  · unfold quadInner
    refine lintegral_congr_ae ?_
    filter_upwards [h] with x hx
    refine lintegral_congr_ae (ae_restrict_of_ae ((hz x).mono fun z hz' => ?_))
    beta_reduce
    rw [hx, hz']
  · unfold quadOuter
    refine lintegral_congr_ae ?_
    filter_upwards [h] with x hx
    refine lintegral_congr_ae (ae_restrict_of_ae ((hz x).mono fun z hz' => ?_))
    beta_reduce
    rw [hx, hz']
  · refine lintegral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]

/-- K3: all smaller jumps are controlled by exterior jumps. The r/delta
factor is retained for restricted inner balls. V need only belong to L2. -/
theorem weighted_inner_from_outer (d q : ℕ) (hd : 1 ≤ d)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ r Λ L : ℝ, 0 < r → r ≤ δ → δ ≤ 1 →
      0 ≤ L → ∀ μ : Euc d → ℝ,
      (∀ x, 0 ≤ μ x ∧ μ x ≤ Λ) →
      (∀ x y, |Real.sqrt (μ x)-Real.sqrt (μ y)| ≤ L*‖x-y‖) →
      ∀ V : Euc d → Euc q, MemLp V 2 volume →
      quadInner d q θ δ r μ V ≤
        ENNReal.ofReal (C*r/δ)*quadOuter d q θ δ μ V +
        ENNReal.ofReal (C*L^2*r*δ^(1-θ))*
          (∫⁻ x, ENNReal.ofReal ‖V x‖^2) := by
  obtain ⟨C, hC, key⟩ := sa16u_K3_meas (q := q) hd hθ0
  refine ⟨C, hC, fun δ r Λ L hr hrδ _ hL μ hμ hlip V hV => ?_⟩
  set V' := hV.aestronglyMeasurable.mk V with hV'
  have hV'm : Measurable V' := hV.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hVV' : V =ᵐ[volume] V' := hV.aestronglyMeasurable.ae_eq_mk
  obtain ⟨e1, e2, e3⟩ := sa16u_congr_V hVV' θ δ r μ
  rw [e1, e2, e3]
  have := key δ r L hr hrδ hL μ (fun x => (hμ x).1) hlip V' hV'm
  refine this.trans (le_of_eq ?_)
  congr 2
  unfold sa16u_V2
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _)]

end K3

end HRS.Whole.AppendixA.Phase2SA16Cutoff
