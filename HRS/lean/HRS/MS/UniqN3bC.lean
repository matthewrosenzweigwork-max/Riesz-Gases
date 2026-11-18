import HRS.MS.UniqN3bA
import HRS.MS.UniqN3bB

/-!
# N3b, part C: the lower bound `B(p²F, q²F) ≥ -C A²` for a Lévy kernel

Route: `UniqT1`-type identity `B(p²F,q²F) = B(pqF,pqF) - ½ ∬ 𝔨(x-y) F(x)F(y) (p(x)q(y)-p(y)q(x))²`
(`n3b_symm`), `B(pqF,pqF) ≥ 0` (`symbolForm_self_nonneg'`), and the remainder bound
`|∬ ...| ≤ (∫ |𝔨| min(|z|²,1)) ∫ (α p² + β q²) F²` (Schur-type, `n3b_remainder`), followed by the
cell-sum lemmas `n3b_decay_mass`, `n3b_ball_mass`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace HRS.MS.UniqN3b

open HRS.MS.UniqM1 HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.WeightAux HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem n3b_min_sq {Δ L M t : ℝ} (ht : 0 ≤ t) (h1 : |Δ| ≤ L * t) (h2 : |Δ| ≤ M) :
    Δ ^ 2 ≤ (L ^ 2 + M ^ 2) * min (t ^ 2) 1 := by
  by_cases h : t ^ 2 ≤ 1
  · rw [min_eq_left h]
    have : Δ ^ 2 ≤ (L * t) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg M, sq_nonneg t]
  · rw [min_eq_right (not_le.1 h).le]
    have : Δ ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    nlinarith [sq_nonneg L]

theorem n3b_W_pt {Lp Lq P : ℝ} {p q : Euc d → ℝ} (hp : HRS.PDE.ToolboxRd.IsLipschitz Lp p)
    (hq : HRS.PDE.ToolboxRd.IsLipschitz Lq q) (hP : ∀ x, 0 ≤ p x ∧ p x ≤ P)
    (hq01 : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (x y : Euc d) :
    (p x * q y - p y * q x) ^ 2 ≤
      (2 * (Lq ^ 2 + 1) * p x ^ 2 + 2 * (Lp ^ 2 + P ^ 2) * q x ^ 2) * min (‖x - y‖ ^ 2) 1 := by
  set μ := min (‖x - y‖ ^ 2) 1 with hμ
  have hμ0 : 0 ≤ μ := le_min (sq_nonneg _) zero_le_one
  have hΔq : (q y - q x) ^ 2 ≤ (Lq ^ 2 + 1 ^ 2) * μ := by
    refine n3b_min_sq (norm_nonneg _) ?_ ?_
    · have := hq y x; rwa [norm_sub_rev] at this
    · rw [abs_le]; constructor <;> linarith [(hq01 x).1, (hq01 x).2, (hq01 y).1, (hq01 y).2]
  have hΔp : (p x - p y) ^ 2 ≤ (Lp ^ 2 + P ^ 2) * μ := by
    refine n3b_min_sq (norm_nonneg _) (hp x y) ?_
    rw [abs_le]; constructor <;> linarith [(hP x).1, (hP x).2, (hP y).1, (hP y).2]
  have e : p x * q y - p y * q x = p x * (q y - q x) + q x * (p x - p y) := by ring
  have hXY : ∀ X Y : ℝ, (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := fun X Y => by
    nlinarith [sq_nonneg (X - Y)]
  have hA : (p x * (q y - q x)) ^ 2 ≤ p x ^ 2 * ((Lq ^ 2 + 1 ^ 2) * μ) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hΔq (sq_nonneg _)
  have hB : (q x * (p x - p y)) ^ 2 ≤ q x ^ 2 * ((Lp ^ 2 + P ^ 2) * μ) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hΔp (sq_nonneg _)
  rw [e]
  calc _ ≤ 2 * (p x * (q y - q x)) ^ 2 + 2 * (q x * (p x - p y)) ^ 2 := hXY _ _
    _ ≤ 2 * (p x ^ 2 * ((Lq ^ 2 + 1 ^ 2) * μ)) + 2 * (q x ^ 2 * ((Lp ^ 2 + P ^ 2) * μ)) := by
        linarith
    _ = _ := by ring

/-- The remainder bound: `|∬ 𝔨 F F W²| ≤ (∫ |𝔨| min(|z|²,1)) ∫ (α p² + β q²) F²`. -/
theorem n3b_remainder {k : Euc d → ℝ} (hkev : ∀ z, k (-z) = k z)
    (hρ : Integrable (fun z : Euc d => |k z| * min (‖z‖ ^ 2) 1) volume)
    {Lp Lq P : ℝ} {p q F : Euc d → ℝ} (hp : HRS.PDE.ToolboxRd.IsLipschitz Lp p)
    (hq : HRS.PDE.ToolboxRd.IsLipschitz Lq q) (hP : ∀ x, 0 ≤ p x ∧ p x ≤ P)
    (hq01 : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hg : Integrable (fun x => (2 * (Lq ^ 2 + 1) * p x ^ 2 + 2 * (Lp ^ 2 + P ^ 2) * q x ^ 2) *
      F x ^ 2) volume) :
    |∫ z : Euc d × Euc d, k z.2 * F z.1 * F (z.1 - z.2) *
        (p z.1 * q (z.1 - z.2) - p (z.1 - z.2) * q z.1) ^ 2| ≤
      (∫ z, |k z| * min (‖z‖ ^ 2) 1) *
        ∫ x, (2 * (Lq ^ 2 + 1) * p x ^ 2 + 2 * (Lp ^ 2 + P ^ 2) * q x ^ 2) * F x ^ 2 := by
  set ρ0 : Euc d → ℝ := fun z => |k z| * min (‖z‖ ^ 2) 1 with hρ0
  set u : Euc d → ℝ := fun x => 2 * (Lq ^ 2 + 1) * p x ^ 2 + 2 * (Lp ^ 2 + P ^ 2) * q x ^ 2 with hu
  set g : Euc d → ℝ := fun x => u x * F x ^ 2 with hgdef
  obtain ⟨h1, e1⟩ := integrable_sub_mul_fst hρ hg
  obtain ⟨h2, e2⟩ := integrable_sub_mul_snd hρ hg
  set Df : Euc d × Euc d → ℝ := fun z => (1 / 2) * (ρ0 (z.1 - z.2) * g z.1 + ρ0 (z.1 - z.2) * g z.2)
    with hDf
  have hDfi : Integrable Df volume := (h1.add h2).const_mul _
  set f' : Euc d × Euc d → ℝ := fun z => k (z.1 - z.2) * F z.1 * F z.2 *
    (p z.1 * q z.2 - p z.2 * q z.1) ^ 2 with hf'
  have hu0 : ∀ x, 0 ≤ u x := fun x => by simp only [hu]; positivity
  have hpt : ∀ z : Euc d × Euc d, ‖f' z‖ ≤ Df z := by
    intro z
    obtain ⟨x, y⟩ := z
    simp only [hf', hDf, hgdef]
    set W := (p x * q y - p y * q x) with hW
    have hWx : W ^ 2 ≤ u x * min (‖x - y‖ ^ 2) 1 := n3b_W_pt hp hq hP hq01 x y
    have hWy : W ^ 2 ≤ u y * min (‖x - y‖ ^ 2) 1 := by
      have := n3b_W_pt hp hq hP hq01 y x
      rw [norm_sub_rev] at this
      have e : (p y * q x - p x * q y) ^ 2 = W ^ 2 := by rw [hW]; ring
      rwa [e] at this
    have hk0 : 0 ≤ |k (x - y)| := abs_nonneg _
    have hFF : |F x| * |F y| ≤ (1 / 2) * (F x ^ 2 + F y ^ 2) := by
      nlinarith [sq_nonneg (|F x| - |F y|), sq_abs (F x), sq_abs (F y)]
    rw [Real.norm_eq_abs]
    have : |k (x - y) * F x * F y * W ^ 2| = |k (x - y)| * (|F x| * |F y|) * W ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg W)]; ring
    rw [this]
    have hμ0 : 0 ≤ min (‖x - y‖ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    calc |k (x - y)| * (|F x| * |F y|) * W ^ 2
        ≤ |k (x - y)| * ((1 / 2) * (F x ^ 2 + F y ^ 2)) * W ^ 2 := by gcongr
      _ = (1 / 2) * (|k (x - y)| * W ^ 2 * F x ^ 2 + |k (x - y)| * W ^ 2 * F y ^ 2) := by ring
      _ ≤ (1 / 2) * (|k (x - y)| * (u x * min (‖x - y‖ ^ 2) 1) * F x ^ 2 +
            |k (x - y)| * (u y * min (‖x - y‖ ^ 2) 1) * F y ^ 2) := by
          gcongr
      _ = _ := by simp only [hρ0]; ring
  have hint : ‖∫ z, f' z‖ ≤ ∫ z, Df z :=
    norm_integral_le_of_norm_le hDfi (Eventually.of_forall hpt)
  have hDfint : ∫ z, Df z = (∫ z, ρ0 z) * ∫ x, g x := by
    simp only [hDf]
    rw [integral_const_mul, integral_add h1 h2, e1, e2]; ring
  have hcomp : (fun z : Euc d × Euc d => k z.2 * F z.1 * F (z.1 - z.2) *
      (p z.1 * q (z.1 - z.2) - p (z.1 - z.2) * q z.1) ^ 2) = f' ∘ (shear d) := by
    funext z
    simp [hf', shear, sub_sub_cancel]
  have hI : ∫ z : Euc d × Euc d, (f' ∘ shear d) z = ∫ z, f' z :=
    measurePreserving_shear.integral_comp' f'
  rw [Real.norm_eq_abs] at hint
  rw [hcomp]
  exact (le_of_eq (congrArg abs hI)).trans (hint.trans (le_of_eq hDfint))

/-- **N3b.**  Lower bound on the two-multiplier form `B(p²F, q²F)` for a Lévy kernel. -/
theorem n3b_sign (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {m : Euc d → ℝ}
    (hm : IsHomogSymbol θ m) {k : Euc d → ℝ} (hk : IsLevyKernel θ m k)
    (Cρ Lp Lq R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Euc d) (p q F : Euc d → ℝ) (A LF BF : ℝ), 0 ≤ A →
      (∀ x, 0 ≤ p x ∧ p x ≤ Cρ * (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2))) →
      HRS.PDE.ToolboxRd.IsLipschitz Lp p →
      (∀ x, 0 ≤ q x ∧ q x ≤ 1) → HRS.PDE.ToolboxRd.IsLipschitz Lq q →
      Function.support q ⊆ closedBall a R →
      HRS.PDE.ToolboxRd.IsLipschitz LF F → (∀ x, |F x| ≤ BF) → LocMass A F →
      -C * A ^ 2 ≤ symbolForm m (fun x => p x ^ 2 * F x) (fun x => q x ^ 2 * F x) := by
  have hkm : Measurable k := measurable_of_smooth hk.smooth
  have hρ : Integrable (fun z : Euc d => |k z| * min (‖z‖ ^ 2) 1) volume :=
    integrable_kernel_min hd hθ0 hθ2 hkm hk.bound
  set I0 : ℝ := ∫ z, |k z| * min (‖z‖ ^ 2) 1 with hI0
  have hI00 : 0 ≤ I0 := integral_nonneg fun z => mul_nonneg (abs_nonneg _) (le_min (sq_nonneg _) zero_le_one)
  have hκ : (d : ℝ) < (d : ℝ) + 3 := by linarith
  obtain ⟨K1, hK10, hK1⟩ := n3b_decay_mass (d := d) hκ
  obtain ⟨N, hN0, hN⟩ := n3b_ball_mass d (|R| + 1)
  set P : ℝ := |Cρ| with hPdef
  set α : ℝ := 2 * (Lq ^ 2 + 1) with hα
  set β : ℝ := 2 * (Lp ^ 2 + P ^ 2) with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  refine ⟨(1 / 2) * I0 * (α * (K1 * Cρ ^ 2) + β * N), by positivity, ?_⟩
  intro a p q F A LF BF hA hpd hpL hq01 hqL hqs hFL hFb hLoc
  have hFc : Continuous F := isLipschitz_continuous hFL
  have hFm : Measurable F := hFc.measurable
  have hpc : Continuous p := isLipschitz_continuous hpL
  have hqc : Continuous q := isLipschitz_continuous hqL
  have hP : ∀ x, 0 ≤ p x ∧ p x ≤ P := fun x => by
    refine ⟨(hpd x).1, (hpd x).2.trans ?_⟩
    have h1 : (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by
        have : (0 : ℝ) ≤ ((d : ℝ) + 3) / 2 := by positivity
        linarith)
    have h2 : 0 ≤ (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) := by positivity
    calc Cρ * (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) ≤ |Cρ| * (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h2
      _ ≤ |Cρ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = P := mul_one _
  have hP' : ∀ x, |p x| ≤ P := fun x => by rw [abs_of_nonneg (hP x).1]; exact (hP x).2
  have hq' : ∀ x, |q x| ≤ 1 := fun x => by rw [abs_of_nonneg (hq01 x).1]; exact (hq01 x).2
  -- decay of p²
  have hpsq : ∀ x, p x ^ 2 ≤ Cρ ^ 2 * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by
    intro x
    obtain ⟨h0, h1⟩ := hpd x
    have hb : 0 ≤ (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) := by positivity
    calc p x ^ 2 ≤ (Cρ * (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2))) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = Cρ ^ 2 * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2))) 2,
            ← Real.rpow_mul (by positivity)]
          congr 2; push_cast; ring
  have hpint : Integrable (fun x => p x ^ 2) volume := by
    have hdom : Integrable (fun x : Euc d => Cρ ^ 2 * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) volume :=
      (integrable_one_add_norm (E := Euc d) (μ := volume) (r := (d : ℝ) + 3)
        (by simpa using hκ)).const_mul _
    refine hdom.mono' (hpc.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpsq x
  -- Lipschitz and Sobolev membership
  have hLa := isLipschitz_congr (v := fun x => p x ^ 2 * F x) (fun x => by ring)
    (isLipschitz_mul (isLipschitz_mul hpL hpL hP' hP')
      hFL (fun x => by rw [abs_mul]; exact mul_le_mul (hP' x) (hP' x) (abs_nonneg _) (by
        exact (abs_nonneg _).trans (hP' x))) hFb)
  have hLb := isLipschitz_congr (v := fun x => q x ^ 2 * F x) (fun x => by ring)
    (isLipschitz_mul (isLipschitz_mul hqL hqL hq' hq')
      hFL (fun x => by rw [abs_mul]; exact mul_le_mul (hq' x) (hq' x) (abs_nonneg _) zero_le_one) hFb)
  have hLc := isLipschitz_mul (isLipschitz_mul hpL hqL hP' hq')
      hFL (fun x => by rw [abs_mul]; exact mul_le_mul (hP' x) (hq' x) (abs_nonneg _) (by
        exact (abs_nonneg _).trans (hP' x))) hFb
  have hsupp : ∀ x, x ∉ closedBall a R → q x = 0 := fun x hx => by
    by_contra h
    exact hx (hqs (Function.mem_support.2 h))
  have hcsb : HasCompactSupport (fun x => q x ^ 2 * F x) :=
    HasCompactSupport.intro (isCompact_closedBall a R) fun x hx => by simp [hsupp x hx]
  have hcsc : HasCompactSupport (fun x => p x * q x * F x) :=
    HasCompactSupport.intro (isCompact_closedBall a R) fun x hx => by simp [hsupp x hx]
  have hHa := n3b_memSobolev_p2F hpL hP' hpint hFL hFb
  have hHb := HRS.MS.UniqT1.t1_memSobolev_one hLb hcsb
  have hHc := HRS.MS.UniqT1.t1_memSobolev_one hLc hcsc
  have hid := n3b_symm hk hLa hLb hLc hHa hHb hHc
  have hnn : 0 ≤ symbolForm m (fun x => p x * q x * F x) (fun x => p x * q x * F x) :=
    symbolForm_self_nonneg' hm.nonneg _
  -- mass bounds
  obtain ⟨hi1, hb1⟩ := hK1 A F hA hFm hLoc (fun x => p x ^ 2) (Cρ ^ 2) (sq_nonneg _)
    (hpc.pow 2).aestronglyMeasurable (fun x => ⟨sq_nonneg _, hpsq x⟩)
  obtain ⟨hi2, hb2⟩ := hN A F hA hFm hLoc a (fun x => q x ^ 2) (hqc.pow 2).aestronglyMeasurable
    (fun x => ⟨sq_nonneg _, by nlinarith [(hq01 x).1, (hq01 x).2]⟩)
    (fun x hx => by
      have : x ∉ closedBall a R := fun h => hx (by
        rw [mem_ball, dist_eq_norm]; rw [mem_closedBall, dist_eq_norm] at h
        linarith [le_abs_self R])
      rw [hsupp x this]; ring)
  have hgint : Integrable (fun x => (α * p x ^ 2 + β * q x ^ 2) * F x ^ 2) volume := by
    have := (hi1.const_mul α).add (hi2.const_mul β)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  have hrem := n3b_remainder (hkev := hk.even) hρ hpL hqL hP hq01 hgint
  have hGs : ∫ x, (α * p x ^ 2 + β * q x ^ 2) * F x ^ 2 =
      α * (∫ x, p x ^ 2 * F x ^ 2) + β * (∫ x, q x ^ 2 * F x ^ 2) := by
    have e : (fun x => (α * p x ^ 2 + β * q x ^ 2) * F x ^ 2) =
        fun x => α * (p x ^ 2 * F x ^ 2) + β * (q x ^ 2 * F x ^ 2) := by funext x; ring
    rw [e, integral_add (hi1.const_mul α) (hi2.const_mul β), integral_const_mul, integral_const_mul]
  rw [hGs] at hrem
  rw [hid]
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hX : α * (∫ x, p x ^ 2 * F x ^ 2) + β * (∫ x, q x ^ 2 * F x ^ 2) ≤
      α * (K1 * Cρ ^ 2 * A ^ 2) + β * (N * A ^ 2) :=
    add_le_add (mul_le_mul_of_nonneg_left hb1 hα0) (mul_le_mul_of_nonneg_left hb2 hβ0)
  have hrem2 : |∫ z : Euc d × Euc d, k z.2 * F z.1 * F (z.1 - z.2) *
        (p z.1 * q (z.1 - z.2) - p (z.1 - z.2) * q z.1) ^ 2| ≤
      I0 * (α * (K1 * Cρ ^ 2 * A ^ 2) + β * (N * A ^ 2)) :=
    hrem.trans (mul_le_mul_of_nonneg_left hX hI00)
  have := (abs_le.1 hrem2).2
  nlinarith [this, hnn]

end HRS.MS.UniqN3b
