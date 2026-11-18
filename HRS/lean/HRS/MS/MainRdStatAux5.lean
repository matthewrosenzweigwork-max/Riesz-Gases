import HRS.MS.MainRdStatAux4
import HRS.MS.QMul

/-!
# SA2, packet 5: the index-1 test-cutoff inequality and the product `h_{ab} = ∇f_a·∇f_b`

* `sa2_pathwise_core`: the pathwise inequality of `B:lem:test-cutoff` (copy of `pathwise_core` of `AppendixALemmas`) with the Sobolev index
  `mm` in place of `m_* - 1`; only `(d-s)/2 ≤ mm` is used.  For `s ≥ d-2`, `mm = 1` suffices.
* the Leibniz estimate `‖χ_z ∇f·∇g‖_{H^1} ≤ C ‖f‖ ‖g‖`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

theorem sa2_pathwise_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (mm : ℕ) (hmm : ((d : ℝ) - s) / 2 ≤ (mm : ℝ)) (χ : Euc d → ℝ)
    (K Lp : ℝ) (hK0 : 0 ≤ K) (hLp0 : 0 ≤ Lp)
    (hK : ∀ (N : ℕ) (h : Euc d → ℝ) (U : ℝ),
      (∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev (mm : ℝ) (fun x => χ (x - z) * h x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq (mm : ℝ) (fun x => χ (x - z) * h x) ≤ U ^ 2) →
      HRS.PDE.ToolboxRd.MemSobolev (mm : ℝ) (fun x => Q09A.plat d N x * h x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq (mm : ℝ) (fun x => Q09A.plat d N x * h x) ≤
          K ^ 2 * ((2 * N + 1 : ℝ) ^ d) * U ^ 2)
    (hLp : ∀ (N : ℕ) (x y : Euc d), |Q09A.plat d N x - Q09A.plat d N y| ≤ Lp * ‖x - y‖)
    (C₁ C₀ : ℝ) (hpair : WholeCoercivityPair d s C₀ C₁)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (N : ℕ) (hN : 2 ≤ N) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ)
    (hρΛ : ∀ x, ρ x ≤ Λ) (hmom : Integrable (fun x => ‖x‖ ^ 2 * ρ x))
    (X : EucConfig d N) (hX : Function.Injective X) (h : Euc d → ℝ) (b l Uv : ℝ)
    (hb0 : 0 ≤ b) (hl0 : 0 ≤ l) (hU0 : 0 ≤ Uv) (hbd : ∀ x, |h x| ≤ b)
    (hlip : ∀ x y : Euc d, |h x - h y| ≤ l * ‖x - y‖)
    (hSob : ∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev (mm : ℝ) (fun x => χ (x - z) * h x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (mm : ℝ) (fun x => χ (x - z) * h x) ≤ Uv ^ 2)
    (R : ℝ) (hR : 1 ≤ R) :
    |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h| ≤
      (|C₁| * (Lp + 1) + |C₁| * (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d)) + 1) * (b + l + Uv) *
        (R ^ ((d : ℝ) / 2) * (smearScale d N Λ +
            Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N)) +
          (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / R ^ 2) := by
  classical
  set n : ℝ := b + l + Uv with hndef
  have hn0 : 0 ≤ n := by positivity
  have hcont : Continuous h :=
    HRS.PDE.ToolboxRd.FourierAux.continuous_of_isLipschitz (L := l) hlip
  have hRpos : 0 < R := by linarith
  set Nr : ℕ := ⌈(d : ℝ) * R⌉₊ + 1 with hNr
  have hNr1 : (d : ℝ) * R + 1 ≤ Nr := by
    have := Nat.le_ceil ((d : ℝ) * R)
    rw [hNr]; push_cast; linarith
  have hNr2 : (Nr : ℝ) ≤ (d : ℝ) * R + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (d : ℝ) * R by positivity)
    rw [hNr]; push_cast; linarith
  set ψ : Euc d → ℝ := fun x => Q09A.plat d Nr x * h x with hψdef
  have hplat_cont : Continuous (Q09A.plat d Nr) := (Q09A.plat_contDiff d Nr).continuous
  have hψcont : Continuous ψ := hplat_cont.mul hcont
  have hψlip : HRS.PDE.ToolboxRd.IsLipschitz ((Lp + 1) * n) ψ := by
    intro x y
    have h1 := hLp Nr x y
    have h2 := hbd x
    have h3 := hlip x y
    have hp1 := Q09A.plat_nonneg d Nr y
    have hp2 := Q09A.plat_le_one d Nr y
    have e : ψ x - ψ y = (Q09A.plat d Nr x - Q09A.plat d Nr y) * h x +
        Q09A.plat d Nr y * (h x - h y) := by simp only [hψdef]; ring
    rw [e]
    calc |(Q09A.plat d Nr x - Q09A.plat d Nr y) * h x + Q09A.plat d Nr y * (h x - h y)|
        ≤ |(Q09A.plat d Nr x - Q09A.plat d Nr y) * h x| + |Q09A.plat d Nr y * (h x - h y)| :=
          abs_add_le _ _
      _ ≤ Lp * ‖x - y‖ * b + 1 * (l * ‖x - y‖) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp1]
          gcongr
      _ ≤ (Lp + 1) * n * ‖x - y‖ := by
          have hxy := norm_nonneg (x - y)
          have : b ≤ n := by simp only [hndef]; linarith
          have : l ≤ n := by simp only [hndef]; linarith
          nlinarith [mul_nonneg hLp0 hxy, mul_nonneg hxy hb0, mul_nonneg hLp0 (mul_nonneg hxy hb0)]
  have hψsupp : HasCompactSupport ψ := by
    have hps : HasCompactSupport (Q09A.plat d Nr) :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) ((Nr : ℝ) + 2)) fun x hx => by
        by_contra hne
        exact hx (by simpa using Q09A.plat_support hd hne)
    exact hps.mul_right
  -- the Sobolev bound
  obtain ⟨hMS, hnorm⟩ := hK Nr h Uv hSob
  have hRd : ((2 * (Nr : ℝ) + 1) ^ d) ≤ (((2 * d + 5 : ℕ) : ℝ) * R) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith
  have ha0 : 0 ≤ ((d : ℝ) - s) / 2 := by linarith
  have ha1 : ((d : ℝ) - s) / 2 ≤ (mm : ℝ) := hmm
  obtain ⟨hI, hIle⟩ := Q09A.hom_le hMS ha0 ha1
  have hHom : HasFiniteHomSobolevRd (((d : ℝ) - s) / 2) ψ := ⟨hMS.1, hI⟩
  have hhomle : homSobolevRd (((d : ℝ) - s) / 2) ψ ≤
      K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n := by
    unfold homSobolevRd
    refine (Real.sqrt_le_sqrt (hIle.trans hnorm)).trans ?_
    have h1 : K ^ 2 * ((2 * (Nr : ℝ) + 1) ^ d) * Uv ^ 2 ≤
        (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2 := by
      have hs : Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) ^ 2 = ((2 * d + 5 : ℕ) : ℝ) ^ d :=
        Real.sq_sqrt (by positivity)
      have hP : (R ^ ((d : ℝ) / 2)) ^ 2 = R ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]
        norm_num
      have hUn : Uv ≤ n := by simp only [hndef]; linarith
      calc K ^ 2 * ((2 * (Nr : ℝ) + 1) ^ d) * Uv ^ 2
          ≤ K ^ 2 * ((((2 * d + 5 : ℕ) : ℝ) * R) ^ d) * n ^ 2 := by
            gcongr
        _ = (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2 := by
            have e : (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2 =
                K ^ 2 * (Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d)) ^ 2 * (R ^ ((d : ℝ) / 2)) ^ 2 *
                  n ^ 2 := by ring
            rw [e, hs, hP]
            ring
    calc Real.sqrt (K ^ 2 * ((2 * (Nr : ℝ) + 1) ^ d) * Uv ^ 2)
        ≤ Real.sqrt ((K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  -- coercivity for the compactly supported part
  obtain ⟨-, hC1pos, hcoer⟩ := hpair
  have hcor := hcoer Λ hΛ N hN ρ hρ hρΛ (fun _ => Q09A.log_integrable_withDensityReal hρ hmom) X hX ψ ((Lp + 1) * n) (by positivity) hψlip hψsupp hHom
  -- the far part
  have hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q09A.measure_isProb hρ
  have hfar : ∀ x : Euc d, |h x - ψ x| ≤ b * ‖x‖ ^ 2 / R ^ 2 := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · have : Q09A.plat d Nr x = 1 := Q09A.plat_eq_one hNr1 hx
      simp only [hψdef, this, one_mul, sub_self, abs_zero]
      positivity
    · push Not at hx
      have hp0 := Q09A.plat_nonneg d Nr x
      have hp1 := Q09A.plat_le_one d Nr x
      have hR2 : 1 ≤ ‖x‖ ^ 2 / R ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc |h x - ψ x| = (1 - Q09A.plat d Nr x) * |h x| := by
            simp only [hψdef]
            rw [show h x - Q09A.plat d Nr x * h x = (1 - Q09A.plat d Nr x) * h x by ring, abs_mul,
              abs_of_nonneg (by linarith)]
        _ ≤ 1 * b := by
            gcongr
            · linarith
            · exact hbd x
        _ ≤ b * (‖x‖ ^ 2 / R ^ 2) := by nlinarith
        _ = b * ‖x‖ ^ 2 / R ^ 2 := by ring
  have hψb : ∀ x, |ψ x| ≤ b := by
    intro x
    simp only [hψdef]
    rw [abs_mul, abs_of_nonneg (Q09A.plat_nonneg d Nr x)]
    calc Q09A.plat d Nr x * |h x| ≤ 1 * b :=
          mul_le_mul (Q09A.plat_le_one d Nr x) (hbd x) (abs_nonneg _) zero_le_one
      _ = b := one_mul b
  have hN0 : 0 < N := by omega
  have hfarE : |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.empirical X) ψ| ≤
      b * secondMomentOf (HRS.Whole.empirical X) / R ^ 2 :=
    Q09A.pair_far _ h ψ b R hfar (Q09A.integrable_empirical hN0 X _) (Q09A.integrable_empirical hN0 X _)
      (Q09A.integrable_empirical hN0 X _)
  have hfarM : |HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ| ≤
      b * secondMomentOf (HRS.Whole.withDensityReal ρ) / R ^ 2 :=
    Q09A.pair_far _ h ψ b R hfar
      (Integrable.of_bound hcont.aestronglyMeasurable b (Eventually.of_forall fun x => by
        simpa using hbd x))
      (Integrable.of_bound hψcont.aestronglyMeasurable b (Eventually.of_forall fun x => by
        simpa using hψb x))
      (Q09A.integrable_sq_withDensityReal hρ hmom)
  -- assemble
  set lam : ℝ := smearScale d N Λ with hlam
  set E0 : ℝ := Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N) with hE0
  set P : ℝ := R ^ ((d : ℝ) / 2) with hP
  set M : ℝ := secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ) with hM
  have hlam0 : 0 ≤ lam := by rw [hlam]; unfold smearScale; exact Real.rpow_nonneg (by positivity) _
  have hE00 : 0 ≤ E0 := Real.sqrt_nonneg _
  have hP1 : 1 ≤ P := Real.one_le_rpow hR (by positivity)
  have hM0 : 0 ≤ M := add_nonneg (Q09A.secondMomentOf_nonneg _) (Q09A.secondMomentOf_nonneg _)
  have hhom0 : 0 ≤ homSobolevRd (((d : ℝ) - s) / 2) ψ := Real.sqrt_nonneg _
  have hbn : b ≤ n := by simp only [hndef]; linarith
  set cc : ℝ := |C₁| with hcc
  set s0 : ℝ := Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) with hs0def
  have hs00 : 0 ≤ s0 := Real.sqrt_nonneg _
  have hcc0 : 0 ≤ cc := abs_nonneg _
  have h1 : |HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ| ≤
      cc * (Lp + 1) * n * lam + cc * (K * s0) * P * n * E0 := by
    refine hcor.trans ?_
    have e1 : C₁ * lam * ((Lp + 1) * n) ≤ cc * (Lp + 1) * n * lam := by
      calc C₁ * lam * ((Lp + 1) * n) = C₁ * (lam * ((Lp + 1) * n)) := by ring
        _ ≤ |C₁| * (lam * ((Lp + 1) * n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = cc * (Lp + 1) * n * lam := by rw [hcc]; ring
    have e2 : C₁ * homSobolevRd (((d : ℝ) - s) / 2) ψ * E0 ≤ cc * (K * s0) * P * n * E0 := by
      calc C₁ * homSobolevRd (((d : ℝ) - s) / 2) ψ * E0
          ≤ |C₁| * homSobolevRd (((d : ℝ) - s) / 2) ψ * E0 := by
            gcongr
            exact le_abs_self _
        _ ≤ |C₁| * (K * s0 * P * n) * E0 := by gcongr
        _ = cc * (K * s0) * P * n * E0 := by rw [hcc]; ring
    linarith
  have h2 : |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.empirical X) ψ| + |HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h -
      HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ| ≤ n * M / R ^ 2 := by
    refine (add_le_add hfarE hfarM).trans ?_
    rw [← add_div, ← mul_add]
    gcongr
  have htri : |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h| ≤
      |HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ| +
      (|HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.empirical X) ψ| +
        |HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ|) := by
    have e : HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h =
        (HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ) +
        (HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.empirical X) ψ) -
        (HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ) := by ring
    rw [e]
    have h1 := abs_sub ((HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ) +
        (HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.empirical X) ψ))
      (HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ)
    have h2 := abs_add_le (HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ)
      (HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.empirical X) ψ)
    linarith
  have key := Q09A.final_ineq cc (Lp + 1) K s0 n lam E0 P M R hcc0 (by linarith) hK0 hs00 hn0 hlam0 hE00 hP1 hM0
  calc |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h|
      ≤ |HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ| +
        (|HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.empirical X) ψ| +
          |HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ|) := htri
    _ ≤ (cc * (Lp + 1) * n * lam + cc * (K * s0) * P * n * E0) + n * M / R ^ 2 := by
        gcongr
    _ ≤ _ := key


/-! ### A cutoff `ζ = 1` on `B(0,3)`, the `H²` bound of `ζ_z f`, and the localised second derivatives -/

theorem sa2_zeta {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ (ζ : Euc d → ℝ) (C : ℝ), ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ (∀ x, ‖x‖ ≤ 3 → ζ x = 1) ∧
      0 ≤ C ∧ ∀ (z : Euc d) (f : Euc d → ℝ), sobolevNormE ((2 : ℕ) : ℝ) (fun x => ζ (x - z) * f x) ≤
        ENNReal.ofReal C * ulocNormE 2 χ f := by
  classical
  let b : ContDiffBump (0 : Euc d) := ⟨3, 4, by norm_num, by norm_num⟩
  obtain ⟨t, -, ht, hcov⟩ := (isCompact_closedBall (0 : Euc d) 4).finite_cover_balls (e := 1) one_pos
  set Y : Finset (Euc d) := ht.toFinset with hY
  have hYcov : ∀ p : Euc d, ‖p‖ ≤ 4 → ∃ y ∈ Y, χ (p - y) = 1 := by
    intro p hp
    have hp' : p ∈ Metric.closedBall (0 : Euc d) 4 := by simpa using hp
    obtain ⟨y, hyt, hpy⟩ := Set.mem_iUnion₂.1 (hcov hp')
    refine ⟨y, by simpa [hY] using hyt, hχ.2.2.2.2 (p - y) ?_⟩
    simpa [dist_eq_norm, Metric.mem_ball, mem_closedBall_zero_iff] using hpy.le
  have hsup : ∀ p : Euc d, b p ≠ 0 → ‖p‖ ≤ 4 := by
    intro p hp
    have : p ∈ Function.support b := hp
    rw [b.support_eq] at this
    have h4 : ‖p‖ < 4 := by simpa [b] using this
    exact h4.le
  obtain ⟨C, hC0, hC⟩ := HRS.MS.Ul.ul0_key 2 b χ b.contDiff b.hasCompactSupport hχ.1 hχ.2.1 Y 4 0 4
    (by norm_num) (by norm_num) hsup hYcov
  refine ⟨b, C * Y.card, b.contDiff, b.hasCompactSupport, fun x hx =>
    b.one_of_mem_closedBall (by simpa using hx), by positivity, fun z f => ?_⟩
  refine (hC z z (by simp) f).trans ?_
  have hsum : ∑ y ∈ Y, sobolevNormE ((2 : ℕ) : ℝ) (fun x => χ (x - (z + y)) * f x) ≤
      Y.card • ulocNormE 2 χ f := by
    calc ∑ y ∈ Y, sobolevNormE ((2 : ℕ) : ℝ) (fun x => χ (x - (z + y)) * f x)
        ≤ ∑ _y ∈ Y, ulocNormE 2 χ f := Finset.sum_le_sum fun y _ =>
          le_iSup (fun z : Euc d => sobolevNormE ((2 : ℕ) : ℝ) fun x => χ (x - z) * f x) (z + y)
      _ = Y.card • ulocNormE 2 χ f := by simp
  calc ENNReal.ofReal C * ∑ y ∈ Y, sobolevNormE ((2 : ℕ) : ℝ) (fun x => χ (x - (z + y)) * f x)
      ≤ ENNReal.ofReal C * (Y.card • ulocNormE 2 χ f) := by gcongr
    _ = ENNReal.ofReal (C * Y.card) * ulocNormE 2 χ f := by
        rw [ENNReal.ofReal_mul hC0.le, ENNReal.ofReal_natCast, nsmul_eq_mul, mul_assoc]

theorem sa2_loc2 {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euc d → ℝ), ContDiff ℝ 2 f → ∀ X : ℝ, 0 ≤ X → ulocNormE 2 χ f ≤ ENNReal.ofReal X →
      ∀ (z : Euc d) (i j : Fin d),
        ∫⁻ x, ENNReal.ofReal ((χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) ^ 2) ≤ ENNReal.ofReal ((C * X) ^ 2) := by
  obtain ⟨ζ, Cz, hζd, hζc, hζ1, hCz0, hζn⟩ := sa2_zeta hχ
  refine ⟨Cz, hCz0, fun f hf X hX hul z i j => ?_⟩
  set G : Euc d → ℝ := fun x => ζ (x - z) * f x with hG
  have hGd : ContDiff ℝ 2 G := by
    have hζ2 : ContDiff ℝ 2 ζ := by simpa using contDiff_infty.1 hζd 2
    have h1 : ContDiff ℝ 2 (fun x : Euc d => ζ (x - z)) :=
      hζ2.comp (contDiff_id.sub contDiff_const)
    exact h1.mul hf
  have hGc : HasCompactSupport G := by
    have h1 : HasCompactSupport (fun x : Euc d => ζ (x - z)) :=
      hζc.comp_homeomorph (Homeomorph.subRight z)
    exact h1.mul_right
  have hpt : ∀ x : Euc d, (χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)) ^ 2 ≤
      (partialDeriv (![i, j] : Fin 2 → Fin d) G x) ^ 2 := by
    intro x
    by_cases hx : χ (x - z) = 0
    · rw [hx, zero_mul, zero_pow two_ne_zero]; exact sq_nonneg _
    · have hxs : x - z ∈ tsupport χ := subset_tsupport _ hx
      have hxb : ‖x - z‖ < 2 := by simpa using hχ.2.2.1 hxs
      have hev : G =ᶠ[nhds x] f := by
        have hopen : Metric.ball z 3 ∈ nhds x := Metric.isOpen_ball.mem_nhds (by
          rw [Metric.mem_ball, dist_eq_norm]; linarith)
        filter_upwards [hopen] with y hy
        have : ‖y - z‖ ≤ 3 := by
          rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le
        simp [hG, hζ1 _ this]
      have h2 : fderiv ℝ (fderiv ℝ G) x = fderiv ℝ (fderiv ℝ f) x :=
        (hev.fderiv (𝕜 := ℝ)).fderiv_eq
      have e : partialDeriv (![i, j] : Fin 2 → Fin d) G x =
          fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        unfold partialDeriv
        rw [iteratedFDeriv_two_apply, h2]
        simp
      rw [e, mul_pow]
      have hχ1 : χ (x - z) ^ 2 ≤ 1 := by
        have := hχ.2.2.2.1 (x - z)
        nlinarith [this.1, this.2]
      nlinarith [sq_nonneg (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))]
  calc ∫⁻ x, ENNReal.ofReal ((χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) ^ 2)
      ≤ ∫⁻ x, ENNReal.ofReal ((partialDeriv (![i, j] : Fin 2 → Fin d) G x) ^ 2) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ ≤ sobolevNormE ((2 : ℕ) : ℝ) G ^ 2 := HRS.MS.UlocMW.um_deriv_le hGd hGc (le_refl 2) _
    _ ≤ ENNReal.ofReal ((Cz * X) ^ 2) := by
        have h1 : sobolevNormE ((2 : ℕ) : ℝ) G ≤ ENNReal.ofReal (Cz * X) := by
          refine (hζn z f).trans ?_
          rw [ENNReal.ofReal_mul hCz0]
          gcongr
        calc sobolevNormE ((2 : ℕ) : ℝ) G ^ 2 ≤ ENNReal.ofReal (Cz * X) ^ 2 := by gcongr
          _ = ENNReal.ofReal ((Cz * X) ^ 2) := by
            rw [ENNReal.ofReal_pow (mul_nonneg hCz0 hX)]


theorem sa2_le_of_sq_le {a : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 ≤ ENNReal.ofReal (c ^ 2)) :
    a ≤ ENNReal.ofReal c := by
  have h1 : (a ^ 2) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (c ^ 2)) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h (by norm_num)
  have h2 : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [h2, ENNReal.ofReal_pow hc, h2] at h1
  exact h1

theorem sa2_apply_le {f : Euc d → ℝ} {X : ℝ} (hX : ∀ x, ‖fderiv ℝ f x‖ ≤ X) (x : Euc d) (j : Fin d) :
    |fderiv ℝ f x (EuclideanSpace.single j 1)| ≤ X := by
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ f x).le_opNorm _).trans ?_
  simpa using hX x

/-- the `H¹` norm of the localised gradient component -/
theorem sa2_loc1 {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euc d → ℝ), ContDiff ℝ 2 f → ∀ X : ℝ, 0 ≤ X → (∀ x, ‖fderiv ℝ f x‖ ≤ X) →
      ulocNormE 2 χ f ≤ ENNReal.ofReal X → ∀ (z : Euc d) (j : Fin d),
        sobolevNormE ((1 : ℕ) : ℝ) (fun x => χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1)) ≤
          ENNReal.ofReal (C * X) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := sa2_loc2 hχ
  have hχ1 : ContDiff ℝ 1 χ := by simpa using contDiff_infty.1 hχ.1 1
  obtain ⟨Bχ0, hBχ0⟩ := (hχ.2.1.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hχ1.continuous_fderiv one_ne_zero)
  set Bχ : ℝ := max Bχ0 0 with hBχ
  have hBχ' : ∀ y, ‖fderiv ℝ χ y‖ ≤ Bχ := fun y => (hBχ0 y).trans (le_max_left _ _)
  have hBχ00 : 0 ≤ Bχ := le_max_right _ _
  set Vn : ℝ≥0∞ := volume (Metric.ball (0 : Euc d) 2) with hVn
  have hVfin : Vn ≠ ⊤ := measure_ball_lt_top.ne
  set V : ℝ := Vn.toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVn' : ENNReal.ofReal V = Vn := ENNReal.ofReal_toReal hVfin
  set K : ℝ := V + d * (2 * Bχ ^ 2 * V + 2 * C₂ ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun f hf X hX hbd hul z j => ?_⟩
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  set a : Euc d → ℝ := fun x => fderiv ℝ f x (EuclideanSpace.single j 1) with ha
  set u : Euc d → ℝ := fun x => χ (x - z) * a x with hu
  have hchi_z : ContDiff ℝ 1 (fun x : Euc d => χ (x - z)) := hχ1.comp (contDiff_id.sub contDiff_const)
  have hac : ContDiff ℝ 1 a :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).contDiff.comp hf1
  have hud : ContDiff ℝ 1 u := hchi_z.mul hac
  have huc : HasCompactSupport u :=
    (hχ.2.1.comp_homeomorph (Homeomorph.subRight z)).mul_right
  -- measure of the ball around z
  have hball : volume (Metric.ball z 2) = Vn := by
    rw [hVn]; exact Measure.addHaar_ball_center volume z 2
  have hiu : ∀ x, |a x| ≤ X := fun x => sa2_apply_le hbd x j
  -- support
  have hχsupp : ∀ y : Euc d, 2 ≤ ‖y‖ → χ y = 0 := by
    intro y hy
    by_contra hne
    have : y ∈ tsupport χ := subset_tsupport _ hne
    have := hχ.2.2.1 this
    simp at this
    linarith
  have hdχsupp : ∀ y : Euc d, 2 ≤ ‖y‖ → fderiv ℝ χ y = 0 := by
    intro y hy
    by_contra hne
    have : y ∈ tsupport χ := support_fderiv_subset ℝ hne
    have := hχ.2.2.1 this
    simp at this
    linarith
  -- the zeroth-order term
  have h0 : ∫⁻ x, ENNReal.ofReal ((u x) ^ 2) ≤ ENNReal.ofReal (X ^ 2) * Vn := by
    calc ∫⁻ x, ENNReal.ofReal ((u x) ^ 2)
        ≤ ∫⁻ x, (Metric.ball z 2).indicator (fun _ => ENNReal.ofReal (X ^ 2)) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ Metric.ball z 2
          · rw [Set.indicator_of_mem hx]
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : |χ (x - z)| ≤ 1 := by
              have := hχ.2.2.2.1 (x - z)
              rw [abs_of_nonneg this.1]; exact this.2
            simp only [hu, mul_pow]
            have : (χ (x - z)) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (χ (x - z)), sq_abs (χ (x - z))]
            have h2 : (a x) ^ 2 ≤ X ^ 2 := by
              have := hiu x
              nlinarith [abs_nonneg (a x), sq_abs (a x)]
            nlinarith [sq_nonneg (a x), sq_nonneg (χ (x - z))]
          · rw [Set.indicator_of_notMem hx]
            have : ‖x - z‖ ≥ 2 := by
              rw [Metric.mem_ball, dist_eq_norm] at hx; exact not_lt.1 hx
            simp [hu, hχsupp _ this]
      _ = ENNReal.ofReal (X ^ 2) * Vn := by
          rw [lintegral_indicator measurableSet_ball, setLIntegral_const, hball]
  -- the first-order terms
  have hder : ∀ x (i : Fin d), fderiv ℝ u x (EuclideanSpace.single i 1) =
      fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) * a x +
        χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro x i
    have h1 : HasFDerivAt (fun x : Euc d => χ (x - z)) (fderiv ℝ χ (x - z)) x := by
      convert (hχ1.differentiable one_ne_zero (x - z)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const z) using 1 <;> first | rfl | simp
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) x := hf1.differentiable one_ne_zero x
    have h2 : HasFDerivAt a ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).comp
        (fderiv ℝ (fderiv ℝ f) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).hasFDerivAt.comp x hfd.hasFDerivAt
    have h3 := h1.mul h2
    have : fderiv ℝ u x = χ (x - z) • (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).comp
        (fderiv ℝ (fderiv ℝ f) x) + a x • fderiv ℝ χ (x - z) := h3.fderiv
    rw [this]
    simp
    ring
  have h1 : ∀ i : Fin d, ∫⁻ x, ENNReal.ofReal ((fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
      ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2) * Vn + ENNReal.ofReal (2 * (C₂ * X) ^ 2) := by
    intro i
    have hpt : ∀ x, ENNReal.ofReal ((fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
        (Metric.ball z 2).indicator (fun _ => ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2)) x +
          ENNReal.ofReal (2 * (χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1)) ^ 2) := by
      intro x
      rw [hder x i]
      set p := fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) * a x with hp
      set q := χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        with hq
      have hsq : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (p - q)]
      have hp2 : 2 * p ^ 2 ≤ (Metric.ball z 2).indicator (fun _ => 2 * Bχ ^ 2 * X ^ 2) x := by
        by_cases hx : x ∈ Metric.ball z 2
        · rw [Set.indicator_of_mem hx]
          have h1 : |fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)| ≤ Bχ := by
            rw [← Real.norm_eq_abs]
            refine ((fderiv ℝ χ (x - z)).le_opNorm _).trans ?_
            simpa using hBχ' (x - z)
          have h2 : p ^ 2 ≤ Bχ ^ 2 * X ^ 2 := by
            rw [hp, mul_pow]
            have := sq_le_sq' (by linarith [abs_nonneg (fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)), neg_abs_le (fderiv ℝ χ (x - z) (EuclideanSpace.single i 1))]) (le_trans (le_abs_self _) h1)
            have h3 : (a x) ^ 2 ≤ X ^ 2 := by
              have := hiu x
              nlinarith [abs_nonneg (a x), sq_abs (a x)]
            exact mul_le_mul this h3 (sq_nonneg _) (sq_nonneg _)
          nlinarith
        · rw [Set.indicator_of_notMem hx]
          have : ‖x - z‖ ≥ 2 := by
            rw [Metric.mem_ball, dist_eq_norm] at hx; exact not_lt.1 hx
          simp [hp, hdχsupp _ this]
      calc ENNReal.ofReal ((p + q) ^ 2) ≤ ENNReal.ofReal ((Metric.ball z 2).indicator (fun _ => 2 * Bχ ^ 2 * X ^ 2) x + 2 * q ^ 2) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal ((Metric.ball z 2).indicator (fun _ => 2 * Bχ ^ 2 * X ^ 2) x) + ENNReal.ofReal (2 * q ^ 2) :=
            ENNReal.ofReal_add_le
        _ = (Metric.ball z 2).indicator (fun _ => ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2)) x + ENNReal.ofReal (2 * q ^ 2) := by
            by_cases hx : x ∈ Metric.ball z 2
            · simp [Set.indicator_of_mem hx]
            · simp [Set.indicator_of_notMem hx]
    calc ∫⁻ x, ENNReal.ofReal ((fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2)
        ≤ ∫⁻ x, ((Metric.ball z 2).indicator (fun _ => ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2)) x +
          ENNReal.ofReal (2 * (χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1)) ^ 2)) := lintegral_mono hpt
      _ = ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2) * Vn + ∫⁻ x, ENNReal.ofReal (2 * (χ (x - z) *
            fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2) := by
          rw [lintegral_add_left (measurable_const.indicator measurableSet_ball), lintegral_indicator measurableSet_ball,
            setLIntegral_const, hball]
      _ ≤ ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2) * Vn + ENNReal.ofReal (2 * (C₂ * X) ^ 2) := by
          gcongr
          calc ∫⁻ x, ENNReal.ofReal (2 * (χ (x - z) * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1)) ^ 2)
              = ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal ((χ (x - z) * fderiv ℝ (fderiv ℝ f) x
                  (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2) := by
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                refine lintegral_congr fun x => ?_
                rw [ENNReal.ofReal_mul (by norm_num)]
            _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal ((C₂ * X) ^ 2) := by
                gcongr
                exact hC₂ f hf X hX hul z i j
            _ = ENNReal.ofReal (2 * (C₂ * X) ^ 2) := by
                rw [← ENNReal.ofReal_mul (by norm_num)]
  -- assemble
  have hsum := HRS.MS.Ul.ul0_sobE_sq_derivs (m := 1) (g := u) (by simpa using hud) huc
  have hA : ∀ i : Fin 0 → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i u x) ^ 2) =
      ∫⁻ x, ENNReal.ofReal ((u x) ^ 2) := by
    intro i
    refine lintegral_congr fun x => ?_
    unfold partialDeriv
    rw [iteratedFDeriv_zero_apply]
  have hB : ∀ i : Fin 1 → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i u x) ^ 2) ≤
      ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2) * Vn + ENNReal.ofReal (2 * (C₂ * X) ^ 2) := by
    intro i
    have : ∀ x, partialDeriv i u x = fderiv ℝ u x (EuclideanSpace.single (i 0) 1) := by
      intro x
      unfold partialDeriv
      rw [iteratedFDeriv_one_apply]
    simp_rw [this]
    exact h1 (i 0)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, one_mul] at hsum
  have hs0 : ∑ i : Fin 0 → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i u x) ^ 2) ≤
      ENNReal.ofReal (X ^ 2) * Vn := by
    rw [Finset.sum_congr rfl (fun i _ => hA i)]
    simpa using h0
  have hs1 : ∑ i : Fin 1 → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i u x) ^ 2) ≤
      (d : ℝ≥0∞) * (ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2) * Vn + ENNReal.ofReal (2 * (C₂ * X) ^ 2)) := by
    refine (Finset.sum_le_card_nsmul _ _ _ (fun i _ => hB i)).trans ?_
    have hcard : (Finset.univ : Finset (Fin 1 → Fin d)).card = d := by simp
    rw [hcard, nsmul_eq_mul]
  have hsq : sobolevNormE (1 : ℝ) u ^ 2 ≤ ENNReal.ofReal ((Real.sqrt K * X) ^ 2) := by
    rw [hsum]
    refine (add_le_add hs0 hs1).trans (le_of_eq ?_)
    have hKX : (Real.sqrt K * X) ^ 2 = K * X ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK0]
    rw [hKX, hK]
    have e1 : ENNReal.ofReal (X ^ 2) * Vn = ENNReal.ofReal (V * X ^ 2) := by
      rw [← hVn', ← ENNReal.ofReal_mul (sq_nonneg X), mul_comm]
    have e2 : ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2) * Vn = ENNReal.ofReal (2 * Bχ ^ 2 * X ^ 2 * V) := by
      rw [← hVn', ← ENNReal.ofReal_mul (by positivity)]
    rw [e1, e2]
    have e3 : (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) := (ENNReal.ofReal_natCast d).symm
    rw [e3, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have := sa2_le_of_sq_le (mul_nonneg (Real.sqrt_nonneg _) hX) hsq
  simpa [mul_assoc] using this


/-! ### The product `h_{fg} = ∇f·∇g` -/

/-- `h_{fg} = ∑_j ∂_jf ∂_jg` -/
def sa2h (f g : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j : Fin d, fderiv ℝ f x (EuclideanSpace.single j 1) * fderiv ℝ g x (EuclideanSpace.single j 1)

theorem sa2h_eq_inner (f g : Euc d → ℝ) (x : Euc d) :
    sa2h f g x = inner ℝ (gradient f x) (gradient g x) := by
  unfold sa2h
  simp only [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HRS.MP.RdMart.mrm_grad_component f x j, HRS.MP.RdMart.mrm_grad_component g x j]
  simp [mul_comm]

theorem sa2_deriv_bounds {f : Euc d → ℝ} (hf : MemCb 2 f) {X : ℝ} (hX : cbNorm 2 f ≤ X) :
    (∀ x, ‖fderiv ℝ f x‖ ≤ X) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ X) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := sa2_norm_iter_le_cbNorm (k := 2) (j := 1) (by norm_num) hf x
    rw [norm_iteratedFDeriv_one] at this
    linarith
  · have := sa2_norm_iter_le_cbNorm (k := 2) (j := 2) le_rfl hf x
    have e : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
      rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
    rw [e]
    linarith

theorem sa2_vj_memCb {g : Euc d → ℝ} (hg : MemCb 2 g) {X : ℝ} (hX : cbNorm 2 g ≤ X) (j : Fin d) :
    MemCb 1 (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) ∧
      cbNorm 1 (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) ≤ 2 * X := by
  obtain ⟨hg1, hg2⟩ := sa2_deriv_bounds hg hX
  have hX0 : 0 ≤ X := (sa2_cbNorm_nonneg 2 g).trans hX
  have hg1' : ContDiff ℝ 1 (fderiv ℝ g) := hg.1.fderiv_right (by norm_num)
  set v : Euc d → ℝ := fun x => fderiv ℝ g x (EuclideanSpace.single j 1) with hv
  have hvd : ContDiff ℝ 1 v :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).contDiff.comp hg1'
  have hb0 : ∀ x, ‖iteratedFDeriv ℝ 0 v x‖ ≤ X := fun x => by
    rw [norm_iteratedFDeriv_zero]
    simpa [hv] using sa2_apply_le hg1 x j
  have hb1 : ∀ x, ‖iteratedFDeriv ℝ 1 v x‖ ≤ X := fun x => by
    rw [norm_iteratedFDeriv_one]
    have hfd : DifferentiableAt ℝ (fderiv ℝ g) x := hg1'.differentiable one_ne_zero x
    have h2 : HasFDerivAt v ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).comp
        (fderiv ℝ (fderiv ℝ g) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).hasFDerivAt.comp x
        hfd.hasFDerivAt
    rw [h2.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hX0 fun w => ?_
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
    calc ‖(fderiv ℝ (fderiv ℝ g) x w) (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ (fderiv ℝ g) x w‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖w‖) * 1 := by
          simp only [EuclideanSpace.norm_single, norm_one]
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ X * ‖w‖ := by
          have := hg2 x
          nlinarith [norm_nonneg w]
  refine ⟨⟨hvd, fun k hk => ?_⟩, ?_⟩
  · refine ⟨X, ?_⟩
    rintro _ ⟨x, rfl⟩
    interval_cases k
    · exact hb0 x
    · exact hb1 x
  · unfold cbNorm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 : (⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 v x‖) ≤ X := Real.iSup_le hb0 hX0
    have h1 : (⨆ x : Euc d, ‖iteratedFDeriv ℝ 1 v x‖) ≤ X := Real.iSup_le hb1 hX0
    linarith

theorem sa2_hSob {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Euc d → ℝ), MemCb 2 f → MemCb 2 g → ∀ Xf Xg : ℝ, 0 ≤ Xf → 0 ≤ Xg →
      cbNorm 2 f ≤ Xf → cbNorm 2 g ≤ Xg → ulocNormE 2 χ f ≤ ENNReal.ofReal Xf → ∀ z : Euc d,
        sobolevNormE ((1 : ℕ) : ℝ) (fun x => χ (x - z) * sa2h f g x) ≤ ENNReal.ofReal (C * Xf * Xg) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := sa2_loc1 hχ
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d 1
  refine ⟨d * (2 * Cm * C₁), by positivity, fun f g hf hg Xf Xg hXf hXg hcf hcg hul z => ?_⟩
  obtain ⟨hf1, -⟩ := sa2_deriv_bounds hf hcf
  have hf2 : ContDiff ℝ 2 f := hf.1
  have hfun : (fun x => χ (x - z) * sa2h f g x) = fun x => ∑ j : Fin d,
      fderiv ℝ g x (EuclideanSpace.single j 1) *
        (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1)) := by
    funext x
    unfold sa2h
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun]
  have hterm : ∀ j : Fin d, sobolevNormE ((1 : ℕ) : ℝ) (fun x => fderiv ℝ g x (EuclideanSpace.single j 1) *
      (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1))) ≤
      ENNReal.ofReal (Cm * (2 * Xg)) * ENNReal.ofReal (C₁ * Xf) := by
    intro j
    obtain ⟨hvm, hvc⟩ := sa2_vj_memCb hg hcg j
    refine (hCm _ hvm _).trans ?_
    gcongr
    exact hC₁ f hf2 Xf hXf hf1 hul z j
  calc sobolevNormE ((1 : ℕ) : ℝ) (fun x => ∑ j : Fin d, fderiv ℝ g x (EuclideanSpace.single j 1) *
        (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1)))
      ≤ ∑ j : Fin d, sobolevNormE ((1 : ℕ) : ℝ) (fun x => fderiv ℝ g x (EuclideanSpace.single j 1) *
        (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1))) :=
        HRS.MS.UlocCut.uc_sum_le _ _ _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (Cm * (2 * Xg)) * ENNReal.ofReal (C₁ * Xf) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = ENNReal.ofReal (d * (2 * Cm * C₁) * Xf * Xg) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast d,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring


theorem sa2_sobE_unpack {w : Euc d → ℝ} {m : ℝ} {U : ℝ} (hU : 0 ≤ U)
    (h : sobolevNormE m w ≤ ENNReal.ofReal U) :
    HRS.PDE.ToolboxRd.MemSobolev m w ∧ HRS.PDE.ToolboxRd.sobolevNormSq m w ≤ U ^ 2 := by
  unfold sobolevNormE at h
  by_cases hM : HRS.PDE.ToolboxRd.MemSobolev m w
  · rw [if_pos hM] at h
    refine ⟨hM, ?_⟩
    have h3 := (ENNReal.ofReal_le_ofReal_iff hU).1 h
    exact (Real.sqrt_le_iff.mp h3).2
  · rw [if_neg hM] at h
    exact absurd h (by simp)

theorem sa2h_bound {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g) {Xf Xg : ℝ}
    (hcf : cbNorm 2 f ≤ Xf) (hcg : cbNorm 2 g ≤ Xg) (x : Euc d) :
    |sa2h f g x| ≤ d * Xf * Xg := by
  obtain ⟨hf1, -⟩ := sa2_deriv_bounds hf hcf
  obtain ⟨hg1, -⟩ := sa2_deriv_bounds hg hcg
  unfold sa2h
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin d, |fderiv ℝ f x (EuclideanSpace.single j 1) * fderiv ℝ g x (EuclideanSpace.single j 1)|
      ≤ ∑ _j : Fin d, Xf * Xg := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (sa2_apply_le hf1 x j) (sa2_apply_le hg1 x j) (abs_nonneg _)
          ((abs_nonneg _).trans (sa2_apply_le hf1 x j))
    _ = d * Xf * Xg := by simp; ring

theorem sa2_coord_lip {f : Euc d → ℝ} (hf : MemCb 2 f) {Xf : ℝ} (hcf : cbNorm 2 f ≤ Xf) (x y : Euc d)
    (j : Fin d) :
    |fderiv ℝ f x (EuclideanSpace.single j 1) - fderiv ℝ f y (EuclideanSpace.single j 1)| ≤
      Xf * ‖x - y‖ := by
  have h1 : (gradient f x - gradient f y) j =
      fderiv ℝ f x (EuclideanSpace.single j 1) - fderiv ℝ f y (EuclideanSpace.single j 1) := by
    simp [HRS.MP.RdMart.mrm_grad_component]
  rw [← h1, ← Real.norm_eq_abs]
  refine (PiLp.norm_apply_le _ j).trans ?_
  exact (HRS.MS.Go.s55_grad_lip_cb hf x y).trans (mul_le_mul_of_nonneg_right hcf (norm_nonneg _))

theorem sa2h_lip {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g) {Xf Xg : ℝ}
    (hcf : cbNorm 2 f ≤ Xf) (hcg : cbNorm 2 g ≤ Xg) (x y : Euc d) :
    |sa2h f g x - sa2h f g y| ≤ (2 * d * Xf * Xg) * ‖x - y‖ := by
  obtain ⟨hf1, -⟩ := sa2_deriv_bounds hf hcf
  obtain ⟨hg1, -⟩ := sa2_deriv_bounds hg hcg
  have hXf : 0 ≤ Xf := (sa2_cbNorm_nonneg 2 f).trans hcf
  have hXg : 0 ≤ Xg := (sa2_cbNorm_nonneg 2 g).trans hcg
  unfold sa2h
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin d, |fderiv ℝ f x (EuclideanSpace.single j 1) * fderiv ℝ g x (EuclideanSpace.single j 1) -
        fderiv ℝ f y (EuclideanSpace.single j 1) * fderiv ℝ g y (EuclideanSpace.single j 1)|
      ≤ ∑ _j : Fin d, (2 * Xf * Xg) * ‖x - y‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        set a := fderiv ℝ f x (EuclideanSpace.single j 1)
        set a' := fderiv ℝ f y (EuclideanSpace.single j 1)
        set b := fderiv ℝ g x (EuclideanSpace.single j 1)
        set b' := fderiv ℝ g y (EuclideanSpace.single j 1)
        have e : a * b - a' * b' = a * (b - b') + b' * (a - a') := by ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 : |a| * |b - b'| ≤ Xf * (Xg * ‖x - y‖) :=
          mul_le_mul (sa2_apply_le hf1 x j) (sa2_coord_lip hg hcg x y j) (abs_nonneg _) hXf
        have h2 : |b'| * |a - a'| ≤ Xg * (Xf * ‖x - y‖) :=
          mul_le_mul (sa2_apply_le hg1 y j) (sa2_coord_lip hf hcf x y j) (abs_nonneg _) hXg
        nlinarith
    _ = (2 * d * Xf * Xg) * ‖x - y‖ := by simp; ring

/-- The test inequality of `B:lem:test-cutoff` for `h_{fg}`, at the Sobolev index `1`. -/
theorem sa2_test_h (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) - 2 ≤ s)
    {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (C₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ C₀ : ℝ, WholeCoercivityPair d s C₀ C₁ →
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      Integrable (fun x => ‖x‖ ^ 2 * ρ x) → ∀ X : EucConfig d N, Function.Injective X →
      ∀ (f g : Euc d → ℝ), MemCb 2 f → MemCb 2 g → ∀ Xf Xg : ℝ, 0 ≤ Xf → 0 ≤ Xg →
        cbNorm 2 f ≤ Xf → cbNorm 2 g ≤ Xg → ulocNormE 2 χ f ≤ ENNReal.ofReal Xf → ∀ R : ℝ, 1 ≤ R →
        |HRS.Whole.pair (HRS.Whole.empirical X) (sa2h f g) -
            HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (sa2h f g)| ≤
          C * Xf * Xg * (R ^ ((d : ℝ) / 2) * (smearScale d N Λ +
              Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N)) +
            (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / R ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := Q09A.sobolev_plat_bound hd (m := 1) le_rfl χ hχ.2.2.2.2
  obtain ⟨Lp, hLp0, hLp⟩ := Q09A.plat_lipschitz d
  obtain ⟨Ch, hCh0, hCh⟩ := sa2_hSob hχ
  set cpc : ℝ := |C₁| * (Lp + 1) + |C₁| * (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d)) + 1 with hcpc
  have hcpc0 : 0 ≤ cpc := by positivity
  refine ⟨cpc * (d + 2 * d + Ch), by positivity, fun C₀ hpair Λ hΛ N hN ρ hρ hρΛ hmom X hX f g hf hg Xf Xg
    hXf hXg hcf hcg hul R hR => ?_⟩
  have hmm : ((d : ℝ) - s) / 2 ≤ ((1 : ℕ) : ℝ) := by push_cast; linarith
  have hsob : ∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev ((1 : ℕ) : ℝ) (fun x => χ (x - z) * sa2h f g x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq ((1 : ℕ) : ℝ) (fun x => χ (x - z) * sa2h f g x) ≤
        (Ch * Xf * Xg) ^ 2 := fun z =>
    sa2_sobE_unpack (by positivity) (hCh f g hf hg Xf Xg hXf hXg hcf hcg hul z)
  have key := sa2_pathwise_core hd s hs0 hsd 1 hmm χ K Lp hK0 hLp0 hK hLp C₁ C₀ hpair Λ hΛ N hN ρ hρ hρΛ
    hmom X hX (sa2h f g) (d * Xf * Xg) (2 * d * Xf * Xg) (Ch * Xf * Xg) (by positivity) (by positivity)
    (by positivity) (fun x => sa2h_bound hf hg hcf hcg x) (fun x y => sa2h_lip hf hg hcf hcg x y) hsob R hR
  refine key.trans (le_of_eq ?_)
  ring

end HRS.MS.MainRdStat
