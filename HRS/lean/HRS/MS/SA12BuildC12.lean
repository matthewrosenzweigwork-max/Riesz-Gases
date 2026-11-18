import HRS.MH.AdjointRdDefs
import HRS.MS.UniqC3c

/-!
# S.A.12 C12: finite covering and weighted overlap of the flowed unit cells by advected cutoff balls

In preimage coordinates every unit cube `z' + [0,1]^d` is covered by a fixed finite set of fine-lattice unit
balls on which the cutoff equals one; continuity of the flow map and its inverse makes the flowed cells and
the transported cutoffs measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12c12_cellPt_add (z' k0 : Fin d → ℤ) (hd : 1 ≤ d) :
    cellPt d (fun i => ⌈Real.sqrt d⌉ * z' i + k0 i) = latticePt z' + cellPt d k0 := by
  have hκ : (⌈Real.sqrt d⌉ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ Real.sqrt d := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    have h2 : (1 : ℝ) ≤ (⌈Real.sqrt d⌉ : ℝ) := this.trans (Int.le_ceil _)
    linarith
  ext i
  simp only [cellPt, latticePt, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  push_cast
  field_simp

theorem sa12c12_kappa_ge (hd : 1 ≤ d) : (1 : ℝ) ≤ (⌈Real.sqrt d⌉ : ℝ) := by
  have : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  exact this.trans (Int.le_ceil _)

theorem sa12c12_finite_cells (hd : 1 ≤ d) (B : ℝ) :
    {k : Fin d → ℤ | ‖cellPt d k‖ ≤ B}.Finite := by
  set κ : ℝ := (⌈Real.sqrt d⌉ : ℝ) with hκ
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos (sa12c12_kappa_ge hd)
  have hsub : {k : Fin d → ℤ | ‖cellPt d k‖ ≤ B} ⊆
      Set.pi Set.univ (fun _ : Fin d => Set.Icc (-⌈κ * B⌉) ⌈κ * B⌉) := by
    intro k hk i _
    have h1 : |(cellPt d k) i| ≤ B := by
      have := (PiLp.norm_apply_le (cellPt d k) i).trans hk
      simpa [Real.norm_eq_abs] using this
    have h2 : (cellPt d k) i = κ⁻¹ * (k i : ℝ) := by simp [cellPt, latticePt, hκ]
    rw [h2, abs_mul, abs_inv, abs_of_pos hκpos, inv_mul_le_iff₀ hκpos] at h1
    have h3 : |(k i : ℝ)| ≤ (⌈κ * B⌉ : ℝ) := h1.trans (Int.le_ceil _)
    rw [abs_le] at h3
    constructor
    · have : (-(⌈κ * B⌉ : ℤ) : ℝ) ≤ k i := by push_cast; linarith [h3.1]
      exact_mod_cast this
    · exact_mod_cast h3.2
  exact (Set.Finite.pi (fun _ => Set.finite_Icc _ _)).subset hsub

/-- A fixed finite set of offsets such that the balls `B(z' + cellPt k0, 1)` cover each unit cube. -/
theorem sa12c12_cover (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ K0 : Finset (Fin d → ℤ), ∀ (z' : Fin d → ℤ) (y : Euc d),
      (∀ i, 0 ≤ (y - latticePt z') i ∧ (y - latticePt z') i ≤ 1) →
      ∃ k0 ∈ K0, χ (y - cellPt d (fun i => ⌈Real.sqrt d⌉ * z' i + k0 i)) = 1 := by
  have hfin := sa12c12_finite_cells hd (Real.sqrt d + 1 / 2)
  refine ⟨hfin.toFinset, fun z' y hy => ?_⟩
  obtain ⟨k0, hk0⟩ := HRS.MS.UniqC3.exists_cellPt_near hd (y - latticePt z')
  refine ⟨k0, ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    show ‖cellPt d k0‖ ≤ Real.sqrt d + 1 / 2
    have h1 : ‖y - latticePt z'‖ ≤ Real.sqrt d := by
      rw [EuclideanSpace.norm_eq]
      refine Real.sqrt_le_sqrt ?_
      calc ∑ i, ‖(y - latticePt z') i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Real.norm_eq_abs, abs_of_nonneg (hy i).1]
            nlinarith [(hy i).1, (hy i).2]
        _ = d := by simp
    calc ‖cellPt d k0‖ = ‖(y - latticePt z') - ((y - latticePt z') - cellPt d k0)‖ := by
          congr 1; abel
      _ ≤ ‖y - latticePt z'‖ + ‖(y - latticePt z') - cellPt d k0‖ := norm_sub_le _ _
      _ ≤ Real.sqrt d + 1 / 2 := add_le_add h1 hk0
  · rw [sa12c12_cellPt_add z' k0 hd]
    apply hχ.2.2.2.2
    rw [Metric.mem_closedBall, dist_zero_right]
    have : y - (latticePt z' + cellPt d k0) = (y - latticePt z') - cellPt d k0 := by abel
    rw [this]
    linarith


/-- Peetre's inequality for the Japanese bracket. -/
theorem sa12c12_peetre (p : ℝ) (hp : 0 ≤ p) (a b : Euc d) :
    jbracket a ^ (-p) ≤ Real.sqrt 2 ^ p * jbracket b ^ p * jbracket (a + b) ^ (-p) := by
  have ha : 0 < jbracket a := by unfold jbracket; positivity
  have hb : 0 < jbracket b := by unfold jbracket; positivity
  have hab : 0 < jbracket (a + b) := by unfold jbracket; positivity
  have h1 : jbracket (a + b) ≤ Real.sqrt 2 * (jbracket a * jbracket b) := by
    unfold jbracket
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [norm_add_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a + b),
      sq_nonneg (‖a‖ - ‖b‖), mul_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖b‖)]
  have h2 : jbracket (a + b) ^ p ≤ Real.sqrt 2 ^ p * jbracket b ^ p * jbracket a ^ p := by
    calc jbracket (a + b) ^ p ≤ (Real.sqrt 2 * (jbracket a * jbracket b)) ^ p :=
          Real.rpow_le_rpow hab.le h1 hp
      _ = Real.sqrt 2 ^ p * jbracket b ^ p * jbracket a ^ p := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hb.le]; ring
  have hA : 0 < jbracket a ^ p := Real.rpow_pos_of_pos ha p
  have hAB : 0 < jbracket (a + b) ^ p := Real.rpow_pos_of_pos hab p
  rw [Real.rpow_neg ha.le, Real.rpow_neg hab.le]
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hAB]
  linarith


-- BEGIN SA12.C12
theorem fine_cell_cover (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ N C : ℝ, 0 ≤ N ∧ 0 ≤ C ∧ ∀ (Ψ : ℝ → Euc d → Euc d) (τ : ℝ), Function.Bijective (Ψ τ) →
      Continuous (Ψ τ) → Continuous (Function.invFun (Ψ τ)) →
      ∀ w : Euc d → ℝ, Measurable w →
        (∀ z' : Fin d → ℤ, ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2) ≤
          ENNReal.ofReal N * ⨆ z : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal ((advCutoff χ Ψ τ (cellPt d z) x * w x) ^ 2)) ∧
        ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') * ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2) ≤
          ENNReal.ofReal C * ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ∫⁻ x, ENNReal.ofReal ((advCutoff χ Ψ τ (cellPt d z) x * w x) ^ 2) := by
  obtain ⟨K0, hK0⟩ := sa12c12_cover hd χ hχ
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  refine ⟨K0.card, ∑ k0 ∈ K0, Real.sqrt 2 ^ p * jbracket (cellPt d k0) ^ p, Nat.cast_nonneg _,
    Finset.sum_nonneg fun k0 _ => by unfold jbracket; positivity, fun Ψ τ hbij hc hci w hw => ?_⟩
  set sh : (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) := fun z' k0 i => ⌈Real.sqrt d⌉ * z' i + k0 i with hsh
  set g : (Fin d → ℤ) → Euc d → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal ((advCutoff χ Ψ τ (cellPt d k) x * w x) ^ 2) with hg
  set I : (Fin d → ℤ) → ℝ≥0∞ := fun k => ∫⁻ x, g k x with hI
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    have : Measurable fun x => advCutoff χ Ψ τ (cellPt d k) x := by
      unfold advCutoff
      exact hχ.1.continuous.measurable.comp ((hci.sub continuous_const).measurable)
    exact ENNReal.measurable_ofReal.comp ((this.mul hw).pow_const 2)
  -- pointwise covering
  have hpt : ∀ (z' : Fin d → ℤ) (x : Euc d), x ∈ flowCell Ψ τ z' →
      ENNReal.ofReal (w x ^ 2) ≤ ∑ k0 ∈ K0, g (sh z' k0) x := by
    intro z' x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k0, hk0, hχ1⟩ := hK0 z' y hy
    have hinv : Function.invFun (Ψ τ) (Ψ τ y) = y := Function.leftInverse_invFun hbij.1 y
    have hcut : advCutoff χ Ψ τ (cellPt d (sh z' k0)) (Ψ τ y) = 1 := by
      unfold advCutoff
      rw [hinv]
      exact hχ1
    calc ENNReal.ofReal (w (Ψ τ y) ^ 2) = g (sh z' k0) (Ψ τ y) := by
          simp only [hg, hcut, one_mul]
      _ ≤ ∑ k0 ∈ K0, g (sh z' k0) (Ψ τ y) :=
          Finset.single_le_sum (f := fun k0 => g (sh z' k0) (Ψ τ y)) (fun _ _ => bot_le) hk0
  have hcell : ∀ z' : Fin d → ℤ, ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2) ≤
      ∑ k0 ∈ K0, I (sh z' k0) := by
    intro z'
    have hpt' : ∀ x ∈ flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2) ≤ ∑ k0 ∈ K0, g (sh z' k0) x :=
      fun x hx => hpt z' x hx
    calc ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2)
        ≤ ∫⁻ x in flowCell Ψ τ z', ∑ k0 ∈ K0, g (sh z' k0) x := by
          exact setLIntegral_mono (Finset.measurable_sum _ fun k0 _ => hgm _) hpt'
      _ ≤ ∫⁻ x, ∑ k0 ∈ K0, g (sh z' k0) x := setLIntegral_le_lintegral _ _
      _ = ∑ k0 ∈ K0, I (sh z' k0) := lintegral_finsetSum _ fun k0 _ => hgm _
  have hsup : ∀ k, I k ≤ ⨆ z, I z := fun k => le_iSup I k
  refine ⟨fun z' => ?_, ?_⟩
  · calc ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2) ≤ ∑ k0 ∈ K0, I (sh z' k0) := hcell z'
      _ ≤ ∑ k0 ∈ K0, ⨆ z, I z := Finset.sum_le_sum fun k0 _ => hsup _
      _ = ENNReal.ofReal (K0.card : ℝ) * ⨆ z, I z := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_natCast]
  · have hκ0 : (⌈Real.sqrt d⌉ : ℤ) ≠ 0 := by
      have := sa12c12_kappa_ge hd
      intro h0
      rw [h0] at this
      simp at this
      linarith
    have hinj : ∀ k0, Function.Injective (fun z' => sh z' k0) := by
      intro k0 z1 z2 h12
      funext i
      have := congr_fun h12 i
      simp only [hsh] at this
      have h3 : (⌈Real.sqrt d⌉ : ℤ) * z1 i = ⌈Real.sqrt d⌉ * z2 i := by linarith
      exact mul_left_cancel₀ hκ0 h3
    set h : (Fin d → ℤ) → ℝ≥0∞ := fun k => ENNReal.ofReal (jbracket (cellPt d k) ^ (-p)) * I k with hh
    set P : (Fin d → ℤ) → ℝ := fun k0 => Real.sqrt 2 ^ p * jbracket (cellPt d k0) ^ p with hP
    have hP0 : ∀ k0, 0 ≤ P k0 := fun k0 => by simp only [hP]; unfold jbracket; positivity
    have hlocal : ∀ (z' : Fin d → ℤ) (k0 : Fin d → ℤ),
        ENNReal.ofReal (cellWeight d z') * I (sh z' k0) ≤ ENNReal.ofReal (P k0) * h (sh z' k0) := by
      intro z' k0
      have hpe := sa12c12_peetre p hp0 (latticePt z') (cellPt d k0)
      rw [← sa12c12_cellPt_add z' k0 hd] at hpe
      have hcw : cellWeight d z' = jbracket (latticePt z') ^ (-p) := rfl
      calc ENNReal.ofReal (cellWeight d z') * I (sh z' k0)
          ≤ ENNReal.ofReal (P k0 * jbracket (cellPt d (sh z' k0)) ^ (-p)) * I (sh z' k0) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            rw [hcw]
            simpa [hP, hsh, mul_assoc] using hpe
        _ = ENNReal.ofReal (P k0) * h (sh z' k0) := by
            rw [ENNReal.ofReal_mul (hP0 k0), hh]; ring
    calc ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') * ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2)
        ≤ ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') * ∑ k0 ∈ K0, I (sh z' k0) :=
          ENNReal.tsum_le_tsum fun z' => mul_le_mul' le_rfl (hcell z')
      _ ≤ ∑' z' : Fin d → ℤ, ∑ k0 ∈ K0, ENNReal.ofReal (P k0) * h (sh z' k0) :=
          ENNReal.tsum_le_tsum fun z' => by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun k0 _ => hlocal z' k0
      _ = ∑ k0 ∈ K0, ∑' z' : Fin d → ℤ, ENNReal.ofReal (P k0) * h (sh z' k0) :=
          Summable.tsum_finsetSum fun k0 _ => ENNReal.summable
      _ = ∑ k0 ∈ K0, ENNReal.ofReal (P k0) * ∑' z' : Fin d → ℤ, h (sh z' k0) := by
          refine Finset.sum_congr rfl fun k0 _ => ?_
          rw [ENNReal.tsum_mul_left]
      _ ≤ ∑ k0 ∈ K0, ENNReal.ofReal (P k0) * ∑' k : Fin d → ℤ, h k :=
          Finset.sum_le_sum fun k0 _ =>
            mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective (hinj k0) h)
      _ = ENNReal.ofReal (∑ k0 ∈ K0, P k0) * ∑' k : Fin d → ℤ, h k := by
          rw [ENNReal.ofReal_sum_of_nonneg fun k0 _ => hP0 k0, Finset.sum_mul]
-- END SA12.C12

end HRS.MH.AdjointRd.Phase2SA12Construction
