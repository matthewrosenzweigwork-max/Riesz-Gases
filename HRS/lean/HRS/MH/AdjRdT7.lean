import HRS.MH.AdjointRdDefs
import HRS.MH.AdjointRdSpec
import HRS.MH.ScreenedFar
import HRS.MH.ScreenedF1
import HRS.MH.ScreenedF2
import HRS.MH.ScreenedA3a
import HRS.MS.SA12BuildC19

/-!
# Packet T7 `screened_far_periodic` of `HRS/MH/AdjointRdSpec.lean` (Proposition S.A.12 on `R^d`)

Route: for `L ≥ L₁ = 16 e^{CF |T|}` the periodic kernel is evaluated at a representative `u'` of `x - y` with
`|u'| ≥ 4 e^{-CF|T|}` (no wrapping, or wrapping and `|u'| ≥ L/4`), so `kernel_cube_bound` (T4) gives a uniform
pointwise bound; the periodic density is dominated by `Λ ⟨y - L k(y)⟩^{-(d+3)}`; the integral over the box
centred at `Ψ_τ(c)` is at most `2^d` times the integral over the central cube (translation invariance of the
periodic integrand); then the cell Cauchy-Schwarz of `far_core_proof` (`far_I_sq`) applied to the shifted flow
`Ψ'_τ = Ψ_τ(· + e)`, with `Kc z z' = ω_{z'}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.AdjointRdP

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.Screened HRS.MH.AdjointRd

variable {d : ℕ}

/-- Invariance of the iterated derivative of a periodic function under lattice translations. -/
lemma t7_iter_shift {f : Euc d → ℝ} (L : ℝ) (hf : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x)
    (j : ℕ) (x : Euc d) (k : Fin d → ℤ) :
    iteratedFDeriv ℝ j f (x + L • latticePt k) = iteratedFDeriv ℝ j f x := by
  have h1 : (fun z => f (z + L • latticePt k)) = f := funext fun z => hf z k
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) j (L • latticePt k) x
  rw [h1] at h
  exact h.symm

/-- The lattice index of the period cell `[-L/2, L/2)^d` containing `y`. -/
def t7kfl (L : ℝ) (y : Euc d) : Fin d → ℤ := fun i => ⌊y i / L + 1 / 2⌋

/-- The representative of `y` in the central period cell. -/
def t7wper (L : ℝ) (y : Euc d) : Euc d := y - L • latticePt (t7kfl L y)

lemma t7_wper_apply (L : ℝ) (y : Euc d) (i : Fin d) :
    t7wper L y i = y i - L * (⌊y i / L + 1 / 2⌋ : ℤ) := by
  simp [t7wper, t7kfl, latticePt]

lemma t7_wper_mem {L : ℝ} (hL : 0 < L) (y : Euc d) (i : Fin d) :
    -(L / 2) ≤ t7wper L y i ∧ t7wper L y i < L / 2 := by
  rw [t7_wper_apply]
  have h1 := Int.floor_le (y i / L + 1 / 2)
  have h2 := Int.lt_floor_add_one (y i / L + 1 / 2)
  set f : ℝ := ((⌊y i / L + 1 / 2⌋ : ℤ) : ℝ)
  have e : y i = L * (y i / L) := by field_simp
  constructor <;> nlinarith

lemma t7_wper_shift {L : ℝ} (hL : 0 < L) (y : Euc d) (k : Fin d → ℤ) :
    t7wper L (y + L • latticePt k) = t7wper L y := by
  ext i
  rw [t7_wper_apply, t7_wper_apply]
  have : (y + L • latticePt k) i / L + 1 / 2 = (y i / L + 1 / 2) + (k i : ℝ) := by
    simp [latticePt]; field_simp; ring
  rw [this, Int.floor_add_intCast]
  push_cast
  simp [latticePt]
  ring

lemma t7_wper_of_mem {L : ℝ} (hL : 0 < L) (y : Euc d) (hy : ∀ i, -(L / 2) ≤ y i ∧ y i < L / 2) :
    t7wper L y = y := by
  ext i
  rw [t7_wper_apply]
  have : ⌊y i / L + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor
    · have := (hy i).1
      have e : y i = L * (y i / L) := by field_simp
      nlinarith
    · have := (hy i).2
      have e : y i = L * (y i / L) := by field_simp
      nlinarith
  rw [this]; simp

lemma t7_decomp {L : ℝ} (y : Euc d) : y = t7wper L y + L • latticePt (t7kfl L y) := by
  simp [t7wper]

lemma t7_coord_le {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : -(L / 2) ≤ a ∧ a < L / 2) (k : ℤ) :
    |a| ≤ |a - L * (k : ℝ)| := by
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    have h3 : L ≤ |L * (k : ℝ)| := by
      rw [abs_mul, abs_of_pos hL]; nlinarith
    have h4 : |a| ≤ L / 2 := by
      rw [abs_le]; exact ⟨ha.1, ha.2.le⟩
    have h5 : |L * (k : ℝ)| - |a| ≤ |a - L * (k : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (L * (k : ℝ)) a
      rwa [abs_sub_comm] at this
    linarith

/-- Weighted bound for the derivatives of the periodic density at the central representative. -/
lemma t7_mu_bound {L : ℝ} (hL : 0 < L) {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hdec : ∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ)
    (j : ℕ) (hj : j ≤ m + 3) (idx : Fin j → Fin d) (y : Euc d) :
    |partialDeriv idx μ y| ≤ Λ * jbracket (t7wper L y) ^ (-((d : ℝ) + 3)) := by
  set w := t7wper L y with hw
  have hwm := t7_wper_mem hL y
  have hyw : iteratedFDeriv ℝ j μ y = iteratedFDeriv ℝ j μ w := by
    conv_lhs => rw [t7_decomp (L := L) y]
    exact t7_iter_shift L hper j w _
  have hpd : |partialDeriv idx μ y| ≤ ‖iteratedFDeriv ℝ j μ w‖ := by
    unfold partialDeriv
    rw [hyw]
    refine (Real.norm_eq_abs _ ▸ ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have : ∏ l : Fin j, ‖(EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)‖ = 1 := by
      simp
    rw [this, mul_one]
  obtain ⟨k, hk⟩ := hdec j hj w
  have hnorm : ‖w‖ ≤ ‖w - L • latticePt k‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    exact sq_le_sq.mpr (t7_coord_le hL (hwm i) (k i))
  have hjb : jbracket w ≤ jbracket (w - L • latticePt k) := by
    unfold jbracket
    exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg w])
  have hjbp : 0 < jbracket w := by unfold jbracket; positivity
  have hjbp' : 0 < jbracket (w - L • latticePt k) := by unfold jbracket; positivity
  have hpow : jbracket w ^ ((d : ℝ) + 3) ≤ jbracket (w - L • latticePt k) ^ ((d : ℝ) + 3) :=
    Real.rpow_le_rpow hjbp.le hjb (by positivity)
  have hA : 0 < jbracket w ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos hjbp _
  have h1 : jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ w‖ ≤ Λ :=
    le_trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hk
  have h2 : jbracket w ^ (-((d : ℝ) + 3)) * jbracket w ^ ((d : ℝ) + 3) = 1 := by
    rw [← Real.rpow_add hjbp]; simp
  have hB : 0 < jbracket w ^ (-((d : ℝ) + 3)) := Real.rpow_pos_of_pos hjbp _
  calc |partialDeriv idx μ y| ≤ ‖iteratedFDeriv ℝ j μ w‖ := hpd
    _ = jbracket w ^ (-((d : ℝ) + 3)) * (jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ w‖) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ jbracket w ^ (-((d : ℝ) + 3)) * Λ := mul_le_mul_of_nonneg_left h1 hB.le
    _ = Λ * jbracket w ^ (-((d : ℝ) + 3)) := mul_comm _ _

lemma t7_translate_lintegral (a : Euc d) (B : Set (Euc d)) (G : Euc d → ℝ≥0∞)
    (hG : ∀ y, G (y + a) = G y) :
    ∫⁻ y in {y | y - a ∈ B}, G y = ∫⁻ y in B, G y := by
  have h := (measurePreserving_add_right (volume : Measure (Euc d)) a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight a) G {y | y - a ∈ B}
  have hpre : (fun x => x + a) ⁻¹' {y | y - a ∈ B} = B := by ext x; simp
  rw [hpre] at h
  simp_rw [hG] at h
  exact h.symm

lemma t7_box_lintegral {L : ℝ} (hL : 0 < L) (p : Euc d) (G : Euc d → ℝ≥0∞)
    (hG : ∀ (y : Euc d) (k : Fin d → ℤ), G (y + L • latticePt k) = G y) :
    ∫⁻ y in {y | y - p ∈ centeredBox d L}, G y ≤ (2 : ℝ≥0∞) ^ d * ∫⁻ y in centeredBox d L, G y := by
  set k0 : Fin d → ℤ := fun i => ⌊p i / L⌋ with hk0
  set kι : (Fin d → Bool) → (Fin d → ℤ) := fun κ i => k0 i + (if κ i then 1 else 0) with hkι
  set A : (Fin d → Bool) → Set (Euc d) := fun κ => {y | y - L • latticePt (kι κ) ∈ centeredBox d L}
    with hA
  have hcover : {y | y - p ∈ centeredBox d L} ⊆ ⋃ κ, A κ := by
    intro y hy
    simp only [mem_setOf_eq, centeredBox] at hy
    have hmem : ∀ i, k0 i ≤ t7kfl L y i ∧ t7kfl L y i ≤ k0 i + 1 := by
      intro i
      have h1 : -(L / 2) ≤ y i - p i := by simpa using (hy i).1
      have h2 : y i - p i < L / 2 := by simpa using (hy i).2
      have e : y i / L + 1 / 2 = p i / L + ((y i - p i) + L / 2) / L := by field_simp; ring
      have h3 : 0 ≤ ((y i - p i) + L / 2) / L := div_nonneg (by linarith) hL.le
      have h4 : ((y i - p i) + L / 2) / L < 1 := (div_lt_one hL).2 (by linarith)
      constructor
      · exact Int.floor_mono (by rw [e]; linarith)
      · have : ⌊y i / L + 1 / 2⌋ ≤ ⌊p i / L + 1⌋ := Int.floor_mono (by rw [e]; linarith)
        rw [Int.floor_add_one] at this
        exact this
    refine mem_iUnion.2 ⟨fun i => decide (t7kfl L y i = k0 i + 1), ?_⟩
    have hk : kι (fun i => decide (t7kfl L y i = k0 i + 1)) = t7kfl L y := by
      funext i
      simp only [hkι]
      by_cases hc : t7kfl L y i = k0 i + 1
      · simp [hc]
      · have := hmem i
        have : t7kfl L y i = k0 i := by omega
        simp [hc, this]
    simp only [hA, mem_setOf_eq, centeredBox, hk]
    intro i
    have := t7_wper_mem hL y i
    simpa [t7wper] using this
  calc ∫⁻ y in {y | y - p ∈ centeredBox d L}, G y
      ≤ ∫⁻ y in ⋃ κ, A κ, G y := lintegral_mono_set hcover
    _ ≤ ∑' κ, ∫⁻ y in A κ, G y := lintegral_iUnion_le _ _
    _ = ∑' κ : Fin d → Bool, ∫⁻ y in centeredBox d L, G y := by
        refine tsum_congr fun κ => ?_
        exact t7_translate_lintegral (L • latticePt (kι κ)) _ G (fun y => hG y _)
    _ = (2 : ℝ≥0∞) ^ d * ∫⁻ y in centeredBox d L, G y := by
        rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
        simp

lemma t7_kernel_ptwise {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) {C4 : ℝ} (hC4 : 0 ≤ C4)
    {L Lf : ℝ} (hLf : 1 ≤ Lf) (hL : 16 * Lf ≤ L) {γ : Euc d → ℝ}
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x)
    (hT4 : ∀ u : Euc d, u ≠ 0 → (∀ i, |u i| ≤ L / 2) →
      ‖iteratedFDeriv ℝ n γ u‖ ≤ C4 * (‖u‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) +
        (if s = 0 then L ^ (-(n : ℝ)) else 0)))
    {x y p : Euc d} (hx : ‖x - p‖ ≤ 2 * Lf) (hy : ∀ i, -(L / 2) ≤ (y - p) i ∧ (y - p) i < L / 2)
    (hsep : 4 / Lf ≤ ‖x - y‖) (κ : Fin n → Fin d) :
    ‖iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ))‖ ≤
      C4 * ((4 / Lf) ^ (-s - n) + 1 + 1) := by
  have hLf0 : 0 < Lf := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have h4 : 0 < 4 / Lf := by positivity
  have h4le : 4 / Lf ≤ 4 := by
    rw [div_le_iff₀ hLf0]; nlinarith
  set u : Euc d := x - y with hu
  have hui : ∀ i, |u i| ≤ 2 * Lf + L / 2 := by
    intro i
    have h1 : |(x - p) i| ≤ 2 * Lf := (PiLp.norm_apply_le (x - p) i).trans' (by simp [Real.norm_eq_abs]) |>.trans hx
    have h2 : |(y - p) i| ≤ L / 2 := abs_le.2 ⟨(hy i).1, (hy i).2.le⟩
    have : u i = (x - p) i - (y - p) i := by simp [hu]
    rw [this]
    calc |(x - p) i - (y - p) i| ≤ |(x - p) i| + |(y - p) i| := abs_sub _ _
      _ ≤ _ := by linarith
  set kk : Fin d → ℤ := fun i => if L / 2 < u i then 1 else if u i < -(L / 2) then -1 else 0 with hkk
  set u' : Euc d := u - L • latticePt kk with hu'
  have hu'i : ∀ i, u' i = u i - L * (kk i : ℝ) := by
    intro i; simp [hu', latticePt]
  have hcoord : ∀ i, |u' i| ≤ L / 2 ∧ (kk i ≠ 0 → L / 4 ≤ |u' i|) ∧ (kk i = 0 → u' i = u i) := by
    intro i
    have hb := abs_le.1 (hui i)
    rw [hu'i]
    by_cases h1 : L / 2 < u i
    · have : kk i = 1 := by simp [hkk, h1]
      rw [this]
      refine ⟨?_, fun _ => ?_, fun h => by simp at h⟩
      · rw [abs_le]; push_cast; constructor <;> nlinarith
      · push_cast
        rw [abs_of_nonpos (by nlinarith)]; nlinarith
    · by_cases h2 : u i < -(L / 2)
      · have : kk i = -1 := by simp [hkk, h1, h2]
        rw [this]
        refine ⟨?_, fun _ => ?_, fun h => by simp at h⟩
        · rw [abs_le]; push_cast; constructor <;> nlinarith
        · push_cast
          rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · have : kk i = 0 := by simp [hkk, h1, h2]
        rw [this]
        refine ⟨?_, fun h => absurd rfl h, fun _ => by simp⟩
        simp only [Int.cast_zero, mul_zero, sub_zero]
        rw [abs_le]; constructor <;> linarith [not_lt.1 h1, not_lt.1 h2]
  have hnorm : 4 / Lf ≤ ‖u'‖ := by
    by_cases hk : ∀ i, kk i = 0
    · have : u' = u := by
        ext i; rw [(hcoord i).2.2 (hk i)]
      rw [this]; exact hsep
    · push_neg at hk
      obtain ⟨i, hi⟩ := hk
      have h1 := (hcoord i).2.1 hi
      have h2 : |u' i| ≤ ‖u'‖ := (PiLp.norm_apply_le u' i).trans' (by simp [Real.norm_eq_abs])
      nlinarith
  have hne : u' ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  have hshift : iteratedFDeriv ℝ n γ (x - y) = iteratedFDeriv ℝ n γ u' := by
    have : x - y = u' + L • latticePt kk := by simp [hu', hu]
    rw [this]
    exact t7_iter_shift L hγp n u' kk
  rw [hshift]
  have hb := hT4 u' hne (fun i => (hcoord i).1)
  have hneg : -s - (n : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hr1 : ‖u'‖ ^ (-s - (n : ℝ)) ≤ (4 / Lf) ^ (-s - (n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos h4 hnorm hneg
  have hr2 : L ^ (-s - (n : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 hneg
  have hr3 : L ^ (-(n : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by simp)
  have hif1 : (if 0 < s then L ^ (-s - (n : ℝ)) else 0) ≤ 1 := by split_ifs <;> linarith
  have hif2 : (if s = 0 then L ^ (-(n : ℝ)) else 0) ≤ 1 := by split_ifs <;> linarith
  have hop : ‖iteratedFDeriv ℝ n γ u' (fun l => EuclideanSpace.single (κ l) (1 : ℝ))‖ ≤
      ‖iteratedFDeriv ℝ n γ u'‖ := by
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have : ∏ l : Fin n, ‖(EuclideanSpace.single (κ l) (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [this, mul_one]
  refine hop.trans (hb.trans ?_)
  exact mul_le_mul_of_nonneg_left (by linarith) hC4

/-- The flow shifted by `e`: `Ψ'_τ = Ψ_τ(· + e)`, whose unit cells are the cells `Ψ_τ(z' + e + [0,1]^d)`. -/
def t7shift (Ψ : ℝ → Euc d → Euc d) (e : Euc d) : ℝ → Euc d → Euc d := fun t x => Ψ t (x + e)

lemma t7_shift_bij {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} (e : Euc d) (hbij : Function.Bijective (Ψ τ)) :
    Function.Bijective (t7shift Ψ e τ) :=
  hbij.comp (Equiv.addRight e).bijective

lemma t7_shift_invFun {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} (e : Euc d) (hbij : Function.Bijective (Ψ τ))
    (w : Euc d) :
    Function.invFun (t7shift Ψ e τ) w = Function.invFun (Ψ τ) w - e := by
  have hb := t7_shift_bij e hbij
  apply hb.injective
  rw [Function.rightInverse_invFun hb.surjective w]
  simp only [t7shift, sub_add_cancel]
  exact (Function.rightInverse_invFun hbij.surjective w).symm

lemma t7_shift_cell (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (e : Euc d) (z : Fin d → ℤ) :
    flowCell (t7shift Ψ e) τ z = flowCellAt Ψ τ (latticePt z + e) := by
  ext y
  simp only [flowCell, flowCellAt, mem_image, mem_setOf_eq, t7shift]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + e, fun i => ?_, rfl⟩
    have := hx i
    simp only [PiLp.sub_apply, PiLp.add_apply] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - e, fun i => ?_, by rw [sub_add_cancel]⟩
    have := hx i
    simp only [PiLp.sub_apply, PiLp.add_apply] at this ⊢
    constructor <;> linarith [this.1, this.2]

lemma t7_alg (Nr A Sr Vr V2r : ℝ) (hN : 0 ≤ Nr) (hA : 0 ≤ A) (hS : 0 ≤ Sr) (hV : 0 ≤ Vr) (_hV2 : 0 ≤ V2r)
    (T J : ℝ≥0∞)
    (hJ : J ^ 2 ≤ (ENNReal.ofReal A * ENNReal.ofReal Sr * ENNReal.ofReal Vr) * (ENNReal.ofReal A * T)) :
    (ENNReal.ofReal Nr * J) ^ 2 * ENNReal.ofReal V2r ≤ ENNReal.ofReal (Nr ^ 2 * A ^ 2 * Sr * Vr * V2r) * T := by
  have key : ENNReal.ofReal (Nr ^ 2 * A ^ 2 * Sr * Vr * V2r) =
      ENNReal.ofReal Nr ^ 2 * ENNReal.ofReal A ^ 2 * ENNReal.ofReal Sr * ENNReal.ofReal Vr *
        ENNReal.ofReal V2r := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hN, ENNReal.ofReal_pow hA]
  rw [key]
  calc (ENNReal.ofReal Nr * J) ^ 2 * ENNReal.ofReal V2r
      = ENNReal.ofReal Nr ^ 2 * J ^ 2 * ENNReal.ofReal V2r := by ring
    _ ≤ ENNReal.ofReal Nr ^ 2 * ((ENNReal.ofReal A * ENNReal.ofReal Sr * ENNReal.ofReal Vr) *
          (ENNReal.ofReal A * T)) * ENNReal.ofReal V2r := by gcongr
    _ = _ := by ring

lemma t7_measurableSet_box (L : ℝ) (p : Euc d) : MeasurableSet {y : Euc d | y - p ∈ centeredBox d L} := by
  have : {y : Euc d | y - p ∈ centeredBox d L} =
      ⋂ i, ({y : Euc d | -(L / 2) ≤ (y - p) i} ∩ {y : Euc d | (y - p) i < L / 2}) := by
    ext y; simp [centeredBox]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.inter ?_ ?_
  · exact measurableSet_le measurable_const (by fun_prop)
  · exact measurableSet_lt (by fun_prop) measurable_const

lemma t7_core {s : ℝ} (hs0 : 0 ≤ s) {n : ℕ} (hn1 : 1 ≤ n) {C4 : ℝ} (hC4 : 0 ≤ C4)
    {Lf L : ℝ} (hLf : 1 ≤ Lf) (hL16 : 16 * Lf ≤ L) {γ : Euc d → ℝ}
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x)
    (hT4 : ∀ u : Euc d, u ≠ 0 → (∀ i, |u i| ≤ L / 2) →
      ‖iteratedFDeriv ℝ n γ u‖ ≤ C4 * (‖u‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) +
        (if s = 0 then L ^ (-(n : ℝ)) else 0)))
    {m : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ) {μ : Euc d → ℝ}
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hdec : ∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ)
    {j : ℕ} (hj : j ≤ m + 1) (idx : Fin j → Fin d) (κ : Fin n → Fin d)
    (ψ : Euc d → ℝ) (hψp : ∀ (x : Euc d) (k : Fin d → ℤ), ψ (x + L • latticePt k) = ψ x)
    (ch : Euc d → ℝ) (hch : ∀ y, ch y ∈ Icc (0 : ℝ) 1) (x p : Euc d) (hx : ‖x - p‖ ≤ 2 * Lf)
    (hsep : ∀ y, 1 - ch y ≠ 0 → 4 / Lf ≤ ‖x - y‖) :
    ‖∫ y in {y | y - p ∈ centeredBox d L},
        iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
          ((1 - ch y) * (partialDeriv idx μ y * ψ y))‖ₑ ≤
      (2 : ℝ≥0∞) ^ d * ∫⁻ y, ENNReal.ofReal (C4 * ((4 / Lf) ^ (-s - n) + 1 + 1) * Λ *
        jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ := by
  have hLf0 : 0 < Lf := by linarith
  have hL0 : 0 < L := by linarith
  set K0 : ℝ := C4 * ((4 / Lf) ^ (-s - n) + 1 + 1) with hK0
  have hK00 : 0 ≤ K0 := by
    rw [hK0]; have : 0 ≤ (4 / Lf) ^ (-s - (n : ℝ)) := Real.rpow_nonneg (by positivity) _
    positivity
  set c1 : ℝ := K0 * Λ with hc1
  have hc10 : 0 ≤ c1 := mul_nonneg hK00 hΛ
  set G : Euc d → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (c1 * jbracket (t7wper L y) ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ with hG
  have hGp : ∀ (y : Euc d) (k : Fin d → ℤ), G (y + L • latticePt k) = G y := by
    intro y k
    simp only [hG, t7_wper_shift hL0, hψp]
  have hSm := t7_measurableSet_box L p
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ y in {y | y - p ∈ centeredBox d L}, ‖iteratedFDeriv ℝ n γ (x - y)
          (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) * ((1 - ch y) * (partialDeriv idx μ y * ψ y))‖ₑ
      ≤ ∫⁻ y in {y | y - p ∈ centeredBox d L}, G y := by
        refine setLIntegral_mono' hSm fun y hy => ?_
        by_cases h0 : 1 - ch y = 0
        · simp [h0]
        have hker := t7_kernel_ptwise hs0 hn1 hC4 hLf hL16 hγp hT4 hx hy (hsep y h0) κ
        have hmu := t7_mu_bound hL0 hμp hdec j (by omega) idx y
        have hc : |1 - ch y| ≤ 1 := by
          have := hch y
          rw [abs_le]; constructor <;> linarith [this.1, this.2]
        have hjb : 0 < jbracket (t7wper L y) ^ (-((d : ℝ) + 3)) :=
          Real.rpow_pos_of_pos (by unfold jbracket; positivity) _
        rw [← ofReal_norm, hG]
        simp only
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        calc ‖iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ))‖ *
              (|1 - ch y| * (|partialDeriv idx μ y| * |ψ y|))
            ≤ K0 * (1 * ((Λ * jbracket (t7wper L y) ^ (-((d : ℝ) + 3))) * |ψ y|)) := by
              gcongr
          _ = _ := by rw [hc1]; ring
    _ ≤ (2 : ℝ≥0∞) ^ d * ∫⁻ y in centeredBox d L, G y := t7_box_lintegral hL0 p G hGp
    _ ≤ (2 : ℝ≥0∞) ^ d * ∫⁻ y, ENNReal.ofReal (c1 * jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ := by
        refine mul_le_mul' le_rfl ?_
        have hcm : MeasurableSet (centeredBox d L) := by
          simpa using t7_measurableSet_box L (0 : Euc d)
        calc ∫⁻ y in centeredBox d L, G y
            ≤ ∫⁻ y in centeredBox d L, ENNReal.ofReal (c1 * jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ := by
              refine setLIntegral_mono' hcm fun y hy => ?_
              have : t7wper L y = y := t7_wper_of_mem hL0 y hy
              simp only [hG, this]; exact le_rfl
          _ ≤ _ := setLIntegral_le_lintegral _ _

lemma t7_meas_K (γ : Euc d → ℝ) {n : ℕ} (hn : 1 ≤ n) (v : Fin n → Euc d) :
    Measurable (fun u : Euc d => iteratedFDeriv ℝ n γ u v) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  letI : MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => Euc d) ℝ) := borel _
  haveI : BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => Euc d) ℝ) := ⟨rfl⟩
  have h : Measurable (iteratedFDeriv ℝ (k + 1) γ) := by
    have : iteratedFDeriv ℝ (k + 1) γ =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Euc d) ℝ).symm ∘
          fderiv ℝ (iteratedFDeriv ℝ k γ) :=
      iteratedFDeriv_succ_eq_comp_left
    rw [this]
    exact (LinearIsometryEquiv.continuous _).measurable.comp (measurable_fderiv ℝ _)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k + 1) => Euc d) ℝ v).continuous.measurable.comp h

lemma t7_meas_partial {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) {j : ℕ} (idx : Fin j → Fin d) :
    Measurable (partialDeriv idx μ) := by
  have h : Continuous (iteratedFDeriv ℝ j μ) := hμ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).continuous.comp h).measurable

/-- `screened_far_periodic` for every kernel order `1 ≤ n ≤ m+2` (the proof only used these two bounds on `n`). -/
theorem screened_far_periodic_gen (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ Cb T R : ℝ)
    (n : ℕ) (hn : 1 ≤ n ∧ n ≤ m + 2) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C L₁ : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ (L : ℝ) (γ : Euc d → ℝ), 1 ≤ L → L₁ ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ μ : Euc d → ℝ, ContDiff ℝ ∞ μ → (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      (∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ) →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ e : Euc d, ‖e‖ ≤ R →
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal C) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal C * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (κ : Fin n → Fin d) (ψ : Euc d → ℝ), Measurable ψ →
          (∀ (x : Euc d) (k : Fin d → ℤ), ψ (x + L • latticePt k) = ψ x) → ∀ z : Fin d → ℤ,
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z + e) x *
                ∫ y in {y | y - Ψ τ (latticePt z + e) ∈ centeredBox d L},
                  iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
                    ((1 - advCutoff χh Ψ τ (latticePt z + e) y) * (partialDeriv idx μ y * ψ y))) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 := by
  intro χ χh hχ
  have hn1 : 1 ≤ n := hn.1
  have hn2 : n ≤ m + 2 := hn.2
  have hns : 0 < (n : ℝ) + s := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  obtain ⟨C4, hC4, hT4⟩ := HRS.MH.AdjointRd.Phase2SA12Construction.periodic_kernel_cube hd s hs0 hsd m
  obtain ⟨CF, hCF0, hCF⟩ := flow_lip_sep_proof hd m Cb T χ χh hχ
  obtain ⟨Lχ, -, hLχ1, hLχ2⟩ := cutoff_lipschitz_proof χ χh hχ
  obtain ⟨Lf, hLfdef⟩ : ∃ Lf : ℝ, Lf = Real.exp (CF * |T|) := ⟨_, rfl⟩
  have hLf1 : 1 ≤ Lf := hLfdef ▸ Real.one_le_exp (mul_nonneg hCF0 (abs_nonneg T))
  have hLf0 : 0 < Lf := by linarith
  obtain ⟨R', hR'def⟩ : ∃ R' : ℝ, R' = |R| := ⟨_, rfl⟩
  have hR'0 : 0 ≤ R' := hR'def ▸ abs_nonneg R
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.exp (|Cb| * |T|) - 1 + Lf * R' := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    have : 1 ≤ Real.exp (|Cb| * |T|) := Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [hBdef]; nlinarith [mul_nonneg hLf0.le hR'0]
  obtain ⟨Kw, hKwdef⟩ : ∃ Kw : ℝ, Kw = Lf + Lf * B + Real.sqrt d + 1 := ⟨_, rfl⟩
  have hKw : 0 < Kw := by rw [hKwdef]; positivity
  obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = C4 * ((4 / Lf) ^ (-s - n) + 1 + 1) := ⟨_, rfl⟩
  have hK00 : 0 ≤ K0 := by
    rw [hK0def]; have : 0 ≤ (4 / Lf) ^ (-s - (n : ℝ)) := Real.rpow_nonneg (by positivity) _
    positivity
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ≥0∞, S = ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) := ⟨_, rfl⟩
  have hS : S < ⊤ := hSdef ▸ cellWeight_tsum_lt_top_proof hd
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ≥0∞, V = volume (Metric.closedBall (0 : Euc d) (Lf * Real.sqrt d)) :=
    ⟨_, rfl⟩
  have hV : V < ⊤ := hVdef ▸ measure_closedBall_lt_top
  obtain ⟨V2, hV2def⟩ : ∃ V2 : ℝ≥0∞, V2 = volume (Metric.closedBall (0 : Euc d) (Lf * 2)) := ⟨_, rfl⟩
  have hV2 : V2 < ⊤ := hV2def ▸ measure_closedBall_lt_top
  obtain ⟨A0, hA0def⟩ : ∃ A0 : ℝ, A0 = K0 * Kw ^ ((d : ℝ) + 3) := ⟨_, rfl⟩
  have hA00 : 0 ≤ A0 := by rw [hA0def]; positivity
  obtain ⟨Nr, hNrdef⟩ : ∃ Nr : ℝ, Nr = (2 : ℝ) ^ d := ⟨_, rfl⟩
  have hNr0 : 0 ≤ Nr := by rw [hNrdef]; positivity
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = Nr ^ 2 * A0 ^ 2 * S.toReal * V.toReal * V2.toReal := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0def]; positivity
  refine ⟨C0 + S.toReal + 1, 16 * Lf, ?_⟩
  intro b Ψ hb hΨ L γ hL1 hL₁ hγ μ hμ hμp hdec τ hτ e he
  have hΛ : 0 ≤ Λ := by
    obtain ⟨k, hk⟩ := hdec 0 (by omega) 0
    refine le_trans (mul_nonneg (Real.rpow_nonneg (by unfold jbracket; positivity) _) (norm_nonneg _)) hk
  have hL0 : 0 < L := by linarith
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ |T| := le_trans hτ.2 (le_abs_self T)
  obtain ⟨hlipF, hlipI, hsep⟩ := hCF b Ψ hb hΨ τ hτ
  have hexp : Real.exp (CF * τ) ≤ Lf := hLfdef ▸ Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτT hCF0)
  have hlipL : ∀ x y : Euc d, ‖Ψ τ x - Ψ τ y‖ ≤ Lf * ‖x - y‖ := fun x y =>
    le_trans (hlipF x y) (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hlipIL : ∀ x y : Euc d, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ Lf * ‖x - y‖ :=
    fun x y => le_trans (hlipI x y) (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hsepL : ∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (advCutoff χ Ψ τ z) →
      y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) → 4 / Lf ≤ ‖x - y‖ := by
    intro z x y hx hy
    refine le_trans ?_ (hsep z x y hx hy)
    rw [div_eq_mul_inv, hLfdef, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_left hτT hCF0))) (by norm_num)
  have hO : ‖Ψ τ 0‖ ≤ Real.exp (|Cb| * |T|) - 1 := by
    refine le_trans (flow_origin_proof m Cb T b Ψ hb hΨ τ hτ)
      (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cb) hτ0)
      (mul_le_mul_of_nonneg_left hτT (abs_nonneg _))
  have hbij : Function.Bijective (Ψ τ) := hΨ.bij τ hτ
  -- the shifted flow
  set Ψ' : ℝ → Euc d → Euc d := t7shift Ψ e with hΨ'
  have hbij' : Function.Bijective (Ψ' τ) := t7_shift_bij e hbij
  have hlip' : ∀ x y : Euc d, ‖Ψ' τ x - Ψ' τ y‖ ≤ Lf * ‖x - y‖ := by
    intro x y
    have := hlipL (x + e) (y + e)
    rwa [add_sub_add_right_eq_sub] at this
  have hlipi' : ∀ x y : Euc d, ‖Function.invFun (Ψ' τ) x - Function.invFun (Ψ' τ) y‖ ≤ Lf * ‖x - y‖ := by
    intro x y
    rw [hΨ', t7_shift_invFun e hbij, t7_shift_invFun e hbij, sub_sub_sub_cancel_right]
    exact hlipIL x y
  have horig' : ‖Ψ' τ 0‖ ≤ B := by
    have h1 : ‖Ψ τ e - Ψ τ 0‖ ≤ Lf * ‖e - 0‖ := hlipL e 0
    have h2 : ‖Ψ' τ 0‖ = ‖Ψ τ e‖ := by simp [hΨ', t7shift]
    rw [h2, hBdef]
    calc ‖Ψ τ e‖ ≤ ‖Ψ τ e - Ψ τ 0‖ + ‖Ψ τ 0‖ := norm_le_norm_sub_add _ _
      _ ≤ Lf * ‖e - 0‖ + (Real.exp (|Cb| * |T|) - 1) := add_le_add h1 hO
      _ ≤ _ := by
        rw [sub_zero, hR'def]
        nlinarith [mul_le_mul_of_nonneg_left (he.trans (le_abs_self R)) hLf0.le]
  have hgeo := flowCell_geometry_proof Ψ τ Lf hLf0.le hbij hlipL
  refine ⟨fun _ z' => Real.toNNReal (cellWeight d z'), ?_, ?_, ?_⟩
  · refine iSup_le fun z => ?_
    have : ∑' z' : Fin d → ℤ, ((Real.toNNReal (cellWeight d z') : ℝ≥0) : ℝ≥0∞) = S := by
      rw [hSdef]; rfl
    rw [this]
    exact le_trans (ENNReal.ofReal_toReal hS.ne).symm.le (ENNReal.ofReal_le_ofReal (by linarith))
  · intro z'
    calc ∑' z, ENNReal.ofReal (cellWeight d z) * ((Real.toNNReal (cellWeight d z') : ℝ≥0) : ℝ≥0∞)
        = S * ENNReal.ofReal (cellWeight d z') := by
          rw [hSdef, ← ENNReal.tsum_mul_right]; rfl
      _ ≤ ENNReal.ofReal (C0 + S.toReal + 1) * ENNReal.ofReal (cellWeight d z') := by
          refine mul_le_mul' ?_ le_rfl
          exact le_trans (ENNReal.ofReal_toReal hS.ne).symm.le (ENNReal.ofReal_le_ofReal (by linarith))
  · intro j hj idx κ ψ hψ hψp z
    have hT4' := hT4 L hL1 γ hγ n hn2 hns
    have hSr : S = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hS.ne).symm
    have hVr : V = ENNReal.ofReal V.toReal := (ENNReal.ofReal_toReal hV.ne).symm
    have hV2r : V2 = ENNReal.ofReal V2.toReal := (ENNReal.ofReal_toReal hV2.ne).symm
    obtain ⟨c, hcdef⟩ : ∃ c : Euc d, c = latticePt z + e := ⟨_, rfl⟩
    rw [← hcdef]
    obtain ⟨p, hpdef⟩ : ∃ p : Euc d, p = Ψ τ c := ⟨_, rfl⟩
    rw [← hpdef]
    have hfacts := advCutoff_facts_proof χ χh hχ Ψ τ Lf Lχ hLf0.le hlipIL ⟨hLχ1, hLχ2⟩ c
    have hxb : ∀ x ∈ tsupport (advCutoff χ Ψ τ c), ‖x - p‖ ≤ 2 * Lf := by
      intro x hx
      have := hgeo.2.2.2.2 c 2 (by norm_num) (hfacts.2.2.1 x hx)
      rw [Metric.mem_closedBall, dist_eq_norm, ← hpdef] at this
      linarith
    obtain ⟨J, hJdef⟩ : ∃ J : ℝ≥0∞, J = ∫⁻ y, ENNReal.ofReal (C4 * ((4 / Lf) ^ (-s - n) + 1 + 1) * Λ *
        jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ := ⟨_, rfl⟩
    have hNe : (2 : ℝ≥0∞) ^ d = ENNReal.ofReal Nr := by
      rw [hNrdef, ENNReal.ofReal_pow (by norm_num)]; simp
    have hcoreB : ∀ x ∈ tsupport (advCutoff χ Ψ τ c),
        ‖∫ y in {y | y - p ∈ centeredBox d L},
          iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
            ((1 - advCutoff χh Ψ τ c y) * (partialDeriv idx μ y * ψ y))‖ₑ ≤ ENNReal.ofReal Nr * J := by
      intro x hx
      rw [← hNe, hJdef]
      exact t7_core hs0 hn1 hC4 hLf1 hL₁ hγ.periodic hT4' hΛ hμp hdec hj idx κ ψ hψp
        (advCutoff χh Ψ τ c) hfacts.2.1 x p (hxb x hx)
        (fun y h0 => hsepL c x y hx (subset_tsupport _ h0))
    -- the cell estimate for `J`
    have hI := far_I_sq hd Ψ' τ Lf B hLf1 hB0 hbij' hlip' hlipi' horig' (K0 * Λ) (mul_nonneg hK00 hΛ) ψ hψ
    rw [← hKwdef, ← hSdef, ← hVdef] at hI
    have hcell : ∀ z', flowCell Ψ' τ z' = flowCellAt Ψ τ (latticePt z' + e) := fun z' => t7_shift_cell Ψ τ e z'
    simp only [hcell] at hI
    have hEeq : K0 * Λ * Kw ^ ((d : ℝ) + 3) = A0 * Λ := by rw [hA0def]; ring
    rw [hEeq] at hI
    have hJK : K0 = C4 * ((4 / Lf) ^ (-s - n) + 1 + 1) := hK0def
    have hJ' : J = ∫⁻ y, ENNReal.ofReal (K0 * Λ * jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ := by
      rw [hJdef, hJK]
    rw [← hJ'] at hI
    obtain ⟨T', hT'def⟩ : ∃ T' : ℝ≥0∞, T' = ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') *
        (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 := ⟨_, rfl⟩
    rw [← hT'def] at hI
    have hI2 : J ^ 2 ≤ (ENNReal.ofReal (A0 * Λ) * ENNReal.ofReal S.toReal * ENNReal.ofReal V.toReal) *
        (ENNReal.ofReal (A0 * Λ) * T') := by
      rw [← hSr, ← hVr]; exact hI
    have halg := t7_alg Nr (A0 * Λ) S.toReal V.toReal V2.toReal hNr0 (mul_nonneg hA00 hΛ)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg T' J hI2
    -- the right side in the required shape
    have hRHS : ∑' z', ((Real.toNNReal (cellWeight d z') : ℝ≥0) : ℝ≥0∞) *
        (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 = T' := by
      rw [hT'def]; rfl
    rw [hRHS]
    have hm : AEStronglyMeasurable (fun x => advCutoff χ Ψ τ c x *
        ∫ y in {y | y - p ∈ centeredBox d L},
          iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
            ((1 - advCutoff χh Ψ τ c y) * (partialDeriv idx μ y * ψ y))) volume := by
      have hΦc : Continuous (Function.invFun (Ψ τ)) := f5_cont_of_lip _ Lf hLf0.le hlipIL
      have hcχ : Continuous (advCutoff χ Ψ τ c) := hχ.1.1.continuous.comp (hΦc.sub continuous_const)
      have hcχh : Continuous (advCutoff χh Ψ τ c) := hχ.2.1.continuous.comp (hΦc.sub continuous_const)
      have hg : Measurable (fun y => (1 - advCutoff χh Ψ τ c y) * (partialDeriv idx μ y * ψ y)) :=
        (continuous_const.sub hcχh).measurable.mul ((t7_meas_partial hμ idx).mul hψ)
      have hK := t7_meas_K γ hn1 (fun l => EuclideanSpace.single (κ l) (1 : ℝ))
      have hjoint : Measurable (fun q : Euc d × Euc d =>
          iteratedFDeriv ℝ n γ (q.1 - q.2) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
            ((1 - advCutoff χh Ψ τ c q.2) * (partialDeriv idx μ q.2 * ψ q.2))) :=
        (hK.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)
      have hI := StronglyMeasurable.integral_prod_right
        (ν := (volume : Measure (Euc d)).restrict {y | y - p ∈ centeredBox d L})
        (f := fun x y => iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
            ((1 - advCutoff χh Ψ τ c y) * (partialDeriv idx μ y * ψ y))) hjoint.stronglyMeasurable
      exact (hcχ.stronglyMeasurable.mul hI).aestronglyMeasurable
    · rw [far_eLpNorm_sq _ hm]
      calc ∫⁻ x, ‖advCutoff χ Ψ τ c x *
            ∫ y in {y | y - p ∈ centeredBox d L},
              iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
                ((1 - advCutoff χh Ψ τ c y) * (partialDeriv idx μ y * ψ y))‖ₑ ^ 2
          ≤ ∫⁻ x, (Metric.closedBall p (Lf * 2)).indicator (fun _ => (ENNReal.ofReal Nr * J) ^ 2) x := by
            refine lintegral_mono fun x => ?_
            by_cases hx : x ∈ tsupport (advCutoff χ Ψ τ c)
            · have hxb' : x ∈ Metric.closedBall p (Lf * 2) := by
                rw [Metric.mem_closedBall, dist_eq_norm]; linarith [hxb x hx]
              rw [Set.indicator_of_mem hxb']
              have hc1 : ‖advCutoff χ Ψ τ c x‖ₑ ≤ 1 := by
                have hr := hfacts.1 x
                rw [Real.enorm_eq_ofReal hr.1]
                exact ENNReal.ofReal_le_one.2 hr.2
              rw [enorm_mul]
              have := mul_le_mul' hc1 (hcoreB x hx)
              rw [one_mul] at this
              gcongr
            · have h0 : advCutoff χ Ψ τ c x = 0 := image_eq_zero_of_notMem_tsupport hx
              simp [h0]
        _ = (ENNReal.ofReal Nr * J) ^ 2 * V2 := by
            rw [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet,
              Measure.addHaar_closedBall_center, hV2def, mul_comm Lf 2]
        _ = (ENNReal.ofReal Nr * J) ^ 2 * ENNReal.ofReal V2.toReal := by rw [← hV2r]
        _ ≤ ENNReal.ofReal (Nr ^ 2 * (A0 * Λ) ^ 2 * S.toReal * V.toReal * V2.toReal) * T' := halg
        _ ≤ ENNReal.ofReal ((C0 + S.toReal + 1) * Λ ^ 2) * T' := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have : Nr ^ 2 * (A0 * Λ) ^ 2 * S.toReal * V.toReal * V2.toReal = C0 * Λ ^ 2 := by
              rw [hC0def]; ring
            rw [this]
            nlinarith [sq_nonneg Λ, ENNReal.toReal_nonneg (a := S)]

theorem screened_far_periodic (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ Cb T R : ℝ)
    (n : ℕ) (hn : n = 1 ∨ n = 2) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C L₁ : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ (L : ℝ) (γ : Euc d → ℝ), 1 ≤ L → L₁ ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ μ : Euc d → ℝ, ContDiff ℝ ∞ μ → (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      (∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ) →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ e : Euc d, ‖e‖ ≤ R →
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal C) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal C * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (κ : Fin n → Fin d) (ψ : Euc d → ℝ), Measurable ψ →
          (∀ (x : Euc d) (k : Fin d → ℤ), ψ (x + L • latticePt k) = ψ x) → ∀ z : Fin d → ℤ,
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z + e) x *
                ∫ y in {y | y - Ψ τ (latticePt z + e) ∈ centeredBox d L},
                  iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
                    ((1 - advCutoff χh Ψ τ (latticePt z + e) y) * (partialDeriv idx μ y * ψ y))) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 := by
  have hn' : 1 ≤ n ∧ n ≤ m + 2 := by rcases hn with h | h <;> omega
  exact screened_far_periodic_gen hd hs0 hsd m Λ Cb T R n hn'

end HRS.MH.AdjointRdP
