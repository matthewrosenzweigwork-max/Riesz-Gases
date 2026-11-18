/-
# HRS.Equilibrium.PairMomentsTriple -- the three-particle term under the reference (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsAssemble
import HRS.Equilibrium.PairMomentsTower

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section PinnedWu

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- Single-site resampling for ordered pair sums under a pinned ensemble. -/
theorem evariance_pairSum_le_pins (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → Torus d) (hκ : weakKappa V β ≤ 1 / 2)
    {b : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry b))
    (hsym : ∀ x y, b x y = b y x) (c : ℝ) :
    evariance (fun X : Config d n => c * pairSumOrdered b X) (pinnedLaw V (β / N) n a) ≤
      ENNReal.ofReal (8 * c ^ 2) * ∑ i, ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) n a) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  set S := fieldSpec (V := V) hψ hlam n with hS
  have hSP : S.P = pinnedLaw V (β / N) n a := rfl
  have hF : Measurable (fun X : Config d n => c * pairSumOrdered b X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  have h1 := weak_resampling (B := B) V hβ hN0 hN a hκ _ hF
  refine h1.trans ?_
  have hper : ∀ i : Fin n, ∫⁻ x, evariance (fun z => c * pairSumOrdered b (update x i z))
      (siteKernel μ (pinnedDensity V (β / N) n a) i x) ∂(pinnedLaw V (β / N) n a)
      ≤ ENNReal.ofReal (4 * c ^ 2) * ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) n a) := by
    intro i
    have hG : ∀ x, siteKernel μ (pinnedDensity V (β / N) n a) i x = S.G i x := fun x => rfl
    have hrow := measurable_rowSum hm (N := n) i
    have hpt : ∀ x, evariance (fun z => c * pairSumOrdered b (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) n a) i x)
        ≤ ∫⁻ z, ENNReal.ofReal (4 * c ^ 2) *
            ‖∑ j ∈ Finset.univ.erase i, b (update x i z i) (update x i z j)‖ₑ ^ 2 ∂(S.G i x) := by
      intro x
      rw [hG]
      refine (evariance_le_lintegral_sub (S.G i x)
        (hF.comp (measurable_update x)).aestronglyMeasurable (c * pairRest b i x)).trans (le_of_eq ?_)
      refine lintegral_congr fun z => ?_
      have e1 := pairSum_update b hsym i x z
      have e2 : ∑ j ∈ Finset.univ.erase i, b (update x i z i) (update x i z j)
          = ∑ j ∈ Finset.univ.erase i, b z (x j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [update_self, update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [e2]
      simp only [Function.comp]
      rw [e1]
      have : c * (2 * ∑ j ∈ Finset.univ.erase i, b z (x j) + pairRest b i x) - c * pairRest b i x
          = (2 * c) * ∑ j ∈ Finset.univ.erase i, b z (x j) := by ring
      rw [this, enorm_sq_mul_real]
      ring_nf
    calc _ ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal (4 * c ^ 2) *
            ‖∑ j ∈ Finset.univ.erase i, b (update x i z i) (update x i z j)‖ₑ ^ 2 ∂(S.G i x)
          ∂(pinnedLaw V (β / N) n a) := lintegral_mono hpt
      _ = ∫⁻ Y, ENNReal.ofReal (4 * c ^ 2) * ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) n a) := by
        rw [← hSP]
        exact S.invariant i (fun Y => ENNReal.ofReal (4 * c ^ 2) *
          ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2)
          (measurable_const.mul (hrow.enorm.pow_const 2))
      _ = _ := by
        rw [lintegral_const_mul _ (hrow.enorm.pow_const 2)]
  calc 2 * ∑ i, ∫⁻ x, evariance (fun z => c * pairSumOrdered b (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) n a) i x) ∂(pinnedLaw V (β / N) n a)
      ≤ 2 * ∑ i : Fin n, (ENNReal.ofReal (4 * c ^ 2) * ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) n a)) := by
        gcongr with i _
        exact hper i
    _ = _ := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rw [show (8 : ℝ) * c ^ 2 = 2 * (4 * c ^ 2) by ring, ENNReal.ofReal_mul (by norm_num)]
        simp

end PinnedWu

section SecondMomentGen

variable {α : Type*} [MeasurableSpace α]

/-- `E F² ≤ Var F + m²` when `|E F| ≤ m`. -/
theorem lintegral_sq_le_evariance_add {P : Measure α} [IsProbabilityMeasure P] {F : α → ℝ}
    (hF : Measurable F) {m : ℝ} (hm : |∫ y, F y ∂P| ≤ m) :
    ∫⁻ y, ‖F y‖ₑ ^ 2 ∂P ≤ evariance F P + ENNReal.ofReal (m ^ 2) := by
  by_cases htop : evariance F P = ⊤
  · rw [htop]; simp
  have hmem : MemLp F 2 P := (evariance_lt_top_iff_memLp hF.aestronglyMeasurable).1 (lt_top_iff_ne_top.2 htop)
  rw [Quad.lintegral_enorm_sq_eq_ofReal hmem]
  have e1 := variance_eq_sub hmem
  simp only [Pi.pow_apply] at e1
  have hint : ∫ y, F y ^ 2 ∂P = variance F P + (∫ y, F y ∂P) ^ 2 := by linarith
  rw [hint, ENNReal.ofReal_add (variance_nonneg _ _) (sq_nonneg _), ofReal_variance hmem]
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (sq_le_sq' (abs_le.1 hm).1 (abs_le.1 hm).2))

end SecondMomentGen

section PinRow

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- The `pinWeight`-weighted integral of a function of the pin variable is the integral of the
corresponding coordinate marginal, hence at most the integral against the pole weight. -/
theorem lintegral_pinWeight_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N m : ℕ} (hN0 : 0 < N)
    (hN : m + 1 + Fintype.card B ≤ N) (a : B → Torus d) {Ψ : Torus d → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ u, pinWeight V (β / N) a m u * Ψ u ∂μ ≤
      ∫⁻ u, Ψ u * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a u)) ∂μ := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hΦ : Measurable fun Y : Fin (m + 1) → Torus d => Ψ (Y 0) := hΨ.comp (measurable_pi_apply 0)
  have h1 := lintegral_pinned_succ V hlam a (0 : Fin (m + 1)) hΦ
  have h2 : ∫⁻ Y, Ψ (Y 0) ∂(pinnedLaw V (β / N) (m + 1) a) =
      ∫⁻ u, pinWeight V (β / N) a m u * Ψ u ∂μ := by
    rw [h1]
    refine lintegral_congr fun u => ?_
    have hP := isProb_pinnedLaw V hlam m (pinsWith a u)
    simp only [insertAt_same]
    rw [lintegral_const, measure_univ, mul_one]
  rw [← h2]
  have h3 := lintegral_marg_le V hβ hN0 hN a (0 : Fin (m + 1)) hΨ
  rw [lintegral_map hΨ (measurable_pi_apply 0)] at h3
  exact h3

/-- **Row second moment under a pinned ensemble**, with pointwise bounds `𝒱(u)`, `𝓜(u)`. -/
theorem row_moment_pins_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N m : ℕ} (hN0 : 0 < N)
    (hN : m + 1 + Fintype.card B ≤ N) (a : B → Torus d) (hκ : weakKappa V β ≤ 1 / 2)
    {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) [NeZero m] (i : Fin (m + 1))
    {𝒱 : Torus d → ℝ≥0∞} {𝓜 : Torus d → ℝ}
    (hV : ∀ᵐ u ∂μ, ∫⁻ z, ‖h u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / N) (pinsWith a u) z)) ∂μ ≤ 𝒱 u)
    (hM : ∀ᵐ u ∂μ, |∑ k : Fin m, ∫ z, h u z ∂((pinnedLaw V (β / N) m (pinsWith a u)).map
        (fun Y => Y k))| ≤ 𝓜 u) :
    ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2 ∂(pinnedLaw V (β / N) (m + 1) a)
      ≤ ∫⁻ u, pinWeight V (β / N) a m u *
          (ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2)) ∂μ := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hΦ : Measurable fun Y : Fin (m + 1) → Torus d => ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2 :=
    (measurable_rowSum hm i).enorm.pow_const 2
  rw [lintegral_pinned_succ V hlam a i hΦ]
  refine lintegral_mono_ae ?_
  filter_upwards [hV, hM] with u hVu hMu
  refine mul_le_mul' le_rfl ?_
  have hrow : ∀ y : Fin m → Torus d, ∑ j ∈ Finset.univ.erase i, h (insertAt i u y i) (insertAt i u y j)
      = ∑ k, h u (y k) - 0 := by
    intro y
    rw [insertAt_same, sum_erase_insertAt i u y (fun z => h u z), sub_zero]
  simp_rw [hrow]
  have hcm : Measurable (h u) := measurable_h_x hm u
  have hcard : m + Fintype.card (Option B) ≤ N := by
    simp only [Fintype.card_option]; omega
  refine (second_moment_pinned (B := Option B) V hβ (N := N) hN0 hcard (pinsWith a u) hκ hcm 0).trans ?_
  refine add_le_add (mul_le_mul' le_rfl hVu) (ENNReal.ofReal_le_ofReal ?_)
  have := abs_le.1 hMu
  have h2 : (∑ k, ∫ z, h u z ∂((pinnedLaw V (β / N) m (pinsWith a u)).map (fun y => y k)) - 0) ^ 2
      ≤ (𝓜 u) ^ 2 := by
    rw [sub_zero]; exact sq_le_sq' this.1 this.2
  exact h2

end PinRow

/-! ### Triple sums -/

section TripleSums

/-- The triple sum over indices different from `i`. -/
def tripleRest (g3 : Torus d → Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (Y : Config d N) : ℝ :=
  ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a,
    ∑ c ∈ ((Finset.univ.erase i).erase a).erase b, g3 (Y a) (Y b) (Y c)

/-- The part of the triple sum with `x_i = z` in the first slot. -/
def tripleB (g3 : Torus d → Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (z : Torus d)
    (Y : Config d N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, g3 z (Y j) (Y k)

theorem tripleRest_update (g3 : Torus d → Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (Y : Config d N)
    (z : Torus d) : tripleRest g3 i (update Y i z) = tripleRest g3 i Y := by
  unfold tripleRest
  have h1 : ∀ a ∈ Finset.univ.erase i, update Y i z a = Y a := fun a ha =>
    update_of_ne (Finset.ne_of_mem_erase ha) _ _
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun c hc => ?_
  have hbi : b ∈ Finset.univ.erase i := Finset.mem_of_mem_erase hb
  have hci : c ∈ Finset.univ.erase i := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  rw [h1 a ha, h1 b hbi, h1 c hci]

theorem tripleSum_update (g3 : Torus d → Torus d → Torus d → ℝ) (hsym : IsSymmTriple g3) {N : ℕ}
    (i : Fin N) (Y : Config d N) (z : Torus d) :
    tripleSum g3 (update Y i z) = 3 * tripleB g3 i z Y + tripleRest g3 i Y := by
  classical
  set U : Config d N := update Y i z with hU
  have hUi : U i = z := update_self i z Y
  have hUa : ∀ a, a ≠ i → U a = Y a := fun a ha => update_of_ne ha _ _
  have hsym12 : ∀ x y w, g3 x y w = g3 y x w := fun x y w => (hsym x y w).1
  have hsym23 : ∀ x y w, g3 x y w = g3 x w y := fun x y w => (hsym x y w).2
  unfold tripleSum
  -- outer split at `a = i`
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hB : ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, g3 (U i) (U j) (U k)
      = tripleB g3 i z Y := by
    unfold tripleB
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hj' : j ≠ i := Finset.ne_of_mem_erase hj
    have hk' : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    rw [hUi, hUa j hj', hUa k hk']
  rw [hB]
  -- inner splits
  have hmid : ∀ a ∈ Finset.univ.erase i,
      ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, g3 (U a) (U b) (U c)
      = ∑ c ∈ (Finset.univ.erase a).erase i, g3 (U a) (U i) (U c)
        + ∑ b ∈ (Finset.univ.erase a).erase i, (g3 (U a) (U b) (U i)
          + ∑ c ∈ ((Finset.univ.erase a).erase b).erase i, g3 (U a) (U b) (U c)) := by
    intro a ha
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    have hmem : i ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hai.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase (Finset.univ.erase a) _ hmem]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbi : b ≠ i := Finset.ne_of_mem_erase hb
    have hba : b ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb)
    have hmem2 : i ∈ (Finset.univ.erase a).erase b :=
      Finset.mem_erase.2 ⟨hbi.symm, hmem⟩
    rw [← Finset.add_sum_erase ((Finset.univ.erase a).erase b) _ hmem2]
  rw [Finset.sum_congr rfl hmid]
  simp only [Finset.sum_add_distrib]
  -- identify the three groups
  have g1 : ∑ a ∈ Finset.univ.erase i, ∑ c ∈ (Finset.univ.erase a).erase i, g3 (U a) (U i) (U c)
      = tripleB g3 i z Y := by
    unfold tripleB
    refine Finset.sum_congr rfl fun a ha => ?_
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    rw [Finset.erase_right_comm]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hci : c ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    rw [hUi, hUa a hai, hUa c hci, hsym12]
  have g2 : ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase a).erase i, g3 (U a) (U b) (U i)
      = tripleB g3 i z Y := by
    unfold tripleB
    refine Finset.sum_congr rfl fun a ha => ?_
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    rw [Finset.erase_right_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbi : b ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb)
    rw [hUi, hUa a hai, hUa b hbi, hsym23, hsym12]
  have g3' : ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase a).erase i,
      ∑ c ∈ ((Finset.univ.erase a).erase b).erase i, g3 (U a) (U b) (U c) = tripleRest g3 i Y := by
    unfold tripleRest
    refine Finset.sum_congr rfl fun a ha => ?_
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    rw [Finset.erase_right_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbi : b ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb)
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have e : ((Finset.univ.erase a).erase b).erase i = ((Finset.univ.erase i).erase a).erase b := by
      ext c; simp only [Finset.mem_erase, Finset.mem_univ, and_true]; tauto
    rw [e]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hci : c ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))
    rw [hUa a hai, hUa b hbi, hUa c hci]
  rw [g1, g2, g3']
  ring

theorem measurable_tripleSum {g3 : Torus d → Torus d → Torus d → ℝ}
    (hm : Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2)) {N : ℕ} :
    Measurable (fun X : Config d N => tripleSum g3 X) := by
  unfold tripleSum
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.comp (g := fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) hm
    (f := fun X : Config d N => (X i, X j, X k))
    ((measurable_pi_apply i).prodMk ((measurable_pi_apply j).prodMk (measurable_pi_apply k)))

end TripleSums

section TripleWu

theorem tripleB_update (g3 : Torus d → Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (z : Torus d)
    (Y : Config d N) (z' : Torus d) : tripleB g3 i z (update Y i z') = tripleB g3 i z Y := by
  unfold tripleB
  have h1 : ∀ a ∈ Finset.univ.erase i, update Y i z' a = Y a := fun a ha =>
    update_of_ne (Finset.ne_of_mem_erase ha) _ _
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
  rw [h1 j hj, h1 k (Finset.mem_of_mem_erase hk)]

theorem measurable_tripleB {g3 : Torus d → Torus d → Torus d → ℝ}
    (hm : Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2)) {N : ℕ} (i : Fin N) :
    Measurable (fun Y : Config d N => tripleB g3 i (Y i) Y) := by
  unfold tripleB
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.comp (g := fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) hm
    (f := fun Y : Config d N => (Y i, Y j, Y k))
    ((measurable_pi_apply i).prodMk ((measurable_pi_apply j).prodMk (measurable_pi_apply k)))

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- **Single-site resampling for ordered triple sums**:
`Var_R(c ∑ g₃) ≤ 18 c² ∑_i E_R |B_i|²`, `B_i = ∑_{j≠k≠i} g₃(x_i,x_j,x_k)`. -/
theorem evariance_tripleSum_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN0 : 0 < N)
    (hκ : weakKappa V β ≤ 1 / 2) {g3 : Torus d → Torus d → Torus d → ℝ}
    (hm : Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2))
    (hsym : IsSymmTriple g3) (c : ℝ) :
    evariance (fun X : Config d N => c * tripleSum g3 X)
        (pinnedLaw V (β / N) N (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (18 * c ^ 2) * ∑ i, ∫⁻ Y, ‖tripleB g3 i (Y i) Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  set S := fieldSpec (V := V) hψ hlam N with hS
  have hSP : S.P = pinnedLaw V (β / N) N (fun e : Empty => e.elim) := rfl
  have hF : Measurable (fun X : Config d N => c * tripleSum g3 X) :=
    measurable_const.mul (measurable_tripleSum hm)
  have h1 := weak_resampling (B := Empty) V hβ hN0 (by simp) (fun e : Empty => e.elim) hκ _ hF
  refine h1.trans ?_
  have hper : ∀ i : Fin N, ∫⁻ x, evariance (fun z => c * tripleSum g3 (update x i z))
      (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (9 * c ^ 2) * ∫⁻ Y, ‖tripleB g3 i (Y i) Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
    intro i
    have hG : ∀ x, siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x = S.G i x :=
      fun x => rfl
    have hrow := measurable_tripleB hm (N := N) i
    have hpt : ∀ x, evariance (fun z => c * tripleSum g3 (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ≤ ∫⁻ z, ENNReal.ofReal (9 * c ^ 2) * ‖tripleB g3 i (update x i z i) (update x i z)‖ₑ ^ 2
            ∂(S.G i x) := by
      intro x
      rw [hG]
      refine (evariance_le_lintegral_sub (S.G i x)
        (hF.comp (measurable_update x)).aestronglyMeasurable (c * tripleRest g3 i x)).trans (le_of_eq ?_)
      refine lintegral_congr fun z => ?_
      have e1 := tripleSum_update g3 hsym i x z
      rw [update_self, tripleB_update]
      simp only [Function.comp]
      rw [e1]
      have : c * (3 * tripleB g3 i z x + tripleRest g3 i x) - c * tripleRest g3 i x
          = (3 * c) * tripleB g3 i z x := by ring
      rw [this, enorm_sq_mul_real]
      ring_nf
    calc _ ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal (9 * c ^ 2) *
            ‖tripleB g3 i (update x i z i) (update x i z)‖ₑ ^ 2 ∂(S.G i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := lintegral_mono hpt
      _ = ∫⁻ Y, ENNReal.ofReal (9 * c ^ 2) * ‖tripleB g3 i (Y i) Y‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
        rw [← hSP]
        exact S.invariant i (fun Y => ENNReal.ofReal (9 * c ^ 2) * ‖tripleB g3 i (Y i) Y‖ₑ ^ 2)
          (measurable_const.mul (hrow.enorm.pow_const 2))
      _ = _ := by
        rw [lintegral_const_mul _ (hrow.enorm.pow_const 2)]
  calc 2 * ∑ i, ∫⁻ x, evariance (fun z => c * tripleSum g3 (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ 2 * ∑ i : Fin N, (ENNReal.ofReal (9 * c ^ 2) * ∫⁻ Y, ‖tripleB g3 i (Y i) Y‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))) := by
        gcongr with i _
        exact hper i
    _ = _ := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rw [show (18 : ℝ) * c ^ 2 = 2 * (9 * c ^ 2) by ring, ENNReal.ofReal_mul (by norm_num)]
        simp

end TripleWu

section Pole2

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- **Two retained poles**: for `z ≠ x`, `z ≠ u`,
`M' + βγ + ψ_{x,u}(z) ≤ M₀ + β C_q - λ g_+(x-z) - λ g_+(u-z)`. -/
theorem pole2_exponent_le {s c Mmax M'max γmax Cq : ℝ} {V : WeakPotential μ}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β lam : ℝ} (hβ : 0 ≤ β) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ β) (hCq : 0 ≤ Cq) (x u z : Torus d) (hzx : z ≠ x) (hzu : z ≠ u) :
    V.M' + β * V.γ + pinField V lam (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z ≤
      (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq)) - lam * gPlus d s c (x - z) -
        lam * gPlus d s c (u - z) := by
  rw [pinField_pinsWith, pinField_pinsWith, HRS.External.RefMarg.pinField_empty]
  have h2 := V.φ_le z
  have h3 := hV.hq z x hzx
  have h3' := hV.hq z u hzu
  have e1 : gPlus d s c (z - x) = gPlus d s c (x - z) := by rw [← neg_sub x z, gPlus_neg]
  have e2 : gPlus d s c (z - u) = gPlus d s c (u - z) := by rw [← neg_sub u z, gPlus_neg]
  rw [e1] at h3
  rw [e2] at h3'
  have h4 : β * V.γ ≤ β * max γmax 0 := mul_le_mul_of_nonneg_left (hV.hγ.trans (le_max_left _ _)) hβ
  have h5 : lam * Cq ≤ β * Cq := mul_le_mul_of_nonneg_right hlam hCq
  have h6 : lam * (gPlus d s c (x - z) - Cq) ≤ lam * V.q z x := mul_le_mul_of_nonneg_left h3 hlam0
  have h6' : lam * (gPlus d s c (u - z) - Cq) ≤ lam * V.q z u := mul_le_mul_of_nonneg_left h3' hlam0
  have := hV.hM'
  have := hV.hM
  nlinarith

theorem lintegral_pole2_le {s c Mmax M'max γmax Cq : ℝ} {V : WeakPotential μ}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β lam : ℝ} (hβ : 0 ≤ β) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ β) (hCq : 0 ≤ Cq) {x u : Torus d} (hatom : ∀ z : Torus d, μ {z} = 0)
    (F : Torus d → ℝ≥0∞) :
    ∫⁻ z, F z * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V lam (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z)) ∂μ ≤
      ENNReal.ofReal (Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq))) *
        ∫⁻ z, F z * ENNReal.ofReal (Real.exp (-lam * gPlus d s c (x - z))) *
          ENNReal.ofReal (Real.exp (-lam * gPlus d s c (u - z))) ∂μ := by
  have hae : ∀ᵐ z ∂μ, z ≠ x ∧ z ≠ u :=
    (HRS.External.PoleVar.ae_ne_pt hatom x).and (HRS.External.PoleVar.ae_ne_pt hatom u)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with z hz
  have h := pole2_exponent_le hV hβ hlam0 hlam hCq x u z hz.1 hz.2
  calc F z * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V lam (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z))
      ≤ F z * (ENNReal.ofReal (Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq))) *
          (ENNReal.ofReal (Real.exp (-lam * gPlus d s c (x - z))) *
            ENNReal.ofReal (Real.exp (-lam * gPlus d s c (u - z))))) := by
        refine mul_le_mul' le_rfl ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
    _ = _ := by ring

end Pole2

section RowMeanPins

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- **Mean of a row under a pinned ensemble** via the signed tower property:
`|E_{R^a} ∑_{j≠i} h(x_i,x_j)| ≤ ∫ pinWeight(u) 𝓜(u) μ(du) ≤ ∫ 𝓜 e^{pole} dμ`. -/
theorem abs_integral_row_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N m : ℕ} [NeZero m] (hN0 : 0 < N)
    (hN : m + 1 + Fintype.card B ≤ N) (a : B → Torus d) {h : Torus d → Torus d → ℝ}
    (hm : Measurable (Function.uncurry h)) (i : Fin (m + 1))
    (hint : Integrable (fun Y : Fin (m + 1) → Torus d => ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j))
      (pinnedLaw V (β / N) (m + 1) a))
    {𝓜 : Torus d → ℝ} (h𝓜m : Measurable 𝓜) (h𝓜0 : ∀ u, 0 ≤ 𝓜 u)
    (hfπ : ∀ᵐ u ∂μ, ∀ k : Fin m, Integrable (h u) ((pinnedLaw V (β / N) m (pinsWith a u)).map
      (fun Y => Y k)))
    (hM : ∀ᵐ u ∂μ, |∑ k : Fin m, ∫ z, h u z ∂((pinnedLaw V (β / N) m (pinsWith a u)).map
        (fun Y => Y k))| ≤ 𝓜 u) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∫⁻ u, ENNReal.ofReal (𝓜 u) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / N) a u)) ∂μ ≤ ENNReal.ofReal W) :
    |∫ Y, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) ∂(pinnedLaw V (β / N) (m + 1) a)| ≤ W := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hΦ : Measurable fun Y : Fin (m + 1) → Torus d => ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) :=
    measurable_rowSum hm i
  rw [integral_pinned_succ V hlam a i hΦ hint]
  have hwint : ∫⁻ u, pinWeight V (β / N) a m u ∂μ = 1 := lintegral_pinWeight V hlam a i (0 : Fin m)
  have hrow : ∀ u : Torus d, ∀ y : Fin m → Torus d, ∑ j ∈ Finset.univ.erase i, h (insertAt i u y i) (insertAt i u y j)
      = ∑ k, h u (y k) := by
    intro u y
    rw [insertAt_same, sum_erase_insertAt i u y (fun z => h u z)]
  have hinner : ∀ᵐ u ∂μ, |∫ y, ∑ j ∈ Finset.univ.erase i, h (insertAt i u y i) (insertAt i u y j)
      ∂(pinnedLaw V (β / N) m (pinsWith a u))| ≤ 𝓜 u := by
    filter_upwards [hfπ, hM] with u hu hMu
    simp_rw [hrow]
    have hP := isProb_pinnedLaw V hlam m (pinsWith a u)
    have : ∫ y, ∑ k, h u (y k) ∂(pinnedLaw V (β / N) m (pinsWith a u)) =
        ∑ k : Fin m, ∫ z, h u z ∂((pinnedLaw V (β / N) m (pinsWith a u)).map (fun Y => Y k)) := by
      have hi : ∀ k : Fin m, Integrable (fun y : Fin m → Torus d => h u (y k))
          (pinnedLaw V (β / N) m (pinsWith a u)) := by
        intro k
        exact (integrable_map_measure (measurable_h_x hm u).aestronglyMeasurable
          (measurable_pi_apply k).aemeasurable).1 (hu k)
      rw [integral_finsetSum _ fun k _ => hi k]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_map (measurable_pi_apply k).aemeasurable (measurable_h_x hm u).aestronglyMeasurable]
    rw [this]; exact hMu
  have hwae : ∀ᵐ u ∂μ, pinWeight V (β / N) a m u < ⊤ := by
    exact pinWeight_ae_lt_top V hlam a i
  have h1 := norm_integral_le_lintegral_norm (μ := μ) (fun x => (pinWeight V (β / N) a m x).toReal *
    ∫ y, ∑ j ∈ Finset.univ.erase i, h (insertAt i x y i) (insertAt i x y j)
      ∂(pinnedLaw V (β / N) m (pinsWith a x)))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_le_of_le_ofReal hW0 ?_)
  have hΨ : Measurable fun u => ENNReal.ofReal (𝓜 u) := ENNReal.measurable_ofReal.comp h𝓜m
  refine le_trans (lintegral_mono_ae ?_) (le_trans (lintegral_pinWeight_le V hβ hN0 hN a hΨ) hW)
  filter_upwards [hwae, hinner] with u hwu hiu
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hwu.ne]
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hiu)

end RowMeanPins

end HRS.PairMom

end
