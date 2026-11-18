import HRS.PDE.MeanFieldPairInverse
import HRS.PDE.MeanFieldAdjointSmoothingLow
import HRS.PDE.MeanFieldAdjointDuhamel
import HRS.PDE.MeanFieldLocalB

/-!
# Packet PX7, file A: the one-variable operator on `H^m` coefficient sequences

`T τ = centerC ρ ∘ frozenCoeff D ρ m` is the complex-linear extension to all of `H^m` of the
coefficient form `x ↦ centerCoeff ρ (frozenCoeff ..)` of the equilibrium semigroup `S τ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.PX7

open HRS.PDE.MFAdjoint

variable {d : ℕ}

/-- The complex-linear mean functional `c ↦ ∑ conj(ρ̂ k) c k` (agrees with `meanCoeff` on real
coefficient sequences). -/
def px7_mC (ρ : Torus d → ℝ) (c : Coeff d) : ℂ := ∑' k, conj (coeffOf ρ k) * c k

/-- Complex-linear centering. -/
def px7_centerC (ρ : Torus d → ℝ) (c : Coeff d) : Coeff d :=
  fun k => c k - px7_mC ρ c * deltaCoeff 0 k

theorem px7_summable_mC {ρ : Torus d → ℝ} (hρ : MemHs 0 (coeffOf ρ)) {c : Coeff d}
    (hc : MemHs 0 c) : Summable fun k => conj (coeffOf ρ k) * c k := by
  have h1 : MemHs 0 (fun k => conj (coeffOf ρ k)) := by
    unfold MemHs at *
    simpa using hρ
  have := MFAdjoint.summable_meanTerm (a := fun k => conj (coeffOf ρ k)) (c := fun k => conj (c k)) h1
    (by unfold MemHs at *; simpa using hc)
  refine this.congr fun k => ?_
  simp [sobWeight_zero]

theorem px7_mC_add {ρ : Torus d → ℝ} (hρ : MemHs 0 (coeffOf ρ)) {x y : Coeff d}
    (hx : MemHs 0 x) (hy : MemHs 0 y) : px7_mC ρ (x + y) = px7_mC ρ x + px7_mC ρ y := by
  unfold px7_mC
  rw [← Summable.tsum_add (px7_summable_mC hρ hx) (px7_summable_mC hρ hy)]
  exact tsum_congr fun k => by simp [mul_add]

theorem px7_mC_smul (ρ : Torus d → ℝ) (a : ℂ) (c : Coeff d) :
    px7_mC ρ (a • c) = a * px7_mC ρ c := by
  unfold px7_mC
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by simp [mul_left_comm]

theorem px7_mC_zero_delta {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (z : ℂ) :
    px7_mC ρ (z • deltaCoeff (0 : Lattice d)) = z := by
  rw [px7_mC_smul]
  unfold px7_mC
  rw [tsum_eq_single (0 : Lattice d)]
  · have h := MFAdjoint.coeffOf_zero_prob hρ
    have h2 : coeffOf ρ 0 = 1 := by
      apply Complex.ext
      · simpa using h
      · have : (coeffOf ρ 0).im = 0 := by
          rw [MFApriori.coeffOf_zero_eq_integral']; simp
        simpa using this
    simp [deltaCoeff, h2]
  · intro k hk; simp [deltaCoeff, hk]


theorem px7_mC_real {ρ : Torus d → ℝ} (hρr : IsRealCoeff (coeffOf ρ)) {c : Coeff d}
    (hc : IsRealCoeff c) : conj (px7_mC ρ c) = px7_mC ρ c := by
  unfold px7_mC
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Lattice d)).tsum_eq (fun k => conj (coeffOf ρ k) * c k)]
  refine tsum_congr fun k => ?_
  simp only [map_mul, Complex.conj_conj, Equiv.neg_apply]
  rw [hρr k, hc k]
  simp

theorem px7_meanCoeff_eq {ρ : Torus d → ℝ} (hρr : IsRealCoeff (coeffOf ρ)) {c : Coeff d}
    (hc : IsRealCoeff c) : (meanCoeff ρ c : ℂ) = px7_mC ρ c := by
  have h1 : conj (px7_mC ρ c) = hsInner 0 (coeffOf ρ) c := by
    unfold px7_mC hsInner
    rw [Complex.conj_tsum]
    refine tsum_congr fun k => ?_
    rw [sobWeight_zero]; simp
  have h2 := px7_mC_real hρr hc
  have h3 : meanCoeff ρ c = (px7_mC ρ c).re := by
    unfold meanCoeff
    rw [← h1, Complex.conj_re]
  rw [h3]
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h2
    simp at this
    simp
    linarith

theorem px7_centerC_eq {ρ : Torus d → ℝ} (hρr : IsRealCoeff (coeffOf ρ)) {c : Coeff d}
    (hc : IsRealCoeff c) : px7_centerC ρ c = centerCoeff ρ c := by
  funext k
  simp only [px7_centerC, centerCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [px7_meanCoeff_eq hρr hc]

theorem px7_centerC_add {ρ : Torus d → ℝ} (hρ : MemHs 0 (coeffOf ρ)) {x y : Coeff d}
    (hx : MemHs 0 x) (hy : MemHs 0 y) :
    px7_centerC ρ (x + y) = px7_centerC ρ x + px7_centerC ρ y := by
  funext k
  simp only [px7_centerC, Pi.add_apply]
  rw [px7_mC_add hρ hx hy]; ring

theorem px7_centerC_smul (ρ : Torus d → ℝ) (a : ℂ) (c : Coeff d) :
    px7_centerC ρ (a • c) = a • px7_centerC ρ c := by
  funext k
  simp only [px7_centerC, Pi.smul_apply, smul_eq_mul]
  rw [px7_mC_smul]; ring

theorem px7_mC_centerC {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ0 : MemHs 0 (coeffOf ρ))
    {c : Coeff d} (hc : MemHs 0 c) : px7_mC ρ (px7_centerC ρ c) = 0 := by
  have e : px7_centerC ρ c = c - px7_mC ρ c • deltaCoeff (0 : Lattice d) := by
    funext k; simp [px7_centerC]
  have hδ : MemHs 0 (px7_mC ρ c • deltaCoeff (0 : Lattice d)) := MFAdjoint.memHs_smul_delta 0 _
  have hneg : MemHs 0 (-(px7_mC ρ c • deltaCoeff (0 : Lattice d))) := by
    have := MFAdjoint.memHs_smul_coeff hδ (-1 : ℂ)
    simpa using this
  have e2 : px7_centerC ρ c = c + -(px7_mC ρ c • deltaCoeff (0 : Lattice d)) := by
    rw [e]; funext k; simp [sub_eq_add_neg]
  rw [e2, px7_mC_add hρ0 hc hneg]
  have : px7_mC ρ (-(px7_mC ρ c • deltaCoeff (0 : Lattice d))) = -px7_mC ρ c := by
    have := px7_mC_smul ρ (-1 : ℂ) (px7_mC ρ c • deltaCoeff (0 : Lattice d))
    rw [px7_mC_zero_delta hρ] at this
    simpa using this
  rw [this]; ring

theorem px7_centerC_idem {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ0 : MemHs 0 (coeffOf ρ))
    {c : Coeff d} (hc : MemHs 0 c) : px7_centerC ρ (px7_centerC ρ c) = px7_centerC ρ c := by
  funext k
  have := px7_mC_centerC hρ hρ0 hc
  simp only [px7_centerC] at this ⊢
  rw [this]; ring

theorem px7_centerC_delta {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (z : ℂ) :
    px7_centerC ρ (z • deltaCoeff (0 : Lattice d)) = 0 := by
  funext k
  simp only [px7_centerC]
  rw [px7_mC_zero_delta hρ]
  simp [deltaCoeff]


/-! ### The operator -/

section Oper

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

/-- `T τ = centerC ∘ frozenCoeff` at level `m`. -/
def px7_T (D : DynData d) (ρ : Torus d → ℝ) (m : ℕ) (τ : ℝ) (c : Coeff d) : Coeff d :=
  px7_centerC ρ (frozenCoeff D ρ m c τ)

theorem px7_frozen_mem (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {c : Coeff d} (hc : MemHs (m : ℝ) c) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    MemHs (m : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ m c τ) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm1 : 1 ≤ m := by omega
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  exact ((exists_frozenCoeff_bound (d := d) (s := s) (m := m) hd H.hs0 H.hsd hm1
    (frozenRegime d s c₀) 1 Λ₀ Λ₀).choose_spec.2 _ 0 (τ + 1) ρ hA c hc τ ⟨hτ, by linarith⟩).1

theorem px7_memHs_centerC (ρ : Torus d → ℝ) {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (px7_centerC ρ c) := by
  have e : px7_centerC ρ c = c - px7_mC ρ c • deltaCoeff (0 : Lattice d) := by
    funext k; simp [px7_centerC]
  rw [e]
  exact memHs_sub hc (memHs_smul_delta m _)

theorem px7_T_mem (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {c : Coeff d} (hc : MemHs (m : ℝ) c) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    MemHs (m : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ c) :=
  px7_memHs_centerC ρ (px7_frozen_mem hd m hm H hc hτ)

theorem px7_T_add (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x y : Coeff d} (hx : MemHs (m : ℝ) x)
    (hy : MemHs (m : ℝ) y) {τ : ℝ} (hτ : 0 ≤ τ) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ (x + y) =
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x +
        px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ y := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm1 : 1 ≤ m := by omega
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega))
  unfold px7_T
  have := MFPair.frozenCoeff_add_aux hd s H.hs0 H.hsd m hm1 _ 1 Λ₀ Λ₀ _ 0 (τ + 1) ρ hA hx hy
    (τ := τ) ⟨hτ, by linarith⟩
  have e : (x + y) = fun k => x k + y k := rfl
  rw [e, this]
  exact px7_centerC_add hρ0 ((px7_frozen_mem hd m hm H hx hτ).mono (by positivity))
    ((px7_frozen_mem hd m hm H hy hτ).mono (by positivity))

theorem px7_T_smul (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d} (hx : MemHs (m : ℝ) x) (a : ℂ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ (a • x) =
      a • px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm1 : 1 ≤ m := by omega
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  unfold px7_T
  rw [frozenCoeff_smul hd H.hs0 H.hsd hm1 hA hx a ⟨hτ, by linarith⟩, px7_centerC_smul]

end Oper


section Oper2

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

theorem px7_centerC_sub_delta {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ0 : MemHs 0 (coeffOf ρ))
    {w : Coeff d} (hw : MemHs 0 w) (z : ℂ) :
    px7_centerC ρ (w - z • deltaCoeff (0 : Lattice d)) = px7_centerC ρ w := by
  have hδ : MemHs 0 ((-z) • deltaCoeff (0 : Lattice d)) := memHs_smul_delta 0 _
  have e : w - z • deltaCoeff (0 : Lattice d) = w + (-z) • deltaCoeff (0 : Lattice d) := by
    funext k; simp [sub_eq_add_neg]
  rw [e, px7_centerC_add hρ0 hw hδ, px7_centerC_delta hρ]
  simp

theorem px7_T_centerC (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {y : Coeff d} (hy : MemHs (m : ℝ) y) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ (px7_centerC ρ y) =
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ y := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm1 : 1 ≤ m := by omega
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  have hρ : IsProbDensity ρ := H.thermal.1
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega))
  have e : px7_centerC ρ y = y - px7_mC ρ y • deltaCoeff (0 : Lattice d) := by
    funext k; simp [px7_centerC]
  have hδ : MemHs (m : ℝ) (px7_mC ρ y • deltaCoeff (0 : Lattice d)) := memHs_smul_delta _ _
  unfold px7_T
  rw [e, frozenCoeff_sub_aux hd H.hs0 H.hsd hm1 hA hy hδ ⟨hτ, by linarith⟩,
    frozenCoeff_const_delta hd H.hs0 H.hsd hm1 hA _ ⟨hτ, by linarith⟩]
  exact px7_centerC_sub_delta hρ hρ0 ((px7_frozen_mem hd m hm H hy hτ).mono (by positivity)) _

theorem px7_T_zero (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d} (hx : MemHs (m : ℝ) x) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m 0 x = px7_centerC ρ x := by
  have h3 := ClassicalPart.three_le_mStar d
  unfold px7_T
  rw [frozenCoeff_zero (by omega) hx]

theorem px7_T_semigroup (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d} (hx : MemHs (m : ℝ) x) {σ τ : ℝ}
    (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m (σ + τ) x =
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m σ
        (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm1 : 1 ≤ m := by omega
  have hA := adjointData_frozen_level m H 0 (σ + τ + 1) (by linarith)
  have hmem := px7_frozen_mem hd m hm H hx hτ
  have e1 : px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m σ
        (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) =
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m σ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ m x τ) := by
    show px7_T _ ρ m σ (px7_centerC ρ (frozenCoeff _ ρ m x τ)) = _
    exact px7_T_centerC hd m hm H hmem hσ
  rw [e1]
  obtain ⟨-, hsh⟩ := frozenCoeff_shift hd H.hs0 H.hsd hm1 hA hx hτ hσ (by linarith)
  unfold px7_T
  rw [hsh, show σ + τ = τ + σ from add_comm _ _]

end Oper2


section Oper3

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

theorem px7_T_const (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) (z : ℂ) {τ : ℝ} (hτ : 0 ≤ τ) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ (z • deltaCoeff (0 : Lattice d)) = 0 := by
  have h3 := ClassicalPart.three_le_mStar d
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  unfold px7_T
  rw [frozenCoeff_const_delta hd H.hs0 H.hsd (by omega) hA _ ⟨hτ, by linarith⟩]
  exact px7_centerC_delta H.thermal.1 z

theorem px7_T_real (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d} (hx : MemHs (m : ℝ) x)
    (hre : IsRealCoeff x) {τ : ℝ} (hτ : 0 ≤ τ) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x =
      centerCoeff ρ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ m x τ) ∧
    IsRealCoeff (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm1 : 1 ≤ m := by omega
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  have hfr := frozenCoeff_real hd H.hs0 H.hsd hm1 hA hx hre (τ := τ) ⟨hτ, by linarith⟩
  have hρr : IsRealCoeff (coeffOf ρ) :=
    isRealCoeff_coeffOf ρ (MFAdjoint.integrable_of_cont (H.cont (by omega)))
  have e : px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x =
      centerCoeff ρ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ m x τ) :=
    px7_centerC_eq hρr hfr
  exact ⟨e, by rw [e]; exact centerCoeff_isReal hfr⟩

theorem px7_T_mean (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d} (hx : MemHs (m : ℝ) x)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    px7_mC ρ (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) = 0 := by
  have h3 := ClassicalPart.three_le_mStar d
  exact px7_mC_centerC H.thermal.1 (MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega)))
    ((px7_frozen_mem hd m hm H hx hτ).mono (by positivity))

/-- The equilibrium semigroup in coefficient form. -/
theorem px7_S_eq (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {ψ : Torus d → ℝ} (hψc : Continuous ψ)
    (hψ : MemSobolev (m : ℝ) ψ) {τ : ℝ} (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρ τ ψ =
      toFun (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ (coeffOf ψ)) := by
  obtain ⟨hcm, hre, -⟩ := coeff_data m hm hψc hψ
  rw [(px7_T_real hd m hm H hcm hre hτ).1]
  exact (S_eq hd m hm H hψc hψ hτ).1

end Oper3


/-! ### Real and imaginary parts of coefficient sequences -/

section Parts

/-- `(c + c̃)/2`, `c̃ k = conj (c (-k))`. -/
def px7_reP (c : Coeff d) : Coeff d := fun k => (c k + conj (c (-k))) / 2

/-- `(c - c̃)/(2i)`. -/
def px7_imP (c : Coeff d) : Coeff d := fun k => (c k - conj (c (-k))) * (-Complex.I / 2)

theorem px7_reP_real (c : Coeff d) : IsRealCoeff (px7_reP c) := by
  intro k
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [px7_reP, neg_neg, map_div₀, map_add, Complex.conj_conj, h2]
  rw [add_comm]

theorem px7_imP_real (c : Coeff d) : IsRealCoeff (px7_imP c) := by
  intro k
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [px7_imP, neg_neg, map_mul, map_sub, Complex.conj_conj, map_div₀, map_neg,
    Complex.conj_I, h2]
  ring

theorem px7_split (c : Coeff d) : c = fun k => px7_reP c k + Complex.I * px7_imP c k := by
  funext k
  simp only [px7_reP, px7_imP]
  linear_combination ((c k - conj (c (-k))) / 2) * Complex.I_sq

theorem px7_hs_refl {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (reflConj c) ∧ hsNorm m (reflConj c) = hsNorm m c := by
  refine ⟨ClassicalPart.memHs_reflConj hc, ?_⟩
  unfold hsNorm hsNormSq
  congr 1
  rw [← (Equiv.neg (Lattice d)).tsum_eq]
  refine tsum_congr fun k => ?_
  simp [reflConj, sobWeight_neg]

theorem px7_hs_reP {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (px7_reP c) ∧ hsNorm m (px7_reP c) ≤ hsNorm m c := by
  obtain ⟨h1, h2⟩ := px7_hs_refl hc
  obtain ⟨h3, h4⟩ := hs_add_le m hc h1
  have e : px7_reP c = fun k => (1 / 2 : ℂ) * (c k + reflConj c k) := by
    funext k; simp [px7_reP, reflConj]; ring
  rw [e]
  refine ⟨MFThermalReg.memHs_smul h3 _, ?_⟩
  rw [MFThermalReg.hsNorm_smul]
  norm_num
  rw [h2] at h4
  linarith

theorem px7_hs_imP {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (px7_imP c) ∧ hsNorm m (px7_imP c) ≤ hsNorm m c := by
  obtain ⟨h1, h2⟩ := px7_hs_refl hc
  obtain ⟨h1', h2'⟩ := hs_neg h1
  obtain ⟨h3, h4⟩ := hs_add_le m hc h1'
  have e : px7_imP c = fun k => (-Complex.I / 2 : ℂ) * (c k + -reflConj c k) := by
    funext k; simp [px7_imP, reflConj]; ring
  rw [e]
  refine ⟨MFThermalReg.memHs_smul h3 _, ?_⟩
  rw [MFThermalReg.hsNorm_smul]
  have hn : ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hn]
  rw [h2] at h2'
  linarith

end Parts


/-! ### Decay on `H^j` -/

section Decay

theorem px7_decay_real (hd : 1 ≤ d) (s : ℝ) (m j : ℕ) (hm : mStar d + 2 ≤ m) (hmj : m ≤ j)
    (hj : (d : ℝ) / 2 + 4 < j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d + 3) νm νp c₀ Λ₀ β V ρ) (x : Coeff d), IsRealCoeff x →
      MemHs (j : ℝ) x → ∀ τ : ℝ, 0 ≤ τ →
        MemHs (j : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) ∧
        hsNorm (j : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) ≤
          C * Real.exp (-c * τ) * hsNorm (j : ℝ) x := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hdec⟩ := exists_frozen_hj_decay' hd s j hj νm νp c₀ Λ₀
  refine ⟨C₁ * (2 * (1 + |Λ₀|)), c₁, by positivity, hc₁, ?_⟩
  intro β V ρ H x hre hx τ hτ
  have h3 := ClassicalPart.three_le_mStar d
  have Hj : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hj3 : FrozenHyp d s (j + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hjm : mStar d + 2 ≤ j := by omega
  have hdj : (d : ℝ) / 2 < j := by linarith [(by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)]
  have hmjR : (m : ℝ) ≤ j := by exact_mod_cast hmj
  have hs := summable_norm_of_memHs (j : ℝ) hdj x hx
  have hψc : Continuous (toFun x) := MFPair.continuous_toFun' x hs
  have hco : coeffOf (toFun x) = x := coeffOf_toFun x hre hs
  have hψj : MemSobolev (j : ℝ) (toFun x) := (ClassicalPart.memSobolev_toFun hs hx hre).1
  have hψm : MemSobolev (m : ℝ) (toFun x) :=
    (ClassicalPart.memSobolev_toFun hs (hx.mono hmjR) hre).1
  obtain ⟨hmem, hnorm⟩ := hdec β V ρ Hj (toFun x) hψc hψj τ hτ
  have hSeq := px7_S_eq hd m hm Hm hψc hψm hτ
  rw [hco] at hSeq
  have hρ : IsProbDensity ρ := H.thermal.1
  have hρc : Continuous ρ := H.cont (by omega)
  -- the level-`j` frozen path
  have hA_m := adjointData_frozen_level m Hm 0 (τ + 1) (by linarith)
  have hA_j := adjointData_frozen_level j Hj3 0 (τ + 1) (by linarith)
  have hlev : frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ m x τ =
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ j x τ :=
    frozenCoeff_level hd H.hs0 H.hsd (by omega) hmj hA_m hA_j hx ⟨hτ, by linarith⟩
  have hTe := (px7_T_real hd m hm Hm (hx.mono hmjR) hre hτ).1
  have hfj := px7_frozen_mem hd j hjm Hj3 hx hτ
  obtain ⟨hSj1, hSj2⟩ := S_facts' hd s H.hs0 H.hsd j hjm Hj hψc hψj hτ (j : ℝ) (by positivity) le_rfl
  rw [hco] at hSj2
  obtain ⟨hPj1, hPj2⟩ := P_facts' hd s H.hs0 H.hsd j hjm Hj hψc hψj (j : ℝ) (by positivity) le_rfl
  rw [hco] at hPj2
  have hTn : hsNorm (j : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) =
      sobolevNorm (j : ℝ) (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρ τ (toFun x)) := by
    rw [hSj2, hTe, hlev]
  have hTm : MemHs (j : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) := by
    have : px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x =
        px7_centerC ρ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ j x τ) := by
      unfold px7_T; rw [hlev]
    rw [this]
    exact px7_memHs_centerC ρ hfj
  refine ⟨hTm, ?_⟩
  rw [hTn]
  refine hnorm.trans ?_
  rw [hPj2]
  obtain ⟨-, hcb⟩ := centerCoeff_bound' hρ hρc (Λ₀ := Λ₀) H.le_Lam (i := (j : ℝ)) (by positivity) hx
  have hb : 2 * (1 + Λ₀) ≤ 2 * (1 + |Λ₀|) := by linarith [le_abs_self Λ₀]
  have h0 := hsNorm_nonneg' (j : ℝ) x
  have hE := (Real.exp_pos (-c₁ * τ)).le
  calc C₁ * Real.exp (-c₁ * τ) * hsNorm (j : ℝ) (centerCoeff ρ x)
      ≤ C₁ * Real.exp (-c₁ * τ) * (2 * (1 + |Λ₀|) * hsNorm (j : ℝ) x) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine hcb.trans ?_
        exact mul_le_mul_of_nonneg_right hb h0
    _ = _ := by ring

end Decay


section Decay2

theorem px7_decay (hd : 1 ≤ d) (s : ℝ) (m j : ℕ) (hm : mStar d + 2 ≤ m) (hmj : m ≤ j)
    (hj : (d : ℝ) / 2 + 4 < j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d + 3) νm νp c₀ Λ₀ β V ρ) (x : Coeff d),
      MemHs (j : ℝ) x → ∀ τ : ℝ, 0 ≤ τ →
        MemHs (j : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) ∧
        hsNorm (j : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) ≤
          C * Real.exp (-c * τ) * hsNorm (j : ℝ) x := by
  obtain ⟨C, c, hC, hc, hdec⟩ := px7_decay_real hd s m j hm hmj hj νm νp c₀ Λ₀
  refine ⟨2 * C, c, by positivity, hc, ?_⟩
  intro β V ρ H x hx τ hτ
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hmjR : (m : ℝ) ≤ j := by exact_mod_cast hmj
  obtain ⟨ha, ha'⟩ := px7_hs_reP hx
  obtain ⟨hb, hb'⟩ := px7_hs_imP hx
  obtain ⟨hTa, hTa'⟩ := hdec β V ρ H _ (px7_reP_real x) ha τ hτ
  obtain ⟨hTb, hTb'⟩ := hdec β V ρ H _ (px7_imP_real x) hb τ hτ
  set T' := px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ with hT'
  have hsplit : x = px7_reP x + Complex.I • px7_imP x := by
    funext k
    have := congrFun (px7_split x) k
    simpa using this
  have hTx : T' x = T' (px7_reP x) + Complex.I • T' (px7_imP x) := by
    conv_lhs => rw [hsplit]
    rw [hT', px7_T_add hd m hm Hm (ha.mono hmjR) (MFAdjoint.memHs_smul_coeff (hb.mono hmjR) _) hτ,
      px7_T_smul hd m hm Hm (hb.mono hmjR) _ hτ]
  have hiT : MemHs (j : ℝ) (Complex.I • T' (px7_imP x)) := MFAdjoint.memHs_smul_coeff hTb _
  have hadd := hs_add_le (j : ℝ) hTa hiT
  have hn : hsNorm (j : ℝ) (Complex.I • T' (px7_imP x)) = hsNorm (j : ℝ) (T' (px7_imP x)) := by
    have := MFThermalReg.hsNorm_smul (j : ℝ) Complex.I (T' (px7_imP x))
    rw [Complex.norm_I, one_mul] at this
    exact this
  have hE := (Real.exp_pos (-c * τ)).le
  have hTx' : T' x = fun k => T' (px7_reP x) k + (Complex.I • T' (px7_imP x)) k := hTx
  rw [hTx']
  refine ⟨hadd.1, hadd.2.trans ?_⟩
  rw [hn]
  have h1 : C * Real.exp (-c * τ) * hsNorm (j : ℝ) (px7_reP x) ≤ C * Real.exp (-c * τ) * hsNorm (j : ℝ) x :=
    mul_le_mul_of_nonneg_left ha' (by positivity)
  have h2 : C * Real.exp (-c * τ) * hsNorm (j : ℝ) (px7_imP x) ≤ C * Real.exp (-c * τ) * hsNorm (j : ℝ) x :=
    mul_le_mul_of_nonneg_left hb' (by positivity)
  linarith

end Decay2


/-! ### Strong continuity -/

section Cont

theorem px7_centerC_sub {ρ : Torus d → ℝ} (hρ : MemHs 0 (coeffOf ρ)) {a b : Coeff d}
    (ha : MemHs 0 a) (hb : MemHs 0 b) :
    px7_centerC ρ (a - b) = px7_centerC ρ a - px7_centerC ρ b := by
  have hb' : MemHs 0 ((-1 : ℂ) • b) := MFAdjoint.memHs_smul_coeff hb _
  have e : a - b = a + (-1 : ℂ) • b := by funext k; simp [sub_eq_add_neg]
  rw [e, px7_centerC_add hρ ha hb', px7_centerC_smul]
  funext k; simp [sub_eq_add_neg]

theorem px7_abs_mC_le {ρ : Torus d → ℝ} (hρ : MemHs 0 (coeffOf ρ)) {c : Coeff d} (hc : MemHs 0 c) :
    ‖px7_mC ρ c‖ ≤ hsNorm 0 (coeffOf ρ) * hsNorm 0 c := by
  have hρ2 : Summable fun k => (‖coeffOf ρ k‖) ^ 2 := (memHs_zero_iff _).mp hρ
  have hc2 : Summable fun k => (‖c k‖) ^ 2 := (memHs_zero_iff _).mp hc
  obtain ⟨hs, hle⟩ := Torus.cs_tsum (fun k => ‖coeffOf ρ k‖) (fun k => ‖c k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hρ2 hc2
  have hsN : Summable fun k => ‖conj (coeffOf ρ k) * c k‖ := hs.congr fun k => by simp
  unfold px7_mC
  refine (norm_tsum_le_tsum_norm hsN).trans ?_
  have e : ∑' k, ‖conj (coeffOf ρ k) * c k‖ = ∑' k, ‖coeffOf ρ k‖ * ‖c k‖ :=
    tsum_congr fun k => by simp
  rw [e]
  refine hle.trans (le_of_eq ?_)
  have h1 : hsNorm 0 (coeffOf ρ) = Real.sqrt (∑' k, ‖coeffOf ρ k‖ ^ 2) := by
    unfold hsNorm hsNormSq; simp [sobWeight_zero]
  have h2 : hsNorm 0 c = Real.sqrt (∑' k, ‖c k‖ ^ 2) := by
    unfold hsNorm hsNormSq; simp [sobWeight_zero]
  rw [h1, h2]

theorem px7_hs_centerC {ρ : Torus d → ℝ} (hρ : MemHs 0 (coeffOf ρ)) {m : ℝ} (hm : 0 ≤ m)
    {c : Coeff d} (hc : MemHs m c) :
    MemHs m (px7_centerC ρ c) ∧
      hsNorm m (px7_centerC ρ c) ≤ (1 + hsNorm 0 (coeffOf ρ)) * hsNorm m c := by
  refine ⟨px7_memHs_centerC ρ hc, ?_⟩
  have e : px7_centerC ρ c = c - px7_mC ρ c • deltaCoeff (0 : Lattice d) := by
    funext k; simp [px7_centerC]
  have hδ : MemHs m (px7_mC ρ c • deltaCoeff (0 : Lattice d)) := memHs_smul_delta m _
  have h0 : MemHs 0 c := by
    have := (hs_lower hm hc).1
    simpa using this
  have h0n : hsNorm 0 c ≤ hsNorm m c := by
    have := (hs_lower hm hc).2
    simpa using this
  have hn : hsNorm m (px7_mC ρ c • deltaCoeff (0 : Lattice d)) = ‖px7_mC ρ c‖ := by
    have := MFThermalReg.hsNorm_smul m (px7_mC ρ c) (deltaCoeff (0 : Lattice d))
    have h1 : hsNorm m (deltaCoeff (0 : Lattice d)) = 1 := by
      rw [hsNorm_deltaCoeff]
      have : Lattice.enorm (0 : Lattice d) = 0 := by
        unfold Lattice.enorm Lattice.toEuc
        have : (WithLp.toLp 2 fun i : Fin d => (((0 : Lattice d) i : ℤ) : ℝ)) = (0 : Euc d) := by
          ext i; simp
        rw [this, norm_zero]
      simp [this]
    rw [h1, mul_one] at this
    exact this
  rw [e]
  refine (MFAdjoint.hsNorm_sub_le_add hc hδ).trans ?_
  rw [hn]
  have hm0 := px7_abs_mC_le hρ h0
  have hn0 := hsNorm_nonneg' (0 : ℝ) (coeffOf ρ)
  have hnc := hsNorm_nonneg' m c
  nlinarith [mul_le_mul_of_nonneg_left h0n hn0]

end Cont


section Cont2

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

/-- Continuity of `τ ↦ T τ y` in `H^m` for `y ∈ H^{m+1}`. -/
theorem px7_T_cont_succ (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 1 + 3) νm νp c₀ Λ₀ β V ρ) {y : Coeff d}
    (hy : MemHs ((m + 1 : ℕ) : ℝ) y) {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) :
    Tendsto (fun τ => hsNorm (m : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ y -
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ₀ y)) (𝓝[Set.Ici 0] τ₀) (𝓝 0) := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega))
  have hmR : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hT' : 0 < τ₀ + 1 := by linarith
  have hcont := MFPair.frozen_path_cont_ps hd (m + 1) (by omega) H hy
    (m'' := (m : ℝ)) (by push_cast; linarith) hT'
  have hA_m := adjointData_frozen_level m Hm 0 (τ₀ + 1) hT'
  have hA_m1 := adjointData_frozen_level (m + 1) H 0 (τ₀ + 1) hT'
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hlev : ∀ τ ∈ Set.Icc (0 : ℝ) (τ₀ + 1),
      frozenCoeff D ρ m y τ = frozenCoeff D ρ (m + 1) y τ := fun τ hτ =>
    frozenCoeff_level hd H.hs0 H.hsd (by omega) (by omega) hA_m hA_m1 hy hτ
  set K := 1 + hsNorm 0 (coeffOf ρ) with hKdef
  have hK0 : 0 ≤ K := by have := hsNorm_nonneg' (0 : ℝ) (coeffOf ρ); linarith
  have hc1 := hcont.2 τ₀ ⟨hτ₀, by linarith⟩
  have hnhds : Set.Icc (0 : ℝ) (τ₀ + 1) ∈ 𝓝[Set.Ici 0] τ₀ := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio (τ₀ + 1), isOpen_Iio, by simp, fun τ hτ => ⟨hτ.2, hτ.1.le⟩⟩
  have hc2 : Tendsto (fun τ => hsNorm (m : ℝ)
      (frozenCoeff D ρ (m + 1) y τ - frozenCoeff D ρ (m + 1) y τ₀)) (𝓝[Set.Ici 0] τ₀) (𝓝 0) :=
    hc1.mono_left (nhdsWithin_le_of_mem hnhds)
  have hbound : ∀ᶠ τ in 𝓝[Set.Ici 0] τ₀,
      hsNorm (m : ℝ) (px7_T D ρ m τ y - px7_T D ρ m τ₀ y) ≤
        K * hsNorm (m : ℝ) (frozenCoeff D ρ (m + 1) y τ - frozenCoeff D ρ (m + 1) y τ₀) := by
    filter_upwards [hnhds] with τ hτ
    have hτ₀' : τ₀ ∈ Set.Icc (0 : ℝ) (τ₀ + 1) := ⟨hτ₀, by linarith⟩
    have e : px7_T D ρ m τ y - px7_T D ρ m τ₀ y =
        px7_centerC ρ (frozenCoeff D ρ (m + 1) y τ - frozenCoeff D ρ (m + 1) y τ₀) := by
      have h1 := hcont.1 τ hτ
      have h2 := hcont.1 τ₀ hτ₀'
      rw [px7_centerC_sub hρ0 (h1.mono (by positivity)) (h2.mono (by positivity))]
      unfold px7_T
      rw [hlev τ hτ, hlev τ₀ hτ₀']
    rw [e]
    exact (px7_hs_centerC hρ0 (by positivity) (memHs_sub (hcont.1 τ hτ) (hcont.1 τ₀ hτ₀'))).2
  refine squeeze_zero' (Filter.Eventually.of_forall fun τ => hsNorm_nonneg' _ _) hbound ?_
  simpa using hc2.const_mul K

end Cont2


section Cont3

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

/-- Strong continuity of `T` on `H^m`, given a uniform bound `M`. -/
theorem px7_T_cont (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 1 + 3) νm νp c₀ Λ₀ β V ρ) (M : ℝ)
    (hM : ∀ τ : ℝ, 0 ≤ τ → ∀ y : Coeff d, MemHs (m : ℝ) y →
      hsNorm (m : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ y) ≤ M * hsNorm (m : ℝ) y)
    {x : Coeff d} (hx : MemHs (m : ℝ) x) {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) :
    Tendsto (fun τ => hsNorm (m : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x -
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ₀ x)) (𝓝[Set.Ici 0] τ₀) (𝓝 0) := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hM0 : 0 ≤ M := by
    have := hM 0 le_rfl (deltaCoeff 0) (deltaCoeff_memHs _ _)
    have h1 : 0 ≤ hsNorm (m : ℝ) (px7_T D ρ m 0 (deltaCoeff 0)) := hsNorm_nonneg' _ _
    have h2 : 0 < hsNorm (m : ℝ) (deltaCoeff (0 : Lattice d)) := by
      rw [hsNorm_deltaCoeff]; positivity
    by_contra hneg
    push_neg at hneg
    nlinarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨-, htr⟩ := truncCoeff_tendsto (m : ℝ) x hx
  have hev := (Metric.tendsto_nhds.1 htr) (ε / (4 * (M + 1))) (by positivity)
  obtain ⟨N, hN⟩ := hev.exists
  set xN := truncCoeff N x with hxN
  have hxNm : MemHs ((m + 1 : ℕ) : ℝ) xN := MFLocal.memHs_truncCoeff _ _ _
  have hxNm' : MemHs (m : ℝ) xN := MFLocal.memHs_truncCoeff _ _ _
  have hdm : MemHs (m : ℝ) (x - xN) := memHs_sub hx hxNm'
  have hdn : hsNorm (m : ℝ) (x - xN) < ε / (4 * (M + 1)) := by
    have := hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg' _ _)] at this
    exact this
  have hcN := (Metric.tendsto_nhds.1 (px7_T_cont_succ hd m hm H hxNm hτ₀)) (ε / 2) (by positivity)
  filter_upwards [hcN, self_mem_nhdsWithin] with τ hτ hτ0
  have hτ0' : 0 ≤ τ := hτ0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg' _ _)] at hτ ⊢
  have hadd : ∀ σ : ℝ, 0 ≤ σ → px7_T D ρ m σ x = px7_T D ρ m σ (x - xN) + px7_T D ρ m σ xN := by
    intro σ hσ
    have := px7_T_add hd m hm Hm hdm hxNm' hσ
    have e : (x - xN) + xN = x := by funext k; simp
    rw [e] at this
    exact this
  have e : px7_T D ρ m τ x - px7_T D ρ m τ₀ x =
      (px7_T D ρ m τ (x - xN) - px7_T D ρ m τ₀ (x - xN)) +
        (px7_T D ρ m τ xN - px7_T D ρ m τ₀ xN) := by
    rw [hadd τ hτ0', hadd τ₀ hτ₀]; funext k; simp; ring
  have m1 := px7_T_mem hd m hm Hm hdm hτ0'
  have m2 := px7_T_mem hd m hm Hm hdm hτ₀
  have m3 := px7_T_mem hd m hm Hm hxNm' hτ0'
  have m4 := px7_T_mem hd m hm Hm hxNm' hτ₀
  rw [e]
  have hsum := (MFAdjoint.hs_add_le (m : ℝ) (memHs_sub m1 m2) (memHs_sub m3 m4)).2
  have hA1 := MFAdjoint.hsNorm_sub_le_add m1 m2
  have hB1 := hM τ hτ0' _ hdm
  have hB2 := hM τ₀ hτ₀ _ hdm
  have hn0 := hsNorm_nonneg' (m : ℝ) (x - xN)
  have hMe : M * hsNorm (m : ℝ) (x - xN) ≤ M * (ε / (4 * (M + 1))) :=
    mul_le_mul_of_nonneg_left hdn.le hM0
  have hfrac : M * (ε / (4 * (M + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hsum' : hsNorm (m : ℝ) ((px7_T D ρ m τ (x - xN) - px7_T D ρ m τ₀ (x - xN)) +
    (px7_T D ρ m τ xN - px7_T D ρ m τ₀ xN)) ≤
      hsNorm (m : ℝ) (px7_T D ρ m τ (x - xN) - px7_T D ρ m τ₀ (x - xN)) +
      hsNorm (m : ℝ) (px7_T D ρ m τ xN - px7_T D ρ m τ₀ xN) := hsum
  linarith

end Cont3


/-! ### The generator -/

section Gen

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

/-- `Â = centerC ∘ forwardGen`. -/
def px7_Ah (D : DynData d) (ρ : Torus d → ℝ) (x : Coeff d) : Coeff d :=
  px7_centerC ρ (forwardGen D ρ x)

theorem px7_gen_bound (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x →
      MemHs (m : ℝ) (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) ∧
      hsNorm (m : ℝ) (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) ≤
        K * hsNorm ((m + 2 : ℕ) : ℝ) x := by
  have h3 := ClassicalPart.three_le_mStar d
  have hA := adjointData_frozen_level m H 0 1 one_pos
  obtain ⟨c, hc, h⟩ := forwardGen_hsNorm_le hd H.hs0 H.hsd m 1 Λ₀ Λ₀
    (mfData d s H.hs0 H.hsd V β H.hβ) hA.hs hA.hM hA.hV
  exact ⟨c, hc, fun x hx => h ρ H.thermal.1 H.hρC H.hρb x hx⟩

theorem px7_Ah_bound (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x →
      MemHs (m : ℝ) (px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) ∧
      hsNorm (m : ℝ) (px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) ≤
        K * hsNorm ((m + 2 : ℕ) : ℝ) x := by
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨K, hK, h⟩ := px7_gen_bound hd m hm H
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega))
  refine ⟨(1 + hsNorm 0 (coeffOf ρ)) * K, by have := hsNorm_nonneg' (0 : ℝ) (coeffOf ρ); positivity, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := h x hx
  obtain ⟨h4, h5⟩ := px7_hs_centerC hρ0 (by positivity) h1
  refine ⟨h4, ?_⟩
  unfold px7_Ah
  have := mul_le_mul_of_nonneg_left h2 (by have := hsNorm_nonneg' (0 : ℝ) (coeffOf ρ); positivity :
    (0 : ℝ) ≤ 1 + hsNorm 0 (coeffOf ρ))
  nlinarith

end Gen


section Deriv

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

/-- Right derivative of `τ ↦ T τ x` at `0` for `x ∈ H^{m+2}`. -/
theorem px7_T_deriv (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 2 + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d}
    (hx : MemHs ((m + 2 : ℕ) : ℝ) x) :
    Tendsto (fun h : ℝ => hsNorm (m : ℝ) (fun k =>
      (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m h x k -
        px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m 0 x k) / ((h : ℝ) : ℂ) -
        px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x k)) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega))
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hx' : MemHs (m : ℝ) x := hx.mono hmR
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hA := adjointData_frozen_level m Hm 0 1 one_pos
  have hA2 := adjointData_frozen_level (m + 2) H 0 1 one_pos
  have hq := MFAdjoint.frozen_quot hd H.hs0 H.hsd (by omega : 1 ≤ m) hA hA2 hx
  obtain ⟨K, hK, hbd⟩ := px7_gen_bound hd m hm Hm
  obtain ⟨hfg, -⟩ := hbd x hx
  set K1 := 1 + hsNorm 0 (coeffOf ρ) with hK1def
  have hK10 : 0 ≤ K1 := by have := hsNorm_nonneg' (0 : ℝ) (coeffOf ρ); linarith
  have hbound : ∀ᶠ h in 𝓝[Set.Ioi 0] (0 : ℝ),
      hsNorm (m : ℝ) (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ) -
        px7_Ah D ρ x k) ≤
      K1 * hsNorm (m : ℝ) (fun k => (frozenCoeff D ρ m x h k - x k) / ((h : ℝ) : ℂ) -
        forwardGen D ρ x k) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 ≤ h := le_of_lt hh
    have hF := px7_frozen_mem hd m hm Hm hx' hh0
    set F := frozenCoeff D ρ m x h with hFdef
    set Q : Coeff d := fun k => (F k - x k) / ((h : ℝ) : ℂ) - forwardGen D ρ x k with hQ
    have hQm : MemHs (m : ℝ) Q := by
      have e : Q = ((h : ℝ) : ℂ)⁻¹ • (F - x) - forwardGen D ρ x := by
        funext k; simp [hQ, div_eq_inv_mul]
      rw [e]
      exact memHs_sub (MFAdjoint.memHs_smul_coeff (memHs_sub hF hx') _) hfg
    have e2 : (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ) -
        px7_Ah D ρ x k) = px7_centerC ρ Q := by
      have eQ : Q = ((h : ℝ) : ℂ)⁻¹ • (F - x) - forwardGen D ρ x := by
        funext k; simp [hQ, div_eq_inv_mul]
      rw [eQ, px7_centerC_sub hρ0 ((MFAdjoint.memHs_smul_coeff (memHs_sub hF hx') _).mono (by positivity))
        (hfg.mono (by positivity)), px7_centerC_smul, px7_centerC_sub hρ0 (hF.mono (by positivity))
        (hx'.mono (by positivity))]
      funext k
      simp only [px7_T, px7_Ah, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [frozenCoeff_zero (by omega) hx']
      simp [hFdef, div_eq_inv_mul]
      rfl
    rw [e2]
    exact (px7_hs_centerC hρ0 (by positivity) hQm).2
  refine squeeze_zero' (Filter.Eventually.of_forall fun h => hsNorm_nonneg' _ _) hbound ?_
  simpa using hq.const_mul K1

end Deriv


section Quot

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

/-- Uniform bound of the difference quotients of the frozen path. -/
theorem px7_frozen_quot_bound (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 2 + 3) νm νp c₀ Λ₀ β V ρ) :
    ∃ Kq : ℝ, 0 ≤ Kq ∧ ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x → ∀ h : ℝ, 0 < h → h ≤ 1 →
      MemHs (m : ℝ) (fun k => frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ m x h k - x k) ∧
      hsNorm (m : ℝ) (fun k => frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ m x h k - x k) ≤
        h * (Kq * hsNorm ((m + 2 : ℕ) : ℝ) x) := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hA := adjointData_frozen_level m Hm 0 1 one_pos
  have hA2 := adjointData_frozen_level (m + 2) H 0 1 one_pos
  obtain ⟨K, hK, hbd⟩ := px7_gen_bound hd m hm Hm
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s H.hs0 H.hsd (m + 2) (by omega)
    (frozenRegime d s c₀) 1 Λ₀ Λ₀
  refine ⟨K * Real.exp |C|, by positivity, fun x hx h hh0 hh1 => ?_⟩
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hx' : MemHs (m : ℝ) x := hx.mono hmR
  obtain ⟨hF, hw, hnorm⟩ := hspec D 0 1 (fun _ => ρ) hA2 1 ⟨one_pos, le_rfl⟩ x hx
  set F := propagatorCoeff D (fun _ => ρ) ((m + 2 : ℕ) : ℝ) 1 x with hFdef
  have hlevF : ∀ σ ∈ Set.Icc (0 : ℝ) 1, F σ = frozenCoeff D ρ m x σ := fun σ hσ => by
    have e1 := frozenCoeff_eq_propagatorCoeff_aux hd H.hs0 H.hsd (by omega : 1 ≤ m + 2) hA2 hx
      (t := 1) (τ := σ) ⟨one_pos, le_rfl⟩ hσ
    have e2 := frozenCoeff_level hd H.hs0 H.hsd (m := m) (m' := m + 2) (by omega) (by omega) hA hA2 hx hσ
    rw [hFdef, e1, ← e2]
  have hFm : ∀ σ ∈ Set.Icc (0 : ℝ) 1, MemHs ((m + 2 : ℕ) : ℝ) (F σ) := fun σ hσ => hw.1 σ hσ
  have hGb : ∀ σ ∈ Set.Ioo (0 : ℝ) h, MemHs (m : ℝ) (forwardGen D ρ (F σ)) ∧
      hsNorm (m : ℝ) (forwardGen D ρ (F σ)) ≤ K * Real.exp |C| * hsNorm ((m + 2 : ℕ) : ℝ) x := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) 1 := ⟨hσ.1.le, by linarith [hσ.2]⟩
    obtain ⟨g1, g2⟩ := hbd (F σ) (hFm σ hσ')
    refine ⟨g1, g2.trans ?_⟩
    have hn := hnorm σ hσ'
    rw [frozenRegime_lambdaM] at hn
    have hex : Real.exp (C * σ) ≤ Real.exp |C| := by
      apply Real.exp_le_exp.2
      calc C * σ ≤ |C| * σ := mul_le_mul_of_nonneg_right (le_abs_self C) hσ'.1
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hσ'.2 (abs_nonneg C)
        _ = |C| := mul_one _
    have hxn := hsNorm_nonneg' ((m + 2 : ℕ) : ℝ) x
    calc K * hsNorm ((m + 2 : ℕ) : ℝ) (F σ) ≤ K * (Real.exp |C| * hsNorm ((m + 2 : ℕ) : ℝ) x) :=
          mul_le_mul_of_nonneg_left (hn.trans (mul_le_mul_of_nonneg_right hex hxn)) hK
      _ = _ := by ring
  have hint : MeasureTheory.IntegrableOn (fun _ : ℝ => K * Real.exp |C| * hsNorm ((m + 2 : ℕ) : ℝ) x)
      (Set.Ioc 0 h) := integrableOn_const (by simp) enorm_ne_top
  obtain ⟨hm1, hm2⟩ := MFAdjoint.hsNorm_intervalIntegral_le_majorant (m : ℝ)
    (fun σ => forwardGen D ρ (F σ)) (fun _ => K * Real.exp |C| * hsNorm ((m + 2 : ℕ) : ℝ) x) 0 h
    hh0.le hGb hint
  have heq : (fun k => frozenCoeff D ρ m x h k - x k) =
      fun k => ∫ σ in (0 : ℝ)..h, forwardGen D ρ (F σ) k := by
    funext k
    have := hF.eq k h ⟨hh0.le, hh1⟩
    rw [← hlevF h ⟨hh0.le, hh1⟩, this]
    simp [hFdef]
  rw [heq]
  refine ⟨hm1, hm2.trans ?_⟩
  simp
  linarith

end Quot


section Quot2

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

theorem px7_T_quot_bound (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 2 + 3) νm νp c₀ Λ₀ β V ρ) :
    ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x → ∀ h : ℝ, 0 < h → h ≤ 1 →
      MemHs (m : ℝ) (fun k => (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m h x k -
        px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m 0 x k) / ((h : ℝ) : ℂ)) ∧
      hsNorm (m : ℝ) (fun k => (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m h x k -
        px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m 0 x k) / ((h : ℝ) : ℂ)) ≤
        Kt * hsNorm ((m + 2 : ℕ) : ℝ) x := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega))
  obtain ⟨Kq, hKq, hq⟩ := px7_frozen_quot_bound hd m hm H
  set K1 := 1 + hsNorm 0 (coeffOf ρ) with hK1def
  have hK10 : 0 ≤ K1 := by have := hsNorm_nonneg' (0 : ℝ) (coeffOf ρ); linarith
  refine ⟨K1 * Kq, by positivity, fun x hx h hh0 hh1 => ?_⟩
  obtain ⟨hm1, hm2⟩ := hq x hx h hh0 hh1
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hx' : MemHs (m : ℝ) x := hx.mono hmR
  have hF := px7_frozen_mem hd m hm Hm hx' hh0.le
  have e : (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ)) =
      ((h : ℝ) : ℂ)⁻¹ • px7_centerC ρ (fun k => frozenCoeff D ρ m x h k - x k) := by
    have e1 : (fun k => frozenCoeff D ρ m x h k - x k) = frozenCoeff D ρ m x h - x := rfl
    rw [e1, px7_centerC_sub hρ0 (hF.mono (by positivity)) (hx'.mono (by positivity))]
    funext k
    simp only [px7_T, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [frozenCoeff_zero (by omega) hx']
    rw [div_eq_inv_mul]
  obtain ⟨c1, c2⟩ := px7_hs_centerC hρ0 (by positivity) hm1
  rw [e]
  refine ⟨MFAdjoint.memHs_smul_coeff c1 _, ?_⟩
  have := MFThermalReg.hsNorm_smul (m : ℝ) (((h : ℝ) : ℂ)⁻¹) (px7_centerC ρ (fun k => frozenCoeff D ρ m x h k - x k))
  show hsNorm (m : ℝ) (fun k => (((h : ℝ) : ℂ)⁻¹) * px7_centerC ρ (fun k => frozenCoeff D ρ m x h k - x k) k) ≤ _
  rw [this]
  have hn : ‖((h : ℝ) : ℂ)⁻¹‖ = h⁻¹ := by simp [abs_of_pos hh0]
  rw [hn]
  have : h⁻¹ * (K1 * (h * (Kq * hsNorm ((m + 2 : ℕ) : ℝ) x))) = K1 * Kq * hsNorm ((m + 2 : ℕ) : ℝ) x := by
    field_simp
  calc h⁻¹ * hsNorm (m : ℝ) (px7_centerC ρ fun k => frozenCoeff D ρ m x h k - x k)
      ≤ h⁻¹ * (K1 * hsNorm (m : ℝ) (fun k => frozenCoeff D ρ m x h k - x k)) :=
        mul_le_mul_of_nonneg_left c2 (by positivity)
    _ ≤ h⁻¹ * (K1 * (h * (Kq * hsNorm ((m + 2 : ℕ) : ℝ) x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm2 hK10) (by positivity)
    _ = _ := this

end Quot2


section GenLin

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

theorem px7_eq_of_hsNorm_zero {m : ℝ} {c : Coeff d} (hc : MemHs m c) (h : hsNorm m c = 0) :
    c = 0 := by
  have h0 : hsNormSq m c = 0 := by
    unfold hsNorm at h
    exact (Real.sqrt_eq_zero (hsNormSq_nonneg m c)).1 h
  funext k
  have h1 : sobWeight m k * ‖c k‖ ^ 2 ≤ hsNormSq m c :=
    hc.le_tsum k (fun j _ => mul_nonneg (sobWeight_pos m j).le (sq_nonneg _))
  rw [h0] at h1
  have h2 : 0 ≤ sobWeight m k * ‖c k‖ ^ 2 := mul_nonneg (sobWeight_pos m k).le (sq_nonneg _)
  have h3 : sobWeight m k * ‖c k‖ ^ 2 = 0 := le_antisymm h1 h2
  have h4 : ‖c k‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (sobWeight_pos m k).ne'
    · exact h
  simpa using h4

theorem px7_gen_data (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) :
    MemHs 0 (coeffOf ρ) ∧ (∀ j, MemHs 0 (driftCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρ j)) ∧
    IsRealCoeff (coeffOf ρ) ∧ IsRealCoeff (coeffOf V) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hA := adjointData_frozen_level m H 0 1 one_pos
  obtain ⟨h1, h2⟩ := ET.coeff_memHs_zero_of_data (mfData d s H.hs0 H.hsd V β H.hβ) ρ
    (m := m) (VB := Λ₀) (by exact_mod_cast H.hρC) hA.hV
  refine ⟨h1, h2, isRealCoeff_coeffOf ρ (MFAdjoint.integrable_of_cont (H.cont (by omega))), ?_⟩
  exact isRealCoeff_coeffOf V (MFAdjoint.integrable_of_cont
    (MFAux.continuous_of_isCk (H.hV.of_le (by exact_mod_cast (show 1 ≤ m + 3 by omega)))))

theorem px7_Ah_add (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 2 + 3) νm νp c₀ Λ₀ β V ρ) {x y : Coeff d}
    (hx : MemHs ((m + 2 : ℕ) : ℝ) x) (hy : MemHs ((m + 2 : ℕ) : ℝ) y) :
    px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ (x + y) =
      px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x + px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ y := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  obtain ⟨hρ0, hb, -, -⟩ := px7_gen_data hd m hm Hm
  obtain ⟨K, hK, hbd⟩ := px7_gen_bound hd m hm Hm
  have h1 : MemHs 1 x := hx.mono (by exact_mod_cast (by omega : 1 ≤ m + 2))
  have h1' : MemHs 1 y := hy.mono (by exact_mod_cast (by omega : 1 ≤ m + 2))
  unfold px7_Ah
  rw [forwardGen_add_H1 _ ρ hρ0 hb h1 h1']
  exact px7_centerC_add hρ0 ((hbd x hx).1.mono (by positivity)) ((hbd y hy).1.mono (by positivity))

theorem px7_Ah_smul (m : ℕ) (a : ℂ) (x : Coeff d) (D : DynData d) :
    px7_Ah D ρ (a • x) = a • px7_Ah D ρ x := by
  unfold px7_Ah
  rw [forwardGen_smul, px7_centerC_smul]

theorem px7_Ah_real (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d} (hx : IsRealCoeff x) :
    IsRealCoeff (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) ∧
    px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x =
      centerCoeff ρ (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) ∧
    IsRealCoeff (px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) := by
  obtain ⟨-, -, hρr, hVr⟩ := px7_gen_data hd m hm H
  have hr : IsRealCoeff (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) :=
    forwardGen_isReal _ ρ hρr hVr hx
  have e : px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x =
      centerCoeff ρ (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) := px7_centerC_eq hρr hr
  exact ⟨hr, e, by rw [e]; exact centerCoeff_isReal hr⟩

/-- Bridge: the classical centered generator of `toFun x` is `toFun (Â x)`. -/
theorem px7_bridge (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 2 + 3) νm νp c₀ Λ₀ β V ρ) {x : Coeff d} (hr : IsRealCoeff x)
    (hx : MemHs ((m + 2 : ℕ) : ℝ) x) :
    Torus.IsCk 2 (toFun x) ∧
    centeredGen (mfData d s H.hs0 H.hsd V β H.hβ) ρ (toFun x) =
      toFun (px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  obtain ⟨K, hK, hbd⟩ := px7_gen_bound hd m hm Hm
  obtain ⟨hfm, -⟩ := hbd x hx
  have hdm : (d : ℝ) / 2 < m := by
    have := mStar_gt d
    have h2 : (mStar d : ℝ) + 2 ≤ m := by exact_mod_cast hm
    linarith
  have hdm2 : (d : ℝ) / 2 + ((2 : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by
    push_cast; linarith
  obtain ⟨C2, hC2⟩ := toFun_isCk_le 2 ((m + 2 : ℕ) : ℝ) hdm2
  obtain ⟨hck, -⟩ := hC2 x hx hr
  refine ⟨hck, ?_⟩
  obtain ⟨hgr, hAe, -⟩ := px7_Ah_real hd m hm Hm hr
  have hdm' : (d : ℝ) / 2 < ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hWS := ClassicalPart.ws0_of_memHs hdm' hx
  have hWSg := ClassicalPart.ws0_of_memHs hdm hfm
  have hK : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V := H.hV.of_le (by exact_mod_cast (show 1 ≤ m + 2 + 3 by omega))
  have hρ1 : Torus.IsCk 1 ρ := H.hρC.of_le (by exact_mod_cast (show 1 ≤ m + 2 + 3 by omega))
  have hbg := ClassicalPart.backwardGenerator_eq_toFun D hK hV1 hρ1 hr hWS hck hgr hWSg
  unfold centeredGen
  rw [hbg, hAe]
  exact (projMean_toFun H.thermal.1 (H.cont (by omega)) ((ClassicalPart.WS_zero_iff _).1 hWSg) hfm hgr).1

end GenLin


section Comm

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρ : Torus d → ℝ}

theorem px7_T_sub (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ) {x y : Coeff d} (hx : MemHs (m : ℝ) x)
    (hy : MemHs (m : ℝ) y) {τ : ℝ} (hτ : 0 ≤ τ) :
    px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ (x - y) =
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x - px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ y := by
  have hy' : MemHs (m : ℝ) ((-1 : ℂ) • y) := MFAdjoint.memHs_smul_coeff hy _
  have e : x - y = x + (-1 : ℂ) • y := by funext k; simp [sub_eq_add_neg]
  rw [e, px7_T_add hd m hm H hx hy' hτ, px7_T_smul hd m hm H hy _ hτ]
  funext k; simp [sub_eq_add_neg]

/-- `Â` commutes with `T τ` on `H^{m+2}`. -/
theorem px7_comm (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 2 + 3) νm νp c₀ Λ₀ β V ρ) (M : ℝ)
    (hM : ∀ τ : ℝ, 0 ≤ τ → ∀ y : Coeff d, MemHs (m : ℝ) y →
      hsNorm (m : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ y) ≤ M * hsNorm (m : ℝ) y)
    (hM2 : ∀ τ : ℝ, 0 ≤ τ → ∀ y : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) y →
      MemHs ((m + 2 : ℕ) : ℝ) (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ y))
    {x : Coeff d} (hx : MemHs ((m + 2 : ℕ) : ℝ) x) {τ : ℝ} (hτ : 0 ≤ τ) :
    px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ (px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ x) =
      px7_T (mfData d s H.hs0 H.hsd V β H.hβ) ρ m τ (px7_Ah (mfData d s H.hs0 H.hsd V β H.hβ) ρ x) := by
  have h3 := ClassicalPart.three_le_mStar d
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous (H.cont (by omega))
  have hρ : IsProbDensity ρ := H.thermal.1
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hx' : MemHs (m : ℝ) x := hx.mono hmR
  set y := px7_T D ρ m τ x with hy
  have hy2 : MemHs ((m + 2 : ℕ) : ℝ) y := hM2 τ hτ x hx
  have hy' : MemHs (m : ℝ) y := hy2.mono hmR
  obtain ⟨Kg, hKg, hbd⟩ := px7_Ah_bound hd m hm Hm
  obtain ⟨hAx, -⟩ := hbd x hx
  obtain ⟨hAy, -⟩ := hbd y hy2
  have d1 := px7_T_deriv hd m hm H hy2
  have d2 := px7_T_deriv hd m hm H hx
  -- the quotient for `y` is `T τ` of the quotient for `x`
  have hTx0 : ∀ h : ℝ, 0 < h → MemHs (m : ℝ) (px7_T D ρ m h x) := fun h hh =>
    px7_T_mem hd m hm Hm hx' hh.le
  have hmain : ∀ h : ℝ, 0 < h →
      (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ)) =
        px7_T D ρ m τ (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ)) := by
    intro h hh
    have hT0x : MemHs (m : ℝ) (px7_T D ρ m 0 x) := px7_T_mem hd m hm Hm hx' le_rfl
    have e1 : px7_T D ρ m h y = px7_T D ρ m τ (px7_T D ρ m h x) := by
      have s1 := px7_T_semigroup hd m hm Hm hx' (σ := h) (τ := τ) hh.le hτ
      have s2 := px7_T_semigroup hd m hm Hm hx' (σ := τ) (τ := h) hτ hh.le
      rw [add_comm τ h] at s2
      exact s1.symm.trans s2
    have e2 : px7_T D ρ m 0 y = px7_T D ρ m τ (px7_T D ρ m 0 x) := by
      have h1 : px7_T D ρ m 0 y = px7_centerC ρ y := px7_T_zero hd m hm Hm hy'
      have h2 : y = px7_centerC ρ (frozenCoeff D ρ m x τ) := rfl
      have hcen : px7_centerC ρ y = y := by
        rw [h2]
        exact px7_centerC_idem hρ hρ0 ((px7_frozen_mem hd m hm Hm hx' hτ).mono (by positivity))
      rw [h1, hcen, px7_T_zero hd m hm Hm hx', px7_T_centerC hd m hm Hm hx' hτ]
    have hdiv : (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ)) =
        ((h : ℝ) : ℂ)⁻¹ • (px7_T D ρ m h x - px7_T D ρ m 0 x) := by
      funext k; simp [div_eq_inv_mul]
    have hdiv' : (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ)) =
        ((h : ℝ) : ℂ)⁻¹ • (px7_T D ρ m h y - px7_T D ρ m 0 y) := by
      funext k; simp [div_eq_inv_mul]
    rw [hdiv', hdiv, px7_T_smul hd m hm Hm (memHs_sub (hTx0 h hh) hT0x) _ hτ,
      px7_T_sub hd m hm Hm (hTx0 h hh) hT0x hτ, e1, e2]
  -- limit
  have hlim : Tendsto (fun h : ℝ => hsNorm (m : ℝ) (fun k =>
      (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ) -
        px7_T D ρ m τ (px7_Ah D ρ x) k)) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    have hM0 : 0 ≤ M := by
      have := hM 0 le_rfl (deltaCoeff 0) (deltaCoeff_memHs _ _)
      have h1 : 0 ≤ hsNorm (m : ℝ) (px7_T D ρ m 0 (deltaCoeff 0)) := hsNorm_nonneg' _ _
      have h2 : 0 < hsNorm (m : ℝ) (deltaCoeff (0 : Lattice d)) := by
        rw [hsNorm_deltaCoeff]; positivity
      by_contra hneg; push_neg at hneg; nlinarith
    have hb : ∀ᶠ h in 𝓝[Set.Ioi 0] (0 : ℝ), hsNorm (m : ℝ) (fun k =>
        (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ) - px7_T D ρ m τ (px7_Ah D ρ x) k) ≤
        M * hsNorm (m : ℝ) (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ) -
          px7_Ah D ρ x k) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : 0 < h := hh
      have hQm : MemHs (m : ℝ) (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ)) := by
        have : (fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ)) =
            ((h : ℝ) : ℂ)⁻¹ • (px7_T D ρ m h x - px7_T D ρ m 0 x) := by
          funext k; simp [div_eq_inv_mul]
        rw [this]
        exact MFAdjoint.memHs_smul_coeff (memHs_sub (hTx0 h hh') (px7_T_mem hd m hm Hm hx' le_rfl)) _
      have hdiffm : MemHs (m : ℝ) ((fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ)) -
          px7_Ah D ρ x) := memHs_sub hQm (hAx.mono (le_refl _))
      have e : (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ) -
          px7_T D ρ m τ (px7_Ah D ρ x) k) =
          px7_T D ρ m τ ((fun k => (px7_T D ρ m h x k - px7_T D ρ m 0 x k) / ((h : ℝ) : ℂ)) -
            px7_Ah D ρ x) := by
        rw [px7_T_sub hd m hm Hm hQm hAx hτ, ← hmain h hh']
        funext k; simp; rfl
      rw [e]
      exact hM τ hτ _ hdiffm
    refine squeeze_zero' (Filter.Eventually.of_forall fun h => hsNorm_nonneg' _ _) hb ?_
    simpa using d2.const_mul M
  -- uniqueness of the limit
  have hbound : ∀ᶠ h in 𝓝[Set.Ioi 0] (0 : ℝ),
      hsNorm (m : ℝ) (px7_Ah D ρ y - px7_T D ρ m τ (px7_Ah D ρ x)) ≤
        hsNorm (m : ℝ) (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ) -
          px7_Ah D ρ y k) +
        hsNorm (m : ℝ) (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ) -
          px7_T D ρ m τ (px7_Ah D ρ x) k) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hTy := px7_T_mem hd m hm Hm hy' hh'.le
    have hTy0 := px7_T_mem hd m hm Hm hy' le_rfl
    have hQm : MemHs (m : ℝ) (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ)) := by
      have : (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ)) =
          ((h : ℝ) : ℂ)⁻¹ • (px7_T D ρ m h y - px7_T D ρ m 0 y) := by
        funext k; simp [div_eq_inv_mul]
      rw [this]
      exact MFAdjoint.memHs_smul_coeff (memHs_sub hTy hTy0) _
    have hT1 := px7_T_mem hd m hm Hm hAx hτ
    have e : px7_Ah D ρ y - px7_T D ρ m τ (px7_Ah D ρ x) =
        ((fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ)) - px7_T D ρ m τ (px7_Ah D ρ x)) -
        ((fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ)) - px7_Ah D ρ y) := by
      funext k; simp
    rw [e]
    have h5 := MFAdjoint.hsNorm_sub_le_add (memHs_sub hQm hT1) (memHs_sub hQm hAy)
    refine h5.trans (le_of_eq ?_)
    exact add_comm _ _
  have hfin : Tendsto (fun h : ℝ =>
      hsNorm (m : ℝ) (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ) -
          px7_Ah D ρ y k) +
        hsNorm (m : ℝ) (fun k => (px7_T D ρ m h y k - px7_T D ρ m 0 y k) / ((h : ℝ) : ℂ) -
          px7_T D ρ m τ (px7_Ah D ρ x) k)) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    simpa using d1.add hlim
  have hle : hsNorm (m : ℝ) (px7_Ah D ρ y - px7_T D ρ m τ (px7_Ah D ρ x)) ≤ 0 :=
    ge_of_tendsto hfin hbound
  have hz : hsNorm (m : ℝ) (px7_Ah D ρ y - px7_T D ρ m τ (px7_Ah D ρ x)) = 0 :=
    le_antisymm hle (hsNorm_nonneg' _ _)
  have := px7_eq_of_hsNorm_zero (memHs_sub hAy (px7_T_mem hd m hm Hm hAx hτ)) hz
  funext k
  have hk := congrFun this k
  simpa [sub_eq_zero] using hk

end Comm


/-! ### The bundle used downstream -/

/-- The base level `m = ⌊d/2⌋ + 5` (`= mStar d + 2`). -/
def px7_m (d : ℕ) : ℕ := ⌊(d : ℝ) / 2⌋₊ + 5

theorem px7_m_eq (d : ℕ) : px7_m d = mStar d + 2 := by
  unfold px7_m mStar; omega

/-- Everything the tensor argument needs from the one-variable operator. -/
structure OV (D : DynData d) (ρ : Torus d → ℝ) (m : ℕ) (T : ℝ → Coeff d → Coeff d)
    (Ah : Coeff d → Coeff d) : Prop where
  hm_gt : (d : ℝ) / 2 + 4 < m
  prob : IsProbDensity ρ
  rho_cont : Continuous ρ
  add : ∀ τ : ℝ, 0 ≤ τ → ∀ x y : Coeff d, MemHs (m : ℝ) x → MemHs (m : ℝ) y →
    T τ (x + y) = T τ x + T τ y
  smul : ∀ τ : ℝ, 0 ≤ τ → ∀ x : Coeff d, MemHs (m : ℝ) x → ∀ a : ℂ, T τ (a • x) = a • T τ x
  dec0 : ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ x : Coeff d, MemHs (m : ℝ) x →
    MemHs (m : ℝ) (T τ x) ∧ hsNorm (m : ℝ) (T τ x) ≤ M * Real.exp (-c * τ) * hsNorm (m : ℝ) x
  dec2 : ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ x : Coeff d,
    MemHs ((m + 2 : ℕ) : ℝ) x → MemHs ((m + 2 : ℕ) : ℝ) (T τ x) ∧
      hsNorm ((m + 2 : ℕ) : ℝ) (T τ x) ≤ M * Real.exp (-c * τ) * hsNorm ((m + 2 : ℕ) : ℝ) x
  real : ∀ τ : ℝ, 0 ≤ τ → ∀ x : Coeff d, MemHs (m : ℝ) x → IsRealCoeff x → IsRealCoeff (T τ x)
  mean : ∀ τ : ℝ, 0 ≤ τ → ∀ x : Coeff d, MemHs (m : ℝ) x → px7_mC ρ (T τ x) = 0
  const : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℂ, T τ (z • deltaCoeff (0 : Lattice d)) = 0
  zero : ∀ x : Coeff d, MemHs (m : ℝ) x → T 0 x = px7_centerC ρ x
  semi : ∀ σ τ : ℝ, 0 ≤ σ → 0 ≤ τ → ∀ x : Coeff d, MemHs (m : ℝ) x → T (σ + τ) x = T σ (T τ x)
  tcont : ∀ x : Coeff d, MemHs (m : ℝ) x → ∀ τ₀ : ℝ, 0 ≤ τ₀ →
    Tendsto (fun τ => hsNorm (m : ℝ) (T τ x - T τ₀ x)) (𝓝[Set.Ici 0] τ₀) (𝓝 0)
  hS : ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev (m : ℝ) ψ → ∀ τ : ℝ, 0 ≤ τ →
    equilibriumSemigroup D ρ τ ψ = toFun (T τ (coeffOf ψ))
  Ah_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x →
    MemHs (m : ℝ) (Ah x) ∧ hsNorm (m : ℝ) (Ah x) ≤ K * hsNorm ((m + 2 : ℕ) : ℝ) x
  Ah_add : ∀ x y : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x → MemHs ((m + 2 : ℕ) : ℝ) y →
    Ah (x + y) = Ah x + Ah y
  Ah_smul : ∀ (a : ℂ) (x : Coeff d), Ah (a • x) = a • Ah x
  Ah_real : ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x → IsRealCoeff x → IsRealCoeff (Ah x)
  deriv : ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x →
    Tendsto (fun h : ℝ => hsNorm (m : ℝ) (fun k =>
      (T h x k - T 0 x k) / ((h : ℝ) : ℂ) - Ah x k)) (𝓝[Set.Ioi 0] 0) (𝓝 0)
  quot : ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x → ∀ h : ℝ, 0 < h → h ≤ 1 →
    MemHs (m : ℝ) (fun k => (T h x k - T 0 x k) / ((h : ℝ) : ℂ)) ∧
    hsNorm (m : ℝ) (fun k => (T h x k - T 0 x k) / ((h : ℝ) : ℂ)) ≤
      Kt * hsNorm ((m + 2 : ℕ) : ℝ) x
  comm : ∀ x : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) x → ∀ τ : ℝ, 0 ≤ τ → Ah (T τ x) = T τ (Ah x)
  bridge : ∀ x : Coeff d, IsRealCoeff x → MemHs ((m + 2 : ℕ) : ℝ) x →
    Torus.IsCk 2 (toFun x) ∧ centeredGen D ρ (toFun x) = toFun (Ah x)


theorem px7_oneVar (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρC : Torus.IsSmooth ρ)
    (hpos : ∀ x, 0 < ρ x) :
    OV (mfData d s hs0 hsd V β hβ) ρ (px7_m d) (px7_T (mfData d s hs0 hsd V β hβ) ρ (px7_m d))
      (px7_Ah (mfData d s hs0 hsd V β hβ) ρ) := by
  have h3 := ClassicalPart.three_le_mStar d
  set m := px7_m d with hmdef
  have hm : mStar d + 2 ≤ m := (px7_m_eq d).ge
  set N := m + 2 + mStar d + 3 with hN
  obtain ⟨c₀, Λ₀, H⟩ := MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρ hρβ hρC hpos N
  have Hm : FrozenHyp d s (m + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hm1 : FrozenHyp d s (m + 1 + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hm2 : FrozenHyp d s (m + 2 + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have hj0 : (d : ℝ) / 2 + 4 < m := by
    have : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have e : (m : ℝ) = (⌊(d : ℝ) / 2⌋₊ : ℝ) + 5 := by rw [hmdef, px7_m]; push_cast; ring
    rw [e]; linarith
  have hj2 : (d : ℝ) / 2 + 4 < ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨M0, c0, hM0, hc0, hdec0⟩ := px7_decay hd s m m hm le_rfl hj0 β⁻¹ β⁻¹ c₀ Λ₀
  obtain ⟨M2, c2, hM2, hc2, hdec2⟩ := px7_decay hd s m (m + 2) hm (by omega) hj2 β⁻¹ β⁻¹ c₀ Λ₀
  have hH0 : FrozenHyp d s (m + mStar d + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have hH2 : FrozenHyp d s (m + 2 + mStar d + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  refine ⟨hj0, H.thermal.1, H.cont (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ x y hx hy; exact px7_T_add hd m hm Hm hx hy hτ
  · intro τ hτ x hx a; exact px7_T_smul hd m hm Hm hx a hτ
  · exact ⟨M0, c0, hM0, hc0, fun τ hτ x hx => hdec0 β V ρ hH0 x hx τ hτ⟩
  · exact ⟨M2, c2, hM2, hc2, fun τ hτ x hx => hdec2 β V ρ hH2 x hx τ hτ⟩
  · intro τ hτ x hx hre; exact (px7_T_real hd m hm Hm hx hre hτ).2
  · intro τ hτ x hx; exact px7_T_mean hd m hm Hm hx hτ
  · intro τ hτ z; exact px7_T_const hd m hm Hm z hτ
  · intro x hx; exact px7_T_zero hd m hm Hm hx
  · intro σ τ hσ hτ x hx; exact px7_T_semigroup hd m hm Hm hx hσ hτ
  · intro x hx τ₀ hτ₀
    refine px7_T_cont hd m hm Hm1 (M0 * 1) ?_ hx hτ₀
    intro τ hτ y hy
    have := (hdec0 β V ρ hH0 y hy τ hτ).2
    have hE : Real.exp (-c0 * τ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc _ ≤ M0 * Real.exp (-c0 * τ) * hsNorm (m : ℝ) y := this
      _ ≤ M0 * 1 * hsNorm (m : ℝ) y := by
        have := hsNorm_nonneg' (m : ℝ) y
        gcongr
  · intro ψ hψc hψ τ hτ; exact px7_S_eq hd m hm Hm hψc hψ hτ
  · obtain ⟨K, hK, h⟩ := px7_Ah_bound hd m hm Hm
    exact ⟨K, hK, h⟩
  · intro x y hx hy; exact px7_Ah_add hd m hm Hm2 hx hy
  · intro a x; exact px7_Ah_smul m a x _
  · intro x hx hre; exact (px7_Ah_real hd m hm Hm hre).2.2
  · intro x hx; exact px7_T_deriv hd m hm Hm2 hx
  · obtain ⟨Kt, hKt, h⟩ := px7_T_quot_bound hd m hm Hm2
    exact ⟨Kt, hKt, h⟩
  · intro x hx τ hτ
    refine px7_comm hd m hm Hm2 M0 ?_ ?_ hx hτ
    · intro τ' hτ' y hy
      have := (hdec0 β V ρ hH0 y hy τ' hτ').2
      have hE : Real.exp (-c0 * τ') ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      calc _ ≤ M0 * Real.exp (-c0 * τ') * hsNorm (m : ℝ) y := this
        _ ≤ M0 * 1 * hsNorm (m : ℝ) y := by
          have := hsNorm_nonneg' (m : ℝ) y
          gcongr
        _ = _ := by ring
    · intro τ' hτ' y hy; exact (hdec2 β V ρ hH2 y hy τ' hτ').1
  · intro x hr hx; exact px7_bridge hd m hm Hm2 hr hx

end HRS.PDE.PX7

end
