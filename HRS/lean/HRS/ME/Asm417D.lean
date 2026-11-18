import HRS.ME.Mode417B
import HRS.ME.Asm417A
import HRS.ME.Asm417B
import HRS.ME.Asm417C
import HRS.ME.Mink417
import HRS.ME.Fourier417B
import HRS.ME.Est417

/-!
# Chunk E, row 4.17: assembly packet D (proofs of B2 `single_j_bound` and of the measurability of the
integrated centered forcing)

* `asmD_pathwise`: on a good event, `integratedCenteredForcing … b ω = ∑' l, J_l(b, ω)` with
  `J_l(b, ω) = ∫_0^b γ_l(b-r) R_{e_l}(X^r ω) dr` (A1, A2, dominated swap of sum and integral).
* `asmD_J_aemeas`: each `ω ↦ J_l(b, ω)` is a.e. measurable.
* `integratedCenteredForcing_aemeasurable`: the measurability statement (second deliverable).
* `single_j_bound_proof`: B2, by Minkowski over the modes and `mode_forcing_bound_proof`.

The statements of `HRS/ME/Spec417Asm.lean` are copied verbatim; `HRS/ME/Spec417Asm.lean` is not imported.
Helpers carry the prefix `asmD_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-! ### Elementary helpers -/

/-- Summability of `⟨l⟩^{-q}` over the nonzero lattice for `q > d`. -/
theorem asmD_summable_rpow (q : ℝ) (hq : (d : ℝ) < q) :
    Summable fun l : NonzeroLattice d => Lattice.jp l.1 ^ (-q) :=
  (summable_jp_rpow (d := d) (q / 2) (by linarith)).congr fun l => by
    rw [show -(2 * (q / 2)) = -q by ring]

/-- `x^{-(b-a)} = x^a / x^b` for natural `a, b`. -/
theorem asmD_rpow_neg_sub (x : ℝ) (hx : 0 < x) (a b : ℕ) :
    x ^ (-((b : ℝ) - (a : ℝ))) = x ^ a / x ^ b := by
  rw [show -((b : ℝ) - (a : ℝ)) = (a : ℝ) - (b : ℝ) by ring, Real.rpow_sub hx, Real.rpow_natCast,
    Real.rpow_natCast]

/-- Squaring commutes with a countable supremum in `ℝ≥0∞` (only `≤` is needed). -/
theorem asmD_biSup_sq {ι : Type*} (S : Set ι) (f : ι → ℝ≥0∞) :
    (⨆ i ∈ S, f i) ^ 2 ≤ ⨆ i ∈ S, f i ^ 2 := by
  rw [sq]
  calc (⨆ i ∈ S, f i) * (⨆ i ∈ S, f i) = ⨆ i ∈ S, ⨆ j ∈ S, f j * f i := by
        simp only [ENNReal.mul_iSup, ENNReal.iSup_mul]
    _ ≤ ⨆ i ∈ S, f i ^ 2 := by
        refine iSup₂_le fun i hi => iSup₂_le fun j hj => ?_
        rcases le_total (f i) (f j) with h | h
        · calc f j * f i ≤ f j * f j := by gcongr
            _ = f j ^ 2 := (sq (f j)).symm
            _ ≤ ⨆ k ∈ S, f k ^ 2 := le_iSup₂ (f := fun k _ => f k ^ 2) j hj
        · calc f j * f i ≤ f i * f i := by gcongr
            _ = f i ^ 2 := (sq (f i)).symm
            _ ≤ ⨆ k ∈ S, f k ^ 2 := le_iSup₂ (f := fun k _ => f k ^ 2) i hi

/-- `(y^{1/2})^2 = y` in `ℝ≥0∞`. -/
theorem asmD_rpow_half_sq (y : ℝ≥0∞) : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- A coefficient bound from the weighted decay: each of `|f l|, |g l|` is at most `Cd E exp(-cd v) / ⟨l⟩^p`. -/
theorem asmD_coef_bound (p : ℕ) (Cd cd E : ℝ) (hE : 0 ≤ E) (hCd : 0 ≤ Cd)
    (f g : NonzeroLattice d → ℝ) (v : ℝ)
    (hs : Summable fun l : NonzeroLattice d => Lattice.jp l.1 ^ p * (|f l| + |g l|))
    (ht : ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p * (|f l| + |g l|) ≤ Cd * E * Real.exp (-cd * v))
    (l : NonzeroLattice d) :
    |f l| ≤ Cd * E / Lattice.jp l.1 ^ p * Real.exp (-cd * v) ∧
      |g l| ≤ Cd * E / Lattice.jp l.1 ^ p * Real.exp (-cd * v) := by
  have hjp : 0 < Lattice.jp l.1 ^ p := pow_pos (Torus.jp_pos l.1) p
  have hfl : Lattice.jp l.1 ^ p * (|f l| + |g l|) ≤ Cd * E * Real.exp (-cd * v) :=
    (hs.le_tsum l (fun k _ => mul_nonneg (pow_nonneg (Torus.jp_pos k.1).le p)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))).trans ht
  have hpf : 0 ≤ Lattice.jp l.1 ^ p * |f l| := mul_nonneg hjp.le (abs_nonneg _)
  have hpg : 0 ≤ Lattice.jp l.1 ^ p * |g l| := mul_nonneg hjp.le (abs_nonneg _)
  constructor
  · rw [show Cd * E / Lattice.jp l.1 ^ p * Real.exp (-cd * v)
        = (Cd * E * Real.exp (-cd * v)) / Lattice.jp l.1 ^ p by ring, le_div_iff₀ hjp]
    nlinarith
  · rw [show Cd * E / Lattice.jp l.1 ^ p * Real.exp (-cd * v)
        = (Cd * E * Real.exp (-cd * v)) / Lattice.jp l.1 ^ p by ring, le_div_iff₀ hjp]
    nlinarith

/-- Regularity of the Fourier coefficients of `U_v φ_j` in `v`. -/
theorem asmD_gam_contOn (hd1 : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) (j l : NonzeroLattice d) :
    ContinuousOn (fun v => Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
      (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l) (Set.Ici 0) := by
  have hψ : Torus.IsSmooth (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x) :=
    asmB_sm_const_mul (HRS.FieldSingAux.isSmooth_realMode j) _
  intro v hv
  exact ((fourier_coeff_regular_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos _ hψ l).2.1 v hv).continuousWithinAt

/-! ### The path integrals of the modes -/

/-- The `l`-th real Fourier coefficient `γ_l(v) = ⟨U_v φ_j, e_l⟩` of the evolved feature. -/
def asmD_gam (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (m : ℝ) (j l : NonzeroLattice d) (v : ℝ) : ℝ :=
  Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
    (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l

/-- The derivative `γ'_l(v) = ⟨-A_β L_β U_v φ_j, e_l⟩`. -/
def asmD_gam' (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (m : ℝ) (j l : NonzeroLattice d) (v : ℝ) : ℝ :=
  Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
    (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l

/-- The mode path integral `J_l(b, ω) = ∫_0^b γ_l(b-r) R_{e_l}(X^r ω) dr`, `γ_l(v) = ⟨U_v φ_j, e_l⟩`. -/
def asmD_J {Ω : Type*} {N : ℕ} (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (m : ℝ) (j l : NonzeroLattice d) (X : ℝ≥0 → Ω → Config d N) (b : ℝ) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..b,
    Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
      (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l *
    forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)

/-- The a.e. measurability of the mode path integral. -/
theorem asmD_J_aemeas (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X) (j l : NonzeroLattice d) (b : ℝ)
    (hb : 0 ≤ b) (hbH : b ≤ H) :
    AEMeasurable (fun ω => asmD_J s hs0 hsd V β hβ ρβ m j l X b ω) P := by
  have hd1 : 1 ≤ d := by omega
  exact pathIntegral_aemeasurable hd hs0 hsd V hV β hβ hN P X₀ W X H hflow
    (forcingStat s V β ρβ (Torus.realMode l)) (asmC_fs_meas hsd V β ρβ (Torus.realMode l)) _ b hb hbH
    ((asmD_gam_contOn hd1 hs0 hsd V hV β hβ ρβ hρβ hρS hρpos m j l).mono Set.Icc_subset_Ici_self)

/-! ### Pathwise identity on a good event -/

/-- On a.e. path, `integratedCenteredForcing` is the (absolutely summable) sum of the mode path integrals,
for every time `b ∈ [0, H]`. -/
theorem asmD_pathwise (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X) (j : NonzeroLattice d) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, 0 ≤ b → b ≤ H →
      HasSum (fun l : NonzeroLattice d => asmD_J s hs0 hsd V β hβ ρβ m j l X b ω)
        (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j b ω) ∧
      Summable (fun l : NonzeroLattice d => ‖asmD_J s hs0 hsd V β hβ ρβ m j l X b ω‖) := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hd1 : 1 ≤ d := by omega
  have hsol : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exact absurd h1 (by omega)
  obtain ⟨B, hBm, hB0, hBL, C₀, C₁, hC₀, hC₁, -, hbd⟩ :=
    forcingStat_envelope_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN
  obtain ⟨Cd, cd, hCd, hcd, hdec⟩ :=
    fourier_coeff_decay_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos (9 * d + 82)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Lattice.jp j.1 ^ (-m + ((9 * d + 82 + d + 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.rpow_pos_of_pos (Torus.jp_pos _) _
  have hgood := ae_lintegral_envelope_finite_proof hd hs0 hsd V hV β hβ hN P X₀ W X H hflow B hBm hB0 hBL
  -- the coefficient bound, uniform in `v ≥ 0`
  have hbnd : ∀ v : ℝ, 0 ≤ v → ∀ l : NonzeroLattice d,
      |Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
        (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| ≤ Cd * E / Lattice.jp l.1 ^ (9 * d + 82) := by
    intro v hv l
    have hdj := hdec m j v hv
    rw [← hE] at hdj
    have hexp : Real.exp (-cd * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hcd.le hv])
    have hΓnn : 0 ≤ Cd * E / Lattice.jp l.1 ^ (9 * d + 82) :=
      div_nonneg (mul_nonneg hCd.le hE0.le) (pow_nonneg (Torus.jp_pos _).le _)
    have h := asmD_coef_bound (d := d) (9 * d + 82) Cd cd E hE0.le hCd.le
      (fun l => Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
        (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l)
      (fun l => Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup
        (PDE.mfData d s hs0 hsd V β hβ) ρβ v (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l)
      v hdj.1 hdj.2 l
    exact h.1.trans (mul_le_of_le_one_right hΓnn hexp)
  -- summability of the bounding series over the modes
  have hKsum : Summable (fun l : NonzeroLattice d =>
      Cd * E / Lattice.jp l.1 ^ (9 * d + 82) * (C₁ * Lattice.jp l.1 ^ 2)) := by
    have h := (asmD_summable_rpow (d := d) (((9 * d + 82 : ℕ) : ℝ) - ((2 : ℕ) : ℝ))
      (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])).mul_left (Cd * E * C₁)
    refine h.congr fun l => ?_
    have hx := Torus.jp_pos l.1
    rw [asmD_rpow_neg_sub _ hx 2 (9 * d + 82)]
    ring
  filter_upwards [hgood, hsol.cont, hsol.no_collision] with ω hfin hc hcl
  intro b hb0 hbH
  have hpath : Continuous fun r : ℝ => X r.toNNReal ω :=
    continuous_pi fun i => (hc i).comp continuous_real_toNNReal
  have hnc : ∀ r : ℝ, 0 ≤ r → r ≤ H → X r.toNNReal ω ∉ collisionSet d N := by
    intro r hr0 hrH hmem
    exact hcl r.toNNReal (by rw [Real.coe_toNNReal r hr0]; exact hrH) hmem
  have hψ : Torus.IsSmooth (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x) :=
    asmB_sm_const_mul (HRS.FieldSingAux.isSmooth_realMode j) _
  have hsmU : ∀ v : ℝ, 0 ≤ v → Torus.IsSmooth (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
      (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) :=
    fun v hv => (fourier_coeff_regular_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos _ hψ j).1 v hv
  -- the pointwise expansion of the forcing at time `r ∈ [0, b]` (A1, A2)
  have hF : ∀ r ∈ Set.Icc (0 : ℝ) b, HasSum (fun l : NonzeroLattice d =>
        Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l *
          forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω))
        (centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
            (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) r ω) := by
    intro r hr
    have hv : 0 ≤ b - r := by linarith [hr.2]
    have hrH : r ≤ H := by linarith [hr.2]
    rw [forcing_eq_forcingStat_proof hd hs0 hsd V hV β hβ ρβ hN P X₀ W X H hflow _ (hsmU (b - r) hv) r hr.1
      hrH ω]
    have hsumsub : Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ 2 *
        |Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l|) := by
      refine Summable.of_nonneg_of_le (fun l => mul_nonneg (sq_nonneg _) (abs_nonneg _)) (fun l => ?_)
        (hdec m j (b - r) hv).1
      have hj : Lattice.jp l.1 ^ 2 ≤ Lattice.jp l.1 ^ (9 * d + 82) :=
        pow_le_pow_right₀ (Torus.jp_ge_one l.1) (by omega)
      have hA : 0 ≤ |Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| := abs_nonneg _
      have hB' : 0 ≤ |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup
          (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r) (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l| :=
        abs_nonneg _
      have hP : 0 ≤ Lattice.jp l.1 ^ (9 * d + 82) := pow_nonneg (Torus.jp_pos _).le _
      nlinarith [mul_nonneg (sub_nonneg.2 hj) hA, mul_nonneg hP hB']
    exact forcingStat_hasSum_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN _ (hsmU (b - r) hv) hsumsub
      (X r.toNNReal ω) (hnc r hr.1 hrH)
  obtain ⟨F, hFdef⟩ : ∃ F : NonzeroLattice d → ℝ → ℝ, ∀ l r, F l r =
      Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
        (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l *
        forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω) :=
    ⟨fun l r => Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
        (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l *
        forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω), fun _ _ => rfl⟩
  have hF' : ∀ r ∈ Set.Icc (0 : ℝ) b, HasSum (fun l : NonzeroLattice d => F l r)
      (centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) r ω) := by
    intro r hr
    simp only [hFdef]
    exact hF r hr
  have hRm : ∀ l : NonzeroLattice d, Measurable (fun r : ℝ =>
      forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) :=
    fun l => (asmC_fs_meas (N := N) hsd V β ρβ (Torus.realMode l)).comp hpath.measurable
  have hBint : Integrable (fun r : ℝ => B (X r.toNNReal ω)) (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
    refine ⟨(hBm.comp hpath.measurable).aestronglyMeasurable, ?_⟩
    have e : ∀ r : ℝ, ‖B (X r.toNNReal ω)‖ₑ = ENNReal.ofReal (B (X r.toNNReal ω)) :=
      fun r => Real.enorm_eq_ofReal (hB0 _)
    show ∫⁻ r in Set.Ioc (0 : ℝ) b, ‖B (X r.toNNReal ω)‖ₑ < ∞
    simp only [e]
    exact lt_of_le_of_lt (lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hbH)))
      hfin
  have hγc : ∀ l : NonzeroLattice d, ContinuousOn (fun r : ℝ => Torus.funRealCoeff
      (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
        (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l) (Set.Icc 0 b) := by
    intro l
    exact (asmD_gam_contOn hd1 hs0 hsd V hV β hβ ρβ hρβ hρS hρpos m j l).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun r hr => show (0 : ℝ) ≤ b - r by linarith [hr.2])
  have hFmeas : ∀ l : NonzeroLattice d, AEStronglyMeasurable (fun r : ℝ => F l r)
      (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
    intro l
    have h0 : AEStronglyMeasurable (fun r : ℝ => Torus.funRealCoeff
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l) (volume.restrict (Set.Icc (0 : ℝ) b)) :=
      (hγc l).aestronglyMeasurable measurableSet_Icc
    have h1 : AEStronglyMeasurable (fun r : ℝ => Torus.funRealCoeff
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l) (volume.restrict (Set.Ioc (0 : ℝ) b)) :=
      h0.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    have e : (fun r : ℝ => F l r) = fun r : ℝ => Torus.funRealCoeff
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l *
          forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω) := funext fun r => hFdef l r
    rw [e]
    exact h1.mul (hRm l).aestronglyMeasurable
  have hdom : ∀ l : NonzeroLattice d, ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) b)),
      ‖F l r‖ ≤ (Cd * E / Lattice.jp l.1 ^ (9 * d + 82) * (C₁ * Lattice.jp l.1 ^ 2)) *
        (B (X r.toNNReal ω) + C₀) := by
    intro l
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => ?_)
    have hv : 0 ≤ b - r := by linarith [hr.2]
    have hrH : r ≤ H := by linarith [hr.2]
    have hW : 0 ≤ B (X r.toNNReal ω) + C₀ := add_nonneg (hB0 _) hC₀
    have hΓ : 0 ≤ Cd * E / Lattice.jp l.1 ^ (9 * d + 82) :=
      div_nonneg (mul_nonneg hCd.le hE0.le) (pow_nonneg (Torus.jp_pos _).le _)
    have hγb := hbnd (b - r) hv l
    have hRb := hbd l (X r.toNNReal ω) (hnc r hr.1.le hrH)
    rw [hFdef, Real.norm_eq_abs, abs_mul]
    calc _ ≤ (Cd * E / Lattice.jp l.1 ^ (9 * d + 82)) * (C₁ * Lattice.jp l.1 ^ 2 * (B (X r.toNNReal ω) + C₀)) :=
          mul_le_mul hγb hRb (abs_nonneg _) hΓ
      _ = _ := by ring
  have hKB : ∀ l : NonzeroLattice d, Integrable (fun r : ℝ =>
      (Cd * E / Lattice.jp l.1 ^ (9 * d + 82) * (C₁ * Lattice.jp l.1 ^ 2)) * (B (X r.toNNReal ω) + C₀))
      (volume.restrict (Set.Ioc (0 : ℝ) b)) :=
    fun l => (hBint.add (integrable_const C₀)).const_mul _
  have hFint : ∀ l : NonzeroLattice d, Integrable (fun r : ℝ => F l r) (volume.restrict (Set.Ioc (0 : ℝ) b)) :=
    fun l => Integrable.mono' (hKB l) (hFmeas l) (hdom l)
  have hsumI : Summable (fun l : NonzeroLattice d => ∫ r in Set.Ioc (0 : ℝ) b, ‖F l r‖) := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun r => norm_nonneg _) (fun l => ?_)
      (hKsum.mul_right (∫ r in Set.Ioc (0 : ℝ) b, (B (X r.toNNReal ω) + C₀)))
    calc ∫ r in Set.Ioc (0 : ℝ) b, ‖F l r‖
        ≤ ∫ r in Set.Ioc (0 : ℝ) b, (Cd * E / Lattice.jp l.1 ^ (9 * d + 82) * (C₁ * Lattice.jp l.1 ^ 2)) *
            (B (X r.toNNReal ω) + C₀) := integral_mono_ae (hFint l).norm (hKB l) (hdom l)
      _ = (Cd * E / Lattice.jp l.1 ^ (9 * d + 82) * (C₁ * Lattice.jp l.1 ^ 2)) *
            ∫ r in Set.Ioc (0 : ℝ) b, (B (X r.toNNReal ω) + C₀) := integral_const_mul _ _
  have hsumF : Summable (fun l : NonzeroLattice d => ∫ r in Set.Ioc (0 : ℝ) b, F l r) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun l => norm_nonneg _)
      (fun l => norm_integral_le_integral_norm _) hsumI)
  have hIeq : integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j b ω =
      ∑' l : NonzeroLattice d, ∫ r in Set.Ioc (0 : ℝ) b, F l r := by
    unfold integratedCenteredForcing
    rw [intervalIntegral.integral_of_le hb0]
    refine (setIntegral_congr_fun measurableSet_Ioc
      (fun r hr => (hF' r ⟨hr.1.le, hr.2⟩).tsum_eq.symm)).trans ?_
    exact (integral_tsum_of_summable_integral_norm hFint hsumI).symm
  have hJF : ∀ l : NonzeroLattice d, asmD_J s hs0 hsd V β hβ ρβ m j l X b ω =
      ∫ r in Set.Ioc (0 : ℝ) b, F l r := by
    intro l
    unfold asmD_J
    rw [intervalIntegral.integral_of_le hb0]
    exact setIntegral_congr_fun measurableSet_Ioc (fun r _ => (hFdef l r).symm)
  have hnormJ : Summable (fun l : NonzeroLattice d => ‖asmD_J s hs0 hsd V β hβ ρβ m j l X b ω‖) := by
    refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_) hsumI
    rw [hJF l]
    exact norm_integral_le_integral_norm _
  refine ⟨?_, hnormJ⟩
  have hfun : (fun l : NonzeroLattice d => asmD_J s hs0 hsd V β hβ ρβ m j l X b ω) =
      fun l : NonzeroLattice d => ∫ r in Set.Ioc (0 : ℝ) b, F l r := funext hJF
  rw [hIeq, hfun]
  exact hsumF.hasSum

/-! ### B2: one feature -/

/-- B2.  One feature.  The exponent `((9 d + 82) + d + 3 : ℕ) = 10 d + 85` is the Sobolev loss of
`fourier_coeff_decay` with `p = 9 d + 82`, the smallest integer with `p - K₀ > d` (summability over `l` of
`⟨l⟩^{K₀ - p}`, `K₀ = 8 d + 80`); `C` does not depend on `m`, `j`, `a`, `N`. -/
theorem single_j_bound_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
      (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X) (j : NonzeroLattice d),
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω ^ 2) ∂P ≤
        ENNReal.ofReal (C * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_D, c_D, hCD, hcD, hdec⟩ :=
    fourier_coeff_decay_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos (9 * d + 82)
  obtain ⟨C_B1, hC_B1, hmode⟩ :=
    mode_forcing_bound_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos c_D hcD T hT
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (-((d : ℝ) + 2)) :=
    ⟨_, rfl⟩
  have hsumSig : Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (-((d : ℝ) + 2))) :=
    asmD_summable_rpow (d := d) ((d : ℝ) + 2) (by linarith)
  refine ⟨C_B1 * C_D ^ 2 * Sg ^ 2, mul_nonneg (mul_nonneg hC_B1 (sq_nonneg _)) (sq_nonneg _), ?_⟩
  intro m N hN Ω _ P _ X₀ W X a ha hflow j
  have hN0 : (0 : ℝ) < N := by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Lattice.jp j.1 ^ (-m + ((9 * d + 82 + d + 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.rpow_pos_of_pos (Torus.jp_pos _) _
  have hE2 : E ^ 2 = Lattice.jp j.1 ^ (2 * (-m + ((9 * d + 82 + d + 3 : ℕ) : ℝ))) := by
    rw [hE, ← Real.rpow_natCast, ← Real.rpow_mul (Torus.jp_pos j.1).le]
    congr 1
    push_cast
    ring
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = Real.sqrt (C_B1 / N) := ⟨_, rfl⟩
  have hc0nn : 0 ≤ c0 := by rw [hc0]; exact Real.sqrt_nonneg _
  have hc0sq : c0 ^ 2 = C_B1 / N := by
    rw [hc0, Real.sq_sqrt (div_nonneg hC_B1 hN0.le)]
  have hy : ∀ l : NonzeroLattice d, C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Lattice.jp l.1 ^ (8 * d + 80)
      = C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)) := by
    intro l
    have hx := Torus.jp_pos l.1
    rw [show (-((d : ℝ) + 2)) = -(((9 * d + 82 : ℕ) : ℝ) - ((8 * d + 80 : ℕ) : ℝ)) by push_cast; ring,
      asmD_rpow_neg_sub _ hx]
    ring
  have hXnn : ∀ l : NonzeroLattice d, 0 ≤ c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2))) := fun l =>
    mul_nonneg hc0nn (mul_nonneg (mul_nonneg hCD.le hE0.le) (Real.rpow_nonneg (Torus.jp_pos _).le _))
  have hSgnn : 0 ≤ Sg := by
    rw [hSg]
    exact tsum_nonneg fun l => Real.rpow_nonneg (Torus.jp_pos l.1).le _
  -- the Minkowski integrands `S_l(ω) = sup_t |J_l(a+t)(ω)|`
  obtain ⟨S, hS⟩ : ∃ S : NonzeroLattice d → Ω → ℝ≥0∞, ∀ l ω, S l ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ :=
    ⟨fun l ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖,
      fun _ _ => rfl⟩
  have hSmeas : ∀ l, AEMeasurable (S l) P := by
    intro l
    have e : S l = fun ω => ⨆ t ∈ ratTimes 0 T,
        ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ := funext (hS l)
    rw [e]
    refine AEMeasurable.biSup (ratTimes 0 T) (est4_ratTimes_countable 0 T) (fun t ht => ?_)
    have hmem := ht
    obtain ⟨⟨ht0, htT⟩, -⟩ := hmem
    have hb0 : 0 ≤ a + t := by linarith
    have hbH : a + t ≤ a + T := by linarith
    exact ((asmD_J_aemeas hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X (a + T) hflow j l
      (a + t) hb0 hbH).norm).ennreal_ofReal
  -- per-mode bound
  have hperl : ∀ l : NonzeroLattice d, ∫⁻ ω, (S l ω) ^ 2 ∂P ≤
      ENNReal.ofReal ((c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) ^ 2) := by
    intro l
    have hψ : Torus.IsSmooth (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x) :=
      asmB_sm_const_mul (HRS.FieldSingAux.isSmooth_realMode j) _
    have hreg := fourier_coeff_regular_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos _ hψ l
    have hγ : ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt (asmD_gam s hs0 hsd V β hβ ρβ m j l)
        (asmD_gam' s hs0 hsd V β hβ ρβ m j l x) (Set.Ici 0) x :=
      fun x hx => hreg.2.1 x hx
    have hγ' : ContinuousOn (asmD_gam' s hs0 hsd V β hβ ρβ m j l) (Set.Ici 0) := hreg.2.2
    have hbdl : ∀ v, 0 ≤ v → |asmD_gam s hs0 hsd V β hβ ρβ m j l v| ≤
          C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Real.exp (-c_D * v) ∧
        |asmD_gam' s hs0 hsd V β hβ ρβ m j l v| ≤
          C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Real.exp (-c_D * v) := by
      intro v hv
      have hdj := hdec m j v hv
      rw [← hE] at hdj
      exact asmD_coef_bound (d := d) (9 * d + 82) C_D c_D E hE0.le hCD.le
        (fun k => asmD_gam s hs0 hsd V β hβ ρβ m j k v) (fun k => asmD_gam' s hs0 hsd V β hβ ρβ m j k v)
        v hdj.1 hdj.2 l
    have hΓnn : 0 ≤ C_D * E / Lattice.jp l.1 ^ (9 * d + 82) :=
      div_nonneg (mul_nonneg hCD.le hE0.le) (pow_nonneg (Torus.jp_pos _).le _)
    have hmodel := hmode hN P X₀ W X a ha hflow l (C_D * E / Lattice.jp l.1 ^ (9 * d + 82)) hΓnn
      (asmD_gam s hs0 hsd V β hβ ρβ m j l) (asmD_gam' s hs0 hsd V β hβ ρβ m j l) hγ hγ'
      (fun v hv => ⟨(hbdl v hv).1, (hbdl v hv).2⟩)
    have hpt : ∀ ω, (S l ω) ^ 2 ≤ ⨆ t ∈ ratTimes 0 T,
        ENNReal.ofReal ((asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω) ^ 2) := by
      intro ω
      rw [hS l ω]
      refine (asmD_biSup_sq _ _).trans (iSup₂_mono fun t _ => le_of_eq ?_)
      rw [← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    refine (lintegral_mono hpt).trans (hmodel.trans (le_of_eq ?_))
    congr 1
    rw [mul_pow, hc0sq, ← hy l]
    ring
  -- the `1/2`-power of each mode
  have hterm : ∀ l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) := by
    intro l
    calc (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal ((c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (hperl l) (by norm_num)
      _ = ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_sq (hXnn l)]
  have hsumX : Summable (fun l : NonzeroLattice d =>
      c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
    (hsumSig.mul_left (C_D * E)).mul_left c0
  have hsumterm : ∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c0 * (C_D * E * Sg)) := by
    calc ∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ ∑' l : NonzeroLattice d, ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' l : NonzeroLattice d, c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
          (ENNReal.ofReal_tsum_of_nonneg hXnn hsumX).symm
      _ = ENNReal.ofReal (c0 * (C_D * E * Sg)) := by
          rw [tsum_mul_left, tsum_mul_left, hSg]
  -- the good event: the pointwise bound of the supremum over `t`
  have hgoodpw := asmD_pathwise hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X (a + T) hflow j
  have hpt' : ∀ᵐ ω ∂P, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
      (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω ^ 2)) ≤
      (∑' l : NonzeroLattice d, S l ω) ^ 2 := by
    filter_upwards [hgoodpw] with ω hω
    refine iSup₂_le fun t ht => ?_
    have hmem := ht
    obtain ⟨⟨ht0, htT⟩, -⟩ := hmem
    have hb0 : 0 ≤ a + t := by linarith
    have hbH : a + t ≤ a + T := by linarith
    obtain ⟨hI, hsum⟩ := hω (a + t) hb0 hbH
    set I := integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω with hIdef
    have h1 : ENNReal.ofReal (I ^ 2) = (ENNReal.ofReal ‖I‖) ^ 2 := by
      rw [← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    have h2 : ENNReal.ofReal ‖I‖ ≤ ∑' l : NonzeroLattice d, S l ω := by
      calc ENNReal.ofReal ‖I‖
          = ENNReal.ofReal ‖∑' l : NonzeroLattice d, asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ := by
            rw [hI.tsum_eq]
        _ ≤ ENNReal.ofReal (∑' l : NonzeroLattice d, ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖) :=
            ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hsum)
        _ = ∑' l : NonzeroLattice d, ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ :=
            ENNReal.ofReal_tsum_of_nonneg (fun l => norm_nonneg _) hsum
        _ ≤ ∑' l : NonzeroLattice d, S l ω := by
            refine ENNReal.tsum_le_tsum fun l => ?_
            rw [hS l ω]
            exact le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) =>
              ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖) t ht
    rw [h1]
    exact pow_le_pow_left₀ zero_le h2 2
  have hreal : (c0 * (C_D * E * Sg)) ^ 2 =
      C_B1 * C_D ^ 2 * Sg ^ 2 * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N := by
    rw [← hE2, mul_pow, hc0sq]
    ring
  have hGsnn : 0 ≤ c0 * (C_D * E * Sg) :=
    mul_nonneg hc0nn (mul_nonneg (mul_nonneg hCD.le hE0.le) hSgnn)
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω ^ 2) ∂P
      ≤ ∫⁻ ω, (∑' l : NonzeroLattice d, S l ω) ^ 2 ∂P := lintegral_mono_ae hpt'
    _ = ((∫⁻ ω, (∑' l : NonzeroLattice d, S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
          (asmD_rpow_half_sq _).symm
    _ ≤ (∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ zero_le (lintegral_sq_tsum_le P S hSmeas) 2
    _ ≤ (ENNReal.ofReal (c0 * (C_D * E * Sg))) ^ 2 := pow_le_pow_left₀ (zero_le) hsumterm 2
    _ = ENNReal.ofReal ((c0 * (C_D * E * Sg)) ^ 2) := (ENNReal.ofReal_pow hGsnn 2).symm
    _ ≤ ENNReal.ofReal (C_B1 * C_D ^ 2 * Sg ^ 2 * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) :=
          ENNReal.ofReal_le_ofReal (le_of_eq hreal)

/-! ### Second deliverable: measurability of the integrated centered forcing -/

/-- `ω ↦ integratedCenteredForcing … b ω` is a.e. measurable for `0 ≤ b ≤ H`. -/
theorem integratedCenteredForcing_aemeasurable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X) (j : NonzeroLattice d) (b : ℝ) (hb : 0 ≤ b)
    (hbH : b ≤ H) :
    AEMeasurable (fun ω => integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j b ω) P := by
  have hpw := asmD_pathwise hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X H hflow j
  refine aemeasurable_of_tendsto_metrizable_ae Filter.atTop
    (f := fun (S : Finset (NonzeroLattice d)) (ω : Ω) =>
      ∑ l ∈ S, asmD_J s hs0 hsd V β hβ ρβ m j l X b ω)
    (fun S => Finset.aemeasurable_fun_sum S fun l _ =>
      asmD_J_aemeas hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X H hflow j l b hb hbH) ?_
  filter_upwards [hpw] with ω hω
  exact (hω b hb hbH).1

end HRS.ME

end
