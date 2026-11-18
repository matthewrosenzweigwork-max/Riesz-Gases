import HRS.Kernel.GradReg
import HRS.Kernel.GradFourier

/-!
# The Fourier-side pairing equals the symmetrized real-space pairing

Auxiliary file of `HRS/Kernel/GradConv.lean` (proof of `rieszGrad_pairing_symmetrized`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

/-- the finite box `{k : |k|_∞ ≤ n}` of the lattice -/
def boxFinset (d n : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

theorem mem_boxFinset {n : ℕ} {k : Lattice d} : k ∈ boxFinset d n ↔ InBox n k := by
  simp only [boxFinset, Fintype.mem_piFinset, Finset.mem_Icc, InBox, abs_le]

theorem neg_mem_boxFinset {n : ℕ} {k : Lattice d} (hk : k ∈ boxFinset d n) : -k ∈ boxFinset d n := by
  rw [mem_boxFinset] at *
  intro i
  simpa [abs_neg] using hk i

theorem trig_expansion {φ : Torus d → ℝ} (hc : Continuous φ) {n : ℕ} (ht : IsTrigPoly n (coeffOf φ))
    (x : Torus d) :
    (φ x : ℂ) = ∑ k ∈ boxFinset d n, coeffOf φ k * Torus.mode k x := by
  set f : C(UnitAddTorus (Fin d), ℂ) := ⟨fun x => (φ x : ℂ), by fun_prop⟩ with hf
  have hcoef : ∀ k, UnitAddTorus.mFourierCoeff f k = coeffOf φ k := fun k => rfl
  have hsupp : ∀ k ∉ boxFinset d n, UnitAddTorus.mFourierCoeff f k = 0 := by
    intro k hk
    rw [hcoef]
    by_contra h
    exact hk (mem_boxFinset.2 (ht k h))
  have hsum : Summable (UnitAddTorus.mFourierCoeff f) := summable_of_ne_finset_zero hsupp
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum x
  have h2 : HasSum (fun k => UnitAddTorus.mFourierCoeff f k • UnitAddTorus.mFourier k x)
      (∑ k ∈ boxFinset d n, UnitAddTorus.mFourierCoeff f k • UnitAddTorus.mFourier k x) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by simp [hsupp k hk])
  have h3 := h.unique h2
  simp only [hcoef, smul_eq_mul] at h3
  exact h3

theorem integral_mul_trig {ψ φ : Torus d → ℝ} (hψ : Integrable ψ) (hc : Continuous φ) {n : ℕ}
    (ht : IsTrigPoly n (coeffOf φ)) :
    ((∫ x, ψ x * φ x : ℝ) : ℂ) = ∑ k ∈ boxFinset d n, coeffOf φ k * coeffOf ψ (-k) := by
  have hint : ∀ k : Lattice d, Integrable (fun x => (ψ x : ℂ) * Torus.mode k x) := by
    intro k
    have h1 : Integrable (fun x => (ψ x : ℂ)) := hψ.ofReal
    refine h1.mul_bdd (c := 1) (Torus.continuous_mode k).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by simp [Torus.norm_mode]
  rw [← integral_complex_ofReal]
  have hpt : ∀ x, ((ψ x * φ x : ℝ) : ℂ) =
      ∑ k ∈ boxFinset d n, coeffOf φ k * ((ψ x : ℂ) * Torus.mode k x) := by
    intro x
    push_cast
    rw [trig_expansion hc ht x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => (hint k).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, coeffOf_eq_integral ψ (-k)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [neg_neg]
  ring

/-- `⟨v, ∇g * f⟩` (cancellation convention) -/
def Phi (d : ℕ) (s : ℝ) (v : Euc d) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  inner ℝ v (convGradConv (periodicRieszGrad d s) f x)

theorem continuous_convGradConv_apply (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hc : Continuous f) {B L : ℝ} (hB : ∀ x, |f x| ≤ B) (hL : IsLipschitz L f) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) : Continuous (convGradConv (periodicRieszGrad d s) f) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 hsd
  exact hG.continuous_op hc hB hL hL0 hB0

theorem continuous_Phi (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d) {f : Torus d → ℝ}
    (hc : Continuous f) {B L : ℝ} (hB : ∀ x, |f x| ≤ B) (hL : IsLipschitz L f) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) : Continuous (Phi d s v f) :=
  continuous_const.inner (continuous_convGradConv_apply hd hs0 hsd hc hB hL hL0 hB0)

theorem inner_eq_sum (v w : Euc d) : inner ℝ v w = ∑ i, v i * w i := by
  simp [PiLp.inner_apply, mul_comm]

theorem coeffOf_Phi (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d) {f : Torus d → ℝ}
    (hc : Continuous f) {B L : ℝ} (hB : ∀ x, |f x| ≤ B) (hL : IsLipschitz L f) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) (k : Lattice d) :
    coeffOf (Phi d s v f) k =
      ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
        coeffOf f k := by
  have hcont := continuous_convGradConv_apply hd hs0 hsd hc hB hL hL0 hB0
  have hci : ∀ i, Continuous fun x => ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ) := fun i =>
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hcont)
  have hint : ∀ i, Integrable fun x => Torus.mode (-k) x *
      ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ) := fun i =>
    ((Torus.continuous_mode (-k)).mul (hci i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPhi : ∀ x, Torus.mode (-k) x * ((Phi d s v f x : ℝ) : ℂ) =
      ∑ i, (v i : ℂ) * (Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ)) := by
    intro x
    unfold Phi
    rw [inner_eq_sum]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [coeffOf_eq_integral]
  simp_rw [hPhi]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
  have hi : ∀ i, ∫ x, (v i : ℂ) * (Torus.mode (-k) x *
      ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ)) =
      (v i : ℂ) * ((∫ y, Torus.mode (-k) y * (f y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ))) := by
    intro i
    rw [integral_const_mul, coeff_convGradConv_lip hd hs0 hsd hc hB hL hL0 hB0 k i]
  simp_rw [hi]
  rw [coeffOf_eq_integral f k, inner_eq_sum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Lattice.toEuc]
  ring

theorem coeffOf_neg_conj (φ : Torus d → ℝ) (k : Lattice d) : coeffOf φ (-k) = conj (coeffOf φ k) := by
  rw [coeffOf_eq_integral, coeffOf_eq_integral, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal, neg_neg]
  rw [Torus.mode_neg k x]
  simp

theorem fourier_side (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    {u w : Torus d → ℝ} (hu : Continuous u) {Bu Lu : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hLu : IsLipschitz Lu u) (hLu0 : 0 ≤ Lu) (hBu0 : 0 ≤ Bu)
    (hw : Continuous w) {Bw Lw : ℝ} (hBw : ∀ x, |w x| ≤ Bw)
    (hLw : IsLipschitz Lw w) (hLw0 : 0 ≤ Lw) (hBw0 : 0 ≤ Bw) {n : ℕ}
    (hwt : IsTrigPoly n (coeffOf w)) :
    (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
        (coeffOf u k * conj (coeffOf w k))).re = ∫ x, Phi d s v u x * w x ∧
      ∫ x, u x * Phi d s v w x = -(∫ x, Phi d s v u x * w x) := by
  set c : Lattice d → ℂ := fun k =>
    (2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ) with hc
  have hcneg : ∀ k, c (-k) = - c k := by
    intro k
    simp only [hc]
    have h1 : (inner ℝ v (Lattice.toEuc (-k)) : ℝ) = -(inner ℝ v (Lattice.toEuc k)) := by
      have : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
      rw [this, inner_neg_right]
    rw [h1, HRS.rieszCoeff_neg]
    push_cast
    ring
  have hP1 := coeffOf_Phi hd hs0 hsd v hu hBu hLu hLu0 hBu0
  have hP0 := coeffOf_Phi hd hs0 hsd v hw hBw hLw hLw0 hBw0
  have hPhi1c := continuous_Phi hd hs0 hsd v hu hBu hLu hLu0 hBu0
  have hPhi0c := continuous_Phi hd hs0 hsd v hw hBw hLw hLw0 hBw0
  have hPt : IsTrigPoly n (coeffOf (Phi d s v w)) := by
    intro k hk
    apply hwt
    intro h0
    apply hk
    rw [hP0, h0, mul_zero]
  have hint1 : Integrable (Phi d s v u) :=
    hPhi1c.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_u : Integrable u := hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hE := integral_mul_trig hint1 hw hwt
  have hE' := integral_mul_trig hint_u hPhi0c hPt
  -- reindexing by `k ↦ -k`
  have hreidx : ∀ g : Lattice d → ℂ, ∑ k ∈ boxFinset d n, g (-k) = ∑ k ∈ boxFinset d n, g k := by
    intro g
    exact Finset.sum_equiv (Equiv.neg _) (fun k => by
      simp only [Equiv.neg_apply]
      exact ⟨neg_mem_boxFinset, fun h => by simpa using neg_mem_boxFinset h⟩) (fun k _ => rfl)
  have hP1' : ∀ k, coeffOf (Phi d s v u) k = c k * coeffOf u k := hP1
  have hP0' : ∀ k, coeffOf (Phi d s v w) k = c k * coeffOf w k := hP0
  set S : ℂ := ∑ k ∈ boxFinset d n, c k * (coeffOf u k * conj (coeffOf w k)) with hS
  have hE_S : ((∫ x, Phi d s v u x * w x : ℝ) : ℂ) = S := by
    rw [hE, ← hreidx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_neg, hP1', coeffOf_neg_conj w k]
    ring
  have hE'_S : ((∫ x, u x * Phi d s v w x : ℝ) : ℂ) = -S := by
    rw [hE', ← hreidx, hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_neg, hP0', hcneg, coeffOf_neg_conj w k]
    ring
  have hreal : ∀ x : ℝ, ((x : ℝ) : ℂ) = S → x = S.re := fun x hx => by rw [← hx]; simp
  have hsum_eq : (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) *
      ((rieszCoeff d s k : ℝ) : ℂ)) * (coeffOf u k * conj (coeffOf w k))) = S := by
    rw [hS]
    refine tsum_eq_sum fun k hk => ?_
    have : coeffOf w k = 0 := by
      by_contra h
      exact hk (mem_boxFinset.2 (hwt k h))
    simp [this]
  rw [hsum_eq]
  have h1 := hreal _ hE_S
  refine ⟨h1.symm, ?_⟩
  have h2 : ((∫ x, u x * Phi d s v w x : ℝ) : ℂ) = (((-(∫ x, Phi d s v u x * w x)) : ℝ) : ℂ) := by
    rw [hE'_S, ← hE_S]; push_cast; ring
  exact_mod_cast h2

/-! ### The real-space side -/

theorem kern_comb (G : Torus d → Euc d) (a w : Torus d → ℝ) (x z : Torus d) :
    kern G (fun y => a y * w y) x z - a x • kern G w x z = (w (x - z) * (a (x - z) - a x)) • G z := by
  unfold kern
  split_ifs
  · simp only [smul_smul, ← sub_smul]
    congr 1
    ring
  · simp only [smul_smul, ← sub_smul]
    congr 1
    ring

theorem prod_data {a w : Torus d → ℝ} {A La Bw Lw : ℝ} (hA : ∀ x, |a x| ≤ A) (hLa : IsLipschitz La a)
    (hA0 : 0 ≤ A) (hBw : ∀ x, |w x| ≤ Bw) (hLw : IsLipschitz Lw w) (hBw0 : 0 ≤ Bw) :
    (∀ y, |a y * w y| ≤ A * Bw) ∧ IsLipschitz (A * Lw + Bw * La) (fun y => a y * w y) := by
  refine ⟨fun y => ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul (hA y) (hBw y) (abs_nonneg _) hA0
  · intro x y
    have h1 : a x * w x - a y * w y = a x * (w x - w y) + w y * (a x - a y) := by ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have := hLw x y
    have := hLa x y
    have := tdist_nonneg x y
    calc |a x| * |w x - w y| + |w y| * |a x - a y| ≤ A * (Lw * tdist x y) + Bw * (La * tdist x y) := by
          gcongr
          · exact hA x
          · exact hBw y
      _ = _ := by ring

theorem Phi_comb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    {a w : Torus d → ℝ} (ha : Continuous a) {A La : ℝ} (hA : ∀ x, |a x| ≤ A) (hLa : IsLipschitz La a)
    (hLa0 : 0 ≤ La) (hA0 : 0 ≤ A) (hw : Continuous w) {Bw Lw : ℝ} (hBw : ∀ x, |w x| ≤ Bw)
    (hLw : IsLipschitz Lw w) (hLw0 : 0 ≤ Lw) (hBw0 : 0 ≤ Bw) (x : Torus d) :
    Phi d s v (fun y => a y * w y) x - a x * Phi d s v w x =
      ∫ y, inner ℝ v (periodicRieszGrad d s (x - y)) * (w y * (a y - a x)) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 hsd
  have hu : Continuous fun y => a y * w y := ha.mul hw
  obtain ⟨huB, huL⟩ := prod_data hA hLa hA0 hBw hLw hBw0
  have huL0 : 0 ≤ A * Lw + Bw * La := by positivity
  have huB0 : 0 ≤ A * Bw := by positivity
  have hk1 := integrable_kern hG (hu.measurable) huB huL huL0 huB0 x
  have hk2 := integrable_kern hG (hw.measurable) hBw hLw hLw0 hBw0 x
  have e1 : ∀ f : Torus d → ℝ, Integrable (kern (periodicRieszGrad d s) f x) →
      Phi d s v f x = ∫ z, inner ℝ v (kern (periodicRieszGrad d s) f x z) := by
    intro f hf
    unfold Phi
    rw [convGradConv_eq_integral_kern, integral_inner hf]
  have hI1 : Integrable fun z => inner ℝ v (kern (periodicRieszGrad d s) (fun y => a y * w y) x z) :=
    hk1.const_inner v
  have hI2 : Integrable fun z => inner ℝ v (kern (periodicRieszGrad d s) w x z) := hk2.const_inner v
  rw [e1 _ hk1, e1 _ hk2, ← integral_const_mul, ← integral_sub hI1 (hI2.const_mul _)]
  have hpt : ∀ z, inner ℝ v (kern (periodicRieszGrad d s) (fun y => a y * w y) x z) -
      a x * inner ℝ v (kern (periodicRieszGrad d s) w x z) =
      inner ℝ v (periodicRieszGrad d s z) * (w (x - z) * (a (x - z) - a x)) := by
    intro z
    have := congrArg (fun q => inner ℝ v q) (kern_comb (periodicRieszGrad d s) a w x z)
    simp only [inner_sub_right, inner_smul_right] at this
    rw [this]; ring
  simp_rw [hpt]
  rw [← integral_sub_left_eq_self (fun z => inner ℝ v (periodicRieszGrad d s z) * (w (x - z) * (a (x - z) - a x))) volume x]
  simp only [sub_sub_cancel]

theorem realspace_identity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    {a w : Torus d → ℝ} (ha : Continuous a) {A La : ℝ} (hA : ∀ x, |a x| ≤ A) (hLa : IsLipschitz La a)
    (hLa0 : 0 ≤ La) (hA0 : 0 ≤ A) (hw : Continuous w) {Bw Lw : ℝ} (hBw : ∀ x, |w x| ≤ Bw)
    (hLw : IsLipschitz Lw w) (hLw0 : 0 ≤ Lw) (hBw0 : 0 ≤ Bw) :
    ∫ p : Torus d × Torus d,
        inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1) =
      (∫ x, Phi d s v (fun y => a y * w y) x * w x) - ∫ x, a x * w x * Phi d s v w x := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 hsd
  have hu : Continuous fun y => a y * w y := ha.mul hw
  obtain ⟨huB, huL⟩ := prod_data hA hLa hA0 hBw hLw hBw0
  have huL0 : 0 ≤ A * Lw + Bw * La := by positivity
  have huB0 : 0 ≤ A * Bw := by positivity
  have hC0 := hG.hC0
  -- the dominating function
  set H : Torus d → ℝ := fun z => ‖v‖ * (Bw * Bw * La) * (C * (‖z‖ ^ (-s) + d)) with hH
  have hHint : Integrable H := by
    have h1 := integrable_norm_rpow_neg hG.pos hG.hsd
    exact ((h1.add (integrable_const (d : ℝ))).const_mul C).const_mul _
  have hconv := Integrable.convolution_integrand (μ := (volume : Measure (Torus d)))
    (ν := (volume : Measure (Torus d))) (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_const (1 : ℝ)) hHint
  set f : Torus d × Torus d → ℝ := fun p =>
    inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1) with hf
  have hmeas : Measurable f := by
    have hGm := hG.meas
    have h1 : Measurable fun p : Torus d × Torus d => periodicRieszGrad d s (p.1 - p.2) :=
      hGm.comp (measurable_fst.sub measurable_snd)
    have h2 : Measurable fun p : Torus d × Torus d => inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) :=
      (continuous_const.inner continuous_id).measurable.comp h1
    exact ((h2.mul (hw.measurable.comp measurable_fst)).mul (hw.measurable.comp measurable_snd)).mul
      ((ha.measurable.comp measurable_snd).sub (ha.measurable.comp measurable_fst))
  have hbd : ∀ p : Torus d × Torus d, ‖f p‖ ≤ H (p.1 - p.2) := by
    intro p
    set z := p.1 - p.2 with hz
    have hHnn : 0 ≤ H z := by
      simp only [hH]
      have := Real.rpow_nonneg (norm_nonneg z) (-s)
      positivity
    by_cases hz0 : z = 0
    · have : p.1 = p.2 := sub_eq_zero.mp hz0
      have : f p = 0 := by simp [hf, this]
      rw [this, norm_zero]; exact hHnn
    · have hdist : |a p.2 - a p.1| ≤ La * tdist z 0 := by
        refine (hLa p.2 p.1).trans ?_
        rw [tdist_eq_sub_zero, hz, ← neg_sub, tdist_neg]
      have hC' := hG.norm_mul_tdist_le z hz0
      have hw1 := hBw p.1
      have hw2 := hBw p.2
      have hin : |inner ℝ v (periodicRieszGrad d s z)| ≤ ‖v‖ * ‖periodicRieszGrad d s z‖ := by
        have := abs_real_inner_le_norm v (periodicRieszGrad d s z)
        exact this
      rw [Real.norm_eq_abs]
      simp only [hf, abs_mul]
      have ht0 := tdist_nonneg z 0
      calc |inner ℝ v (periodicRieszGrad d s (p.1 - p.2))| * |w p.1| * |w p.2| * |a p.2 - a p.1|
          ≤ (‖v‖ * ‖periodicRieszGrad d s z‖) * Bw * Bw * (La * tdist z 0) := by gcongr
        _ = ‖v‖ * (Bw * Bw * La) * (tdist z 0 * ‖periodicRieszGrad d s z‖) := by ring
        _ ≤ ‖v‖ * (Bw * Bw * La) * (C * (‖z‖ ^ (-s) + d)) := by gcongr
  have hint : Integrable f := by
    refine (hconv.congr (Filter.Eventually.of_forall fun p => ?_)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
    simp [hH]
  have hfub : ∫ p, f p = ∫ x, ∫ y, f (x, y) := integral_prod f hint
  rw [hfub]
  have hin : ∀ x, ∫ y, f (x, y) = w x * (Phi d s v (fun y => a y * w y) x - a x * Phi d s v w x) := by
    intro x
    rw [Phi_comb hd hs0 hsd v ha hA hLa hLa0 hA0 hw hBw hLw hLw0 hBw0 x, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf]
    ring
  simp_rw [hin]
  have hP1 : Continuous (Phi d s v (fun y => a y * w y)) :=
    continuous_Phi hd hs0 hsd v hu huB huL huL0 huB0
  have hP2 : Continuous (Phi d s v w) := continuous_Phi hd hs0 hsd v hw hBw hLw hLw0 hBw0
  have i1 : Integrable fun x => Phi d s v (fun y => a y * w y) x * w x :=
    (hP1.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable fun x => a x * w x * Phi d s v w x :=
    ((ha.mul hw).mul hP2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

end HRS.KernelGrad
