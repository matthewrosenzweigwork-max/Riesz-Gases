import HRS.Torus.Sobolev
import HRS.PDE.MeanFieldPairSeries
import HRS.Equilibrium.PairCorrection
import HRS.PDE.MeanField
import HRS.PDE.MeanFieldAprioriSubord

/-!
# Row 4.17, packet M5 (part A): proofs of two specification statements

* `fourier_expansion_tail_proof` (Fourier reconstruction with tails in `posSeminorm`);
* `equilibriumGen_sobolev_bound_proof` (the generator loses two derivatives in Sobolev norms).

Statements copied verbatim from `HRS/ME/Spec417Fourier.lean`.  The second proof goes through the
coefficient level: `A f = projMean (backwardGenerator f)`, the forward generator splits into the
Laplacian (`hs_mult`) and a lower-order remainder bounded by `exists_forwardGen_loss`, and the
zero mode of `A f` is controlled by Parseval and Hölder.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.ME

variable {d : ℕ}

open HRS

/-- A real multiple of a real mode is a single trigonometric term, with the coefficient
sum `|a| + |b| = √2 |γ|`. -/
theorem fourierTailA_mul_realMode_trig (γ : ℝ) (k : NonzeroLattice d) :
    ∃ a b : ℝ, (fun x => γ * Torus.realMode k x) = HRS.PDE.MFPair.trigTerm a b k.1 ∧
      |a| + |b| = Real.sqrt 2 * |γ| := by
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  unfold Torus.realMode
  split_ifs
  · refine ⟨γ * Real.sqrt 2, 0, ?_, ?_⟩
    · funext x
      simp only [HRS.PDE.MFPair.trigTerm, zero_mul, add_zero]
      ring
    · simp only [abs_mul, abs_of_nonneg hs2, abs_zero, add_zero]
      ring
  · refine ⟨0, γ * Real.sqrt 2, ?_, ?_⟩
    · funext x
      simp only [HRS.PDE.MFPair.trigTerm, zero_mul, zero_add]
      ring
    · simp only [abs_mul, abs_of_nonneg hs2, abs_zero, zero_add]
      ring

theorem fourierTailA_mul_realMode_isCk (γ : ℝ) (k : NonzeroLattice d) (L : ℕ) :
    Torus.IsCk (L : WithTop ℕ∞) (fun x => γ * Torus.realMode k x) := by
  obtain ⟨a, b, h1, -⟩ := fourierTailA_mul_realMode_trig γ k
  rw [h1]
  exact HRS.PDE.MFPair.trigTerm_isCk a b k.1 L

theorem fourierTailA_mul_realMode_cbNorm (γ : ℝ) (k : NonzeroLattice d) (L : ℕ) :
    Torus.cbNorm L (fun x => γ * Torus.realMode k x) ≤
      ((L : ℝ) + 1) * (Real.sqrt 2 * |γ| * Lattice.jp k.1 ^ L) := by
  obtain ⟨a, b, h1, h2⟩ := fourierTailA_mul_realMode_trig γ k
  rw [h1]
  refine (HRS.PDE.MFPair.cbNorm_trigTerm_le a b k.1 L).trans (le_of_eq ?_)
  rw [h2]

/-- `(fourier_expansion_tail)`: Fourier reconstruction of `g - mean g` with tails in `posSeminorm`. -/
theorem fourier_expansion_tail_proof (g : Torus d → ℝ) (hg : ∀ n : ℕ, Torus.IsCk n g) (K : ℕ)
    (hs : Summable fun l : NonzeroLattice d => Lattice.jp l.1 ^ K * |Torus.funRealCoeff g l|) :
    (∀ x, HasSum (fun l : NonzeroLattice d => Torus.funRealCoeff g l * Torus.realMode l x)
        (g x - Torus.mean g)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset (NonzeroLattice d),
      posSeminorm K (fun x => g x - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l x) ≤
        C * ∑' l : {l : NonzeroLattice d // l ∉ S}, Lattice.jp l.1.1 ^ K * |Torus.funRealCoeff g l.1| := by
  have hcont : Continuous g := Torus.continuous_of_continuous_lift (ContDiff.continuous (hg 0))
  have hfc : Summable fun k : Lattice d => ‖Torus.fcoef g k‖ :=
    Torus.summable_fcoef_of_contDiff (fun n => hg n)
  have hexp : ∀ x, HasSum (fun l : NonzeroLattice d => Torus.funRealCoeff g l * Torus.realMode l x)
      (g x - Torus.mean g) := fun x => Torus.hasSum_realExpansion hcont hfc x
  refine ⟨hexp, (K : ℝ) * ((K : ℝ) + 1) ^ 2 * Real.sqrt 2, by positivity, fun S => ?_⟩
  -- The tail after the finite set `S`, as a series indexed by the complement.
  have hsplit : ∀ y : Torus d, (∑' i : {l : NonzeroLattice d // l ∉ S},
      Torus.funRealCoeff g i.1 * Torus.realMode i.1 y) =
      g y - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l y := by
    intro y
    have h1 := (hexp y).summable.sum_add_tsum_subtype_compl S
    rw [(hexp y).tsum_eq] at h1
    linarith
  have hfun : (fun x => g x - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l x) =
      fun y => ∑' i : {l : NonzeroLattice d // l ∉ S}, Torus.funRealCoeff g i.1 * Torus.realMode i.1 y :=
    funext fun y => (hsplit y).symm
  rw [hfun]
  have hsub : Summable (fun i : {l : NonzeroLattice d // l ∉ S} =>
      Lattice.jp i.1.1 ^ K * |Torus.funRealCoeff g i.1|) :=
    hs.comp_injective Subtype.val_injective
  have hcb : ∀ i : {l : NonzeroLattice d // l ∉ S},
      Torus.cbNorm K (fun x => Torus.funRealCoeff g i.1 * Torus.realMode i.1 x) ≤
        (Real.sqrt 2 * ((K : ℝ) + 1)) * (Lattice.jp i.1.1 ^ K * |Torus.funRealCoeff g i.1|) := by
    intro i
    refine (fourierTailA_mul_realMode_cbNorm _ i.1 K).trans (le_of_eq ?_)
    ring
  have hsumG : Summable (fun i : {l : NonzeroLattice d // l ∉ S} =>
      Torus.cbNorm K (fun x => Torus.funRealCoeff g i.1 * Torus.realMode i.1 x)) :=
    Summable.of_nonneg_of_le (fun i => HRS.PDE.MFPair.cbNorm_nonneg_ps K _) hcb (hsub.mul_left _)
  obtain ⟨hCk, hcbF⟩ := HRS.PDE.MFPair.isCk_tsum_cbNorm_ps K
    (fun (i : {l : NonzeroLattice d // l ∉ S}) (x : Torus d) =>
      Torus.funRealCoeff g i.1 * Torus.realMode i.1 x)
    (fun i => fourierTailA_mul_realMode_isCk _ i.1 K) hsumG
  -- bound the tail's cbNorm by the weighted coefficient sum
  have htail : Torus.cbNorm K (fun y => ∑' i : {l : NonzeroLattice d // l ∉ S},
      Torus.funRealCoeff g i.1 * Torus.realMode i.1 y) ≤
      ((K : ℝ) + 1) * ((Real.sqrt 2 * ((K : ℝ) + 1)) *
        ∑' i : {l : NonzeroLattice d // l ∉ S}, Lattice.jp i.1.1 ^ K * |Torus.funRealCoeff g i.1|) := by
    refine hcbF.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Summable.tsum_le_tsum hcb hsumG (hsub.mul_left _)).trans (le_of_eq ?_)
    rw [← tsum_mul_left]
  -- posSeminorm is bounded by `K` times the top cbNorm
  unfold posSeminorm
  calc ∑ j ∈ Finset.Icc 1 K, ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift
        (fun y => ∑' i : {l : NonzeroLattice d // l ∉ S},
          Torus.funRealCoeff g i.1 * Torus.realMode i.1 y)) x‖
      ≤ ∑ j ∈ Finset.Icc 1 K, Torus.cbNorm K (fun y => ∑' i : {l : NonzeroLattice d // l ∉ S},
          Torus.funRealCoeff g i.1 * Torus.realMode i.1 y) :=
        Finset.sum_le_sum fun j hj =>
          HRS.PDE.MFPair.sup_le_cb_ps hCk (Finset.mem_Icc.mp hj).2
    _ = (K : ℝ) * Torus.cbNorm K (fun y => ∑' i : {l : NonzeroLattice d // l ∉ S},
          Torus.funRealCoeff g i.1 * Torus.realMode i.1 y) := by
        simp
    _ ≤ (K : ℝ) * (((K : ℝ) + 1) * ((Real.sqrt 2 * ((K : ℝ) + 1)) *
          ∑' i : {l : NonzeroLattice d // l ∉ S}, Lattice.jp i.1.1 ^ K * |Torus.funRealCoeff g i.1|)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (K : ℝ) * ((K : ℝ) + 1) ^ 2 * Real.sqrt 2 *
          ∑' i : {l : NonzeroLattice d // l ∉ S}, Lattice.jp i.1.1 ^ K * |Torus.funRealCoeff g i.1| := by
        ring

/-! ### Part 2: the generator bound `equilibriumGen_sobolev_bound` -/

theorem fourierTailA_jp_rpow_two (k : Lattice d) :
    Lattice.jp k ^ (2 : ℝ) = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  unfold Lattice.jp
  rw [Real.rpow_two, Real.sq_sqrt (by positivity)]

theorem fourierTailA_hs_mono {m m' : ℝ} {c : PDE.Coeff d} (h : m ≤ m') (hc : PDE.MemHs m' c) :
    PDE.MemHs m c ∧ PDE.hsNorm m c ≤ PDE.hsNorm m' c := by
  have := PDE.MFAdjoint.hs_lower (sub_nonneg.mpr h) hc
  rwa [sub_sub_cancel] at this

theorem fourierTailA_lap (ν m : ℝ) {F : PDE.Coeff d} (hF : PDE.MemHs (m + 2) F) :
    PDE.MemHs m (fun k => (ν : ℂ) * PDE.laplaceCoeff F k) ∧
      PDE.hsNorm m (fun k => (ν : ℂ) * PDE.laplaceCoeff F k) ≤ |ν| * PDE.hsNorm (m + 2) F := by
  have hb : ∀ k : Lattice d, ‖(ν : ℂ) * PDE.laplaceCoeff F k‖ ≤
      |ν| * Lattice.jp k ^ (2 : ℝ) * ‖F k‖ := by
    intro k
    have hp : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
    have e1 : ‖(ν : ℂ) * PDE.laplaceCoeff F k‖ =
        |ν| * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖F k‖ := by
      unfold PDE.laplaceCoeff
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hp]
      ring
    rw [e1, fourierTailA_jp_rpow_two]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ν)) (norm_nonneg _)
  have h := PDE.MFAdjoint.hs_mult (m := m + 2) (γ := 2) (C := |ν|) (c := F)
    (e := fun k => (ν : ℂ) * PDE.laplaceCoeff F k) (abs_nonneg ν) hF hb
  rw [add_sub_cancel_right] at h
  exact h

theorem fourierTailA_const_delta (c m : ℝ) :
    PDE.MemHs m (fun k => (c : ℂ) * PDE.deltaCoeff (0 : Lattice d) k) ∧
      PDE.hsNorm m (fun k => (c : ℂ) * PDE.deltaCoeff (0 : Lattice d) k) ≤ |c| := by
  have hb : ∀ k : Lattice d, ‖(c : ℂ) * PDE.deltaCoeff (0 : Lattice d) k‖ ≤
      |c| * Lattice.jp k ^ (0 : ℝ) * ‖PDE.deltaCoeff (0 : Lattice d) k‖ := by
    intro k
    exact le_of_eq (by simp only [Real.rpow_zero, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs])
  have h := PDE.MFAdjoint.hs_mult (m := m) (γ := 0) (C := |c|)
    (c := PDE.deltaCoeff (0 : Lattice d)) (e := fun k => (c : ℂ) * PDE.deltaCoeff (0 : Lattice d) k)
    (abs_nonneg c) (PDE.MFAdjoint.memHs_deltaCoeff m) hb
  rw [sub_zero, PDE.MFAdjoint.hsNorm_deltaCoeff_zero, mul_one] at h
  exact h

theorem fourierTailA_integral_sq (φ : Torus d → ℝ) (hφ : MemLp φ 2 volume)
    (hS : PDE.MemHs 0 (PDE.coeffOf φ)) :
    ∫ x, φ x ^ 2 = PDE.hsNormSq 0 (PDE.coeffOf φ) := by
  have hSob : MemSobolev 0 φ := PDE.memSobolev_of_memHs 0 φ hφ hS
  have hT : 0 ≤ (Torus.mean φ) ^ 2 + ∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (2 * (0 : ℝ)) * Torus.funRealCoeff φ k ^ 2 :=
    add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
  rw [(PDE.hsNormSq_coeffOf 0 φ hSob).2, Torus.parseval_realCoeff φ hφ]
  unfold sobolevNorm
  rw [Real.sq_sqrt hT]
  simp

theorem fourierTailA_integrable (g : Torus d → ℝ) (hg : Continuous g) : Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem equilibriumGen_sobolev_bound_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ f) ≤ C * sobolevNorm ((n : ℝ) + 2) f := by
  obtain ⟨D, hD⟩ : ∃ D : DynData d, D = PDE.mfData d s hs0 hsd V β hβ := ⟨_, rfl⟩
  have hDs : D.s = s := by rw [hD]; rfl
  have hDM : D.M = -1 := by rw [hD]; rfl
  have hDV : D.V = V := by rw [hD]; rfl
  have hDinv : D.invβ = β⁻¹ := by rw [hD]; rfl
  have hK : PDE.ClassicalAux.ConvKernelFacts d D.s := PDE.ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 V := PDE.ClassicalAux.isCk_of_le (by norm_num) hV
  have hV2 : Torus.IsCk 2 V := PDE.ClassicalAux.isCk_of_le (by norm_num) hV
  have hρ1 : Torus.IsCk 1 ρβ := PDE.ClassicalAux.isCk_of_le (by norm_num) hρS
  have hρ2 : Torus.IsCk 2 ρβ := PDE.ClassicalAux.isCk_of_le (by norm_num) hρS
  have hρC : Continuous ρβ := Torus.continuous_of_continuous_lift (ContDiff.continuous hρ1)
  have hprob : IsProbDensity ρβ := hρβ.1
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρC.continuousOn
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ρβ x0 := ⟨_, rfl⟩
  have hM : ∀ x, ρβ x ≤ M := fun x => by
    rw [hMdef]; exact isMaxOn_iff.mp hx0 x (Set.mem_univ x)
  have hM0 : 0 ≤ M := by rw [hMdef]; exact (hpos x0).le
  -- loss bound at index `n + 2`, with a fixed auxiliary regularity index `r`
  have hiN : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  obtain ⟨Cl, hCl, hloss⟩ := PDE.MFAdjoint.exists_forwardGen_loss hd s hs0 hsd ((n : ℝ) + 2)
    ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) hiN (by linarith)
  have hρH : PDE.MemHs ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) :=
    PDE.MFSemigroup.memHs_of_isSmooth hρS _
  have hVH : PDE.MemHs ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V) :=
    PDE.MFSemigroup.memHs_of_isSmooth hV _
  have ha := PDE.MFAdjoint.aExp_spec s hsd
  refine ⟨(1 + M) * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
      PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) + |β⁻¹|),
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg hCl (add_nonneg
      (PDE.MFAdjoint.hsNorm_nonneg' _ _) (PDE.MFAdjoint.hsNorm_nonneg' _ _))) (abs_nonneg _)), ?_⟩
  intro f hf
  have hf2 : Torus.IsCk 2 f := PDE.ClassicalAux.isCk_of_le (by norm_num) hf
  have hfC : Continuous f := Torus.continuous_of_continuous_lift (ContDiff.continuous hf2)
  have hFH : PDE.MemHs ((n : ℝ) + 2) (PDE.coeffOf f) := PDE.MFSemigroup.memHs_of_isSmooth hf _
  -- the backward generator and its coefficients
  have hbgC := PDE.ClassicalPart.continuous_backwardGenerator D hK (by rw [hDV]; exact hV1) hρ1 hf2
  have hbgc := PDE.ClassicalAux.coeffOf_backwardGenerator D hK (by rw [hDV]; exact hV1) hρ1 hf2
  obtain ⟨φ, hφ⟩ : ∃ φ : Torus d → ℝ, φ = backwardGenerator D ρβ f := ⟨_, rfl⟩
  rw [← hφ] at hbgC hbgc
  -- the loss bound for `forwardGen F`
  have hlossF := hloss D hDs hDM ρβ hρC hρH (by rw [hDV]; exact hVH) (PDE.coeffOf f) hFH
  rw [hDinv, hDV] at hlossF
  obtain ⟨RF, hRF⟩ : ∃ R : PDE.Coeff d, R = PDE.forwardGen D ρβ (PDE.coeffOf f) -
      fun k => ((β⁻¹ : ℝ) : ℂ) * PDE.laplaceCoeff (PDE.coeffOf f) k := ⟨_, rfl⟩
  rw [← hRF] at hlossF
  obtain ⟨L, hL⟩ : ∃ L : PDE.Coeff d,
      L = fun k => ((β⁻¹ : ℝ) : ℂ) * PDE.laplaceCoeff (PDE.coeffOf f) k := ⟨_, rfl⟩
  have hLapH : PDE.MemHs (n : ℝ) L := by rw [hL]; exact (fourierTailA_lap (β⁻¹) (n : ℝ) hFH).1
  have hLapN : PDE.hsNorm (n : ℝ) L ≤ |β⁻¹| * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := by
    rw [hL]; exact (fourierTailA_lap (β⁻¹) (n : ℝ) hFH).2
  have hRFn0 := fourierTailA_hs_mono (m := (n : ℝ)) (m' := (n : ℝ) + 2 - PDE.MFAdjoint.aExp d s)
    (by linarith [ha.2.1]) hlossF.1
  have hRFN : PDE.hsNorm (n : ℝ) RF ≤ Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
      PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) :=
    hRFn0.2.trans hlossF.2
  have hRF0 := fourierTailA_hs_mono (m := 0) (m' := (n : ℝ)) (Nat.cast_nonneg n) hRFn0.1
  have hL0 := fourierTailA_hs_mono (m := 0) (m' := (n : ℝ)) (Nat.cast_nonneg n) hLapH
  -- decomposition `forwardGen F = RF + L` (pointwise)
  have hGRL : PDE.forwardGen D ρβ (PDE.coeffOf f) = fun k => RF k + L k := by
    funext k
    rw [hRF, hL]
    simp only [Pi.sub_apply]
    ring
  have hGRLk : ∀ k, PDE.forwardGen D ρβ (PDE.coeffOf f) k = RF k + L k := fun k => congrFun hGRL k
  -- the centering constant `c = μ_β(backward generator)`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = pair (withDensityReal ρβ) φ := ⟨_, rfl⟩
  have hEq0 := PDE.equilibrium_operator_order hd s hs0 hsd β hβ V hV2 ρβ hρβ hρ2 hpos f hf2
  rw [← hD, ← hφ] at hEq0
  have hAF : PDE.equilibriumGen d s ρβ β⁻¹ f = fun x => φ x - c := by
    rw [← hEq0, hc]; rfl
  obtain ⟨e', he'⟩ : ∃ e' : PDE.Coeff d, ∀ k, e' k = ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k :=
    ⟨fun k => ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k, fun k => rfl⟩
  have hcdelta := fourierTailA_const_delta (d := d) (-c) (n : ℝ)
  have he'fun : e' = fun k => ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k := funext he'
  rw [← he'fun] at hcdelta
  -- coefficients of `A f`
  have hAcoef : PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f) =
      fun k => RF k + (L k + e' k) := by
    funext k
    rw [hAF]
    have hsub : PDE.coeffOf (fun x => φ x - c) k = PDE.coeffOf φ k - PDE.coeffOf (fun _ : Torus d => c) k :=
      PDE.MFApriori.coeffOf_sub φ (fun _ => c) hbgC continuous_const k
    rw [hsub, PDE.coeffOf_const, hbgc, hGRLk, he' k]
    push_cast
    ring
  have hAFMem : PDE.MemHs (n : ℝ) (PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f)) := by
    rw [hAcoef]
    exact (PDE.MFAdjoint.hs_add_le (n : ℝ) hRFn0.1 (PDE.MFAdjoint.hs_add_le (n : ℝ) hLapH hcdelta.1).1).1
  have hAFL2 : MeasureTheory.MemLp (PDE.equilibriumGen d s ρβ β⁻¹ f) 2 volume := by
    rw [hAF]; exact PDE.ClassicalAux.memLp_two_of_continuous (hbgC.sub continuous_const)
  have hAFS : MemSobolev (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ f) :=
    PDE.memSobolev_of_memHs _ _ hAFL2 hAFMem
  -- the centering constant `c = μ_β(backward generator)` is controlled by `‖bg f‖_{L²}`
  have hφL2 : MeasureTheory.MemLp φ 2 volume := PDE.ClassicalAux.memLp_two_of_continuous hbgC
  have hφ0 : PDE.MemHs 0 (PDE.coeffOf φ) := by
    rw [hbgc, hGRL]
    exact (PDE.MFAdjoint.hs_add_le 0 hRF0.1 hL0.1).1
  have hGN : PDE.hsNorm 0 (PDE.coeffOf φ) ≤ PDE.hsNorm 0 RF + PDE.hsNorm 0 L := by
    rw [hbgc, hGRL]
    exact (PDE.MFAdjoint.hs_add_le 0 hRF0.1 hL0.1).2
  have hsqφ := fourierTailA_integral_sq φ hφL2 hφ0
  have hL1 : ∫ y, |φ y| ≤ PDE.hsNorm 0 (PDE.coeffOf φ) := by
    have hfm : MeasureTheory.MemLp (fun y => |φ y|) (ENNReal.ofReal 2) volume := by
      rw [ENNReal.ofReal_ofNat]; exact PDE.ClassicalAux.memLp_two_of_continuous hbgC.abs
    have hgm : MeasureTheory.MemLp (fun _ : Torus d => (1 : ℝ)) (ENNReal.ofReal 2) volume := by
      rw [ENNReal.ofReal_ofNat]; exact MeasureTheory.memLp_const 1
    have H := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
      Real.HolderConjugate.two_two (f := fun y => |φ y|) (g := fun _ : Torus d => (1 : ℝ))
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one) hfm hgm
    have e1 : ∀ y, |φ y| ^ (2 : ℝ) = φ y ^ 2 := fun y => by rw [Real.rpow_two, sq_abs]
    have e2 : ∫ _ : Torus d, (1 : ℝ) = 1 := by simp
    simp only [mul_one, e1, Real.one_rpow, e2] at H
    have e3 : PDE.hsNorm 0 (PDE.coeffOf φ) = (∫ y, φ y ^ 2) ^ (1 / 2 : ℝ) := by
      unfold PDE.hsNorm
      rw [← hsqφ, Real.sqrt_eq_rpow]
    rw [e3]
    exact H
  have hcint : c = ∫ y, ρβ y * φ y := by
    rw [hc]; exact PDE.MFSemigroup.pair_withDensityReal hprob φ
  have hc0 : |c| ≤ M * PDE.hsNorm 0 (PDE.coeffOf φ) := by
    rw [hcint]
    calc |∫ y, ρβ y * φ y| ≤ ∫ y, |ρβ y * φ y| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ y, M * |φ y| := MeasureTheory.integral_mono
          (fourierTailA_integrable _ (hρC.mul hbgC).abs)
          (fourierTailA_integrable _ (continuous_const.mul hbgC.abs))
          (fun y => by
            rw [abs_mul, abs_of_pos (hpos y)]
            exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _))
      _ = M * ∫ y, |φ y| := MeasureTheory.integral_const_mul _ _
      _ ≤ M * PDE.hsNorm 0 (PDE.coeffOf φ) := mul_le_mul_of_nonneg_left hL1 hM0
  -- assembly
  have hI := PDE.MFAdjoint.hs_add_le (n : ℝ) hLapH hcdelta.1
  have hA2 := (PDE.MFAdjoint.hs_add_le (n : ℝ) hRFn0.1 hI.1).2
  have hA3 : PDE.hsNorm (n : ℝ) e' ≤ |c| := hcdelta.2.trans (le_of_eq (abs_neg c))
  have hP1 := mul_le_mul_of_nonneg_left hGN hM0
  have hP2 := mul_le_mul_of_nonneg_left (add_le_add hRF0.2 hL0.2) hM0
  have hP3 := mul_le_mul_of_nonneg_left (add_le_add hRFN hLapN) hM0
  have hbound : PDE.hsNorm (n : ℝ) (PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f)) ≤
      (1 + M) * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
        PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) + |β⁻¹|) *
        PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := by
    have eq : (1 + M) * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
        PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) + |β⁻¹|) *
        PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) =
        (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
          PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) *
          PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) + |β⁻¹| * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f)) +
        M * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
          PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) *
          PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) + |β⁻¹| * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f)) := by
      ring
    rw [hAcoef, eq]
    linarith [hA2, hI.2, hA3, hc0, hP1, hP2, hP3, hRFN, hLapN, hRF0.2, hL0.2]
  have e1 : sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ f) =
      PDE.hsNorm (n : ℝ) (PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f)) := by
    unfold PDE.hsNorm
    rw [(PDE.hsNormSq_coeffOf (n : ℝ) _ hAFS).2,
      Real.sqrt_sq (by unfold sobolevNorm; exact Real.sqrt_nonneg _)]
  have e2 : sobolevNorm ((n : ℝ) + 2) f = PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := by
    have hfS : MemSobolev ((n : ℝ) + 2) f := PDE.MFSemigroup.memSobolev_of_isSmooth hf _
    unfold PDE.hsNorm
    rw [(PDE.hsNormSq_coeffOf ((n : ℝ) + 2) f hfS).2,
      Real.sqrt_sq (by unfold sobolevNorm; exact Real.sqrt_nonneg _)]
  rw [e1, e2]
  exact hbound


end HRS.ME

end
