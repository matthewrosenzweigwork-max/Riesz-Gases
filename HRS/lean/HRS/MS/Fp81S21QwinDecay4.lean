import HRS.MS.Fp81S21QwinDecay3

/-!
# HRS S2.1(iii), SOL26 packet 27c: shifted cosine-window decay

This combines the retained-endpoint cosine integration estimate with the
separate zero-mode estimate and the exact root-window normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrb
open HRS.MS.R2WinOrbNL

private theorem fp81s21_qwin_m0_scale
    {T C E : ℝ} (hE : 0 ≤ E) :
    s103nM0 T (C * E) ≤ s103nM0 T C * E := by
  unfold s103nM0
  apply max_le
  · calc
      T * (1 / Real.sqrt T) * (C * E) =
          (T * (1 / Real.sqrt T) * C) * E := by ring
      _ ≤ max (T * (1 / Real.sqrt T) * C)
            (4 * (Real.sqrt (2 / T) * ((2 * C + T * C) * T ^ 2 / Real.pi ^ 2))) * E :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hE
  · calc
      4 * (Real.sqrt (2 / T) * ((2 * (C * E) + T * (C * E)) * T ^ 2 / Real.pi ^ 2)) =
          (4 * (Real.sqrt (2 / T) * ((2 * C + T * C) * T ^ 2 / Real.pi ^ 2))) * E := by ring
      _ ≤ max (T * (1 / Real.sqrt T) * C)
            (4 * (Real.sqrt (2 / T) * ((2 * C + T * C) * T ^ 2 / Real.pi ^ 2))) * E :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hE

private theorem fp81s21_qwin_windowTest_jet_eq
    {d : ℕ} {C : WholeCoeff d} {F : ℕ → ℝ → Euc d → ℝ}
    {T0 A a T m : ℝ}
    (H : s103_famHyp F (4 * d + 42) T0 A)
    (ha : 0 ≤ a) (hT : 0 < T) (haT : a + T ≤ T0)
    {α : MultiIndex d} {n k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ 4 * d + 42)
    (hvalues : ∀ (i : ℕ) (hi : i < 3) (t : ℝ),
      F i t = propagatorW C 0 t
        (s103nData C (oscTestFun m α) ⟨i, hi⟩ t))
    (x : Euc d) :
    iteratedFDeriv ℝ k (r2WindowTest C m T a n α) x =
      (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) •
        ∫ u in Set.Icc (0 : ℝ) T,
          r2CosBasis T n u • iteratedFDeriv ℝ k (F 0 (a + u)) x := by
  let W : Euc d → ℝ := fun y =>
    ∫ u in Set.Icc (0 : ℝ) T, r2CosBasis T n u * F 0 (a + u) y
  let cn : ℝ := (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8)
  have hroot : r2WindowTest C m T a n α =
      fun y => cn * W y := by
    funext y
    unfold r2WindowTest W
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    have huT : a + u ∈ Set.Icc (0 : ℝ) (a + T) :=
      ⟨by linarith [hu.1, ha], by linarith [hu.2]⟩
    have huT0 : a + u ∈ Set.Icc (0 : ℝ) T0 :=
      ⟨huT.1, huT.2.trans haT⟩
    have hv := hvalues 0 (by norm_num) (a + u)
    have hzero : s103nData C (oscTestFun m α) ⟨0, by norm_num⟩ (a + u) =
        oscTestFun m α := rfl
    rw [hzero] at hv
    rw [← hv]
  have hwindow := fp81s21_qwin_window_jet_eq H ha hT haT
    (by omega : 1 ≤ 4 * d + 42) (n := n) (j := k)
    (by omega : k ≤ 4 * d + 42) x
  rw [hroot]
  change iteratedFDeriv ℝ k (fun y => cn * W y) x = _
  have hsmul : (fun y => cn * W y) = cn • W := rfl
  rw [hsmul, iteratedFDeriv_const_smul_apply
    ((hwindow.1.of_le (by exact_mod_cast hkK)).contDiffAt)]
  simpa [cn] using congrArg (fun z => cn • z) hwindow.2

private theorem fp81s21_qwin_windowTest_shifted_jet_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {F : ℕ → ℝ → Euc p.d → ℝ} {T0 Afam : ℝ}
    (Hfam : s103_famHyp F (4 * p.d + 42) T0 Afam)
    {α : MultiIndex p.d}
    (hvalues : ∀ (i : ℕ) (hi : i < 3) (t : ℝ),
      F i t = propagatorW (r26t3_coeff R) 0 t
        (s103nData (r26t3_coeff R)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) ⟨i, hi⟩ t))
    {Cj c : ℝ} (hCj : 0 ≤ Cj) (hc : 0 < c)
    (hjet : ∀ (t : ℝ), 0 ≤ t →
      ∀ k : ℕ, 1 ≤ k → k ≤ 4 * p.d + 40 → ∀ x : Euc p.d,
        ‖iteratedFDeriv ℝ k
          (propagatorW (r26t3_coeff R) 0 t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤
            Cj * Real.exp (-c * t) * s103_b p.d α ∧
        ‖iteratedFDeriv ℝ k
          (propagatorW (r26t3_coeff R) 0 t
            (generatorW (r26t3_coeff R) t
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x‖ ≤
            Cj * Real.exp (-c * t) * s103_b p.d α ∧
        ‖iteratedFDeriv ℝ k
          (propagatorW (r26t3_coeff R) 0 t
            (s103nData (r26t3_coeff R)
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α) 2 t)) x‖ ≤
            Cj * Real.exp (-c * t) * s103_b p.d α)
    {a : ℝ} (ha : 0 ≤ a) (hT : 0 < p.T) (haT : a + p.T ≤ T0)
    {n k : ℕ}
    (hk : 1 ≤ k) (hkJ : k ≤ 4 * p.d + 40) (x : Euc p.d) :
    ‖iteratedFDeriv ℝ k
      (r2WindowTest (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a n α) x‖ ≤
      s103nM0 p.T Cj * Real.exp (-c * a) *
        (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d α := by
  let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let E : ℝ := Real.exp (-c * a)
  let Cp : ℝ := Cj * E
  let B : ℝ := Cp * s103_b p.d α
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hb : 0 ≤ s103_b p.d α := s103_b_nonneg α
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : ∀ u ∈ Set.Icc (0 : ℝ) p.T,
      ‖iteratedFDeriv ℝ k (F 1 (a + u)) x‖ ≤ B := by
    intro u hu
    have ht : 0 ≤ a + u := by linarith [ha, hu.1]
    have hraw := hjet (a + u) ht k hk hkJ x
    have hval := hvalues 1 (by omega) (a + u)
    have hFbound : ‖iteratedFDeriv ℝ k (F 1 (a + u)) x‖ ≤
        Cj * Real.exp (-c * (a + u)) * s103_b p.d α := by
      rw [hval]
      simpa [s103nData, φ] using hraw.2.1
    have hexp : Real.exp (-c * (a + u)) ≤ E := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (le_of_lt hc) hu.1]
    calc
      ‖iteratedFDeriv ℝ k (F 1 (a + u)) x‖ ≤
          Cj * Real.exp (-c * (a + u)) * s103_b p.d α := hFbound
      _ ≤ Cj * E * s103_b p.d α :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp hCj) hb
      _ = B := rfl
  have hB2 : ∀ u ∈ Set.Icc (0 : ℝ) p.T,
      ‖iteratedFDeriv ℝ k (F 2 (a + u)) x‖ ≤ B := by
    intro u hu
    have ht : 0 ≤ a + u := by linarith [ha, hu.1]
    have hraw := hjet (a + u) ht k hk hkJ x
    have hval := hvalues 2 (by omega) (a + u)
    have hFbound : ‖iteratedFDeriv ℝ k (F 2 (a + u)) x‖ ≤
        Cj * Real.exp (-c * (a + u)) * s103_b p.d α := by
      rw [hval]
      simpa [s103nData, φ] using hraw.2.2
    have hexp : Real.exp (-c * (a + u)) ≤ E := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (le_of_lt hc) hu.1]
    calc
      ‖iteratedFDeriv ℝ k (F 2 (a + u)) x‖ ≤
          Cj * Real.exp (-c * (a + u)) * s103_b p.d α := hFbound
      _ ≤ Cj * E * s103_b p.d α :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp hCj) hb
      _ = B := rfl
  have hder := fp81s21_qwin_windowTest_jet_eq Hfam ha hT haT
    (C := r26t3_coeff R) (m := (wholeSpaceIndex p.d : ℝ)) (α := α) (n := n)
    (k := k) hk (by omega : k ≤ 4 * p.d + 42) hvalues x
  have hcn : 0 ≤ (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) := by positivity
  by_cases hn : n = 0
  · subst n
    have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) p.T,
        ‖r2CosBasis p.T 0 u • iteratedFDeriv ℝ k (F 0 (a + u)) x‖ ≤
          (1 / Real.sqrt p.T) * B := by
      intro u hu
      have ht : 0 ≤ a + u := by linarith [ha, hu.1]
      have hraw := hjet (a + u) ht k hk hkJ x
      have hval := hvalues 0 (by norm_num) (a + u)
      have hFbound : ‖iteratedFDeriv ℝ k (F 0 (a + u)) x‖ ≤
          Cj * Real.exp (-c * (a + u)) * s103_b p.d α := by
        rw [hval]
        simpa [s103nData, φ] using hraw.1
      have hexp : Real.exp (-c * (a + u)) ≤ E := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (le_of_lt hc) hu.1]
      have hFdec : ‖iteratedFDeriv ℝ k (F 0 (a + u)) x‖ ≤ B := by
        calc
          ‖iteratedFDeriv ℝ k (F 0 (a + u)) x‖ ≤
              Cj * Real.exp (-c * (a + u)) * s103_b p.d α := hFbound
          _ ≤ Cj * E * s103_b p.d α :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hexp hCj) hb
          _ = B := rfl
      rw [norm_smul, Real.norm_eq_abs]
      have hcos := s103_cos_abs_le hT 0 u
      simp only [if_pos rfl] at hcos
      exact mul_le_mul hcos hFdec (norm_nonneg _) (one_div_pos.2 (Real.sqrt_pos.2 hT)).le
    have hle := norm_setIntegral_le_of_norm_le_const
      (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) p.T)
      (f := fun u => r2CosBasis p.T 0 u •
        iteratedFDeriv ℝ k (F 0 (a + u)) x)
      (C := (1 / Real.sqrt p.T) * B) (by simp) hpoint
    have hvol : (volume : Measure ℝ).real (Set.Icc (0 : ℝ) p.T) = p.T := by
      simp [Measure.real, Real.volume_Icc, hT.le]
    have hsetBound :
        ‖∫ u in Set.Icc (0 : ℝ) p.T,
          r2CosBasis p.T 0 u • iteratedFDeriv ℝ k (F 0 (a + u)) x‖ ≤
          p.T * (1 / Real.sqrt p.T) * B := by
      calc
        _ ≤ ((1 / Real.sqrt p.T) * B) *
            (volume : Measure ℝ).real (Set.Icc (0 : ℝ) p.T) := hle
        _ = p.T * (1 / Real.sqrt p.T) * B := by rw [hvol]; ring
    have hcn0 : (1 + ((0 : ℕ) : ℝ) ^ 2) ^ ((3 : ℝ) / 8) = 1 := by norm_num
    have hcosBound :
        ‖iteratedFDeriv ℝ k
          (r2WindowTest (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a 0 α) x‖ ≤
          s103_cosBound p.T B 0 := by
      rw [hder, hcn0, one_smul]
      simpa [s103_cosBound, B, Cp, E] using hsetBound
    have hArith := s103_cosBound_arith hT hCp 0
    have hFactored :
        (1 + (0 : ℝ)) ^ ((3 : ℝ) / 8) *
          s103_cosBound p.T B 0 ≤
          s103nM0 p.T Cp * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d α := by
      have hbase := s103_cosBound_arith hT hCp (0 : ℕ)
      have hbase' : s103_cosBound p.T Cp 0 ≤
          s103nM0 p.T Cp * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) := by
        simpa [s103nM0] using hbase
      have hfreq : (1 + (0 : ℝ)) ^ ((3 : ℝ) / 8) = 1 := by norm_num
      rw [hfreq, show B = Cp * s103_b p.d α by rfl, s103_cosBound_mul, one_mul]
      calc
        s103_b p.d α * s103_cosBound p.T Cp 0 ≤
            s103_b p.d α *
              (s103nM0 p.T Cp * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hbase' hb
        _ = s103nM0 p.T Cp * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) *
              s103_b p.d α := by ring
    have hfinal :
        s103nM0 p.T (Cj * E) * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) *
          s103_b p.d α ≤
          s103nM0 p.T Cj * E * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) *
            s103_b p.d α := by
      have hscale := fp81s21_qwin_m0_scale (T := p.T) (C := Cj) (E := E) hE
      have hfreq0 : 0 ≤ (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
      have hscale' := mul_le_mul_of_nonneg_right hscale
        (mul_nonneg hfreq0 hb)
      simpa [mul_assoc] using hscale'
    calc
      ‖iteratedFDeriv ℝ k
          (r2WindowTest (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a 0 α) x‖ ≤
          s103_cosBound p.T B 0 := hcosBound
      _ ≤ s103nM0 p.T Cp * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) *
          s103_b p.d α := by
            have hfreq : (1 + (0 : ℝ)) ^ ((3 : ℝ) / 8) = 1 := by norm_num
            simpa only [hfreq, one_mul] using hFactored
      _ ≤ s103nM0 p.T Cj * E * (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) *
          s103_b p.d α := hfinal
      _ = s103nM0 p.T Cj * Real.exp (-c * a) *
            (1 + ((0 : ℕ) : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d α := by
          have hpow₁ : (1 + (0 : ℝ)) ^ (-(5 : ℝ) / 4) = 1 := by norm_num
          have hpow₂ : (1 + ((0 : ℕ) : ℝ)) ^ (-(5 : ℝ) / 4) = 1 := by norm_num
          simpa only [E, hpow₁, hpow₂]
  · have hn0 : n ≠ 0 := hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
    let lam : ℝ := (n : ℝ) * Real.pi / p.T
    have hlam : 0 < lam := by dsimp [lam]; positivity
    have hcosInt :
        ∫ u in Set.Icc (0 : ℝ) p.T,
          r2CosBasis p.T n u • iteratedFDeriv ℝ k (F 0 (a + u)) x =
        Real.sqrt (2 / p.T) •
          ∫ u in (0 : ℝ)..p.T,
            Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (a + u)) x := by
      rw [intervalIntegral.integral_of_le hT.le,
        ← integral_Icc_eq_integral_Ioc, ← integral_smul]
      refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
      simp only [r2CosBasis, if_neg hn0, lam]
      have harg : (n : ℝ) * Real.pi * u / p.T =
          ((n : ℝ) * Real.pi / p.T) * u := by ring
      rw [harg]
      simp only [smul_smul, smul_eq_mul]
    have hcos := fp81s21_qwin_cos_jet_ibp Hfam ha hT haT
      (j := k) (by omega : k ≤ 4 * p.d + 42) x n hn1 hB1 hB2
    have hshift :
        ∫ u in (0 : ℝ)..p.T,
          Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (u + a)) x =
        ∫ u in (0 : ℝ)..p.T,
          Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (a + u)) x := by
      apply intervalIntegral.integral_congr
      intro u hu
      change Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (u + a)) x =
        Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (a + u)) x
      rw [show u + a = a + u by ring]
    have hnorm :
        ‖iteratedFDeriv ℝ k
          (r2WindowTest (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a n α) x‖ ≤
          (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * Real.sqrt (2 / p.T) *
            ‖∫ u in (0 : ℝ)..p.T,
              Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (a + u)) x‖ := by
      rw [hder, hcosInt, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hcn, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [← mul_assoc]
    have hcos' :
        ‖∫ u in (0 : ℝ)..p.T,
          Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (a + u)) x‖ ≤
          (2 * B + p.T * B) / lam ^ 2 := by
      simpa [lam] using hcos
    have hscaled :
        (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * Real.sqrt (2 / p.T) *
            ‖∫ u in (0 : ℝ)..p.T,
              Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (a + u)) x‖ ≤
          (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * Real.sqrt (2 / p.T) *
            ((2 * B + p.T * B) / lam ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcos'
        (mul_nonneg hcn (Real.sqrt_nonneg (2 / p.T)))
    have hcosBound :
        ‖iteratedFDeriv ℝ k
          (r2WindowTest (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a n α) x‖ ≤
          (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * s103_cosBound p.T B n := by
      calc
        _ ≤ (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * Real.sqrt (2 / p.T) *
            ‖∫ u in (0 : ℝ)..p.T,
              Real.cos (lam * u) • iteratedFDeriv ℝ k (F 0 (a + u)) x‖ := hnorm
        _ ≤ _ := by
          calc
            _ ≤ (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * Real.sqrt (2 / p.T) *
                ((2 * B + p.T * B) / lam ^ 2) := hscaled
            _ = (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * s103_cosBound p.T B n := by
              dsimp [s103_cosBound, lam]
              simp [hn0]
              ring
    have hbase := s103_cosBound_arith hT hCp n
    have hfactored :
        (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * s103_cosBound p.T B n ≤
          s103nM0 p.T Cp * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d α := by
      dsimp [B]
      rw [s103_cosBound_mul]
      have hbase' : (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * s103_cosBound p.T Cp n ≤
          s103nM0 p.T Cp * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by
        simpa [s103nM0] using hbase
      have hbmul := mul_le_mul_of_nonneg_right hbase' hb
      calc
        _ = ((1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) *
              s103_cosBound p.T Cp n) * s103_b p.d α := by ring
        _ ≤ (s103nM0 p.T Cp * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4)) *
              s103_b p.d α := hbmul
    have hscale := fp81s21_qwin_m0_scale (T := p.T) (C := Cj) (E := E) hE
    have hfreq0 : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
    have hfinal : s103nM0 p.T Cp * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) *
          s103_b p.d α ≤ s103nM0 p.T Cj * E *
          (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d α := by
      have hscale' := mul_le_mul_of_nonneg_right hscale
        (mul_nonneg hfreq0 hb)
      simpa [Cp, mul_assoc] using hscale'
    exact hcosBound.trans (hfactored.trans hfinal)

theorem fp81s21_qwin_shifted_decay (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧
          ∀ a : ℝ, 0 ≤ a → ∀ j k : ℕ, 1 ≤ k → k ≤ r26t3_J p.d →
            ∀ x : Euc p.d,
              ‖iteratedFDeriv ℝ k (r26t3_qwin R a j) x‖ ≤
                C * Real.exp (-c * a) * r26t3_feature_weight p.d j := by
  obtain ⟨δf, hδf, hδfhalf, hfamily⟩ := fp81s21_qwin_shifted_family p
  obtain ⟨δj, hδj, hδjhalf, hjetAll⟩ := fp81s21_qwin_terminal_jet_decay p
  let δ0 : ℝ := min δf δj
  have hδ0 : 0 < δ0 := by dsimp [δ0]; exact lt_min hδf hδj
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδfhalf
  refine ⟨δ0, hδ0, hδ0half, fun δ hδ hδle R => ?_⟩
  have hδf' : δ ≤ δf := hδle.trans (min_le_left _ _)
  have hδj' : δ ≤ δj := hδle.trans (min_le_right _ _)
  obtain ⟨Cfam, hCfam, hfamilyR⟩ := hfamily δ hδ hδf' R
  obtain ⟨Cj, hCj, c, hc, hjet⟩ := hjetAll δ hδ hδj' R
  let C := s103nM0 p.T Cj
  have hC : 0 ≤ C := s103nM0_nonneg p.hT hCj
  refine ⟨C, hC, c, hc, ?_⟩
  intro a ha j k hk hkJ x
  let i := r26t3_feature_enum p.d j
  let T0 := a + p.T
  obtain ⟨F, Hfam, hvalues⟩ := hfamilyR i.2 T0 (by linarith [ha, p.hT.le])
  have hmode := fp81s21_qwin_windowTest_shifted_jet_bound p R Hfam
    (α := i.2) hvalues hCj hc (hjet i.2) ha p.hT (by rfl)
    (n := i.1) (k := k) hk ?_ x
  · have hroot := fp81s21_qwin_eq_windowTest R a j
    rw [hroot]
    have hweight := fp81s21_qwin_feature_weight_eq p j
    have hfinal :
        C * Real.exp (-c * a) * r26t3_feature_weight p.d j =
          s103nM0 p.T Cj * Real.exp (-c * a) *
            (1 + (i.1 : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d i.2 := by
      rw [hweight]
      dsimp [C, i]
      ring
    exact hfinal ▸ hmode
  · dsimp [r26t3_J] at hkJ ⊢
    omega

#print axioms fp81s21_qwin_shifted_decay

end HRS.Fp81.S21

end
