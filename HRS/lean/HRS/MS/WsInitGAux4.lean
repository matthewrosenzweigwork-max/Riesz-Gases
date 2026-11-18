import HRS.MS.WsInitGAux3
import HRS.MS.ThCorrSmAux1

/-!
# S21 packet G, part 4: the cosine coefficients of the orbit are summable in `C_b^J`

`s21g_orbit_cos`: for an orbit `S21GOrbit C m T K J b G0 G1 G2 G3` (WsInitGAux1) and `T > 0`:
* every `r2CosOrbitTest C m T n α` is in `C_b^J`;
* `∑_{(n,α)} cbNorm J (r2CosOrbitTest C m T n α) < ∞` (two integrations by parts: `cbNorm J f_{n,α} ≲ (1+n²)^{3/8} n^{-2} b_α`);
* `t ↦ propagatorW C 0 t φ_α x` is continuous on `[0,T]`.
These are exactly the hypotheses `hmem`, `hsum`, `hcont` of the rows `r2_static_observation_path*` (Round2).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole

variable {d : ℕ}

theorem s21g_cbNorm_le {J : ℕ} {g : Euc d → ℝ} {B : ℝ} (hB : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    cbNorm J g ≤ (J + 1 : ℝ) * B := by
  unfold cbNorm
  have : ∀ j ∈ Finset.range (J + 1), (⨆ z : Euc d, ‖iteratedFDeriv ℝ j g z‖) ≤ B := fun j hj =>
    ciSup_le fun x => hB j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
  refine (Finset.sum_le_sum this).trans ?_
  simp [Finset.sum_const, Finset.card_range]

theorem s21g_memCb_const_mul {J : ℕ} {g : Euc d → ℝ} (c : ℝ) (h : MemCb J g) :
    MemCb J (fun x => c * g x) := by
  refine ⟨h.1.const_smul c, fun j hj => ?_⟩
  obtain ⟨M, hM⟩ := h.2 j hj
  refine ⟨|c| * M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have e : (fun x => c * g x) = c • g := by funext y; simp [smul_eq_mul]
  show ‖iteratedFDeriv ℝ j (fun x => c * g x) x‖ ≤ _
  rw [e, iteratedFDeriv_const_smul_apply ((h.1.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM ⟨x, rfl⟩) (abs_nonneg _)

theorem s21g_iter_const_mul {J j : ℕ} {g : Euc d → ℝ} (c : ℝ) (h : MemCb J g) (hj : j ≤ J) (x : Euc d) :
    iteratedFDeriv ℝ j (fun x => c * g x) x = c • iteratedFDeriv ℝ j g x := by
  have e : (fun x => c * g x) = c • g := by funext y; simp [smul_eq_mul]
  rw [e]
  exact iteratedFDeriv_const_smul_apply ((h.1.of_le (by exact_mod_cast hj)).contDiffAt)

/-- The coefficient bound for `n ≥ 1`. -/
theorem s21g_cos_coef_bound {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 1 ≤ n) {u0 u1 u2 : ℝ → ℝ}
    (hd0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u0 (u1 τ) (Set.Icc (0 : ℝ) T) τ)
    (hd1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u1 (u2 τ) (Set.Icc (0 : ℝ) T) τ)
    (hc2 : ContinuousOn u2 (Set.Icc (0 : ℝ) T)) {B : ℝ} (h1a : |u1 0| ≤ B) (h1b : |u1 T| ≤ B)
    (h2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, |u2 τ| ≤ B) :
    |∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * u0 t| ≤
      Real.sqrt (2 / T) * ((T / (n * Real.pi)) ^ 2 * (2 * B + T * B)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hom : 0 < (n : ℝ) * Real.pi / T := by positivity
  have hsin : Real.sin ((n : ℝ) * Real.pi / T * T) = 0 := by
    rw [div_mul_cancel₀ _ hT.ne']; exact Real.sin_nat_mul_pi n
  have hib := s21g_cos_ibp hT.le hom hsin hd0 hd1 hc2 h1a h1b h2
  have hnz : n ≠ 0 := by omega
  have e1 : ∀ t : ℝ, r2CosBasis T n t * u0 t =
      Real.sqrt (2 / T) * (Real.cos ((n : ℝ) * Real.pi / T * t) * u0 t) := by
    intro t
    unfold r2CosBasis
    rw [if_neg hnz]
    have : (n : ℝ) * Real.pi * t / T = (n : ℝ) * Real.pi / T * t := by ring
    rw [this]; ring
  have e2 : ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * u0 t =
      Real.sqrt (2 / T) * ∫ t in (0 : ℝ)..T, Real.cos ((n : ℝ) * Real.pi / T * t) * u0 t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le,
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => e1 t
  rw [e2, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine hib.trans (le_of_eq ?_)
  rw [inv_div]

/-- The coefficient bound for `n = 0`. -/
theorem s21g_cos_coef_bound0 {T : ℝ} (hT : 0 < T) {u0 : ℝ → ℝ} {B : ℝ}
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) T, |u0 τ| ≤ B) :
    |∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T 0 t * u0 t| ≤ Real.sqrt T * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (h 0 ⟨le_rfl, hT.le⟩)
  have e : ∀ t : ℝ, r2CosBasis T 0 t * u0 t = (Real.sqrt T)⁻¹ * u0 t := by
    intro t; simp [r2CosBasis]
  simp_rw [e]
  rw [integral_const_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T)
    (f := u0) (C := B) (by simp) (fun t ht => by rw [Real.norm_eq_abs]; exact h t ht)
  rw [Real.norm_eq_abs] at h1
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
  calc (Real.sqrt T)⁻¹ * |∫ t in Set.Icc (0 : ℝ) T, u0 t| ≤ (Real.sqrt T)⁻¹ * (B * volume.real (Set.Icc (0 : ℝ) T)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hs.le)
    _ = Real.sqrt T * B := by
        rw [Real.volume_real_Icc_of_le hT.le, sub_zero]
        field_simp
        nlinarith [hsq]

variable {C : WholeCoeff d} {m T K : ℝ} {J : ℕ} {b : MultiIndex d → ℝ} {G0 G1 G2 G3 : MultiIndex d → ℝ → Euc d → ℝ}

/-- `h_n = n^{-2}` envelope times `(1+n²)^{3/8}`. -/
def s21g_env (n : ℕ) : ℝ := (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * (((n : ℝ) ^ 2)⁻¹)

theorem s21g_env_nonneg (n : ℕ) : 0 ≤ s21g_env n := by
  unfold s21g_env; positivity

theorem s21g_env_le (n : ℕ) : s21g_env n ≤ 2 * (((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [s21g_env]
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    have hn0 : (0 : ℝ) < n := by linarith
    unfold s21g_env
    have hc : (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 4) := by
      have h2 : 1 + (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
      calc (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) ≤ (2 * (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) :=
            Real.rpow_le_rpow (by positivity) h2 (by norm_num)
        _ = 2 ^ ((3 : ℝ) / 8) * ((n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 4) := by
            have h3 : ((n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) = (n : ℝ) ^ ((3 : ℝ) / 4) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
            rw [h3]
            gcongr
            calc (2 : ℝ) ^ ((3 : ℝ) / 8) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    have h4 : ((n : ℝ) ^ 2)⁻¹ = ((n : ℝ) ^ (2 : ℝ))⁻¹ := by rw [Real.rpow_two]
    have h5 : (n : ℝ) ^ ((3 : ℝ) / 4) * ((n : ℝ) ^ (2 : ℝ))⁻¹ = ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ := by
      rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
      rw [← Real.rpow_neg hn0.le]; norm_num
    calc (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * ((n : ℝ) ^ 2)⁻¹
        ≤ (2 * (n : ℝ) ^ ((3 : ℝ) / 4)) * ((n : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2 * ((n : ℝ) ^ ((3 : ℝ) / 4) * ((n : ℝ) ^ (2 : ℝ))⁻¹) := by rw [h4]; ring
      _ = _ := by rw [h5]

theorem s21g_env_summable : Summable s21g_env := by
  have h1 : Summable fun n : ℕ => 2 * (((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
  exact Summable.of_nonneg_of_le s21g_env_nonneg s21g_env_le h1

theorem s21g_inv_le {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ ≤ 4 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : (1 + (n : ℝ)) ^ ((5 : ℝ) / 4) ≤ 4 * (n : ℝ) ^ ((5 : ℝ) / 4) := by
    calc (1 + (n : ℝ)) ^ ((5 : ℝ) / 4) ≤ (2 * (n : ℝ)) ^ ((5 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = 2 ^ ((5 : ℝ) / 4) * (n : ℝ) ^ ((5 : ℝ) / 4) := Real.mul_rpow (by norm_num) hn0.le
      _ ≤ 4 * (n : ℝ) ^ ((5 : ℝ) / 4) := by
          gcongr
          calc (2 : ℝ) ^ ((5 : ℝ) / 4) ≤ 2 ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := by norm_num
  have hp : 0 < (1 + (n : ℝ)) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have hq : 0 < (n : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos hn0 _
  have hneg : (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) = ((1 + (n : ℝ)) ^ ((5 : ℝ) / 4))⁻¹ := by
    rw [show (-(5 : ℝ) / 4) = -((5 : ℝ) / 4) by ring, Real.rpow_neg (by linarith)]
  rw [hneg]
  calc ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ = 4 * (4 * (n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ := by field_simp
    _ ≤ 4 * ((1 + (n : ℝ)) ^ ((5 : ℝ) / 4))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hp h1) (by norm_num)

theorem s21g_orbit_cos_full (hT : 0 < T) (O : S21GOrbit C m T K J b G0 G1 G2 G3) :
    (∀ n α, MemCb J (r2CosOrbitTest C m T n α)) ∧
    (Summable fun q : ℕ × MultiIndex d => cbNorm J (r2CosOrbitTest C m T q.1 q.2)) ∧
    (∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW C 0 t (oscTestFun m α) x) (Set.Icc (0 : ℝ) T)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (α : MultiIndex d),
      cbNorm J (r2CosOrbitTest C m T n α) ≤ B * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * b α) := by
  have hKb : ∀ α, 0 ≤ K * b α := fun α => mul_nonneg O.hK (O.b_nonneg α)
  have hGM : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (G0 α τ) x‖ ≤ K * b α :=
    fun α τ hτ j hj x => (s21g_norm_iter_le_cb (O.mem0 α τ hτ) hj x).trans (O.cb0 α τ hτ)
  have hcont0 : ∀ α, ∀ j ≤ J, ∀ x, ContinuousOn (fun t => iteratedFDeriv ℝ j (G0 α t) x) (Set.Icc (0 : ℝ) T) :=
    fun α j hj x => s21g_cont_iter (O.mem0 α) (O.mem1 α) (O.diff0 α) hj x
  -- the key bound on the derivative coordinates
  have hcoord : ∀ (n : ℕ) (α : MultiIndex d) (j : ℕ) (hj : j ≤ J) (x : Euc d) (v : Fin j → Euc d),
      |∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * iteratedFDeriv ℝ j (G0 α t) x v| ≤
        (if n = 0 then Real.sqrt T else Real.sqrt (2 / T) * ((T / (n * Real.pi)) ^ 2 * (2 + T))) *
          (K * b α) * ∏ i, ‖v i‖ := by
    intro n α j hj x v
    set P : ℝ := ∏ i, ‖v i‖ with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
    have hbd : ∀ (G : ℝ → Euc d → ℝ), (∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G τ)) →
        (∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm J (G τ) ≤ K * b α) → ∀ τ ∈ Set.Icc (0 : ℝ) T,
        |iteratedFDeriv ℝ j (G τ) x v| ≤ K * b α * P := fun G hm hc τ hτ =>
      (s21g_abs_iter_le_cb (hm τ hτ) hj x v).trans (mul_le_mul_of_nonneg_right (hc τ hτ) hP0)
    by_cases hn : n = 0
    · subst hn
      rw [if_pos rfl]
      have := s21g_cos_coef_bound0 hT (u0 := fun t => iteratedFDeriv ℝ j (G0 α t) x v) (B := K * b α * P)
        (hbd (G0 α) (O.mem0 α) (O.cb0 α))
      calc _ ≤ _ := this
        _ = _ := by ring
    · rw [if_neg hn]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
      have h0 := hbd (G1 α) (O.mem1 α) (O.cb1 α)
      have h2 := hbd (G2 α) (O.mem2 α) (O.cb2 α)
      have hd0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun t => iteratedFDeriv ℝ j (G0 α t) x v)
          (iteratedFDeriv ℝ j (G1 α τ) x v) (Set.Icc (0 : ℝ) T) τ := fun τ hτ =>
        s21g_hasDerivWithin_iter (O.mem0 α) (O.mem1 α) (O.diff0 α) hj x v hτ
      have hd1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun t => iteratedFDeriv ℝ j (G1 α t) x v)
          (iteratedFDeriv ℝ j (G2 α τ) x v) (Set.Icc (0 : ℝ) T) τ := fun τ hτ =>
        s21g_hasDerivWithin_iter (O.mem1 α) (O.mem2 α) (O.diff1 α) hj x v hτ
      have hc2 : ContinuousOn (fun t => iteratedFDeriv ℝ j (G2 α t) x v) (Set.Icc (0 : ℝ) T) := fun τ hτ =>
        (s21g_hasDerivWithin_iter (O.mem2 α) (O.mem3 α) (O.diff2 α) hj x v hτ).continuousWithinAt
      have := s21g_cos_coef_bound hT hn1 hd0 hd1 hc2 (B := K * b α * P)
        (h0 0 ⟨le_rfl, hT.le⟩) (h0 T ⟨hT.le, le_rfl⟩) h2
      refine this.trans (le_of_eq ?_)
      ring
  -- the coefficient function
  have hmain : ∀ (n : ℕ) (α : MultiIndex d),
      MemCb J (fun x => ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * G0 α t x) ∧
      ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (fun x => ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * G0 α t x) x‖ ≤
        (if n = 0 then Real.sqrt T else Real.sqrt (2 / T) * ((T / (n * Real.pi)) ^ 2 * (2 + T))) * (K * b α) := by
    intro n α
    obtain ⟨hmem, hder⟩ := s21g_F_memCb hT n (O.mem0 α) (hGM α) (hcont0 α)
    refine ⟨hmem, fun j hj x => ?_⟩
    have hcn : 0 ≤ (if n = 0 then Real.sqrt T else Real.sqrt (2 / T) * ((T / (n * Real.pi)) ^ 2 * (2 + T))) := by
      split_ifs
      · exact Real.sqrt_nonneg _
      · positivity
    refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hcn (hKb α)) fun v => ?_
    rw [Real.norm_eq_abs, hder j hj x v]
    exact hcoord n α j hj x v
  -- the test functions
  have hfeq : ∀ n α, r2CosOrbitTest C m T n α =
      fun x => (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * G0 α t x := by
    intro n α
    funext x
    unfold r2CosOrbitTest
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    show r2CosBasis T n t * propagatorW C 0 t (oscTestFun m α) x = r2CosBasis T n t * G0 α t x
    rw [O.hom α 0 t le_rfl ht.1 ht.2, sub_zero]
  have hmem : ∀ n α, MemCb J (r2CosOrbitTest C m T n α) := fun n α => by
    rw [hfeq]; exact s21g_memCb_const_mul _ (hmain n α).1
  have hboth : (Summable fun q : ℕ × MultiIndex d => cbNorm J (r2CosOrbitTest C m T q.1 q.2)) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (α : MultiIndex d),
        cbNorm J (r2CosOrbitTest C m T n α) ≤ B * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * b α) := by
    set u : ℕ → ℝ := fun n => (if n = 0 then (1 + (0 : ℝ) ^ 2) ^ ((3 : ℝ) / 8) * Real.sqrt T else 0) +
      (Real.sqrt (2 / T) * (T ^ 2 * (2 + T) / Real.pi ^ 2)) * s21g_env n with hu
    have hu0 : ∀ n, 0 ≤ u n := fun n => by
      simp only [hu]
      have := s21g_env_nonneg n
      positivity
    have hus : Summable u := by
      refine Summable.add ?_ (s21g_env_summable.mul_left _)
      exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        have : n ≠ 0 := by simpa using hn
        simp [this]
    have hbound : ∀ q : ℕ × MultiIndex d,
        cbNorm J (r2CosOrbitTest C m T q.1 q.2) ≤ (J + 1 : ℝ) * K * (u q.1 * b q.2) := by
      intro ⟨n, α⟩
      simp only
      have hb := hmain n α
      have hcb : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (r2CosOrbitTest C m T n α) x‖ ≤
          ((1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) *
            (if n = 0 then Real.sqrt T else Real.sqrt (2 / T) * ((T / (n * Real.pi)) ^ 2 * (2 + T)))) *
            (K * b α) := by
        intro j hj x
        rw [hfeq, s21g_iter_const_mul _ (hb.1) hj x, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), mul_assoc]
        exact mul_le_mul_of_nonneg_left (hb.2 j hj x) (by positivity)
      refine (s21g_cbNorm_le hcb).trans ?_
      have hle : (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) *
            (if n = 0 then Real.sqrt T else Real.sqrt (2 / T) * ((T / (n * Real.pi)) ^ 2 * (2 + T))) ≤ u n := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have : (0 : ℝ) ≤ (Real.sqrt (2 / T) * (T ^ 2 * (2 + T) / Real.pi ^ 2)) * s21g_env 0 := by
            have := s21g_env_nonneg 0
            positivity
          simp only [hu, if_pos rfl]
          simp at this ⊢
          nlinarith [this]
        · have hn0 : n ≠ 0 := hpos.ne'
          simp only [hu, if_neg hn0, zero_add]
          unfold s21g_env
          have e : (T / (n * Real.pi)) ^ 2 = T ^ 2 / Real.pi ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
            field_simp
          rw [e]
          exact le_of_eq (by ring)
      have hKb' := hKb α
      have hJ1 : (0 : ℝ) ≤ J + 1 := by positivity
      calc (J + 1 : ℝ) * (((1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) *
            (if n = 0 then Real.sqrt T else Real.sqrt (2 / T) * ((T / (n * Real.pi)) ^ 2 * (2 + T)))) * (K * b α))
          ≤ (J + 1 : ℝ) * (u n * (K * b α)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hKb') hJ1
        _ = _ := by ring
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun q => HRS.MS.Tc5.tc5_cb_nonneg J _) hbound ?_
      exact ((Summable.mul_of_nonneg hus O.b_summable (fun n => hu0 n) (fun α => O.b_nonneg α)).mul_left
        ((J + 1 : ℝ) * K)).congr fun q => by ring
    · set A0 : ℝ := Real.sqrt (2 / T) * (T ^ 2 * (2 + T) / Real.pi ^ 2) with hA0
      have hA00 : 0 ≤ A0 := by positivity
      have hule : ∀ n : ℕ, u n ≤ (Real.sqrt T + 8 * A0) * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by
        intro n
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have e0 : s21g_env 0 = 0 := by simp [s21g_env]
          simp only [hu, if_pos rfl, e0]
          simp
          nlinarith [Real.sqrt_nonneg T]
        · have hn0 : n ≠ 0 := hpos.ne'
          have hrp : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
          simp only [hu, if_neg hn0, zero_add]
          have h1 := s21g_env_le n
          have h2 := s21g_inv_le hpos
          calc A0 * s21g_env n ≤ A0 * (2 * (4 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4))) := by
                gcongr
                exact h1.trans (by gcongr)
            _ ≤ (Real.sqrt T + 8 * A0) * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by
                nlinarith [Real.sqrt_nonneg T, mul_nonneg hA00 hrp]
      refine ⟨(J + 1 : ℝ) * K * (Real.sqrt T + 8 * A0),
        mul_nonneg (mul_nonneg (by positivity) O.hK) (by positivity), fun n α => ?_⟩
      have hbn := hbound (n, α)
      simp only at hbn
      refine hbn.trans ?_
      have hKJ : 0 ≤ (J + 1 : ℝ) * K := mul_nonneg (by positivity) O.hK
      calc (J + 1 : ℝ) * K * (u n * b α) ≤ (J + 1 : ℝ) * K * (((Real.sqrt T + 8 * A0) *
            (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4)) * b α) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hule n) (O.b_nonneg α)) hKJ
        _ = _ := by ring
  refine ⟨hmem, hboth.1, ?_, hboth.2⟩
  · intro α x
    have h0 : ContinuousOn (fun t => G0 α t x) (Set.Icc (0 : ℝ) T) := by
      intro τ hτ
      have := (s21g_hasDerivWithin_iter (O.mem0 α) (O.mem1 α) (O.diff0 α) (j := 0) (Nat.zero_le _) x
        (fun i => i.elim0) hτ).continuousWithinAt
      simpa only [iteratedFDeriv_zero_apply] using this
    refine h0.congr fun t ht => ?_
    show propagatorW C 0 t (oscTestFun m α) x = G0 α t x
    rw [O.hom α 0 t le_rfl ht.1 ht.2, sub_zero]

theorem s21g_orbit_cos (hT : 0 < T) (O : S21GOrbit C m T K J b G0 G1 G2 G3) :
    (∀ n α, MemCb J (r2CosOrbitTest C m T n α)) ∧
    (Summable fun q : ℕ × MultiIndex d => cbNorm J (r2CosOrbitTest C m T q.1 q.2)) ∧
    (∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW C 0 t (oscTestFun m α) x) (Set.Icc (0 : ℝ) T)) :=
  let h := s21g_orbit_cos_full hT O
  ⟨h.1, h.2.1, h.2.2.1⟩

end HRS.MS.S21
