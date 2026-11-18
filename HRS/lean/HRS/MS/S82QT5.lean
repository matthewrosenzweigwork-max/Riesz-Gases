import HRS.MS.S82QT4
import HRS.MS.S82QTri

/-!
# S8.2 (S82Q): R07, once-pinned outer row, second moment
Under `Y ~ R_{m+2}^{x}` (`N = m + 3`) the ordered row sum `R_x = sum_{j != k} G(x, Y_j, Y_k)` satisfies
`E R_x^2 <= C A^2 <x>^{8M} N^2 log(eN)^2`: variance from the pair template (inner rows, `s82q_inner`),
plus the squared mean (`s82q_outer_mean`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

lemma s82q_jb_rpow_pow' {d : ℕ} (M : ℝ) (x : Euc d) (k : ℕ) :
    (jbracket x ^ M) ^ k = jbracket x ^ ((k : ℝ) * M) := s82q_jb_rpow_pow M x k

theorem s82q_outer {d : ℕ} (hd : 2 ≤ d) {a beta M C0 C1 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ Cout : ℝ, 0 ≤ Cout ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      PinComparison beta rho q h C1 → ∀ A : ℝ, 0 ≤ A → ∀ Gt : Euc d → Euc d → Euc d → ℝ,
      Measurable (fun p : Euc d × Euc d × Euc d => Gt p.1 p.2.1 p.2.2) →
      CanonicalTriple (HRS.Whole.withDensityReal rho) Gt →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
        |Gt x y z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z) →
      ∀ m : ℕ, ∀ x : Euc d,
      ∫⁻ Y, ENNReal.ofReal ((Phase2S82.pairSum (fun y w => Gt x y w) Y) ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 3) (m + 2)
            (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d) ≤
        ENNReal.ofReal (Cout * A ^ 2 * jbracket x ^ (8 * M) * ((m + 3 : ℕ) : ℝ) ^ 2 *
          logN (m + 3) ^ 2) := by
  obtain ⟨Cin, hCin, hin⟩ := s82q_inner hd (a := a) (C0 := C0) (C1 := C1) hM hbeta q hq G c hG hc hρ hρG
  obtain ⟨Cmean, hCmean, hmeanl⟩ := s82q_outer_mean hd (a := a) (C0 := C0) (C1 := C1) hM hbeta q hq G c hG hc hρ hρG
  obtain ⟨CR, hCR, hrow3⟩ := weighted_radial_rows d hd beta (4 * M) G c hbeta (by linarith) hG hc q hq
  refine ⟨16 * C0 ^ 2 * Cin * CR + Cmean ^ 2, by positivity, ?_⟩
  intro h hW hP A hA Gt hGm hGc hGb m x
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  set N := m + 3 with hNdef
  have hN : 2 ≤ N := by omega
  have hC0 := hW.positive
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := s82q_logN_nonneg (N := N) (by omega)
  let pins1 : Fin (0 + 1) → Euc d := Fin.cons x (fun i : Fin 0 => i.elim0)
  set Kx : Euc d → Euc d → ℝ := fun y w => Gt x y w with hKx
  have hKs : ∀ y w, Kx y w = Kx w y := fun y w => (hGc.1 x y w).2
  have hKxm : Measurable (Function.uncurry Kx) :=
    hGm.comp (measurable_const.prodMk measurable_id)
  set Px4 := jbracket x ^ (4 * M) with hPx4
  set L := logN N with hL
  have hPx40 : 0 ≤ Px4 := s82q_jb_rpow_nonneg _ x
  set Ψ : Euc d → ℝ := fun y => Cin * A ^ 2 * Px4 * (jbracket y ^ (4 * M) * pole x y ^ 2) *
    ((N : ℕ) : ℝ) * L with hΨ
  have hrow : ∀ᵐ y ∂mu, ∫⁻ X', ENNReal.ofReal ((∑ k, Kx y (X' k)) ^ 2)
      ∂referenceLaw q h mu beta N (m + 1) (Fin.cons y pins1 : Fin (0 + 1 + 1) → Euc d) ≤
      ENNReal.ofReal (Ψ y) := by
    filter_upwards [s82q_ae_ne hd rho x] with y hy
    refine (hin h hW hP A hA Gt hGm hGc hGb m x y (Ne.symm hy)).trans (le_of_eq ?_)
    simp only [hΨ, hPx4, hL, hNdef]
    congr 1
    ring
  set J : ℝ := Cin * A ^ 2 * Px4 * ((N : ℕ) : ℝ) * L * (CR * Px4 * L) with hJ
  have hq0 := hW.short.nonneg
  have hqe := hW.short.even
  have hJle : ∫⁻ y, ENNReal.ofReal (Ψ y) ∂s82q_nu q mu beta N pins1 ≤ ENNReal.ofReal J := by
    unfold s82q_nu
    have hwm : Measurable (fun z : Euc d => ENNReal.ofReal
        (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
        (Finset.measurable_sum _ fun j _ => hW.short.measurable.comp
          (measurable_id.sub measurable_const))))
    have hfm : Measurable (fun y => ENNReal.ofReal (Ψ y)) := by
      refine ENNReal.measurable_ofReal.comp ?_
      simp only [hΨ]
      exact ((measurable_const.mul ((s82q_measurable_jb (4 * M)).mul
        ((s82q_measurable_pole x).pow_const 2))).mul measurable_const).mul measurable_const
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
    have hpin : ∀ y : Euc d, ∑ j, q (y - pins1 j) = q (x - y) := by
      intro y
      have : ∑ j, q (y - pins1 j) = q (y - x) := by simp [pins1, Fin.sum_univ_succ]
      rw [this, show y - x = -(x - y) by abel, hqe]
    have hr3 := (hrow3 rho hρ hρG N hN x).2.2.1
    have hc0 : 0 ≤ Cin * A ^ 2 * Px4 * ((N : ℕ) : ℝ) * L := by positivity
    calc ∫⁻ y, ((fun z : Euc d => ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)))) *
            fun y => ENNReal.ofReal (Ψ y)) y ∂mu
        = ∫⁻ y, ENNReal.ofReal (Real.exp (-(beta / N) * q (x - y)) * Ψ y) ∂mu := by
          refine lintegral_congr fun y => ?_
          simp only [Pi.mul_apply]
          rw [hpin y, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Cin * A ^ 2 * Px4 * ((N : ℕ) : ℝ) * L) *
            ∫⁻ y, ENNReal.ofReal (jbracket y ^ (4 * M) * pole x y ^ 2 *
              Real.exp (-(beta / N) * q (x - y))) ∂mu := by
          refine s82q_lint_scale _ _ _ _ hc0 (ae_of_all _ fun y => le_of_eq ?_)
          simp only [hΨ]
          ring
      _ ≤ ENNReal.ofReal (Cin * A ^ 2 * Px4 * ((N : ℕ) : ℝ) * L) *
            ENNReal.ofReal (CR * jbracket x ^ (4 * M) * logN N) :=
          mul_le_mul_of_nonneg_left hr3 bot_le
      _ = ENNReal.ofReal J := by
          rw [← ENNReal.ofReal_mul hc0]
  obtain ⟨hrowL, hFL, hvar⟩ := s82q_pair_template hW hbeta hN (p := 0 + 1) (m := m + 1)
    (by omega) (by omega) (by omega) pins1 Kx hKs hKxm 1 Ψ J hrow hJle
  have hmean := hmeanl h hW hP A hA Gt hGm hGc hGb m x hrowL
  have hFL' : MemLp (Phase2S82.pairSum Kx) 2 (referenceLaw q h mu beta N (m + 2) pins1) := by
    simpa using hFL
  have hvar' : evariance (Phase2S82.pairSum Kx) (referenceLaw q h mu beta N (m + 2) pins1) ≤
      ENNReal.ofReal (16 * C0 ^ 2 * ((m + 1 + 1 : ℕ) : ℝ) * J) := by
    have := hvar
    simpa using this
  have : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 2) pins1) :=
    hW.probability N hN (0 + 1) (m + 2) (by omega) (by omega) pins1
  have hsm := s82q_second_moment hFL' _ hvar' _ hmean
  refine hsm.trans ?_
  have hP3 := s82q_jb_rpow_nonneg (3 * M) x
  rw [← ENNReal.ofReal_add (by positivity) (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hP8 : Px4 * Px4 = jbracket x ^ (8 * M) := by
    rw [hPx4, ← Real.rpow_add (HRS.MS.S82N.s82n_jb_pos x)]; congr 1; ring
  have hP6 : (jbracket x ^ (3 * M)) ^ 2 ≤ jbracket x ^ (8 * M) := by
    rw [s82q_jb_rpow_pow' (3 * M) x 2]
    exact Real.rpow_le_rpow_of_exponent_le (HRS.MS.S82N.s82n_jb_one_le x) (by push_cast; linarith)
  have hm1 : ((m + 1 + 1 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
    rw [hNdef]; push_cast; linarith
  have hP80 : 0 ≤ jbracket x ^ (8 * M) := s82q_jb_rpow_nonneg _ x
  have hL0 : 0 ≤ L := by linarith
  have t1 : 16 * C0 ^ 2 * ((m + 1 + 1 : ℕ) : ℝ) * J ≤
      16 * C0 ^ 2 * Cin * CR * A ^ 2 * jbracket x ^ (8 * M) * ((N : ℕ) : ℝ) ^ 2 * L ^ 2 := by
    have hJe : J = (Cin * CR * A ^ 2 * jbracket x ^ (8 * M)) * (((N : ℕ) : ℝ) * L ^ 2) := by
      rw [hJ, ← hP8]; ring
    rw [hJe]
    have hk : 0 ≤ 16 * C0 ^ 2 * (Cin * CR * A ^ 2 * jbracket x ^ (8 * M)) * L ^ 2 := by positivity
    calc 16 * C0 ^ 2 * ((m + 1 + 1 : ℕ) : ℝ) * ((Cin * CR * A ^ 2 * jbracket x ^ (8 * M)) *
          (((N : ℕ) : ℝ) * L ^ 2))
        = (16 * C0 ^ 2 * (Cin * CR * A ^ 2 * jbracket x ^ (8 * M)) * L ^ 2) *
            (((m + 1 + 1 : ℕ) : ℝ) * ((N : ℕ) : ℝ)) := by ring
      _ ≤ (16 * C0 ^ 2 * (Cin * CR * A ^ 2 * jbracket x ^ (8 * M)) * L ^ 2) *
            (((N : ℕ) : ℝ) * ((N : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm1 hNr.le) hk
      _ = _ := by ring
  have t2 : (Cmean * A * jbracket x ^ (3 * M) * ((N : ℕ) : ℝ) * L) ^ 2 ≤
      Cmean ^ 2 * A ^ 2 * jbracket x ^ (8 * M) * ((N : ℕ) : ℝ) ^ 2 * L ^ 2 := by
    have : (Cmean * A * jbracket x ^ (3 * M) * ((N : ℕ) : ℝ) * L) ^ 2 =
        (Cmean ^ 2 * A ^ 2 * ((N : ℕ) : ℝ) ^ 2 * L ^ 2) * (jbracket x ^ (3 * M)) ^ 2 := by ring
    rw [this]
    calc (Cmean ^ 2 * A ^ 2 * ((N : ℕ) : ℝ) ^ 2 * L ^ 2) * (jbracket x ^ (3 * M)) ^ 2
        ≤ (Cmean ^ 2 * A ^ 2 * ((N : ℕ) : ℝ) ^ 2 * L ^ 2) * jbracket x ^ (8 * M) :=
          mul_le_mul_of_nonneg_left hP6 (by positivity)
      _ = _ := by ring
  calc 16 * C0 ^ 2 * ((m + 1 + 1 : ℕ) : ℝ) * J + (Cmean * A * jbracket x ^ (3 * M) * ((N : ℕ) : ℝ) * L) ^ 2
      ≤ _ := add_le_add t1 t2
    _ = _ := by ring

end HRS.MS.S82Q
