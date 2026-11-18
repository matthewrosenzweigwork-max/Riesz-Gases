import HRS.MS.Fp81S21MovingHeat4
import HRS.MS.Fp81S21MovingItoRep6
import HRS.MS.Fp81S21MovingGram
import HRS.MS.R2InterpAux56

/-!
# S2.1(iii), packet 18b: moving heat Itô formula

The first analytic stage replaces the stationary fixed-density `s102_c12` input
by the time-dependent Gram continuity already carried by `Fp81MovingStd`.
The full stopped stochastic formula is stated in the contract below only after
its exact finite-projection and moving-reference integrands are fixed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

variable {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r0 : ℕ}
  {c : MultiIndex d → ℝ} {hH : 0 < H}

/-- The moving-reference `C^{1,2}` heat extension on an observation-free piece.
It uses the moving Gram continuity in `Fp81MovingStd.hGram`; the stationary
`S102Std.hstat` hypothesis is not used. -/
theorem fp81s21_moving_heat_c12
    (hs : Fp81MovingStd C m H r0 c hH) (L : ℕ)
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ u ∈ Icc (0 : ℝ) H, IsR2FutureGaussian C m H u (γ u))
    {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (hsH : s ≤ H)
    (hno : ∀ k : Fin (s102_q d L),
      ¬ (q < s102_tk hH L k ∧ s102_tk hH L k < s))
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG4 : MemCb 4 G) :
    ∃ f : ℝ → EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ,
      HRS.IsC12On H Set.univ f ∧
      (∀ v ∈ Icc q s,
        f v = gaussHeat
          (s102_obsCov C m (s102_tauk hH L) (s102_alk L)) G v) ∧
      ∀ v ∈ Ioc q s, ∀ x,
        derivWithin (fun t => f t x) (Icc 0 H) v =
          -(1 / 2) * ∑ i, ∑ j,
            s102_rateM C m hH L v i j *
              iteratedFDeriv ℝ 2
                (gaussHeat (s102_obsCov C m (s102_tauk hH L) (s102_alk L)) G v)
                x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  have hGi : S102GramInt C m hH L := fp81s21_moving_gramInt hs L
  obtain ⟨f, hf, hfeq, hfd⟩ :=
    HRS.MC.Sec7.S7PIH.s7_PIH_heat_c12_proof'
      (q := s102_q d L) q s H hq hqs hsH hH
      (s102_Ar C m hH L s) (s102_obsCov C m (s102_tauk hH L) (s102_alk L))
      (fun i j => by
        by_cases h : s ≤ min (s102_tk hH L i) (s102_tk hH L j)
        · have hsub : Icc q s ⊆
              Icc 0 (min (s102_tk hH L i) (s102_tk hH L j)) :=
            Icc_subset_Icc hq h
          have hcont := (hs.hGram L i j).mono hsub
          have hmul := hcont.const_mul (2 * C.ν)
          refine hmul.congr fun v hv => ?_
          simp only [s102_Ar, Matrix.of_apply, if_pos h]
        · simp only [s102_Ar, Matrix.of_apply, if_neg h, mul_zero]
          exact continuousOn_const)
      (fun v hv => fp81s21_moving_Ar_psd hs L hv hq hsH)
      (s102_obs_law C (hγ s ⟨hq.trans hqs, hsH⟩) (s102_tauk hH L) (s102_alk L)).1
      (fun u hu i j => by
        have hcov := s102_obsCov_eq_rate hH L hGi (hq.trans hu.1) hu.2 hsH i j
        rw [hcov]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
        have har := s102_Ar_eq_rate (C := C) (m := m) hH L
          (a := q) (b := s) (v := v)
          ⟨hu.1.trans_lt hv.1, hv.2⟩ hno
        change s102_rateM C m hH L v i j = s102_Ar C m hH L s v i j
        rw [har])
      G hG4
  refine ⟨f, hf, hfeq, ?_⟩
  intro v hv x
  rw [hfd v ⟨hv.1.le, hv.2⟩ x]
  have har := s102_Ar_eq_rate (C := C) (m := m) hH L
    (a := q) (b := s) (v := v) hv hno
  rw [har]

private theorem fp81s21_pair_withDensityReal
    {d : ℕ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (g : Euc d → ℝ) :
    HRS.Whole.pair (HRS.Whole.withDensityReal ρ) g = ∫ x, ρ x * g x := by
  unfold HRS.Whole.pair HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x)]
  · exact (hρ.measurable.ennreal_ofReal).aemeasurable
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem fp81s21_moving_mu_pair
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) H)
    (g : Euc p.d → ℝ) :
    HRS.Whole.pair (r26t3_mu R u) g =
      ∫ x, g x * (r26t3_coeff R).ρ u x := by
  have hρ : HRS.Whole.IsProbDensity (R.ρ u) :=
    (R.resulting.global H).density u hu
  change HRS.Whole.pair (HRS.Whole.withDensityReal (R.ρ u)) g =
    ∫ x, g x * R.ρ u x
  calc
    _ = ∫ x, R.ρ u x * g x := fp81s21_pair_withDensityReal hρ g
    _ = ∫ x, g x * R.ρ u x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring

/-- A finite-projection drift density using the actual time-dependent reference measure.
The path argument is the particle observation; the filtered realization supplies the
drift field inside `s102_hh`. -/
private def fp81s21_moving_cylA
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (H : ℝ) (hH : 0 < H) (L : ℕ)
    (G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ)
    (ζ : A.Ω) (u : ℝ) : ℝ :=
  ∑ i, fderiv ℝ
      (gaussHeat
        (s102_obsCov (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (s102_tauk hH L) (s102_alk L)) G u)
      (s102_obs (s102_tauk hH L) (s102_alk L)
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P A.X ζ u))
      (EuclideanSpace.single i 1) *
    s102_hh (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (s102_tauk hH L) (s102_alk L)
      (fun v => r2QuadField p.s (r26t3_mu R v) A.P F.X v ζ) i u

/-- A finite-projection covariance density with the moving centered fluctuation. -/
private def fp81s21_moving_cylJ
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (H : ℝ) (hH : 0 < H) (L : ℕ)
    (G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ)
    (ζ : A.Ω) (u : ℝ) : ℝ :=
  ∑ i, ∑ j, iteratedFDeriv ℝ 2
      (gaussHeat
        (s102_obsCov (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (s102_tauk hH L) (s102_alk L)) G u)
      (s102_obs (s102_tauk hH L) (s102_alk L)
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P A.X ζ u))
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
    (2 * (r26t3_coeff R).ν *
      s102_hh2 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (s102_tauk hH L) (s102_alk L)
        (fun v => s102_etaf (r26t3_mu R v) F.X ζ v) i j u)

private theorem fp81s21_moving_Phic_bound
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r0 : ℕ}
    {c : MultiIndex d → ℝ} {hH : 0 < H}
    (hs : Fp81MovingStd C m H r0 c hH) (L : ℕ)
    {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → EucConfig d N) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ s ∈ Icc (0 : ℝ) H,
      ∀ ζ k i, |s102_Phic C m hH L X s ζ k i| ≤ Cn := by
  have hc0 : 0 ≤ ∑ k : Fin (s102_q d L), c (s102_alk L k) :=
    Finset.sum_nonneg fun k _ => hs.hD.nonneg _
  refine ⟨Real.sqrt N * (Real.sqrt (2 * C.ν) / N *
    ∑ k : Fin (s102_q d L), c (s102_alk L k)), ?_, ?_⟩
  · positivity
  · intro s hsT ζ k i
    unfold s102_Phic
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul,
      abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ?_ (by positivity)) (Real.sqrt_nonneg _)
    have hi : c (s102_alk L i) ≤ ∑ k : Fin (s102_q d L), c (s102_alk L k) :=
      Finset.single_le_sum (f := fun k => c (s102_alk L k))
        (fun k _ => hs.hD.nonneg _) (Finset.mem_univ i)
    refine le_trans ?_ hi
    unfold s102_ot
    by_cases h : s ≤ (s102_tauk hH L i : ℝ)
    · rw [if_pos h]
      have hb := hs.hD.bddU (s102_alk L i) s hsT
        (s102_tauk hH L i) ⟨h, (s102_tauk hH L i).2.2⟩
        1 (by omega) (X s.toNNReal ζ k.1)
      rw [s102_gradient_apply, ← Real.norm_eq_abs]
      have h1 := (iteratedFDeriv ℝ 1
        (propagatorW C s (s102_tk hH L i) (oscTestFun m (s102_alk L i)))
        (X s.toNNReal ζ k.1)).le_opNorm
        (fun _ : Fin 1 =>
          (EuclideanSpace.single k.2 (1 : ℝ) : Euc d))
      simp only [iteratedFDeriv_one_apply, Finset.univ_unique,
        Fin.default_eq_zero, Finset.prod_singleton, EuclideanSpace.norm_single,
        norm_one, mul_one] at h1
      exact h1.trans hb
    · rw [if_neg h, s102_gradient_zero]
      simpa using hs.hD.nonneg (s102_alk L i)

/-- Stopped finite-projection heat Itô formula on a moving observation-free piece.
The finite-level test is exactly `Φ (W_a (P_L^H w))`, with `H = a + p.T`.
The representation is produced from the moving density/Gram data and the
filtered realization.  In `hstd`, the `S101Data` field is supplied by
`fp81s21_moving_s101data_of_common`; the remaining `Fp81MovingStd` fields give
the moving density and Gram inputs.  No stationary `S102Std` or fixed
reference measure is used. -/
theorem fp81s21_moving_heat_ito_piece
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {r0 : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) r0 c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hr0 : (p.d : ℝ) / 2 + 2 < r0)
    (hphys : Fp81MovingPhysicalInputs R hN A (a + p.T))
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (L : ℕ) {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s)
    (hsH : s ≤ a + p.T)
    (hno : ∀ k : Fin (s102_q p.d L),
      ¬ (q < s102_tk hH L k ∧ s102_tk hH L k < s))
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ) :
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := a + p.T) ha le_rfl
    ∃ Mart : A.Ω → ℝ, Integrable Mart A.P ∧
      (∫ ζ, Mart ζ ∂A.P = 0) ∧
      ∀ᵐ ζ ∂A.P,
        IntegrableOn
          (fun u => -(Real.sqrt N)⁻¹ *
              fp81s21_moving_cylA R A F (a + p.T)
                (by linarith [p.hT, ha]) L
                (fun x => Φ (W (s102_Lam (a + p.T) L x))) ζ u +
            (1 / (2 * Real.sqrt N)) *
              fp81s21_moving_cylJ R A F (a + p.T)
                (by linarith [p.hT, ha]) L
                (fun x => Φ (W (s102_Lam (a + p.T) L x))) ζ u)
          (Ioc q s) ∧
        r2HeatFn (future (a + p.T))
            (fun w => Φ (W (s102_Pj (a + p.T)
              hH L w))) s
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + p.T) A.P A.X ζ s) -
          r2HeatFn (future (a + p.T))
            (fun w => Φ (W (s102_Pj (a + p.T)
              hH L w))) q
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + p.T) A.P A.X ζ q) =
          (∫ u in Ioc q s,
            (-(Real.sqrt N)⁻¹ *
                fp81s21_moving_cylA R A F (a + p.T)
                  (by linarith [p.hT, ha]) L
                  (fun x => Φ (W (s102_Lam (a + p.T) L x))) ζ u +
              (1 / (2 * Real.sqrt N)) *
                fp81s21_moving_cylJ R A F (a + p.T)
                  (by linarith [p.hT, ha]) L
                  (fun x => Φ (W (s102_Lam (a + p.T) L x))) ζ u)) + Mart ζ := by
  classical
  dsimp only
  let H : ℝ := a + p.T
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := H) ha le_rfl
  let τ : Fin (s102_q p.d L) → Icc (0 : ℝ) H := s102_tauk hH L
  let α : Fin (s102_q p.d L) → MultiIndex p.d := s102_alk L
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ :=
    fun x => Φ (W (s102_Lam H L x))
  have hG5 : MemCb 5 G := by
    dsimp [G]
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof
      (W.comp (s102_Lam H L)) hΦ).1
  have hG4 : MemCb 4 G := s102_memCb4 hG5
  have hG2 : MemCb 2 G :=
    ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
  have hγ : ∀ u ∈ Icc (0 : ℝ) H, IsR2FutureGaussian C m H u (future H u) := by
    simpa [C, m, H] using hfuture.2.1 H hH
  have hrep : fp81s21_moving_S102ItoRep p R hH L A F :=
    fp81s21_moving_itoRep p R hδ hδh hH hN A F hstd hlin hr0 hphys L
  obtain ⟨bd, Φc, hbd, hΦc, hX0, hbform, hΦform, hid⟩ := hrep
  obtain ⟨f, hf, hfeq, hfd⟩ := fp81s21_moving_heat_c12
    hstd L (future H) hγ hq hqs (by simpa [H] using hsH)
    hno hG4
  let X0f : A.Ω → EuclideanSpace ℝ (Fin (s102_q p.d L)) :=
    fun ζ => s102_obs τ α (s102_y0 C m H A.P F.X ζ)
  let Z : ℝ → A.Ω → EuclideanSpace ℝ (Fin (s102_q p.d L)) :=
    itoProcess A.P F.ℱ F.Wc X0f bd Φc
  obtain ⟨Cn, hCn0, hCn⟩ := fp81s21_moving_Phic_bound hstd L F.X
  let K1 : ℝ := ⨆ z, ‖iteratedFDeriv ℝ 1 G z‖
  have hK10 : 0 ≤ K1 := Real.iSup_nonneg fun z => norm_nonneg _
  have hbound : ∀ u ∈ Ioc q s, ∀ ζ k,
      |fderiv ℝ (f u) (Z u ζ) (Φc u ζ k)| ≤
        (s102_q p.d L : ℝ) * Cn * K1 := by
    intro u hu ζ k
    have huH : u ∈ Icc (0 : ℝ) H :=
      ⟨hq.trans hu.1.le, hu.2.trans (by simpa [H] using hsH)⟩
    rw [hfeq u ⟨hu.1.le, hu.2⟩, S7PIF6_lin_expand]
    calc
      |∑ i, (Φc u ζ k) i *
          fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u) (Z u ζ)
            (EuclideanSpace.single i 1)|
          ≤ ∑ i, |(Φc u ζ k) i *
            fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u) (Z u ζ)
              (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (s102_q p.d L), Cn * K1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) hCn0
        · rw [hΦform u ζ k i huH.1]
          exact hCn u huH ζ k i
        · have h2 := S7PIF6_heat_fderiv_bound
            (s102_obsCov C m τ α) hG4 u (Z u ζ)
            (EuclideanSpace.single i (1 : ℝ))
          have h3 : ‖(EuclideanSpace.single i (1 : ℝ) :
              EuclideanSpace ℝ (Fin (s102_q p.d L)))‖ = 1 := by simp
          rw [h3, mul_one] at h2
          exact h2
      _ = (s102_q p.d L : ℝ) * Cn * K1 := by
        simp [Finset.sum_const, mul_assoc]
  obtain ⟨Mart, hMi, hM0, hMeq⟩ := s102_ito_piece_abs
    A.P F.filtered.brownian hH.le f hf X0f hX0 bd hbd Φc hΦc
    hq hqs (by simpa [H] using hsH) hbound
  have hμpair : ∀ u ∈ Icc (0 : ℝ) H, ∀ g : Euc p.d → ℝ,
      HRS.Whole.pair (r26t3_mu R u) g = ∫ x, g x * C.ρ u x := by
    intro u hu g
    simpa [C, m] using fp81s21_moving_mu_pair p R hH hu g
  have hsub : Ioc q s ⊆ Icc (0 : ℝ) H := fun u hu =>
    ⟨hq.trans hu.1.le, hu.2.trans (by simpa [H] using hsH)⟩
  refine ⟨Mart, hMi, hM0, ?_⟩
  filter_upwards [hMeq, hid] with ζ hM hidζ
  obtain ⟨hItoInt, hItoEq⟩ := hM
  have hZ : ∀ u ∈ Icc (0 : ℝ) H,
      Z u ζ = s102_obs τ α (s102_Y C m H A.P A.X ζ u) := by
    intro u hu
    exact (hidζ u hu).symm
  have hpt : ∀ u ∈ Ioc q s,
      itoDrift H f Z bd Φc u ζ =
        -(Real.sqrt N)⁻¹ * fp81s21_moving_cylA R A F H hH L G ζ u +
        (1 / (2 * Real.sqrt N)) *
          fp81s21_moving_cylJ R A F H hH L G ζ u := by
    intro u hu
    have huH : u ∈ Icc (0 : ℝ) H := hsub hu
    have hEta : ∀ i j,
        s102_hh2 C m τ α
          (fun v => s102_etaf (r26t3_mu R v) F.X ζ v) i j u =
        s102_hh2 C m τ α (s102_etaf (r26t3_mu R u) F.X ζ) i j u := by
      intro i j
      unfold s102_hh2
      by_cases hmem : u ∈ Iic (min (τ i : ℝ) (τ j : ℝ))
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    have hbr : ∀ i j,
        ∑ k : Fin N × Fin p.d, Φc u ζ k i * Φc u ζ k j =
          s102_rateM C m hH L u i j + (Real.sqrt N)⁻¹ *
            (2 * C.ν * s102_hh2 C m τ α
              (fun v => s102_etaf (r26t3_mu R v) F.X ζ v) i j u) := by
      intro i j
      have hgrid := s102_bracket_grid (C := C) (m := m)
        hstd.hν hH L (r26t3_mu R u)
        (hμpair u huH) (by omega : 0 < N) F.X ζ i j
      calc
        _ = ∑ k : Fin N × Fin p.d,
            s102_Phic C m hH L F.X u ζ k i *
              s102_Phic C m hH L F.X u ζ k j := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hΦform u ζ k i huH.1, hΦform u ζ k j huH.1]
        _ = _ := by rw [hEta i j]; simpa [τ, α] using hgrid
    have hito := s102_drift_pt (C := C) (m := m) (mΩ := A.mΩ)
      hH L u N G f (hfeq u ⟨hu.1.le, hu.2⟩)
      (fun x => hfd u hu x)
      Z ζ bd Φc
      (fun v => r2QuadField p.s (r26t3_mu R v) A.P F.X v ζ)
      (fun v => s102_etaf (r26t3_mu R v) F.X ζ v)
      (fun i => by simpa [C, m, τ, α] using hbform u ζ i huH.1)
      hbr
    rw [hZ u huH] at hito
    simpa [H, fp81s21_moving_cylA, fp81s21_moving_cylJ,
      C, m, τ, α] using hito
  have hDint : IntegrableOn
      (fun u => -(Real.sqrt N)⁻¹ * fp81s21_moving_cylA R A F H hH L G ζ u +
        (1 / (2 * Real.sqrt N)) * fp81s21_moving_cylJ R A F H hH L G ζ u)
      (Ioc q s) := (hItoInt.mono_set hsub).congr_fun hpt measurableSet_Ioc
  have hDintEq :
      (∫ u in Ioc q s, itoDrift H f Z bd Φc u ζ) =
        ∫ u in Ioc q s,
          (-(Real.sqrt N)⁻¹ * fp81s21_moving_cylA R A F H hH L G ζ u +
            (1 / (2 * Real.sqrt N)) * fp81s21_moving_cylJ R A F H hH L G ζ u) :=
    setIntegral_congr_fun measurableSet_Ioc hpt
  have htest : (fun w => G (s102_obs τ α w)) =
      (fun w => Φ (W (s102_Pj H hH L w))) := by
    funext w
    dsimp [G]
    rw [← s102_Pj_eq_Lam hH L w]
  have hheat (u : ℝ) (hu : u ∈ Icc (0 : ℝ) H) :
      r2HeatFn (future H) (fun w => Φ (W (s102_Pj H hH L w))) u
        (s102_Y C m H A.P A.X ζ u) =
      gaussHeat (s102_obsCov C m τ α) G u
        (s102_obs τ α (s102_Y C m H A.P A.X ζ u)) := by
    rw [← htest]
    exact s102_heat_obs C (future H) hγ τ α G hG2 u hu _
  have hFormula : f s (Z s ζ) - f q (Z q ζ) =
      (∫ u in Ioc q s, itoDrift H f Z bd Φc u ζ) + Mart ζ := by
    simpa only [Z] using hItoEq
  rw [hfeq s ⟨hqs, by simpa [H] using hsH⟩,
      hfeq q ⟨le_rfl, hqs.trans (by simpa [H] using hsH)⟩,
      hZ s ⟨hq.trans hqs, by simpa [H] using hsH⟩,
      hZ q ⟨hq, hqs.trans (by simpa [H] using hsH)⟩] at hFormula
  rw [← hheat s ⟨hq.trans hqs, by simpa [H] using hsH⟩,
      ← hheat q ⟨hq, hqs.trans (by simpa [H] using hsH)⟩,
      hDintEq] at hFormula
  exact ⟨hDint, by simpa [H, W, G] using hFormula⟩

#print axioms fp81s21_moving_heat_c12
#print axioms fp81s21_moving_heat_ito_piece

end HRS.Fp81.S21

end
