import HRS.MS.Fp81S21MovingMeas
import HRS.MS.R2InterpAux124
import HRS.MS.R2InterpAux83
import HRS.MS.R2S11Aux10

/-!
# HRS S2.1(iii), packet 8.6: moving-reference M1

Exact exported statements in this packet:

1. `fp81s21_moving_envelope_bound` states the following. One `CE ≥ 0` is
   chosen before `u`, and for every `u ∈ [0,H]` the moving envelope is
   integrable under `A.P` with integral at most `CE`:

   ```lean
   theorem fp81s21_moving_envelope_bound
       (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
       {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
       (hphys : Fp81MovingPhysicalInputs R hN A H) :
       ∃ CE : ℝ, 0 ≤ CE ∧ ∀ u ∈ Icc (0 : ℝ) H,
         Integrable
           (fun ζ => s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
             (A.X u.toNNReal ζ) (r26t3_mu R u)) A.P ∧
         ∫ ζ, s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
           (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P ≤ CE
   ```
2. `fp81s21_moving_M1` has the unchanged stationary `S102Drift` conclusion
   for `C = r26t3_coeff R`, `m = wholeSpaceIndex p.d`, and `Pw = p.d+2`,
   applied to the moving field `u ↦ r2QuadField p.s (r26t3_mu R u) A.P
   (A.X u) ζ`. It supplies one majorant `Mb`; a.e. pathwise the drift
   conditions hold, and `ζ ↦ ∫_(0,H] Mb ζ u du` is integrable:

   ```lean
   theorem fp81s21_moving_M1
       (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
       (hH : 0 < H) {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
       {r : ℕ} {c : MultiIndex p.d → ℝ}
       (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r c hH)
       (hr : (p.d : ℝ) / 2 + 2 < r)
       (hphys : Fp81MovingPhysicalInputs R hN A H) :
       ∃ Mb : A.Ω → ℝ → ℝ,
         (∀ᵐ ζ ∂A.P,
           S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r
             ((p.d : ℝ) + 2)
             (fun u f => fp81s21_moving_r2QuadField R A u ζ f) (Mb ζ)) ∧
         Integrable (fun ζ => ∫ u in Ioc (0 : ℝ) H, Mb ζ u) A.P
   ```

Stationary sources recorded: `R2InterpAux121.s102_Env_eq`,
`s102_Env_nonneg`, `s102_pE_abs_le_Env`, `s102_Env_meas`;
`R2InterpAux122.s102_gk_int`, `s102_Env_bound`; and
`R2InterpAux125.s102_M1`. The following are the exact stationary producer
statements used for the envelope bound, row estimate, and drift interface:

```lean
theorem s102_gk_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) (M C₀ c₀ : ℝ) (hc : 0 < c₀)
    {Pw : ℝ} (hP0 : 0 ≤ Pw) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      (∀ x, Integrable (s102_gk s Pw x) (HRS.Whole.withDensityReal ρ)) ∧
      Integrable (fun x => ∫ y, s102_gk s Pw x y
        ∂(HRS.Whole.withDensityReal ρ)) (HRS.Whole.withDensityReal ρ) ∧
      ∀ x, ∫ y, s102_gk s Pw x y ∂(HRS.Whole.withDensityReal ρ) ≤ A * jbracket x ^ Pw

theorem s102_Env_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) (M L C₀ c₀ β p K : ℝ)
    (hc : 0 < c₀) (hβ : 0 < β) (hp : 1 < p) {Pw : ℝ}
    (hPw : 0 ≤ Pw) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ {ρ : Euc d → ℝ},
      IsRound2Density d s M L ρ →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      ∀ {N : ℕ}, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Y : Ω → EucConfig d N), Measurable Y →
        HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map Y) →
        Integrable (fun ζ => s102_Env (s102_gk s Pw) (Y ζ)
          (HRS.Whole.withDensityReal ρ)) P ∧
        ∫ ζ, s102_Env (s102_gk s Pw) (Y ζ)
          (HRS.Whole.withDensityReal ρ) ∂P ≤ CE

theorem s102_M1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) {C : WholeCoeff d} {m T : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hS : S102Std C m T r c) (hT : 0 < T)
    (hr : (d : ℝ) / 2 + 2 < r) {Pw : ℝ} (hP0 : 0 ≤ Pw)
    {β p K M L C₀ c₀ : ℝ} (hc : 0 < c₀) (hβ : 0 < β) (hp : 1 < p)
    {ρ : Euc d → ℝ} (hρR : IsRound2Density d s M L ρ)
    (hG : ∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (hXjm : ∀ t ∈ Icc (0 : ℝ) T,
      Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T,
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ)
        (P.map (X r.toNNReal))) :
    ∃ Mb : Ω → ℝ → ℝ,
      (∀ᵐ ζ ∂P,
        S102Drift C m T r Pw
          (fun u => r2QuadField s (HRS.Whole.withDensityReal ρ) P X u ζ)
          (Mb ζ)) ∧
      Integrable (fun ζ => ∫ u in Ioc 0 T, Mb ζ u) P
```

`R2InterpAux121.s102_Env_eq`, `s102_Env_nonneg`, `s102_pE_abs_le_Env`, and
`s102_Env_meas` are already generic in the reference measure. The moving proofs
replace the fixed `withDensityReal ρ` in `s102_Env_bound`/`s102_M1` by
`r26t3_mu R u` at the same time `u`. No stationarity assumption is used. The
common constants `c₁`, `CE`, and the row bound are selected before `u`; they can
depend on the horizon, model, particle realization, and `N`.

The interface adjustment is using moving `Fp81MovingStd` in place of stationary
`S102Std`: it supplies the same `S101Data`, sign of `ν`, and classical-adjoint
existence, but does not assert stationarity of `C.ρ`; M1 uses only the adjoint
field `hcls`, not `S102Std.hstat`, `hint`, or `hnn`. Its extra `hGram` field is
available from the moving packet. The local `S102Z` estimate is unchanged and
`s102_Z_quad` requires no
stationarity hypothesis. The particle path is replaced internally by a jointly
measurable modification equal to `A.X` almost surely for every time, to meet the
measurability step without changing the exported moving field. The supplied
reference and particle moment bounds are not needed for this M1 estimate: the
Gaussian row bound and actual-density envelope bound already give the integrable
majorant.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

private def fp81s21_m1_clipNN (H u : ℝ) : ℝ≥0 :=
  ⟨max 0 (min u H), le_max_left _ _⟩

private theorem fp81s21_m1_clip_mem (H : ℝ) (hH : 0 < H) (u : ℝ) :
    (fp81s21_m1_clipNN H u : ℝ) ∈ Icc (0 : ℝ) H := by
  constructor
  · exact (fp81s21_m1_clipNN H u).property
  · change max 0 (min u H) ≤ H
    exact max_le hH.le (min_le_right _ _)

private def fp81s21_m1_clipIcc (H : ℝ) (hH : 0 < H) (u : ℝ) : Icc (0 : ℝ) H :=
  ⟨(fp81s21_m1_clipNN H u : ℝ), fp81s21_m1_clip_mem H hH u⟩

private theorem fp81s21_m1_clip_eq (H : ℝ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) H) :
    fp81s21_m1_clipNN H u = ⟨u, hu.1⟩ := by
  apply Subtype.ext
  change max 0 (min u H) = u
  rw [min_eq_left hu.2, max_eq_right hu.1]

private theorem fp81s21_m1_clipIcc_continuous (H : ℝ) (hH : 0 < H) :
    Continuous (fp81s21_m1_clipIcc H hH) := by
  have hc : Continuous fun u : ℝ => max 0 (min u H) := by fun_prop
  exact hc.subtype_mk (fun u => fp81s21_m1_clip_mem H hH u)

/-- Timewise moving-reference form of the stationary envelope integrability and expectation
bound `s102_Env_bound`. Its constant is fixed before `u`. -/
theorem fp81s21_moving_envelope_bound
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ u ∈ Icc (0 : ℝ) H,
      Integrable
        (fun ζ => s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
          (A.X u.toNNReal ζ) (r26t3_mu R u)) A.P ∧
      ∫ ζ, s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
        (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P ≤ CE := by
  obtain ⟨M, L, hround⟩ := hphys.round2
  obtain ⟨C₀, c₀, hc₀, hgauss⟩ := hphys.gaussian_upper
  obtain ⟨q, K, hq, hactual⟩ := hphys.actual_density
  have hPw : 0 ≤ (p.d : ℝ) + 2 := by positivity
  obtain ⟨CE, hCE0, hCE⟩ := s102_Env_bound p.hd p.hs0 p.hs M L C₀ c₀ p.β q K
    hc₀ p.hβ hq hPw
  refine ⟨CE, hCE0, fun u hu => ?_⟩
  have hρ := hround u hu
  have hG := hgauss u hu
  have hdens := hactual u hu
  exact hCE hρ hG hN A.P (A.X u.toNNReal) ((A.strong H).adapted u.toNNReal) hdens

/-- The explicitly moving version of the S10.2 quadratic field. -/
def fp81s21_moving_r2QuadField
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (u : ℝ) (ζ : A.Ω) (f : Euc p.d → ℝ) : ℝ :=
  r2QuadField p.s (r26t3_mu R u) A.P A.X u ζ f

private def fp81s21_m1_envActual
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (u : ℝ) (ζ : A.Ω) : ℝ :=
  s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
    (A.X (fp81s21_m1_clipNN H u) ζ)
    (r26t3_mu R (fp81s21_m1_clipNN H u))

private def fp81s21_m1_majorant
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (c₁ : ℝ) (ec : ℝ → ℝ) (ζ : A.Ω) (u : ℝ) : ℝ :=
  c₁ * N * (fp81s21_m1_envActual (H := H) R A u ζ + ec u)

private theorem fp81s21_m1_envClip_eq
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) H) :
    ∀ ζ, fp81s21_m1_envActual (H := H) R A u ζ =
      s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
        (A.X u.toNNReal ζ) (r26t3_mu R u) := by
  intro ζ
  have hclip := fp81s21_m1_clip_eq H hu
  have htimeReal : (fp81s21_m1_clipNN H u : ℝ) = u := congrArg Subtype.val hclip
  have htimeNN : fp81s21_m1_clipNN H u = u.toNNReal := by
    apply Subtype.ext
    change (fp81s21_m1_clipNN H u : ℝ) = (u.toNNReal : ℝ)
    rw [htimeReal]
    simp [Real.toNNReal_of_nonneg hu.1]
  unfold fp81s21_m1_envActual
  have huReal : (u.toNNReal : ℝ) = u := by
    simp [Real.toNNReal_of_nonneg hu.1]
  rw [htimeNN, huReal]

set_option maxHeartbeats 3200000 in
private theorem fp81s21_moving_pair_time_meas
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {ρ : ℝ → Euc d → ℝ} {k : ℝ → Euc d → Euc d → ℝ}
    {X : ℝ × Ω → EucConfig d N}
    (hρ : Measurable fun q : ℝ × Euc d => ρ q.1 q.2)
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    (hk : Measurable fun q : ℝ × Euc d × Euc d => k q.1 q.2.1 q.2.2)
    (hX : Measurable X) :
    Measurable (fun q : ℝ × Ω =>
      pairEnergy (k q.1) (X q) (HRS.Whole.withDensityReal (ρ q.1))) := by
  have hpE := fp81s21_moving_pairEnergy_joint_meas (N := N) hρ hρ0 hk
  exact hpE.comp (measurable_fst.prodMk hX)

private theorem fp81s21_moving_M1_product_integrable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H CE c₁ : ℝ} {N : ℕ} (hc₁ : 0 ≤ c₁)
    {F : ℝ × Ω → ℝ} (hF : Measurable F) (hF0 : ∀ q, 0 ≤ F q)
    (hE : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun ζ => F (u, ζ)) P ∧ ∫ ζ, F (u, ζ) ∂P ≤ CE) :
    Integrable (fun q : ℝ × Ω =>
      c₁ * N * (F q + ∫ ζ, F (q.1, ζ) ∂P))
      ((volume.restrict (Icc (0 : ℝ) H)).prod P) := by
  classical
  let ec : ℝ → ℝ := fun u => ∫ ζ, F (u, ζ) ∂P
  have hecm : Measurable ec := fp81s21_moving_total_integral_meas hF
  have hec0 : ∀ u, 0 ≤ ec u := fun u => integral_nonneg fun ζ => hF0 (u, ζ)
  let G : ℝ × Ω → ℝ := fun q => c₁ * N * (F q + ec q.1)
  have hGm : Measurable G := measurable_const.mul (hF.add (hecm.comp measurable_fst))
  refine s102_prodInt (C := c₁ * N * (2 * CE)) hGm fun u hu => ?_
  obtain ⟨hi, hb⟩ := hE u hu
  have hslice : Integrable (fun ζ => c₁ * N * (F (u, ζ) + ec u)) P :=
    (hi.add (integrable_const _)).const_mul _
  have hnn : ∀ ζ, 0 ≤ c₁ * N * (F (u, ζ) + ec u) := fun ζ =>
    mul_nonneg (mul_nonneg hc₁ (Nat.cast_nonneg N))
      (add_nonneg (hF0 (u, ζ)) (hec0 u))
  rw [show (fun ζ => ‖G (u, ζ)‖ₑ) =
    fun ζ => ENNReal.ofReal (c₁ * N * (F (u, ζ) + ec u)) by
      funext ζ; rw [Real.enorm_eq_ofReal (hnn ζ)]]
  rw [← ofReal_integral_eq_lintegral_ofReal hslice (Eventually.of_forall hnn)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_const_mul, integral_add hi (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have hcN : 0 ≤ c₁ * N := mul_nonneg hc₁ (Nat.cast_nonneg N)
  exact mul_le_mul_of_nonneg_left (by linarith) hcN

private structure Fp81S21MovingM1DensityCtx
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H) : Type where
  rhoClip : ℝ → Euc p.d → ℝ
  rhoClip_meas : Measurable (fun q : ℝ × Euc p.d => rhoClip q.1 q.2)
  rhoClip_nonneg : ∀ u x, 0 ≤ rhoClip u x
  rhoClip_eq : ∀ u ∈ Icc (0 : ℝ) H, rhoClip u = R.ρ u
  rhoClip_def : ∀ u x, rhoClip u x = R.ρ (fp81s21_m1_clipIcc H hH u) x

private structure Fp81S21MovingM1ParticleCtx
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) : Type where
  Xjoint : ℝ × A.Ω → EucConfig p.d N
  Xjoint_meas : Measurable Xjoint
  Xae : ∀ᵐ ζ ∂A.P, ∀ t : ℝ, Xjoint (t, ζ) = A.X t.toNNReal ζ

private structure Fp81S21MovingM1EnvFunctionCtx
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (density : Fp81S21MovingM1DensityCtx p R hH)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A) : Type where
  Xclip : ℝ × A.Ω → EucConfig p.d N
  Xclip_def : ∀ q, Xclip q =
    particle.Xjoint ((fp81s21_m1_clipNN H q.1 : ℝ), q.2)
  Xclip_meas : Measurable Xclip
  EnvV : ℝ × A.Ω → ℝ
  EnvV_def : ∀ q, EnvV q = s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
    (Xclip q) (HRS.Whole.withDensityReal (density.rhoClip q.1))
  EnvV_meas : Measurable EnvV
  EnvV_nonneg : ∀ q, 0 ≤ EnvV q
  ec : ℝ → ℝ
  ec_def : ∀ u, ec u = ∫ ζ, EnvV (u, ζ) ∂A.P
  ec_nonneg : ∀ u, 0 ≤ ec u

private def fp81s21_m1_clipPath
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A) :
    ℝ × A.Ω → EucConfig p.d N := fun q =>
      particle.Xjoint ((fp81s21_m1_clipNN H q.1 : ℝ), q.2)

private def fp81s21_m1_kernel
    (p : Parameters) : ℝ → Euc p.d → Euc p.d → ℝ :=
  fun _ => s102_gk p.s ((p.d : ℝ) + 2)

private def fp81s21_m1_movingEnvJointFn
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (density : Fp81S21MovingM1DensityCtx p R hH) {N : ℕ} :
    ℝ × EucConfig p.d N → ℝ := fun q =>
      s102_Env (fp81s21_m1_kernel p q.1) q.2
        (HRS.Whole.withDensityReal (density.rhoClip q.1))

private def fp81s21_m1_movingEnvMap
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A) :
    ℝ × A.Ω → ℝ × EucConfig p.d N := fun q =>
      (q.1, fp81s21_m1_clipPath R hH hN A particle q)

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
private theorem fp81s21_m1_clipPath_meas
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A) :
    Measurable (fp81s21_m1_clipPath R hH hN A particle) := by
  let clip : ℝ → Icc (0 : ℝ) H := fp81s21_m1_clipIcc H hH
  have hclipContinuous : Continuous clip := fp81s21_m1_clipIcc_continuous H hH
  have htime : Measurable fun u : ℝ => (fp81s21_m1_clipNN H u : ℝ) :=
    (continuous_subtype_val.comp hclipContinuous).measurable
  exact particle.Xjoint_meas.comp ((htime.comp measurable_fst).prodMk measurable_snd)

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 12800000 in
private theorem fp81s21_m1_movingEnv_joint_meas
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (density : Fp81S21MovingM1DensityCtx p R hH) {N : ℕ} :
    Measurable (fp81s21_m1_movingEnvJointFn p R hH density (N := N)) := by
  have hgtime : Measurable fun q : ℝ × Euc p.d × Euc p.d =>
      (fp81s21_m1_kernel p q.1) q.2.1 q.2.2 := by
    change Measurable fun q : ℝ × Euc p.d × Euc p.d =>
      s102_gk p.s ((p.d : ℝ) + 2) q.2.1 q.2.2
    exact (s102_gk_meas p.s ((p.d : ℝ) + 2)).comp
      (measurable_snd.fst.prodMk measurable_snd.snd)
  exact fp81s21_moving_envelope_joint_meas
    (d := p.d) (N := N) (ρ := density.rhoClip) (g := fp81s21_m1_kernel p)
    density.rhoClip_meas density.rhoClip_nonneg hgtime

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
private theorem fp81s21_m1_movingEnv_map_meas
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A) :
    Measurable (fp81s21_m1_movingEnvMap R hH hN A particle) := by
  exact measurable_fst.prodMk (fp81s21_m1_clipPath_meas R hH hN A particle)

private structure Fp81S21MovingM1BaseCtx
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (c₁ : ℝ) : Type where
  density : Fp81S21MovingM1DensityCtx p R hH
  particle : Fp81S21MovingM1ParticleCtx p R hH hN A
  env : Fp81S21MovingM1EnvFunctionCtx p R hH hN A density particle
  c₁_nonneg : 0 ≤ c₁
  envEq : ∀ u, (fun ζ => env.EnvV (u, ζ)) =ᵐ[A.P]
    (fun ζ => fp81s21_m1_envActual (H := H) R A u ζ)
  pathEq : ∀ᵐ ζ ∂A.P, ∀ u,
    c₁ * N * (env.EnvV (u, ζ) + env.ec u) =
      fp81s21_m1_majorant (H := H) R A c₁ env.ec ζ u

private structure Fp81S21MovingM1EnvCtx
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (CE c₁ : ℝ) : Type where
  base : Fp81S21MovingM1BaseCtx p R hH hN A c₁
  ec_eq : ∀ u ∈ Icc (0 : ℝ) H,
    base.env.ec u = ∫ ζ, s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
      (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P
  env_actual_integrable : ∀ u ∈ Icc (0 : ℝ) H,
    Integrable (fun ζ => s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
      (A.X u.toNNReal ζ) (r26t3_mu R u)) A.P
  envV_integrable_bound : ∀ u ∈ Icc (0 : ℝ) H,
    Integrable (fun ζ => base.env.EnvV (u, ζ)) A.P ∧
      ∫ ζ, base.env.EnvV (u, ζ) ∂A.P ≤ CE
  rowsAt : ∀ u ∈ Icc (0 : ℝ) H,
    (∀ x, Integrable (s102_gk p.s ((p.d : ℝ) + 2) x) (r26t3_mu R u)) ∧
    Integrable (fun x => ∫ y, s102_gk p.s ((p.d : ℝ) + 2) x y ∂(r26t3_mu R u))
      (r26t3_mu R u)
  probAt : ∀ u ∈ Icc (0 : ℝ) H, IsProbabilityMeasure (r26t3_mu R u)

private theorem fp81s21_moving_M1_density_context
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∃ density : Fp81S21MovingM1DensityCtx p R hH, True := by
  classical
  obtain ⟨M, L, hround⟩ := hphys.round2
  let clip : ℝ → Icc (0 : ℝ) H := fp81s21_m1_clipIcc H hH
  let ρclip : ℝ → Euc p.d → ℝ := fun u x => R.ρ (clip u) x
  have hclipContinuous : Continuous clip := fp81s21_m1_clipIcc_continuous H hH
  have hρmap : Measurable (fun q : ℝ × Euc p.d => (clip q.1, q.2)) := by
    exact (hclipContinuous.measurable.comp measurable_fst).prodMk measurable_snd
  have hρmeas : Measurable (fun q : ℝ × Euc p.d => ρclip q.1 q.2) :=
    hphys.density_joint.comp hρmap
  have hρnonneg : ∀ u x, 0 ≤ ρclip u x := by
    intro u x
    exact (hround (clip u) (clip u).property).prob.nonneg x
  have hρeq : ∀ u ∈ Icc (0 : ℝ) H, ρclip u = R.ρ u := by
    intro u hu
    funext x
    change R.ρ (↑(clip u)) x = R.ρ u x
    have hc := fp81s21_m1_clip_eq H hu
    have hval : (↑(clip u) : ℝ) = u := by
      change (fp81s21_m1_clipNN H u : ℝ) = u
      exact congrArg Subtype.val hc
    rw [hval]
  refine ⟨{
    rhoClip := ρclip
    rhoClip_meas := hρmeas
    rhoClip_nonneg := hρnonneg
    rhoClip_eq := hρeq
    rhoClip_def := fun _ _ => rfl
  }, trivial⟩

private theorem fp81s21_moving_M1_particle_context
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) :
    ∃ particle : Fp81S21MovingM1ParticleCtx p R hH hN A, True := by
  classical
  obtain ⟨Xjoint, hXjoint, hXae⟩ :=
    HRS.MS.R2S11.s11_X_joint (fun t => (A.strong H).adapted t) (A.strong H).cont
  exact ⟨{ Xjoint := Xjoint, Xjoint_meas := hXjoint, Xae := hXae }, trivial⟩

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 12800000 in
private theorem fp81s21_moving_M1_env_function_context
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (density : Fp81S21MovingM1DensityCtx p R hH)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A) :
    ∃ env : Fp81S21MovingM1EnvFunctionCtx p R hH hN A density particle, True := by
  let Xclip := fp81s21_m1_clipPath R hH hN A particle
  let EnvV : ℝ × A.Ω → ℝ :=
    fp81s21_m1_movingEnvJointFn p R hH density (N := N) ∘
      fp81s21_m1_movingEnvMap R hH hN A particle
  let ec : ℝ → ℝ := fun u => ∫ ζ, EnvV (u, ζ) ∂A.P
  have hEnvVNonneg : ∀ q, 0 ≤ EnvV q := by
    intro q
    change 0 ≤ s102_Env (fp81s21_m1_kernel p q.1)
      (fp81s21_m1_clipPath R hH hN A particle q)
      (HRS.Whole.withDensityReal (density.rhoClip q.1))
    exact s102_Env_nonneg (s102_gk_nonneg p.s ((p.d : ℝ) + 2)) _ _
  have hEnvVMeas : Measurable EnvV :=
    (fp81s21_m1_movingEnv_joint_meas R hH density (N := N)).comp
      (fp81s21_m1_movingEnv_map_meas R hH hN A particle)
  refine ⟨{
    Xclip := Xclip
    Xclip_def := fun _ => rfl
    Xclip_meas := fp81s21_m1_clipPath_meas R hH hN A particle
    EnvV := EnvV
    EnvV_def := fun _ => rfl
    EnvV_meas := hEnvVMeas
    EnvV_nonneg := hEnvVNonneg
    ec := ec
    ec_def := fun _ => rfl
    ec_nonneg := fun u => integral_nonneg fun ζ => hEnvVNonneg (u, ζ)
  }, trivial⟩

private theorem fp81s21_moving_M1_env_eq
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (density : Fp81S21MovingM1DensityCtx p R hH)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A)
    (env : Fp81S21MovingM1EnvFunctionCtx p R hH hN A density particle) :
    ∀ u, (fun ζ => env.EnvV (u, ζ)) =ᵐ[A.P]
      (fun ζ => fp81s21_m1_envActual (H := H) R A u ζ) := by
  classical
  let clip : ℝ → Icc (0 : ℝ) H := fp81s21_m1_clipIcc H hH
  have hμclip (u : ℝ) :
      r26t3_mu R (fp81s21_m1_clipNN H u) =
        HRS.Whole.withDensityReal (density.rhoClip u) := by
    have hρ : density.rhoClip u = fun x => R.ρ (clip u) x := by
      funext x
      exact density.rhoClip_def u x
    rw [hρ]
    rfl
  intro u
  filter_upwards [particle.Xae] with ζ hζ
  have htime := hζ (fp81s21_m1_clipNN H u : ℝ)
  have htimeNN : ((fp81s21_m1_clipNN H u : ℝ).toNNReal) =
      fp81s21_m1_clipNN H u := by
    apply Subtype.ext
    simp [Real.toNNReal_of_nonneg (fp81s21_m1_clipNN H u).property]
  rw [env.EnvV_def, env.Xclip_def, fp81s21_m1_envActual, hμclip]
  rw [htimeNN] at htime
  rw [htime]

private theorem fp81s21_moving_M1_path_majorant_eq
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (density : Fp81S21MovingM1DensityCtx p R hH)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A)
    (env : Fp81S21MovingM1EnvFunctionCtx p R hH hN A density particle)
    (c₁ : ℝ) :
    ∀ᵐ ζ ∂A.P, ∀ u,
      c₁ * N * (env.EnvV (u, ζ) + env.ec u) =
        fp81s21_m1_majorant (H := H) R A c₁ env.ec ζ u := by
  classical
  let clip : ℝ → Icc (0 : ℝ) H := fp81s21_m1_clipIcc H hH
  have hμclip (u : ℝ) :
      r26t3_mu R (fp81s21_m1_clipNN H u) =
        HRS.Whole.withDensityReal (density.rhoClip u) := by
    have hρ : density.rhoClip u = fun x => R.ρ (clip u) x := by
      funext x
      exact density.rhoClip_def u x
    rw [hρ]
    rfl
  filter_upwards [particle.Xae] with ζ hζ
  intro u
  have htime := hζ (fp81s21_m1_clipNN H u : ℝ)
  have htimeNN : ((fp81s21_m1_clipNN H u : ℝ).toNNReal) =
      fp81s21_m1_clipNN H u := by
    apply Subtype.ext
    simp [Real.toNNReal_of_nonneg (fp81s21_m1_clipNN H u).property]
  rw [fp81s21_m1_majorant, fp81s21_m1_envActual, env.EnvV_def,
    env.Xclip_def, hμclip]
  rw [htimeNN] at htime
  rw [htime]

private theorem fp81s21_moving_M1_base_context
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (density : Fp81S21MovingM1DensityCtx p R hH)
    (particle : Fp81S21MovingM1ParticleCtx p R hH hN A)
    (env : Fp81S21MovingM1EnvFunctionCtx p R hH hN A density particle)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁) :
    ∃ base : Fp81S21MovingM1BaseCtx p R hH hN A c₁, True := by
  refine ⟨{
    density := density
    particle := particle
    env := env
    c₁_nonneg := hc₁
    envEq := fp81s21_moving_M1_env_eq p R hH hN A density particle env
    pathEq := fp81s21_moving_M1_path_majorant_eq p R hH hN A density particle env c₁
  }, trivial⟩

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 6400000 in
private theorem fp81s21_moving_M1_envelope_context
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (CE : ℝ)
    (hCE : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun ζ => s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
        (A.X u.toNNReal ζ) (r26t3_mu R u)) A.P ∧
        ∫ ζ, s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
          (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P ≤ CE) :
    ∃ ctx : Fp81S21MovingM1EnvCtx p R hH hN A CE c₁, True := by
  classical
  let Pw : ℝ := (p.d : ℝ) + 2
  have hPw : 0 ≤ Pw := by dsimp [Pw]; positivity
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide) p.hd
  obtain ⟨M, L, hround⟩ := hphys.round2
  obtain ⟨C₀, c₀, hc₀, hgauss⟩ := hphys.gaussian_upper
  obtain ⟨Aenv, hAenv0, hRows⟩ := fp81s21_moving_envelope_rows_integrable
    hd1 p.hs0 p.hs hc₀ hPw (fun u hu => hround u hu) (fun u hu => hgauss u hu)
  obtain ⟨density, _⟩ :=
    fp81s21_moving_M1_density_context p R hH hN A hphys
  obtain ⟨particle, _⟩ := fp81s21_moving_M1_particle_context p R hH hN A
  obtain ⟨env, _⟩ :=
    fp81s21_moving_M1_env_function_context p R hH hN A density particle
  obtain ⟨base, _⟩ :=
    fp81s21_moving_M1_base_context p R hH hN A density particle env c₁ hc₁
  have hEactual : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun ζ => s102_Env (s102_gk p.s Pw)
        (A.X u.toNNReal ζ) (r26t3_mu R u)) A.P ∧
        ∫ ζ, s102_Env (s102_gk p.s Pw)
          (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P ≤ CE := by
    intro u hu
    exact hCE u hu
  have hEversion : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun ζ => base.env.EnvV (u, ζ)) A.P ∧
        ∫ ζ, base.env.EnvV (u, ζ) ∂A.P ≤ CE := by
    intro u hu
    obtain ⟨hi, hb⟩ := hEactual u hu
    have hEq := (base.envEq u).trans
      (Eventually.of_forall (fp81s21_m1_envClip_eq R A hu))
    have hiV : Integrable (fun ζ => base.env.EnvV (u, ζ)) A.P := hi.congr hEq.symm
    have hIntEq : (∫ ζ, base.env.EnvV (u, ζ) ∂A.P) =
        ∫ ζ, s102_Env (s102_gk p.s Pw) (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P :=
          integral_congr_ae hEq
    exact ⟨hiV, by rw [hIntEq]; exact hb⟩
  have hEcEq : ∀ u ∈ Icc (0 : ℝ) H,
      base.env.ec u = ∫ ζ, s102_Env (s102_gk p.s Pw)
        (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P := by
    intro u hu
    rw [base.env.ec_def]
    exact integral_congr_ae ((base.envEq u).trans
      (Eventually.of_forall (fp81s21_m1_envClip_eq R A hu)))
  have hrowsAt : ∀ u ∈ Icc (0 : ℝ) H,
      (∀ x, Integrable (s102_gk p.s Pw x) (r26t3_mu R u)) ∧
      Integrable (fun x => ∫ y, s102_gk p.s Pw x y ∂(r26t3_mu R u))
        (r26t3_mu R u) := by
    intro u hu
    obtain ⟨hgi, hgH, -⟩ := hRows u hu
    exact ⟨by simpa [r26t3_mu] using hgi, by simpa [r26t3_mu] using hgH⟩
  have hprobAt : ∀ u ∈ Icc (0 : ℝ) H,
      IsProbabilityMeasure (r26t3_mu R u) := by
    intro u hu
    exact HRS.Whole.Q34.isProbabilityMeasure_nu (hround u hu).prob
  refine ⟨{
    base := base
    ec_eq := hEcEq
    env_actual_integrable := fun u hu => (hEactual u hu).1
    envV_integrable_bound := hEversion
    rowsAt := hrowsAt
    probAt := hprobAt
  }, trivial⟩

private theorem fp81s21_moving_M1_path_integrable
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (CE c₁ : ℝ)
    (ctx : Fp81S21MovingM1EnvCtx p R hH hN A CE c₁) :
    (∀ᵐ ζ ∂A.P,
        IntegrableOn (fun u => fp81s21_m1_majorant (H := H) R A c₁ ctx.base.env.ec ζ u)
          (Icc (0 : ℝ) H)) ∧
      Integrable (fun ζ => ∫ u in Ioc (0 : ℝ) H,
        fp81s21_m1_majorant (H := H) R A c₁ ctx.base.env.ec ζ u) A.P := by
  classical
  let MtV : ℝ × A.Ω → ℝ := fun q =>
    c₁ * N * (ctx.base.env.EnvV q + ctx.base.env.ec q.1)
  have hEprod : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun ζ => ctx.base.env.EnvV (u, ζ)) A.P ∧
        ∫ ζ, ctx.base.env.EnvV (u, ζ) ∂A.P ≤ CE := ctx.envV_integrable_bound
  have hprod : Integrable MtV ((volume.restrict (Icc (0 : ℝ) H)).prod A.P) := by
    simpa [MtV, ctx.base.env.ec_def] using
      (fp81s21_moving_M1_product_integrable (P := A.P) (H := H) (CE := CE)
        (c₁ := c₁) (N := N) ctx.base.c₁_nonneg ctx.base.env.EnvV_meas
        ctx.base.env.EnvV_nonneg hEprod)
  have hMbInt : ∀ᵐ ζ ∂A.P,
      IntegrableOn (fun u => fp81s21_m1_majorant (H := H) R A c₁ ctx.base.env.ec ζ u)
        (Icc (0 : ℝ) H) := by
    filter_upwards [hprod.prod_left_ae, ctx.base.pathEq] with ζ hζ hEq
    refine ⟨?_, ?_⟩
    · exact hζ.1.congr (Filter.Eventually.of_forall fun u => hEq u)
    · exact hζ.2.congr (Filter.Eventually.of_forall fun u => hEq u)
  refine ⟨hMbInt, ?_⟩
  have hVint := hprod.integral_prod_right
  have haeEq : (fun ζ => ∫ u in Icc (0 : ℝ) H, MtV (u, ζ)) =ᵐ[A.P]
      (fun ζ => ∫ u in Icc (0 : ℝ) H,
        fp81s21_m1_majorant (H := H) R A c₁ ctx.base.env.ec ζ u) := by
    filter_upwards [ctx.base.pathEq] with ζ hζ
    exact integral_congr_ae (Eventually.of_forall fun u => hζ u)
  refine hVint.congr ?_
  exact haeEq.trans (Filter.Eventually.of_forall fun ζ => integral_Icc_eq_integral_Ioc)

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 1600000 in
private theorem fp81s21_moving_M1_coord_meas
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (A : Particle R N) {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r c hH)
    {ρclip : ℝ → Euc p.d → ℝ}
    (hρclip : Measurable fun q : ℝ × Euc p.d => ρclip q.1 q.2)
    (hρnonneg : ∀ u x, 0 ≤ ρclip u x)
    (hρeq : ∀ u ∈ Icc (0 : ℝ) H, ρclip u = R.ρ u)
    (Xjoint : ℝ × A.Ω → EucConfig p.d N) (hXjoint : Measurable Xjoint)
    (hXae : ∀ᵐ ζ ∂A.P, ∀ t : ℝ, Xjoint (t, ζ) = A.X t.toNNReal ζ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) (ζ : A.Ω)
    (hXζ : ∀ t : ℝ, Xjoint (t, ζ) = A.X t.toNNReal ζ) (α : MultiIndex p.d) :
    AEStronglyMeasurable
      (fun u : ℝ => fp81s21_moving_r2QuadField R A u ζ
        (propagatorW (r26t3_coeff R) u t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))
      (volume.restrict (Icc 0 t)) := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  have hf := s102_propagator_classical (hstd.hcls α t ht)
  obtain ⟨hK, -, hKm, hKr, -⟩ := s102_kernel_pkg p.hs0 hf
  let ccv : ℝ → ℝ := fun u => ∫ ζ',
    pairEnergy (hK u) (Xjoint (u, ζ')) (HRS.Whole.withDensityReal (ρclip u)) ∂A.P
  have hpairV : Measurable fun q : ℝ × A.Ω =>
      pairEnergy (hK q.1) (Xjoint q) (HRS.Whole.withDensityReal (ρclip q.1)) :=
    fp81s21_moving_pair_time_meas hρclip hρnonneg hKm hXjoint
  have hccv : Measurable ccv := fp81s21_moving_total_integral_meas hpairV
  have hpairFixed : Measurable fun u : ℝ =>
      pairEnergy (hK u) (Xjoint (u, ζ)) (HRS.Whole.withDensityReal (ρclip u)) :=
    hpairV.comp (measurable_id.prodMk measurable_const)
  have hRm : Measurable fun u : ℝ =>
      (N : ℝ) * (pairEnergy (hK u) (Xjoint (u, ζ))
        (HRS.Whole.withDensityReal (ρclip u)) - ccv u) :=
    measurable_const.mul (hpairFixed.sub hccv)
  have hRae : (fun u : ℝ =>
      (N : ℝ) * (pairEnergy (hK u) (Xjoint (u, ζ))
        (HRS.Whole.withDensityReal (ρclip u)) - ccv u)) =ᵐ[volume.restrict (Icc 0 t)]
      (fun u => fp81s21_moving_r2QuadField R A u ζ
        (propagatorW C u t (oscTestFun m α))) := by
    refine (ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun u hu => ?_)
    have huH : u ∈ Icc (0 : ℝ) H := ⟨hu.1, hu.2.trans ht.2⟩
    have hkr := hKr u hu
    have hρeq' := hρeq u huH
    have hμeq : HRS.Whole.withDensityReal (ρclip u) = r26t3_mu R u := by
      rw [hρeq', r26t3_mu]
    have hXeq : Xjoint (u, ζ) = A.X u.toNNReal ζ := hXζ u
    have hccEq : ccv u = ∫ ζ', pairEnergy (hK u) (A.X u.toNNReal ζ')
        (r26t3_mu R u) ∂A.P := by
      rw [show ccv u = ∫ ζ', pairEnergy (hK u) (Xjoint (u, ζ'))
        (HRS.Whole.withDensityReal (ρclip u)) ∂A.P by rfl]
      rw [hμeq]
      have hslice : (fun ζ' => Xjoint (u, ζ')) =ᵐ[A.P]
          (fun ζ' => A.X u.toNNReal ζ') := by
        filter_upwards [hXae] with ζ' hζ'
        exact hζ' u
      exact integral_congr_ae (hslice.mono fun ζ' hζ' => by simp [hζ'])
    simp [fp81s21_moving_r2QuadField, r2QuadField, hkr, hXeq, hμeq, hccEq, C, m]
  exact hRm.aestronglyMeasurable.congr hRae

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 1600000 in
private theorem fp81s21_moving_M1_drift
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (A : Particle R N) {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r c hH)
    (hr : (p.d : ℝ) / 2 + 2 < r)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁)
    (hker : ∀ f : Euc p.d → ℝ, ContDiff ℝ r f → weightedSobolevE r ((p.d : ℝ) + 2) f < ⊤ →
      IsR2PolyPairKernel p.s ((p.d : ℝ) + 2)
        (c₁ * (weightedSobolevE r ((p.d : ℝ) + 2) f).toReal)
        (commutatorKernel p.d p.s (fun z => gradient f z)) ∧
      ∀ x y, |commutatorKernel p.d p.s (fun z => gradient f z) x y| ≤
        (c₁ * (weightedSobolevE r ((p.d : ℝ) + 2) f).toReal) *
          s102_gk p.s ((p.d : ℝ) + 2) x y)
    {ρclip : ℝ → Euc p.d → ℝ}
    (hρclip : Measurable fun q : ℝ × Euc p.d => ρclip q.1 q.2)
    (hρnonneg : ∀ u x, 0 ≤ ρclip u x)
    (hρeq : ∀ u ∈ Icc (0 : ℝ) H, ρclip u = R.ρ u)
    (Xjoint : ℝ × A.Ω → EucConfig p.d N) (hXjoint : Measurable Xjoint)
    (hXae : ∀ᵐ ζ ∂A.P, ∀ t : ℝ, Xjoint (t, ζ) = A.X t.toNNReal ζ)
    (ec : ℝ → ℝ) (hec0 : ∀ u, 0 ≤ ec u)
    (hEcEq : ∀ u ∈ Icc (0 : ℝ) H,
      ec u = ∫ ζ, s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
        (A.X u.toNNReal ζ) (r26t3_mu R u) ∂A.P)
    (hEactual : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun ζ => s102_Env (s102_gk p.s ((p.d : ℝ) + 2))
        (A.X u.toNNReal ζ) (r26t3_mu R u)) A.P)
    (hRowsAt : ∀ u ∈ Icc (0 : ℝ) H,
      (∀ x, Integrable (s102_gk p.s ((p.d : ℝ) + 2) x) (r26t3_mu R u)) ∧
      Integrable (fun x => ∫ y, s102_gk p.s ((p.d : ℝ) + 2) x y ∂(r26t3_mu R u))
        (r26t3_mu R u))
    (hprobAt : ∀ u ∈ Icc (0 : ℝ) H, IsProbabilityMeasure (r26t3_mu R u))
    (hMbInt : ∀ᵐ ζ ∂A.P,
      IntegrableOn (fun u => fp81s21_m1_majorant (H := H) R A c₁ ec ζ u) (Icc (0 : ℝ) H)) :
    ∀ᵐ ζ ∂A.P,
      S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r
        ((p.d : ℝ) + 2)
        (fun u f => fp81s21_moving_r2QuadField R A u ζ f)
        (fp81s21_m1_majorant (H := H) R A c₁ ec ζ) := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let Pw : ℝ := (p.d : ℝ) + 2
  have hZAt : ∀ u ∈ Icc (0 : ℝ) H, ∀ ζ : A.Ω,
      S102Z r Pw (fun f => s102_fld A.P (r26t3_mu R u)
        (A.X u.toNNReal) (commutatorKernel p.d p.s (fun x => gradient f x)) ζ) ∧
      ∀ f, IsR2WeightedTest r Pw f →
        |s102_fld A.P (r26t3_mu R u) (A.X u.toNNReal)
          (commutatorKernel p.d p.s (fun x => gradient f x)) ζ| ≤
          (c₁ * N * (s102_Env (s102_gk p.s Pw) (A.X u.toNNReal ζ)
            (r26t3_mu R u) +
            ∫ ζ', s102_Env (s102_gk p.s Pw) (A.X u.toNNReal ζ')
              (r26t3_mu R u) ∂A.P)) * (weightedSobolevE r Pw f).toReal := by
    intro u hu ζ
    letI : IsProbabilityMeasure (r26t3_mu R u) := hprobAt u hu
    exact s102_Z_quad r hr hc₁ hker (hRowsAt u hu).1 (hRowsAt u hu).2
      A.P (A.X u.toNNReal) ((A.strong H).adapted u.toNNReal) (hEactual u hu) ζ
  have hMbNonneg : ∀ ζ u, 0 ≤ fp81s21_m1_majorant (H := H) R A c₁ ec ζ u := by
    intro ζ u
    unfold fp81s21_m1_majorant fp81s21_m1_envActual
    exact mul_nonneg (mul_nonneg hc₁ (Nat.cast_nonneg N))
      (add_nonneg (s102_Env_nonneg (s102_gk_nonneg p.s ((p.d : ℝ) + 2))
        (A.X (fp81s21_m1_clipNN H u) ζ)
        (r26t3_mu R (fp81s21_m1_clipNN H u))) (hec0 u))
  filter_upwards [hMbInt, hXae] with ζ hζ hXζ
  refine ⟨?_, ?_, ?_, hζ, ?_⟩
  · intro u hu
    have hZ := hZAt u hu ζ
    have heq : (fun f => s102_fld A.P (r26t3_mu R u)
        (A.X u.toNNReal) (commutatorKernel p.d p.s (fun x => gradient f x)) ζ) =
        (fun f => fp81s21_moving_r2QuadField R A u ζ f) := by
      funext f
      rfl
    rw [← heq]
    exact hZ.1
  · intro u hu f hf
    have hZ := (hZAt u hu ζ).2 f hf
    have hEnv : fp81s21_m1_envActual (H := H) R A u ζ =
        s102_Env (s102_gk p.s Pw) (A.X u.toNNReal ζ) (r26t3_mu R u) :=
      fp81s21_m1_envClip_eq R A hu ζ
    have hEc : ec u = ∫ ζ', s102_Env (s102_gk p.s Pw)
        (A.X u.toNNReal ζ') (r26t3_mu R u) ∂A.P := hEcEq u hu
    rw [fp81s21_m1_majorant, hEnv, hEc]
    simpa [fp81s21_moving_r2QuadField, r2QuadField, s102_fld, C, m, Pw] using hZ
  · exact hMbNonneg ζ
  · intro t ht α
    exact fp81s21_moving_M1_coord_meas p R hH A hstd hρclip hρnonneg hρeq
      Xjoint hXjoint hXae t ht ζ hXζ α

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 400000 in
theorem fp81s21_moving_M1
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r c hH)
    (hr : (p.d : ℝ) / 2 + 2 < r)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∃ Mb : A.Ω → ℝ → ℝ,
      (∀ᵐ ζ ∂A.P,
        S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r
          ((p.d : ℝ) + 2)
          (fun u f => fp81s21_moving_r2QuadField R A u ζ f) (Mb ζ)) ∧
      Integrable (fun ζ => ∫ u in Ioc (0 : ℝ) H, Mb ζ u) A.P := by
  classical
  let Pw : ℝ := (p.d : ℝ) + 2
  have hPw : 0 ≤ Pw := by dsimp [Pw]; positivity
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide) p.hd
  obtain ⟨c₁, hc₁, hker⟩ := s102_comm_poly hd1 p.hs0 hPw r hr
  obtain ⟨CE, hCE0, hCE⟩ := fp81s21_moving_envelope_bound p R hN A hphys
  obtain ⟨ctx, _⟩ := fp81s21_moving_M1_envelope_context p R hH hN A hphys c₁ hc₁ CE
    (fun u hu => hCE u hu)
  let Mb : A.Ω → ℝ → ℝ := fp81s21_m1_majorant (H := H) R A c₁ ctx.base.env.ec
  obtain ⟨hMbInt, hMbIntegral⟩ :=
    fp81s21_moving_M1_path_integrable p R hH hN A CE c₁ ctx
  have hS102 := fp81s21_moving_M1_drift p R hH A hstd hr c₁ hc₁ hker
    ctx.base.density.rhoClip_meas ctx.base.density.rhoClip_nonneg
    ctx.base.density.rhoClip_eq
    ctx.base.particle.Xjoint ctx.base.particle.Xjoint_meas ctx.base.particle.Xae
    ctx.base.env.ec ctx.base.env.ec_nonneg ctx.ec_eq ctx.env_actual_integrable
    ctx.rowsAt ctx.probAt hMbInt
  have hMbIntegral' : Integrable (fun ζ => ∫ u in Ioc (0 : ℝ) H, Mb ζ u) A.P := by
    simpa [Mb] using hMbIntegral
  exact ⟨Mb, hS102, hMbIntegral'⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_envelope_bound
#print axioms HRS.Fp81.S21.fp81s21_moving_M1

end HRS.Fp81.S21

end
