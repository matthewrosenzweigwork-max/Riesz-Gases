import HRS.MS.Fp81S21MovingDuality
import HRS.MS.R2InterpAux82
import HRS.MS.R2InterpAux84
import HRS.MS.R2InterpAux85
import HRS.MS.R2InterpAux86
import HRS.MS.R2InterpAux7
import HRS.MS.R2MtAux3

/-!
# HRS S2.1(iii), packet 8.4: the moving centered orbit identity

This is the moving-reference counterpart of `R2InterpAux87.s102_orbit_zeta`.
The reference in the drift is `r26t3_mu R r` at the integration time `r`.
The moving actual-density and round-two fields give the timewise pair-energy
bound required by `s102_centered_identity`; the latter is reused unchanged.
The filtered particle version from P00 is used for the Itô integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA
open HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.R2Mt

private def fp81s21_clipMovingTime (H : ℝ) (hH : 0 ≤ H) (u : ℝ) :
    Set.Icc (0 : ℝ) H :=
  ⟨max 0 (min u H), ⟨le_max_left _ _,
    max_le hH (min_le_right _ _)⟩⟩

private theorem fp81s21_clipMovingTime_continuous
    {H : ℝ} (hH : 0 ≤ H) :
    Continuous (fp81s21_clipMovingTime H hH) := by
  exact (continuous_const.max (continuous_id.min continuous_const)).subtype_mk
    (fun u => ⟨le_max_left _ _, max_le hH (min_le_right _ _)⟩)

private def fp81s21_clipMovingDensity
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (H : ℝ)
    (hH : 0 ≤ H) (u : ℝ) : Euc p.d → ℝ :=
  fun x => R.ρ (fp81s21_clipMovingTime H hH u) x

private def fp81s21_clipMovingKernel
    (p : Parameters) (H : ℝ) (hH : 0 ≤ H)
    (hK : ℝ → Euc p.d → Euc p.d → ℝ) :
    ℝ → Euc p.d → Euc p.d → ℝ :=
  fun u => hK (fp81s21_clipMovingTime H hH u)

private theorem fp81s21_moving_clip_pairEnergy_meas
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) {H : ℝ} (hH : 0 < H)
    {N : ℕ} (hK : ℝ → Euc p.d → Euc p.d → ℝ)
    (hKm : Measurable fun q : ℝ × Euc p.d × Euc p.d => hK q.1 q.2.1 q.2.2) :
    Measurable (fun z : ℝ × EucConfig p.d N =>
      pairEnergy (fp81s21_clipMovingKernel p H hH.le hK z.1) z.2
        (HRS.Whole.withDensityReal (fp81s21_clipMovingDensity p R H hH.le z.1))) := by
  classical
  let ρclip := fp81s21_clipMovingDensity p R H hH.le
  let hKclip := fp81s21_clipMovingKernel p H hH.le hK
  have hclipC := fp81s21_clipMovingTime_continuous hH.le
  have hρjoint : Measurable (fun z : Set.Icc (0 : ℝ) H × Euc p.d => R.ρ z.1 z.2) :=
    fp81s21_moving_density_joint_meas p R hδ hδh
  have hclipMap : Continuous fun z : ℝ × Euc p.d =>
      (fp81s21_clipMovingTime H hH.le z.1, z.2) :=
    (hclipC.comp continuous_fst).prodMk continuous_snd
  have hρm : Measurable fun z : ℝ × Euc p.d => ρclip z.1 z.2 := by
    exact hρjoint.comp hclipMap.measurable
  have hρ0 : ∀ u x, 0 ≤ ρclip u x := by
    intro u x
    have hglobal := R.resulting.global H
    exact (hglobal.density (fp81s21_clipMovingTime H hH.le u)
      (fp81s21_clipMovingTime H hH.le u).property).nonneg x
  have hKclipm : Measurable fun z : ℝ × Euc p.d × Euc p.d =>
      hKclip z.1 z.2.1 z.2.2 := by
    exact hKm.comp
      (((continuous_subtype_val.comp hclipC).measurable.comp measurable_fst).prodMk
        measurable_snd)
  change Measurable (fun z : ℝ × EucConfig p.d N =>
      pairEnergy (hKclip z.1) z.2 (HRS.Whole.withDensityReal (ρclip z.1)))
  exact fp81s21_moving_pairEnergy_joint_meas hρm hρ0 hKclipm

private theorem fp81s21_moving_pairEnergy_marginal_bound
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (hK : ℝ → Euc p.d → Euc p.d → ℝ) {B : ℝ}
    (hKb : ∀ r ∈ Icc (0 : ℝ) t, IsBoundedPairKernel p.s B (hK r)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ r ∈ Icc (0 : ℝ) t,
      Integrable (fun Z : EucConfig p.d N =>
        (N : ℝ) * pairEnergy (hK r) Z (r26t3_mu R r))
          (A.P.map (F.X r.toNNReal)) ∧
      ∫ Z, ‖(N : ℝ) * pairEnergy (hK r) Z (r26t3_mu R r)‖
        ∂(A.P.map (F.X r.toNNReal)) ≤ C₀ := by
  classical
  obtain ⟨M, L, hround⟩ := hphys.round2
  obtain ⟨q, K, hq, hactual⟩ := hphys.actual_density
  obtain ⟨C₀, hC₀, hC⟩ := s102_comm_L1 p.hd p.hs0 p.hs M L p.β q K B
    p.hβ hq
  have hmap : ∀ r : ℝ,
      A.P.map (F.X r.toNNReal) = A.P.map (A.X r.toNNReal) := by
    intro r
    exact Measure.map_congr (F.indist.mono fun ω hω => hω r.toNNReal)
  refine ⟨C₀, hC₀, ?_⟩
  intro r hr
  have hrH : r ∈ Icc (0 : ℝ) H := ⟨hr.1, hr.2.trans ht.2⟩
  have hActualF : HasR2ActualDensity p.s p.β q K (r26t3_mu R r)
      (A.P.map (F.X r.toNNReal)) := by
    rw [hmap r]
    exact hactual r hrH
  obtain ⟨⟨hPair, hPairBound⟩, _⟩ := hC (R.ρ r) (hround r hrH) N hN
    (A.P.map (F.X r.toNNReal)) hActualF (hK r) (hKb r hr)
  exact ⟨hPair, hPairBound⟩

/-- Time × probability integrability of the moving pair energy. This is the
point where the moving actual-law density is used; no fixed thermal law is
substituted for the law of the particles. -/
private theorem fp81s21_moving_pairEnergy_prodInt
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (hK : ℝ → Euc p.d → Euc p.d → ℝ)
    (hKm : Measurable fun q : ℝ × Euc p.d × Euc p.d => hK q.1 q.2.1 q.2.2)
    {B : ℝ}
    (hKb : ∀ r ∈ Icc (0 : ℝ) t, IsBoundedPairKernel p.s B (hK r)) :
    Integrable
      (fun q : ℝ × A.Ω => pairEnergy (hK q.1) (F.X q.1.toNNReal q.2)
        (r26t3_mu R q.1))
      ((volume.restrict (Icc (0 : ℝ) t)).prod A.P) := by
  classical
  obtain ⟨C₀, hC₀, hMarg⟩ := fp81s21_moving_pairEnergy_marginal_bound
    p R hN A F hphys ht hK hKb
  have hclipC := fp81s21_clipMovingTime_continuous hH.le
  let ρclip := fp81s21_clipMovingDensity p R H hH.le
  let hKclip := fp81s21_clipMovingKernel p H hH.le hK
  have hEm : Measurable fun z : ℝ × EucConfig p.d N =>
      pairEnergy (hKclip z.1) z.2 (HRS.Whole.withDensityReal (ρclip z.1)) :=
    fp81s21_moving_clip_pairEnergy_meas p R hδ hδh hH hK hKm
  let Y : ℝ → A.Ω → EucConfig p.d N := fun r => F.X (min r t).toNNReal
  have hYm : Measurable fun z : ℝ × A.Ω => Y z.1 z.2 :=
    measurable_progressive_min_gen (u := ofNNRealTime F.X) F.filtered.progressive t
  let g : ℝ → EucConfig p.d N → ℝ := fun r Z =>
    (N : ℝ) * pairEnergy (hKclip r) Z (HRS.Whole.withDensityReal (ρclip r))
  have hgm : Measurable fun z : ℝ × EucConfig p.d N => g z.1 z.2 :=
    measurable_const.mul hEm
  have htime : ∀ r ∈ Icc (0 : ℝ) t,
      Measurable (Y r) ∧ Integrable (g r) (A.P.map (Y r)) ∧
        ∫ Z, ‖g r Z‖ ∂(A.P.map (Y r)) ≤ C₀ := by
    intro r hr
    have hrH : r ∈ Icc (0 : ℝ) H := ⟨hr.1, hr.2.trans ht.2⟩
    have hclipr : (fp81s21_clipMovingTime H hH.le r : ℝ) = r := by
      change max 0 (min r H) = r
      rw [min_eq_left (hr.2.trans ht.2), max_eq_right hr.1]
    have hclipEq : fp81s21_clipMovingTime H hH.le r = ⟨r, hrH⟩ :=
      Subtype.ext hclipr
    have hKclipr : hKclip r = hK r := by
      dsimp [hKclip, fp81s21_clipMovingKernel]
      rw [hclipEq]
    have hρclipr : ρclip r = R.ρ r := by
      funext x
      dsimp [ρclip, fp81s21_clipMovingDensity]
      rw [hclipEq]
    have hYr : Y r = F.X r.toNNReal := by
      funext ω
      simp [Y, min_eq_left hr.2]
    have hYmeas : Measurable (Y r) :=
      hYm.comp (measurable_const.prodMk measurable_id)
    refine ⟨hYmeas, ?_⟩
    rw [hYr]
    change Integrable (fun Z => (N : ℝ) * pairEnergy (hKclip r) Z
      (HRS.Whole.withDensityReal (ρclip r))) (A.P.map (F.X r.toNNReal)) ∧ _
    simpa [g, hKclipr, hρclipr, r26t3_mu] using hMarg r hr
  have hprodN := s102_prodInt_family (P := A.P) (T := t) (C := C₀)
    (Y := Y) hYm g hgm htime
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hprodEq : (fun z : ℝ × A.Ω => g z.1 (Y z.1 z.2)) =ᵐ[
      (volume.restrict (Icc (0 : ℝ) t)).prod A.P]
      (fun z => (N : ℝ) * pairEnergy (hK z.1)
        (F.X z.1.toNNReal z.2) (r26t3_mu R z.1)) := by
    filter_upwards [s102_ae_mem_prod (P := A.P) t] with z hz
    have hc : (fp81s21_clipMovingTime H hH.le z.1 : ℝ) = z.1 := by
      change max 0 (min z.1 H) = z.1
      rw [min_eq_left (hz.2.trans ht.2), max_eq_right hz.1]
    have hzH : z.1 ∈ Icc (0 : ℝ) H := ⟨hz.1, hz.2.trans ht.2⟩
    have hclipEq : fp81s21_clipMovingTime H hH.le z.1 = ⟨z.1, hzH⟩ :=
      Subtype.ext hc
    have hKclipz : hKclip z.1 = hK z.1 := by
      dsimp [hKclip, fp81s21_clipMovingKernel]
      rw [hclipEq]
    have hρclipz : ρclip z.1 = R.ρ z.1 := by
      funext x
      dsimp [ρclip, fp81s21_clipMovingDensity]
      rw [hclipEq]
    simp [g, hKclipz, hρclipz, Y, min_eq_left hz.2, r26t3_mu, hNne]
  have hprodN' := hprodN.congr hprodEq
  refine (hprodN'.const_mul ((N : ℝ)⁻¹)).congr ?_
  filter_upwards with z
  field_simp [hNne]

/-- Moving centered orbit identity. It preserves the stationary coefficient and
drift sign, with the moving law evaluated at each drift time. `F` is the P00
filtered version of `A`; its path agrees with `A.X` for all times on one
probability-one event. -/
theorem fp81s21_moving_orbit_zeta
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (α : MultiIndex p.d) :
    ∀ᵐ ζ ∂A.P, ∀ τ ∈ Icc (0 : ℝ) t,
      s102_zf A.P F.X ζ τ
          (propagatorW (r26t3_coeff R) τ t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) =
        s102_zf A.P F.X ζ 0
          (propagatorW (r26t3_coeff R) 0 t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) +
        (Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)) *
          itoIntegral A.P F.ℱ F.Wc
            (s102_Ig (fun r => propagatorW (r26t3_coeff R) r t
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) t F.X) τ ζ +
        ∫ r in Icc (0 : ℝ) τ,
          (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
            A.P F.X r ζ
            (propagatorW (r26t3_coeff R) r t
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) := by
  classical
  let D : WholeDyn p.d := quadraticGradientDyn p.d p.s p.a p.β
  let C : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let f : ℝ → Euc p.d → ℝ := fun r => propagatorW C r t φ
  have hN0 : 0 < N := by omega
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
  have htH : t ≤ H := ht.2
  have hglobal := R.resulting.global H
  have hrounds := hphys.round2
  obtain ⟨M, L, hround⟩ := hrounds
  obtain ⟨q, K, hq, hactual⟩ := hphys.actual_density
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hsqrt : Real.sqrt (2 * p.β⁻¹) =
      Real.sqrt 2 * (Real.sqrt p.β)⁻¹ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_inv]
  have hAdj : ∃ f₀, IsClassicalAdjointW C t φ f₀ := by
    obtain ⟨ψ, hψ⟩ := HRS.MS.R2Interp.s102_osc_schwartz
      (wholeSpaceIndex p.d : ℝ) α
    have hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) := by
      constructor
      · rw [← hψ]
        exact ψ.smooth ⊤
      · rw [← hψ]
        exact memOsc_schwartz ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ
    exact fp81s21_adjoint_of_osc_test p R hφ ht.1
  have hf : IsClassicalAdjointW C t φ f := s102_propagator_classical hAdj
  have hdual := fp81s21_moving_duality p R hH A F hphys.regular ht α
  set V : ℝ → Euc p.d → Euc p.d := fun r x =>
    if r ∈ Icc (0 : ℝ) t then gradient (f r) x else 0 with hV
  have hVm : Measurable fun z : ℝ × Euc p.d => V z.1 z.2 :=
    s102_gradJoint_meas hf
  let hK : ℝ → Euc p.d → Euc p.d → ℝ := fun r => commutatorKernel p.d p.s (V r)
  have hKm : Measurable fun z : ℝ × Euc p.d × Euc p.d =>
      hK z.1 z.2.1 z.2.2 := s102_kernelFam_meas p.s V hVm
  have hKr : ∀ r ∈ Icc (0 : ℝ) t,
      hK r = commutatorKernel p.d p.s (fun x => gradient (f r) x) := by
    intro r hr
    change commutatorKernel p.d p.s (V r) = _
    rw [hV]
    simp only [if_pos hr]
  obtain ⟨B, hB⟩ := s102_orbit_kernel_bdd p.hs0 hf
  have hKb : ∀ r ∈ Icc (0 : ℝ) t, IsBoundedPairKernel p.s B (hK r) := by
    intro r hr
    rw [hKr r hr]
    exact hB r hr
  have hprod := fp81s21_moving_pairEnergy_prodInt p R hδ hδh hH hN A F hphys ht
    hK hKm hKb
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ, ∀ r ∈ Icc (0 : ℝ) t, ∀ x,
      |f r x| ≤ Bf := by
    obtain ⟨Bf, hBf⟩ := hf.bdd 0 (Nat.zero_le _)
    refine ⟨Bf, fun r hr x => ?_⟩
    have h := hBf r hr x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hfm : ∀ r ∈ Icc (0 : ℝ) t, Measurable (f r) := fun r hr =>
    (hf.c2 r hr).continuous.measurable
  have hXτm : ∀ τ : ℝ, Measurable (F.X τ.toNNReal) := fun τ =>
    (F.strong H).adapted _
  let aR : ℝ → A.Ω → ℝ := fun τ ζ =>
    HRS.Whole.pair (HRS.Whole.empirical (F.X τ.toNNReal ζ)) (f τ) -
      HRS.Whole.pair (r26t3_mu R τ) (f τ)
  let I : ℝ → A.Ω → ℝ := itoIntegral A.P F.ℱ F.Wc
    (s102_Ig f t F.X)
  have ha_int : ∀ τ ∈ Icc (0 : ℝ) t, Integrable (aR τ) A.P := by
    intro τ hτ
    exact (s102_pairEmp_int hN0 (hXτm τ) (hfm τ hτ) (hBf τ hτ)).sub
      (integrable_const _)
  obtain ⟨Bg, hBg⟩ := s102_Ig_bdd hf F.X
  have hΦ : IsProgressiveL2 A.P F.ℱ (s102_Ig f t F.X) :=
    IsProgressiveL2.of_bounded A.P
      (s102_Ig_progressive hf F.filtered.progressive) Bg hBg
  have hI_int : ∀ τ ∈ Icc (0 : ℝ) t, Integrable (I τ) A.P := by
    intro τ _
    exact (memLp_two_itoIntegral F.filtered.brownian hΦ τ).integrable
      (by norm_num)
  have hI0 : ∀ τ ∈ Icc (0 : ℝ) t, ∫ ζ, I τ ζ ∂A.P = 0 := by
    intro τ _
    exact integral_itoIntegral F.filtered.brownian hΦ τ
  have hFe : ∀ᵐ ζ ∂A.P, ∀ r ∈ Icc (0 : ℝ) t,
      flucInteractionRd D (f r) (F.X r.toNNReal ζ) (R.ρ r) =
        -pairEnergy (hK r) (F.X r.toNNReal ζ) (r26t3_mu R r) := by
    filter_upwards [(F.strong H).no_collision] with ζ hno r hr
    have hkernel : ∀ x : Euc p.d,
        Integrable (commutatorKernel p.d D.s
          (fun z => gradient (f r) z) x) (r26t3_mu R r) := by
      intro x
      have hd1 : 1 ≤ p.d := Nat.le_trans (by norm_num) p.hd
      have hk := (HRS.MS.R2Mt.s92_kernel_integrable hd1 p.hs0 hsd M
        (hround r ⟨hr.1, hr.2.trans htH⟩).prob
        (hround r ⟨hr.1, hr.2.trans htH⟩).bdd (hKb r hr)).1 x
      rw [hKr r hr] at hk
      exact hk
    have hno' : F.X r.toNNReal ζ ∉ eucCollisionSet p.d N :=
      hno r.toNNReal (by
        rw [Real.coe_toNNReal _ hr.1]
        exact hr.2.trans htH)
    have hfl := s102_flucInteractionRd_eq D rfl hN0 (f r)
      (F.X r.toNNReal ζ) hno' (R.ρ r) hkernel
    rw [hfl, hKr r hr]
    rfl
  have hid : ∀ᵐ ζ ∂A.P, ∀ τ ∈ Icc (0 : ℝ) t,
      aR τ ζ = aR 0 ζ + (Real.sqrt (2 * p.β⁻¹) / N) * I τ ζ -
        ∫ r in Icc (0 : ℝ) τ,
          pairEnergy (hK r) (F.X r.toNNReal ζ) (r26t3_mu R r) := by
    filter_upwards [hdual, hFe] with ζ h1 h2 τ hτ
    obtain ⟨-, h3⟩ := h1 τ hτ
    have hsubτ : Icc (0 : ℝ) τ ⊆ Icc 0 t := Icc_subset_Icc le_rfl hτ.2
    have h4 : ∫ r in Icc (0 : ℝ) τ,
        flucInteractionRd D (f r) (F.X r.toNNReal ζ) (R.ρ r) =
          -∫ r in Icc (0 : ℝ) τ,
            pairEnergy (hK r) (F.X r.toNNReal ζ) (r26t3_mu R r) := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Icc fun r hr => h2 r
        (hsubτ hr)
    have h0 : aR 0 ζ =
        HRS.Whole.pair (HRS.Whole.empirical (F.X 0 ζ)) (f 0) -
          HRS.Whole.pair (r26t3_mu R 0) (f 0) := by
      simp [aR, Real.toNNReal_zero]
    have h3' : aR τ ζ =
        (HRS.Whole.pair (HRS.Whole.empirical (F.X 0 ζ)) (f 0) -
          HRS.Whole.pair (r26t3_mu R 0) (f 0)) +
          (Real.sqrt (2 * p.β⁻¹) / N) * I τ ζ +
          ∫ r in Icc (0 : ℝ) τ,
            flucInteractionRd D (f r) (F.X r.toNNReal ζ) (R.ρ r) := by
      let IgRaw : ℝ → A.Ω → (Fin N × Fin p.d) → ℝ := fun r ζ' ia =>
        if 0 ≤ r ∧ r ≤ t then
          gradComp ia.2 (f r) (F.X r.toNNReal ζ' ia.1) else 0
      have hIgRaw : IgRaw = s102_Ig f t F.X := by
        funext r ζ' ia
        simp [IgRaw, s102_Ig, Set.mem_Icc, gradComp]
      have hItoRaw : itoIntegral A.P F.ℱ F.Wc IgRaw τ ζ = I τ ζ := by
        rw [hIgRaw]
      have hraw : aR τ ζ =
          (HRS.Whole.pair (HRS.Whole.empirical (F.X 0 ζ)) (f 0) -
            HRS.Whole.pair (r26t3_mu R 0) (f 0)) +
            (Real.sqrt (2 * p.β⁻¹) / N) *
              itoIntegral A.P F.ℱ F.Wc IgRaw τ ζ +
            ∫ r in Icc (0 : ℝ) τ,
              flucInteractionRd D (f r) (F.X r.toNNReal ζ) (R.ρ r) := by
        simpa [aR, D, C, f, φ, r26t3_mu, r26t3_coeff,
          quadraticGradientDyn, IgRaw, hsqrt] using h3
      rw [hItoRaw] at hraw
      exact hraw
    rw [h3', h0, h4]
    ring
  have he := hprod
  have hcent := s102_centered_identity (c := Real.sqrt (2 * p.β⁻¹) / N)
    aR I (fun z => pairEnergy (hK z.1) (F.X z.1.toNNReal z.2)
      (r26t3_mu R z.1)) he ha_int hI_int hI0 ht0 hid
  have hsq : (Real.sqrt N)⁻¹ * (N : ℝ) = Real.sqrt N := by
    have h0 : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN0)
    have h1 : (N : ℝ) = Real.sqrt N * Real.sqrt N :=
      (Real.mul_self_sqrt (by positivity)).symm
    rw [inv_mul_eq_iff_eq_mul₀ h0.ne']
    exact h1
  have hquad : ∀ r ζ,
      r2QuadField p.s (r26t3_mu R r) A.P F.X r ζ (f r) =
        (N : ℝ) * (pairEnergy (commutatorKernel p.d p.s
          (fun x => gradient (f r) x)) (F.X r.toNNReal ζ) (r26t3_mu R r) -
          ∫ ζ', pairEnergy (commutatorKernel p.d p.s
            (fun x => gradient (f r) x)) (F.X r.toNNReal ζ')
              (r26t3_mu R r) ∂A.P) := by
    intro r ζ
    rfl
  have hquadInt : ∀ᵐ ζ ∂A.P, ∀ τ ∈ Icc (0 : ℝ) t,
      ∫ r in Icc (0 : ℝ) τ,
        (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
          A.P F.X r ζ (f r)) =
      -Real.sqrt N * ∫ r in Icc (0 : ℝ) τ,
        (pairEnergy (hK r) (F.X r.toNNReal ζ) (r26t3_mu R r) -
          ∫ ζ', pairEnergy (hK r) (F.X r.toNNReal ζ')
            (r26t3_mu R r) ∂A.P) := by
    filter_upwards with ζ τ hτ
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [hquad, hKr r (Icc_subset_Icc le_rfl hτ.2 hr)]
    rw [← mul_assoc, neg_mul, hsq]
  filter_upwards [hcent, hquadInt] with ζ hζ hQI
  intro τ hτ
  have hsubτ : Icc (0 : ℝ) τ ⊆ Icc 0 t := Icc_subset_Icc le_rfl hτ.2
  have hmuτ : IsProbabilityMeasure (r26t3_mu R τ) :=
    HRS.MS.R2Mt.s92_isProb_mu (hround τ ⟨hτ.1, hτ.2.trans htH⟩).prob
  letI := hmuτ
  have hzτ := s102_zf_eq hN0 A.P F.X τ (hXτm τ)
    (r26t3_mu R τ) (hfm τ hτ) (hBf τ hτ)
  have hmu0 : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.MS.R2Mt.s92_isProb_mu (hround 0 ⟨le_rfl, hH.le⟩).prob
  letI := hmu0
  have hz0 := s102_zf_eq hN0 A.P F.X 0 (hXτm 0)
    (r26t3_mu R 0) (hfm 0 ht0) (hBf 0 ht0)
  rw [hzτ ζ, hz0 ζ]
  rw [hQI τ hτ]
  rw [hζ τ hτ]
  ring

#print axioms HRS.Fp81.S21.fp81s21_moving_pairEnergy_prodInt
#print axioms HRS.Fp81.S21.fp81s21_moving_orbit_zeta

end HRS.Fp81.S21

end
