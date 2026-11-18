import HRS.MS.Fp81S21MartBdg
import HRS.MS.CritWholeW2Shift
import HRS.Uniform.Q48eAux1

/-!
# HRS S2.1(iii), B7: shifted Hilbert martingale adapter

A Hilbert martingale with covariation on every real horizon remains such a
martingale after translating time by a nonnegative amount and freezing its
negative-time part.  The filtration is the shifted filtration used by the
particle Brownian motion.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

private theorem fp81s21_b7_shiftedCore
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {M : ℝ → Ω → V} {Sg : ℝ → Ω → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {b H : ℝ} (hb : 0 ≤ b) (hH : 0 < H) :
    (∀ x : V, Martingale
      (fun r ω => inner ℝ (M (b + max r 0) ω - M b ω) x)
      (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ b.toNNReal) P) ∧
    (∀ᵐ ω ∂P, M (b + max 0 0) ω - M b ω = 0) ∧
    (∀ᵐ ω ∂P, ContinuousOn
      (fun r => M (b + max r 0) ω - M b ω) (Set.Icc (0 : ℝ) H)) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) H,
      MemLp (fun ω => M (b + max r 0) ω - M b ω) 2 P) := by
  let ℱb := HRS.Whole.BreakdownS81.s81b_shiftFil ℱ b.toNNReal
  let ψ : ℝ → ℝ := fun r => b + max r 0
  have hbcoe : (b.toNNReal : ℝ) = b := Real.coe_toNNReal b hb
  have hfil : ∀ r, ℱb r = ℱ (ψ r) := by
    intro r
    simp [ℱb, ψ, HRS.Whole.BreakdownS81.s81b_shiftFil, hbcoe]
  have hψmono : Monotone ψ := by
    intro s t hst
    dsimp [ψ]
    simpa [add_comm] using add_le_add_left (max_le_max_right 0 hst) b
  have hψb (r : ℝ) : b ≤ ψ r := by
    dsimp [ψ]
    linarith [le_max_right r 0]
  have hψrange (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) H) :
      ψ r ∈ Set.Icc (0 : ℝ) (b + H) := by
    constructor
    · dsimp [ψ]
      exact add_nonneg hb (le_max_right r 0)
    · dsimp [ψ]
      simpa [add_comm] using add_le_add_left (max_le hr.2 hH.le) b
  let hsrc := hHM (b + H)
  have hsrcB : b ∈ Set.Icc (0 : ℝ) (b + H) := by
    constructor <;> linarith
  have hcoordComp : ∀ x : V,
      Martingale (fun r ω => inner ℝ (M (ψ r) ω) x) ℱb P := by
    intro x
    refine ⟨?_, ?_⟩
    · intro r
      rw [hfil r]
      exact (hsrc.martingale x).stronglyAdapted (ψ r)
    · intro s t hst
      rw [hfil s]
      exact (hsrc.martingale x).condExp_ae_eq (hψmono hst)
  have hcoordConst : ∀ x : V,
      Martingale (fun _ ω => inner ℝ (M b ω) x) ℱb P := by
    intro x
    refine ⟨?_, ?_⟩
    · intro r
      rw [hfil r]
      exact ((hsrc.martingale x).stronglyAdapted b).mono (ℱ.mono (hψb r))
    · intro s t _
      rw [hfil s]
      rw [condExp_of_stronglyMeasurable (ℱ.le (ψ s))
        (((hsrc.martingale x).stronglyAdapted b).mono (ℱ.mono (hψb s)))
        ((hsrc.martingale x).integrable b)]
  have hcoord : ∀ x : V, Martingale
      (fun r ω => inner ℝ (M (ψ r) ω - M b ω) x) ℱb P := by
    intro x
    have hsub := (hcoordComp x).sub (hcoordConst x)
    have heq : (fun r ω => inner ℝ (M (ψ r) ω - M b ω) x) =
        (fun r ω => inner ℝ (M (ψ r) ω) x) - fun _ ω => inner ℝ (M b ω) x := by
      funext r ω
      simp [inner_sub_left]
    rw [heq]
    exact hsub
  have hzero : ∀ᵐ ω ∂P, M (b + max 0 0) ω - M b ω = 0 :=
    Filter.Eventually.of_forall fun ω => by simp
  have hcont : ∀ᵐ ω ∂P, ContinuousOn
      (fun r => M (ψ r) ω - M b ω) (Set.Icc (0 : ℝ) H) := by
    filter_upwards [hsrc.cont] with ω hω
    have hψcont : ContinuousOn ψ (Set.Icc (0 : ℝ) H) := by fun_prop
    have hψmem : ∀ r ∈ Set.Icc (0 : ℝ) H, ψ r ∈ Set.Icc (0 : ℝ) (b + H) :=
      fun r hr => hψrange r hr
    exact (hω.comp hψcont hψmem).sub continuousOn_const
  have hsq : ∀ r ∈ Set.Icc (0 : ℝ) H, MemLp
      (fun ω => M (ψ r) ω - M b ω) 2 P := by
    intro r hr
    have h1 := hsrc.sq_int (ψ r) (hψrange r hr)
    have h2 := hsrc.sq_int b hsrcB
    have heq : (fun ω => M (ψ r) ω - M b ω) =
        (fun ω => M (ψ r) ω) - M b := by
      funext ω
      rfl
    rw [heq]
    exact h1.sub h2
  refine ⟨?_, hzero, ?_, hsq⟩
  · intro x
    simpa [ℱb, ψ] using hcoord x
  · simpa [ψ] using hcont

private theorem fp81s21_b7_shiftedSigmaCore
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {M : ℝ → Ω → V} {Sg : ℝ → Ω → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {b H : ℝ} (hb : 0 ≤ b) (hH : 0 < H) :
    (∀ x y : V, Measurable (Function.uncurry fun r ω => Sg (b + max r 0) ω x y)) ∧
    (∀ r, ∀ x y : V,
      Measurable[HRS.Whole.BreakdownS81.s81b_shiftFil ℱ b.toNNReal r]
        (fun ω => Sg (b + max r 0) ω x y)) ∧
    (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) H,
      IsTraceClassCov (Sg (b + max r 0) ω)) := by
  let ℱb := HRS.Whole.BreakdownS81.s81b_shiftFil ℱ b.toNNReal
  let ψ : ℝ → ℝ := fun r => b + max r 0
  let hsrc := hHM (b + H)
  have hψrange (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) H) :
      ψ r ∈ Set.Icc (0 : ℝ) (b + H) := by
    constructor
    · dsimp [ψ]
      exact add_nonneg hb (le_max_right r 0)
    · dsimp [ψ]
      simpa [add_comm] using add_le_add_left (max_le hr.2 hH.le) b
  have hbcoe : (b.toNNReal : ℝ) = b := Real.coe_toNNReal b hb
  have hfil : ∀ r, ℱb r = ℱ (ψ r) := by
    intro r
    simp [ℱb, ψ, HRS.Whole.BreakdownS81.s81b_shiftFil, hbcoe]
  have hSshiftmeas : ∀ x y : V,
      Measurable (Function.uncurry fun r ω => Sg (ψ r) ω x y) := by
    intro x y
    have hmap : Measurable (fun p : ℝ × Ω => (ψ p.1, p.2)) := by
      exact (measurable_const.add (measurable_fst.max measurable_const)).prodMk measurable_snd
    exact (hsrc.sigma_meas x y).comp hmap
  have hSadapt : ∀ r, ∀ x y : V, Measurable[ℱb r] (fun ω => Sg (ψ r) ω x y) := by
    intro r x y
    rw [hfil r]
    exact hsrc.sigma_adapted (ψ r) x y
  have hSclass : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) H, IsTraceClassCov (Sg (ψ r) ω) := by
    filter_upwards [hsrc.sigma_traceClass] with ω hω r hr
    exact hω (ψ r) (hψrange r hr)
  refine ⟨?_, ?_, hSclass⟩
  · intro x y
    simpa only [ψ] using hSshiftmeas x y
  · intro r x y
    simpa [ℱb, ψ] using hSadapt r x y

private theorem fp81s21_b7_shiftedTraceIntegralIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {M : ℝ → Ω → V} {Sg : ℝ → Ω → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hComplete : IsCompleteFiltration P ℱ)
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {b H : ℝ} (hb : 0 ≤ b) (hH : 0 < H) :
    Integrable (fun ω => ∫ r in Set.Icc (0 : ℝ) H,
      traceNormForm (Sg (b + max r 0) ω)) P := by
  let hsrc := hHM (b + H)
  have hwin := HRS.Uniform.Q48e.isHMC_window hComplete hb hH.le hsrc
  have heq : ∀ ω, ∫ r in Set.Icc (0 : ℝ) H,
      traceNormForm (if r ≤ H then Sg (b + r) ω else 0) =
      ∫ r in Set.Icc (0 : ℝ) H, traceNormForm (Sg (b + max r 0) ω) := by
    intro ω
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp [max_eq_left hr.1, if_pos hr.2]
  exact hwin.sigma_int.congr (Filter.Eventually.of_forall heq)

private theorem fp81s21_b7_shiftedTracePathIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {M : ℝ → Ω → V} {Sg : ℝ → Ω → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {b H : ℝ} (hb : 0 ≤ b) (hH : 0 < H) :
    ∀ᵐ ω ∂P, IntegrableOn
      (fun r => traceNormForm (Sg (b + max r 0) ω)) (Set.Icc (0 : ℝ) H) := by
  let hsrc := hHM (b + H)
  filter_upwards [hsrc.sigma_pathint] with ω hω
  have hlocal : IntegrableOn
      (fun r => traceNormForm (Sg (b + r) ω)) (Set.Icc (0 : ℝ) H) :=
    (HRS.Uniform.Q48e.integrableOn_Icc_shift
      (fun r => traceNormForm (Sg r ω)) b H).2
      (hω.mono_set (Set.Icc_subset_Icc_left hb))
  have heq : (fun r => traceNormForm (Sg (b + max r 0) ω)) =ᵐ[volume.restrict (Set.Icc 0 H)]
      fun r => traceNormForm (Sg (b + r) ω) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp [max_eq_left hr.1]
  exact hlocal.congr heq.symm

private theorem fp81s21_b7_shiftedEntryPathIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {M : ℝ → Ω → V} {Sg : ℝ → Ω → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {b H : ℝ} (hb : 0 ≤ b) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ x y : V, IntegrableOn
      (fun r => Sg (b + max r 0) ω x y) (Set.Icc (0 : ℝ) H) := by
  let hsrc := hHM (b + H)
  filter_upwards [hsrc.sigma_entry_int] with ω hω x y
  have hlocal : IntegrableOn
      (fun r => Sg (b + r) ω x y) (Set.Icc (0 : ℝ) H) :=
    (HRS.Uniform.Q48e.integrableOn_Icc_shift
      (fun r => Sg r ω x y) b H).2
      ((hω x y).mono_set (Set.Icc_subset_Icc_left hb))
  have heq : (fun r => Sg (b + max r 0) ω x y) =ᵐ[volume.restrict (Set.Icc 0 H)]
      fun r => Sg (b + r) ω x y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp [max_eq_left hr.1]
  exact hlocal.congr heq.symm

private theorem fp81s21_b7_shiftedCovariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {M : ℝ → Ω → V} {Sg : ℝ → Ω → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hComplete : IsCompleteFiltration P ℱ)
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {b : ℝ} (hb : 0 ≤ b) :
    ∀ x y : V, Martingale
      (fun r ω => inner ℝ (M (b + max r 0) ω - M b ω) x *
        inner ℝ (M (b + max r 0) ω - M b ω) y -
          ∫ s in Set.Icc (0 : ℝ) r, Sg (b + max s 0) ω x y)
      (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ b.toNNReal) P := by
  intro x y
  let ℱb := HRS.Whole.BreakdownS81.s81b_shiftFil ℱ b.toNNReal
  let ψ : ℝ → ℝ := fun r => b + max r 0
  let U : ℝ → Ω → ℝ := fun t ω => inner ℝ (M t ω) x
  let V' : ℝ → Ω → ℝ := fun t ω => inner ℝ (M t ω) y
  let Λ : ℝ → Ω → ℝ := fun t ω => ∫ s in Set.Icc (0 : ℝ) t, Sg s ω x y
  let Δ : ℝ → Ω → ℝ := fun t ω =>
    (U t ω - U (min b t) ω) * (V' t ω - V' (min b t) ω) -
      (Λ t ω - Λ (min b t) ω)
  have hbcoe : (b.toNNReal : ℝ) = b := Real.coe_toNNReal b hb
  have hfil : ∀ r, ℱb r = ℱ (ψ r) := by
    intro r
    simp [ℱb, ψ, HRS.Whole.BreakdownS81.s81b_shiftFil, hbcoe]
  have hψmono : Monotone ψ := by
    intro s t hst
    dsimp [ψ]
    simpa [add_comm] using add_le_add_left (max_le_max_right 0 hst) b
  let hsrc := hHM (b + 1)
  have hU2 : ∀ t, MemLp (U t) 2 P := by
    intro t
    have htT : t ≤ max (b + 1) (max t 0) := by
      exact (le_max_left t 0).trans (le_max_right (b + 1) (max t 0))
    exact HRS.Uniform.Q48e.memLp_inner_win
      (hHM (max (b + 1) (max t 0))) x htT
  have hV2 : ∀ t, MemLp (V' t) 2 P := by
    intro t
    have htT : t ≤ max (b + 1) (max t 0) := by
      exact (le_max_left t 0).trans (le_max_right (b + 1) (max t 0))
    exact HRS.Uniform.Q48e.memLp_inner_win
      (hHM (max (b + 1) (max t 0))) y htT
  have hfour : Martingale Δ ℱ P := by
    exact HRS.Uniform.Q48e.four_piece (U := U) (V := V') (Λ := Λ)
      (hsrc.martingale x) (hsrc.martingale y) hU2 hV2 (hsrc.covariation x y) b
  have hcomp : Martingale (fun r ω => Δ (ψ r) ω) ℱb P := by
    refine ⟨?_, ?_⟩
    · intro r
      rw [hfil r]
      exact hfour.stronglyAdapted (ψ r)
    · intro s t hst
      rw [hfil s]
      exact hfour.condExp_ae_eq (hψmono hst)
  have hℱbComplete : IsCompleteFiltration P ℱb := by
    intro r s hs hzero
    rw [hfil r]
    exact hComplete (ψ r) s hs hzero
  have hMmeas : ∀ r, Measurable (M r) := by
    obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := V)
    letI := hι
    intro r
    exact measurable_of_inner_basis e (fun i => by
      simpa only [real_inner_comm] using
        ((hsrc.martingale (e i)).stronglyAdapted r).measurable.mono
          (ℱ.le r) le_rfl)
  have hSmeas : Measurable (Function.uncurry fun r ω => Sg (ψ r) ω x y) := by
    have hmap : Measurable (fun p : ℝ × Ω => (ψ p.1, p.2)) := by
      change Measurable (fun p : ℝ × Ω => (b + max p.1 0, p.2))
      exact (measurable_const.add (measurable_fst.max measurable_const)).prodMk measurable_snd
    change Measurable
      ((Function.uncurry fun r ω => Sg r ω x y) ∘ fun p : ℝ × Ω => (ψ p.1, p.2))
    exact (hsrc.sigma_meas x y).comp hmap
  have htargetMeas : ∀ r, Measurable (fun ω =>
      inner ℝ (M (ψ r) ω - M b ω) x * inner ℝ (M (ψ r) ω - M b ω) y -
        ∫ s in Set.Icc (0 : ℝ) r, Sg (ψ s) ω x y) := by
    intro r
    have hMψ : Measurable (fun ω => M (ψ r) ω - M b ω) :=
      (hMmeas (ψ r)).sub (hMmeas b)
    have hI := HRS.MRep.measurable_setIntegral_Icc
      (g := fun s ω => Sg (ψ s) ω x y) hSmeas r
    exact ((hMψ.inner measurable_const).mul (hMψ.inner measurable_const)).sub hI
  have hae : ∀ r, (fun ω => Δ (ψ r) ω) =ᵐ[P]
      fun ω => inner ℝ (M (ψ r) ω - M b ω) x *
        inner ℝ (M (ψ r) ω - M b ω) y -
          ∫ s in Set.Icc (0 : ℝ) r, Sg (ψ s) ω x y := by
    intro r
    by_cases hr : 0 ≤ r
    · let hneed := hHM (b + max r 0)
      have htime : ψ r = b + r := by simp [ψ, max_eq_left hr]
      filter_upwards [hneed.sigma_entry_int] with ω hω
      have hω' : ∀ x y : V,
          IntegrableOn (fun s => Sg s ω x y) (Set.Icc (0 : ℝ) (b + r)) := by
        simpa [max_eq_left hr] using hω
      have hintegral := HRS.Uniform.Q48e.integral_Icc_shift_sub
        (fun s => Sg s ω x y) hb hr (hω' x y)
      have htarget :
          ∫ s in Set.Icc (0 : ℝ) r, Sg (ψ s) ω x y =
            (∫ s in Set.Icc (0 : ℝ) (b + r), Sg s ω x y) -
              (∫ s in Set.Icc (0 : ℝ) b, Sg s ω x y) := by
        have heq : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) r →
            Sg (ψ s) ω x y = Sg (b + s) ω x y := by
          exact Filter.Eventually.of_forall fun s hs => by simp [ψ, max_eq_left hs.1]
        rw [setIntegral_congr_ae measurableSet_Icc heq]
        simpa only using hintegral
      rw [htime, htarget]
      simp only [Δ, Λ, U, V', min_eq_left (show b ≤ b + r by linarith)]
      rw [inner_sub_left, inner_sub_left]
    · have hr' : r < 0 := lt_of_not_ge hr
      have hψ : ψ r = b := by simp [ψ, max_eq_right (le_of_lt hr')]
      have hempty : Set.Icc (0 : ℝ) r = ∅ := Set.Icc_eq_empty (not_le_of_gt hr')
      rw [hψ]
      simp [Δ, Λ, U, V', ψ, hempty]
  exact HRS.MRep.martingale_congr_complete hℱbComplete hcomp htargetMeas hae

/-- Translate an all-horizon Hilbert martingale to the shifted filtration
`r ↦ ℱ (b + max r 0)`.  The process and covariance density are exactly
`M (b + max r 0) - M b` and `Sg (b + max r 0)`. -/
theorem fp81s21_b7_shiftedHilbertMartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {M : ℝ → Ω → V} {Sg : ℝ → Ω → (V →L[ℝ] V →L[ℝ] ℝ)}
    (hComplete : IsCompleteFiltration P ℱ)
    (hHM : ∀ T : ℝ, IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {b H : ℝ} (hb : 0 ≤ b) (hH : 0 < H) :
    IsHilbertMartingaleWithCovariation P
      (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ b.toNNReal) H
      (fun r ω => M (b + max r 0) ω - M b ω)
      (fun r ω => Sg (b + max r 0) ω) := by
  obtain ⟨hcoord, hzero, hcont, hsq⟩ :=
    fp81s21_b7_shiftedCore hHM hb hH
  obtain ⟨hSmeas, hSadapt, hSclass⟩ :=
    fp81s21_b7_shiftedSigmaCore hHM hb hH
  have htraceInt := fp81s21_b7_shiftedTraceIntegralIntegrable hComplete hHM hb hH
  have hpathint := fp81s21_b7_shiftedTracePathIntegrable hHM hb hH
  have hentryint := fp81s21_b7_shiftedEntryPathIntegrable hHM hb hH
  have hcov := fp81s21_b7_shiftedCovariance hComplete hHM hb
  exact ⟨hcoord, hzero, hcont, hsq, hSmeas, hSadapt, hSclass,
    htraceInt, hpathint, hentryint, hcov⟩

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b7_shiftedHilbertMartingale
