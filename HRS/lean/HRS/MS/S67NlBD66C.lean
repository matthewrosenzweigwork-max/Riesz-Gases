import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.GradSmAux2
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.MovAdjAux20
import HRS.MS.S67NlBD29
import HRS.MS.S67NlBD30
import HRS.MS.S67NlBD33
import HRS.MS.S67NlBD39
import HRS.MS.S67NlBD40
import HRS.MS.S67NlBD41
import HRS.MS.S67NlBD47
import HRS.MS.S67NlBD51
import HRS.MS.S67NlBD53
import HRS.MS.S67NlBD64
import HRS.MS.S67NlBD65
import HRS.MS.S67NlBD66A
import HRS.MS.S67NlBD66B

/-!
# S6.7nl.66C: differentiated Duhamel inequality for the gradient `cb` norm
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: on a Brownian realization, `f r = hom + Φ` with `Φ x = ∫_{Icc 0 (T-r)} G t x dt`,
`G t = sg_{t/β}(src (r+t))` (packet 51).  Gradient smoothing on the source `J - F·∇f` with the jets
of packets 47 and 66A bounds `∂^i G t` by `CG · kernel 1 lam t · (CJ·‖ψ‖ + C·R0·Y)`;
packet 53 integrates the jet bounds; packet 66B bounds the homogeneous term.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- the kernel times a bounded measurable path is integrable on `[r,T]` -/
lemma s67bd66C_int {a lam T r : ℝ} (ha : a < 2) (hlam : 0 < lam) (hr : r ∈ Icc (0 : ℝ) T)
    {Z : ℝ → ℝ} (hZm : AEStronglyMeasurable Z (volume.restrict (Icc (0 : ℝ) T)))
    {B : ℝ} (hB : ∀ v ∈ Icc (0 : ℝ) T, |Z v| ≤ B) :
    IntegrableOn (fun v => s67bd_kernel a lam (v - r) * Z v) (Icc r T) volume := by
  have hker := s67bd_kernel_integrableOn ha hlam hr.2
  have hmeas : AEStronglyMeasurable Z (volume.restrict (Icc r T)) :=
    hZm.mono_measure (Measure.restrict_mono (Icc_subset_Icc hr.1 le_rfl) le_rfl)
  refine Integrable.mul_bdd (c := max B 0) hker hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hv0 : v ∈ Icc (0 : ℝ) T := ⟨le_trans hr.1 hv.1, hv.2⟩
  rw [Real.norm_eq_abs]
  exact (hB v hv0).trans (le_max_left _ _)

lemma s67bd66C_shift_int {F : ℝ → ℝ} {r T : ℝ} (hrT : r ≤ T) (h : IntegrableOn F (Icc r T) volume) :
    IntegrableOn (fun t => F (r + t)) (Icc 0 (T - r)) volume := by
  have h1 := (intervalIntegrable_iff_integrableOn_Icc_of_le hrT).2 h
  have h2 := h1.comp_add_left r
  rw [sub_self] at h2
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (sub_nonneg.2 hrT)).1 h2

lemma s67bd66C_shift_integral (F : ℝ → ℝ) {r T : ℝ} (hrT : r ≤ T) :
    ∫ t in Icc (0 : ℝ) (T - r), F (r + t) = ∫ v in Icc r T, F v := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (sub_nonneg.2 hrT), ← intervalIntegral.integral_of_le hrT,
    intervalIntegral.integral_comp_add_left F r]
  simp

lemma s67bd66C_kernel_le {β cg lam t : ℝ} (hβ : 0 < β) (hlam : lam ≤ cg / β) (ht : 0 < t) :
    (1 + (Real.sqrt (t / β))⁻¹) * Real.exp (-cg * (t / β)) ≤
      max 1 (Real.sqrt β) * s67bd_kernel 1 lam t := by
  have hu : t ^ ((-1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]; norm_num
  have hs : (Real.sqrt (t / β))⁻¹ = Real.sqrt β * (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_div ht.le, inv_div, div_eq_mul_inv]
  have hu0 : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg t)
  have hE : Real.exp (-cg * (t / β)) ≤ Real.exp (-lam * t) := by
    apply Real.exp_le_exp.2
    have : cg / β * t = cg * (t / β) := by ring
    nlinarith [mul_le_mul_of_nonneg_right hlam ht.le]
  have hmx1 : 1 ≤ max 1 (Real.sqrt β) := le_max_left _ _
  have hmx2 : Real.sqrt β ≤ max 1 (Real.sqrt β) := le_max_right _ _
  have h1 : 1 + (Real.sqrt (t / β))⁻¹ ≤ max 1 (Real.sqrt β) * (1 + (Real.sqrt t)⁻¹) := by
    rw [hs]; nlinarith [mul_le_mul_of_nonneg_right hmx2 hu0]
  unfold s67bd_kernel
  rw [hu]
  calc (1 + (Real.sqrt (t / β))⁻¹) * Real.exp (-cg * (t / β))
      ≤ (max 1 (Real.sqrt β) * (1 + (Real.sqrt t)⁻¹)) * Real.exp (-lam * t) :=
        mul_le_mul h1 hE (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 6400000 in
theorem s67bd_gradient_duhamel_inequality (H : Mov2dTh d s β q ρ₀)
    (j M m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M)
    (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m) :
    ∃ C lam : ℝ, 0 ≤ C ∧ 0 < lam ∧
      ∀ R0 c0 : ℝ, 0 ≤ R0 → R0 ≤ 1 → 0 ≤ c0 →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ →
      ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f →
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ →
      MemOsc (M : ℝ) (s67psi ρ₀ φ) → cbNormVecE j (fun x => gradient φ x) < ⊤ →
      ∀ r ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun v => s67bd_kernel 1 lam (v - r) * s67bd_Y j f v) (Icc r T) volume ∧
        IntegrableOn (fun v => s67bd_kernel 1 lam (v - r) *
          oscNorm (M : ℝ) (s67psi ρ₀ (f v))) (Icc r T) volume ∧
        s67bd_Y j f r ≤ C * Real.exp (-lam * (T - r)) *
          (cbNormVecE j (fun x => gradient φ x)).toReal +
          C * (∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * oscNorm (M : ℝ) (s67psi ρ₀ (f v))) +
          C * R0 * ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * s67bd_Y j f v := by
  have hβ := H.hβ
  have hq' : 0 < β * q := mul_pos hβ H.hq
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hM2 : 2 ≤ M := by exact_mod_cast (show (2 : ℝ) ≤ M by linarith)
  obtain ⟨CJ, hCJ0, hCJ⟩ := s67bd_J_bound H j M m hM hm hmM
  obtain ⟨C6, hC60, h6⟩ := s67bd_transport_source_jets H j M m hM hm hmM
  obtain ⟨Ch, lamh, hCh0, hlamh, hhom⟩ := s67bd_homogeneous_gradient_decay H j
  obtain ⟨Mb, hMb0, hMb⟩ := s67bd_onebody_drift H (j + 2)
  obtain ⟨Cg, cg, hCg0, hcg, hGS⟩ := HRS.MS.GradSm.gradient_smoothing_cb.{0} (d := d) (β * q) Mb hq'
    hMb0 (j + 2) (by omega) j (le_refl _)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = min lamh (cg / β) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := hlam ▸ lt_min hlamh (div_pos hcg hβ)
  have hlam1 : lam ≤ lamh := hlam ▸ min_le_left _ _
  have hlam2 : lam ≤ cg / β := hlam ▸ min_le_right _ _
  obtain ⟨CG, hCGdef⟩ : ∃ CG : ℝ, CG = Cg * max 1 (Real.sqrt β) * ((j : ℝ) + 1) := ⟨_, rfl⟩
  have hCG0 : 0 ≤ CG := by rw [hCGdef]; positivity
  refine ⟨((j : ℝ) + 1) * (Ch + CG * CJ + CG * C6), lam, by positivity, hlam0, ?_⟩
  intro R0 c0 hR0 hR1 hc0 f0 ρ hρ T φ f hT hf hφreg hφ hφfin
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := HRS.exists_isBrownianFiltration_type (Fin d)
  obtain ⟨Bf, hBf0, hBf⟩ := s67bd_bootstrap_finite H M m hM2 hm hmM R0 c0 hR0 hc0 f0 ρ hρ T φ f
    hT hf hφ
  obtain ⟨By, hBy0, hBy⟩ := s67bd_classical_cb_finite H j M m hM hm hmM R0 c0 hR0 hR1 hc0 f0 ρ hρ
    T φ f hT hf hφreg hφ hφfin
  have hreg : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (f r) := fun r hr =>
    ((s67bd_qualitative_regular H j M hM (f r) (hf.c2 r hr) (hBf r hr).1).1).of_le
      (by exact_mod_cast (by omega : j + 1 ≤ j + 5))
  have hmemcb : ∀ r ∈ Icc (0 : ℝ) T, MemCb 2 (f r) := by
    intro r hr
    refine ⟨hf.c2 r hr, fun j' hj' => ?_⟩
    obtain ⟨B, hB⟩ := hf.bdd j' hj'
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩
  have hfc : ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun p : ↥(Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) =>
        ((⟨p.1.1, p.2.1⟩ : Icc (0 : ℝ) T), p.1.2) :=
      (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    exact (s67_cont_val hf).comp h1
  obtain ⟨-, hYm⟩ := s67bd_gradient_norm_measurable d j T hT f hfc hreg (fun r hr => (hBy r hr).1)
  have hYnn : ∀ v, 0 ≤ s67bd_Y j f v := fun v => ENNReal.toReal_nonneg
  have hYb : ∀ v ∈ Icc (0 : ℝ) T, |s67bd_Y j f v| ≤ By := fun v hv => by
    rw [abs_of_nonneg (hYnn v)]; exact (hBy v hv).2
  have hOnn : ∀ v, 0 ≤ oscNorm (M : ℝ) (s67psi ρ₀ (f v)) := fun v =>
    HRS.MS.MovC1.movc1_osc_nonneg _ _
  have hOb : ∀ v ∈ Icc (0 : ℝ) T, |oscNorm (M : ℝ) (s67psi ρ₀ (f v))| ≤ Bf := fun v hv => by
    rw [abs_of_nonneg (hOnn v)]; exact (hBf v hv).2
  -- measurability of the weighted norm path
  obtain ⟨Ψ, R, hrep⟩ := s67bd_classical_realizations H m hm R0 c0 f0 ρ hρ T φ f hT hf
  obtain ⟨hΨc, -, -⟩ := s67bd_source_continuity H m hm R0 c0 f0 ρ hρ T φ f hT hf Ψ R hrep
  have hΨmem : ∀ v ∈ Icc (0 : ℝ) T, MemOsc (M : ℝ) (movFun (Ψ v)) := fun v hv =>
    HRS.MS.MovLin.mov2b_memOsc_congr (show movFun (Ψ v) =ᵐ[volume] _ from (hrep v hv).1).symm _
      (hBf v hv).1
  have hOm : AEStronglyMeasurable (fun v => oscNorm (M : ℝ) (s67psi ρ₀ (f v)))
      (volume.restrict (Icc (0 : ℝ) T)) := by
    have h33 := s67bd_higher_measurable ρ₀ (M : ℝ) T (by positivity) hT Ψ hΨc hΨmem
    refine h33.norm.congr ((ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun v hv => ?_))
    show ‖OscSpace.ofFun (M : ℝ) (movFun (Ψ v))‖ = oscNorm (M : ℝ) (s67psi ρ₀ (f v))
    rw [OscSpace.norm_ofFun _ (hΨmem v hv)]
    exact HRS.MS.MovLin.mov2b_oscNorm_congr (show movFun (Ψ v) =ᵐ[volume] _ from (hrep v hv).1) _
  -- jets of the source
  have hsrc : ∀ v ∈ Icc (0 : ℝ) T, ContDiff ℝ (j : WithTop ℕ∞) (s67bd_source d s ρ₀ ρ f v) ∧
      ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i (s67bd_source d s ρ₀ ρ f v) y‖ ≤
        CJ * oscNorm (M : ℝ) (s67psi ρ₀ (f v)) + C6 * R0 * s67bd_Y j f v := by
    intro v hv
    obtain ⟨hJ1, hJ2⟩ := hCJ R0 c0 hR0 hR1 hc0 f0 ρ hρ v hv.1 (f v) (hmemcb v hv) (hBf v hv).1
    obtain ⟨hI1, hI2⟩ := h6 R0 c0 hR0 hR1 hc0 f0 ρ hρ v hv.1 (f v) (hreg v hv) (hBy v hv).1
    have hJ1' : ContDiff ℝ (j : WithTop ℕ∞) (s67J d s (ρ v) (f v)) :=
      hJ1.of_le (by exact_mod_cast (by omega : j ≤ j + 2))
    have e : s67bd_source d s ρ₀ ρ f v = (s67J d s (ρ v) (f v)) -
        (fun x => inner ℝ (s67bd_F d s ρ₀ (movV ρ₀ ρ v) x) (gradient (f v) x)) := by
      funext x; rfl
    rw [e]
    refine ⟨hJ1'.sub hI1, fun i hi y => ?_⟩
    have hiC : (i : WithTop ℕ∞) ≤ j := by exact_mod_cast hi
    rw [iteratedFDeriv_sub_apply (hJ1'.of_le hiC).contDiffAt (hI1.of_le hiC).contDiffAt]
    exact (norm_sub_le _ _).trans (add_le_add (hJ2 i (by omega) y) (hI2 i hi y))
  have hmemφ : MemCb 2 φ := by
    have := hmemcb T ⟨hT, le_rfl⟩
    rwa [hf.terminal] at this
  intro r hr
  have hrT : r ≤ T := hr.2
  have hIY := s67bd66C_int (a := 1) (by norm_num) hlam0 hr hYm hYb
  have hIO := s67bd66C_int (a := 1) (by norm_num) hlam0 hr hOm hOb
  refine ⟨hIY, hIO, ?_⟩
  -- the Duhamel formula and the homogeneous term
  have h51 := s67bd_onebody_duhamel P ℱ W hW H j M m hM hm hmM R0 c0 hR0 hR1 hc0 f0 ρ hρ T φ f hT
    hf hφ r hr
  obtain ⟨hhomC, hhomF, hhomB⟩ := hhom P ℱ W hW φ hmemφ hφreg hφfin (T - r) (sub_nonneg.2 hrT)
  obtain ⟨hom, hhomdef⟩ : ∃ hom : Euc d → ℝ,
      hom = sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) ((T - r) / β) φ := ⟨_, rfl⟩
  rw [← hhomdef] at hhomC hhomF hhomB
  obtain ⟨Yφ, hYφ⟩ : ∃ Yφ : ℝ, Yφ = (cbNormVecE j (fun x => gradient φ x)).toReal := ⟨_, rfl⟩
  have hYφ0 : 0 ≤ Yφ := hYφ ▸ ENNReal.toReal_nonneg
  obtain ⟨Yh, hYhdef⟩ : ∃ Yh : ℝ, Yh = (cbNormVecE j (fun x => gradient hom x)).toReal :=
    ⟨_, rfl⟩
  have hYh0 : 0 ≤ Yh := hYhdef ▸ ENNReal.toReal_nonneg
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Euc d → ℝ, Φ = fun x => f r x - hom x := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → Euc d → ℝ, G = fun t x => sg P W (β * q)
      (s67bd_oneBodyB d s β ρ₀) (t / β) (s67bd_source d s ρ₀ ρ f (r + t)) x := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun t => CG * (CJ * (s67bd_kernel 1 lam t *
      oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t)))) +
      C6 * R0 * (s67bd_kernel 1 lam t * s67bd_Y j f (r + t))) := ⟨_, rfl⟩
  have hΦint : ∀ x, Φ x = ∫ t in Icc (0 : ℝ) (T - r), G t x := by
    intro x
    have h1 := (h51 x).2
    have h2 : ∫ v in r..T, sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) ((v - r) / β)
        (s67bd_source d s ρ₀ ρ f v) x = ∫ t in Icc (0 : ℝ) (T - r), G t x := by
      rw [intervalIntegral.integral_of_le hrT, ← integral_Icc_eq_integral_Ioc,
        ← s67bd66C_shift_integral (fun v => sg P W (β * q) (s67bd_oneBodyB d s β ρ₀)
          ((v - r) / β) (s67bd_source d s ρ₀ ρ f v) x) hrT, hGdef]
      simp
    rw [hΦdef]
    show f r x - hom x = _
    rw [← h2, h1, ← hhomdef]
    ring
  have hGI : ∀ x, IntegrableOn (fun t => G t x) (Icc (0 : ℝ) (T - r)) volume := by
    intro x
    have h1 := (intervalIntegrable_iff_integrableOn_Icc_of_le hrT).1 (h51 x).1
    have h2 := s67bd66C_shift_int hrT h1
    rw [hGdef]
    simpa using h2
  have hIOt : IntegrableOn (fun t => s67bd_kernel 1 lam t *
      oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t)))) (Icc (0 : ℝ) (T - r)) volume := by
    simpa using s67bd66C_shift_int hrT hIO
  have hIYt : IntegrableOn (fun t => s67bd_kernel 1 lam t * s67bd_Y j f (r + t))
      (Icc (0 : ℝ) (T - r)) volume := by
    simpa using s67bd66C_shift_int hrT hIY
  have hgI : IntegrableOn g (Icc (0 : ℝ) (T - r)) volume := by
    rw [hgdef]
    exact ((hIOt.const_mul CJ).add (hIYt.const_mul (C6 * R0))).const_mul CG
  have hae : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (T - r))),
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (G t) ∧ 0 ≤ g t ∧
      ∀ i, 1 ≤ i → i ≤ j + 1 → ∀ x, ‖iteratedFDeriv ℝ i (G t) x‖ ≤ g t := by
    have hne : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (T - r))), t ≠ 0 :=
      ae_restrict_of_ae (by rw [ae_iff]; simp)
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with t ht ht0
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hv : r + t ∈ Icc (0 : ℝ) T := ⟨by linarith [hr.1, ht.1], by linarith [ht.2]⟩
    have hk0 : 0 ≤ s67bd_kernel 1 lam t := s67bd_kernel_nonneg 1 lam htpos.le
    have hSv0 : 0 ≤ CJ * oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t))) +
        C6 * R0 * s67bd_Y j f (r + t) :=
      add_nonneg (mul_nonneg hCJ0 (hOnn _)) (mul_nonneg (mul_nonneg hC60 hR0) (hYnn _))
    have hg0 : 0 ≤ g t := by
      rw [hgdef]
      exact mul_nonneg hCG0 (add_nonneg (mul_nonneg hCJ0 (mul_nonneg hk0 (hOnn _)))
        (mul_nonneg (mul_nonneg hC60 hR0) (mul_nonneg hk0 (hYnn _))))
    obtain ⟨hc1, -, hj, -⟩ := hGS P ℱ W hW (s67bd_oneBodyB d s β ρ₀) hMb
      (s67bd_source d s ρ₀ ρ f (r + t)) (hsrc _ hv).1
      (fun _ => CJ * oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t))) + C6 * R0 * s67bd_Y j f (r + t))
      (fun i hi y => (hsrc _ hv).2 i hi y) (t / β) (div_pos htpos hβ)
    refine ⟨by rw [hGdef]; exact hc1, hg0, fun i hi1 hi2 x => ?_⟩
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have h1 := hj i' (by omega) x
    rw [HRS.MS.GradSm.s67b_norm_iter_grad (hc1.of_le (by exact_mod_cast
      (by omega : i' + 1 ≤ j + 1))) x] at h1
    have h2 : (∑ _i ∈ Finset.range (j + 1), (CJ * oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t))) +
        C6 * R0 * s67bd_Y j f (r + t))) = ((j : ℝ) + 1) * (CJ * oscNorm (M : ℝ)
        (s67psi ρ₀ (f (r + t))) + C6 * R0 * s67bd_Y j f (r + t)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    rw [h2] at h1
    have hA := s67bd66C_kernel_le (cg := cg) (lam := lam) hβ hlam2 htpos
    rw [hGdef]
    refine h1.trans ?_
    calc Cg * (1 + (Real.sqrt (t / β))⁻¹) * Real.exp (-cg * (t / β)) *
          (((j : ℝ) + 1) * (CJ * oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t))) +
            C6 * R0 * s67bd_Y j f (r + t)))
        = Cg * ((1 + (Real.sqrt (t / β))⁻¹) * Real.exp (-cg * (t / β))) *
          (((j : ℝ) + 1) * (CJ * oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t))) +
            C6 * R0 * s67bd_Y j f (r + t))) := by ring
      _ ≤ Cg * (max 1 (Real.sqrt β) * s67bd_kernel 1 lam t) *
          (((j : ℝ) + 1) * (CJ * oscNorm (M : ℝ) (s67psi ρ₀ (f (r + t))) +
            C6 * R0 * s67bd_Y j f (r + t))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hCg0)
          (mul_nonneg (by positivity) hSv0)
      _ = g t := by rw [hgdef, hCGdef]; ring
  have hΦK : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) Φ := by
    rw [hΦdef]; exact (hreg r hr).sub hhomC
  have hD := (s67bd_param_deriv_ae d (j + 1) (by omega) (T - r) (sub_nonneg.2 hrT) G g hGI hgI
    hae Φ hΦint hΦK).2
  -- the value of the integral
  have hIg : ∫ t in Icc (0 : ℝ) (T - r), g t =
      CG * (CJ * (∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * oscNorm (M : ℝ) (s67psi ρ₀ (f v))) +
        C6 * R0 * ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * s67bd_Y j f v) := by
    rw [hgdef]
    simp only []
    rw [integral_const_mul, integral_add (hIOt.const_mul CJ) (hIYt.const_mul (C6 * R0)),
      integral_const_mul, integral_const_mul]
    have e1 := s67bd66C_shift_integral (fun v => s67bd_kernel 1 lam (v - r) *
      oscNorm (M : ℝ) (s67psi ρ₀ (f v))) hrT
    have e2 := s67bd66C_shift_integral (fun v => s67bd_kernel 1 lam (v - r) *
      s67bd_Y j f v) hrT
    simp only [add_sub_cancel_left] at e1 e2
    rw [e1, e2]
  -- jet bounds for the gradient of `f r = hom + Φ`
  have hfe : f r = hom + Φ := by
    funext y; rw [hΦdef]; simp
  have hpt : ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i (fun y => gradient (f r) y) x‖ ≤
      Yh + ∫ t in Icc (0 : ℝ) (T - r), g t := by
    intro i hi x
    have hiC : ((i + 1 : ℕ) : WithTop ℕ∞) ≤ ((j + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : i + 1 ≤ j + 1)
    rw [HRS.MS.GradSm.s67b_norm_iter_grad ((hreg r hr).of_le hiC) x, hfe,
      iteratedFDeriv_add_apply (hhomC.of_le hiC).contDiffAt (hΦK.of_le hiC).contDiffAt]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hD (i + 1) (by omega) (by omega) x))
    rw [← HRS.MS.GradSm.s67b_norm_iter_grad (hhomC.of_le hiC) x]
    have hcb : cbNormVecE j (fun x => gradient hom x) ≤ ENNReal.ofReal Yh := by
      rw [hYhdef]; exact (ENNReal.ofReal_toReal hhomF.ne).ge
    exact (s67bd63_cb_le hcb hi x).trans (max_eq_left hYh0).le
  have hIg0 : 0 ≤ ∫ t in Icc (0 : ℝ) (T - r), g t := by
    refine setIntegral_nonneg measurableSet_Icc (fun t ht => ?_)
    rw [hgdef]
    have hk0 : 0 ≤ s67bd_kernel 1 lam t := s67bd_kernel_nonneg 1 lam ht.1
    exact mul_nonneg hCG0 (add_nonneg (mul_nonneg hCJ0 (mul_nonneg hk0 (hOnn _)))
      (mul_nonneg (mul_nonneg hC60 hR0) (mul_nonneg hk0 (hYnn _))))
  have hYr : s67bd_Y j f r ≤ ((j : ℝ) + 1) * (Yh + ∫ t in Icc (0 : ℝ) (T - r), g t) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    unfold cbNormVecE
    have h1 : ∀ i ∈ Finset.range (j + 1), (⨆ x : Euc d,
        ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => gradient (f r) y) x‖) ≤
        ENNReal.ofReal (Yh + ∫ t in Icc (0 : ℝ) (T - r), g t) := fun i hi =>
      iSup_le fun x => ENNReal.ofReal_le_ofReal (hpt i (by have := Finset.mem_range.1 hi; omega) x)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine le_of_eq (congrArg _ ?_)
    push_cast; ring
  -- the homogeneous term with the common rate
  have hexp : Real.exp (-lamh * (T - r)) ≤ Real.exp (-lam * (T - r)) :=
    Real.exp_le_exp.2 (by nlinarith [sub_nonneg.2 hrT])
  have hYh : Yh ≤ Ch * Real.exp (-lam * (T - r)) * Yφ := by
    rw [hYhdef, hYφ]
    refine hhomB.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hCh0) ENNReal.toReal_nonneg
  have hIO0 : 0 ≤ ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) *
      oscNorm (M : ℝ) (s67psi ρ₀ (f v)) :=
    setIntegral_nonneg measurableSet_Icc (fun v hv => mul_nonneg
      (s67bd_kernel_nonneg 1 lam (sub_nonneg.2 hv.1)) (hOnn _))
  have hIY0 : 0 ≤ ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * s67bd_Y j f v :=
    setIntegral_nonneg measurableSet_Icc (fun v hv => mul_nonneg
      (s67bd_kernel_nonneg 1 lam (sub_nonneg.2 hv.1)) (hYnn _))
  obtain ⟨IO, hIOdef⟩ : ∃ IO : ℝ, IO = ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) *
      oscNorm (M : ℝ) (s67psi ρ₀ (f v)) := ⟨_, rfl⟩
  obtain ⟨IY, hIYdef⟩ : ∃ IY : ℝ, IY = ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) *
      s67bd_Y j f v := ⟨_, rfl⟩
  rw [← hIOdef] at hIg hIO0 ⊢
  rw [← hIYdef] at hIg hIY0 ⊢
  rw [← hYφ]
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (-lam * (T - r)) * Yφ := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; exact mul_nonneg (Real.exp_pos _).le hYφ0
  have hj1 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hcc1 : 0 ≤ CG * CJ := mul_nonneg hCG0 hCJ0
  have hcc2 : 0 ≤ CG * C6 := mul_nonneg hCG0 hC60
  have hmain : s67bd_Y j f r ≤ ((j : ℝ) + 1) * (Ch * E + CG * (CJ * IO + C6 * R0 * IY)) := by
    rw [hIg] at hYr
    refine hYr.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hj1)
    calc Yh ≤ Ch * Real.exp (-lam * (T - r)) * Yφ := hYh
      _ = Ch * E := by rw [hEdef]; ring
  have k1 : ((j : ℝ) + 1) * (Ch * E) ≤ ((j : ℝ) + 1) * (Ch + CG * CJ + CG * C6) * E := by
    nlinarith [mul_nonneg hj1 (mul_nonneg hcc1 hE0), mul_nonneg hj1 (mul_nonneg hcc2 hE0)]
  have k2 : ((j : ℝ) + 1) * (CG * (CJ * IO)) ≤ ((j : ℝ) + 1) * (Ch + CG * CJ + CG * C6) * IO := by
    nlinarith [mul_nonneg hj1 (mul_nonneg hCh0 hIO0), mul_nonneg hj1 (mul_nonneg hcc2 hIO0)]
  have k3 : ((j : ℝ) + 1) * (CG * (C6 * R0 * IY)) ≤
      ((j : ℝ) + 1) * (Ch + CG * CJ + CG * C6) * R0 * IY := by
    have hR := mul_nonneg hR0 hIY0
    nlinarith [mul_nonneg hj1 (mul_nonneg hCh0 hR), mul_nonneg hj1 (mul_nonneg hcc1 hR)]
  rw [hEdef] at k1 hmain
  linarith [k1, k2, k3, hmain]

end HRS.MS.BreakdownS67
