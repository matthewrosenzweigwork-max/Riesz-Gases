import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD55

/-!
# S6.7 nonlinear, packet S6.7nl.59A: generic physical-time OU Duhamel with Brownian data

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4835-4851, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definition: `s67bd_OUDuhamel`.
The unit-viscosity data `U(sigma, y) = u(sigma/nu, y)` on `[0, nu T]` with drift parameter `q/nu`,
zero bounded drift and source `(B grad u + J)/nu` is packaged as `S67DuhData` (all fields are
verified from `s67bd_ParabolicData`), the merged `s67_duhamel_abs` is applied at `tau = nu t`, and
the substitution `sigma = nu v` returns the physical-time integral; interval integrability comes
from `s67_cont_sg_comp`. `T = 0` is the time-zero identity `sg 0 f = f`.
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

def s67bd_OUDuhamel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (ν q T : ℝ)
    (u : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Euc d,
    IntervalIntegrable (fun v => sg P W (q / ν) (fun _ => 0) (ν * (t - v))
      (fun y => inner ℝ (B v y) (gradient (u v) y) + J v y) x) volume 0 t ∧
    u t x = sg P W (q / ν) (fun _ => 0) (ν * t) (u 0) x +
      ∫ v in (0 : ℝ)..t, sg P W (q / ν) (fun _ => 0) (ν * (t - v))
        (fun y => inner ℝ (B v y) (gradient (u v) y) + J v y) x

lemma s67bd59_zero_cb (m : ℕ) : HasCbBound (d := d) m 0 (fun _ : Euc d => (0 : Euc d)) := by
  refine ⟨contDiff_const, fun j _ x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

lemma s67bd59_gradient_norm (f : Euc d → ℝ) (y : Euc d) :
    ‖gradient f y‖ = ‖fderiv ℝ f y‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

lemma s67bd59_fderiv_eq_curry (f : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ f x = continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 f x) := by
  ext v
  simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

lemma s67bd59_val_eq (f : Euc d → ℝ) (x : Euc d) :
    continuousMultilinearCurryFin0 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 0 f x) = f x := by
  rw [iteratedFDeriv_zero_eq_comp]; simp

/-- time-zero identity of the semigroup -/
lemma s67bd59_sg_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → Fin d → ℝ) (hW' : SgNoise W) {q' : ℝ} (hq : 0 ≤ q')
    (f : Euc d → ℝ) (x : Euc d) :
    sg P W q' (fun _ : Euc d => (0 : Euc d)) 0 f x = f x := by
  unfold sg
  have : ∀ o, flowMap q' (fun _ : Euc d => (0 : Euc d)) (fun s => W s o) 0 x = x := by
    intro o
    have H : PfHyp q' 0 1 (fun _ : Euc d => (0 : Euc d)) (fun s => W s o) :=
      ⟨hq, le_rfl, s67bd59_zero_cb 1, hW'.cont o, hW'.zero o⟩
    simp [flowMap, pf_Z_zero H, pf_ou_zero (w := fun s => W s o) (hW'.zero o)]
  simp [this]


lemma s67bd59_scale_cont {E : Type*} [TopologicalSpace E] {ν T : ℝ} (hν : 0 < ν)
    {F : ℝ → Euc d → E}
    (hF : ContinuousOn (fun p : ℝ × Euc d => F p.1 p.2) (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)))) :
    ContinuousOn (fun p : ℝ × Euc d => F (p.1 / ν) p.2)
      (Icc (0 : ℝ) (ν * T) ×ˢ (univ : Set (Euc d))) := by
  have h1 : ContinuousOn (fun p : ℝ × Euc d => (p.1 / ν, p.2))
      (Icc (0 : ℝ) (ν * T) ×ˢ (univ : Set (Euc d))) :=
    (continuousOn_fst.div_const ν).prodMk continuousOn_snd
  refine hF.comp h1 (fun p hp => ⟨⟨div_nonneg hp.1.1 hν.le, ?_⟩, mem_univ _⟩)
  rw [div_le_iff₀ hν]
  nlinarith [hp.1.2]

lemma s67bd59_fderiv_cont {u : ℝ → Euc d → ℝ} {S : Set (ℝ × Euc d)}
    (hc : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 1 (u p.1) p.2) S) :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (u p.1) p.2) S :=
  ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp_continuousOn hc).congr
    (fun p _ => s67bd59_fderiv_eq_curry _ _)

lemma s67bd59_gradient_cont {u : ℝ → Euc d → ℝ} {S : Set (ℝ × Euc d)}
    (hc : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 1 (u p.1) p.2) S) :
    ContinuousOn (fun p : ℝ × Euc d => gradient (u p.1) p.2) S :=
  ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
    (s67bd59_fderiv_cont hc))

lemma s67bd59_val_cont {u : ℝ → Euc d → ℝ} {S : Set (ℝ × Euc d)}
    (hc : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 0 (u p.1) p.2) S) :
    ContinuousOn (fun p : ℝ × Euc d => u p.1 p.2) S :=
  ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp_continuousOn hc).congr
    (fun p _ => s67bd59_val_eq _ _)

lemma s67bd59_duhData (ν q T Mb MJ : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ)
    (hu : s67bd_ParabolicData ν q T u a B J)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖B t x‖ ≤ Mb)
    (hJ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |J t x| ≤ MJ) :
    S67DuhData (q / ν) (fun _ : Euc d => (0 : Euc d)) (ν * T)
      (fun σ y => u (σ / ν) y) (fun σ y => ν⁻¹ * a (σ / ν) y)
      (fun σ y => ν⁻¹ * (inner ℝ (B (σ / ν) y) (gradient (u (σ / ν)) y) + J (σ / ν) y)) := by
  have hmem : ∀ σ ∈ Icc (0 : ℝ) (ν * T), σ / ν ∈ Icc (0 : ℝ) T := fun σ hσ =>
    ⟨div_nonneg hσ.1 hν.le, by rw [div_le_iff₀ hν]; nlinarith [hσ.2]⟩
  obtain ⟨K, hK⟩ := hu.bdd_c2
  have hgc1 := hu.cont_c2 1 (by norm_num)
  have hgrad : ContinuousOn (fun p : ℝ × Euc d => gradient (u p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := s67bd59_gradient_cont hgc1
  have hfd : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (u p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := s67bd59_fderiv_cont hgc1
  have hucont : ContinuousOn (fun p : ℝ × Euc d => u p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := s67bd59_val_cont (hu.cont_c2 0 (by norm_num))
  have hgn : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, ‖gradient (u t) y‖ ≤ K := fun t ht y => by
    rw [s67bd59_gradient_norm, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact hK t ht 1 (by norm_num) y
  have hScont : ContinuousOn (fun p : ℝ × Euc d =>
      inner ℝ (B p.1 p.2) (gradient (u p.1) p.2) + J p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) :=
    (hu.Bcont.inner hgrad).add hu.Jcont
  refine
    { c2 := fun σ hσ => hu.c2 _ (hmem σ hσ)
      bd := ⟨K, K, K, fun σ hσ y => ⟨?_, ?_, ?_⟩⟩
      ucont := s67bd59_scale_cont hν (F := u) hucont
      gcont := s67bd59_scale_cont hν (F := fun r y => fderiv ℝ (u r) y) hfd
      acont := (continuousOn_const.mul (s67bd59_scale_cont hν (F := a) hu.acont))
      agrow := ?_
      Scont := continuousOn_const.mul (s67bd59_scale_cont hν
        (F := fun r y => inner ℝ (B r y) (gradient (u r) y) + J r y) hScont)
      Sbd := ?_
      hint := ?_
      hL := ?_ }
  · have := hK _ (hmem σ hσ) 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := hK _ (hmem σ hσ) 1 (by norm_num) y
    rwa [norm_iteratedFDeriv_one] at this
  · exact hK _ (hmem σ hσ) 2 le_rfl y
  · obtain ⟨Ka, hKa⟩ := hu.agrow
    refine ⟨ν⁻¹ * Ka, fun σ hσ y => ?_⟩
    have := hKa _ (hmem σ hσ) y
    rw [abs_mul, abs_of_pos (inv_pos.2 hν)]
    calc ν⁻¹ * |a (σ / ν) y| ≤ ν⁻¹ * (Ka * (1 + ‖y‖)) :=
          mul_le_mul_of_nonneg_left this (inv_pos.2 hν).le
      _ = ν⁻¹ * Ka * (1 + ‖y‖) := by ring
  · refine ⟨ν⁻¹ * (Mb * K + MJ), fun σ hσ y => ?_⟩
    have ht := hmem σ hσ
    have h1 : |inner ℝ (B (σ / ν) y) (gradient (u (σ / ν)) y)| ≤ Mb * K := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul (hB _ ht y) (hgn _ ht y) (norm_nonneg _) ((norm_nonneg _).trans (hB _ ht y))
    rw [abs_mul, abs_of_pos (inv_pos.2 hν)]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (inv_pos.2 hν).le
    linarith [hJ _ ht y]
  · intro σ hσ s0 hs0 y
    have h := hu.hint _ (hmem σ hσ) _ (hmem s0 hs0) y
    rw [h]
    have := intervalIntegral.integral_comp_div (a := s0) (b := σ) (fun v => a v y) hν.ne'
    simp only [smul_eq_mul] at this
    simp only [intervalIntegral.integral_const_mul]
    rw [this]
    field_simp
  · intro σ hσ y
    have ht := hmem σ hσ
    have he := hu.equation _ ht y
    unfold kolmL
    simp only [add_zero]
    rw [he]
    simp only [inner_add_left, inner_smul_left, inner_neg_left, RCLike.conj_to_real]
    field_simp
    ring


lemma s67bd59_sg_const_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (q' : ℝ) (B : Euc d → Euc d) (τ c : ℝ) (f : Euc d → ℝ)
    (x : Euc d) : sg P W q' B τ (fun y => c * f y) x = c * sg P W q' B τ f x := by
  unfold sg
  exact integral_const_mul c _

set_option maxHeartbeats 1600000 in
theorem s67bd_parabolic_ou_duhamel {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : IsBrownianFiltration P ℱ W)
    (ν q T Mb MJ : ℝ) (hν : 0 < ν) (hq : 0 < q) (hT : 0 ≤ T)
    (hMb : 0 ≤ Mb) (hMJ : 0 ≤ MJ)
    (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ)
    (hu : s67bd_ParabolicData ν q T u a B J)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖B t x‖ ≤ Mb)
    (hJ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |J t x| ≤ MJ) :
    s67bd_OUDuhamel P W ν q T u B J := by
  have hq' : 0 < q / ν := div_pos hq hν
  have hW' := sgNoise_of_brownian hW
  intro t ht x
  rcases hT.eq_or_lt with hT0 | hTpos
  · -- T = 0
    have ht0 : t = 0 := le_antisymm (hT0 ▸ ht.2) ht.1
    subst ht0
    refine ⟨by simp, ?_⟩
    simp [s67bd59_sg_zero P W hW' hq'.le]
  · set gg : ℝ → Euc d → ℝ := fun v y => inner ℝ (B v y) (gradient (u v) y) + J v y with hgg
    set Sf : ℝ → Euc d → ℝ := fun σ y => ν⁻¹ * gg (σ / ν) y with hSf
    have hD := s67bd59_duhData ν q T Mb MJ hν hT u a B J hu hB hJ
    have hνT : 0 < ν * T := mul_pos hν hTpos
    have hτmem : ν * t ∈ Icc (0 : ℝ) (ν * T) :=
      ⟨mul_nonneg hν.le ht.1, mul_le_mul_of_nonneg_left ht.2 hν.le⟩
    have e1 : ν * t / ν = t := by field_simp
    have hduh := s67_duhamel_abs (P := P) (W := W) hW hq' (m := 2) le_rfl (s67bd59_zero_cb 2)
      hD hνT hτmem x
    simp only [e1, zero_div] at hduh
    -- reduce the integral by scaling
    set Fv : ℝ → ℝ := fun v => sg P W (q / ν) (fun _ => 0) (ν * (t - v)) (gg v) x with hFv
    have hint1 : ∫ s in (0 : ℝ)..(ν * t), sg P W (q / ν) (fun _ => 0) (ν * t - s) (Sf s) x =
        ∫ v in (0 : ℝ)..t, Fv v := by
      have h1 : ∀ s, sg P W (q / ν) (fun _ => 0) (ν * t - s) (Sf s) x = ν⁻¹ * Fv (s / ν) := by
        intro s
        rw [hSf]
        simp only []
        rw [s67bd59_sg_const_mul, hFv]
        simp only []
        congr 2
        field_simp
      simp_rw [h1]
      rw [intervalIntegral.integral_const_mul]
      have := intervalIntegral.integral_comp_div (a := 0) (b := ν * t) Fv hν.ne'
      simp only [smul_eq_mul, zero_div, e1] at this
      rw [this]
      field_simp
    -- continuity (hence interval integrability) of the physical integrand
    have hcl : Continuous fun p : ℝ × Euc d => Sf (HRS.clampT (ν * T) p.1) p.2 :=
      s67_comp_clamp (g := Sf) hνT.le hD.Scont
    obtain ⟨KS, hKS⟩ := hD.Sbd
    have hcont := s67_cont_sg_comp (P := P) (W := W) (ℱ := ℱ) hW hq' (m := 2) le_rfl
      (s67bd59_zero_cb 2) hνT.le (g := fun s y => Sf (HRS.clampT (ν * T) s) y) hcl
      (K := KS) (fun r y => hKS _ (HRS.clampT_mem hνT.le r) y) hτmem x
    have hFcont : ContinuousOn Fv (Icc 0 t) := by
      have hH : ContinuousOn (fun v => ν * sg P W (q / ν) (fun _ => 0) (ν * t - ν * v)
          (fun y => Sf (HRS.clampT (ν * T) (ν * v)) y) x) (Icc 0 t) :=
        continuousOn_const.mul (hcont.comp (continuous_const.mul continuous_id).continuousOn
          (fun v hv => ⟨mul_nonneg hν.le hv.1, mul_le_mul_of_nonneg_left hv.2 hν.le⟩))
      refine hH.congr (fun v hv => ?_)
      have hv' : ν * v ∈ Icc (0 : ℝ) (ν * T) :=
        ⟨mul_nonneg hν.le hv.1, mul_le_mul_of_nonneg_left (hv.2.trans ht.2) hν.le⟩
      have e2 : (fun y => Sf (ν * v) y) = fun y => ν⁻¹ * gg v y := by
        funext y; simp only [hSf]; rw [mul_div_cancel_left₀ _ hν.ne']
      beta_reduce
      rw [HRS.clampT_of_mem hv', e2, s67bd59_sg_const_mul,
        show ν * t - ν * v = ν * (t - v) by ring, ← mul_assoc, mul_inv_cancel₀ hν.ne', one_mul]
    refine ⟨?_, ?_⟩
    · have : IntervalIntegrable Fv volume 0 t := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
        exact hFcont.integrableOn_Icc
      exact this
    · rw [hint1] at hduh
      exact hduh

end HRS.MS.BreakdownS67
