import HRS.MS.SA12W2M

/-!
# S.A.12 C5 (SA12W2 worker), part N: the symmetric annulus term of the cutoff comparison

For a `GoodKernel` `G` (odd, `‖G z‖ ≤ C(‖z‖^{-s-1}+1)`), the function
`Q(w) = ([‖mk w‖ ≤ 1/4] - [‖L w‖ ≤ 1/4]) G(mk w)` is bounded on the centred cube, hence integrable there, and has integral zero
(oddness; the cubes `[-1/2,1/2)^d`, `(-1/2,1/2]^d` agree a.e.).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

/-- The cube `(-1/2,1/2]^d`. -/
def sa12w2_cubeO (d : ℕ) : Set (Euc d) := {w | ∀ i, w i ∈ Ioc (-1 / 2 : ℝ) (1 / 2)}

theorem sa12w2_cubeO_neg : (fun w : Euc d => -w) ⁻¹' sa12w2_cubeC d = sa12w2_cubeO d := by
  ext w
  simp only [mem_preimage, sa12w2_cubeC, sa12w2_cubeO, mem_setOf_eq, mem_Ico, mem_Ioc]
  refine forall_congr' fun i => ?_
  simp only [PiLp.neg_apply]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem sa12w2_cubeC_ae_cubeO : sa12w2_cubeC d =ᵐ[volume] sa12w2_cubeO d := by
  have h1 : sa12w2_cubeC d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ico (-1 / 2 : ℝ) (1 / 2)) := by
    ext w; simp [sa12w2_cubeC]
  have h2 : sa12w2_cubeO d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (-1 / 2 : ℝ) (1 / 2)) := by
    ext w; simp [sa12w2_cubeO]
  rw [h1, h2]
  have hae : (Set.pi univ fun _ : Fin d => Ico (-1 / 2 : ℝ) (1 / 2)) =ᵐ[Measure.pi fun _ : Fin d => (volume : Measure ℝ)]
      (Set.pi univ fun _ : Fin d => Ioc (-1 / 2 : ℝ) (1 / 2)) :=
    Measure.ae_eq_set_pi fun _ _ => Ico_ae_eq_Ioc
  exact (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.preimage_ae_eq hae

theorem sa12w2_mk_neg (w : Euc d) : Torus.mk (-w) = -Torus.mk w := by
  have h := Torus.mk_add w (-w)
  rw [add_neg_cancel] at h
  have h0 : (Torus.mk (0 : Euc d)) = 0 := by funext i; simp [Torus.mk]
  rw [h0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- The annulus integrand. -/
def sa12w2_Q (L : ℝ) (G : Torus d → Euc d) (w : Euc d) : Euc d :=
  ((if ‖(Torus.mk w : Torus d)‖ ≤ 1 / 4 then (1 : ℝ) else 0) - (if ‖L • w‖ ≤ 1 / 4 then (1 : ℝ) else 0)) •
    G (Torus.mk w)

theorem sa12w2_Q_odd {L : ℝ} {s C : ℝ} {G : Torus d → Euc d} (hG : HRS.KernelGrad.GoodKernel d s C G) (w : Euc d) :
    sa12w2_Q L G (-w) = -sa12w2_Q L G w := by
  simp only [sa12w2_Q, sa12w2_mk_neg, norm_neg, smul_neg, hG.odd]

theorem sa12w2_Q_int_zero {L s C : ℝ} {G : Torus d → Euc d} (hG : HRS.KernelGrad.GoodKernel d s C G) :
    ∫ w in sa12w2_cubeC d, sa12w2_Q L G w = 0 := by
  have h1 : ∫ w in sa12w2_cubeC d, sa12w2_Q L G w = ∫ w in sa12w2_cubeO d, sa12w2_Q L G w :=
    setIntegral_congr_set sa12w2_cubeC_ae_cubeO
  have h2 : ∫ w in sa12w2_cubeO d, sa12w2_Q L G w = ∫ w in sa12w2_cubeC d, sa12w2_Q L G (-w) := by
    rw [← sa12w2_cubeO_neg]
    have := (Measure.measurePreserving_neg (volume : Measure (Euc d))).setIntegral_preimage_emb
      (MeasurableEquiv.neg (Euc d)).measurableEmbedding (fun z => sa12w2_Q L G (-z)) (sa12w2_cubeC d)
    simpa [neg_neg] using this
  have h3 : ∫ w in sa12w2_cubeC d, sa12w2_Q L G (-w) = -∫ w in sa12w2_cubeC d, sa12w2_Q L G w := by
    simp_rw [sa12w2_Q_odd hG]
    rw [integral_neg]
  have h4 : ∫ w in sa12w2_cubeC d, sa12w2_Q L G w = -∫ w in sa12w2_cubeC d, sa12w2_Q L G w :=
    h1.trans (h2.trans h3)
  have h5 : (2 : ℝ) • ∫ w in sa12w2_cubeC d, sa12w2_Q L G w = 0 := by
    rw [two_smul]; nth_rewrite 1 [h4]; simp
  simpa using h5

theorem sa12w2_cubeC_finite : IsFiniteMeasure (volume.restrict (sa12w2_cubeC d)) := by
  refine ⟨?_⟩
  have := (sa12w2_mk_mp_cubeC (d := d)).measure_preimage (s := univ) MeasurableSet.univ.nullMeasurableSet
  simp only [preimage_univ] at this
  rw [Measure.restrict_apply_univ] at this
  rw [Measure.restrict_apply_univ, this]
  exact measure_lt_top _ _

theorem sa12w2_Q_integrable {L s C : ℝ} (hL : 0 < L) (hd : 1 ≤ d) {G : Torus d → Euc d}
    (hG : HRS.KernelGrad.GoodKernel d s C G) :
    IntegrableOn (sa12w2_Q L G) (sa12w2_cubeC d) := by
  have := sa12w2_cubeC_finite (d := d)
  have hmk : Measurable (Torus.mk : Euc d → Torus d) := (sa12w2_mk_mp_cubeC (d := d)).measurable
  have hmeas : Measurable (sa12w2_Q L G) := by
    unfold sa12w2_Q
    have hm1 : Measurable (fun w : Euc d => if ‖(Torus.mk w : Torus d)‖ ≤ 1 / 4 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le (measurable_norm.comp hmk) measurable_const) measurable_const
        measurable_const
    have hm2 : Measurable (fun w : Euc d => if ‖L • w‖ ≤ 1 / 4 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le (measurable_norm.comp (measurable_const_smul L)) measurable_const)
        measurable_const measurable_const
    exact (hm1.sub hm2).smul (hG.meas.comp hmk)
  set δ : ℝ := min (1 / 4) (1 / (4 * L * d)) with hδ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := C * (δ ^ (-s - 1) + 1)) ?_
  filter_upwards [ae_restrict_mem sa12w2_measurableSet_cubeC] with w hw
  have hwb : ∀ i, |w i| ≤ 1 / 2 := fun i => by
    have := hw i
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  by_cases hQ : sa12w2_Q L G w = 0
  · rw [hQ, norm_zero]
    have := hG.hC0
    have : 0 ≤ δ ^ (-s - 1) := (Real.rpow_pos_of_pos hδpos _).le
    positivity
  · have hδle : δ ≤ ‖(Torus.mk w : Torus d)‖ := by
      by_cases h2 : ‖(Torus.mk w : Torus d)‖ ≤ 1 / 4
      · by_cases h1 : ‖L • w‖ ≤ 1 / 4
        · exact absurd (by unfold sa12w2_Q; rw [if_pos h2, if_pos h1]; simp : sa12w2_Q L G w = 0) hQ
        · have hall := (sa12w2_norm_mk_le hwb (norm_nonneg _)).1 le_rfl
          have hsum : ‖w‖ ≤ d * ‖(Torus.mk w : Torus d)‖ := by
            have := HRS.KernelAux.norm_toLp_le_sum (d := d) (fun i => w i)
            refine this.trans ?_
            calc ∑ j, |w j| ≤ ∑ _j : Fin d, ‖(Torus.mk w : Torus d)‖ := Finset.sum_le_sum fun j _ => hall j
              _ = d * ‖(Torus.mk w : Torus d)‖ := by simp
          have h3 : 1 / 4 < L * ‖w‖ := by
            rw [norm_smul, Real.norm_of_nonneg hL.le] at h1
            exact not_le.1 h1
          refine (min_le_right _ _).trans ?_
          rw [div_le_iff₀ (by positivity)]
          nlinarith
      · exact (min_le_left _ _).trans (not_le.1 h2).le
    have hne : (Torus.mk w : Torus d) ≠ 0 := by
      intro h; rw [h, norm_zero] at hδle; linarith
    have hb := hG.bound_norm _ hne
    have hpow : ‖(Torus.mk w : Torus d)‖ ^ (-s - 1) ≤ δ ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hδpos hδle (by have := hG.hs0; linarith)
    have hC := hG.hC0
    have hcoef : ‖((if ‖(Torus.mk w : Torus d)‖ ≤ 1 / 4 then (1 : ℝ) else 0) -
        (if ‖L • w‖ ≤ 1 / 4 then (1 : ℝ) else 0))‖ ≤ 1 := by
      split_ifs <;> norm_num
    calc ‖sa12w2_Q L G w‖ = ‖((if ‖(Torus.mk w : Torus d)‖ ≤ 1 / 4 then (1 : ℝ) else 0) -
          (if ‖L • w‖ ≤ 1 / 4 then (1 : ℝ) else 0))‖ * ‖G (Torus.mk w)‖ := norm_smul _ _
      _ ≤ 1 * (C * (‖(Torus.mk w : Torus d)‖ ^ (-s - 1) + 1)) := by gcongr
      _ ≤ C * (δ ^ (-s - 1) + 1) := by rw [one_mul]; gcongr

end HRS.PDE.SA12W2
