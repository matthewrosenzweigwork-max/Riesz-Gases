import HRS.MS.CovMeasAux25

/-!
# S10.1 (worker S101B), part 26: evaluation of the push-forward measure (`IsR2JValue` integral)
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

variable (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ, IsR2DualCombo m φ →
    IsR2DualCombo m ψ → propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)

include hlin in
theorem s101_Dm_eval_ae (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) T)
    {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) T) (htb : tb ∈ Icc (0 : ℝ) T) (hρa : ρ < ta) (hρb : ρ < tb)
    (Sa Sb : Finset (MultiIndex d)) (ca cb : MultiIndex d → ℝ) :
    s101D C m T z ρ (s101Pc m T ta Sa ca + s101Qc m T Sa ca) (s101Pc m T tb Sb cb + s101Qc m T Sb cb) =
      2 * C.ν * z ρ (fun x => inner ℝ
        (gradient (propagatorW C ρ ta (fun x => ∑ α ∈ Sa, ca α * oscTestFun m α x)) x)
        (gradient (propagatorW C ρ tb (fun x => ∑ α ∈ Sb, cb α * oscTestFun m α x)) x)) := by
  obtain ⟨c, hD⟩ := s101_data_of_horb A.hd A.horb
  have hΓ := s101_Gamma_diff A hρ
  have hu : ∀ x, inner ℝ (s101Gamma C m T ρ x) (s101Pc m T ta Sa ca + s101Qc m T Sa ca) =
      propagatorW C ρ ta (fun x => ∑ α ∈ Sa, ca α * oscTestFun m α x) x := by
    intro x
    rw [inner_add_right, s101g_Pc hlin hD hρ hta Sa ca x, s101g_Qc hlin hD hρ Sa ca x, if_pos hρa]
    ring
  have hv : ∀ x, inner ℝ (s101Gamma C m T ρ x) (s101Pc m T tb Sb cb + s101Qc m T Sb cb) =
      propagatorW C ρ tb (fun x => ∑ α ∈ Sb, cb α * oscTestFun m α x) x := by
    intro x
    rw [inner_add_right, s101g_Pc hlin hD hρ htb Sb cb x, s101g_Qc hlin hD hρ Sb cb x, if_pos hρb]
    ring
  rw [s101_D_apply A hρ, s101_Fm_Rk_eq_inner hΓ hu hv]

include hlin in
theorem s101_Jx_eval (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) (htr : S101Tr C m T z) {C0 : ℝ}
    {J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T)))}
    (hJ : S101Jprops T C0 J) {I : Set ℝ} (hI : MeasurableSet I) {ta tb : ℝ}
    (hta : ta ∈ Icc (0 : ℝ) T) (htb : tb ∈ Icc (0 : ℝ) T)
    (Sa Sb : Finset (MultiIndex d)) (ca cb : MultiIndex d → ℝ) (l₁ l₂ : StrongDual ℝ (OscPath d m T))
    (h₁ : ∀ w, l₁ w = OscDual.eval (r2PathAt w ta) (fun x => ∑ α ∈ Sa, ca α * oscTestFun m α x))
    (h₂ : ∀ w, l₂ w = OscDual.eval (r2PathAt w tb) (fun x => ∑ α ∈ Sb, cb α * oscTestFun m α x)) :
    s101Jx hT J (s101Dm C m T z) I
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      2 * C.ν * ∫ r in I ∩ Icc 0 (min ta tb), z r (fun x => inner ℝ
        (gradient (propagatorW C r ta (fun x => ∑ α ∈ Sa, ca α * oscTestFun m α x)) x)
        (gradient (propagatorW C r tb (fun x => ∑ α ∈ Sb, cb α * oscTestFun m α x)) x)) := by
  have hTD := s101_Dm_isTraceDensity A hT htr
  set Pa := s101Pc m T ta Sa ca with hPa
  set Qa := s101Qc m T Sa ca with hQa
  set Pb := s101Pc m T tb Sb cb with hPb
  set Qb := s101Qc m T Sb cb with hQb
  have e1 := s101_Jx_four hT hJ hTD hI hta htb Pa Qa Pb Qb l₁ l₂
    (fun y => by rw [h₁]; exact s101_recon_eval hT y hta Sa ca)
    (fun y => by rw [h₂]; exact s101_recon_eval hT y htb Sb cb)
  rw [e1]
  set S : Set ℝ := I ∩ Icc 0 (min ta tb) with hS
  have hSm : MeasurableSet S := hI.inter measurableSet_Icc
  have hmta : min ta tb ≤ ta := min_le_left _ _
  have hmtb : min ta tb ≤ tb := min_le_right _ _
  have hS_sub : S ⊆ Icc 0 T := fun r hr => ⟨hr.2.1, hr.2.2.trans (hmta.trans hta.2)⟩
  have t1 : ∫ r in I ∩ Icc 0 T, s101Dm C m T z r Pa Pb = ∫ r in S, s101Dm C m T z r Pa Pb := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.inter measurableSet_Icc) ?_ ?_
    · intro r hr; exact ⟨hr.1, hr.2.1, hr.2.2.trans (hmta.trans hta.2)⟩
    · intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := hr.1.2
      have : min ta tb < r := by
        by_contra hle; exact hr.2 ⟨hr.1.1, hr.1.2.1, not_lt.1 hle⟩
      rcases min_lt_iff.1 this with h | h
      · exact s101_Dm_Pc_zero hlin A hT hrT hta h.le Sa ca _
      · exact s101_Dm_Pc_zero' hlin A hT hrT htb h.le Sb cb _
  have t2 : ∫ r in I ∩ Icc 0 tb, s101Dm C m T z r Pa Qb = ∫ r in S, s101Dm C m T z r Pa Qb := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.inter measurableSet_Icc) ?_ ?_
    · intro r hr; exact ⟨hr.1, hr.2.1, hr.2.2.trans hmtb⟩
    · intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.2.1, hr.1.2.2.trans htb.2⟩
      have : min ta tb < r := by
        by_contra hle; exact hr.2 ⟨hr.1.1, hr.1.2.1, not_lt.1 hle⟩
      rcases min_lt_iff.1 this with h | h
      · exact s101_Dm_Pc_zero hlin A hT hrT hta h.le Sa ca _
      · exact absurd hr.1.2.2 (not_le.2 h)
  have t3 : ∫ r in I ∩ Icc 0 ta, s101Dm C m T z r Qa Pb = ∫ r in S, s101Dm C m T z r Qa Pb := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.inter measurableSet_Icc) ?_ ?_
    · intro r hr; exact ⟨hr.1, hr.2.1, hr.2.2.trans hmta⟩
    · intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.2.1, hr.1.2.2.trans hta.2⟩
      have : min ta tb < r := by
        by_contra hle; exact hr.2 ⟨hr.1.1, hr.1.2.1, not_lt.1 hle⟩
      rcases min_lt_iff.1 this with h | h
      · exact absurd hr.1.2.2 (not_le.2 h)
      · exact s101_Dm_Pc_zero' hlin A hT hrT htb h.le Sb cb _
  rw [t1, t2, t3]
  have hint : ∀ u v, IntegrableOn (fun r => s101Dm C m T z r u v) S := fun u v =>
    (s101_Dm_entry_integrable A hT htr u v).mono_set hS_sub
  have i12 : IntegrableOn (fun r => s101Dm C m T z r Pa Pb + s101Dm C m T z r Pa Qb) S :=
    (hint Pa Pb).add (hint Pa Qb)
  have i123 : IntegrableOn (fun r => s101Dm C m T z r Pa Pb + s101Dm C m T z r Pa Qb +
      s101Dm C m T z r Qa Pb) S := i12.add (hint Qa Pb)
  rw [← integral_add (hint Pa Pb) (hint Pa Qb), ← integral_add i12 (hint Qa Pb),
    ← integral_add i123 (hint Qa Qb)]
  have hpt : ∀ r, s101Dm C m T z r Pa Pb + s101Dm C m T z r Pa Qb + s101Dm C m T z r Qa Pb +
      s101Dm C m T z r Qa Qb = s101Dm C m T z r (Pa + Qa) (Pb + Qb) := by
    intro r; simp only [map_add, ContinuousLinearMap.add_apply]; ring
  simp_rw [hpt]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  have hne : ∀ᵐ r ∂(volume.restrict S), r ≠ min ta tb := by
    refine ae_restrict_of_ae ?_
    have := measure_eq_zero_iff_ae_notMem.1 (measure_singleton (min ta tb) : (volume : Measure ℝ) {min ta tb} = 0)
    exact this.mono fun r hr => by simpa using hr
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hS_sub (s101_Dm_ae_eq A hT), ae_restrict_mem hSm, hne]
    with ρ hDm hρS hne'
  have hρT : ρ ∈ Icc (0 : ℝ) T := hS_sub hρS
  have hlt : ρ < min ta tb := lt_of_le_of_ne hρS.2.2 hne'
  have := s101_Dm_eval_ae hlin A hT hρT hta htb (lt_of_lt_of_le hlt hmta) (lt_of_lt_of_le hlt hmtb) Sa Sb ca cb
  show s101Dm C m T z ρ (Pa + Qa) (Pb + Qb) = _
  rw [hDm]
  exact this

end HRS.MS.CovMeas
