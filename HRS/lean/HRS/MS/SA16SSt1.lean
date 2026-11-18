import HRS.MS.SA16SNl4

/-!
# S.A.16 (SA16S) St1: the strong form of the Duhamel solution (packet P7, step 1)

`sa16sx_eq_of_ell`: elements of `WmpSpace` with equal pairings against all `C_c^∞` tests are equal.
`sa16sx_strong`: the mild solution `u ∈ C([0,T]; W^{m+2,p})` of `sa16r_fixedn_mild` satisfies, as an identity in `W^{m,p}`,
`u(τ) = φ + ∫_0^τ (νΔ u(r) + K_r u(r)) dr` (`sa16sx_f` is the integrand), hence `u ∈ C^1((0,T); W^{m,p})`
(`sa16sx_hasDerivAt`) with `u' = νΔu + K u`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section St1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16sx_loc (k : ℕ) (Z : WmpSpace d k p) : LocallyIntegrable (wrep d k p Z) volume := by
  have hP : MemLp (wrep d k p Z) (ENNReal.ofReal p) volume := by
    have hD' := Lp.memLp (Z : WLp d k p)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d k => ℝ) (wZero d k)).comp_memLp' hD'
  refine hP.locallyIntegrable ?_
  have : (1 : ℝ) ≤ p := by linarith [Fact.out (p := 2 ≤ p)]
  simpa using ENNReal.ofReal_le_ofReal this

lemma sa16sx_eq_of_ell (k : ℕ) (X Y : WmpSpace d k p)
    (h : ∀ {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ), sa16r_ell d k p hψ X = sa16r_ell d k p hψ Y) : X = Y := by
  refine sa16r_wrep_inj d k p _ _ ?_
  refine ae_eq_of_integral_contDiff_smul_eq (sa16sx_loc k X) (sa16sx_loc k Y) (fun g hg hgs => ?_)
  have hgg : IsCcInfty g := ⟨hg, hgs⟩
  have := h hgg
  rw [sa16r_ell_apply hgg k X, sa16r_ell_apply hgg k Y] at this
  simpa [smul_eq_mul, mul_comm] using this

/-- the integrand of the strong form -/
def sa16sx_f (m : ℕ) (ν : ℝ) (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (u : ℝ → WmpSpace d (m + 1 + 1) p) (r : ℝ) : WmpSpace d m p :=
  ν • sa16so_Lap d m p (u r) + sa16r_iota d m p (K r (u r))

lemma sa16sx_f_cont {m : ℕ} {ν T B : ℝ} {K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p}
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ B) (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T))
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T)) :
    ContinuousOn (sa16sx_f m ν K u) (Icc 0 T) := by
  unfold sa16sx_f
  refine ContinuousOn.add ?_ ?_
  · exact ((sa16so_Lap d m p).continuous.comp_continuousOn hu).const_smul ν
  · refine (sa16r_iota d m p).continuous.comp_continuousOn ?_
    intro a ha
    exact sa16r_clm_apply_strong (S := Icc 0 T) (B := B) (fun v => hKc v a ha)
      (eventually_nhdsWithin_of_forall fun q hq => hKb q hq) (hu a ha)

theorem sa16sx_strong {m : ℕ} {ν T B : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ B) (hB : 0 ≤ B)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, sa16r_iota d m p (sa16r_iota d (m + 1) p (u τ)) =
      sa16r_iota d m p (sa16r_iota d (m + 1) p φ) + ∫ r in (0 : ℝ)..τ, sa16sx_f m ν K u r := by
  intro τ hτ
  have hfc := sa16sx_f_cont (ν := ν) hKb hKc hu
  have hii : IntervalIntegrable (sa16sx_f m ν K u) volume 0 τ :=
    (hfc.mono (Icc_subset_Icc le_rfl hτ.2)).intervalIntegrable_of_Icc hτ.1
  refine sa16sx_eq_of_ell m _ _ (fun {ψ} hψ => ?_)
  have hW := sa16r_fixedn_weak hν hT hB (m + 1) K hKb hKc φ hψ (sa16sw_cc_lap hψ)
    (sa16sw_heatWeak hν T (m + 1) hψ) hu hsol τ hτ
  rw [map_add, sa16r_ell_iota, sa16r_ell_iota, sa16r_ell_iota, sa16r_ell_iota, hW]
  congr 1
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hii]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  simp only [sa16sx_f, map_add, map_smul, smul_eq_mul]
  rw [sa16so_ell_Lap m hψ, sa16r_ell_iota]

theorem sa16sx_hasDerivAt {m : ℕ} {ν T B : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ B) (hB : 0 ≤ B)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ) {τ : ℝ} (hτ : τ ∈ Ioo 0 T) :
    HasDerivAt (fun r => sa16r_iota d m p (sa16r_iota d (m + 1) p (u r))) (sa16sx_f m ν K u τ) τ := by
  have hstrong := sa16sx_strong hν hT K hKb hB hKc φ hu hsol
  have hfc := sa16sx_f_cont (ν := ν) hKb hKc hu
  have hint : IntervalIntegrable (sa16sx_f m ν K u) volume 0 τ :=
    (hfc.mono (Icc_subset_Icc le_rfl hτ.2.le)).intervalIntegrable_of_Icc hτ.1.le
  have hcont : ContinuousAt (sa16sx_f m ν K u) τ :=
    hfc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
  have hmeas : StronglyMeasurableAtFilter (sa16sx_f m ν K u) (𝓝 τ) volume :=
    (hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ
  have h1 := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have h2 := h1.const_add (sa16r_iota d m p (sa16r_iota d (m + 1) p φ))
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with r hr
  exact hstrong r hr

end St1

end HRS.Whole.AppendixA.Phase2SA16R
