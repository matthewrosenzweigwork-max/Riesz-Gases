import HRS.MC.CepP3Aux7

/-!
# Packet P3, Aux8: the distributional equation of the periodic lift (Proposition B.3 in covering form)
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp

theorem exists_supp {F : ℝ × (Fin N → Euc d) → ℝ} (hFc : HasCompactSupport F) :
    ∃ R, Supp R F := by
  obtain ⟨R, hR⟩ := hFc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun q hq => ?_⟩
  by_contra h
  have : q ∈ tsupport F := subset_tsupport _ h
  have := hR this
  rw [mem_closedBall_zero_iff] at this
  linarith

theorem exists_time_bound {F : ℝ × (Fin N → Euc d) → ℝ} {T : ℝ} (hT : 0 < T)
    (hFc : HasCompactSupport F) (hFO : tsupport F ⊆ Ioo 0 T ×ˢ liftedFree d N) :
    ∃ b < T, ∀ p ∈ tsupport F, p.1 ≤ b := by
  rcases (tsupport F).eq_empty_or_nonempty with h | h
  · exact ⟨0, hT, fun p hp => by simp [h] at hp⟩
  · obtain ⟨p, hp, hmax⟩ := hFc.isCompact.exists_isMaxOn h continuous_fst.continuousOn
    exact ⟨p.1, (hFO hp).1.2, fun q hq => isMaxOn_iff.1 hmax q hq⟩

theorem F_eq_zero_of_notMem {F : ℝ × (Fin N → Euc d) → ℝ} {p : ℝ × (Fin N → Euc d)}
    (h : p ∉ tsupport F) : F p = 0 := image_eq_zero_of_notMem_tsupport h

theorem per_eq_zero {F : ℝ × (Fin N → Euc d) → ℝ} {p : ℝ × (Fin N → Euc d)}
    (h : ∀ w : Fin N → Lattice d, tau w p ∉ tsupport F) : per F p = 0 := by
  unfold per
  exact finsum_eq_zero_of_forall_eq_zero fun w => F_eq_zero_of_notMem (h w)

theorem PhiOf_time_zero {F : ℝ × (Fin N → Euc d) → ℝ} {T : ℝ} (hFO : tsupport F ⊆ Ioo 0 T ×ˢ liftedFree d N)
    (x : Config d N) : PhiOf (per F) 0 x = 0 := by
  refine per_eq_zero fun w hw => ?_
  have := (hFO hw).1
  simp [tau] at this

theorem isFKETest_PhiOf {F : ℝ × (Fin N → Euc d) → ℝ} {T : ℝ} (hT : 0 < T)
    (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFO : tsupport F ⊆ Ioo 0 T ×ˢ liftedFree d N) :
    IsFKETest T (PhiOf (per F)) := by
  obtain ⟨R, hR⟩ := exists_supp hFc
  have hcd : ContDiff ℝ ∞ (per F) := contDiff_per hFs hR
  have hper : ∀ (w : Fin N → Lattice d) p, per F (tau w p) = per F p := fun w p => per_tau F w p
  refine ⟨?_, ?_, ?_⟩
  · have hl : configLift (PhiOf (per F)) = fun r Y => per F (r, Y) :=
      funext fun r => funext fun Y => configLift_PhiOf (per F) hper r Y
    rw [hl]
    exact IsC12On.of_contDiff T univ _ (hcd.of_le two_le_infty)
  · obtain ⟨b, hb, hbd⟩ := exists_time_bound hT hFc hFO
    refine ⟨(b + T) / 2, by linarith, fun r hr x => ?_⟩
    refine per_eq_zero fun w hw => ?_
    have := hbd _ hw
    simp only [tau] at this
    linarith
  · refine ⟨mkC '' (Prod.snd '' tsupport F), (hFc.isCompact.image continuous_snd).image continuous_mkC,
      ?_, fun r x hx => ?_⟩
    · rw [Set.disjoint_left]
      rintro x ⟨Y, ⟨p, hp, rfl⟩, rfl⟩
      exact (hFO hp).2
    · refine per_eq_zero fun w hw => ?_
      apply hx
      refine ⟨_, ⟨_, hw, rfl⟩, ?_⟩
      show mkC (repC x + lat w) = x
      rw [mkC_add_lat]
      exact mk_repC x

end HRS.MC.CepP3
