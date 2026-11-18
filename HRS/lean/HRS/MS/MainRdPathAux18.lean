import HRS.MS.MainRdPathAux17

/-!
# S.A.9, packet P3l: the Parseval frame of `H^{-q}` and from tails for large `N` to tails for all `N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdInit

variable {d : ℕ}

/-- The coordinate functionals of the Parseval system `h`. -/
def sa9_cH (q : ℕ) (h : ℕ → mhn_Hc d) (ℓ : ℕ) : HNeg d (q : ℝ) →L[ℝ] ℝ :=
  innerSL ℝ (mhn_rep (q : ℝ) (h ℓ))

theorem sa9_cH_parseval {q : ℕ} (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d (q : ℝ), HasSum (fun n => (inner ℝ (mhn_rep (q : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2)) :
    Sa9Parseval (sa9_cH q h) := fun F => by simpa [sa9_cH] using hP F

theorem sa9_cH_apply (q : ℕ) (h : ℕ → mhn_Hc d) (ℓ : ℕ) (F : HNeg d (q : ℝ)) :
    sa9_cH q h ℓ F = HNeg.pairing (mhn_phi (h ℓ)) F := by
  simp only [sa9_cH, innerSL_apply_apply]
  rw [mhn_pairing_phi, real_inner_comm]

section Tails

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] {c : ℕ → H →L[ℝ] ℝ}

theorem sa9_ofReal_tail (hc : Sa9Parseval c) (Lc : ℕ) (F : H) :
    ENNReal.ofReal (sa9_tail c Lc F) = ∑' l, ENNReal.ofReal ((c (l + Lc) F) ^ 2) := by
  rw [sa9_tail_eq hc, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    ((summable_nat_add_iff Lc).2 (hc F).summable)]

theorem sa9_tail_anti (hc : Sa9Parseval c) {L L' : ℕ} (hLL : L ≤ L') (x : H) :
    sa9_tail c L' x ≤ sa9_tail c L x := by
  unfold sa9_tail
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun ℓ => (c ℓ x) ^ 2)
    (Finset.range_mono hLL) (fun _ _ _ => sq_nonneg _)
  linarith

theorem sa9_tail_le_norm (hc : Sa9Parseval c) (L : ℕ) (x : H) : sa9_tail c L x ≤ ‖x‖ ^ 2 := by
  unfold sa9_tail
  have : 0 ≤ ∑ ℓ ∈ Finset.range L, (c ℓ x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem sa9_tail_tendsto (hc : Sa9Parseval c) (x : H) :
    Tendsto (fun L => ENNReal.ofReal (sa9_tail c L x)) atTop (𝓝 0) := by
  simp_rw [sa9_ofReal_tail hc]
  refine ENNReal.tendsto_sum_nat_add (fun l => ENNReal.ofReal ((c l x) ^ 2)) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hc x).summable, (hc x).tsum_eq]
  exact ENNReal.ofReal_ne_top

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]

theorem sa9_tails_all (hc : Sa9Parseval c) (J : Set ℕ) (F : ∀ N, Ω N → H) (hF : ∀ N ∈ J, Measurable (F N))
    (hfin : ∀ N ∈ J, ∫⁻ ζ, ENNReal.ofReal (‖F N ζ‖ ^ 2) ∂(P N) ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → ∃ Lc N₀ : ℕ, ∀ N ∈ J, N₀ ≤ N →
      ∫⁻ ζ, ENNReal.ofReal (sa9_tail c Lc (F N ζ)) ∂(P N) ≤ ENNReal.ofReal η) :
    ∀ η : ℝ, 0 < η → ∃ Lc : ℕ, ∀ N ∈ J,
      ∫⁻ ζ, ENNReal.ofReal (sa9_tail c Lc (F N ζ)) ∂(P N) ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨Lc₁, N₀, h1⟩ := h η hη
  have hηpos : (0 : ℝ≥0∞) < ENNReal.ofReal η := ENNReal.ofReal_pos.2 hη
  have hev : ∀ N ∈ J ∩ Set.Iio N₀, ∀ᶠ L in atTop,
      ∫⁻ ζ, ENNReal.ofReal (sa9_tail c L (F N ζ)) ∂(P N) ≤ ENNReal.ofReal η := by
    intro N hN
    have := tendsto_lintegral_of_dominated_convergence (μ := P N)
      (F := fun L ζ => ENNReal.ofReal (sa9_tail c L (F N ζ))) (f := fun _ => (0 : ℝ≥0∞))
      (fun ζ => ENNReal.ofReal (‖F N ζ‖ ^ 2))
      (fun L => ENNReal.measurable_ofReal.comp ((sa9_tail_continuous L).measurable.comp (hF N hN.1)))
      (fun L => Eventually.of_forall fun ζ => ENNReal.ofReal_le_ofReal (sa9_tail_le_norm hc L _))
      (hfin N hN.1) (Eventually.of_forall fun ζ => sa9_tail_tendsto hc _)
    simp only [lintegral_zero] at this
    exact (this.eventually (gt_mem_nhds hηpos)).mono fun L hL => hL.le
  have hfinite : (J ∩ Set.Iio N₀).Finite := (Set.finite_Iio N₀).subset Set.inter_subset_right
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 ((hfinite.eventually_all).2 hev)
  refine ⟨max Lc₁ L₂, fun N hN => ?_⟩
  by_cases hNN : N₀ ≤ N
  · refine le_trans (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal
      (sa9_tail_anti hc (le_max_left Lc₁ L₂) _)) (h1 N hN hNN)
  · exact hL₂ (max Lc₁ L₂) (le_max_right _ _) N ⟨hN, not_le.1 hNN⟩

end Tails

end HRS.MS.MainRdPath
