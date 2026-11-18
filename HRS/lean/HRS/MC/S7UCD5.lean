import HRS.MC.S7UCD5A

/-!
# Packet ucD, D5: `s7_UC_D5_mean_window_proof` (statement copied verbatim from `HRS/MC/S7UCPlan.lean`)

Sorry-free; imports no sorried module.  The window-`a` version of `S7FCD5.lean:s7_FC_D5_mean_proof`: the deterministic mean path
is `m = (s ↦ D_N^{a+s})` (`S7FCD5B_D`), with `η_N^{a+s} = ζ_N^{a+s} + D_N^{a+s}` pointwise (`S7FCD5B_identity`), and
`‖D_N^{a+s}‖ ≤ W_2(Law windowFluc^a, Law procWin^a)` from the coupling bound and the mean-zero Gaussian limit.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCD

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4

variable {d : ℕ}

/-- **UC-D5 (the mean shift at window `a`)**: proof of `s7_UC_D5_mean_window`. -/
theorem s7_UC_D5_mean_window_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → ∃ m : PathSpace d r T,
      ENNReal.ofReal ‖m‖ ≤ wassersteinE 2
        (law (P N) (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ)) (law P' (procWin r T a η)) ∧
      ∀ᵐ ω ∂(P N), zetaWin r T a (P N) (X N) ω =
        HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ ω - m := by
  intro a ha N hN2
  have hN : 1 ≤ N := by omega
  have hdr : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨h1, h2⟩ := S7UCD_honest R r hr T hN (P N) (X₀ N) (W N) (X N) (hreal N hN) a ha
  have hadapt : ∀ t : ℝ≥0, Measurable (X N t) := ((hreal N hN).solution 0).adapted
  -- the deterministic path `s ↦ D_N^{a+s}`
  obtain ⟨ω0, hω1, hω2⟩ := (h1.and h2).exists
  have hcont : Continuous fun s : Set.Icc (0 : ℝ) T => S7FCD5B.S7FCD5B_D R r (P N) (X N) (a + (s : ℝ)) := by
    have heq : (fun s : Set.Icc (0 : ℝ) T => S7FCD5B.S7FCD5B_D R r (P N) (X N) (a + (s : ℝ))) =
        fun s : Set.Icc (0 : ℝ) T =>
          etaE r (X N (a + (s : ℝ)).toNNReal ω0) (withDensityReal (R.ρ (a + (s : ℝ))))
            - zetaAt r (P N) (X N) (a + (s : ℝ)) ω0 := by
      funext s
      rw [S7FCD5B.S7FCD5B_identity R r hdr (P N) (X N) hadapt hN (a + (s : ℝ)) (add_nonneg ha s.2.1) ω0]
      abel
    rw [heq]
    exact hω1.sub hω2
  let mk : PathSpace d r T :=
    ⟨fun s => S7FCD5B.S7FCD5B_D R r (P N) (X N) (a + (s : ℝ)), hcont⟩
  -- the Gaussian side: centred at every time
  obtain ⟨Y₀, hY, hLin⟩ := hη
  have hGzero : ∀ s : Set.Icc (0 : ℝ) T, ∫ ω, η (a + (s : ℝ)) ω ∂P' = 0 := fun s =>
    S7FCD5A.S7FCD5A_eta_integral_zero P' R.D R.ρ r R.D.invβ (a + (s : ℝ)) _ Y₀ η hY (hLin (a + (s : ℝ)))
      (add_nonneg ha s.2.1)
      (fun φ hφ => (HRS.MC.L2C0.l2c0_proof R φ hφ 0 (a + (s : ℝ)) le_rfl (add_nonneg ha s.2.1)).1)
  have hmη : ∀ t, Measurable (η t) := fun t => (hLin (a + T)).meas t
  have hc' : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T)) := (hLin (a + T)).cont
  have hν : ∀ s : Set.Icc (0 : ℝ) T, ∫ w, PathSpace.at' w s ∂(law P' (procWin r T a η)) = 0 := by
    intro s
    rw [integral_map (S7UCD_procWin_aemeasurable P' r T hT a ha η hmη hc')
      (HRS.MC.Sec7.S7FCD5.S7FCD5_evalMeas (d := d) r T s).aestronglyMeasurable]
    exact (integral_congr_ae ((S7UCD_procWin_val P' r T a ha η hc').mono fun ω hω => hω s)).trans (hGzero s)
  have hbound : ∀ s : Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ‖S7FCD5B.S7FCD5B_D R r (P N) (X N) (a + (s : ℝ))‖ ≤
        wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ))
          (law P' (procWin r T a η)) := by
    intro s
    exact S7UCD_bound_s R r T hdr hN (P N) (X N) hadapt a ha
      (HRS.MC.Sec7.S7FCF5I.fcf5_E2_window_aemeasurable_proof R r hr T hT hN (P N) (X₀ N) (W N) (X N)
        (hreal N hN) a ha).1 h1 P' η s (hν s)
  refine ⟨mk, ?_, ?_⟩
  · by_cases hW : wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ))
        (law P' (procWin r T a η)) = ⊤
    · rw [hW]
      exact le_top
    · rw [ENNReal.ofReal_le_iff_le_toReal hW]
      refine (ContinuousMap.norm_le (show C(Set.Icc (0 : ℝ) T, NegSobolev d r) from mk) ENNReal.toReal_nonneg).2 ?_
      intro s
      show ‖S7FCD5B.S7FCD5B_D R r (P N) (X N) (a + (s : ℝ))‖ ≤ _
      exact (ENNReal.ofReal_le_iff_le_toReal hW).1 (hbound s)
  · filter_upwards [h1, h2] with ω hω1 hω2
    rw [S7UCD_zetaWin_eq, S7UCD_windowFluc_eq R r T (X N) a ha]
    apply S7FCD5B.S7FCD5B_path_ext
    intro s
    have hL : PathSpace.at' (toPath r T (fun t ω => zetaAt r (P N) (X N) (a + t) ω) ω) s =
        zetaAt r (P N) (X N) (a + (s : ℝ)) ω :=
      S7FCD5B.S7FCD5B_toPath_apply r T (fun t ω => zetaAt r (P N) (X N) (a + t) ω) ω hω2 s
    have hR : PathSpace.at' (toPath r T
        (fun t ω => etaE r (X N (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω) s =
        etaE r (X N (a + (s : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + (s : ℝ)))) :=
      S7FCD5B.S7FCD5B_toPath_apply r T
        (fun t ω => etaE r (X N (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω hω1 s
    have hsub : PathSpace.at' (toPath r T
        (fun t ω => etaE r (X N (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω - mk) s =
        PathSpace.at' (toPath r T
          (fun t ω => etaE r (X N (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω) s
          - PathSpace.at' mk s := rfl
    rw [hL, hsub, hR]
    show _ = _ - S7FCD5B.S7FCD5B_D R r (P N) (X N) (a + (s : ℝ))
    rw [S7FCD5B.S7FCD5B_identity R r hdr (P N) (X N) hadapt hN (a + (s : ℝ)) (add_nonneg ha s.2.1) ω]
    abel

end HRS.MC.Sec7.S7UCD

end
