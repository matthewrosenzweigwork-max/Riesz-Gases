import HRS.MC.S7FCD5B
import HRS.MC.S7FCD4
import HRS.MC.S7FCF5IE2
import HRS.MC.L2C0

/-!
# Packet fcf5p, D5: `s7_FC_D5_mean_proof` (proof of `s7_FC_D5_mean`, statement copied verbatim from
`HRS/MC/S7FCPlan.lean:219`).  Sorry-free; imports no sorried module.

Route (see `S7FCD5B.lean`): `m N := D_N` (the deterministic mean window, a continuous path for `N ≥ 1`),
`ζ_N = η_N - m_N` a.s. (for `N ≥ 2`, in fact for `N ≥ 1`), and `‖m_N‖ ≤ W_2` of the window `a = 0` (D4), since the
Gaussian limit has mean zero at every time.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCD5

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- Evaluation at a time `s` is measurable on path space. -/
theorem S7FCD5_evalMeas (r T : ℝ) (s : Set.Icc (0 : ℝ) T) :
    Measurable (fun w : PathSpace d r T => PathSpace.at' w s) := by
  have hevc0 : Continuous (fun f : C(Set.Icc (0 : ℝ) T, NegSobolev d r) => f s) := continuous_eval_const s
  have hevc : Continuous (fun w : PathSpace d r T => PathSpace.at' w s) := hevc0
  exact hevc.measurable

/-- The one-time bound: `‖E η_N^s‖ ≤ W_2(Law η_N^{·}, Law η^{·})` at every time `s`, given that the Gaussian side has
mean zero at `s`. -/
theorem S7FCD5_bound_s {Ω : Type} [MeasurableSpace Ω] (R : Regime d) (r T : ℝ) (hdr : (d : ℝ) < 2 * r)
    {N : ℕ} (hN : 1 ≤ N) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hF : AEMeasurable (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ) P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T =>
      etaE r (X (Real.toNNReal (t : ℝ)) ω) (withDensityReal (R.ρ (t : ℝ))))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (η : ℝ → Ω' → NegSobolev d r)
    (s : Set.Icc (0 : ℝ) T)
    (hν : ∫ w, PathSpace.at' w s ∂(law P' (procWin r T 0 η)) = 0) :
    ENNReal.ofReal ‖S7FCD5B.S7FCD5B_D R r P X (s : ℝ)‖ ≤
      wassersteinE 2 (law P (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ)) (law P' (procWin r T 0 η)) := by
  have hevm := S7FCD5_evalMeas (d := d) r T s
  haveI hμP : IsProbabilityMeasure (law P (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ)) :=
    (Measure.isProbabilityMeasure_map_iff hF).2 inferInstance
  have hint : Integrable (fun w : PathSpace d r T => PathSpace.at' w s)
      (law P (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ)) := by
    refine (integrable_map_measure hevm.aestronglyMeasurable hF).2 ?_
    refine (integrable_const (Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))))).mono' ?_ ?_
    · exact (hevm.comp_aemeasurable hF).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => S7FCD5B.S7FCD5B_Y_bound R r T hdr X hN P ω s
  have hmean : ∫ w, PathSpace.at' w s ∂(law P (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ)) =
      S7FCD5B.S7FCD5B_D R r P X (s : ℝ) := by
    rw [integral_map hF hevm.aestronglyMeasurable]
    have hae : (fun ω => PathSpace.at' (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ ω) s) =ᵐ[P]
        (fun ω => etaE r (X (Real.toNNReal (s : ℝ)) ω) (withDensityReal (R.ρ (s : ℝ)))) := by
      filter_upwards [hcont] with ω hω
      rw [S7FCD5B.S7FCD5B_windowFluc_eq]
      exact S7FCD5B.S7FCD5B_toPath_apply r T (fun t ω => etaE r (X (Real.toNNReal t) ω) (withDensityReal (R.ρ t)))
        ω hω s
    exact (integral_congr_ae hae).trans (S7FCD5B.S7FCD5B_mean R r hdr P X hadapt hN (s : ℝ) s.2.1)
  unfold wassersteinE
  refine le_iInf fun π => ?_
  have hc := S7FCD5B.S7FCD5B_eval_coupling r T (law P (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ))
    (law P' (procWin r T 0 η)) s hint π.1 π.2
  rw [hmean, hν, sub_zero] at hc
  exact hc

/-- **D5 (`ζ_N = η_N - m_N` a.s. with a deterministic path `m_N → 0`)**: proof of `s7_FC_D5_mean`. -/
theorem s7_FC_D5_mean_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∃ m : ℕ → PathSpace d r T, Tendsto (fun N => ‖m N‖) atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ᵐ ω ∂(P N), zetaWin r T 0 (P N) (X N) ω =
        HRS.Main.windowFluc r T 0 (Real.sqrt N) (X N) R.ρ ω - m N := by
  have hη2 := hη
  have hdr : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- a.s. continuity of both windows, for each `N ≥ 1`
  have hhon : ∀ N : ℕ, 1 ≤ N →
      (∀ᵐ ω ∂(P N), Continuous fun t : Set.Icc (0 : ℝ) T =>
          etaE r (X N (Real.toNNReal (t : ℝ)) ω) (withDensityReal (R.ρ (t : ℝ)))) ∧
      (∀ᵐ ω ∂(P N), Continuous fun t : Set.Icc (0 : ℝ) T => zetaAt r (P N) (X N) t ω) :=
    fun N hN => S7FCD5B.S7FCD5B_honest R r hr T hN (P N) (X₀ N) (W N) (X N) (hreal N hN)
  have hadapt : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ≥0, Measurable (X N t) :=
    fun N hN => ((hreal N hN).solution 0).adapted
  -- the deterministic paths `m N = D_N`
  have hpath : ∀ N : ℕ, ∃ m : PathSpace d r T, 1 ≤ N → ∀ s : Set.Icc (0 : ℝ) T,
      PathSpace.at' m s = S7FCD5B.S7FCD5B_D R r (P N) (X N) (s : ℝ) := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨h1, h2⟩ := hhon N hN
      obtain ⟨ω0, hω1, hω2⟩ := (h1.and h2).exists
      have hcont : Continuous fun s : Set.Icc (0 : ℝ) T => S7FCD5B.S7FCD5B_D R r (P N) (X N) (s : ℝ) := by
        have heq : (fun s : Set.Icc (0 : ℝ) T => S7FCD5B.S7FCD5B_D R r (P N) (X N) (s : ℝ)) =
            fun s : Set.Icc (0 : ℝ) T => etaE r (X N (Real.toNNReal (s : ℝ)) ω0) (withDensityReal (R.ρ (s : ℝ)))
              - zetaAt r (P N) (X N) (s : ℝ) ω0 := by
          funext s
          rw [S7FCD5B.S7FCD5B_identity R r hdr (P N) (X N) (hadapt N hN) hN (s : ℝ) s.2.1 ω0]
          abel
        rw [heq]
        exact hω1.sub hω2
      let mk : C(Set.Icc (0 : ℝ) T, NegSobolev d r) :=
        ⟨fun s => S7FCD5B.S7FCD5B_D R r (P N) (X N) (s : ℝ), hcont⟩
      exact ⟨mk, fun _ s => rfl⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose m hm using hpath
  -- the Gaussian side: centred at every time
  obtain ⟨Y₀, hY, hLin⟩ := hη
  have hGzero : ∀ s : Set.Icc (0 : ℝ) T, ∫ ω, η (s : ℝ) ω ∂P' = 0 := fun s =>
    S7FCD5A.S7FCD5A_eta_integral_zero P' R.D R.ρ r R.D.invβ (s : ℝ) _ Y₀ η hY (hLin (s : ℝ)) s.2.1
      (fun φ hφ => (HRS.MC.L2C0.l2c0_proof R φ hφ 0 (s : ℝ) le_rfl s.2.1).1)
  have hmη : ∀ t, Measurable (η t) := fun t => (hLin T).meas t
  have hc' : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 T) := (hLin T).cont
  have hν : ∀ s : Set.Icc (0 : ℝ) T, ∫ w, PathSpace.at' w s ∂(law P' (procWin r T 0 η)) = 0 := by
    intro s
    rw [integral_map (S7FCD5B.S7FCD5B_procWin_aemeasurable P' r T hT η hmη hc')
      (S7FCD5_evalMeas (d := d) r T s).aestronglyMeasurable]
    exact (integral_congr_ae ((S7FCD5B.S7FCD5B_procWin_val P' r T η hc').mono fun ω hω => hω s)).trans (hGzero s)
  -- the uniform bound `‖D_N^s‖ ≤ W_2(a = 0)` for `N ≥ 1`
  have hbound : ∀ N : ℕ, 1 ≤ N → ∀ s : Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ‖S7FCD5B.S7FCD5B_D R r (P N) (X N) (s : ℝ)‖ ≤
        wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T 0 (Real.sqrt N) (X N) R.ρ))
          (law P' (procWin r T 0 η)) := by
    intro N hN s
    exact S7FCD5_bound_s R r T hdr hN (P N) (X N) (hadapt N hN)
      (HRS.MC.Sec7.S7FCF5I.fcf5_E2_window_aemeasurable_proof R r hr T hT hN (P N) (X₀ N) (W N) (X N)
        (hreal N hN) 0 le_rfl).1
      (hhon N hN).1 P' η s (hν s)
  -- W_2 → 0 by D4 (window `a = 0`)
  have hD4 := HRS.MC.Sec7.S7FCD4.s7_FC_D4_eta_W2_proof R r hr T hT P X₀ W X hreal P' η hη2
  have hW : Tendsto (fun N : ℕ => wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T 0 (Real.sqrt N) (X N) R.ρ))
      (law P' (procWin r T 0 η))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD4 (fun _ => zero_le) (fun N => ?_)
    exact le_iSup (fun a : {a : ℝ // 0 ≤ a} =>
      wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T a.1 (Real.sqrt N) (X N) R.ρ))
        (law P' (procWin r T a.1 η))) ⟨0, le_rfl⟩
  refine ⟨m, ?_, ?_⟩
  · have hWr : Tendsto (fun N : ℕ => (wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T 0 (Real.sqrt N) (X N) R.ρ))
        (law P' (procWin r T 0 η))).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW
      rw [ENNReal.toReal_zero] at h
      exact h
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hWr
    filter_upwards [eventually_ge_atTop 1, hW.eventually (Iio_mem_nhds zero_lt_one)] with N hN1 hlt
    have hne := ne_top_of_lt hlt
    refine (ContinuousMap.norm_le (show C(Set.Icc (0 : ℝ) T, NegSobolev d r) from m N)
      ENNReal.toReal_nonneg).2 ?_
    intro s
    show ‖PathSpace.at' (m N) s‖ ≤ _
    rw [hm N hN1 s]
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 (hbound N hN1 s)
  · intro N hN2
    have hN : 1 ≤ N := by omega
    obtain ⟨h1, h2⟩ := hhon N hN
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [S7FCD5B.S7FCD5B_zetaWin_eq, S7FCD5B.S7FCD5B_windowFluc_eq]
    apply S7FCD5B.S7FCD5B_path_ext
    intro s
    have hL : PathSpace.at' (toPath r T (fun t ω => zetaAt r (P N) (X N) t ω) ω) s = zetaAt r (P N) (X N) (s : ℝ) ω :=
      S7FCD5B.S7FCD5B_toPath_apply r T (fun t ω => zetaAt r (P N) (X N) t ω) ω hω2 s
    have hR : PathSpace.at' (toPath r T (fun t ω => etaE r (X N (Real.toNNReal t) ω) (withDensityReal (R.ρ t))) ω) s =
        etaE r (X N (Real.toNNReal (s : ℝ)) ω) (withDensityReal (R.ρ (s : ℝ))) :=
      S7FCD5B.S7FCD5B_toPath_apply r T (fun t ω => etaE r (X N (Real.toNNReal t) ω) (withDensityReal (R.ρ t))) ω hω1 s
    have hsub : PathSpace.at' (toPath r T (fun t ω => etaE r (X N (Real.toNNReal t) ω) (withDensityReal (R.ρ t))) ω
        - m N) s = PathSpace.at' (toPath r T (fun t ω => etaE r (X N (Real.toNNReal t) ω) (withDensityReal (R.ρ t))) ω) s
          - PathSpace.at' (m N) s := rfl
    rw [hL, hsub, hR, hm N hN s, S7FCD5B.S7FCD5B_identity R r hdr (P N) (X N) (hadapt N hN) hN (s : ℝ) s.2.1 ω]
    abel

end HRS.MC.Sec7.S7FCD5

end
