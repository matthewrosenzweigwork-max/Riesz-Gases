import HRS.MS.R2GenInitAux32

/-!
# S10.5 window comparison, packet D4: the law of the linear window process is that of `c + 𝒯G`

`s105_D_law`, `s105_FArr_range`, `s105_D_range`, `s105_Y_array_law`, `s105_Yc_law`: the law of the window `Y_{N,b}` of the linear fluctuation
process equals the law of `s56Ext (g c'') + (𝒯 G_b)` for a measurable path-extension `g`, a copy `c''` of the initial array independent of the
Gaussian window martingale `G` (window analogues of `GenPathAux56-58`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.Uniform.Q54c

variable {d : ℕ}

theorem s105_pw_eq (m T b : ℝ) {Ω : Type*} (Y : ℝ → Ω → OscDual d m) :
    processWindow m T b Y = fun ζ => windowPathOf m T 0 (fun t => Y (b + t) ζ) := by
  funext ζ
  unfold processWindow windowPathOf
  exact HRS.GF.dite_continuousMap_congr _ _ (funext fun t => by simp)

theorem s105_D_law {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q) [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)]
    {Ω Ω₂ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) [IsProbabilityMeasure P] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) q (b + T) η₀ Y)
    (s' : ℕ → Set.Icc (0 : ℝ) T)
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P)
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (b + T) G (fun r _ =>
      s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) q hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t)) :
    P.map (fun ζ i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ i -
        s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) =
      P₂.map (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G) := by
  have hFm : Measurable (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G) :=
    measurable_pi_iff.2 fun i => (hGm _).inner measurable_const
  have hD : AEMeasurable (fun ζ i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ i -
      s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P :=
    aemeasurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (s56_Psi0_meas s' (fun t ζ => Y (b + t) ζ) (fun t => hYm (b + t)))).aemeasurable.sub
        (hη i)
  refine s56_seq_law_eq P P₂ _ _ hD hFm.aemeasurable fun p f hf => ?_
  obtain ⟨-, hlaw⟩ := s105_VD_law _ ((wholeSpaceIndex d : ℕ) : ℝ) b q T P η₀ Y hb hY s' f
  refine hlaw.trans ?_
  exact (s105_Gb_fdd hS hb hT q hq hG hGc hGz hGm (fun a => (s' (f a).1 : ℝ)) (fun a => (s' (f a).1).2)
    (fun a => (f a).2)).symm

theorem s105_FArr_range {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b)
    (q : ℝ) (hq : 0 ≤ q) [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ =>
      s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) q hq r))
    (s' : ℕ → Set.Icc (0 : ℝ) T) :
    ∀ᵐ ζ ∂P, s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ = fun i =>
      OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ (s' i.1)) i.2 := by
  have : ∀ i : ℕ × MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ (s' i.1)) i.2 =
        inner ℝ (G (b + s' i.1) ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (s' i.1) i.2) := fun i =>
    s105_recon_coord_eq hS hb q hq hG (s' i.1).2 i.2
  filter_upwards [ae_all_iff.2 this] with ζ hζ
  funext i
  exact (hζ i).symm

theorem s105_D_range {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q) [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)]
    {Ω Ω₂ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) [IsProbabilityMeasure P] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) q (b + T) η₀ Y)
    (s' : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s')
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P)
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (b + T) G (fun r _ =>
      s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) q hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t)) :
    (∀ᵐ ζ ∂P, (fun i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ i -
        s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) ∈
        Set.range (s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s')) ∧
    (∀ᵐ ζ ∂P, s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ ∈
        Set.range (s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s')) := by
  have hT0 : 0 ≤ T := hT.le
  have hemb := s56_measurableEmbedding_pathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' hs
  have hFm : Measurable (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G) :=
    measurable_pi_iff.2 fun i => (hGm _).inner measurable_const
  have hD : AEMeasurable (fun ζ i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ i -
      s105Psic ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P :=
    aemeasurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (s56_Psi0_meas s' (fun t ζ => Y (b + t) ζ) (fun t => hYm (b + t)))).aemeasurable.sub
        (hη i)
  have hlaw := s105_D_law hS hb hT q hq P P₂ η₀ Y hYm hY s' hη hG hGc hGz hGm
  have hF : ∀ᵐ ζ ∂P₂, s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ ∈
      Set.range (s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s') := by
    filter_upwards [s105_FArr_range hS hb q hq hG s'] with ζ hζ
    have hshift : ContinuousOn (fun τ => G (b + τ) ζ) (Set.Icc 0 T) := (hGc ζ).comp_continuousOn (by fun_prop)
    refine ⟨windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t), ?_⟩
    rw [hζ]
    exact s56_pathCoords_windowPathOf (d := d) (m := ((wholeSpaceIndex d : ℕ) : ℝ)) (T := T) s'
      (fun t ζ => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t)
      (continuousOn_iff_continuous_restrict.2 (HRS.MS.U9.u9_continuous_recon hT0 (fun τ ζ => G (b + τ) ζ) ζ hshift))
  have hD' := s56_ae_mem_of_map_eq P P₂ _ _ hD hFm.aemeasurable hlaw hemb.measurableSet_range hF
  refine ⟨hD', ?_⟩
  filter_upwards [hD', hY.cont] with ζ h1 h2
  obtain ⟨w', hw'⟩ := h1
  have h2' : ContinuousOn (fun t => Y (b + t) ζ) (Set.Icc 0 T) :=
    h2.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  refine ⟨windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => Y (b + t) ζ) - w', ?_⟩
  rw [s56_pathCoords_sub, s56_pathCoords_windowPathOf s' (fun t ζ => Y (b + t) ζ) h2', hw']
  funext i
  simp only [Pi.sub_apply, s56Psi0]
  ring

end HRS.MS.R2GenInit
