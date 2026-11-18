import HRS.MS.S104bNL1

/-!
# S10.5 (nonlinear), packet S104b-NL2: array law of the linear window process and the law of `c + 𝒯G` along a moving reference

Moving analogues of `s105_Y_array_law`, `s105_Yc_law` (R2GenInitAux34).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.Uniform.Q54c HRS.MS.R2GenInit HRS.MS.S21m

variable {d : ℕ}

theorem s104b_Y_array_law {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q)
    {Ω Ω₂ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) [IsProbabilityMeasure P] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) q (b + T) η₀ Y)
    (s' : ℕ → Set.Icc (0 : ℝ) T)
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s105Psic ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P)
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (b + T) G (fun r _ =>
      s21mDb _ hS.hF hS.hpAll q hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t))
    (c'' : Ω₂ → (ℕ × MultiIndex d → ℝ)) (hc''m : Measurable c'')
    (hc''law : P₂.map c'' = P.map (s105Psic ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀))
    (hW : ∀ (p : ℕ) (f : Fin p → ℕ × MultiIndex d),
      IndepFun (fun ζ => (WithLp.toLp 2 fun i => s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ (f i) :
        EuclideanSpace ℝ (Fin p)))
        (fun ζ => (WithLp.toLp 2 fun i => c'' ζ (f i) : EuclideanSpace ℝ (Fin p))) P₂) :
    P.map (s56Psi0 s' (fun t ζ => Y (b + t) ζ)) =
      P₂.map (fun ζ i => c'' ζ i + s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ i) := by
  set C := (quadraticGradientDyn d s a β).coeff ρ with hCdef
  have hFm : Measurable (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G) :=
    measurable_pi_iff.2 fun i => (hGm _).inner measurable_const
  have hΨc : AEMeasurable (s105Psic C ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀) P := aemeasurable_pi_iff.2 hη
  have hlawD := s104b_D_law hS hb hT q hq P P₂ η₀ Y hYm hY s' hη hG hGc hGz hGm
  refine s56_seq_law_eq P P₂ _ _ (s56_Psi0_meas s' (fun t ζ => Y (b + t) ζ) (fun t => hYm (b + t))).aemeasurable
    (hc''m.add hFm).aemeasurable fun p f hf => ?_
  obtain ⟨hDm, hVcm, hindV⟩ := s105_Vc_props C ((wholeSpaceIndex d : ℕ) : ℝ) b q T P η₀ Y hb hYm hY s' hη f
  set vec : (ℕ × MultiIndex d → ℝ) → EuclideanSpace ℝ (Fin p) := fun x => WithLp.toLp 2 fun i => x (f i) with hvec
  have hvm : Measurable vec :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun i => measurable_pi_apply (f i))
  have hD' : AEMeasurable (fun ζ i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ i - s105Psic C ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P :=
    aemeasurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (s56_Psi0_meas s' (fun t ζ => Y (b + t) ζ) (fun t => hYm (b + t)))).aemeasurable.sub
        (hη i)
  have e1 : (fun ζ => (WithLp.toLp 2 fun i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ (f i) : EuclideanSpace ℝ (Fin p))) =
      fun ζ => (WithLp.toLp 2 fun i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ (f i) -
        s105Psic C ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ (f i) : EuclideanSpace ℝ (Fin p)) +
        (WithLp.toLp 2 fun i => s105Psic C ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ (f i) :
          EuclideanSpace ℝ (Fin p)) := by
    funext ζ; ext i; simp
  have e2 : (fun ζ => (WithLp.toLp 2 fun i => c'' ζ (f i) + s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ (f i) :
      EuclideanSpace ℝ (Fin p))) =
      fun ζ => (WithLp.toLp 2 fun i => s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ (f i) :
        EuclideanSpace ℝ (Fin p)) + (WithLp.toLp 2 fun i => c'' ζ (f i) : EuclideanSpace ℝ (Fin p)) := by
    funext ζ; ext i; simp [add_comm]
  show P.map (fun ζ => (WithLp.toLp 2 fun i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ (f i) : EuclideanSpace ℝ (Fin p))) =
    P₂.map (fun ζ => (WithLp.toLp 2 fun i => c'' ζ (f i) + s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ (f i) :
      EuclideanSpace ℝ (Fin p)))
  rw [e1, e2]
  have hWF : Measurable (fun ζ => (WithLp.toLp 2 fun i => s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ (f i) :
      EuclideanSpace ℝ (Fin p))) := hvm.comp hFm
  have hWc : Measurable (fun ζ => (WithLp.toLp 2 fun i => c'' ζ (f i) : EuclideanSpace ℝ (Fin p))) := hvm.comp hc''m
  have hlawc : P.map (fun ζ => (WithLp.toLp 2 fun i => s105Psic C ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ (f i) :
        EuclideanSpace ℝ (Fin p))) =
      P₂.map (fun ζ => (WithLp.toLp 2 fun i => c'' ζ (f i) : EuclideanSpace ℝ (Fin p))) := by
    have := congrArg (fun μ => μ.map vec) hc''law
    rw [Measure.map_map hvm hc''m, AEMeasurable.map_map_of_aemeasurable hvm.aemeasurable hΨc] at this
    exact this.symm
  have hlawF : P.map (fun ζ => (WithLp.toLp 2 fun i => s56Psi0 s' (fun t ζ => Y (b + t) ζ) ζ (f i) -
        s105Psic C ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ (f i) : EuclideanSpace ℝ (Fin p))) =
      P₂.map (fun ζ => (WithLp.toLp 2 fun i => s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ (f i) :
        EuclideanSpace ℝ (Fin p))) := by
    have := congrArg (fun μ => μ.map vec) hlawD
    rw [AEMeasurable.map_map_of_aemeasurable hvm.aemeasurable hD', Measure.map_map hvm hFm] at this
    exact this
  exact s56_sum_law P P₂ _ _ _ _ hVcm hDm hWc.aemeasurable hWF.aemeasurable hindV (hW p f) hlawc hlawF

theorem s104b_Yc_law {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q)
    {Ω Ω₂ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    (P : Measure Ω) [IsProbabilityMeasure P] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) q (b + T) η₀ Y)
    (s' : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s')
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s105Psic ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀ ζ i) P)
    {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›} {G : ℝ → Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (b + T) G (fun r _ =>
      s21mDb _ hS.hF hS.hpAll q hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t))
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) (hgm : Measurable g)
    (hgleft : ∀ c ∈ Set.range (s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s'),
      s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' (g c) = c)
    (c'' : Ω₂ → (ℕ × MultiIndex d → ℝ)) (hc''m : Measurable c'')
    (hc''law : P₂.map c'' = P.map (s105Psic ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀))
    (hW : ∀ (p : ℕ) (f : Fin p → ℕ × MultiIndex d),
      IndepFun (fun ζ => (WithLp.toLp 2 fun i => s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ (f i) :
        EuclideanSpace ℝ (Fin p)))
        (fun ζ => (WithLp.toLp 2 fun i => c'' ζ (f i) : EuclideanSpace ℝ (Fin p))) P₂) :
    law P₂ (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
        (fun t => s56Ext hT.le (g (c'' ζ)) t +
          reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t)) =
      law P (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y) := by
  have hT0 : 0 ≤ T := hT.le
  have hemb := s56_measurableEmbedding_pathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' hs
  have hΨc : AEMeasurable (s105Psic ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) b s' η₀) P := aemeasurable_pi_iff.2 hη
  obtain ⟨-, hrange⟩ := s104b_D_range hS hb hT q hq P P₂ η₀ Y hYm hY s' hs hη hG hGc hGz hGm
  have hrange₂ : ∀ᵐ ζ ∂P₂, c'' ζ ∈ Set.range (s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s') :=
    s56_ae_mem_of_map_eq P₂ P c'' _ hc''m.aemeasurable hΨc hc''law hemb.measurableSet_range hrange
  have hcoords : ∀ᵐ ζ ∂P₂, s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' (g (c'' ζ)) = c'' ζ := by
    filter_upwards [hrange₂] with ζ hζ
    exact hgleft _ hζ
  set Y' : ℝ → Ω₂ → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ) := fun t ζ => s56Ext hT0 (g (c'' ζ)) t +
    reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t with hY'
  have hrecm : ∀ t, Measurable fun ζ => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t :=
    fun t => by
    unfold reconstructPath
    exact (((s56_evalA_cont hT0 t).measurable.comp (hGm (b + T))).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm (b + T)))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hGm (b + t)))
  have hY'm : ∀ t, Measurable (Y' t) := fun t =>
    (s56Ext_meas hT0 _ (hgm.comp hc''m) t).add (hrecm t)
  have hY'c : ∀ᵐ ζ ∂P₂, ContinuousOn (fun t => Y' t ζ) (Set.Icc 0 T) := by
    refine Filter.Eventually.of_forall fun ζ => ?_
    have hshift : ContinuousOn (fun τ => G (b + τ) ζ) (Set.Icc 0 T) := (hGc ζ).comp_continuousOn (by fun_prop)
    exact ((s56Ext_cont hT0 (g (c'' ζ))).continuousOn).add
      (continuousOn_iff_continuous_restrict.2 (HRS.MS.U9.u9_continuous_recon hT0 (fun τ ζ => G (b + τ) ζ) ζ hshift))
  have hYbc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Y (b + t) ζ) (Set.Icc 0 T) := by
    filter_upwards [hY.cont] with ζ h
    exact h.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have harr := s104b_Y_array_law hS hb hT q hq P P₂ η₀ Y hYm hY s' hη hG hGc hGz hGm c'' hc''m hc''law hW
  have harr' : P.map (s56Psi0 s' (fun t ζ => Y (b + t) ζ)) =
      P₂.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Y' (s' i.1) ζ) i.2) := by
    rw [harr]
    refine Measure.map_congr ?_
    filter_upwards [hcoords, s104b_FArr_range hS hb q hq hG s'] with ζ h1 h2
    funext i
    simp only [hY']
    rw [OscDual.coord_add, s56Ext_of_mem hT0 _ (s' i.1).2]
    have := congrFun h1 i
    simp only [s56PathCoords, OscPath.at'] at this
    rw [this, congrFun h2 i]
  have key := s56_path_law_eq hT0 P P₂ (fun t ζ => Y (b + t) ζ) Y' (fun t => hYm (b + t)) hY'm hYbc hY'c s' hs harr'
  rw [s105_pw_eq]
  exact key.symm

end HRS.MS.S104b
