import HRS.MS.R2GenInitAux40
import HRS.MS.GenPathAux59

/-!
# S10.5 window comparison, packet F3: helper lemmas for the master (independence of the window arrays, a.e. changes of the Gaussian martingale, the particle window)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.Uniform

variable {d : ℕ}

theorem s105_indepFun_vec (m T b : ℝ) (hb : 0 ≤ b) {Ω₂ : Type*} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
    (s' : ℕ → Set.Icc (0 : ℝ) T) (G : ℝ → Ω₂ → KSpace d m T) (c'' : Ω₂ → (ℕ × MultiIndex d → ℝ))
    (hind : Indep (MeasurableSpace.comap c'' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) (b + T), MeasurableSpace.comap (G τ) inferInstance) P₂)
    {p : ℕ} (f : Fin p → ℕ × MultiIndex d) :
    IndepFun (fun ζ => (WithLp.toLp 2 fun a => s105FArr m T b s' G ζ (f a) : EuclideanSpace ℝ (Fin p)))
      (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) P₂ := by
  set mG : MeasurableSpace Ω₂ := ⨆ τ ∈ Set.Icc (0 : ℝ) (b + T), MeasurableSpace.comap (G τ) inferInstance with hmG
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) (b + T), MeasurableSpace.comap (G t) inferInstance ≤ mG := fun t ht =>
    le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) (b + T)) => MeasurableSpace.comap (G τ) inferInstance) t ht
  have hG : ∀ t ∈ Set.Icc (0 : ℝ) (b + T), @Measurable Ω₂ (KSpace d m T) mG _ (G t) := fun t ht =>
    Measurable.of_comap_le (hle t ht)
  have hΦ : @Measurable Ω₂ (Fin p → ℝ) mG _ (fun ζ (a : Fin p) => s105FArr m T b s' G ζ (f a)) := by
    refine @measurable_pi_iff Ω₂ (Fin p) (fun _ => ℝ) mG _ _ |>.2 fun a => ?_
    exact @Measurable.comp Ω₂ (KSpace d m T) ℝ mG _ _
      (fun x : KSpace d m T => inner ℝ x (s52y1 m T (s' (f a).1) (f a).2)) (G (b + s' (f a).1))
      (continuous_id.inner continuous_const).measurable
      (hG _ ⟨by linarith [(s' (f a).1).2.1], by linarith [(s' (f a).1).2.2]⟩)
  have hWF : @Measurable Ω₂ (EuclideanSpace ℝ (Fin p)) mG _
      (fun ζ => (WithLp.toLp 2 fun a => s105FArr m T b s' G ζ (f a) : EuclideanSpace ℝ (Fin p))) :=
    @Measurable.comp Ω₂ (Fin p → ℝ) (EuclideanSpace ℝ (Fin p)) mG _ _
      (fun v : Fin p → ℝ => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p)))
      (fun ζ (a : Fin p) => s105FArr m T b s' G ζ (f a))
      (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable hΦ
  have hWc : @Measurable Ω₂ (EuclideanSpace ℝ (Fin p)) (MeasurableSpace.comap c'' inferInstance) _
      (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) :=
    @Measurable.comp Ω₂ (ℕ × MultiIndex d → ℝ) (EuclideanSpace ℝ (Fin p)) (MeasurableSpace.comap c'' inferInstance) _ _
      (fun c : ℕ × MultiIndex d → ℝ => (WithLp.toLp 2 fun a => c (f a) : EuclideanSpace ℝ (Fin p))) c''
      ((PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
        (measurable_pi_iff.2 fun a => measurable_pi_apply (f a))) (comap_measurable c'')
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm hWF.comap_le) hWc.comap_le

theorem s105_window_recon_ae {m T b : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G G' : ℝ → Ω → KSpace d m T) (s' : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s')
    (hGc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 (b + T)))
    (hG'c : ∀ ζ, Continuous fun t => G' t ζ)
    (hae : ∀ τ ∈ Set.Icc (0 : ℝ) (b + T), G τ =ᵐ[P] G' τ) (cp : Ω → OscPath d m T) :
    (fun ζ => windowPathOf m T 0 (fun t => s56Ext hT (cp ζ) t + reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t)) =ᵐ[P]
    (fun ζ => windowPathOf m T 0 (fun t => s56Ext hT (cp ζ) t + reconstructPath m T (fun τ ζ => G' (b + τ) ζ) ζ t)) := by
  have hT' : b + T ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith, le_rfl⟩
  have h1 : ∀ᵐ ζ ∂P, ∀ n : ℕ, G (b + s' n) ζ = G' (b + s' n) ζ :=
    ae_all_iff.2 fun n => hae _ ⟨by linarith [(s' n).2.1], by linarith [(s' n).2.2]⟩
  filter_upwards [h1, hae _ hT', hGc] with ζ hn hT'' hc
  refine s56_wpo_congr fun t ht => ?_
  congr 1
  have hshift : ContinuousOn (fun τ => G (b + τ) ζ) (Set.Icc 0 T) :=
    hc.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hshift' : ContinuousOn (fun τ => G' (b + τ) ζ) (Set.Icc 0 T) := (hG'c ζ).comp_continuousOn (by fun_prop)
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t :=
    HRS.MS.U9.u9_continuous_recon hT _ ζ hshift
  have hcont' : Continuous fun t : Set.Icc (0 : ℝ) T => reconstructPath m T (fun τ ζ => G' (b + τ) ζ) ζ t :=
    HRS.MS.U9.u9_continuous_recon hT _ ζ hshift'
  have heq : (fun t : Set.Icc (0 : ℝ) T => reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t) =
      fun t : Set.Icc (0 : ℝ) T => reconstructPath m T (fun τ ζ => G' (b + τ) ζ) ζ t := by
    refine hs.equalizer hcont hcont' (funext fun n => ?_)
    show reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ (s' n) = reconstructPath m T (fun τ ζ => G' (b + τ) ζ) ζ (s' n)
    unfold reconstructPath
    beta_reduce
    rw [hT'', hn n]
  exact congrFun heq ⟨t, ht⟩

theorem s105_fluc_eq {m σ : ℝ} {T b : ℝ} {N : ℕ} {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (ρ : Euc d → ℝ) (ζ : Ω) :
    flucPathW m T b σ X (fun _ : ℝ => ρ) ζ = windowPathOf m T 0 (fun u => s105Xi m σ ρ X (b + u) ζ) := by
  unfold flucPathW windowPathOf s105Xi
  exact HRS.GF.dite_continuousMap_congr _ _ (funext fun t => by simp)

end HRS.MS.R2GenInit
