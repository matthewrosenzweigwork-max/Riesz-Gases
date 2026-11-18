import HRS.MC.S7PIDefs
import HRS.MC.S7PIS1Path2

/-!
# Packet piG6 (PI-G6), part A: auxiliary lemmas for the removal of the projection

* `S7PIG6_IsRS_congr`: `IsRS` only sees the integrand at tags and endpoints in `[0,T]`;
* `S7PIG6_concl_congr`: `PathItoConcl` only sees `γ_u` for `u ∈ [0,T]` (so `γ` can be replaced by a family of probability
  measures, which is what `s7_PIG_RS_drift`, `s7_PIG_RS_J` need);
* `S7PIG6_jPair_congr`: `jPair z` only sees `z` on `[0,T]`;
* `S7PIG6_initProp_cont`: `z ↦ 𝖨z` is continuous `E_m → 𝒳`;
* `S7PIG6_heat_cont`: `y ↦ ∫ Ψ(y+z) dμ` is continuous for `Ψ` bounded continuous;
* `S7PIG6_lim`: a.e. limits of integrable functions dominated by an integrable function.
Namespace `HRS.MC.Sec7.S7PIG6`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- `IsRS` only depends on the integrand for `τ ∈ [0,T]`, `0 ≤ a ≤ b ≤ T`. -/
theorem S7PIG6_IsRS_congr {T : ℝ} {S S' : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S I)
    (hS : ∀ τ a b : ℝ, τ ∈ Set.Icc (0 : ℝ) T → 0 ≤ a → a ≤ b → b ≤ T → S τ a b = S' τ a b) :
    IsRS T S' I := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := h ε hε
  refine ⟨δ, hδ, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have hmono : Monotone u := hu.monotone
  have hsum : ∑ i : Fin n, S' (τ i) (u i.castSucc) (u i.succ) = ∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have ha : 0 ≤ u i.castSucc := hu0 ▸ hmono (Fin.zero_le _)
    have hb : u i.succ ≤ T := huT ▸ hmono (Fin.le_last _)
    have hab : u i.castSucc ≤ u i.succ := (htag i).1.trans (htag i).2
    have hτ : τ i ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans (htag i).1, (htag i).2.trans hb⟩
    exact (hS _ _ _ hτ ha hab hb).symm
  rw [hsum]
  exact hδ' n u τ hu hu0 huT htag hmesh

/-- `heatFn` at a time `τ` only depends on `γ τ`. -/
theorem S7PIG6_heat_congr {m T : ℝ} {γ₁ γ₂ : ℝ → Measure (PathSpace d m T)} {τ : ℝ} (h : γ₁ τ = γ₂ τ)
    (Ψ : PathSpace d m T → ℝ) : heatFn γ₁ Ψ τ = heatFn γ₂ Ψ τ := by
  funext y
  unfold heatFn
  rw [h]

/-- `IsJValue` only sees `z` on `[0,T]`. -/
theorem S7PIG6_isJValue_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) {z z' : ℝ → NegSobolev d m}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) T, z u = z' u) (I : Set ℝ) :
    IsJValue D ρ m T z I = IsJValue D ρ m T z' I := by
  funext J
  unfold IsJValue
  refine propext (and_congr Iff.rfl (forall_congr' fun ta => forall_congr' fun tb => forall_congr' fun φa =>
    forall_congr' fun φb => forall_congr' fun l₁ => forall_congr' fun l₂ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun hta => imp_congr_right fun htb => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_))
  have : ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), NegSobolev.eval (z u)
        (fun x => inner ℝ (Torus.grad (propagator D ρ u ta φa) x) (Torus.grad (propagator D ρ u tb φb) x)) =
      ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), NegSobolev.eval (z' u)
        (fun x => inner ℝ (Torus.grad (propagator D ρ u ta φa) x) (Torus.grad (propagator D ρ u tb φb) x)) := by
    refine integral_congr_ae ?_
    have hmin : min ta tb ≤ T := min_le_of_left_le hta.2
    refine ae_restrict_of_ae_restrict_of_subset (t := Set.Icc (0 : ℝ) T) ?_ ?_
    · exact Set.inter_subset_right.trans (Set.Icc_subset_Icc le_rfl hmin)
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
      simp only [h u hu]
  rw [this]

/-- `jPair z` only sees `z` on `[0,T]`. -/
theorem S7PIG6_jPair_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) {z z' : ℝ → NegSobolev d m}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) T, z u = z' u) (I : Set ℝ) :
    jPair D ρ m T z I = jPair D ρ m T z' I := by
  unfold jPair
  rw [S7PIG6_isJValue_congr D ρ m T h I]

section Prob

variable (R : Regime d) (m T : ℝ) (N : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  (X : ℝ≥0 → Ω → Config d N)

/-- `PathItoConcl` only sees `γ_u` for `u ∈ [0,T]`. -/
theorem S7PIG6_concl_congr (hT : 0 ≤ T) {γ₁ γ₂ : ℝ → Measure (PathSpace d m T)}
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, γ₁ u = γ₂ u) (Φ : PathSpace d m T → ℝ)
    (Pj : PathSpace d m T →L[ℝ] PathSpace d m T)
    (h : PathItoConcl R m T γ₁ N P X Φ Pj) : PathItoConcl R m T γ₂ N P X Φ Pj := by
  obtain ⟨A, J, hA, hJ, hAR, hJR, hid⟩ := h
  refine ⟨A, J, hA, hJ, ?_, ?_, ?_⟩
  · filter_upwards [hAR] with ω hω
    refine S7PIG6_IsRS_congr hω fun τ a b hτ _ _ _ => ?_
    rw [S7PIG6_heat_congr (hγ τ hτ)]
  · filter_upwards [hJR] with ω hω
    refine S7PIG6_IsRS_congr hω fun τ a b hτ _ _ _ => ?_
    rw [S7PIG6_heat_congr (hγ τ hτ)]
  · rw [S7PIG6_heat_congr (hγ 0 ⟨le_rfl, hT⟩)] at hid
    exact hid

end Prob

open HRS.PDE HRS.A33 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV HRS.MC.Sec7.S7PIS1 in
/-- `z ↦ 𝖨z` is continuous `E_m → 𝒳_{m,T}`. -/
theorem S7PIG6_initProp_cont (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    Continuous fun z : NegSobolev d m => initProp R.D R.ρ m T z := by
  obtain ⟨J, k, hk, hJ, hm0, hm1, H⟩ := S7PIS1_data R m hm T hT
  have hjoint : Continuous fun p : NegSobolev d m × Set.Icc (0 : ℝ) T => Vprop R.D R.ρ m p.2.1 0 p.1 := by
    rw [continuous_iff_continuousAt]
    intro p₀
    exact S7PIS1_V_joint H m k hk hJ hm0 hm1 (𝓝 p₀) (fun p => p.2.1) (fun _ => (0 : ℝ))
      (Eventually.of_forall fun p => ⟨le_rfl, p.2.2.1, p.2.2.2⟩) ⟨le_rfl, p₀.2.2.1, p₀.2.2.2⟩
      tendsto_const_nhds ((continuous_subtype_val.comp continuous_snd).tendsto p₀) (fun p => p.1)
      (continuous_fst.tendsto p₀)
  let g : C(NegSobolev d m × Set.Icc (0 : ℝ) T, NegSobolev d m) := ⟨_, hjoint⟩
  have hcur := (ContinuousMap.curry g).continuous
  refine hcur.congr fun z => ?_
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Vprop R.D R.ρ m t.1 0 z :=
    (ContinuousMap.curry g z).continuous
  unfold initProp
  rw [S7PIS1_pathOf_eq _ hc]
  rfl

section Gen

/-- `y ↦ ∫ Ψ(y+z) dμ` is continuous for `Ψ` bounded continuous and `μ` a probability measure. -/
theorem S7PIG6_heat_cont {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] {Ψ : B → ℝ} (hc : Continuous Ψ) (K : ℝ) (hK : ∀ x, |Ψ x| ≤ K) :
    Continuous fun y : B => ∫ z, Ψ (y + z) ∂μ := by
  refine continuous_of_dominated (bound := fun _ => K) (fun y => ?_) (fun y => ?_) (integrable_const K)
    (Eventually.of_forall fun z => ?_)
  · exact (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by simpa using hK (y + z)
  · exact hc.comp (continuous_id.add continuous_const)

/-- a.e. limits of integrable functions dominated by an integrable function -/
theorem S7PIG6_lim {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f : ℕ → Ω → ℝ)
    (hf : ∀ L, AEStronglyMeasurable (f L) P) (b : Ω → ℝ) (hb : Integrable b P)
    (h : ∀ᵐ ω ∂P, (∃ I, Tendsto (fun L => f L ω) atTop (𝓝 I)) ∧ ∀ L, |f L ω| ≤ b ω) :
    Integrable (fun ω => limUnder atTop (fun L => f L ω)) P ∧
      (∀ᵐ ω ∂P, Tendsto (fun L => f L ω) atTop (𝓝 (limUnder atTop (fun L => f L ω)))) ∧
      Tendsto (fun L => ∫ ω, f L ω ∂P) atTop (𝓝 (∫ ω, limUnder atTop (fun L => f L ω) ∂P)) := by
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun L => f L ω) atTop (𝓝 (limUnder atTop (fun L => f L ω))) := by
    filter_upwards [h] with ω hω
    obtain ⟨I, hI⟩ := hω.1
    rw [hI.limUnder_eq]
    exact hI
  have hbd : ∀ L, ∀ᵐ ω ∂P, ‖f L ω‖ ≤ b ω := fun L => by
    filter_upwards [h] with ω hω
    simpa [Real.norm_eq_abs] using hω.2 L
  have hmeas : AEStronglyMeasurable (fun ω => limUnder atTop (fun L => f L ω)) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  refine ⟨?_, hlim, ?_⟩
  · refine hb.mono' hmeas ?_
    filter_upwards [hlim, h] with ω hω hω'
    exact le_of_tendsto hω.abs (Eventually.of_forall fun L => hω'.2 L)
  · exact tendsto_integral_of_dominated_convergence b hf hb hbd hlim

end Gen

end HRS.MC.Sec7.S7PIG6

end
