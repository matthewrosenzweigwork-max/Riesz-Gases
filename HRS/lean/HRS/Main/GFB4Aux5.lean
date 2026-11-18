import HRS.Main.GFB4Aux4

/-!
# GFB4, part 5: Itô sums as pairings of Riemann sums, `L²` convergence, a.s.-modification of `IsStochConv`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gfb4_min_sub_le {a b t : ℝ} (hab : b ≤ a) : min a t - min b t ≤ a - b := by
  rcases le_total a t with h | h
  · rw [min_eq_left h, min_eq_left (hab.trans h)]
  · rcases le_total b t with h2 | h2
    · rw [min_eq_right h, min_eq_left h2]; linarith
    · rw [min_eq_right h, min_eq_right h2]; linarith

/-- The Itô sum along the grid truncated at `t`, against `σ ↦ V(t,σ)^*ℓ`, is `ℓ` applied to a Riemann sum. -/
theorem gfb4_isum_eq {Ω : Type*} (G : ℝ → Ω → H) (EV : EvolData H E) (ℓ : E →L[ℝ] ℝ) (T t : ℝ)
    (N : ℕ) (ω : Ω) :
    isum (fun σ => G σ ω) (fun σ => pullbackVec EV t σ ℓ) T t N =
      ℓ (riemannSum EV.VE EV.j G t (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) ω) := by
  unfold isum riemannSum
  rw [map_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ((i.castSucc : Fin (N + 2)) : ℕ) = (i : ℕ) := rfl
  have h2 : ((i.succ : Fin (N + 2)) : ℕ) = (i : ℕ) + 1 := rfl
  simp only [h1, h2]
  rw [real_inner_comm, pullback_inner]

/-- The partitions `min (gridPt T N i) t` are admissible in `IsStochConv`. -/
theorem gfb4_grid_partition {T t : ℝ} (hT : 0 ≤ T) (ht0 : 0 ≤ t) (htT : t ≤ T) (N : ℕ) :
    (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) 0 = 0 ∧
    (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) (Fin.last (N + 1)) = t ∧
    Monotone (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) ∧
    ∀ i : Fin (N + 1), (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) i.succ -
      (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) i.castSucc ≤ T / ((N : ℝ) + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [gridPt_zero, ht0]
  · simp only [Fin.val_last]
    rw [gridPt_last, min_eq_right htT]
  · intro i j hij
    exact min_le_min_right _ (gridPt_mono hT N (by exact_mod_cast hij))
  · intro i
    have h1 : ((i.castSucc : Fin (N + 2)) : ℕ) = (i : ℕ) := rfl
    have h2 : ((i.succ : Fin (N + 2)) : ℕ) = (i : ℕ) + 1 := rfl
    simp only [h1, h2]
    refine (gfb4_min_sub_le (gridPt_mono hT N (Nat.le_succ _))).trans ?_
    rw [gridPt_succ_sub]

theorem gfb4_L2_of_stochConv {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (EV : EvolData H E) (G : ℝ → Ω → H) {T t : ℝ} (hT : 0 ≤ T) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (Zb : Ω → E) (hZ : IsStochConv P EV.VE EV.j G 0 t Zb) (ℓ : E →L[ℝ] ℝ) (X : Ω → ℝ)
    (hX : ∀ ω, X ω = ℓ (Zb ω)) :
    Tendsto (fun N => ∫⁻ ω, ‖X ω - isum (fun σ => G σ ω) (fun σ => pullbackVec EV t σ ℓ) T t N‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => ∫⁻ ω, ‖Zb ω - riemannSum EV.VE EV.j G t
      (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · exact Filter.Eventually.of_forall fun _ => htop ▸ le_top
    obtain ⟨δ, hδ, hh⟩ := hZ ε.toReal (ENNReal.toReal_pos hε.ne' htop)
    obtain ⟨N0, hN0⟩ := exists_nat_gt (T / δ)
    filter_upwards [Filter.eventually_ge_atTop N0] with N hN
    obtain ⟨p0, p1, p2, p3⟩ := gfb4_grid_partition hT ht0 htT N
    have hstep : T / ((N : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      have : T / δ < N + 1 := by
        have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      rw [div_lt_iff₀ hδ] at this
      linarith
    have := hh (N + 1) _ p0 p1 p2 (fun i => lt_of_le_of_lt (p3 i) hstep)
    rw [ENNReal.ofReal_toReal htop] at this
    exact this.le
  have hc : Tendsto (fun N : ℕ => (‖ℓ‖ₑ ^ 2) * ∫⁻ ω, ‖Zb ω - riemannSum EV.VE EV.j G t
      (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hg (a := ‖ℓ‖ₑ ^ 2) (Or.inr (by simp))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun N => bot_le) (fun N => ?_)
  have hne : ‖ℓ‖ₑ ^ 2 ≠ ⊤ := by
    exact ENNReal.pow_ne_top enorm_ne_top
  rw [← lintegral_const_mul' _ _ hne]
  refine lintegral_mono fun ω => ?_
  rw [hX ω, gfb4_isum_eq, ← map_sub]
  calc ‖ℓ (Zb ω - riemannSum EV.VE EV.j G t (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) ω)‖ₑ ^ 2
      ≤ (‖ℓ‖ₑ * ‖Zb ω - riemannSum EV.VE EV.j G t
          (fun i : Fin (N + 2) => min (gridPt T N (i : ℕ)) t) ω‖ₑ) ^ 2 := by
        gcongr
        exact ℓ.le_opNorm_enorm _
    _ = _ := by rw [mul_pow]

/-- `IsStochConv` only depends on `G` up to a.e. modification at the times in `[0,t]`. -/
theorem gfb4_isStochConv_congr {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E) {G G' : ℝ → Ω → H} {t : ℝ} (ht : 0 ≤ t)
    (hGG : ∀ τ ∈ Set.Icc (0 : ℝ) t, G' τ =ᵐ[P] G τ) {Z : Ω → E}
    (h : IsStochConv P VE j G 0 t Z) : IsStochConv P VE j G' 0 t Z := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have hmem : ∀ i, r i ∈ Set.Icc (0 : ℝ) t := fun i => by
    refine ⟨h0 ▸ hmono (Fin.zero_le i), hn ▸ hmono (Fin.le_last i)⟩
  have hae : ∀ᵐ ω ∂P, ∀ i, G' (r i) ω = G (r i) ω := ae_all_iff.2 fun i => hGG _ (hmem i)
  refine lt_of_le_of_lt (le_of_eq ?_) (hh n r h0 hn hmono hmesh)
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ω hω
  simp only [riemannSum, hω]

end HRS.GF
