import HRS.MS.WsStatAux9

/-!
# S21 packet E3: `OscAdjointInput` for the stationary coefficient

`s21_oscAdjointInput`: for `d >= 2`, `0 <= s < d`, `nu > 0`, `Q` symmetric, `rho` a Schwartz probability density, `T >= 0` and
`m >= 24 d + 240`, the coefficient `Cf = fixedViscosityCoeff s (-1) Q nu (s85c s rho) rho`
(`= (<s, -1, quadV Q 0, nu>).coeff (fun _ => rho)`, `S85.s85_coeff_fv`) satisfies `OscAdjointInput Cf m T`:

* `duhamel`: `d_a U^{r,t} phi_alpha - d_a phi_alpha = int_r^t d_a U^{r,s} L phi_alpha ds`, from the terminal-time derivative
  `d/dt U_t L^a f = U_t L^{a+1} f` (packet E1), time homogeneity of the propagator (`s52b_prop_eq`: the fixed-horizon evolution
  `w`, `U^{r,t} g = w(r + T - t)`) and the fundamental theorem of calculus (`s21_duhamel_core`);
* `feature`: `s21_isOrbitFeatureK` with the majorant of `s21_feature_bounds`.

This discharges the hypothesis `OscAdjointInput` of `general_paths`/`orbit_maximal_identification` in the stationary quadratic
setting (the `FcauTie` docstring: "`oscAdjointInput_of_ulAdjointInput` NOT provided" in general).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S21

open HRS.Whole HRS.MS.Ul HRS.MS.S52B HRS.MS.S85 HRS.MS.UlW HRS.MS.Go
open HRS (Euc)

variable {d : ℕ}

theorem s21_duhamel_core {G0 G1 : ℝ → ℝ} {T : ℝ}
    (hd0 : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt G0 (G1 τ) (Icc 0 T) τ)
    (hc1 : ContinuousOn G1 (Icc 0 T)) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    IntegrableOn (fun σ => G1 (σ - r)) (Icc r t) ∧
      G0 (t - r) - G0 0 = ∫ σ in Icc r t, G1 (σ - r) := by
  have hsub : Icc (0 : ℝ) (t - r) ⊆ Icc 0 T := fun τ hτ => ⟨hτ.1, by linarith [hτ.2]⟩
  have hint : IntervalIntegrable G1 volume 0 (t - r) :=
    (hc1.mono hsub).intervalIntegrable_of_Icc (by linarith)
  have hcont : ContinuousOn G0 (Icc 0 (t - r)) := fun τ hτ =>
    ((hd0 τ (hsub hτ)).continuousWithinAt).mono hsub
  have hderiv : ∀ τ ∈ Ioo (0 : ℝ) (t - r), HasDerivAt G0 (G1 τ) τ := by
    intro τ hτ
    have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, by linarith [hτ.2]⟩
    exact (hd0 τ hτT).hasDerivAt (Icc_mem_nhds hτ.1 (by linarith [hτ.2]))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hderiv hint
  have hmaps : MapsTo (fun σ : ℝ => σ - r) (Icc r t) (Icc 0 T) := fun σ hσ =>
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hcomp : ContinuousOn (fun σ => G1 (σ - r)) (Icc r t) :=
    hc1.comp (continuousOn_id.sub continuousOn_const) hmaps
  refine ⟨hcomp.integrableOn_Icc, ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrt,
    intervalIntegral.integral_comp_sub_right (f := G1) r]
  simp only [sub_self]
  exact hftc.symm

theorem s21_shift (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) (hT : 0 ≤ T) {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) {K : ℕ} (hK : (4 : ℝ) + (d : ℝ) / 2 < K)
    {g : Euc d → ℝ} (hg : UlClosure K θ g) (r σ : ℝ) (hr : 0 ≤ r) (hrσ : r ≤ σ) (hσT : σ ≤ T) :
    propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) r σ g =
      propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) 0 (σ - r) g := by
  have O : UlOrb d s ν ρ (fun _ => 0) (s85c s ρ) θ := ⟨hd, hs0, hsd, hν, hρ.2, s85_sigma d, rfl, hθ⟩
  obtain ⟨w, -, hw⟩ := s52b_prop_eq O Q hK hT (s85_uniq hd hs0 hsd hν Q hQ hρ T) hg
  rw [hw r σ hr hrσ hσT, hw 0 (σ - r) le_rfl (by linarith) (by linarith)]
  congr 1
  ring

theorem s21_duhamel (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) (hT : 0 ≤ T) (m : ℝ) :
    ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ (α : MultiIndex d) (a : Fin d) (x : Euc d),
      IntegrableOn (fun σ => gradComp a (propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) r σ
        (generatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) σ (oscTestFun m α))) x) (Icc r t) ∧
      gradComp a (propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) r t (oscTestFun m α)) x -
        gradComp a (oscTestFun m α) x =
      ∫ σ in Icc r t, gradComp a (propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) r σ
        (generatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) σ (oscTestFun m α))) x := by
  intro r t hr hrt htT α a x
  set Cf := fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ with hCf
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have O : UlOrb d s ν ρ (fun _ => 0) (s85c s ρ) θ := ⟨hd, hs0, hsd, hν, hρ.2, s85_sigma d, rfl, hθ⟩
  set K : ℕ := ⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hKdef
  have hK : (4 : ℝ) + (d : ℝ) / 2 < K := by
    rw [hKdef]; push_cast; exact Nat.lt_floor_add_one _
  obtain ⟨f, hf, -⟩ := s52b_phi (d := d) m α
  have hφ0 : UlClosure K θ (oscTestFun m α) := by
    have := ul6_closure O Q f 0 K
    rw [← hf]; exact this
  have hφ1 : UlClosure K θ (generatorW Cf 0 (oscTestFun m α)) := by
    have := ul6_closure O Q f 1 K
    have e : ul6L s Q ν (s85c s ρ) ρ f 1 = fun x => generatorW Cf 0 (⇑f) x := by
      rw [ul6L_succ]; rfl
    rw [e] at this
    rw [← hf]; exact this
  -- the derivative facts
  have hD0 := s21_stat_deriv hd hs0 hsd hν Q hQ hρ T hT f 0 (by norm_num) a x
  have hD1 := s21_stat_deriv hd hs0 hsd hν Q hQ hρ T hT f 1 (by norm_num) a x
  simp only [Function.iterate_zero, id, zero_add, Function.iterate_one, hf] at hD0 hD1
  set G0 : ℝ → ℝ := fun τ => gradComp a (propagatorW Cf 0 τ (oscTestFun m α)) x with hG0
  set G1 : ℝ → ℝ := fun τ => gradComp a (propagatorW Cf 0 τ (generatorW Cf 0 (oscTestFun m α))) x with hG1
  have hd0 : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt G0 (G1 τ) (Icc 0 T) τ := fun τ hτ => hD0 τ hτ
  have hc1 : ContinuousOn G1 (Icc 0 T) := fun τ hτ => (hD1 τ hτ).continuousWithinAt
  obtain ⟨hI, hE⟩ := s21_duhamel_core hd0 hc1 hr hrt htT
  -- terminal value
  have hterm : propagatorW Cf 0 0 (oscTestFun m α) = oscTestFun m α := by
    obtain ⟨⟨f₀, hf₀⟩, -⟩ := s85_exists_adjoint hd hs0 hsd hν Q hQ hρ T hT m α 0 ⟨le_rfl, hT⟩
    rw [s85_coeff_fv Q hQ ρ] at hf₀
    have := s21_prop_eq_classical hd hs0 hsd hν Q hQ hρ T (t := 0) ⟨le_rfl, hT⟩ hf₀ 0 ⟨le_rfl, le_rfl⟩
    rw [this]
    exact hf₀.terminal
  have hshift0 := fun σ (h1 : r ≤ σ) (h2 : σ ≤ T) =>
    s21_shift hd hs0 hsd hν Q hQ hρ T hT hθ hK hφ0 r σ hr h1 h2
  have hshift1 := fun σ (h1 : r ≤ σ) (h2 : σ ≤ T) =>
    s21_shift hd hs0 hsd hν Q hQ hρ T hT hθ hK hφ1 r σ hr h1 h2
  have hgen : ∀ σ, generatorW Cf σ (oscTestFun m α) = generatorW Cf 0 (oscTestFun m α) := fun σ => rfl
  have heq : ∀ σ ∈ Icc r t,
      gradComp a (propagatorW Cf r σ (generatorW Cf σ (oscTestFun m α))) x = G1 (σ - r) := by
    intro σ hσ
    rw [hgen σ, hshift1 σ hσ.1 (hσ.2.trans htT)]
  refine ⟨hI.congr_fun (fun σ hσ => (heq σ hσ).symm) measurableSet_Icc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Icc (fun σ hσ => heq σ hσ), ← hE]
  have h1 : gradComp a (propagatorW Cf r t (oscTestFun m α)) x = G0 (t - r) := by
    rw [hshift0 t hrt htT]
  have h2 : gradComp a (oscTestFun m α) x = G0 0 := by
    simp only [hG0, hterm]
  rw [h1, h2]

theorem s21_oscAdjointInput (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) (hT : 0 ≤ T) (m : ℝ) (hm : (24 : ℝ) * d + 240 ≤ m) :
    OscAdjointInput (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) m T where
  duhamel := s21_duhamel hd hs0 hsd hν Q hQ hρ T hT m
  feature := by
    obtain ⟨c, hc0, hcs, hbase, horb, hmeas⟩ := s21_feature_bounds hd hs0 hsd hν Q hQ hρ T hT m hm
    intro a r hr x
    exact s21_isOrbitFeatureK a c hc0 hcs (fun α x => hbase a α x) (fun α r t h1 h2 h3 x => horb a α r t h1 h2 h3 x)
      (fun r hr α x => hmeas a r hr α x) hr x

end HRS.MS.S21
