import HRS.MS.R2WinOrbNLAux21

/-!
# S10.3, part 22: the nonlinear window tests from the terminal-time regularity of the adjoint orbit

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103n_window_of_famHyp`: the tail of `s103_window_tests` for an arbitrary coefficient: an orbit family `F'` (`s103_famHyp`, bound `C b_α`) with
  `F' 0 τ = U(0,τ)φ_α` on `[0,b+T]` gives `f_{b,n,α} ∈ C_b^k` and `‖f_{b,n,α}‖_{C_b^k} ≤ ((4d+42)+1) M₀(C,T) (1+n)^{-5/4} b_α`.
* `s103nData`: the three terminal data `φ_α`, `L_tφ_α`, `L_t²φ_α + ∂_tL_tφ_α` (ED13 right derivative).
* `S103nTermReg`: the nonlinear analogue of `ul_adjoint_orbit_bounds` for the orbit of `φ_α` (classical adjoint solutions for the three data and the
  `C_b^k` difference quotients `h⁻¹(F a (t+h) - F a t) → F (a+1) t` in the terminal time).  This is the single analytic input that is NOT in the repository.
* `s103n_windowClause_of_termReg`: the orbit claims and `S103nTermReg` give `S103nWindowClause`.
* `s103n_tie_of_termReg`: `R2WinOrbED13` from `S103nTermReg` alone.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who HRS.MS.BreakdownS67
  HRS.MS.MovAdj HRS.MS.R2WinOrb

variable {d : ℕ}

/-- The window-test bound constant for the orbit constant `C` and the window length `T`. -/
def s103nM0 (T C : ℝ) : ℝ :=
  max (T * (1 / Real.sqrt T) * C) (4 * (Real.sqrt (2 / T) * ((2 * C + T * C) * T ^ 2 / Real.pi ^ 2)))

theorem s103nM0_nonneg {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) : 0 ≤ s103nM0 T C :=
  le_trans (by positivity) (le_max_left _ _)

theorem s103n_window_of_famHyp {Cf : WholeCoeff d} {α : MultiIndex d} {b T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    {F' : ℕ → ℝ → Euc d → ℝ} (Hfam : s103_famHyp F' (4 * d + 42) (b + T) (C * s103_b d α))
    (hb : 0 ≤ b)
    (hF0 : ∀ τ ∈ Set.Icc (0 : ℝ) (b + T), F' 0 τ = propagatorW Cf 0 τ (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α))
    (n : ℕ) :
    MemCb (4 * d + 42) (r2WindowTest Cf ((24 * d + 240 : ℕ) : ℝ) T b n α) ∧
      cbNorm (4 * d + 42) (r2WindowTest Cf ((24 * d + 240 : ℕ) : ℝ) T b n α) ≤
        (((4 * d + 42 : ℕ) + 1 : ℝ) * s103nM0 T C) * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b d α := by
  have hb0 := s103_b_nonneg (d := d) α
  have hA : 0 ≤ C * s103_b d α := mul_nonneg hC hb0
  have hM00 : 0 ≤ s103nM0 T C := s103nM0_nonneg hT hC
  obtain ⟨hcd, hdb⟩ := s103_window_core (by omega : 1 ≤ 4 * d + 42) Hfam hb hT le_rfl hA n
  set G : Euc d → ℝ := fun x => ∫ u in Set.Icc (0 : ℝ) T, r2CosBasis T n u * F' 0 (b + u) x with hG
  set cn : ℝ := (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) with hcn
  have hcn0 : 0 ≤ cn := by positivity
  have hfun : r2WindowTest Cf ((24 * d + 240 : ℕ) : ℝ) T b n α = fun x => cn * G x := by
    funext x
    unfold r2WindowTest
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    have h1 := hF0 (b + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [h1]
  rw [hfun]
  have e : (fun x => cn * G x) = cn • G := rfl
  have hjet : ∀ j ≤ 4 * d + 42, ∀ x, ‖iteratedFDeriv ℝ j (fun x => cn * G x) x‖ ≤
      cn * s103_cosBound T (C * s103_b d α) n := by
    intro j hj x
    rw [e, iteratedFDeriv_const_smul_apply ((hcd.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hcn0]
    exact mul_le_mul_of_nonneg_left (hdb j hj x) hcn0
  refine ⟨⟨contDiff_const.mul hcd, fun j hj => ⟨cn * s103_cosBound T (C * s103_b d α) n, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hjet j hj x
  · unfold cbNorm
    have hB : ∀ j ≤ 4 * d + 42, (⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => cn * G x) z‖) ≤
        cn * s103_cosBound T (C * s103_b d α) n := fun j hj => ciSup_le fun z => hjet j hj z
    calc ∑ j ∈ Finset.range (4 * d + 42 + 1), (⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => cn * G x) z‖)
        ≤ ∑ j ∈ Finset.range (4 * d + 42 + 1), cn * s103_cosBound T (C * s103_b d α) n :=
          Finset.sum_le_sum fun j hj => hB j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      _ = ((4 * d + 42 : ℕ) + 1 : ℝ) * (cn * (s103_b d α * s103_cosBound T C n)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, s103_cosBound_mul]; push_cast; ring
      _ ≤ ((4 * d + 42 : ℕ) + 1 : ℝ) * (s103_b d α * (s103nM0 T C * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := s103_cosBound_arith hT hC n
          calc cn * (s103_b d α * s103_cosBound T C n) = s103_b d α * (cn * s103_cosBound T C n) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left this hb0
      _ = _ := by ring

/-- The three terminal data of the window orbit: `φ_α`, `L_tφ_α`, and `L_t²φ_α + ∂_tL_tφ_α` (right derivative, ED13 form). -/
def s103nData (Cf : WholeCoeff d) (φ : Euc d → ℝ) : Fin 3 → ℝ → Euc d → ℝ :=
  fun a t => match a with
    | 0 => φ
    | 1 => generatorW Cf t φ
    | 2 => fun x => generatorW Cf t (generatorW Cf t φ) x +
        derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t

/-- THE OPEN INPUT.  Nonlinear analogue of `ul_adjoint_orbit_bounds` for the orbit of `φ_α` along a trajectory of the class: if classical adjoint
solutions with datum `φ_α` exist for all terminal times (the hypothesis of the window clause), then on every horizon `[0,T0]` there is a family `F a t`
(`a ≤ 2`) of values `u 0` of classical adjoint solutions with terminal datum `s103nData a t`, `F 0 t = U(0,t)φ_α`, whose terminal-time difference quotients
converge in every `C^j` sup norm, `j ≤ 4d+42`: `h⁻¹ (F a (t+h) - F a t) → F (a+1) t`. -/
def S103nTermReg (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ : ℝ) : Prop :=
  ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
    IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
    ∀ (α : MultiIndex d),
      (∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
        (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) f) →
      ∀ T0 : ℝ, 0 ≤ T0 →
        ∃ F : Fin 3 → ℝ → Euc d → ℝ,
          (∀ t ∈ Set.Icc (0 : ℝ) T0, F 0 t = propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 t
            (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α)) ∧
          (∀ a' : Fin 3, ∀ t ∈ Set.Icc (0 : ℝ) T0, ∃ u : ℝ → Euc d → ℝ,
            IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
              (s103nData ((quadraticGradientDyn d s a β).coeff ρ) (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) a' t) u ∧
            F a' t = u 0) ∧
          (∀ a' : Fin 3, ∀ ha : (a' : ℕ) < 2, ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
            ∀ h : ℝ, h ≠ 0 → |h| < δ → t + h ∈ Set.Icc (0 : ℝ) T0 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
              ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (F a' (t + h) y - F a' t y) - F ⟨(a' : ℕ) + 1, by omega⟩ t y) x‖ ≤ e)

theorem s103n_windowClause_of_termReg {s a β T : ℝ} (hT : 0 < T) {ρβ : Euc d → ℝ} {εstar c₁ C₁ C c : ℝ}
    (hOrb : S103nOrbitClaims d s a β ρβ εstar c₁ C₁ C c) (hR : S103nTermReg d s a β ρβ εstar c₁ C₁) :
    S103nWindowClause d s a β T ρβ εstar c₁ C₁ := by
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨((4 * d + 42 : ℕ) + 1 : ℝ) * s103nM0 T C', fun ε ψ ρ hψ hres α hex b hb n => ?_⟩
  obtain ⟨F, hF0, hFcl, hFdq⟩ := hR ε ψ ρ hψ hres α hex (b + T) (by linarith)
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  set φ := oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α with hφ
  have hb0 := s103_b_nonneg (d := d) α
  have hA : 0 ≤ C' * s103_b d α := mul_nonneg hC'0 hb0
  have hm : C * s103_b d α ≤ C' * s103_b d α := mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  set F' : ℕ → ℝ → Euc d → ℝ := fun a' => if h : a' < 3 then F ⟨a', h⟩ else fun _ _ => 0 with hF'
  have hF'eq : ∀ (a' : ℕ) (h : a' < 3), F' a' = F ⟨a', h⟩ := fun a' h => by simp [hF', h]
  have Hfam : s103_famHyp F' (4 * d + 42) (b + T) (C' * s103_b d α) := by
    have hcb : ∀ a' ≤ 2, ∀ t ∈ Set.Icc (0 : ℝ) (b + T),
        ContDiff ℝ (4 * d + 42 : ℕ) (F' a' t) ∧ r2CbNormE (4 * d + 42) (F' a' t) ≤ ENNReal.ofReal (C' * s103_b d α) := by
      intro a' ha t ht
      obtain ⟨u, hu, hFu⟩ := hFcl ⟨a', by omega⟩ t ht
      obtain ⟨c1, c2, c3, c4, c5⟩ := hOrb ε ψ ρ hψ hres α t ht.1
      rw [hF'eq a' (by omega), hFu]
      interval_cases a'
      · exact s103_orbitSup_mono c1 hm u hu 0 ⟨le_rfl, ht.1⟩
      · exact s103_orbitSup_mono c3 hm u hu 0 ⟨le_rfl, ht.1⟩
      · exact s103_orbitSup_mono c5 hm u hu 0 ⟨le_rfl, ht.1⟩
    refine ⟨fun a' ha t ht => (hcb a' ha t ht).1, fun a' ha t ht j hj x =>
      s103_cb_of_E hA (hcb a' ha t ht).2 j hj x, fun a' ha t ht e he => ?_⟩
    obtain ⟨δ, hδ, hh⟩ := hFdq ⟨a', by omega⟩ (by simpa using ha) t ht e he
    refine ⟨δ, hδ, fun h h0 hd' ht' j hj x => ?_⟩
    rw [hF'eq a' (by omega), hF'eq (a' + 1) (by omega)]
    exact hh h h0 hd' ht' j hj x
  have hF0' : ∀ τ ∈ Set.Icc (0 : ℝ) (b + T), F' 0 τ = propagatorW Cf 0 τ φ := by
    intro τ hτ
    rw [hF'eq 0 (by norm_num)]
    exact hF0 τ hτ
  obtain ⟨w1, w2⟩ := s103n_window_of_famHyp hT hC'0 Hfam hb hF0' n
  refine ⟨w1, w2.trans (le_of_eq ?_)⟩
  rfl

/-- `R2WinOrbED13` from the single analytic input `S103nTermReg` (the terminal-time regularity of the nonlinear adjoint orbit). -/
theorem s103n_tie_of_termReg (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) (hT : 0 < T)
    (hR : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ εstar c₁ C₁ : ℝ,
      0 < εstar → 0 < c₁ → S103nTermReg d s a β ρβ εstar c₁ C₁) :
    R2WinOrbED13 d s a β T :=
  s103n_tie hd s hs0 hs a β ha hβ T hT fun ρβ hρ εstar c₁ C₁ C c hε hc₁ _ hOrb =>
    s103n_windowClause_of_termReg hT hOrb (hR ρβ hρ εstar c₁ C₁ hε hc₁)

end HRS.MS.R2WinOrbNL

end
