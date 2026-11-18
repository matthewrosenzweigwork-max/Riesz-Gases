import HRS.MS.FixEqP2Aux8

/-!
# S5.7 `fixed_equation` (worker S57P), part 12: the difference estimate for the adjoint orbits (packet P1)

`s57p_diff_bound`: for the coefficients `fixedEqCoeff s M Q ν c ρ` and `fixedEqCoeff s M Q νN cN ρN`, with the uniformly local
adjoint input of the `N`-family through order `n+1` (`UlAdjointInput θ C_N t (n+1) K_N`), uniqueness of classical adjoint solutions
for the `N`-family, and the orbit `f = U^{·,t} ψ` of the limit family bounded in `C^{n+4+⌈d/2⌉}` by `B_f` (the adjoint input of the
limit family through order `n+4+⌈d/2⌉`):
`‖D^i (U - U_N)^{r,t} ψ‖_∞ ≤ t |K_N| C_u C_g (D_ν + D_c + D_ρ) B_f`, `i ≤ n`, with constants independent of the coefficients.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_contOn_of_cont {t : ℝ} {F : ℝ → Euc d → ℝ}
    (h : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => F p.1 p.2) (y : Euc d) :
    ContinuousOn (fun u => F u y) (Set.Icc (0 : ℝ) t) := by
  have hmap : Continuous (fun τ : Set.Icc (0 : ℝ) t => ((τ, y) : Set.Icc (0 : ℝ) t × Euc d)) :=
    continuous_id.prodMk continuous_const
  have h' := h.comp hmap
  intro τ hτ
  exact (continuousWithinAt_iff_continuousAt_restrict (fun u => F u y) hτ).2 h'.continuousAt

theorem s57p_norm_le_cbNorm {m : ℕ} {F : Euc d → ℝ} (hF : HRS.MemCb m F) {j : ℕ} (hj : j ≤ m) (y : Euc d) :
    ‖iteratedFDeriv ℝ j F y‖ ≤ HRS.cbNorm m F := by
  have hbdd := hF.2 j hj
  have h1 : ‖iteratedFDeriv ℝ j F y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j F z‖ := le_ciSup hbdd y
  refine h1.trans ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i F z‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem s57p_diff_bound {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (n : ℕ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν νN : ℝ} {c cN : ℝ → Euc d → Euc d}
      {ρ ρN : ℝ → Euc d → ℝ} {t : ℝ} (ht : 0 ≤ t) (hn4 : 4 ≤ n)
      (hD : S57pFeData s Q ν c ρ t) (hDN : S57pFeData s Q νN cN ρN t)
      (huniqN : HRS.MS.S52B.S52bUniq (fixedEqCoeff s M Q νN cN ρN) t) {KN : ℝ}
      (adjN : UlAdjointInput θ (fixedEqCoeff s M Q νN cN ρN) t (n + 1) KN)
      {K' : ℕ} (hK' : n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3 ≤ K') {L' : ℝ} (hL' : (d : ℝ) + 3 ≤ L') {Dν Dc Dρ : ℝ}
      (hν : |ν - νN| ≤ Dν)
      (hc : ∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ K' (c τ) ∧ ContDiff ℝ K' (cN τ) ∧
        cbNormVecE K' (fun x => c τ x - cN τ x) ≤ ENNReal.ofReal Dc)
      (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ K' (ρ τ) ∧ ContDiff ℝ K' (ρN τ) ∧
        weightedSupE K' L' (fun x => ρN τ x - ρ τ x) ≤ ENNReal.ofReal Dρ)
      {ψ : Euc d → ℝ} {f fN : ℝ → Euc d → ℝ}
      (hf : IsClassicalAdjointW (fixedEqCoeff s M Q ν c ρ) t ψ f)
      (hfN : IsClassicalAdjointW (fixedEqCoeff s M Q νN cN ρN) t ψ fN) {Bf BfN : ℝ}
      (hf4 : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ (n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3 : ℕ) (f r) ∧
        ∀ i ≤ n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3, ∀ x, ‖iteratedFDeriv ℝ i (f r) x‖ ≤ Bf)
      (hfN4 : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 4 (fN r) ∧ ∀ i ≤ 4, ∀ x, ‖iteratedFDeriv ℝ i (fN r) x‖ ≤ BfN),
      ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ n, ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => f r y - fN r y) x‖ ≤
          t * (|KN| * (Cu * (s57pCg d s M (n + 1 + ⌈(d : ℝ) / 2⌉₊) * (max Dν 0 + max Dc 0 + max Dρ 0) * Bf))) := by
  obtain ⟨Cu, hCu0, hCu⟩ := s55_ul_of_sup hθ (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊)
  refine ⟨Cu, hCu0, fun {s} M Q {ν νN c cN ρ ρN t} ht hn4 hD hDN huniqN {KN} adjN {K'} hK' {L'} hL' {Dν Dc Dρ}
    hν hc hρ {ψ f fN} hf hfN {Bf BfN} hf4 hfN4 => ?_⟩
  set e : ℕ := ⌈(d : ℝ) / 2⌉₊ with he
  set CN : WholeCoeff d := fixedEqCoeff s M Q νN cN ρN with hCN
  have hBf0 : 0 ≤ Bf := le_trans (norm_nonneg _) ((hf4 0 ⟨le_rfl, ht⟩).2 0 (by omega) 0)
  have hCg0 := s57pCg_nonneg hD.hs0 M (n + 1 + e)
  set Dt : ℝ := max Dν 0 + max Dc 0 + max Dρ 0 with hDt
  have hDt0 : 0 ≤ Dt := by positivity
  set Kg : ℝ := s57pCg d s M (n + 1 + e) * Dt * Bf with hKg
  have hKg0 : 0 ≤ Kg := by positivity
  have gdiff := s57p_gen_diff M Q hD hDN (n + 1 + e) hK' hL' hν hc hρ
  set g : ℝ → Euc d → ℝ := fun u x => generatorW (fixedEqCoeff s M Q ν c ρ) u (f u) x - generatorW CN u (f u) x with hg
  have hRg : ∀ u ∈ Set.Icc (0 : ℝ) t, RgW (fun _ : Euc d => (1 : ℝ)) (n + 1 + e + 1) Kg (g u) := fun u hu =>
    gdiff u hu Bf (f u) hBf0 (hf4 u hu).1 (fun i hi x => (hf4 u hu).2 i hi x)
  have hreg : ∀ u ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((n + 1 + 1 + e : ℕ) : WithTop ℕ∞) (g u) := by
    intro u hu
    have := (hRg u hu).1
    have e1 : n + 1 + 1 + e = n + 1 + e + 1 := by omega
    rw [e1]; exact this
  have hul : ∀ u ∈ Set.Icc (0 : ℝ) t, ulNormE (n + 1 + 1 + e) θ (g u) ≤ ENNReal.ofReal (Cu * Kg) := by
    intro u hu
    refine hCu (g u) Kg hKg0 (hreg u hu) (fun l hl idx x => ?_)
    refine (s57p_abs_partialDeriv_le idx (g u) x).trans ?_
    have := (hRg u hu).2 l (by omega) x
    simpa using this
  have hfin : ∀ u ∈ Set.Icc (0 : ℝ) t, ulNormE (n + 1 + 1 + e) θ (g u) < ⊤ := fun u hu =>
    lt_of_le_of_lt (hul u hu) ENNReal.ofReal_lt_top
  have hCuKg0 : 0 ≤ Cu * Kg := mul_nonneg hCu0 hKg0
  have hulr : ∀ u ∈ Set.Icc (0 : ℝ) t, (ulNormE (n + 1 + 1 + e) θ (g u)).toReal ≤ Cu * Kg := by
    intro u hu
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hul u hu)
    rwa [ENNReal.toReal_ofReal hCuKg0] at this
  set Borb : ℝ := |KN| * (Cu * Kg) with hBorb
  have hBorb0 : 0 ≤ Borb := by positivity
  have hOrb : S57pOrbFam CN t n Borb g := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      have h1 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW (fixedEqCoeff s M Q ν c ρ) p.1 (f p.1) p.2 :=
        hf.cont_time_deriv
      have h2 := s57p_gen_family_cont ht (s57p_gen_inst M Q hDN) hf
        (fun r hr => ⟨(hf4 r hr).1.of_le (by exact_mod_cast (by omega : 4 ≤ n + 1 + e + 3)),
          fun i hi x => (hf4 r hr).2 i (by omega) x⟩)
      exact (s57p_contOn_of_cont h1 y).sub (s57p_contOn_of_cont h2 y)
    · intro u hu
      obtain ⟨hex, -, -⟩ := adjN 0 u le_rfl hu.1 hu.2 (g u) (hreg u hu) (hfin u hu)
      exact propagatorW_isClassical hex
    · intro u hu r' hr'
      obtain ⟨-, hmem, hcb⟩ := adjN r' u hr'.1 hr'.2 hu.2 (g u) (hreg u hu) (hfin u hu)
      refine ⟨hmem.1, fun j hj y => ?_⟩
      refine (s57p_norm_le_cbNorm hmem hj y).trans (hcb.trans ?_)
      calc KN * (ulNormE (n + 1 + 1 + e) θ (g u)).toReal ≤ |KN| * (ulNormE (n + 1 + 1 + e) θ (g u)).toReal :=
            mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
        _ ≤ |KN| * (Cu * Kg) := mul_le_mul_of_nonneg_left (hulr u hu) (abs_nonneg _)
  exact s57p_diff_of_orb ht (s57p_gen_inst M Q hDN) (s57p_lin_inst M Q hDN) huniqN hf hfN
    (fun r hr => ⟨(hf4 r hr).1.of_le (by exact_mod_cast (by omega : 4 ≤ n + 1 + e + 3)),
      fun i hi x => (hf4 r hr).2 i (by omega) x⟩) hfN4 hn4 hBorb0 hOrb

end HRS.MS.FixEq
