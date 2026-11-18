import HRS.MS.WsInitGAux5

/-!
# S21 packet K, part 1: the orbit data with the explicit weight `b_alpha = lambda_alpha^{(I-m)/2}`

`s21g_orbit_of_uniq` (WsInitGAux1) only records the existence of a summable weight `b`; the `W_1` projection tails of packet H need the explicit
decay `b_alpha = lambda_alpha^{(I-m)/2}`.  `s21k_orbit_of_uniq` and `s21k_orbit_stat` restate the construction with `b` explicit (the proof is the
construction of `s21g_orbit_of_uniq`, with the witness `b` named in the statement).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B HRS.MS.S53

variable {d : ℕ}

/-- The orbit input of packet G for a fixed-viscosity coefficient, conditional on the uniqueness of classical adjoint solutions
(`S52bUniq`) and the index condition `m - s52bIdx d s (K0+4) > 3d`; `K0` is any level with `4 + d/2 < K0` and `J + d/2 < K0`. -/
theorem s21k_orbit_of_uniq {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}
    (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) (m : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (huniq : S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T) (J K0 : ℕ)
    (hK4 : (4 : ℝ) + (d : ℝ) / 2 < K0) (hkK : (J : ℝ) + (d : ℝ) / 2 < K0)
    (hJm : ((s52bIdx d s (K0 + 4) : ℕ) : ℝ) + 3 * d < m) :
    ∃ (K : ℝ) (G0 G1 G2 G3 : MultiIndex d → ℝ → Euc d → ℝ),
      S21GOrbit (fixedViscosityCoeff s (-1) Q ν c ρ) m T K J
        (fun α => oscEigenvalue d α ^ ((((s52bIdx d s (K0 + 4) : ℕ) : ℝ) - m) / 2)) G0 G1 G2 G3 := by
  set Cf := fixedViscosityCoeff s (-1) Q ν c ρ with hCf
  set I : ℕ := s52bIdx d s (K0 + 4) with hI
  obtain ⟨Cf0, hCf00, hCf0⟩ := HRS.MS.S53.s53_orbit_ul0 O.hd O.hs0 O.hsd O.hθ K0 ν Q ρ O.hρ σ O.hσ c O.hc
  obtain ⟨Cf1, hCf10, hCf1⟩ := s52b_orbit_ul1 O.hd O.hs0 O.hsd O.hθ K0 ν Q ρ O.hρ σ O.hσ c O.hc
  obtain ⟨Cf2, hCf20, hCf2⟩ := s21g_orbit_ul2 O.hd O.hs0 O.hsd O.hθ K0 ν Q ρ O.hρ σ O.hσ c O.hc
  obtain ⟨Ccb, hCcb0, hCcb⟩ := ul6_cb_bound O Q hK4 hkK T hT
  obtain ⟨Cev, hCev⟩ := ul_evolution_exists O.hs0 O.hsd θ O.hθ K0 hK4 T ν hT O.hν Q (-1) ρ O.hρ c O.smooth
  choose f hf hfN using fun α : MultiIndex d => s52b_phi (d := d) m α
  have hex : ∀ (α : MultiIndex d) (a : Fin 4), ∃ w : ℝ → Euc d → ℝ,
      IsUlBackwardEvolution θ K0 Cf T (ul6L s Q ν c ρ (f α) (a : ℕ)) w := fun α a => by
    obtain ⟨w, hw, -⟩ := hCev T ⟨hT, le_rfl⟩ _ (ul6_closure O Q (f α) (a : ℕ) K0)
    exact ⟨w, hw⟩
  choose w hw using hex
  have hsh : ∀ (α : MultiIndex d) (a : Fin 4), ∀ τ ∈ Icc (0 : ℝ) T,
      IsUlBackwardEvolution θ K0 Cf τ (ul6L s Q ν c ρ (f α) (a : ℕ)) (fun r => w α a (r + (T - τ))) := by
    intro α a τ hτ
    have hδ : T - τ ∈ Icc (0 : ℝ) T := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have := ul6_shift s (-1) Q ν c ρ hδ (hw α a)
    rwa [show T - (T - τ) = τ by ring] at this
  have hpos : ∀ α : MultiIndex d, 0 ≤ oscEigenvalue d α ^ (((I : ℝ) - m) / 2) := fun α =>
    Real.rpow_nonneg (oscEv_pos α).le _
  have hbd : ∀ (α : MultiIndex d) (a : Fin 4) (Cfin : ℝ), 0 ≤ Cfin →
      ulNormE K0 θ (ul6L s Q ν c ρ (f α) (a : ℕ)) ≤ ENNReal.ofReal (Cfin * oscNorm (I : ℝ) (f α)) →
      ∀ τ ∈ Icc (0 : ℝ) T, MemCb J (w α a (T - τ)) ∧
        cbNorm J (w α a (T - τ)) ≤ Ccb * Cfin * oscEigenvalue d α ^ (((I : ℝ) - m) / 2) := by
    intro α a Cfin hC hU τ hτ
    obtain ⟨-, hmem, hnb⟩ := hCcb τ hτ _ (ul6_closure O Q (f α) (a : ℕ) K0) K0 le_rfl _ (hsh α a τ hτ)
    simp only [zero_add] at hmem hnb
    refine ⟨hmem, ?_⟩
    have hnn : 0 ≤ Cfin * oscNorm (I : ℝ) (f α) := mul_nonneg hC (Real.sqrt_nonneg _)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
    rw [ENNReal.toReal_ofReal hnn, hfN α I] at h2
    refine hnb.trans ?_
    calc Ccb * (ulNormE K0 θ (ul6L s Q ν c ρ (f α) (a : ℕ))).toReal
        ≤ Ccb * (Cfin * oscEigenvalue d α ^ (((I : ℝ) - m) / 2)) :=
          mul_le_mul_of_nonneg_left h2 hCcb0
      _ = _ := by ring
  -- the data of `L^a f`, `a ≤ 2`, raised to the common index `I`
  have hI0 : s52bIdx d s (K0 + 2) ≤ I := by rw [hI]; unfold s52bIdx; omega
  have hd0 : ∀ α, ulNormE K0 θ (ul6L s Q ν c ρ (f α) ((0 : Fin 4) : ℕ)) ≤
      ENNReal.ofReal (Cf0 * oscNorm (I : ℝ) (f α)) := fun α => by
    refine (hCf0 (f α)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (ul6_osc_mono hI0 (f α)) hCf00
  have hd1 : ∀ α, ulNormE K0 θ (ul6L s Q ν c ρ (f α) ((1 : Fin 4) : ℕ)) ≤
      ENNReal.ofReal (Cf1 * oscNorm (I : ℝ) (f α)) := fun α => by
    refine (hCf1 (f α)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (ul6_osc_mono hI0 (f α)) hCf10
  have hd2 : ∀ α, ulNormE K0 θ (ul6L s Q ν c ρ (f α) ((2 : Fin 4) : ℕ)) ≤
      ENNReal.ofReal (Cf2 * oscNorm (I : ℝ) (f α)) := fun α => hCf2 (f α)
  have hmem : ∀ (α : MultiIndex d) (a : Fin 4), ∀ τ ∈ Icc (0 : ℝ) T, MemCb J (w α a (T - τ)) := by
    intro α a τ hτ
    obtain ⟨-, hmem, -⟩ := hCcb τ hτ _ (ul6_closure O Q (f α) (a : ℕ) K0) K0 le_rfl _ (hsh α a τ hτ)
    simpa only [zero_add] using hmem
  have hdiff : ∀ (α : MultiIndex d) (a : Fin 4) (ha : (a : ℕ) < 3),
      S21GDiff J T (fun τ => w α a (T - τ)) (fun τ => w α ⟨(a : ℕ) + 1, by omega⟩ (T - τ)) := by
    intro α a ha τ hτ ε hε
    have hF : ∀ (b' : Fin 4), ∀ t ∈ Icc (0 : ℝ) T, ∃ u,
        IsUlBackwardEvolution θ K0 Cf t (ul6L s Q ν c ρ (f α) (b' : ℕ)) u ∧
          (fun τ => w α b' (T - τ)) t = u 0 := fun b' t ht =>
      ⟨_, hsh α b' t ht, by simp⟩
    exact ul6_main_diff O Q hK4 hkK le_rfl hT (f α) (fun b' τ => w α b' (T - τ)) hF a ha τ hτ ε hε
  have hdnn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hJm' : (d : ℝ) < (m - I) / 2 := by linarith
  have hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ (((I : ℝ) - m) / 2) := by
    have h := (summable_oscEigenvalue_rpow_iff (by have := O.hd; omega : 1 ≤ d) ((m - I) / 2)).2 hJm'
    have e : -((m - (I : ℝ)) / 2) = ((I : ℝ) - m) / 2 := by ring
    rwa [e] at h
  have hsum45 : Summable fun α : MultiIndex d => (oscEigenvalue d α ^ (((I : ℝ) - m) / 2)) ^ ((4 : ℝ) / 5) := by
    have h := (summable_oscEigenvalue_rpow_iff (by have := O.hd; omega : 1 ≤ d) ((m - I) * (2 / 5))).2
      (by linarith)
    refine h.congr fun α => ?_
    rw [← Real.rpow_mul (oscEv_pos α).le]
    congr 1; ring
  refine ⟨Ccb * max (max Cf0 Cf1) Cf2,
    fun α τ => w α 0 (T - τ), fun α τ => w α 1 (T - τ), fun α τ => w α 2 (T - τ),
    fun α τ => w α 3 (T - τ), ?_⟩
  have hmax : ∀ C' : ℝ, C' ≤ max (max Cf0 Cf1) Cf2 → ∀ α : MultiIndex d,
      Ccb * C' * oscEigenvalue d α ^ (((I : ℝ) - m) / 2) ≤
        Ccb * max (max Cf0 Cf1) Cf2 * oscEigenvalue d α ^ (((I : ℝ) - m) / 2) := fun C' h α =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hCcb0) (hpos α)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsum, hsum45, ?_, ?_, ?_⟩
  · -- identification
    intro α r t hr hrt htT
    have hv := hsh α 0 t ⟨hr.trans hrt, htT⟩
    have hprop := s52b_prop_isClassical (C := Cf) ⟨_, hv.classicalSol⟩
    have := huniq t ⟨hr.trans hrt, htT⟩ _ _ _ hprop hv.classicalSol r ⟨hr, hrt⟩
    have e0 : oscTestFun m α = ul6L s Q ν c ρ (f α) ((0 : Fin 4) : ℕ) := by
      rw [← hf α]; rfl
    rw [e0]
    refine this.trans ?_
    show w α 0 (r + (T - t)) = w α 0 (T - (t - r))
    congr 1; ring
  · exact fun α τ hτ => hmem α 0 τ hτ
  · exact fun α τ hτ => hmem α 1 τ hτ
  · exact fun α τ hτ => hmem α 2 τ hτ
  · exact fun α τ hτ => hmem α 3 τ hτ
  · intro α τ hτ
    exact ((hbd α 0 Cf0 hCf00 (hd0 α) τ hτ).2).trans (hmax _ (le_trans (le_max_left _ _) (le_max_left _ _)) α)
  · intro α τ hτ
    exact ((hbd α 1 Cf1 hCf10 (hd1 α) τ hτ).2).trans (hmax _ (le_trans (le_max_right _ _) (le_max_left _ _)) α)
  · intro α τ hτ
    exact ((hbd α 2 Cf2 hCf20 (hd2 α) τ hτ).2).trans (hmax _ (le_max_right _ _) α)
  · exact mul_nonneg hCcb0 (le_max_of_le_left (le_max_of_le_left hCf00))
  · exact hpos
  · exact fun α => hdiff α 0 (by norm_num)
  · exact fun α => hdiff α 1 (by norm_num)
  · exact fun α => hdiff α 2 (by norm_num)


/-- The stationary orbit data with the explicit weight `b_α = λ_α^{(I - m)/2}`, `I = s52bIdx d s (K0 + 4)`. -/
theorem s21k_orbit_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ (K : ℝ) (G0 G1 G2 G3 : MultiIndex d → ℝ → Euc d → ℝ),
      S21GOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T K
        (s21gJ d) (fun α => oscEigenvalue d α ^
          ((((s52bIdx d s (s21gK0 d + 4) : ℕ) : ℝ) - ((wholeSpaceIndex d : ℕ) : ℝ)) / 2)) G0 G1 G2 G3 := by
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have hO : UlOrb d s β⁻¹ ρ (fun _ => (0 : Euc d)) (fun x => (fun _ : Euc d => (0 : Euc d)) x -
      convGradConvW (rieszKernelGrad d s) ρ x) θ :=
    ⟨hd, hs0, hsd, hν, hρS.2.elim fun ψ hψ => ⟨ψ, hψ⟩, fun i => ⟨0, by ext x; simp⟩, rfl, hθ⟩
  have huniq := s53_uniq hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hρS T
  rw [s53_coeff_eq] at huniq
  obtain ⟨hK4, hkK⟩ := s21gK0_gt d
  obtain ⟨K, G0, G1, G2, G3, Orb⟩ := s21k_orbit_of_uniq hO (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ)))
    ((wholeSpaceIndex d : ℕ) : ℝ) hT huniq (s21gJ d) (s21gK0 d) hK4 hkK (s21g_index_bound hd s hs0 hsd)
  rw [← s53_coeff_eq, ← s21_dyn_eq] at Orb
  exact ⟨K, G0, G1, G2, G3, Orb⟩

end HRS.MS.S21
