import HRS.MS.FldRemTie
import HRS.MS.FldRemAux3
import HRS.MS.OrbFeatAux1

/-!
# S21 packet G (S2.1 (i), the smooth half of `S21Init`), part 1: plan and the `C_b^J` orbit input

Worker S21G.  Target: for the stationary Gibbs law `P_{N,beta}` the centred initial orbit path `s21IP` (WsStatAux34) is within `C sqrt(delta_N)`
in `d_{C_b^2}` of a Gaussian path measure `gamma0 = Phi_* gamma` on `C([0,T];B_m)` whose finite-dimensional laws are
`multivariateGaussian 0 (susceptibilityCov (U^{0,t_i} phi_{alpha_i}, U^{0,t_j} phi_{alpha_j}))` (positive semidefinite).

## Verdict
The smooth half of `S21InitAt` is TRUE and non-vacuous (junk-value audit in `docs`-free form): `smoothDist` is a real `iSup` (junk `0` if unbounded:
not the case for probability measures), `Measure.map` is applied to the measurable map `Phi o featureVec`, the cosine series has summable terms,
`responseInverse` exists for every `C_b^J` datum (`exists_gaussian_feature`), the thermal density is unique (`mv0_rho_eq`), centring at
`meanEmpirical` equals centring at `firstMarginal` (exchangeability).  The fdd covariance is `susceptibilityCov` at the INFINITE combinations
`U^{0,t} phi_alpha = sum_n kappa_n e_n(t) f_{n,alpha}` (continuity of `susceptibilityCov` along uniformly convergent series is part of the proof).
`gamma0` does not depend on `N`; packet H (the `W_1` half) needs the same `gamma0`, hence the structural output `s21g_struct` of WsInitGAux7.

## Route and files (new files only; namespace `HRS.MS.S21`, helpers `s21g_`; about 2.9k lines in total)
* WsInitGAux1 (this file): `S21GOrbit` (orbit data in `C_b^J`, `J = floor(d/2)+3`, with three time derivatives, explicit linear index
  `s52bIdx d s (K0+4)`; the a = 2 datum `L^2 phi_alpha` is `s21g_orbit_ul2`), `s21g_orbit_of_uniq` (adapted from `s53_orbit_of_uniq`).
* WsInitGAux2: scalar time regularity of `D^j G_a(t)(x) v` (`s21g_hasDerivWithin_iter`), double integration by parts against a cosine (`s21g_cos_ibp`).
* WsInitGAux3: differentiation under the time integral (`HRS.MS.PoisSg.sg_iteratedFDeriv_integral`, `s21g_F_memCb`).
* WsInitGAux4: the cosine tests `f_{n,alpha} = r2CosOrbitTest` are in `C_b^J`, `cbNorm_J f_{n,alpha} <= B (1+n)^{-5/4} b_alpha`, summable (`s21g_orbit_cos_full`).
* WsInitGAux5: the stationary instance (`s21g_orbit_stat`, `s21g_stat_cos`) and the product decay `s21g_stat_decay` (for the `W_1` projection tails, packet H).
* WsInitGAux6: transport `K = l2(N x MultiIndex) ~ SeqL2` and the synthesis map `Phi` (`s21gPhi`, `s21gPhi_coord_inner`).
* WsInitGAux7: coordinates of the initial `K`-state `s56k0` (`s21g_k0_eval`), the cosine series in the enumeration, first moment of `meanEmpirical`.
* WsInitGAux8: the particle initial path in the cosine coordinates.
* WsInitGAux9: covariance of the `l2` Gaussian on infinite combinations (`s21g_cov`).
* WsInitGAux10: finite-dimensional laws of a centred Gaussian on a Hilbert space (`s21g_fdd_gaussian`).
* WsInitGAux11: the centred initial path equals `Phi (featureVec phi (firstMarginal P) x)` for every configuration (`s21g_path_eq`).
* WsInitGAux12: the structural output `s21g_struct` (family, Gaussian `gamma`, `Phi`, static conclusion, path identity, fdd laws).
* WsInitGAux13: the smooth half `s21g_init_smooth`; WsInitGAux14: its `S21InitAt` shape `s21g_init_smooth_at` and `s21g_gauss_coord_sq`.

## Interface for packet H (the `W_1` half)
`gamma_0 = gamma.map Phi` does not depend on `N`.  Use `s21g_struct` (path identity `s21IP = Phi o featureVec`, summable family, static conclusion, Gaussian),
`s21g_stat_decay` (`cbNorm_J(phi_k)^2 <= B (1+n)^{-5/2} V_alpha`, `sum V^{2/5} < infty`, the box hypothesis of `s21h_init_w1` after `s21h_box_of_product`)
and `s21g_gauss_coord_sq` (`E z_j^2 <= 4 cbNorm_J(phi_j)^2`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B HRS.MS.S53

variable {d : ℕ}

/-- The difference-quotient property in `C_b^J` (clause of `ul_adjoint_orbit_bounds`), `G' = ∂_τ G`. -/
def S21GDiff (J : ℕ) (T : ℝ) (G G' : ℝ → Euc d → ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → |h| < δ → τ + h ∈ Set.Icc (0 : ℝ) T →
    ∀ j ≤ J, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (G (τ + h) y - G τ y) - G' τ y) x‖ ≤ ε

/-- The orbit input of packet G: `G0 α τ = U_τ φ_α`, `G1 = U_τ L φ_α`, `G2 = U_τ L² φ_α` in `C_b^J` with uniform bounds
`cbNorm J ≤ K b_α` (`b` summable), `∂_τ G0 = G1`, `∂_τ G1 = G2`, `∂_τ G2 = G3` in the `C_b^J` sense, and the identification
`propagatorW C r t φ_α = G0 α (t - r)`. -/
structure S21GOrbit (C : WholeCoeff d) (m T K : ℝ) (J : ℕ) (b : MultiIndex d → ℝ)
    (G0 G1 G2 G3 : MultiIndex d → ℝ → Euc d → ℝ) : Prop where
  hom : ∀ α, ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → propagatorW C r t (oscTestFun m α) = G0 α (t - r)
  mem0 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G0 α τ)
  mem1 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G1 α τ)
  mem2 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G2 α τ)
  mem3 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G3 α τ)
  cb0 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm J (G0 α τ) ≤ K * b α
  cb1 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm J (G1 α τ) ≤ K * b α
  cb2 : ∀ α, ∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm J (G2 α τ) ≤ K * b α
  hK : 0 ≤ K
  b_nonneg : ∀ α, 0 ≤ b α
  b_summable : Summable b
  b_pow : Summable fun α => b α ^ ((4 : ℝ) / 5)
  diff0 : ∀ α, S21GDiff J T (G0 α) (G1 α)
  diff1 : ∀ α, S21GDiff J T (G1 α) (G2 α)
  diff2 : ∀ α, S21GDiff J T (G2 α) (G3 α)

/-- **The datum `L² f` in `H^K_ul` with the linear index `s52bIdx d s (K+4)`.** -/
theorem s21g_orbit_ul2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {θ : Euc d → ℝ}
    (hθ : IsUlCutoff θ) (K : ℕ) (ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (σ : Euc d → Euc d)
    (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) (c : Euc d → Euc d)
    (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) :
    ∃ Cfin : ℝ, 0 ≤ Cfin ∧ ∀ f : SchwartzMap (Euc d) ℝ,
      ulNormE K θ (ul6L s Q ν c ρ f 2) ≤
        ENNReal.ofReal (Cfin * oscNorm ((s52bIdx d s (K + 4) : ℕ) : ℝ) f) := by
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) s (K + 4)
  obtain ⟨ψ, hψ⟩ := hρ
  have hρr : UlRapid ρ := by rw [← hψ]; exact ult_schwartz_rapid ψ
  choose φ hφ using hσ
  have hσr : ∀ i, UlRapid (fun x => σ x i) := fun i => by rw [← hφ i]; exact ult_schwartz_rapid (φ i)
  obtain ⟨C2, hC20, hC2⟩ := ul6_L_step (by omega) hs0 hsd ν Q hρr hσr hc K
  obtain ⟨C3, hC30, hC3⟩ := ul6_L_step (by omega) hs0 hsd ν Q hρr hσr hc (K + 2)
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S hθ K
  refine ⟨Cu * (C2 * (C3 * C1)), by positivity, fun f => ?_⟩
  have hdec : ∀ a : ℕ, UlSym (-(s + 1)) (ul6L s Q ν c ρ f a) := fun a => by
    obtain ⟨hcd0, hdec0, _⟩ := orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f a
    refine ⟨hcd0, fun m' => ?_⟩
    obtain ⟨C, hC0, hC⟩ := hdec0 m'
    refine ⟨C, hC0, fun x => ?_⟩
    rw [show -(s + 1) - (m' : ℝ) = -(s + 1 + (m' : ℝ)) by ring]
    exact hC x
  have hS0 := hC3 _ _ (hdec 0) (hC1 f)
  have hS1 := hC2 _ _ (hdec 1) (by
    have e : ul6L s Q ν c ρ f 1 = fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0
        (ul6L s Q ν c ρ f 0) x := by rw [ul6L_succ]
    rw [e]; exact hS0)
  have hcd2 : ContDiff ℝ ∞ (ul6L s Q ν c ρ f 2) :=
    (orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f 2).1
  have e2 : ul6L s Q ν c ρ f 2 = fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0
      (ul6L s Q ν c ρ f 1) x := by rw [ul6L_succ]
  have h1 := hCu (-(s + 1)) _ _ (by linarith) hcd2 (by rw [e2]; exact hS1)
  refine h1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-- The orbit input of packet G for a fixed-viscosity coefficient, conditional on the uniqueness of classical adjoint solutions
(`S52bUniq`) and the index condition `m - s52bIdx d s (K0+4) > 3d`; `K0` is any level with `4 + d/2 < K0` and `J + d/2 < K0`. -/
theorem s21g_orbit_of_uniq {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}
    (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) (m : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (huniq : S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T) (J K0 : ℕ)
    (hK4 : (4 : ℝ) + (d : ℝ) / 2 < K0) (hkK : (J : ℝ) + (d : ℝ) / 2 < K0)
    (hJm : ((s52bIdx d s (K0 + 4) : ℕ) : ℝ) + 3 * d < m) :
    ∃ (b : MultiIndex d → ℝ) (K : ℝ) (G0 G1 G2 G3 : MultiIndex d → ℝ → Euc d → ℝ),
      S21GOrbit (fixedViscosityCoeff s (-1) Q ν c ρ) m T K J b G0 G1 G2 G3 := by
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
  refine ⟨fun α => oscEigenvalue d α ^ (((I : ℝ) - m) / 2), Ccb * max (max Cf0 Cf1) Cf2,
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

end HRS.MS.S21
