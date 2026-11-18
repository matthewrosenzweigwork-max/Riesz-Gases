import HRS.MS.OrbFeatAux1
import HRS.MS.GoFeatTie

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S52B

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Go

variable {d : ℕ}

open Classical in
theorem s52b_prop_isClassical {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) :
    IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ) := by
  have : (fun r => propagatorW C r t φ) = h.choose := by
    funext r; unfold propagatorW; rw [dif_pos h]
  rw [this]
  exact h.choose_spec

/-- **The missing uniqueness statement** (the gap of the frozen row `orbit_feature_bounded`): classical adjoint
solutions (`IsClassicalAdjointW`) with the same terminal datum agree on `[0,t]`, for every `t ∈ [0,T]`. -/
def S52bUniq (C : WholeCoeff d) (T : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ (φ : Euc d → ℝ) (f₁ f₂ : ℝ → Euc d → ℝ),
    IsClassicalAdjointW C t φ f₁ → IsClassicalAdjointW C t φ f₂ → ∀ r ∈ Icc (0 : ℝ) t, f₁ r = f₂ r

theorem s52b_gen_const (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d) (ρ : Euc d → ℝ)
    (t : ℝ) (φ : Euc d → ℝ) :
    generatorW (fixedViscosityCoeff s M Q ν c ρ) t φ = generatorW (fixedViscosityCoeff s M Q ν c ρ) 0 φ := rfl

/-- identification of the adjoint propagator with the fixed-horizon `UL` evolution -/
theorem s52b_prop_eq {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}
    (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) {K : ℕ} (hK : (4 : ℝ) + (d : ℝ) / 2 < K)
    {T : ℝ} (hT : 0 ≤ T) (huniq : S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T)
    {g : Euc d → ℝ} (hg : UlClosure K θ g) :
    ∃ w : ℝ → Euc d → ℝ, IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) T g w ∧
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
        propagatorW (fixedViscosityCoeff s (-1) Q ν c ρ) r t g = w (r + (T - t)) := by
  obtain ⟨Cev, hCev⟩ := ul_evolution_exists O.hs0 O.hsd θ O.hθ K hK T ν hT O.hν Q (-1) ρ O.hρ c O.smooth
  obtain ⟨w, hw, -⟩ := hCev T ⟨hT, le_rfl⟩ g hg
  refine ⟨w, hw, fun r t hr hrt htT => ?_⟩
  have hδ : T - t ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hv := ul6_shift s (-1) Q ν c ρ hδ hw
  rw [show T - (T - t) = t by ring] at hv
  have hcl := hv.classicalSol
  have hprop := s52b_prop_isClassical ⟨_, hcl⟩
  exact huniq t ⟨hr.trans hrt, htT⟩ g _ _ hprop hcl r ⟨hr, hrt⟩


theorem s52b_cont_grad {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (a : Fin d) (x : Euc d) :
    ContinuousOn (fun r => gradComp a (f r) x) (Icc 0 t) := by
  have h := hf.cont_c2 1 (by norm_num)
  have e : (fun r : Icc (0 : ℝ) t => gradComp a (f r) x) = fun r : Icc (0 : ℝ) t =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ (fun _ => EuclideanSpace.single a (1 : ℝ)))
        (iteratedFDeriv ℝ 1 (f r) x) := by
    funext r
    simp only [ContinuousMultilinearMap.apply_apply, iteratedFDeriv_one_apply, gradComp,
      movtr_gradient_apply]
  rw [continuousOn_iff_continuous_domRestrict]
  show Continuous fun r : Icc (0 : ℝ) t => gradComp a (f r) x
  rw [e]
  have hp : Continuous fun r : Icc (0 : ℝ) t => ((r, x) : Icc (0 : ℝ) t × Euc d) :=
    continuous_id.prodMk continuous_const
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
    (fun _ => EuclideanSpace.single a (1 : ℝ))).continuous.comp (h.comp hp)


/-- the level `K` of the orbit bound for `C_b^{n+1}` -/
def s52bK (d n : ℕ) : ℕ := n + 1 + ⌊(d : ℝ) / 2⌋₊ + 1

theorem s52bK_gt (n : ℕ) : ((n + 1 : ℕ) : ℝ) + (d : ℝ) / 2 < (s52bK d n : ℕ) := by
  unfold s52bK
  push_cast
  have := Nat.lt_floor_add_one ((d : ℝ) / 2)
  linarith

/-- **The orbit coordinates `∂_a U(r,t) L φ_α`** (conditional on uniqueness): `C^n` with the bound
`Co · λ_α^{(J-m)/2}`, `J = s52bIdx d s (K+2)`, and continuity in `t`. -/
theorem s52b_orbit_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (n : ℕ)
    (hn : (d : ℝ) / 2 + 6 < ((n + 1 : ℕ) : ℝ)) (m : ℝ) {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (σ : Euc d → Euc d) (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) (c : Euc d → Euc d)
    (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x)
    (huniq : S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T) :
    ∃ Co : ℝ, 0 ≤ Co ∧ ∀ (α : MultiIndex d) (a : Fin d),
      (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
        ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (propagatorW (fixedViscosityCoeff s (-1) Q ν c ρ)
          r t (generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) t (oscTestFun m α))) x) ∧
        ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a (propagatorW
          (fixedViscosityCoeff s (-1) Q ν c ρ) r t
          (generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) t (oscTestFun m α))) x) x‖ ≤
            Co * oscEigenvalue d α ^ ((((s52bIdx d s (s52bK d n + 2) : ℕ) : ℝ) - m) / 2)) ∧
      (∀ r ∈ Icc (0 : ℝ) T, ∀ x, ContinuousOn (fun t => gradComp a (propagatorW
          (fixedViscosityCoeff s (-1) Q ν c ρ) r t
          (generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) t (oscTestFun m α))) x) (Icc r T)) := by
  set K : ℕ := s52bK d n with hK
  have hkK : ((n + 1 : ℕ) : ℝ) + (d : ℝ) / 2 < K := s52bK_gt n
  have hK4 : (4 : ℝ) + (d : ℝ) / 2 < K := by
    have : (6 : ℝ) < ((n + 1 : ℕ) : ℝ) + (d : ℝ) / 2 := by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith
    linarith
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have O : UlOrb d s ν ρ σ c θ := ⟨hd, hs0, hsd, hν, hρ, hσ, hc, hθ⟩
  obtain ⟨Cfin, hCfin0, hCfin⟩ := s52b_orbit_ul1 hd hs0 hsd hθ K ν Q ρ hρ σ hσ c hc
  obtain ⟨Ccb, hCcb0, hCcb⟩ := ul6_cb_bound O Q hK4 hkK T hT
  refine ⟨Ccb * Cfin, by positivity, fun α a => ?_⟩
  obtain ⟨f, hf, hfN⟩ := s52b_phi (d := d) m α
  set J : ℕ := s52bIdx d s (K + 2) with hJ
  set Cf := fixedViscosityCoeff s (-1) Q ν c ρ with hCf
  set g : Euc d → ℝ := ul6L s Q ν c ρ f 1 with hg
  have hgdef : ∀ t : ℝ, generatorW Cf t (oscTestFun m α) = g := by
    intro t
    have e : ul6L s Q ν c ρ f 1 = generatorW Cf 0 (⇑f) := by
      rw [ul6L_succ]; rfl
    rw [hg, e, hf, s52b_gen_const]
  have hgcl : UlClosure K θ g := ul6_closure O Q f 1 K
  obtain ⟨w, hw, hprop⟩ := s52b_prop_eq O Q hK4 hT huniq hgcl
  -- bound of the datum
  have hgnorm : (ulNormE K θ g).toReal ≤ Cfin * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
    have h1 := hCfin f
    have hnn : 0 ≤ Cfin * oscNorm (J : ℝ) f := mul_nonneg hCfin0 (Real.sqrt_nonneg _)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal hnn, hfN J] at h2
    exact h2
  refine ⟨fun r t hr hrt htT => ?_, fun r hr x => ?_⟩
  · have hδ : r + (T - t) ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
    have hv := ul6_shift s (-1) Q ν c ρ hδ hw
    obtain ⟨-, hmem, hnb⟩ := hCcb (T - (r + (T - t))) ⟨by linarith, by linarith⟩ g hgcl K le_rfl _ hv
    have hP : propagatorW Cf r t (generatorW Cf t (oscTestFun m α)) = w (r + (T - t)) := by
      rw [hgdef t]; exact hprop r t hr hrt htT
    simp only [zero_add] at hmem hnb
    rw [hP]
    have hU := hmem.1
    obtain ⟨hc', hbd⟩ := s55f_gradComp (n := n) hU a
    refine ⟨hc', fun j hj x => (hbd j hj x).trans ?_⟩
    have hsup : ‖iteratedFDeriv ℝ (j + 1) (w (r + (T - t))) x‖ ≤ cbNorm (n + 1) (w (r + (T - t))) := by
      unfold cbNorm
      have hbdd := hmem.2 (j + 1) (by omega)
      have h1 : ‖iteratedFDeriv ℝ (j + 1) (w (r + (T - t))) x‖ ≤
          ⨆ z, ‖iteratedFDeriv ℝ (j + 1) (w (r + (T - t))) z‖ := le_ciSup hbdd x
      refine h1.trans ?_
      exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i (w (r + (T - t))) z‖)
        (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    refine hsup.trans (hnb.trans ?_)
    calc Ccb * (ulNormE K θ g).toReal ≤ Ccb * (Cfin * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) :=
          mul_le_mul_of_nonneg_left hgnorm hCcb0
      _ = _ := by ring
  · have hc0 : ContinuousOn (fun τ => gradComp a (w τ) x) (Icc 0 T) :=
      s52b_cont_grad hw.classicalSol a x
    have hlin : ContinuousOn (fun t : ℝ => r + (T - t)) (Icc r T) := by fun_prop
    have hmaps : MapsTo (fun t : ℝ => r + (T - t)) (Icc r T) (Icc 0 T) := fun t ht =>
      ⟨by linarith [ht.2, hr.1], by linarith [ht.1]⟩
    refine (hc0.comp hlin hmaps).congr fun t ht => ?_
    have hP : propagatorW Cf r t (generatorW Cf t (oscTestFun m α)) = w (r + (T - t)) := by
      rw [hgdef t]; exact hprop r t hr.1 ht.1 ht.2
    simp only [Function.comp, hP]

end HRS.MS.S52B
