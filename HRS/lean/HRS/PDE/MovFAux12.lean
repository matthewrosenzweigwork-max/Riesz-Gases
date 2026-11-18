import HRS.PDE.MovFAux11

/-!
# MOVF Aux12: bridge `movT_isC12Test_of_weak`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_isC12Test_of_weak {D : DynData d} {T Λ lam₀ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hM : D.M = -1) (hβ : 0 < D.invβ) (hV : Torus.IsCk (PDE.mStar d + 2) D.V)
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF (PDE.mStar d + 2) Λ T ρ)
    (hpos : 0 < lam₀ ∧ ∀ t ∈ Set.Icc 0 T, ∀ x, lam₀ ≤ ρ t x) :
    ∃ ρt : ℝ → Torus d → ℝ, IsC12Test T ρ ρt := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨_, movf_isC12_empty hT ρ⟩
  have hd1 : 1 ≤ d := b15_one_le_d D
  set n : ℕ := PDE.mStar d + 2 with hn
  have hn3 : 3 ≤ n := by
    have : 3 ≤ PDE.mStar d := by unfold PDE.mStar; omega
    omega
  have hV2 : Torus.IsCk 2 D.V := mova_isCk_of_le (by exact_mod_cast (by omega : 2 ≤ n)) hV
  have hreg3 : IsRegularMF 3 Λ T ρ := fun t ht =>
    ⟨mova_isCk_of_le (by exact_mod_cast hn3) (hreg t ht).1,
      (KernelGrad.cbNorm_mono hn3).trans (hreg t ht).2⟩
  have W := MFWeak.of_regular hmf hreg3
  have hck : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (ρ r) := fun r hr =>
    mova_isCk_of_le (by exact_mod_cast (by omega : 2 ≤ n)) (hreg r hr).1
  have hρc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (ρ r) := fun r hr => mova_continuous_of_isCk (hck r hr)
  -- continuity of the pairings
  have hpair : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      ContinuousOn (fun r => pair (withDensityReal (ρ r)) ψ) (Set.Icc 0 T) := by
    intro ψ hψ
    obtain ⟨K, hK0, hK⟩ := pair_lipschitz_time hd1 hV2 hT W hψ
    refine LipschitzOnWith.continuousOn (K := K.toNNReal) ?_
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    exact hK b hb a ha
  -- coordinate continuity
  have hcoord : ∀ k : Lattice d, ContinuousOn (fun τ => PDE.coeffOf (ρ τ) k) (Set.Icc 0 T) := by
    intro k
    have h1 := hpair _ (mova_isCk_two_of_smooth (d1_isSmooth_cosMode (-k)))
    have h2 := hpair _ (mova_isCk_two_of_smooth (d1_isSmooth_sinMode (-k)))
    have hcomb : ContinuousOn (fun τ => ((pair (withDensityReal (ρ τ)) (Torus.cosMode (-k)) : ℝ) : ℂ) +
        ((pair (withDensityReal (ρ τ)) (Torus.sinMode (-k)) : ℝ) : ℂ) * Complex.I) (Set.Icc 0 T) :=
      (Complex.continuous_ofReal.comp_continuousOn h1).add
        ((Complex.continuous_ofReal.comp_continuousOn h2).mul (continuousOn_const (c := Complex.I)))
    refine hcomb.congr ?_
    intro τ hτ
    exact movf_coeffOf_eq_pair (hmf.density τ hτ) (hρc τ hτ) k
  -- the Sobolev bound
  set σ : ℝ := (n : ℝ) - 1 with hσ
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) T, PDE.MemHs (σ + 1) (PDE.coeffOf (ρ τ)) := by
    intro τ hτ
    have := (PDE.memHs_coeffOf_cbNorm n (ρ τ) (hreg τ hτ).1).1
    have e : σ + 1 = (n : ℝ) := by rw [hσ]; ring
    rw [e]; exact this
  set Bs : ℝ := ((d : ℝ) + 1) ^ n * ((PDE.multiIndices d n).card : ℝ) * Λ ^ 2 with hBs
  have hB : ∀ τ ∈ Set.Icc (0 : ℝ) T, PDE.hsNormSq (σ + 1) (PDE.coeffOf (ρ τ)) ≤ Bs := by
    intro τ hτ
    have h := (PDE.memHs_coeffOf_cbNorm n (ρ τ) (hreg τ hτ).1).2
    have e : σ + 1 = (n : ℝ) := by rw [hσ]; ring
    rw [e]
    refine h.trans ?_
    have h0 : 0 ≤ Torus.cbNorm n (ρ τ) := KernelGrad.cbNorm_nonneg' _ n
    have hΛ := (hreg τ hτ).2
    have : Torus.cbNorm n (ρ τ) ^ 2 ≤ Λ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hcont := PDE.TRB.continuousInHs_of_bdd (σ := σ) (δ := 1) one_pos Bs hmem hB hcoord
  -- Sobolev embedding
  have hσd : (d : ℝ) / 2 + 2 < σ := by
    have h1 : (d : ℝ) / 2 + 2 < ((PDE.mStar d : ℕ) : ℝ) - 0 := by
      unfold PDE.mStar
      have := Nat.lt_floor_add_one ((d : ℝ) / 2)
      push_cast
      linarith
    rw [hσ, hn]
    push_cast
    linarith
  obtain ⟨Ce, hCe⟩ := PDE.toFun_isCk_le (d := d) 2 σ hσd
  have hKd : (d : ℝ) / 2 < σ := by linarith
  have hrate : ∀ r₀ : Set.Icc (0 : ℝ) T, Tendsto (fun r : Set.Icc (0 : ℝ) T =>
      Torus.cbNorm 2 (fun x => ρ r.1 x - ρ r₀.1 x)) (𝓝 r₀) (𝓝 0) := by
    intro r₀
    have h1 := hcont.2 r₀.1 r₀.2
    have h2 : Tendsto (fun r : Set.Icc (0 : ℝ) T => (r.1 : ℝ)) (𝓝 r₀) (𝓝[Set.Icc 0 T] r₀.1) :=
      tendsto_nhdsWithin_iff.2 ⟨continuous_subtype_val.tendsto _, Eventually.of_forall fun r => r.2⟩
    have h3 := ((h1.comp h2).const_mul Ce)
    rw [mul_zero] at h3
    refine squeeze_zero (fun r => KernelGrad.cbNorm_nonneg' _ 2) (fun r => ?_) h3
    have hg : Continuous fun x => ρ r.1 x - ρ r₀.1 x := (hρc r.1 r.2).sub (hρc r₀.1 r₀.2)
    have hcoef : PDE.coeffOf (fun x => ρ r.1 x - ρ r₀.1 x) =
        PDE.coeffOf (ρ r.1) - PDE.coeffOf (ρ r₀.1) := by
      have := PDE.ClassicalAux.coeffOf_sub (mova_int_cont (hρc r.1 r.2)) (mova_int_cont (hρc r₀.1 r₀.2))
      rw [this]; rfl
    have hmem' : PDE.MemHs σ (PDE.coeffOf (ρ r.1) - PDE.coeffOf (ρ r₀.1)) :=
      PDE.MFApriori.Aux.memHs_sub ((hmem r.1 r.2).mono (by linarith)) ((hmem r₀.1 r₀.2).mono (by linarith))
    have hsum : Summable fun k => ‖PDE.coeffOf (fun x => ρ r.1 x - ρ r₀.1 x) k‖ := by
      rw [hcoef]; exact PDE.summable_norm_of_memHs σ hKd _ hmem'
    have e : PDE.toFun (PDE.coeffOf (ρ r.1) - PDE.coeffOf (ρ r₀.1)) = fun x => ρ r.1 x - ρ r₀.1 x := by
      rw [← hcoef]; exact PDE.MFThermalReg.toFun_coeffOf hg hsum
    have hreal : PDE.IsRealCoeff (PDE.coeffOf (ρ r.1) - PDE.coeffOf (ρ r₀.1)) := by
      rw [← hcoef]; exact PDE.isRealCoeff_coeffOf _ (mova_int_cont hg)
    have := (hCe _ hmem' hreal).2
    rw [e] at this
    calc Torus.cbNorm 2 (fun x => ρ r.1 x - ρ r₀.1 x) ≤
        Ce * PDE.hsNorm σ (PDE.coeffOf (ρ r.1) - PDE.coeffOf (ρ r₀.1)) := this
      _ = Ce * PDE.hsNorm σ (PDE.coeffOf (ρ r.1) - PDE.coeffOf (ρ r₀.1)) := rfl
  have hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2 :=
    fun j hj => movf_joint_cont hck hrate j hj
  exact movf_isC12_core D hM hV2 hT hmf hck hcc

end HRS

end
