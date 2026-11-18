import HRS.Main.GFEVAux1
import HRS.Main.GFEVAux2
import HRS.Main.GFEVAux3

/-!
# Packet GFEVG, part 4: the PDE input (hold estimate without a viscosity lower bound)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ}

theorem gfev_forward_hold (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (νM l : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (D : DynData d) (T : ℝ) (μ : ℝ → Torus d → ℝ) (m : ℕ) (R : Regime)
      (MB' Λ VB ν₁ : ℝ), AdjointData s m R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → D.invβ ≤ νM →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ (φc : Coeff d) (F : ℝ → Coeff d), IsForwardSolution D μ t φc F →
        ContinuousInHs (a + 2) F t → ContinuousInHs ((m : ℝ) + 2) F t →
        (∀ σ ∈ Set.Icc (0 : ℝ) t, hsNormSq (a + 2) (F σ) ≤ Real.exp (2 * l * σ) * hsNormSq (a + 2) φc) →
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          hsNormSq a (F τ - φc) ≤ B * hsNormSq (a + 2) φc * τ * Real.exp ((1 + 2 * |l|) * τ) := by
  obtain ⟨C₁, hC₁, hgen⟩ := gen_hs_bound s hsd K MB Bμ BV hMB hBμ hBV a hK
  refine ⟨2 * νM ^ 2 + C₁, by positivity, ?_⟩
  intro D T μ m R MB' Λ VB ν₁ hA hG hνM t ht φc F hF hcA hcm hQ τ hτ
  have hc10 : 0 ≤ 2 * D.invβ ^ 2 + C₁ := by positivity
  have hνle : 2 * D.invβ ^ 2 + C₁ ≤ 2 * νM ^ 2 + C₁ := by
    have h0 : 0 ≤ D.invβ := D.hβ
    nlinarith
  obtain ⟨B1, hB10, hB1⟩ := bounded_of_continuousInHs hcA
  -- the datum
  have hφc2 : MemHs (a + 2) φc := by
    have := hcA.1 0 ⟨le_rfl, ht.1.le⟩
    have h0 : F 0 = φc := by
      funext k
      have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
      simpa using this
    rwa [h0] at this
  have hφc1 : MemHs 1 φc := by
    have := hF.h1 0 ⟨le_rfl, ht.1.le⟩
    have h0 : F 0 = φc := by
      funext k
      have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
      simpa using this
    rwa [h0] at this
  set w : ℝ → Coeff d := fun σ => F σ - φc with hw
  have hwm : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs (a + 2) (w σ) := fun σ hσ => memHs_sub (hcA.1 σ hσ) hφc2
  have hcw : ContinuousInHs (a + 2) w t := by
    refine ⟨hwm, fun τ₀ hτ₀ => ?_⟩
    have := hcA.2 τ₀ hτ₀
    refine this.congr fun σ => ?_
    simp only [hw]
    congr 1
    funext k; simp
  obtain ⟨Bw, hBw0, hBw⟩ := bounded_of_continuousInHs hcw
  -- derivative of the energy of `w`
  obtain ⟨Kb1, -, hgenσ⟩ : ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs a (forwardGen D (μ (t - σ)) (F σ)) ∧
        hsNormSq a (forwardGen D (μ (t - σ)) (F σ)) ≤ (2 * D.invβ ^ 2 + C₁) * hsNormSq (a + 2) (F σ) := by
    refine ⟨0, le_rfl, fun σ hσ => ?_⟩
    exact hgen D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) (F σ) (hcA.1 σ hσ) (hF.h1 σ hσ)
  have hderiv := hasDeriv_energy_abstract (t := t) a w (fun σ => forwardGen D (μ (t - σ)) (F σ))
    ((2 * D.invβ ^ 2 + C₁) * B1) Bw (by positivity) hBw0 hwm hBw (fun σ hσ => (hgenσ σ hσ).1)
    (fun σ hσ => (hgenσ σ hσ).2.trans (mul_le_mul_of_nonneg_left (hB1 σ hσ) hc10))
    (fun k => continuousOn_coord_of_continuousInHs hcw k)
    (fun k => gen_coord_continuousOn hA ht hcm k)
    (fun k => by
      have := hasDerivWithinAt_of_primitive (gen_coord_continuousOn hA ht hcm k) (φc k) (hF.eq k)
      intro σ hσ
      exact (this σ hσ).sub_const (φc k))
  -- the differential inequality
  set c : ℝ := 2 * νM ^ 2 + C₁ with hc
  have hc0 : 0 ≤ c := by positivity
  set B₀sq : ℝ := c * (Real.exp (2 * |l| * τ) * hsNormSq (a + 2) φc) with hB₀
  have hB0' : 0 ≤ B₀sq := mul_nonneg hc0 (mul_nonneg (Real.exp_pos _).le (hsNormSq_nonnegE _ _))
  have hineq : ∀ σ ∈ Set.Icc (0 : ℝ) τ,
      (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (w σ)).re ≤
        1 * ((1 / 2 : ℝ) * hsNormSq a (w σ)) + B₀sq / 2 := by
    intro σ hσ
    have hσt : σ ∈ Set.Icc (0 : ℝ) t := ⟨hσ.1, hσ.2.trans hτ.2⟩
    have hGσ := hG _ (tsub_mem_Icc ht hσt)
    have h1F := hF.h1 σ hσt
    have hgF := hgen D (μ (t - σ)) hGσ (F σ) (hcA.1 σ hσt) h1F
    have hwa : MemHs a (w σ) := (hwm σ hσt).mono (by linarith)
    have hX := hsNormSq_nonnegE a (w σ)
    have hcs := norm_hsInner_le hgF.1 hwa
    have hre : (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (w σ)).re ≤
        Real.sqrt (hsNormSq a (forwardGen D (μ (t - σ)) (F σ))) * Real.sqrt (hsNormSq a (w σ)) :=
      (Complex.re_le_norm _).trans hcs
    have hφb : hsNormSq a (forwardGen D (μ (t - σ)) (F σ)) ≤ B₀sq := by
      refine hgF.2.trans ?_
      have h2 : 2 * D.invβ ^ 2 + C₁ ≤ c := hνle
      calc (2 * D.invβ ^ 2 + C₁) * hsNormSq (a + 2) (F σ)
          ≤ c * hsNormSq (a + 2) (F σ) := mul_le_mul_of_nonneg_right h2 (hsNormSq_nonnegE _ _)
        _ ≤ c * (Real.exp (2 * l * σ) * hsNormSq (a + 2) φc) :=
            mul_le_mul_of_nonneg_left (hQ σ hσt) hc0
        _ ≤ B₀sq := by
            refine mul_le_mul_of_nonneg_left ?_ hc0
            refine mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonnegE _ _)
            refine Real.exp_le_exp.2 ?_
            calc 2 * l * σ ≤ 2 * |l| * σ := by
                  nlinarith [le_abs_self l, hσ.1]
              _ ≤ 2 * |l| * τ := by
                  have := abs_nonneg l
                  nlinarith [hσ.2]
    have hsq : Real.sqrt (hsNormSq a (forwardGen D (μ (t - σ)) (F σ))) * Real.sqrt (hsNormSq a (w σ)) ≤
        hsNormSq a (w σ) / 2 + B₀sq / 2 := by
      have h1 : Real.sqrt (hsNormSq a (forwardGen D (μ (t - σ)) (F σ))) ≤ Real.sqrt B₀sq :=
        Real.sqrt_le_sqrt hφb
      have h2 : Real.sqrt B₀sq * Real.sqrt (hsNormSq a (w σ)) ≤ hsNormSq a (w σ) / 2 + B₀sq / 2 := by
        nlinarith [sq_nonneg (Real.sqrt B₀sq - Real.sqrt (hsNormSq a (w σ))), Real.sq_sqrt hB0', Real.sq_sqrt hX]
      exact (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)).trans h2
    nlinarith
  have hz := gronwall_aux (t := τ) (y := fun σ => (1 / 2 : ℝ) * hsNormSq a (w σ) + (B₀sq / 2) / 1)
    (y' := fun σ => (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (w σ)).re) 1
    (fun σ hσ => ((hderiv σ ⟨hσ.1, hσ.2.trans hτ.2⟩).mono (Set.Icc_subset_Icc le_rfl hτ.2)).add_const _)
    (fun σ hσ => by
      have := hineq σ hσ
      have e : (1:ℝ) * ((1 / 2 : ℝ) * hsNormSq a (w σ) + B₀sq / 2 / 1) =
          1 * ((1 / 2 : ℝ) * hsNormSq a (w σ)) + B₀sq / 2 := by ring
      rw [e]; exact this) τ ⟨hτ.1, le_rfl⟩
  have hw0 : w 0 = 0 := by
    funext k
    have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
    simp [hw, this]
  have hy0 : hsNormSq a (w 0) = 0 := by rw [hw0]; simp [hsNormSq]
  simp only [hy0, mul_zero, zero_add, div_one, one_mul] at hz
  have hexp : Real.exp τ - 1 ≤ τ * Real.exp τ := by
    have := Real.add_one_le_exp (-τ)
    have h2 : Real.exp (-τ) * Real.exp τ = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos τ, Real.exp_pos (-τ)]
  have hmain : hsNormSq a (w τ) ≤ B₀sq * (Real.exp τ - 1) := by
    nlinarith
  have hfin : hsNormSq a (w τ) ≤ B₀sq * (τ * Real.exp τ) :=
    hmain.trans (mul_le_mul_of_nonneg_left hexp hB0')
  calc hsNormSq a (F τ - φc) = hsNormSq a (w τ) := rfl
    _ ≤ B₀sq * (τ * Real.exp τ) := hfin
    _ = c * hsNormSq (a + 2) φc * τ * (Real.exp (2 * |l| * τ) * Real.exp τ) := by rw [hB₀]; ring
    _ = c * hsNormSq (a + 2) φc * τ * Real.exp ((1 + 2 * |l|) * τ) := by
        rw [← Real.exp_add]; congr 2; ring


theorem gfev_prop_hold (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB)
    (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (νM l : ℝ)
    (J : ℕ) (hJa : a + 2 < J) (hJ3 : (3 : ℝ) < J) (hJm : mStar d ≤ J) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (R : Regime) (MB' Λ VB ν₁ : ℝ) (D : DynData d) (T : ℝ)
      (μ : ℝ → Torus d → ℝ), AdjointData s J R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → D.invβ ≤ νM →
      (∀ {φ : Torus d → ℝ}, Dom J φ → ∀ {u t : ℝ}, 0 ≤ u → u ≤ t → 0 < t → t ≤ T →
        MemSobolev (a + 2) (propagator D μ u t φ) ∧
          sobolevNorm (a + 2) (propagator D μ u t φ) ≤ Real.exp (l * (t - u)) * sobolevNorm (a + 2) φ) →
      ∀ {φ : Torus d → ℝ}, Dom J φ → ∀ {u t : ℝ}, 0 ≤ u → u ≤ t → 0 < t → t ≤ T →
        MemSobolev a (fun x => propagator D μ u t φ x - φ x) ∧
          sobolevNorm a (fun x => propagator D μ u t φ x - φ x) ^ 2 ≤
            B * sobolevNorm (a + 2) φ ^ 2 * (t - u) * Real.exp ((1 + 2 * |l|) * (t - u)) := by
  obtain ⟨B, hB0, hH⟩ := gfev_forward_hold s hsd K MB Bμ BV hMB hBμ hBV a hK νM l
  refine ⟨B, hB0, fun R MB' Λ VB ν₁ D T μ hA hG hνM hq φ hφ u t hu hut ht0 htT => ?_⟩
  have hJ1 : 1 ≤ J := by
    have : (3 : ℝ) < J := hJ3
    exact_mod_cast (by linarith : (1 : ℝ) ≤ J)
  have htm : t ∈ Set.Ioc 0 T := ⟨ht0, htT⟩
  have hutm : u ∈ Set.Icc 0 t := ⟨hu, hut⟩
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJm
    linarith
  have hφa : MemSobolev a φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by linarith)
  have hφa2 : MemSobolev (a + 2) φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by linarith)
  obtain ⟨hprop, hpc⟩ := prop_facts hd s hs0 hsd J hJm R MB' Λ VB D ν₁ T μ hA htm hφ hutm
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB' Λ VB
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  obtain ⟨hsol, hw, -⟩ := hspec D ν₁ T μ hA t htm (coeffOf φ) hφc
  set F := propagatorCoeff D μ J t (coeffOf φ) with hF
  have hcA : ContinuousInHs (a + 2) F t := forward_strong_continuity (J : ℝ) t F hw (a + 2) hJa
  have hA1 : AdjointData s 1 R MB' Λ VB D ν₁ T μ := StabAux.adjointData_mono hJ1 hA
  have hcm : ContinuousInHs (((1 : ℕ) : ℝ) + 2) F t :=
    forward_strong_continuity (J : ℝ) t F hw _ (by push_cast; linarith)
  have hτ : t - u ∈ Set.Icc (0 : ℝ) t := ⟨by linarith, by linarith⟩
  have hQ : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      hsNormSq (a + 2) (F σ) ≤ Real.exp (2 * l * σ) * hsNormSq (a + 2) (coeffOf φ) := by
    intro σ hσ
    have hσu : t - σ ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    obtain ⟨hprop', hpc'⟩ := prop_facts hd s hs0 hsd J hJm R MB' Λ VB D ν₁ T μ hA htm hφ hσu
    obtain ⟨hreal', hsum'⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB' Λ VB D ν₁ T μ hA htm hφ
      (show σ ∈ Set.Icc (0 : ℝ) t from hσ)
    have hcoef' : coeffOf (propagator D μ (t - σ) t φ) = F σ := by
      rw [hprop']; simpa using coeffOf_toFun _ (by simpa using hreal') (by simpa using hsum')
    obtain ⟨hms, hnm⟩ := hq hφ (u := t - σ) (t := t) hσu.1 hσu.2 ht0 htT
    have e1 := (hsNormSq_coeffOf (a + 2) _ hms).2
    have e2 := (hsNormSq_coeffOf (a + 2) φ hφa2).2
    rw [hcoef'] at e1
    rw [e1, e2]
    have hn0 : 0 ≤ sobolevNorm (a + 2) (propagator D μ (t - σ) t φ) := Real.sqrt_nonneg _
    calc sobolevNorm (a + 2) (propagator D μ (t - σ) t φ) ^ 2
        ≤ (Real.exp (l * (t - (t - σ))) * sobolevNorm (a + 2) φ) ^ 2 := by gcongr
      _ = Real.exp (2 * l * σ) * sobolevNorm (a + 2) φ ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hen := hH D T μ 1 R MB' Λ VB ν₁ hA1 hG hνM t htm (coeffOf φ) F hsol hcA hcm hQ (t - u) hτ
  obtain ⟨hreal, hsum⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB' Λ VB D ν₁ T μ hA htm hφ hτ
  have hcoef : coeffOf (propagator D μ u t φ) = F (t - u) := by
    rw [hprop]; exact coeffOf_toFun _ hreal hsum
  have hcd : Continuous (fun x => propagator D μ u t φ x - φ x) := hpc.sub hφ.1
  have hcoefd : coeffOf (fun x => propagator D μ u t φ x - φ x) = fun k => F (t - u) k - coeffOf φ k := by
    have := coeffOf_lin hpc hφ.1 1 (-1)
    have e : (fun x => propagator D μ u t φ x - φ x) =
        fun x => (1 : ℝ) * propagator D μ u t φ x + (-1 : ℝ) * φ x := by funext x; ring
    rw [e, this, hcoef]
    funext k; push_cast; ring
  have hmemA2 : MemHs (a + 2) (F (t - u)) := hcA.1 (t - u) hτ
  have hmemφ2 : MemHs (a + 2) (coeffOf φ) := (hsNormSq_coeffOf (a + 2) φ hφa2).1
  have hmemd : MemHs a (F (t - u) - coeffOf φ) :=
    (memHs_sub hmemA2 hmemφ2).mono (by linarith)
  have hMS : MemSobolev a (fun x => propagator D μ u t φ x - φ x) :=
    memSobolev_of_memHs a _ (ClassicalAux.memLp_two_of_continuous hcd) (by
      rw [hcoefd]; exact hmemd)
  refine ⟨hMS, ?_⟩
  have e1 := (hsNormSq_coeffOf a _ hMS).2
  have e2 := (hsNormSq_coeffOf (a + 2) φ hφa2).2
  rw [hcoefd] at e1
  rw [← e1, ← e2]
  exact hen


end HRS.GF
