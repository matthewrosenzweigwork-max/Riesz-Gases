import HRS.MC.L5566Aux2

/-!
# Packet L5566, auxiliary 3: differentiability off the lattice, the lower bound and the Lipschitz step
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.L5566

open HRS

variable {d : ℕ}

/-- The point `τ e_i`. -/
def l5566_pt (i : Fin d) (τ : ℝ) : Euc d := τ • EuclideanSpace.single i (1 : ℝ)

lemma l5566_pt_apply (i : Fin d) (τ : ℝ) : (l5566_pt i τ) i = τ := by
  simp [l5566_pt]

lemma l5566_dot_pt (k : Lattice d) (i : Fin d) (τ : ℝ) :
    Lattice.dot k (l5566_pt i τ) = (k i : ℝ) * τ := by
  simp [Lattice.dot, l5566_pt, EuclideanSpace.single_apply]

lemma l5566_differentiableAt {s c : ℝ} (hs : s < 0) (hc : 0 < c) (i : Fin d) {y : Euc d}
    (hy : Real.cos (2 * Real.pi * y i) ≠ 1) :
    DifferentiableAt ℝ (Torus.lift (negSpectralKernel d s c)) y := by
  set h : Euc d → ℝ := fun z => Real.cos (2 * Real.pi * z i) - 1 with hh
  have hproj : Differentiable ℝ (fun z : Euc d => z i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).differentiable
  have hD : Differentiable ℝ h := by
    refine Differentiable.sub ?_ (differentiable_const _)
    exact Real.differentiable_cos.comp (hproj.const_mul _)
  have hcont : Continuous h := hD.continuous
  have hy0 : h y ≠ 0 := by
    simp only [hh]; intro h0; exact hy (by linarith)
  have hev : ∀ᶠ z in 𝓝 y, h z ≠ 0 := hcont.continuousAt.eventually_ne hy0
  have heq : Torus.lift (negSpectralKernel d s c) =ᶠ[𝓝 y] fun z => l5566_F d s c i z * (h z)⁻¹ := by
    filter_upwards [hev] with z hz
    rw [eq_mul_inv_iff_mul_eq₀ hz]
    exact l5566_identity hs c i z
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact ((l5566_F_differentiable hs hc i) y).mul ((hD y).inv hy0)

lemma l5566_card_box (i : Fin d) (M : ℕ) :
    M ^ d ≤ (Fintype.piFinset (fun j : Fin d => if j = i then Finset.Icc (M : ℤ) (2 * M)
        else Finset.Icc (-(M : ℤ)) M)).card := by
  rw [Fintype.card_piFinset]
  calc M ^ d = ∏ _j : Fin d, M := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod' 
      intro j _
      split_ifs <;> simp <;> omega

lemma l5566_lower {s c : ℝ} (hs : s < 0) (hc : 0 < c) (hd : 1 ≤ d) (i : Fin d) (M : ℕ) (hM : 1 ≤ M) :
    c * (4 * Real.pi * d) ^ (s - d) * (M : ℝ) ^ s ≤
      Torus.lift (negSpectralKernel d s c) 0 -
        Torus.lift (negSpectralKernel d s c) (l5566_pt i (1 / (4 * M))) := by
  set a := negSpectralCoeff d s c with ha
  set τ : ℝ := 1 / (4 * M) with hτ
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : s - d < 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hG0 : Torus.lift (negSpectralKernel d s c) 0 = ∑' k : Lattice d, a k := by
    rw [l5566_lift_eq]; simp [Lattice.dot]; rfl
  have hsum1 : Summable fun k => a k * Real.cos (2 * Real.pi * Lattice.dot k (l5566_pt i τ)) :=
    l5566_summable_a hs c i _ (fun k => Real.abs_cos_le_one _)
  have hdiff : Torus.lift (negSpectralKernel d s c) 0 -
      Torus.lift (negSpectralKernel d s c) (l5566_pt i τ) =
      ∑' k : Lattice d, a k * (1 - Real.cos (2 * Real.pi * ((k i : ℝ) * τ))) := by
    rw [hG0, l5566_lift_eq]
    simp_rw [l5566_dot_pt]
    rw [← (summable_negSpectralCoeff d hs c).tsum_sub (by simpa [l5566_dot_pt] using hsum1)]
    refine tsum_congr (fun k => by ring)
  rw [hdiff]
  set S : Finset (Lattice d) := Fintype.piFinset (fun j : Fin d => if j = i then Finset.Icc (M : ℤ) (2 * M)
        else Finset.Icc (-(M : ℤ)) M) with hS
  have hnn : ∀ k : Lattice d, 0 ≤ a k * (1 - Real.cos (2 * Real.pi * ((k i : ℝ) * τ))) := fun k =>
    mul_nonneg (negSpectralCoeff_nonneg d s hc.le k) (by linarith [Real.cos_le_one (2 * Real.pi * ((k i : ℝ) * τ))])
  have hsm : Summable fun k : Lattice d => a k * (1 - Real.cos (2 * Real.pi * ((k i : ℝ) * τ))) := by
    have := (summable_negSpectralCoeff d hs c).sub (by simpa [l5566_dot_pt] using hsum1)
    refine this.congr (fun k => by ring)
  have hge : ∑ k ∈ S, a k * (1 - Real.cos (2 * Real.pi * ((k i : ℝ) * τ))) ≤
      ∑' k : Lattice d, a k * (1 - Real.cos (2 * Real.pi * ((k i : ℝ) * τ))) :=
    Summable.sum_le_tsum S (fun k _ => hnn k) hsm
  refine le_trans ?_ hge
  -- termwise lower bound on S
  have hterm : ∀ k ∈ S, c * (4 * Real.pi * d * M) ^ (s - d) ≤
      a k * (1 - Real.cos (2 * Real.pi * ((k i : ℝ) * τ))) := by
    intro k hk
    have hk' : ∀ j, k j ∈ (if j = i then Finset.Icc (M : ℤ) (2 * M) else Finset.Icc (-(M : ℤ)) M) :=
      Fintype.mem_piFinset.mp hk
    have hki : (M : ℤ) ≤ k i ∧ k i ≤ 2 * M := by
      have := hk' i; simpa using this
    have hkj : ∀ j, |(k j : ℝ)| ≤ 2 * M := by
      intro j
      have hmem := hk' j
      have key : -(2 * (M : ℤ)) ≤ k j ∧ k j ≤ 2 * (M : ℤ) := by
        by_cases hj : j = i
        · subst hj; simp only [if_true, Finset.mem_Icc] at hmem; omega
        · simp only [hj, if_false, Finset.mem_Icc] at hmem; omega
      have h0 : |k j| ≤ 2 * (M : ℤ) := abs_le.mpr key
      have h := Int.cast_le (R := ℝ) |>.mpr h0
      simpa [Int.cast_abs] using h
    have hk0 : k ≠ 0 := by
      intro h0
      have : (M : ℤ) ≤ 0 := by have := hki.1; rwa [h0, Pi.zero_apply] at this
      omega
    have hen : Lattice.enorm k ≤ 2 * d * M := by
      have h2 : Lattice.enorm k ^ 2 ≤ (2 * d * M) ^ 2 := by
        rw [enorm_sq]
        calc ∑ j, ((k j : ℤ) : ℝ) ^ 2 ≤ ∑ _j : Fin d, (2 * (M : ℝ)) ^ 2 := by
              apply Finset.sum_le_sum; intro j _
              have := hkj j
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = d * (2 * (M : ℝ)) ^ 2 := by simp
          _ ≤ d * d * (2 * (M : ℝ)) ^ 2 := by
              have h0 : (0 : ℝ) ≤ (2 * (M : ℝ)) ^ 2 := by positivity
              have hdd : (d : ℝ) ≤ d * d := by nlinarith
              have := mul_le_mul_of_nonneg_right hdd h0
              linarith
          _ = (2 * d * M) ^ 2 := by ring
      exact le_of_sq_le_sq (by simpa using h2) (by positivity) |>.trans_eq' rfl
    have hen1 : 1 ≤ Lattice.enorm k := one_le_enorm k hk0
    have ha1 : c * (4 * Real.pi * d * M) ^ (s - d) ≤ a k := by
      have : a k = c * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) := by
        simp only [ha, negSpectralCoeff, hk0, if_false]
      rw [this]
      have hπ := Real.pi_pos
      have h := Real.rpow_le_rpow_of_nonpos (x := 2 * Real.pi * Lattice.enorm k)
          (y := 4 * Real.pi * d * M) (by positivity)
          (by nlinarith) hp.le
      exact mul_le_mul_of_nonneg_left h hc.le
    have hcosle : Real.cos (2 * Real.pi * ((k i : ℝ) * τ)) ≤ 0 := by
      have h1 : ((M : ℤ) : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hki.1
      have h2 : (k i : ℝ) ≤ 2 * M := by exact_mod_cast hki.2
      have h1' : (M : ℝ) ≤ (k i : ℝ) := by simpa using h1
      have hτe : 2 * Real.pi * ((k i : ℝ) * τ) = Real.pi * (k i : ℝ) / (2 * M) := by
        rw [hτ]; field_simp; ring
      rw [hτe]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
      · rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
    calc c * (4 * Real.pi * d * M) ^ (s - d) ≤ a k := ha1
      _ = a k * 1 := (mul_one _).symm
      _ ≤ a k * (1 - Real.cos (2 * Real.pi * ((k i : ℝ) * τ))) := by
          gcongr
          · exact negSpectralCoeff_nonneg d s hc.le k
          · linarith
  calc c * (4 * Real.pi * d) ^ (s - d) * (M : ℝ) ^ s
      = (M ^ d : ℕ) * (c * (4 * Real.pi * d * M) ^ (s - d)) := by
        have h1 : (4 * Real.pi * d * M) ^ (s - d) = (4 * Real.pi * d) ^ (s - d) * (M : ℝ) ^ (s - d) :=
          Real.mul_rpow (by have := Real.pi_pos; positivity) hMpos.le
        have h2 : ((M ^ d : ℕ) : ℝ) * (M : ℝ) ^ (s - d) = (M : ℝ) ^ s := by
          push_cast
          rw [← Real.rpow_natCast, ← Real.rpow_add hMpos]; congr 1; ring
        rw [h1, ← h2]; ring
    _ ≤ (S.card : ℝ) * (c * (4 * Real.pi * d * M) ^ (s - d)) := by
        gcongr
        exact_mod_cast l5566_card_box i M
    _ = ∑ _k ∈ S, c * (4 * Real.pi * d * M) ^ (s - d) := by simp
    _ ≤ _ := Finset.sum_le_sum hterm

end HRS.MC.L5566
