import HRS.MS.R26T8AP06a7

/-!
# S8.2 local Newton layer, packet T8A.P06a: Taylor subtraction for sources of negative conormal order
Statement of the Pro contract `r26t8a_negative_taylor`.  Route: the limit jets `T_j` at `0` (P06a (4)-(6), dimension `>= 2`),
the polynomial `P = sum_{l<m} T_l/l! (v,...,v)` with `m = ceil(min(-sigma,k))` (P06a (3)), and a downward induction on `j`
for the remainder `D^j (h - P)` by dyadic mean-value summation (P06a (1)).
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_negative_taylor {d : ℕ} (hd : 2 ≤ d) (k b : ℕ) (hk : 1 ≤ k)
    (sigma : ℝ) (hsigma : sigma < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ h : Euc d → ℝ,
      ContDiffOn ℝ k h {z | z ≠ 0} →
      (∀ j ≤ k, ∀ z, 0 < ‖z‖ → ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ j h z‖ ≤ A * r26t8a_jetEnvelope b (sigma + j) ‖z‖) →
      ∃ coeff : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ,
        (∀ j < k, ‖coeff j‖ ≤ C * A) ∧
        (∀ j : ℕ, min (-sigma) (k : ℝ) ≤ (j : ℝ) → coeff j = 0) ∧
        ∀ j ≤ k, ∀ z, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖iteratedFDeriv ℝ j (fun v => h v - ∑ ell ∈ Finset.range k, coeff ell (fun _ => v)) z‖ ≤
            C * A * ‖z‖ ^ (min (-sigma) (k : ℝ) - j) * (1 + |Real.log ‖z‖|) ^ b := by
  set θ : ℝ := min (-sigma) (k : ℝ) with hθ
  have hθ0 : 0 < θ := lt_min (by linarith) (by exact_mod_cast hk)
  set m : ℕ := ⌈θ⌉₊ with hm
  have hmk : m ≤ k := Nat.ceil_le.2 (min_le_right _ _)
  have hjm : ∀ j : ℕ, j < m ↔ (j : ℝ) < θ := fun j => Nat.lt_ceil
  have hTall : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j < m → ∀ A : ℝ, 0 ≤ A → ∀ h : Euc d → ℝ,
      ContDiffOn ℝ k h {z | z ≠ 0} →
      (∀ i ≤ k, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ i h z‖ ≤ A * r26t8a_jetEnvelope b (sigma + i) ‖z‖) →
      ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ, ‖T‖ ≤ C * A ∧
        (∀ (τ : Equiv.Perm (Fin j)) (v : Fin j → Euc d), T (v ∘ τ) = T v) ∧
        ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖iteratedFDeriv ℝ j h z - T‖ ≤
            C * A * (‖z‖ ^ (min (-(sigma + j)) 1) * (1 + |Real.log ‖z‖|) ^ b)) := by
    intro j
    by_cases hj : j < m
    · have hjθ : (j : ℝ) < θ := (hjm j).1 hj
      obtain ⟨C, hC0, hC⟩ := r26t8a_p06_T d hd b k sigma j
        (by exact_mod_cast lt_of_lt_of_le hjθ (min_le_right _ _)) (lt_of_lt_of_le hjθ (min_le_left _ _))
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose CT hCT0 hCT using hTall
  set β0 : ℝ := 2 + |r26t8a_p06_M (-(sigma + k)) b| with hβ0
  have hβ00 : 0 ≤ β0 := by rw [hβ0]; positivity
  set bet : ℕ → ℝ := fun j => r26t8a_p06_beta θ b m β0 (m - j) with hbet
  have hbet0 : ∀ j, 0 ≤ bet j := fun j => r26t8a_p06_beta_nonneg θ b m hβ00 _
  set C : ℝ := ∑ j ∈ Finset.range (k + 1), (bet j + CT j) with hC
  have hCle : ∀ j ≤ k, bet j + CT j ≤ C := fun j hj =>
    Finset.single_le_sum (f := fun j => bet j + CT j) (fun i _ => add_nonneg (hbet0 i) (hCT0 i))
      (Finset.mem_range.2 (by omega))
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => add_nonneg (hbet0 j) (hCT0 j)
  refine ⟨C, hC0, ?_⟩
  intro A hA h hcont hjet
  have hcd : ∀ y : Euc d, y ≠ 0 → ContDiffAt ℝ (k : WithTop ℕ∞) h y := fun y hy =>
    hcont.contDiffAt (isOpen_ne.mem_nhds hy)
  have hTex : ∀ j : ℕ, ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ, j < m →
      (‖T‖ ≤ CT j * A ∧ (∀ (τ : Equiv.Perm (Fin j)) (v : Fin j → Euc d), T (v ∘ τ) = T v) ∧
        ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖iteratedFDeriv ℝ j h z - T‖ ≤
            CT j * A * (‖z‖ ^ (min (-(sigma + j)) 1) * (1 + |Real.log ‖z‖|) ^ b)) := by
    intro j
    by_cases hj : j < m
    · obtain ⟨T, hT⟩ := hCT j hj A hA h hcont hjet
      exact ⟨T, fun _ => hT⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose T hT using hTex
  set coeff : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ :=
    fun j => if j < m then ((1 : ℝ) / j.factorial) • T j else 0 with hcoeff
  have hcoeff_lt : ∀ j, j < m → coeff j = ((1 : ℝ) / j.factorial) • T j := fun j hj => by
    simp [hcoeff, hj]
  have hcoeff_ge : ∀ j, ¬ j < m → coeff j = 0 := fun j hj => by simp [hcoeff, hj]
  have hsym : ∀ j, j < m → ∀ (τ : Equiv.Perm (Fin j)) (v : Fin j → Euc d), coeff j (v ∘ τ) = coeff j v := by
    intro j hj τ v
    rw [hcoeff_lt j hj]
    simp only [ContinuousMultilinearMap.smul_apply]
    rw [(hT j hj).2.1 τ v]
  set P : Euc d → ℝ := r26t8a_p06_poly m coeff with hP
  have hPc : ContDiff ℝ ⊤ P := r26t8a_p06_poly_contDiff m coeff
  have hsumP : ∀ v : Euc d, ∑ ell ∈ Finset.range k, coeff ell (fun _ => v) = P v := by
    intro v
    rw [hP, r26t8a_p06_poly]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 hmk) (fun ell hell hell' => ?_)
    have : ¬ ell < m := fun h' => hell' (Finset.mem_range.2 h')
    rw [hcoeff_ge ell this]; rfl
  set g : Euc d → ℝ := fun v => h v - P v with hg
  have hgfun : (fun v => h v - ∑ ell ∈ Finset.range k, coeff ell (fun _ => v)) = g :=
    funext fun v => by rw [hsumP]
  have hPk : ∀ y : Euc d, ContDiffAt ℝ (k : WithTop ℕ∞) P y := fun y =>
    (hPc.of_le le_top).contDiffAt
  have hcdg : ∀ y : Euc d, y ≠ 0 → ContDiffAt ℝ (k : WithTop ℕ∞) g y := fun y hy =>
    (hcd y hy).sub (hPk y)
  have hrho : ∀ j ≤ k, ∀ y : Euc d, y ≠ 0 →
      iteratedFDeriv ℝ j g y = iteratedFDeriv ℝ j h y - iteratedFDeriv ℝ j P y := by
    intro j hj y hy
    exact fun_iteratedFDeriv_sub_apply ((hcd y hy).of_le (by exact_mod_cast hj))
      ((hPk y).of_le (by exact_mod_cast hj))
  refine ⟨coeff, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjm' : j < m
    · rw [hcoeff_lt j hjm', norm_smul]
      have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_pos j).ne'
      have h1 : ‖((1 : ℝ) / j.factorial)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]; exact hf
      calc ‖((1 : ℝ) / j.factorial)‖ * ‖T j‖ ≤ 1 * ‖T j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ CT j * A := by rw [one_mul]; exact (hT j hjm').1
        _ ≤ C * A := by
            have := hCle j hj.le
            have := hbet0 j
            exact mul_le_mul_of_nonneg_right (by linarith) hA
    · rw [hcoeff_ge j hjm', norm_zero]; positivity
  · intro j hj
    apply hcoeff_ge
    intro hjm'
    have := (hjm j).1 hjm'
    linarith
  -- the jet of the polynomial at 0
  have hPzero : ∀ j, j < m → iteratedFDeriv ℝ j P 0 = T j := by
    intro j hj
    have h0 := r26t8a_p06_poly_zero m coeff j hj (hsym j hj)
    rw [hcoeff_lt j hj, smul_smul] at h0
    have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    rw [mul_one_div_cancel hf, one_smul] at h0
    exact h0
  -- high orders
  have hhigh : ∀ j : ℕ, ¬ j < m → j ≤ k → ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ j g z‖ ≤ bet j * A * (‖z‖ ^ (θ - j) * (1 + |Real.log ‖z‖|) ^ b) := by
    intro j hj hjk z hz hz2
    have hθj : θ ≤ j := by
      by_contra hlt; exact hj ((hjm j).2 (not_le.1 hlt))
    have hPh : iteratedFDeriv ℝ j P z = 0 := r26t8a_p06_poly_high m coeff j (not_lt.1 hj) z
    rw [hrho j hjk z (norm_pos_iff.1 hz), hPh, sub_zero]
    have hb : bet j = β0 := by
      have : m - j = 0 := Nat.sub_eq_zero_of_le (not_lt.1 hj)
      simp [hbet, this, r26t8a_p06_beta]
    rw [hb]
    exact r26t8a_p06_high d b k sigma hsigma j hjk hθj A hA h hjet hz hz2
  have Q : ∀ n j : ℕ, k - j = n → j ≤ k → ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ j g z‖ ≤ bet j * A * (‖z‖ ^ (θ - j) * (1 + |Real.log ‖z‖|) ^ b) := by
    intro n
    induction n with
    | zero =>
      intro j hjn hjk
      have : j = k := by omega
      subst this
      exact hhigh j (by omega) le_rfl
    | succ n ih =>
      intro j hjn hjk z hz hz2
      by_cases hj : j < m
      · have hjθ : (j : ℝ) < θ := (hjm j).1 hj
        set a : ℝ := θ - j with ha_def
        have ha : 0 < a := by rw [ha_def]; linarith
        have hdiff : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 → DifferentiableAt ℝ (iteratedFDeriv ℝ j g) y :=
          fun y hy _ => (hcdg y (norm_pos_iff.1 hy)).differentiableAt_iteratedFDeriv
            (by exact_mod_cast (by omega : j < k))
        have hder : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 →
            ‖fderiv ℝ (iteratedFDeriv ℝ j g) y‖ ≤
              (bet (j + 1) * A) * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b := by
          intro y hy hy2
          rw [norm_fderiv_iteratedFDeriv]
          have := ih (j + 1) (by omega) (by omega) y hy hy2
          refine this.trans (le_of_eq ?_)
          rw [show θ - ((j + 1 : ℕ) : ℝ) = a - 1 by rw [ha_def]; push_cast; ring]
          ring
        have hpart := r26t8a_p06_partial (iteratedFDeriv ℝ j g) ha b (bet (j + 1) * A)
          (mul_nonneg (hbet0 _) hA) hdiff hder z hz hz2
        -- the remainder tends to 0 along the dyadic points
        have hyn : ∀ N : ℕ, ‖((1 : ℝ) / 2) ^ N • z‖ = ((1 : ℝ) / 2) ^ N * ‖z‖ := fun N => by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        have hy0 : ∀ N : ℕ, 0 < ‖((1 : ℝ) / 2) ^ N • z‖ := fun N => by rw [hyn]; positivity
        have hy2 : ∀ N : ℕ, ‖((1 : ℝ) / 2) ^ N • z‖ ≤ 1 / 2 := fun N => by
          rw [hyn]
          calc ((1 : ℝ) / 2) ^ N * ‖z‖ ≤ 1 * (1 / 2) :=
                mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num)) hz2 hz.le (by norm_num)
            _ = 1 / 2 := one_mul _
        have ha' : 0 < min (-(sigma + j)) 1 := lt_min (by linarith [lt_of_lt_of_le hjθ (min_le_left _ _)]) one_pos
        have hH : Tendsto (fun N : ℕ => iteratedFDeriv ℝ j h (((1 : ℝ) / 2) ^ N • z)) atTop (𝓝 (T j)) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          have hdec := (r26t8a_p06_decay_ray b ha' hz (by linarith)).const_mul (CT j * A)
          rw [mul_zero] at hdec
          refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hdec
          have := (hT j hj).2.2 _ (hy0 N) (hy2 N)
          rw [hyn] at this
          exact this
        have hPt : Tendsto (fun N : ℕ => iteratedFDeriv ℝ j P (((1 : ℝ) / 2) ^ N • z)) atTop (𝓝 (T j)) := by
          have hc : Continuous (iteratedFDeriv ℝ j P) :=
            hPc.continuous_iteratedFDeriv (by exact_mod_cast le_top)
          have hlim0 : Tendsto (fun N : ℕ => ((1 : ℝ) / 2) ^ N • z) atTop (𝓝 0) := by
            have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (1 : ℝ) / 2 < 1)).smul_const z
            simpa using this
          have := (hc.tendsto 0).comp hlim0
          rw [hPzero j hj] at this
          exact this
        have hlim : Tendsto (fun N : ℕ => iteratedFDeriv ℝ j g (((1 : ℝ) / 2) ^ N • z)) atTop (𝓝 0) := by
          have := hH.sub hPt
          rw [sub_self] at this
          refine this.congr (fun N => ?_)
          rw [hrho j (by omega) _ (norm_pos_iff.1 (hy0 N))]
        have hcont : Tendsto (fun N : ℕ => ‖iteratedFDeriv ℝ j g z -
            iteratedFDeriv ℝ j g (((1 : ℝ) / 2) ^ N • z)‖) atTop (𝓝 ‖iteratedFDeriv ℝ j g z - 0‖) :=
          (tendsto_const_nhds.sub hlim).norm
        have hle := le_of_tendsto' hcont hpart
        rw [sub_zero] at hle
        have hbs : bet j = bet (j + 1) * r26t8a_p06_K a b := by
          simp only [hbet]
          rw [r26t8a_p06_beta_step θ b m β0 hj]
        refine hle.trans (le_of_eq ?_)
        rw [hbs]; ring
      · exact hhigh j hj hjk z hz hz2
  refine fun j hj z hz hz2 => ?_
  rw [hgfun]
  have := Q (k - j) j rfl hj z hz hz2
  refine this.trans ?_
  have hL : 0 ≤ ‖z‖ ^ (θ - j) * (1 + |Real.log ‖z‖|) ^ b := by positivity
  have h1 : bet j ≤ C := by
    have := hCle j hj
    have := hCT0 j
    linarith
  have h2 : bet j * A ≤ C * A := mul_le_mul_of_nonneg_right h1 hA
  calc bet j * A * (‖z‖ ^ (θ - j) * (1 + |Real.log ‖z‖|) ^ b) ≤ C * A * (‖z‖ ^ (θ - j) * (1 + |Real.log ‖z‖|) ^ b) :=
        mul_le_mul_of_nonneg_right h2 hL
    _ = C * A * ‖z‖ ^ (θ - j) * (1 + |Real.log ‖z‖|) ^ b := by ring

end HRS.MS.R26T8A
