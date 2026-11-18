import HRS.MS.R26T8AA01a

/-!
# S8.2 T8A A01 (part b): the pointwise envelope of `tripleG`
For `Q` a `PairCorrector` and `‖forceMean ρ‖ ≤ BF`: on pairwise distinct `x y z`,
`|tripleG x y z| ≤ K (1+BF) A jb(x)^M' jb(y)^M' jb(z)^M' triplePole x y z`.
The three singular force pairs are grouped (`g(x-z)` with `g(z-x)`, etc.) and A00 is applied to each group.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_gradY_symm {Q : Euc d → Euc d → ℝ} (hs : ∀ x y, Q x y = Q y x) (x y : Euc d) :
    pairGradY Q x y = pairGradX Q y x := by
  unfold pairGradY pairGradX
  have : (Q x) = fun x' => Q x' x := funext fun y' => hs x y'
  rw [this]

theorem r26t8a_a01_inner_le {a b : Euc d} {c : ℝ} (hab : ‖a‖ ≤ c) : |inner ℝ a b| ≤ c * ‖b‖ :=
  (abs_real_inner_le_norm a b).trans (mul_le_mul_of_nonneg_right hab (norm_nonneg _))

theorem r26t8a_a01_key {a beta : ℝ} {rho : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (x y z : Euc d) :
    3 * tripleG (critCoeff d a beta rho) rho Q x y z =
      -inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (pairGradX Q x y - pairGradX Q z y) -
      inner ℝ (rieszKernelGrad d (criticalS d) (y - z)) (pairGradX Q y x - pairGradX Q z x) -
      inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (pairGradX Q x z - pairGradX Q y z) +
      (inner ℝ (forceMean rho x) (pairGradX Q x y) + inner ℝ (forceMean rho y) (pairGradY Q x y) +
        inner ℝ (forceMean rho x) (pairGradX Q x z) + inner ℝ (forceMean rho z) (pairGradY Q x z) +
        inner ℝ (forceMean rho y) (pairGradX Q y z) + inner ℝ (forceMean rho z) (pairGradY Q y z)) -
      pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y -
      pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x z -
      pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q y z := by
  have gy1 : pairGradY Q x y = pairGradX Q y x := r26t8a_a01_gradY_symm hsymm x y
  have gy2 : pairGradY Q x z = pairGradX Q z x := r26t8a_a01_gradY_symm hsymm x z
  have gy3 : pairGradY Q y z = pairGradX Q z y := r26t8a_a01_gradY_symm hsymm y z
  have hn1 : rieszKernelGrad d (criticalS d) (z - x) = -rieszKernelGrad d (criticalS d) (x - z) := by
    rw [show z - x = -(x - z) from (neg_sub x z).symm]; exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
  have hn2 : rieszKernelGrad d (criticalS d) (y - x) = -rieszKernelGrad d (criticalS d) (x - y) := by
    rw [show y - x = -(x - y) from (neg_sub x y).symm]; exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
  have hn3 : rieszKernelGrad d (criticalS d) (z - y) = -rieszKernelGrad d (criticalS d) (y - z) := by
    rw [show z - y = -(y - z) from (neg_sub y z).symm]; exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
  unfold tripleG tripleT HRS.MS.Phase2S82.centeredForce
  simp only [hn1, hn2, hn3, gy1, gy2, gy3, inner_sub_left, inner_neg_left, inner_sub_right]
  ring

set_option maxHeartbeats 6400000 in
theorem r26t8a_a01_env (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (hM : 0 ≤ M) :
    ∃ K M' : ℝ, 0 ≤ K ∧ M ≤ M' ∧ ∀ (rho f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M A f Q →
      ∀ BF : ℝ, 0 ≤ BF → (∀ u, ‖forceMean rho u‖ ≤ BF) →
      ∀ x y z : Euc d, x ≠ y → x ≠ z → y ≠ z →
        |tripleG (critCoeff d a beta rho) rho Q x y z| ≤
          K * (1 + BF) * A * (jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M') * triplePole x y z := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : (1 : ℝ) ≤ criticalS d := by unfold criticalS; linarith
  have hs0 : (0 : ℝ) < criticalS d := by linarith
  obtain ⟨C0, M', hC0, hMM', hA00⟩ := r26t8a_corrector_gradient_difference d hd a beta M hM
  refine ⟨criticalS d * C0 + 3, M', by positivity, hMM', ?_⟩
  intro rho f A hA Q hQ BF hBF0 hBF x y z hxy hxz hyz
  set s := criticalS d with hsdef
  set JJ : ℝ := jbracket x ^ M' * jbracket y ^ M' * jbracket z ^ M' with hJJ
  have j1 : ∀ u : Euc d, 1 ≤ jbracket u ^ M' := fun u => Real.one_le_rpow (s83_one_le_jb u) (by linarith)
  have jM : ∀ u : Euc d, jbracket u ^ M ≤ jbracket u ^ M' := fun u =>
    Real.rpow_le_rpow_of_exponent_le (s83_one_le_jb u) hMM'
  have hJJ1 : 1 ≤ jbracket x ^ M' := j1 x
  have hJJ2 : 1 ≤ jbracket y ^ M' := j1 y
  have hJJ3 : 1 ≤ jbracket z ^ M' := j1 z
  have hJJ0 : 0 ≤ JJ := by positivity
  -- pairWeight bounds
  have pwle : ∀ u v : Euc d, HRS.MS.Phase2S82.pairWeight M u v ≤ jbracket u ^ M' * jbracket v ^ M' := fun u v =>
    mul_le_mul (jM u) (jM v) (Real.rpow_nonneg (s83_jb_pos v).le _) (Real.rpow_nonneg (s83_jb_pos u).le _)
  have pwxy : HRS.MS.Phase2S82.pairWeight M x y ≤ JJ := by
    refine (pwle x y).trans ?_
    nlinarith [mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le M') (Real.rpow_nonneg (s83_jb_pos y).le M')]
  have pwxz : HRS.MS.Phase2S82.pairWeight M x z ≤ JJ := by
    refine (pwle x z).trans ?_
    have := mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le M') (Real.rpow_nonneg (s83_jb_pos z).le M')
    have h2 := Real.rpow_nonneg (s83_jb_pos y).le M'
    nlinarith [mul_le_mul_of_nonneg_left hJJ2 this]
  have pwyz : HRS.MS.Phase2S82.pairWeight M y z ≤ JJ := by
    refine (pwle y z).trans ?_
    have := mul_nonneg (Real.rpow_nonneg (s83_jb_pos y).le M') (Real.rpow_nonneg (s83_jb_pos z).le M')
    have h2 := Real.rpow_nonneg (s83_jb_pos x).le M'
    nlinarith [mul_le_mul_of_nonneg_left hJJ1 this]
  set pxy := pole x y with hpxy
  set pxz := pole x z with hpxz
  set pyz := pole y z with hpyz
  have p1 : 1 ≤ pxy := r26t8a_a01_pole_ge_one x y
  have p2 : 1 ≤ pxz := r26t8a_a01_pole_ge_one x z
  have p3 : 1 ≤ pyz := r26t8a_a01_pole_ge_one y z
  have hTP : triplePole x y z = pxy * pxz + pxy * pyz + pxz * pyz := rfl
  have hTP1 : pxy ≤ triplePole x y z := by rw [hTP]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ pxy) (by linarith : (0:ℝ) ≤ pxz - 1), mul_nonneg (by linarith : (0:ℝ) ≤ pxy) (by linarith : (0:ℝ) ≤ pyz), mul_nonneg (by linarith : (0:ℝ) ≤ pxz) (by linarith : (0:ℝ) ≤ pyz)]
  have hTP2 : pxz ≤ triplePole x y z := by rw [hTP]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ pxz) (by linarith : (0:ℝ) ≤ pxy - 1), mul_nonneg (by linarith : (0:ℝ) ≤ pxy) (by linarith : (0:ℝ) ≤ pyz), mul_nonneg (by linarith : (0:ℝ) ≤ pxz) (by linarith : (0:ℝ) ≤ pyz)]
  have hTP3 : pyz ≤ triplePole x y z := by rw [hTP]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ pyz) (by linarith : (0:ℝ) ≤ pxz - 1), mul_nonneg (by linarith : (0:ℝ) ≤ pxy) (by linarith : (0:ℝ) ≤ pyz), mul_nonneg (by linarith : (0:ℝ) ≤ pxy) (by linarith : (0:ℝ) ≤ pxz)]
  have hTP0 : 0 ≤ triplePole x y z := by linarith
  -- the pole products appearing in the three groupings
  have g1 : pxz * (pxy + pole z y) ≤ triplePole x y z := by
    rw [r26t8a_a01_pole_comm z y, hTP]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ pxy) (by linarith : (0:ℝ) ≤ pyz)]
  have g2 : pyz * (pole y x + pole z x) ≤ triplePole x y z := by
    rw [r26t8a_a01_pole_comm y x, r26t8a_a01_pole_comm z x, hTP]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ pxy) (by linarith : (0:ℝ) ≤ pxz)]
  have g3 : pxy * (pxz + pyz) ≤ triplePole x y z := by
    rw [hTP]; nlinarith
  -- symmetry of the gradients
  have hsymm := hQ.symmetric
  have gy1 : pairGradY Q x y = pairGradX Q y x := r26t8a_a01_gradY_symm hsymm x y
  have gy2 : pairGradY Q x z = pairGradX Q z x := r26t8a_a01_gradY_symm hsymm x z
  have gy3 : pairGradY Q y z = pairGradX Q z y := r26t8a_a01_gradY_symm hsymm y z
  -- the three grouped singular terms
  have grp : ∀ (u v w : Euc d), u ≠ v → w ≠ v → u ≠ w →
      |inner ℝ (rieszKernelGrad d s (u - w)) (pairGradX Q u v - pairGradX Q w v)| ≤
        s * C0 * A * (jbracket u ^ M' * jbracket v ^ M' * jbracket w ^ M') *
          (pole u w * (pole u v + pole w v)) := by
    intro u v w huv hwv huw
    have hD := hA00 rho f A hA Q hQ u v w huv hwv
    have hn : 0 < ‖u - w‖ := norm_pos_iff.2 (sub_ne_zero.2 huw)
    have hg : ‖rieszKernelGrad d s (u - w)‖ = s * ‖u - w‖ ^ (-s - 1) := r26t8a_norm_rieszGrad hs0 (sub_ne_zero.2 huw)
    refine (r26t8a_a01_inner_le (le_of_eq hg)).trans ?_
    have h1 : s * ‖u - w‖ ^ (-s - 1) * ‖pairGradX Q u v - pairGradX Q w v‖ ≤
        s * ‖u - w‖ ^ (-s - 1) * (C0 * A * jbracket u ^ M' * jbracket v ^ M' * jbracket w ^ M' *
          ‖u - w‖ * (pole u v + pole w v)) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    refine h1.trans ?_
    have e : ‖u - w‖ ^ (-s - 1) * ‖u - w‖ = ‖u - w‖ ^ (-s) := by
      rw [← Real.rpow_add_one hn.ne']; congr 1; ring
    have hp := r26t8a_a01_pole_ge hs0 huw
    have hpl : 0 ≤ pole u v + pole w v := by
      have := r26t8a_a01_pole_ge_one u v; have := r26t8a_a01_pole_ge_one w v; linarith
    have hsc : 0 ≤ s * C0 * A * (jbracket u ^ M' * jbracket v ^ M' * jbracket w ^ M') := by
      have := Real.rpow_nonneg (s83_jb_pos u).le M'
      have := Real.rpow_nonneg (s83_jb_pos v).le M'
      have := Real.rpow_nonneg (s83_jb_pos w).le M'
      positivity
    calc s * ‖u - w‖ ^ (-s - 1) * (C0 * A * jbracket u ^ M' * jbracket v ^ M' * jbracket w ^ M' *
          ‖u - w‖ * (pole u v + pole w v))
        = s * C0 * A * (jbracket u ^ M' * jbracket v ^ M' * jbracket w ^ M') *
            ((‖u - w‖ ^ (-s - 1) * ‖u - w‖) * (pole u v + pole w v)) := by ring
      _ = s * C0 * A * (jbracket u ^ M' * jbracket v ^ M' * jbracket w ^ M') *
            (‖u - w‖ ^ (-s) * (pole u v + pole w v)) := by rw [e]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hpl) hsc
  -- bounds
  set F : Euc d → Euc d := forceMean rho with hFdef
  set tA := inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (pairGradX Q x y - pairGradX Q z y) with htA
  set tB := inner ℝ (rieszKernelGrad d (criticalS d) (y - z)) (pairGradX Q y x - pairGradX Q z x) with htB
  set tC := inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (pairGradX Q x z - pairGradX Q y z) with htC
  have key := r26t8a_a01_key (a := a) (beta := beta) (rho := rho) hsymm x y z
  have hZ : 0 ≤ A * JJ * triplePole x y z := by positivity
  have bA : |tA| ≤ s * C0 * (A * JJ * triplePole x y z) := by
    have := grp x y z hxy hyz.symm hxz
    refine this.trans ?_
    rw [← hJJ] at *
    calc s * C0 * A * JJ * (pole x z * (pole x y + pole z y)) ≤ s * C0 * A * JJ * triplePole x y z :=
          mul_le_mul_of_nonneg_left g1 (by positivity)
      _ = _ := by ring
  have bB : |tB| ≤ s * C0 * (A * JJ * triplePole x y z) := by
    have := grp y x z hxy.symm hxz.symm hyz
    refine this.trans ?_
    have e : jbracket y ^ M' * jbracket x ^ M' * jbracket z ^ M' = JJ := by rw [hJJ]; ring
    rw [e]
    calc s * C0 * A * JJ * (pole y z * (pole y x + pole z x)) ≤ s * C0 * A * JJ * triplePole x y z :=
          mul_le_mul_of_nonneg_left g2 (by positivity)
      _ = _ := by ring
  have bC : |tC| ≤ s * C0 * (A * JJ * triplePole x y z) := by
    have := grp x z y hxz hyz hxy
    refine this.trans ?_
    have e : jbracket x ^ M' * jbracket z ^ M' * jbracket y ^ M' = JJ := by rw [hJJ]; ring
    rw [e]
    calc s * C0 * A * JJ * (pole x y * (pole x z + pole y z)) ≤ s * C0 * A * JJ * triplePole x y z :=
          mul_le_mul_of_nonneg_left g3 (by positivity)
      _ = _ := by ring
  have fb : ∀ (u v : Euc d) (hv : u ≠ v) (e1 : Euc d) (hu : ‖e1‖ ≤ BF) (pw : HRS.MS.Phase2S82.pairWeight M u v ≤ JJ)
      (hp : pole u v ≤ triplePole x y z), |inner ℝ e1 (pairGradX Q u v)| ≤ BF * (A * JJ * triplePole x y z) ∧
        |inner ℝ e1 (pairGradY Q u v)| ≤ BF * (A * JJ * triplePole x y z) := by
    intro u v hv e1 hu pw hp
    have hg := hQ.gradient u v hv
    have hgp := r26t8a_a01_grad_pole hv hs1
    have hA' : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M u v := by
      have := mul_nonneg (Real.rpow_nonneg (s83_jb_pos u).le M) (Real.rpow_nonneg (s83_jb_pos v).le M)
      exact mul_nonneg hA this
    have hfield : ‖pairGradX Q u v‖ + ‖pairGradY Q u v‖ ≤ A * JJ * triplePole x y z := by
      refine hg.trans ?_
      calc A * HRS.MS.Phase2S82.pairWeight M u v * (1 + smallRadius u v ^ (1 - criticalS d))
          ≤ A * HRS.MS.Phase2S82.pairWeight M u v * pole u v := mul_le_mul_of_nonneg_left hgp hA'
        _ ≤ A * JJ * triplePole x y z := by
            have h0 : 0 ≤ pole u v := by linarith [r26t8a_a01_pole_ge_one u v]
            exact mul_le_mul (mul_le_mul_of_nonneg_left pw hA) hp h0 (by positivity)
    have hX : ‖pairGradX Q u v‖ ≤ A * JJ * triplePole x y z := (le_add_of_nonneg_right (norm_nonneg _)).trans hfield
    have hY : ‖pairGradY Q u v‖ ≤ A * JJ * triplePole x y z := (le_add_of_nonneg_left (norm_nonneg _)).trans hfield
    exact ⟨(abs_real_inner_le_norm e1 _).trans (mul_le_mul hu hX (norm_nonneg _) hBF0),
      (abs_real_inner_le_norm e1 _).trans (mul_le_mul hu hY (norm_nonneg _) hBF0)⟩
  have hJb : ∀ (u v : Euc d) (hv : u ≠ v) (pw : HRS.MS.Phase2S82.pairWeight M u v ≤ JJ)
      (hp : pole u v ≤ triplePole x y z),
      |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q u v| ≤ A * JJ * triplePole x y z := by
    intro u v hv pw hp
    refine (hQ.nonlocal.2 u v hv).trans ?_
    have h0 : 0 ≤ pole u v := by linarith [r26t8a_a01_pole_ge_one u v]
    exact mul_le_mul (mul_le_mul_of_nonneg_left pw hA) hp h0 (by positivity)
  have hf1 := fb x y hxy (F x) (hBF x) pwxy hTP1
  have hf2 := fb x y hxy (F y) (hBF y) pwxy hTP1
  have hf3 := fb x z hxz (F x) (hBF x) pwxz hTP2
  have hf4 := fb x z hxz (F z) (hBF z) pwxz hTP2
  have hf5 := fb y z hyz (F y) (hBF y) pwyz hTP3
  have hf6 := fb y z hyz (F z) (hBF z) pwyz hTP3
  have hJ1 := hJb x y hxy pwxy hTP1
  have hJ2 := hJb x z hxz pwxz hTP2
  have hJ3 := hJb y z hyz pwyz hTP3
  have a1 := abs_le.1 bA
  have a2 := abs_le.1 bB
  have a3 := abs_le.1 bC
  have b1 := abs_le.1 hf1.1
  have b2 := abs_le.1 hf2.2
  have b3 := abs_le.1 hf3.1
  have b4 := abs_le.1 hf4.2
  have b5 := abs_le.1 hf5.1
  have b6 := abs_le.1 hf6.2
  have c1 := abs_le.1 hJ1
  have c2 := abs_le.1 hJ2
  have c3 := abs_le.1 hJ3
  set Z : ℝ := A * JJ * triplePole x y z with hZdef
  have hsC : 0 ≤ s * C0 := by positivity
  have hfin : |3 * tripleG (critCoeff d a beta rho) rho Q x y z| ≤ (3 * (s * C0) + 6 * BF + 3) * Z := by
    rw [key, abs_le]
    constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2,
      b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  have h3 : |3 * tripleG (critCoeff d a beta rho) rho Q x y z| = 3 * |tripleG (critCoeff d a beta rho) rho Q x y z| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [h3] at hfin
  have : (s * C0 + 2 * BF + 1) * Z ≤ (s * C0 + 3) * (1 + BF) * A * JJ * triplePole x y z := by
    have hZ0 : 0 ≤ Z := hZ
    have : (s * C0 + 3) * (1 + BF) * A * JJ * triplePole x y z = (s * C0 + 3) * (1 + BF) * Z := by
      rw [hZdef]; ring
    rw [this]
    nlinarith [mul_nonneg hsC hBF0, mul_nonneg (mul_nonneg hsC hBF0) hZ0, mul_nonneg hBF0 hZ0, mul_nonneg hsC hZ0]
  nlinarith

end HRS.MS.R26T8A
