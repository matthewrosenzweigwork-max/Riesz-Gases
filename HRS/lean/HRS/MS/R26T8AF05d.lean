import HRS.MS.R26T8AF05c
import HRS.MS.R26T8AF03
import HRS.MS.AdjRdNorms

/-!
# S8.2 observed-time layer, packet T8A.F05 (helper 05d): Schwartz reduction of the nonlocal term

For a thermal density `ρ = σ²` (σ Schwartz) and a `SobSmooth` function `f`, the function
`ρ ∂_j f` is the Schwartz function `h = σ ∂_j(σ f) - (∂_j σ)(σ f)`, and its Euler derivative
`G = E h` is a finite combination of Schwartz coefficients times derivatives of `σ f`
(`D = ∂_j(σ f)`, `U = σ f`).  Bounds: `N_r(h) ≤ K₁ ‖f‖_{H^{r+1}}`, `N_r(G) ≤ K₂ ‖f‖_{H^{r+2}}`
with `N_r u = ‖u‖_{H^r} + ‖u‖_{L¹}`, constants independent of `f`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
open LineDeriv

variable {d : ℕ}

theorem r26t8a_f05d_mulL {x y : ℝ≥0∞} (h : x ≤ y) (a : ℝ≥0∞) : a * x ≤ a * y := by
  gcongr

theorem r26t8a_f05d_N_add (r : ℝ) (u v : Euc d → ℝ) :
    sobolevNormE r (fun x => u x + v x) + eLpNorm (fun x => u x + v x) 1 volume ≤
      (sobolevNormE r u + eLpNorm u 1 volume) + (sobolevNormE r v + eLpNorm v 1 volume) := by
  have h1 := HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le r u v
  have h2 : eLpNorm (fun x => u x + v x) 1 volume ≤ eLpNorm u 1 volume + eLpNorm v 1 volume :=
    eLpNorm_add_le (f := u) (g := v) le_rfl
  calc _ ≤ (sobolevNormE r u + sobolevNormE r v) + (eLpNorm u 1 volume + eLpNorm v 1 volume) :=
        add_le_add h1 h2
    _ = _ := by ring

theorem r26t8a_f05d_N_sub (r : ℝ) (u v : Euc d → ℝ) :
    sobolevNormE r (fun x => u x - v x) + eLpNorm (fun x => u x - v x) 1 volume ≤
      (sobolevNormE r u + eLpNorm u 1 volume) + (sobolevNormE r v + eLpNorm v 1 volume) := by
  have h1 := HRS.MS.SA12BD.sa12_sobolevNormE_sub r u v
  have h2 : eLpNorm (fun x => u x - v x) 1 volume ≤ eLpNorm u 1 volume + eLpNorm v 1 volume :=
    eLpNorm_sub_le (f := u) (g := v) le_rfl
  calc _ ≤ (sobolevNormE r u + sobolevNormE r v) + (eLpNorm u 1 volume + eLpNorm v 1 volume) :=
        add_le_add h1 h2
    _ = _ := by ring

theorem r26t8a_f05d_N_sum (r : ℝ) {ι : Type*} (s : Finset ι) (F : ι → Euc d → ℝ) :
    sobolevNormE r (fun x => ∑ i ∈ s, F i x) + eLpNorm (fun x => ∑ i ∈ s, F i x) 1 volume ≤
      ∑ i ∈ s, (sobolevNormE r (F i) + eLpNorm (F i) 1 volume) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [r26t8a_f05c_sob_zero]
    simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine le_trans (r26t8a_f05d_N_add r (F a) (fun x => ∑ i ∈ s, F i x)) ?_
    exact add_le_add le_rfl ih

theorem r26t8a_f05d_sum_comb {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (X : ι → ℝ≥0∞) (S : ℝ≥0∞) (hX : ∀ i ∈ s, X i ≤ ENNReal.ofReal (a i) * S) :
    ∑ i ∈ s, X i ≤ ENNReal.ofReal (∑ i ∈ s, a i) * S := by
  calc ∑ i ∈ s, X i ≤ ∑ i ∈ s, ENNReal.ofReal (a i) * S := Finset.sum_le_sum hX
    _ = (∑ i ∈ s, ENNReal.ofReal (a i)) * S := by rw [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ i ∈ s, a i) * S := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => ha i]

theorem r26t8a_f05d_add_comb (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (X Y S : ℝ≥0∞)
    (hX : X ≤ ENNReal.ofReal a * S) (hY : Y ≤ ENNReal.ofReal b * S) :
    X + Y ≤ ENNReal.ofReal (a + b) * S := by
  rw [ENNReal.ofReal_add ha hb, add_mul]
  exact add_le_add hX hY

theorem r26t8a_f05d_mul_chain (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (X S F : ℝ≥0∞)
    (hX : X ≤ ENNReal.ofReal a * S) (hS : S ≤ ENNReal.ofReal c * F) :
    X ≤ ENNReal.ofReal (a * c) * F := by
  calc X ≤ ENNReal.ofReal a * S := hX
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal c * F) := r26t8a_f05d_mulL hS _
    _ = ENNReal.ofReal (a * c) * F := by
      rw [ENNReal.ofReal_mul ha, mul_assoc]

theorem r26t8a_f05d_prod_apply (s v : Euc d → ℝ) (x w : Euc d) (hs : DifferentiableAt ℝ s x)
    (hv : DifferentiableAt ℝ v x) :
    fderiv ℝ (fun y => s y * v y) x w = s x * fderiv ℝ v x w + v x * fderiv ℝ s x w := by
  have h := fderiv_mul hs hv
  rw [show (fun y => s y * v y) = s * v from rfl, h, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

theorem r26t8a_f05d_piece (σ : SchwartzMap (Euc d) ℝ) (rho : Euc d → ℝ)
    (hsq : ∀ x, rho x = σ x * σ x) (r : ℕ) (j : Fin d) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ f : Euc d → ℝ, r26t8a_SobSmooth f →
      ∃ h G : SchwartzMap (Euc d) ℝ,
        (∀ x, h x = rho x * fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) ∧
        (∀ x, G x = fderiv ℝ (⇑h) x x) ∧
        sobolevNormE (r : ℝ) (⇑h) + eLpNorm (⇑h) 1 volume ≤
          ENNReal.ofReal K1 * sobolevNormE ((r : ℝ) + 1) f ∧
        sobolevNormE (r : ℝ) (⇑G) + eLpNorm (⇑G) 1 volume ≤
          ENNReal.ofReal K2 * sobolevNormE ((r : ℝ) + 2) f := by
  classical
  obtain ⟨σj, hσj⟩ : ∃ σj : SchwartzMap (Euc d) ℝ, ∀ x,
      σj x = fderiv ℝ (⇑σ) x (EuclideanSpace.single j (1 : ℝ)) :=
    ⟨(LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ) : Euc d) σ : SchwartzMap (Euc d) ℝ),
      fun x => rfl⟩
  have hCex : ∀ k : Fin d, ∃ C : SchwartzMap (Euc d) ℝ, ∀ x,
      C x = inner ℝ x (EuclideanSpace.single k (1 : ℝ)) * σ x :=
    fun k => r26t8a_f05c_mul _ (r26t8a_f05c_coord_tg k) σ
  choose Ck hCk using hCex
  have hCex' : ∀ k : Fin d, ∃ C : SchwartzMap (Euc d) ℝ, ∀ x,
      C x = inner ℝ x (EuclideanSpace.single k (1 : ℝ)) * σj x :=
    fun k => r26t8a_f05c_mul _ (r26t8a_f05c_coord_tg k) σj
  choose Ck' hCk' using hCex'
  obtain ⟨P, hP⟩ := r26t8a_f03_euler_schw σ
  obtain ⟨Q, hQ⟩ := r26t8a_f03_euler_schw σj
  have hK : ∀ (c : SchwartzMap (Euc d) ℝ) (s : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ g : Euc d → ℝ,
      r26t8a_SobSmooth g →
      sobolevNormE (s : ℝ) (fun x => c x * g x) + eLpNorm (fun x => c x * g x) 1 volume ≤
        ENNReal.ofReal K * sobolevNormE (s : ℝ) g := by
    intro c s
    obtain ⟨K, hK0, H⟩ := r26t8a_rapid_product c s
    exact ⟨K, hK0, fun g hg => (H g hg).2⟩
  choose Kc hKc0 hKc using hK
  have hprod : ∀ (c : SchwartzMap (Euc d) ℝ) (g : Euc d → ℝ), r26t8a_SobSmooth g →
      ∃ h : SchwartzMap (Euc d) ℝ, ∀ x, h x = c x * g x := by
    intro c g hg
    obtain ⟨K, -, H⟩ := r26t8a_rapid_product c 0
    obtain ⟨h, hh⟩ := (H g hg).1
    exact ⟨h, fun x => congrFun hh x⟩
  have hnn : ∀ (c : SchwartzMap (Euc d) ℝ) (s : ℕ), 0 ≤ Kc c s := fun c s => hKc0 c s
  refine ⟨(Kc σ r + Kc σj r) * Kc σ (r + 1),
    ((∑ k : Fin d, Kc (Ck k) r) + Kc P r + ((∑ k : Fin d, Kc (Ck' k) r) + Kc Q r)) * Kc σ (r + 2),
    mul_nonneg (add_nonneg (hnn _ _) (hnn _ _)) (hnn _ _),
    mul_nonneg (add_nonneg (add_nonneg (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _))
      (add_nonneg (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _))) (hnn _ _), ?_⟩
  intro f hf
  obtain ⟨U, hU⟩ := hprod σ f hf
  have hUfun : (⇑U) = fun x => σ x * f x := funext hU
  have hfd : Differentiable ℝ f := hf.1.differentiable (by simp)
  obtain ⟨D, hD⟩ : ∃ D : SchwartzMap (Euc d) ℝ, ∀ x,
      D x = fderiv ℝ (⇑U) x (EuclideanSpace.single j (1 : ℝ)) :=
    ⟨(LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ) : Euc d) U : SchwartzMap (Euc d) ℝ),
      fun x => rfl⟩
  have hDfun : (⇑D) = fun x => fderiv ℝ (⇑U) x (EuclideanSpace.single j (1 : ℝ)) := funext hD
  obtain ⟨A, hA⟩ := hprod σ (⇑D) (r26t8a_f05c_schw_sob D)
  obtain ⟨B, hB⟩ := hprod σj (⇑U) (r26t8a_f05c_schw_sob U)
  have hkey : ∀ x, (A - B) x = rho x * fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) := by
    intro x
    rw [SchwartzMap.sub_apply, hA x, hB x, hsq x, hσj x, hU x, hD x, hUfun,
      r26t8a_f05d_prod_apply σ f x _ (σ.differentiableAt) (hfd x)]
    ring
  obtain ⟨G, hG⟩ := r26t8a_f03_euler_schw (A - B)
  have hAfun : (⇑A) = fun x => σ x * D x := funext hA
  have hBfun : (⇑B) = fun x => σj x * U x := funext hB
  have hABfun : (⇑(A - B)) = fun x => (⇑A) x - (⇑B) x := funext fun x => SchwartzMap.sub_apply _ _ _
  -- Sobolev chain of the derivative objects
  have c1 : sobolevNormE (r : ℝ) (⇑D) ≤ sobolevNormE ((r : ℝ) + 1) (⇑U) := by
    rw [hDfun]
    exact r26t8a_f05a_sobolevNormE_pd U j (r : ℝ)
  have c2 : sobolevNormE ((r : ℝ) + 1) (⇑D) ≤ sobolevNormE ((r : ℝ) + 2) (⇑U) := by
    rw [hDfun]
    have := r26t8a_f05a_sobolevNormE_pd U j ((r : ℝ) + 1)
    rw [show (r : ℝ) + 1 + 1 = (r : ℝ) + 2 by ring] at this
    exact this
  have hDDex : ∀ k : Fin d, ∃ E : SchwartzMap (Euc d) ℝ, ∀ x,
      E x = fderiv ℝ (⇑D) x (EuclideanSpace.single k (1 : ℝ)) :=
    fun k => ⟨(LineDeriv.lineDerivOp (EuclideanSpace.single k (1 : ℝ) : Euc d) D :
      SchwartzMap (Euc d) ℝ), fun x => rfl⟩
  choose DD hDD using hDDex
  have hUUex : ∀ k : Fin d, ∃ E : SchwartzMap (Euc d) ℝ, ∀ x,
      E x = fderiv ℝ (⇑U) x (EuclideanSpace.single k (1 : ℝ)) :=
    fun k => ⟨(LineDeriv.lineDerivOp (EuclideanSpace.single k (1 : ℝ) : Euc d) U :
      SchwartzMap (Euc d) ℝ), fun x => rfl⟩
  choose UU hUU using hUUex
  have c3 : ∀ k : Fin d, sobolevNormE (r : ℝ) (⇑(DD k)) ≤ sobolevNormE ((r : ℝ) + 2) (⇑U) := by
    intro k
    have e : (⇑(DD k)) = fun x => fderiv ℝ (⇑D) x (EuclideanSpace.single k (1 : ℝ)) :=
      funext (hDD k)
    rw [e]
    exact (r26t8a_f05a_sobolevNormE_pd D k (r : ℝ)).trans c2
  have c4 : ∀ k : Fin d, sobolevNormE (r : ℝ) (⇑(UU k)) ≤ sobolevNormE ((r : ℝ) + 2) (⇑U) := by
    intro k
    have e : (⇑(UU k)) = fun x => fderiv ℝ (⇑U) x (EuclideanSpace.single k (1 : ℝ)) :=
      funext (hUU k)
    rw [e]
    have h1 := r26t8a_f05a_sobolevNormE_pd U k (r : ℝ)
    have h2 : sobolevNormE ((r : ℝ) + 1) (⇑U) ≤ sobolevNormE ((r : ℝ) + 2) (⇑U) :=
      r26t8a_f05c_sob_mono (by linarith) _
    exact h1.trans h2
  have c5 : sobolevNormE (r : ℝ) (⇑U) ≤ sobolevNormE ((r : ℝ) + 2) (⇑U) :=
    r26t8a_f05c_sob_mono (by linarith) _
  have c6 : sobolevNormE ((r : ℝ) + 1) (⇑U) ≤
      ENNReal.ofReal (Kc σ (r + 1)) * sobolevNormE ((r : ℝ) + 1) f := by
    have h := hKc σ (r + 1) f hf
    push_cast at h
    rw [← hUfun] at h
    exact le_trans le_self_add h
  have c7 : sobolevNormE ((r : ℝ) + 2) (⇑U) ≤
      ENNReal.ofReal (Kc σ (r + 2)) * sobolevNormE ((r : ℝ) + 2) f := by
    have h := hKc σ (r + 2) f hf
    push_cast at h
    rw [← hUfun] at h
    exact le_trans le_self_add h
  have c5' : sobolevNormE ((r : ℝ) + 1) (⇑U) ≤ sobolevNormE ((r : ℝ) + 2) (⇑U) :=
    r26t8a_f05c_sob_mono (by linarith) _
  -- Euler identity: E h = Σ_k C_k ∂_k D + P D - Σ_k C'_k ∂_k U - Q U
  have hGfun : (⇑G) = fun x => ((∑ k : Fin d, Ck k x * DD k x) + P x * D x) -
      ((∑ k : Fin d, Ck' k x * UU k x) + Q x * U x) := by
    funext x
    rw [hG x, hABfun, fderiv_fun_sub (A.differentiableAt (x := x)) (B.differentiableAt (x := x)),
      ContinuousLinearMap.sub_apply, hAfun, hBfun,
      r26t8a_f05c_euler_mul (⇑σ) (⇑D) x σ.differentiableAt D.differentiableAt,
      r26t8a_f05c_euler_mul (⇑σj) (⇑U) x σj.differentiableAt U.differentiableAt,
      r26t8a_f05c_euler_sum (⇑D) x, r26t8a_f05c_euler_sum (⇑U) x, ← hP x, ← hQ x]
    have s1 : σ x * ∑ k : Fin d, inner ℝ x (EuclideanSpace.single k (1 : ℝ)) *
        fderiv ℝ (⇑D) x (EuclideanSpace.single k (1 : ℝ)) =
        ∑ k : Fin d, Ck k x * DD k x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hCk k x, hDD k x]
      ring
    have s2 : σj x * ∑ k : Fin d, inner ℝ x (EuclideanSpace.single k (1 : ℝ)) *
        fderiv ℝ (⇑U) x (EuclideanSpace.single k (1 : ℝ)) =
        ∑ k : Fin d, Ck' k x * UU k x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hCk' k x, hUU k x]
      ring
    rw [s1, s2]
    ring
  refine ⟨A - B, G, hkey, hG, ?_, ?_⟩
  · -- bound on h
    rw [hABfun]
    refine le_trans (r26t8a_f05d_N_sub _ (⇑A) (⇑B)) ?_
    have nA : sobolevNormE (r : ℝ) (⇑A) + eLpNorm (⇑A) 1 volume ≤
        ENNReal.ofReal (Kc σ r) * sobolevNormE (r : ℝ) (⇑D) := by
      rw [hAfun]
      exact hKc σ r (⇑D) (r26t8a_f05c_schw_sob D)
    have nB : sobolevNormE (r : ℝ) (⇑B) + eLpNorm (⇑B) 1 volume ≤
        ENNReal.ofReal (Kc σj r) * sobolevNormE (r : ℝ) (⇑U) := by
      rw [hBfun]
      exact hKc σj r (⇑U) (r26t8a_f05c_schw_sob U)
    have hmU : sobolevNormE (r : ℝ) (⇑U) ≤ sobolevNormE ((r : ℝ) + 1) (⇑U) :=
      r26t8a_f05c_sob_mono (by linarith) (⇑U)
    have hX : sobolevNormE (r : ℝ) (⇑A) + eLpNorm (⇑A) 1 volume ≤
        ENNReal.ofReal (Kc σ r) * sobolevNormE ((r : ℝ) + 1) (⇑U) :=
      nA.trans (r26t8a_f05d_mulL c1 _)
    have hY : sobolevNormE (r : ℝ) (⇑B) + eLpNorm (⇑B) 1 volume ≤
        ENNReal.ofReal (Kc σj r) * sobolevNormE ((r : ℝ) + 1) (⇑U) :=
      nB.trans (r26t8a_f05d_mulL hmU _)
    have hsum := r26t8a_f05d_add_comb (Kc σ r) (Kc σj r) (hnn _ _) (hnn _ _) _ _ _ hX hY
    exact r26t8a_f05d_mul_chain (Kc σ r + Kc σj r) (Kc σ (r + 1)) (add_nonneg (hnn _ _) (hnn _ _))
      (hnn _ _) _ _ _ hsum c6
  · -- bound on G
    have hX1 : sobolevNormE (r : ℝ) (fun x => ∑ k : Fin d, Ck k x * DD k x) +
        eLpNorm (fun x => ∑ k : Fin d, Ck k x * DD k x) 1 volume ≤
        ENNReal.ofReal (∑ k : Fin d, Kc (Ck k) r) * sobolevNormE ((r : ℝ) + 2) (⇑U) := by
      refine le_trans (r26t8a_f05d_N_sum (r : ℝ) Finset.univ (fun k x => Ck k x * DD k x)) ?_
      refine r26t8a_f05d_sum_comb Finset.univ (fun k => Kc (Ck k) r) (fun k => hnn _ _) _ _ ?_
      intro k _
      exact (hKc (Ck k) r (⇑(DD k)) (r26t8a_f05c_schw_sob (DD k))).trans
        (r26t8a_f05d_mulL (c3 k) _)
    have hX2 : sobolevNormE (r : ℝ) (fun x => P x * D x) +
        eLpNorm (fun x => P x * D x) 1 volume ≤
        ENNReal.ofReal (Kc P r) * sobolevNormE ((r : ℝ) + 2) (⇑U) :=
      (hKc P r (⇑D) (r26t8a_f05c_schw_sob D)).trans (r26t8a_f05d_mulL (c1.trans c5') _)
    have hY1 : sobolevNormE (r : ℝ) (fun x => ∑ k : Fin d, Ck' k x * UU k x) +
        eLpNorm (fun x => ∑ k : Fin d, Ck' k x * UU k x) 1 volume ≤
        ENNReal.ofReal (∑ k : Fin d, Kc (Ck' k) r) * sobolevNormE ((r : ℝ) + 2) (⇑U) := by
      refine le_trans (r26t8a_f05d_N_sum (r : ℝ) Finset.univ (fun k x => Ck' k x * UU k x)) ?_
      refine r26t8a_f05d_sum_comb Finset.univ (fun k => Kc (Ck' k) r) (fun k => hnn _ _) _ _ ?_
      intro k _
      exact (hKc (Ck' k) r (⇑(UU k)) (r26t8a_f05c_schw_sob (UU k))).trans
        (r26t8a_f05d_mulL (c4 k) _)
    have hY2 : sobolevNormE (r : ℝ) (fun x => Q x * U x) +
        eLpNorm (fun x => Q x * U x) 1 volume ≤
        ENNReal.ofReal (Kc Q r) * sobolevNormE ((r : ℝ) + 2) (⇑U) :=
      (hKc Q r (⇑U) (r26t8a_f05c_schw_sob U)).trans (r26t8a_f05d_mulL c5 _)
    have hXfull := (r26t8a_f05d_N_add (r : ℝ) (fun x => ∑ k : Fin d, Ck k x * DD k x)
      (fun x => P x * D x)).trans (r26t8a_f05d_add_comb (∑ k : Fin d, Kc (Ck k) r) (Kc P r)
        (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _) _ _ _ hX1 hX2)
    have hYfull := (r26t8a_f05d_N_add (r : ℝ) (fun x => ∑ k : Fin d, Ck' k x * UU k x)
      (fun x => Q x * U x)).trans (r26t8a_f05d_add_comb (∑ k : Fin d, Kc (Ck' k) r) (Kc Q r)
        (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _) _ _ _ hY1 hY2)
    have hfin := r26t8a_f05d_add_comb
      ((∑ k : Fin d, Kc (Ck k) r) + Kc P r) ((∑ k : Fin d, Kc (Ck' k) r) + Kc Q r)
      (add_nonneg (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _))
      (add_nonneg (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _)) _ _ _ hXfull hYfull
    rw [hGfun]
    exact (r26t8a_f05d_N_sub _ _ _).trans
      (r26t8a_f05d_mul_chain _ (Kc σ (r + 2))
        (add_nonneg (add_nonneg (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _))
          (add_nonneg (Finset.sum_nonneg fun k _ => hnn _ _) (hnn _ _)))
        (hnn _ _) _ _ _ hfin c7)

end HRS.MS.R26T8A

end
