import HRS.MS.Fp81S21RespIid
import HRS.MS.WsStatAux32

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas HRS.MS.S21E HRS.MS.S21

private theorem fp81s21_respIid_windowPath_smul
    {d : ℕ} (m T b c : ℝ) (hc : c ≠ 0)
    (f g : ℝ → OscDual d m)
    (hfg : ∀ t : Icc (0 : ℝ) T, f (b + (t : ℝ)) = c • g (b + (t : ℝ))) :
    windowPathOf m T b f = c • windowPathOf m T b g := by
  unfold windowPathOf
  rw [show (fun t : Icc (0 : ℝ) T => f (b + (t : ℝ))) =
      (fun t : Icc (0 : ℝ) T => c • g (b + (t : ℝ))) from funext hfg]
  exact HRS.MS.S21.s21_dite_smul
    (fun t : Icc (0 : ℝ) T => g (b + (t : ℝ))) c hc

/-- The synthesis of the centered endpoint response vector is exactly the
actual response window at every nonnegative shift. -/
theorem fp81s21_respIid_path (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        p.γ = 0 → ∀ a : ℝ, 0 ≤ a → ∀ x : Euc p.d,
          s21gPhi (r26t3_feature_enum p.d) p.hT
            ((wholeSpaceIndex p.d : ℕ) : ℝ)
            (fp81s21_initial_ellv R (r26t3_qwin R a) x) =
              responseWindow R a x := by
  obtain ⟨δq, hδq, hδqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  obtain ⟨δr, hδr, hδrhalf, hrec⟩ := fp81s21_initRecon_path p
  obtain ⟨δo, hδo, hδohalf, horbit⟩ := fp81s21_uniform_orbit_amplitudes p
  let δ0 := min δq (min δr δo)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hδq (lt_min hδr hδo)
  have hδhalf : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδqhalf
  have hDq : δ0 ≤ δq := min_le_left _ _
  have hDr : δ0 ≤ δr := (min_le_right _ _).trans (min_le_left _ _)
  have hDo : δ0 ≤ δo := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ a ha x => ?_⟩
  have hδq' := hδle.trans hDq
  have hδr' := hδle.trans hDr
  have hδo' := hδle.trans hDo
  have hδh : δ ≤ 1 / 2 := hδle.trans hδhalf
  obtain ⟨Cq, hCq, hqfamily⟩ := hqwin δ hδ hδq' R
  have hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a) :=
    (hqfamily a ha).1
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_s09_prob hδ hδh R
  have hmean : HRS.Whole.meanEmpirical (r26t3_Q R 2) = r26t3_mu R 0 := by
    calc
      HRS.Whole.meanEmpirical (r26t3_Q R 2) = r26t3_marg R 2 :=
        fp81s21_initRecon_meanEmpirical_marg hδ hδh R (Or.inr hγ) 2 (by omega)
      _ = r26t3_mu R 0 :=
        fp81s21_initial_iid_marg hδ hδh R hγ 2 (by omega)
  let X : EucConfig p.d 2 := fun _ => x
  have hpair : ∀ f : Euc p.d → ℝ,
      HRS.Whole.pair (HRS.Whole.empirical X) f = f x := by
    intro f
    rw [HRS.Whole.pair_empirical (by norm_num) X f]
    simp [X]
  have hinitfun : initialFunctional R 2 X =
      (fun f => Real.sqrt 2 * r26t3_a R f x) := by
    funext f
    dsimp [initialFunctional]
    rw [hpair f, hmean, fp81s21_initial_iid_response (R := R) hγ f x]
  let zresp : (Euc p.d → ℝ) → ℝ := fun f => r26t3_a R f x
  let zinit : (Euc p.d → ℝ) → ℝ := initialFunctional R 2 X
  have hinit : zinit = fun f => Real.sqrt 2 * zresp f := hinitfun
  have hzresp : S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ) zresp := by
    exact fp81s21_respIid_functional_admissible hδ hδh R hγ x
  have hzinit : S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ) zinit := by
    rw [hinit]
    exact HRS.MS.R2Interp.s102_Z_smul hzresp (Real.sqrt 2)
  obtain ⟨Co, co, hco, hcsum, horbitsAt⟩ := horbit δ hδ hδo' R
  let H : ℝ := a + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, ha]
  have hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) (fp81s21_uniform_orbit_coefficient p Co) := horbitsAt H hH
  have hP : (p.d : ℝ) < 2 * (wholeSpaceIndex p.d : ℝ) := by
    dsimp [HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H := by
    intro u t hu hut _ φ ψ c hφ hψ
    have h := fp81s21_U_linear_of_hermite_combo p R hφ hψ c
      (t := t) (r := u) (le_trans hu hut) ⟨hu, hut⟩
    have hfun : φ + c • ψ = (fun y => φ y + c * ψ y) := by
      funext y
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    funext y
    rw [hfun]
    exact congrFun h y
  have hu : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
  have hroot : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hroot
  have hscaleV : ∀ t : Icc (0 : ℝ) p.T,
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (a + (t : ℝ)) 0 zresp =
        c • r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (a + (t : ℝ)) 0 zinit := by
    intro t
    have hs : a + (t : ℝ) ∈ Icc (0 : ℝ) H := by
      constructor
      · linarith [ha, t.2.1]
      · dsimp [H]
        linarith [t.2.2]
    apply OscDual.ext_hermiteCoeff
    intro α
    rw [OscDual.hermiteCoeff_smul]
    change oscEigenvalue p.d α ^ ((wholeSpaceIndex p.d : ℝ) / 2) *
        OscDual.coord (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (a + (t : ℝ)) 0 zresp) α =
      c * (oscEigenvalue p.d α ^ ((wholeSpaceIndex p.d : ℝ) / 2) *
        OscDual.coord (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (a + (t : ℝ)) 0 zinit) α)
    rw [s102_Vprop_coord hP hD hzresp hlin (u := 0) hu hs α,
      s102_Vprop_coord hP hD hzinit hlin (u := 0) hu hs α]
    have heval := congrFun hinit (propagatorW (r26t3_coeff R) 0
      (a + (t : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
    rw [heval]
    dsimp [c]
    field_simp [hroot]
  have hwindowScale : responseWindow R a x = c • initialWindow R 2 a X := by
    unfold responseWindow initialWindow
    exact fp81s21_respIid_windowPath_smul (wholeSpaceIndex p.d)
      p.T a c hc (fun s => r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        s 0 zresp) (fun s => r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        s 0 zinit) (fun t => by simpa [add_assoc] using hscaleV t)
  have hrecPath := hrec δ hδ hδr' R (Or.inr hγ) 2 (by omega) a ha X
  have hmarg : r26t3_marg R 2 = r26t3_mu R 0 :=
    fp81s21_initial_iid_marg hδ hδh R hγ 2 (by omega)
  have hW : r26t3_W R (r26t3_qwin R a) 2 X =
      Real.sqrt 2 • s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x := by
    unfold r26t3_W
    rw [hmarg]
    have hfeature := S45.s45_feature_memℓp (by omega) hq
      (ν := r26t3_mu R 0) X
    apply lp.ext (funext fun j => ?_)
    change SeqL2.coord (featureVec (r26t3_qwin R a) (r26t3_mu R 0) X) j =
      SeqL2.coord (Real.sqrt 2 •
        s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) j
    have hleftcoord : SeqL2.coord (featureVec (r26t3_qwin R a)
        (r26t3_mu R 0) X) j = Real.sqrt 2 *
          (HRS.Whole.pair (HRS.Whole.empirical X) (r26t3_qwin R a j) -
            HRS.Whole.pair (r26t3_mu R 0) (r26t3_qwin R a j)) := by
      unfold featureVec
      exact S45.s45_coord_ofSeq hfeature j
    rw [hleftcoord, s21h_coord_smul,
      s21h2_coord hq (r26t3_mu R 0) x j, hpair]
  let S : SeqL2 →L[ℝ] Window p :=
    s21gPhi (r26t3_feature_enum p.d) p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ)
  have hS : S (r26t3_W R (r26t3_qwin R a) 2 X) =
      Real.sqrt 2 • S (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) := by
    calc
      S (r26t3_W R (r26t3_qwin R a) 2 X) =
          S (Real.sqrt 2 • s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) :=
        congrArg S hW
      _ = Real.sqrt 2 • S (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) :=
        map_smul S (Real.sqrt 2) _
  have hrootInv : c * Real.sqrt 2 = 1 := by
    dsimp [c]
    exact inv_mul_cancel₀ hroot
  have hscaled : c • initialWindow R 2 a X =
      S (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) := by
    calc
      c • initialWindow R 2 a X =
          c • S (r26t3_W R (r26t3_qwin R a) 2 X) :=
        congrArg (fun v => c • v) hrecPath.symm
      _ = c • (Real.sqrt 2 •
          S (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x)) :=
        congrArg (fun v => c • v) hS
      _ = S (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) := by
        rw [smul_smul, hrootInv, one_smul]
  have hvec := fp81s21_respIid_vector_eq_centered hδ hδh R hγ a ha x hq
  change S (fp81s21_initial_ellv R (r26t3_qwin R a) x) = responseWindow R a x
  rw [hvec]
  calc
    S (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) =
        c • initialWindow R 2 a X := hscaled.symm
    _ = responseWindow R a x := hwindowScale.symm

/-- The endpoint response-window field is continuous in the spatial point. -/
theorem fp81s21_respIid_responseWindow_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        p.γ = 0 → ∀ a : ℝ, 0 ≤ a →
          Continuous (fun x : Euc p.d => responseWindow R a x) := by
  obtain ⟨δp, hp, hphalf, hpath⟩ := fp81s21_respIid_path p
  obtain ⟨δq, hq, hqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  let δ0 := min δp δq
  refine ⟨δ0, lt_min hp hq, (min_le_left _ _).trans hphalf,
    fun δ hδ hδle R hγ a ha => ?_⟩
  have hδp := hδle.trans (min_le_left δp δq)
  have hδq := hδle.trans (min_le_right δp δq)
  have hδh := hδle.trans ((min_le_left δp δq).trans hphalf)
  obtain ⟨C, hC, hfamily⟩ := hqwin δ hδ hδq R
  have hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a) :=
    (hfamily a ha).1
  have hvec : Continuous (fp81s21_initial_ellv R (r26t3_qwin R a)) :=
    (fp81s21_respIid_vector_regular hδ hδh R hγ a ha hq).1
  let S : SeqL2 →L[ℝ] Window p :=
    s21gPhi (r26t3_feature_enum p.d) p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ)
  have hEq : (fun x : Euc p.d => responseWindow R a x) =
      (fun x => S (fp81s21_initial_ellv R (r26t3_qwin R a) x)) := by
    funext x
    exact (hpath δ hδ hδp R hγ a ha x).symm
  rw [hEq]
  exact S.continuous.comp hvec

#print axioms fp81s21_respIid_path
#print axioms fp81s21_respIid_responseWindow_continuous

end HRS.Fp81.S21
end
