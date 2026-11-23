module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RepIntCastMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BridgeQminor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle075
public import Formalism.HermitianCurvature.Bundle004
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoRatioPow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle076

@[expose] public section

section

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem lie_sub {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X - Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hX, hY, sub_zero]

theorem lie_add {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X + Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem EHH {φ F : Mat k r → E} {U : Set (Mat k r)} {g : Mat k r} (hφ : CkOn 2 (GV k r) φ) (hU : IsOpen U)
    (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : ContDiffOn ℝ 2 F U) (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h)
    (a b c d : Fin (2 * r + k + 1)) :
    Q.EH k r a b (Q.EH k r c d φ) g =
      (fderiv ℝ F g (g * Xa k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xa k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xb k r c d)) +
      Complex.I • ((fderiv ℝ F g (g * Xb k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xb k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xb k r c d))) := by
  have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF
  have hφ2 : CkOn ((1 : ℕ∞) + 1) (GV k r) φ := by
    have e : ((1 : ℕ∞) + 1) = 2 := by norm_num
    rw [e]; exact hφ
  have hφ1 : ∀ X : Mat k r, inLie k r X → CkOn 1 (GV k r) (Dx (false, X) φ) :=
    fun X hX => CkOn_Dx (x := (false, X)) hX hφ2
  have hop : ∀ X Y : Mat k r, inLie k r X → inLie k r Y →
      Dx (false, X) (Dx (false, Y) φ) g =
        fderiv ℝ (fderiv ℝ F) g (g * X) (g * Y) + fderiv ℝ F g (g * X * Y) :=
    fun X Y hX hY => Formalism.FourierDecayAlt.P.B4.op_op_ext false false hU hc hff hX hY hgU hg
  have hEcd : Q.EH k r c d φ = fun h => Dx (false, Xa k r c d) φ h + Complex.I • Dx (false, Xb k r c d) φ h :=
    EH_eq c d φ
  rw [EH_eq a b, hEcd]
  simp only
  rw [Dx_add (x := (false, Xa k r a b)) (Xa_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_add (x := (false, Xb k r a b)) (Xb_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_smul, Dx_smul]
  simp only
  rw [hop _ _ (Xa_lie a b) (Xa_lie c d), hop _ _ (Xa_lie a b) (Xb_lie c d), hop _ _ (Xb_lie a b) (Xa_lie c d),
    hop _ _ (Xb_lie a b) (Xb_lie c d)]
  simp only [smul_add]
  abel

theorem single_comm (a b c d : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) : Mat k r) := by
  split_ifs with h1 h2 h2
  all_goals
    first
    | (try subst h1); (try subst h2)
      simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, *]
    | ext i j
      simp_all [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul, Finset.sum_ite_eq,
        Finset.sum_ite_eq']

theorem EH_HGl : HGl (Q.EH (E := E) k r) := by
  intro a b c d φ hφ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := hφ g hg
  have hF2 : ContDiffOn ℝ 2 F U := by exact_mod_cast hF
  have hF' : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hgU)).hasFDerivAt
  have hsym : ∀ v w : Mat k r, fderiv ℝ (fderiv ℝ F) g v w = fderiv ℝ (fderiv ℝ F) g w v := by
    have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF2
    have := (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
    intro v w; exact this v w
  set A1 := Xa k r a b with hA1
  set A2 := Xb k r a b with hA2
  set C1 := Xa k r c d with hC1
  set C2 := Xb k r c d with hC2
  set D1 := fderiv ℝ F g with hD1
  set D2 := fderiv ℝ (fderiv ℝ F) g with hD2
  have hR : (if b = c then Q.EH k r a d φ g else 0) - (if d = a then Q.EH k r c b φ g else 0) =
      Psi D1 g (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
    rw [single_comm, Psi_sub]
    congr 1
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff a d
      · exact (Psi_zero D1 g).symm
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff c b
      · exact (Psi_zero D1 g).symm
  have e1 : A1 + Complex.I • A2 = Matrix.single a b 1 := hp_decomp _
  have e2 : C1 + Complex.I • C2 = Matrix.single c d 1 := hp_decomp _
  have hbr : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) := by
    rw [← e1, ← e2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (norm := module) hI • (A2 * C2 - C2 * A2)
  have hl1 : inLie k r ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) :=
    lie_sub (lie_bracket (Xa_lie a b) (Xa_lie c d)) (lie_bracket (Xb_lie a b) (Xb_lie c d))
  have hl2 : inLie k r ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) :=
    lie_add (lie_bracket (Xa_lie a b) (Xb_lie c d)) (lie_bracket (Xb_lie a b) (Xa_lie c d))
  have hP : Psi D1 g (((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) =
      D1 (g * ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2))) + Complex.I • D1 (g * ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) := by
    unfold Psi
    rw [(hp_of_parts hl1 hl2).1, (hp_of_parts hl1 hl2).2]
  rw [hR, hbr, hP, EHH hφ hU hgU hg hF2 hff a b c d, EHH hφ hU hgU hg hF2 hff c d a b]
  rw [← hA1, ← hA2, ← hC1, ← hC2, ← hD1, ← hD2]
  rw [hsym (g * C1) (g * A1), hsym (g * C2) (g * A1), hsym (g * C1) (g * A2), hsym (g * C2) (g * A2)]
  simp only [Matrix.mul_sub, Matrix.mul_add, map_sub, map_add (f := _), ← Matrix.mul_assoc]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (norm := module) hI • (D1 (g * A2 * C2) - D1 (g * C2 * A2))

theorem capAdInv : CapAdInv := by
  intro k r E _ _ y u f hy hf h hh
  have hyu := gv_unit hy
  have hQP : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hyu
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  set e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr hm with he
  have hpos : Q.posL k r 0 = ⇑e := by
    funext j; apply Fin.ext; simp [Q.posL, he]
  rw [hpos]
  exact ad_main (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (EHc k r y) (EHc_HL hy) hQP
    (fun c d φ hφ g hg => EHc_change hy c d φ hφ g hg) e u f (by rw [hm]; exact hf) h hh

theorem cVRho : JF.CVRho := cvRho_of capAdInv

end Formalism.FourierDecayAlt.P.JFxE
end
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ∞) :
    CkOn m (GV k r) (fun _ : Mat k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma dLR_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : List (Mat k r)) :
    dLR u v (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
  have hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show RdV X (Rw w _) = _
      rw [ih]
      funext g
      simp only [RdV, deriv_const']
  induction u with
  | nil => exact hR v
  | cons X u ih =>
    show LdV X (dLR u v _) = _
    rw [ih]
    funext g
    simp only [LdV, deriv_const']

lemma norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [Complex.norm_exp]
  simp

lemma isOpen_OmPlus (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Formalism.FourierDecayAlt.Q.OmPlus k r z z') := by
  have e : Formalism.FourierDecayAlt.Q.OmPlus k r z z' =
      (⋂ l : Fin (r + 2), {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0}) ∩ {g | 0 < Gf k r z z' g} := by
    ext g; simp [Formalism.FourierDecayAlt.Q.OmPlus]
  rw [e]
  refine (isOpen_iInter_of_finite fun l => ?_).inter
    (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z'))
  by_cases hl : l.val ≤ r
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' l) continuous_const
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_univ

lemma cv_continuous (b : Bool) (X g : Mat k r) : Continuous fun t : ℝ => cv b X t g := by
  cases b
  · exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  · have h := (Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous
    have h2 := (continuous_mul_const g).comp h
    refine h2.congr fun t => ?_
    simp [cv, smul_neg]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma norm_xiP (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiP D p‖ ≤ 1 := by
  unfold xiP
  simp [norm_psi]

lemma continuous_xiP (D : RealPlaceData k r Wp Wq) : Continuous (xiP D) := by
  have key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M) := by
    intro z
    unfold ell
    refine continuous_finsetSum _ fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, ↓reduceDIte, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]
      refine continuous_finsetSum _ fun j _ => ?_
      first
        | fun_prop
        | exact (((continuous_apply j).comp (continuous_apply (eI k r a))).mul continuous_const :)
        | continuity
  have hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M) := by
    intro z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (key z)))))
  unfold xiP
  exact ((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul
    (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))

lemma ckOn_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) := by
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have e : rho D p F = fun x => ((ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)))
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
    funext x
    simp only [rho, sgs, Matrix.mul_assoc]
    rfl
  rw [e]
  exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hF ha hb) _

lemma ckOn_dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X)
    (hv : ∀ X ∈ v, unitLie k r X) (j : ℕ) (hl : j + (u.length + v.length) ≤ m) :
    CkOn ((j : ℕ) : ℕ∞) (GV k r) (dLR u v (rho D p F)) := by
  rw [dLR_eq]
  exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) j (ckOn_mono (by rw [length_lr]; omega) (ckOn_rho D hp hF))

lemma good_set (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F)
    {K : Set (Mat k r)} (hK : IsCompact K) (hKG : K ⊆ GV k r)
    {WS : Set (List (Mat k r) × List (Mat k r))} (hWS : WS.Countable)
    (hWSl : ∀ uv ∈ WS, (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m)
    (b : SS k r → ℝ)
    (hb : ∀ uv ∈ WS, ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖rho D p (dLR (uv.1.map (AdL p)) (uv.2.map (AdR p)) F) g‖ ≤ b p) :
    ∀ᵐ p ∂D.μSS, D.inSS p ∧ ∀ uv ∈ WS, ∀ g ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g‖ ≤ b p := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat k r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨S, hSK, hSc, hKS⟩ := hK.isSeparable.exists_countable_dense_subset
  haveI := hWS.to_subtype
  haveI := hSc.to_subtype
  have hall : ∀ᵐ p ∂D.μSS, ∀ i : WS × S,
      ‖rho D p (dLR (i.1.1.1.map (AdL p)) (i.1.1.2.map (AdR p)) F) i.2.1‖ ≤ b p :=
    ae_all_iff.2 fun i => hb i.1.1 i.1.2 i.2.1 (hSK i.2.2)
  filter_upwards [hall, Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp hpS
  refine ⟨hpS, fun uv huv g hg => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hWSl uv huv
  have hcont : ContinuousOn (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) (GV k r) :=
    (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_dLR_rho D hpS hF h1 h2 0 (by omega))).norm
  have hcl : IsClosed (GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p)) :=
    hcont.preimage_isClosed_of_isClosed Formalism.FourierDecayAlt.P.B5.GV_closed isClosed_Iic
  have hS : S ⊆ GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p) := by
    intro x hx
    refine ⟨hKG (hSK hx), ?_⟩
    show ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ b p
    rw [dLR_rho D hpS]
    exact hp ⟨⟨uv, huv⟩, ⟨x, hx⟩⟩
  exact (hcl.closure_subset_iff.2 hS (hKS hg)).2

lemma curve_ball (D : RealPlaceData k r Wp Wq) {g : Mat k r} (hg : g ∈ Om k r D.z D.z') (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ Om k r D.z D.z' := by
  have hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') :=
    (isOpen_OmPlus _ _).preimage (cv_continuous b X g)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := by
    show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'
    rw [cv_zero]; exact hg.2
  obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := hg
  refine ⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩
  rw [Metric.mem_closedBall] at ht
  rw [Metric.mem_ball]
  linarith

end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
end
end

section

namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def gK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (p q : C.LPt × ℂ) : ℂ :=
  KB.gN S v ε (b + s - 2) a (p.1 ++ [(s - 1, p.2⁻¹)]) (q.1 ++ [(s - 1, q.2⁻¹)])

def gDens (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (h h' : C.LPt) (z : ℂ) : ℂ :=
  KB.gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)])

structure GermReal (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (Y : Finset C.LPt) where
  H : Type
  [nag : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  ut : C.LPt → ℂ → ℂ → H
  bt : C.LPt → ℂ → H
  β : ℂ
  ε' : ℂ
  hβ : β ≠ 0
  hε' : ‖ε'‖ = 1
  hdl : KB.dlB S b s ≠ 0
  hpsi : ∀ σ z : ℂ, G.psi β (σ * z) = KB.psiL S σ z
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (ut h x) 2 volume
  gram : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
    gK S v ε b s a (h, x) (h', x') = gramL volume (Uc s ut) (Uc s ut) (h, x) (h', x')
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖ut h x D - mainD s β ε' (bt h) x D‖ ≤ C * ‖x‖⁻¹
  dens : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ z : ℂ, z ≠ 0 →
    gDens S v ε b s a h h' z = (KB.dlB S b s : ℂ) * ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ

attribute [instance] GermReal.nag GermReal.ips GermReal.cs

def GermRealised (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ Y : Finset C.LPt,
    (∀ h ∈ Y, D.ptSize h = b - 1) → Nonempty (GermReal S v ε b s a Y)

def GermCont (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ h h' : C.LPt,
    D.ptSize h = b - 1 → D.ptSize h' = b - 1 → ContinuousOn (gDens S v ε b s a h h') {0}ᶜ

theorem integral_inner_self_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : ℂ → H) :
    ∫ c, ⟪f c, f c⟫_ℂ = ((∫ c, ‖f c‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ c, ⟪f c, f c⟫_ℂ = ((‖f c‖ ^ 2 : ℝ) : ℂ) := fun c => by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [h]
  exact integral_ofReal

theorem GermReal.germD {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) (hs : 2 ≤ s) (B : ℝ)
    (hB : ∀ h ∈ Y, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + s - 2) a (h ++ [(s - 1, t)]) (h ++ [(s - 1, t)])‖ ≤ B) :
    GermD s R.β R.ε' Y R.ut R.bt B := by
  refine ⟨by omega, R.hβ, R.hε', R.memU, fun h hh x hx => ?_, R.meas, R.loc, R.germ⟩
  have hg := R.gram h hh h hh x x hx hx
  have hb := hB h hh x⁻¹ (inv_ne_zero hx)
  unfold gK at hg
  dsimp only at hg
  rw [hg] at hb
  unfold gramL Uc at hb
  dsimp only at hb
  rw [integral_inner_self_eq, integral_norm_cvec_sq s (R.ut h) x hx, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hb
  exact hb

theorem GermReal.nhat_eq {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) {h h' : C.LPt} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ : ℂ) :
    Nhat s R.β R.bt σ h h' = KB.hatB S v ε b s a σ h h' := by
  have hdl : ((KB.dlB S b s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr R.hdl
  have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    rw [ae_iff]; simp
  unfold KB.hatB Nhat
  have hae : (fun c => KB.gN S v ε (b + s - 1) a (h ++ [(s, c)]) (h' ++ [(s, c)]) * KB.psiL S σ c)
      =ᵐ[volume] fun c => ((KB.dlB S b s : ℝ) : ℂ) *
        (G.psi R.β (σ * c) • ⟪bz s (R.bt h) c, bz s (R.bt h') c⟫_ℂ) := by
    filter_upwards [h0] with c hc
    have hd := R.dens h hh h' hh' c hc
    unfold gDens at hd
    rw [hd, ← R.hpsi σ c, smul_eq_mul]
    ring
  rw [integral_congr_ae hae, integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hdl, one_mul]

theorem ae_ne_zero : ∀ᵐ z : ℂ, z ≠ 0 := by
  rw [ae_iff]; simp

theorem germLoc_of_realised {S : C.HidaSetting E Wp Wq} {v : Fin S.f} (hR : GermRealised S v) (hC : GermCont S v) :
    KB.GermLoc S v := by
  intro ε hε b s hb hs hbs a ha Y hY hB
  obtain ⟨B, hB⟩ := hB
  obtain ⟨R⟩ := hR ε hε b s hb hs hbs a ha Y hY
  have G := R.germD hs B hB
  obtain ⟨hint, rest⟩ := G.germLoc_tail
    (fun p q => KB.gN S v ε (b + s - 2) a (p.1 ++ [(s - 1, p.2⁻¹)]) (q.1 ++ [(s - 1, q.2⁻¹)]))
    (fun h hh h' hh' x x' hx hx' => R.gram h hh h' hh' x x' hx hx')
    (KB.hatB S v ε b s a) (fun σ h hh h' hh' => R.nhat_eq hh hh' σ)
  refine ⟨fun h hh h' hh' => ⟨hC ε hε b s hb hs hbs a ha h h' (hY h hh) (hY h' hh'), ?_⟩, rest⟩
  have hae : (fun z => ((KB.dlB S b s : ℝ) : ℂ) * ⟪bz s (R.bt h) z, bz s (R.bt h') z⟫_ℂ) =ᵐ[volume]
      fun z => KB.gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)]) := by
    filter_upwards [ae_ne_zero] with z hz
    exact (R.dens h hh h' hh' z hz).symm
  exact ((hint h hh h' hh').const_mul _).congr hae

end loc

end

end Formalism.FourierDecayAlt.P.GermRealisation
end
