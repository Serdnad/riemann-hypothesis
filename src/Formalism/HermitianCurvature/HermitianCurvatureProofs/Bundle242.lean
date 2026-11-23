module

public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle227
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentRotationHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle241
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSStab
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle240
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle186
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle216
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

namespace TR

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.P.TheSecStab

section block

variable {k : ℕ}

theorem img_perp_a {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : herm (Hb k) a a = -(T : ℂ))
    (hb : herm (Hb k) b b = -(T' : ℂ)) {x : Fin (k + 1) → ℂ} (hxb : herm (Hb k) x b = 0) :
    herm (Hb k) (gA k a T *ᵥ (gB k b T' *ᵥ x)) a = 0 := by
  have hne : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
  have hne' : star ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by
    rw [show star ((Real.sqrt T' : ℝ) : ℂ) = _ from Complex.conj_ofReal _]; exact hne
  have h1 : herm (Hb k) (gB k b T' *ᵥ x) (Pi.single (Fin.last k) 1) = 0 := by
    rw [← form_of_unitary (Hb k) (gB_spec k hT' hb).1, (gB_spec k hT' hb).2, herm_smul_right] at hxb
    exact (mul_eq_zero.1 hxb).resolve_left hne'
  have h2 := form_of_unitary (Hb k) (gA_spec k hT ha).1 (gB k b T' *ᵥ x)
    (((Real.sqrt T : ℝ) : ℂ) • Pi.single (Fin.last k) 1)
  rw [(gA_spec k hT ha).2] at h2
  rw [h2, herm_smul_right, h1, mul_zero]

theorem img_perp_0 {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : herm (Hb k) a a = -(T : ℂ))
    (hb : herm (Hb k) b b = -(T' : ℂ)) {x : Fin (k + 1) → ℂ}
    (hx0 : herm (Hb k) x ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) = 0) :
    herm (Hb k) (gA k a T *ᵥ (gB k b T' *ᵥ x)) (gA k a T *ᵥ Pi.single 0 1) = 0 := by
  rw [form_of_unitary (Hb k) (gA_spec k hT ha).1, ← DC.gB_adj hT' hb]
  exact hx0

end block

section big

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem stabilizer_fixes_section_embedding (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) {h : Q.Mx k r}
    (hfix : ∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (DC.EE k r z) = 0 → h *ᵥ v = v) :
    h * SSn.io0 k r z z' (theSection k r z z') ζ = SSn.io0 k r z z' (theSection k r z z') ζ := by
  have ha := SettingConstruction.herm_self k r z hz
  have hb := SettingConstruction.herm_self k r z' hz'
  rw [DC.section_embedding_eq_matrix hk hz hz' hT hT' hζ]
  ext i j
  obtain ⟨h1, h2, h3⟩ := DC.uu_facts (r := r) hk hz' hT' j
  have g2 : herm (Hb k) (wbPart k r (DC.uu k r z' j)) (wbPart k r z') = 0 := by
    rw [← DC.herm_of h1 hz']; exact h2
  have g3 : herm (Hb k) (wbPart k r (DC.uu k r z' j)) ((gB k (wbPart k r z') (Tz k r z'))⁻¹ *ᵥ Pi.single 0 1) = 0 := by
    rw [DC.EE', DC.herm_of h1 (inWb_jV _), wbPart_jV] at h3; exact h3
  have e := hfix (jV k r (gA k (wbPart k r z) (Tz k r z) *ᵥ (gB k (wbPart k r z') (Tz k r z') *ᵥ wbPart k r (DC.uu k r z' j))))
    (inWb_jV _)
    (by rw [DC.herm_of (inWb_jV _) hz, wbPart_jV]; exact img_perp_a hT hT' ha hb g2)
    (by rw [DC.EE, herm_jV]; exact img_perp_0 hT hT' ha hb g3)
  rw [Matrix.mul_apply]
  exact congrFun e i

end big

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
  {π : B.Mat k r → (Wp →L[ℂ] Wp)} {π' : B.Mat k r → (Wq →L[ℂ] Wq)}

theorem tht_iota_smul (F F' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) {ι ι' : B.Mat k r}
    (h : ∀ q, ι' *ᵥ F' q = u • (ι *ᵥ F' q)) : tht k r z z' π π' F F' a a' ι' = u • tht k r z z' π π' F F' a a' ι := by
  unfold tht
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [h q, P.Qx8.herm_smul_left', smul_smul]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tht_rot (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    {h h' : B.Mat k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (u : ℂ) (hu : conj u * u = 1)
    {a a' : Fin (2 * r + k + 1) → ℂ} {ι : B.Mat k r} (ha : h *ᵥ a = u • a) (ha' : h' *ᵥ a' = u • a') (hι : h * ι = ι)
    (hsc : ∀ q, h' *ᵥ F' q = u • F' q) (X : Wq →L[ℂ] Wp) :
    (π h).comp ((tht k r z z' π π' F F' a a' ι X).comp (π' h')) =
      conj u • tht k r z z' π π' F F' a a' ι ((π h).comp (X.comp (π' h'))) := by
  have uh' : IsUnit h'.det := WeylGroupFacts.isUnit_of_uh hh'.1
  have hinv : (h'⁻¹)⁻¹ = h' := Matrix.nonsing_inv_nonsing_inv _ uh'
  have e2 : h'⁻¹ *ᵥ a' = conj u • a' := by
    have e := congrArg (fun v => conj u • (h'⁻¹ *ᵥ v)) ha'
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uh', Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, hu,
      one_smul] at e
    exact e.symm
  have e3 : ∀ q, (h * ι * h') *ᵥ F' q = u • (ι *ᵥ F' q) := by
    intro q
    rw [hι, ← Matrix.mulVec_mulVec, hsc q, Matrix.mulVec_smul]
  have key := TF.tht_eqv hz hT hR hz' hT' hR' hF hF' hh (P.LieBracketMultiplication.uw_inv hh') a a' ι X
  rw [hinv, ha, e2, TF.tht_phase hz hT hR hz' hT' hR' hF hF', tht_iota_smul F F' a a' u e3, smul_smul] at key
  rw [← key, FunLike.coe_smul, Pi.smul_apply]
  congr 1
  linear_combination (conj u) * hu

end gen

end TR

open Formalism.FourierDecayAlt.P.TheSec in
theorem theta_rotation_holds : ThtRot := by
  intro Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec Bw Bw' hBw hBw' θ h h' hh hh' ζ hζ hν hfix hsc Xf
  obtain ⟨hOK, hz, hz', hTe, hTe', hty, hty'⟩ := hPl
  have hT : 0 < Tz P.k P.r Bs.z := hTe ▸ hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := hTe' ▸ hOK.T'_pos
  have hR : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨hty.2.1, hty.2.2.1⟩
  have hR' : Qr.IsRepW P.k P.r Bs.z' Bs.π' := ⟨hty'.2.1, hty'.2.2.1⟩
  have hk1 : 1 ≤ P.k := by omega
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by rw [hTe, hTe']; exact hζ
  have hu : conj (PS.eM θ) * PS.eM θ = 1 := by
    rw [← Complex.star_def, PS.star_eM]; exact PS.expPlus_mul_expMinus θ
  have hcu : conj (PS.eM θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.star_def, PS.star_eM]; rfl
  rw [hsec] at hν hfix ⊢
  obtain ⟨hE, hEz, _⟩ := DC.EE'_facts (r := P.r) hk1 hz' hT'
  have hν' : h' *ᵥ SSn.nu0' P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ =
      PS.eM θ • SSn.nu0' P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ := by
    rw [DC.nu0'_eq hk1 hz hz' hT hT' hζ', Matrix.mulVec_neg, smul_neg]
    exact congrArg Neg.neg (hsc _ hE hEz)
  have hι : h * SSn.io0 P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ =
      SSn.io0 P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ := by
    refine TR.stabilizer_fixes_section_embedding hk1 hz hz' hT hT' hζ' ?_
    rw [DC.section_first_vector_eq hk1 hz hz' hT hT' hζ'] at hfix
    exact hfix
  rw [← hcu]
  exact TR.tht_rot hz hT hR hz' hT' hR' hBw hBw' hh hh' (PS.eM θ) hu hν hν' hι
    (fun q => hsc _ (TF.frame_inW hBw' q).1 (TF.frame_inW hBw' q).2) Xf

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_hat (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hHat : JDHatOpQQ) (hBdd : JA.JABddOpQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_genTransfer hJ hG (jDecayTrQQ_of_open hHat) (JA.jAdjTrQQ_of_three hHat hBdd JA.star_operator_transfer_holds)

end Formalism.FourierDecayAlt.P.CutMP
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem datum_transitivity_holds : DatumTransit := datumTransit_of_cut datum_transit_existence datum_transit_stabilizer

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.TwoByOneBlock

variable {k r : ℕ}

theorem star_exp_mul (θ : ℝ) :
    star (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem cW_mem_UWb (θ : ℝ) : cW k r θ ∈ UWb k r := by
  refine emb_mem_UWb ?_
  show (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))ᴴ * Hb k *
    (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) = Hb k
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
    mul_comm, star_exp_mul, one_smul]

theorem cW_comm (θ : ℝ) {h : Q.Mx k r} (hh : h ∈ UWb k r) : cW k r θ * h = h * cW k r θ := by
  obtain ⟨μ, _, rfl⟩ := (UWb_iff h).1 hh
  unfold cW
  rw [← emb_mul, ← emb_mul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem cW_Glev (θ : ℝ) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) : cW k r θ * g ∈ Q.Glev k r (Fin.last r) := by
  obtain ⟨hc, hfix⟩ := cW_mem_UWb (k := k) (r := r) θ
  refine ⟨UH_mul hc hg.1, fun a ha => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, (hg.2 a ha).1, (hfix a).1]
  · rw [← Matrix.mulVec_mulVec, (hg.2 a ha).2, (hfix a).2]

theorem herm_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (cW k r θ *ᵥ v) z = Complex.exp ((θ : ℂ) * Complex.I) * herm (Hpk k r) v z := by
  have h1 : cW k r θ *ᵥ (Complex.exp (-((θ : ℂ) * Complex.I)) • z) = z := by
    rw [Matrix.mulVec_smul, cW_mulVec _ hz, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  have h2 : star (Complex.exp (-((θ : ℂ) * Complex.I))) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  calc herm (Hpk k r) (cW k r θ *ᵥ v) z
      = herm (Hpk k r) (cW k r θ *ᵥ v) (cW k r θ *ᵥ (Complex.exp (-((θ : ℂ) * Complex.I)) • z)) := by rw [h1]
    _ = _ := by rw [herm_UH (cW_mem_UWb θ).1, herm_smul_right, h2]

theorem GGl_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) :
    Q.GGl k r z z' (cW k r θ * g) = Q.GGl k r z z' g := by
  unfold Q.GGl Q.zetaL
  rw [fvec_last, fvec_last, ← Matrix.mulVec_mulVec, herm_cW θ hz, map_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem domR_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ Q.DomR k r z z') : (x.1, cW k r θ * x.2) ∈ Q.DomR k r z z' :=
  ⟨hx.1, cW_Glev θ hx.2.1, by
    show 0 < Q.GGl k r z z' (cW k r θ * x.2)
    rw [GGl_cW θ hz]
    exact hx.2.2⟩

theorem domR_of_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : (x.1, cW k r θ * x.2) ∈ Q.DomR k r z z') : x ∈ Q.DomR k r z z' := by
  have h := domR_cW (-θ) hz z' hx
  have e : cW k r (-θ) * (cW k r θ * x.2) = x.2 := by
    rw [← Matrix.mul_assoc, cW_mul, neg_add_cancel, cW_zero, one_mul]
  change (x.1, cW k r (-θ) * (cW k r θ * x.2)) ∈ Q.DomR k r z z' at h
  rwa [e] at h

theorem rotation_radial_space_holds : RotRadSp := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz' θ Φ hΦ
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 (x.1, cW k r θ * x.2) (fun h => hx (domR_of_cW θ hz z' h)), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs (x₀.1, cW k r θ * x₀.2) (domR_cW θ hz z' hx₀)
    have hL : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)) :=
      contDiff_fst.prodMk (((LinearMap.mulLeft ℝ (cW k r θ)).toContinuousLinearMap.contDiff).comp contDiff_snd)
    exact ⟨(fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)) ⁻¹' U,
      F ∘ (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)), hU.preimage hL.continuous, hxU,
      hF.comp hL.contDiffOn (fun x hx => hx), fun x hx hg => hΦF (x.1, cW k r θ * x.2) hx (cW_Glev θ hg)⟩
  · show Φ x.1 (cW k r θ * (h * x.2 * h')) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, cW_comm θ ⟨hh.1, hh.2.1⟩, Matrix.mul_assoc h]
    exact he (x.1, cW k r θ * x.2) (domR_cW θ hz z' hx) h hh h' hh'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

section

theorem Formalism.FourierDecayAlt.P.germ_rate_bound : Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.germ_rate_bound_of_split Formalism.FourierDecayAlt.P.germ_rate_lower_bound Formalism.FourierDecayAlt.P.germ_rate_top_bound
end

section

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section WaveFF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem rdb_one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

theorem rdb_h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_fsv_dmin_contDiff (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (h1 : 1 < r + 2) :
    ContDiff ℝ ∞ (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) := by
  have e : (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) = fun g =>
      Complex.exp (Formalism.FourierDecayAlt.P.PBFV.phaseL s (Formalism.FourierDecayAlt.P.JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) :=
    funext fun g => Formalism.FourierDecayAlt.P.PBFV.fsv_dmin_one s z z' g h1
  rw [e]
  exact Complex.contDiff_exp.comp (ContinuousLinearMap.contDiff _)

theorem rdb_wvG_mem_FFl {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (s : ℂ)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' 0 Dm) : wvG z z' s J ∈ FFl k r z z' π π' 0 Dm := by
  have h1 : 1 < r + 2 := by omega
  have inv : ∀ {a b : Mx k r}, a ∈ Sset k r z → b ∈ Sset k r z' → ∀ g : Mx k r,
      Dmin k r z z' (a * g * b) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ :=
    fun ha hb g => dInv k r z z' hz hz' _ ha _ hb g _
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => fsv s (Dmin k r z z' g ⟨1, h1⟩) • F g, hU, hgU,
      (rdb_fsv_dmin_contDiff z z' s h1).contDiffOn.smul hF, fun g hgU hgG => ?_⟩
    show fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g = _
    rw [hFJ g hgU hgG]
  · intro g hg n hn
    have e : Dmin k r z z' (n * g) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_n_mem_Sset z hn) (rdb_one_mem_Sset z') g
      simpa using this
    show fsv s (Dmin k r z z' (n * g) ⟨1, h1⟩) • J (n * g) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hL g hg n hn, smul_comm]
  · intro g hg n hn
    have e : Dmin k r z z' (g * n) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_one_mem_Sset z) (rdb_n_mem_Sset z' hn) g
      simpa using this
    show fsv s (Dmin k r z z' (g * n) ⟨1, h1⟩) • J (g * n) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hR g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    show fsv s (Dmin k r z z' (h * g * h') ⟨1, h1⟩) • J (h * g * h') =
      (π h).comp ((fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g).comp (π' h'))
    rw [inv (rdb_h_mem_Sset z hh) (rdb_h_mem_Sset z' hh') g, hU g hg h hh h' hh',
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end WaveFF

theorem radial_wave_function_field : RDWaveFF := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD J hJ
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  have h1 : 1 < P.r + 2 := by omega
  refine ⟨rdb_wvG_mem_FFl hz hz' s hJ, fun x hx => ?_⟩
  simp only [resG, wvG]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord hz hz' hr x.1 hx.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_wave_orbital : RDWaveJ := by
  intro k r Wp Wq _ _ _ _ _ _ D s H _ g _
  unfold wvG
  exact PBFV.JF_mul_inv D _ (fun p hp x => by rw [BigCellZetaMinors.dmin_sgs D hp]) H g

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_start_coordinates : RDStartCoord := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have ht : ∀ Y (a b : Fin 2) l (i : Fin 6), Commute (X.t Y a b) (X.op l i) :=
    fun Y a b l i => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i
  intro Y a b l x hx
  have hm : Commute (X.QQ Y a b) x := by
    rw [Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 0) (ht (star Y) b a l 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 3) (ht (star Y) b a l 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 1) (ht (star Y) b a l 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 2) (ht (star Y) b a l 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 4) (ht (star Y) b a l 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 5) (ht (star Y) b a l 2)
  rw [hQ Y, Matrix.smul_apply]
  exact hm.smul_left _

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_operator_locality : RDOpLocal := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ f₁ f₂ h g hg
  have hO := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus (k := k) (r := r) D.z D.z'
  have h' : ∀ x ∈ B.GV k r, x ∈ Q.OmPlus k r D.z D.z' → f₁ x = f₂ x := fun x hx hxO => h x ⟨hx, hxO⟩
  exact ⟨Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opApply_congr_GV Θ hO h' g hg.1 hg.2,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hO h' g hg.1 hg.2⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end
