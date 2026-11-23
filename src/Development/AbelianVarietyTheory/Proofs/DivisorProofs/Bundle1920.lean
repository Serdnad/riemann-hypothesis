module

import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.DetNormOneGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.TrMult


end GlobalTheory.TrMult
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.EllTraceProof
open GlobalTheory.TruncKer

end GlobalTheory.EllTraceProof
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.LeviArch
open GlobalTheory.LeviPlane
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.LeviArch
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.UnipMem

open GlobalTheory.LeviPlane Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.UnipMem
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.GenFibreLine

theorem genericFibre_subsingleton : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) n i) := by
  intro q _ T _ _ _ hA hq A _ _ _ _ _ hind n i hn
  haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
  have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left (Polynomial T) A
    (TensorProduct T (Polynomial T) (FractionRing T)) hind
  let eX : TensorProduct (Polynomial T) (TensorProduct T (Polynomial T) (FractionRing T)) A ≃+*
      TensorProduct T (FractionRing T) A :=
    (Algebra.TensorProduct.comm (Polynomial T) _ A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange T (Polynomial T) (Polynomial T) A (FractionRing T)).toRingEquiv.trans
        (Algebra.TensorProduct.comm T A (FractionRing T)).toRingEquiv)
  let eK : Polynomial (FractionRing T) ≃+* TensorProduct T (Polynomial T) (FractionRing T) :=
    (polyEquivTensor T (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T (FractionRing T) (Polynomial T)).toRingEquiv
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h2
  let c : Cocone D := ⟨CommRingCat.of (TensorProduct T (FractionRing T) A),
    s ≫ (Functor.const J).map (CommRingCat.ofHom (eX : _ →+* _))⟩
  have hc : IsColimit c := hs.ofIsoColimit (Cocone.ext eX.toCommRingCatIso (fun j => rfl))
  have hqA : IsUnit (q : c.pt) := by
    simpa using hq.map (algebraMap T (TensorProduct T (FractionRing T) A))
  suffices h0 : ∀ x : Ht q (sp (TensorProduct T (FractionRing T) A)) n i, x = 0 from
    ⟨fun x y => by rw [h0 x, h0 y]⟩
  intro x
  obtain ⟨j, z, hz⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q D c hc n i).1 x hqA
  let g : TensorProduct T (Polynomial T) (FractionRing T) →+* D.obj j := (t.app j).hom
  letI : Algebra (Polynomial (FractionRing T)) (D.obj j) := (g.comp eK.toRingHom).toAlgebra
  haveI : Algebra.Etale (Polynomial (FractionRing T)) (D.obj j) := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective eK.bijective) (hst j).1
  haveI := GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed q (FractionRing T) (D.obj j) hqK n i hn
  rw [← hz, Subsingleton.elim z 0, map_zero]

end GlobalTheory.EtC.GenFibreLine
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DetDecomp

open GlobalTheory.UTrans

theorem hf_single {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    hf σ M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [hf, Pi.single_apply]

theorem isU_mat {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M γ : Matrix (Fin n) (Fin n) R)
    (h : IsU σ M γ) : γᵀ * M * γ.map σ = M := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hf_single] at this
  rw [← this]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_aniso {K : Type} [Field K] [CharZero K] {n : ℕ} (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ a b, σ (M a b) = M b a) {i j : Fin n} (hij : M i j ≠ 0) :
    ∃ x : Fin n → K, hf σ M x x ≠ 0 := by
  by_contra hno
  push_neg at hno
  set x : Fin n → K := Pi.single i 1
  set y : Fin n → K := Pi.single j 1
  have hm0 : hf σ M x y ≠ 0 := by rw [hf_single]; exact hij
  have hc := Calc.hf_conj σ M hσ hM x y
  have e : hf σ M (x + hf σ M x y • y) (x + hf σ M x y • y) = hf σ M x x + σ (hf σ M x y) * hf σ M x y
      + hf σ M x y * hf σ M y x + hf σ M x y * σ (hf σ M x y) * hf σ M y y := by
    simp only [Calc.hf_add_left, Calc.hf_add_right, Calc.hf_smul_left, Calc.hf_smul_right]
    ring
  rw [hno, hno x, hno y, ← hc] at e
  have hs : σ (hf σ M x y) ≠ 0 := (map_ne_zero σ).2 hm0
  have : (2 : K) * (σ (hf σ M x y) * hf σ M x y) = 0 := by linear_combination -e
  rcases mul_eq_zero.1 this with h2 | h2
  · exact two_ne_zero h2
  · exact mul_ne_zero hs hm0 h2

theorem refl_isU_det {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) R) (hM : ∀ a b, σ (M a b) = M b a) (x : Fin n → R) {Q r z : R}
    (hQ : hf σ M x x = Q) (hrQ : r * Q = 1) (hcr : σ r = r) (hz : z * σ z = 1) :
    IsU σ M (tv σ M x ((z - 1) * r)) ∧ (tv σ M x ((z - 1) * r)).det = z := by
  refine ⟨Calc.isU_tv σ M hσ hM x _ ?_, ?_⟩
  · rw [hQ, map_mul, map_sub, map_one, hcr]
    linear_combination r * hz + (z - 1) * (σ z - 1) * r * hrQ
  · rw [Calc.tv_det, hQ]
    linear_combination (z - 1) * hrQ

variable {D : D7}

theorem hf_incA (V : HSp D) (x0 : Fin V.rank → D.host.E) :
    hf (cA D) (V.gram.map (incA D))ᵀ (fun a => incA D (x0 a)) (fun a => incA D (x0 a)) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA,
    starRingEnd_apply]

theorem exists_aniso_gram (V : HSp D) (hV : 0 < V.rank) :
    ∃ x0 : Fin V.rank → D.host.E, hf (starRingEnd D.host.E) V.gramᵀ x0 x0 ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, V.gramᵀ i j ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply GlobalTheory.LevelSubgroup.gram_det_ne_zero V
    have h0 : V.gram = 0 := Matrix.ext fun a b => hne b a
    rw [h0]
    haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
    exact Matrix.det_zero
  exact exists_aniso _ (fun a => star_star a) _ (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) hij

theorem exists_det_eq (V : HSp D) (hV : 0 < V.rank) (z : Formalism.L2.Theta.AE D) (hz : z * cA D z = 1) :
    ∃ g : GA D V, (mt V g).det = z := by
  obtain ⟨x0, hx0⟩ := exists_aniso_gram V hV
  have hqs : star (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = hf (starRingEnd D.host.E) V.gramᵀ x0 x0 :=
    Calc.hf_conj (starRingEnd D.host.E) V.gramᵀ (fun a => star_star a) (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) x0 x0
  have hrQ : incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ * incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have hcr : cA D (incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, hqs]
  have hMA : ∀ a b, cA D ((V.gram.map (incA D))ᵀ a b) = (V.gram.map (incA D))ᵀ b a := fun a b => by
    simp only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨hU, hdet⟩ := refl_isU_det (cA D) GlobalTheory.DualPairCheck.cA_cA _ hMA _ (hf_incA V x0) hrQ hcr hz
  generalize tv (cA D) ((HSpace.gram V).map ⇑(incA D))ᵀ (fun a ↦ (incA D) (x0 a))
    ((z - 1) * (incA D) (hf (starRingEnd D.host.E) (HSpace.gram V)ᵀ x0 x0)⁻¹) = γ at hU hdet
  have hzu : IsUnit z := ⟨⟨z, cA D z, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hmat := congrArg Matrix.transpose (isU_mat (cA D) _ _ hU)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
    ← Matrix.mul_assoc] at hmat
  have hunit := (Matrix.isUnit_iff_isUnit_det γ).2 (by rw [hdet]; exact hzu)
  refine ⟨⟨hunit.unit, ?_⟩, ?_⟩
  · show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) hunit.unit.1 * JR (AF D.host.F) V.gram * hunit.unit.1 =
      JR (AF D.host.F) V.gram
    rw [IsUnit.unit_spec]
    exact hmat
  · show (hunit.unit.1).det = z
    rw [IsUnit.unit_spec]
    exact hdet

theorem det_blk {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (P : Matrix (Fin p) (Fin p) R)
    (Q : Matrix (Fin q) (Fin q) R) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q).det = P.det * Q.det := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem skewGram_det_ne (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e).det ≠ 0 := by
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, Matrix.det_smul, det_blk, Matrix.det_transpose, Matrix.det_transpose]
  exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
    (mul_ne_zero (GlobalTheory.LevelSubgroup.gram_det_ne_zero A) (GlobalTheory.LevelSubgroup.gram_det_ne_zero B))

theorem det_mul_conj (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (x : UB J) : (mat x).det * cA D (mat x).det = 1 := by
  have hx : (mat x)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (mat x).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  have hd := congrArg Matrix.det hx
  have hm : ((mat x).map (cA D)).det = cA D (mat x).det := (RingHom.map_det (cA D) (mat x)).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm] at hd
  have hJ : IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).det := by
    have hm' : (J.map (incA D)).det = incA D J.det := (RingHom.map_det (incA D) J).symm
    show IsUnit (J.map (incA D)).det
    rw [hm']
    have h0 : J.det ≠ 0 := h ▸ skewGram_det_ne A B e
    refine ⟨⟨incA D J.det, incA D J.det⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    · rw [← map_mul, inv_mul_cancel₀ h0, map_one]
  apply hJ.mul_right_injective
  simp only
  rw [mul_one]
  linear_combination hd

theorem mat_blkU (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A × GA D B) :
    mat (blkU A B e h g) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (mt A g.1) (mt B g.2) := rfl

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem exists_detOne_mul_blkU : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e), 0 < d → ∀ x : UB J, ∃ (s : UB J) (g : GA D A × GA D B), (mat s).det = 1 ∧ x = s * blkU A B e h g := by
  intro D A B d e J h hd x
  have hz := det_mul_conj A B e h x
  have hzu : IsUnit (mat x).det := ⟨⟨_, _, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hcard : A.rank + B.rank = d := by simpa using Fintype.card_congr e
  obtain ⟨g, hg⟩ : ∃ g : GA D A × GA D B, (mat (blkU A B e h g)).det = (mat x).det := by
    rcases Nat.eq_zero_or_pos A.rank with hA | hA
    · obtain ⟨g, hg⟩ := exists_det_eq B (by omega) _ hz
      exact ⟨(1, g), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, one_mul, hg]⟩
    · obtain ⟨g, hg⟩ := exists_det_eq A hA _ hz
      exact ⟨(g, 1), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, mul_one, hg]⟩
  refine ⟨x * (blkU A B e h g)⁻¹, g, ?_, (inv_mul_cancel_right x _).symm⟩
  have hm : mat x = mat (x * (blkU A B e h g)⁻¹) * mat (blkU A B e h g) := by
    conv_lhs => rw [← inv_mul_cancel_right x (blkU A B e h g)]
    rfl
  have hd2 := congrArg Matrix.det hm
  rw [Matrix.det_mul, hg] at hd2
  apply hzu.mul_left_injective
  simp only [one_mul]
  exact hd2.symm

end GlobalTheory.DetDecomp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUIntegral

theorem setIntegral_conjU_eq : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∀ dom : Set (UB J), IsFundamentalDomain (ratU D.sp.cm.sig J) dom (ν.map (conjU V c h)) →
    ∀ f : UB J → ℂ, (∀ γ ∈ ratU D.sp.cm.sig J, ∀ x, f (γ * x) = f x) →
      ∫ u in fd, f (conjU V c h u) ∂ν = ∫ x in dom, f x ∂(ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd dom hdom f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := GlobalTheory.ConjUTransport.conjEquiv V c hc h
  have c1 : Continuous φ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c h
  have c2 : Continuous φ.symm := GlobalTheory.ConjUTransport.continuous_conjUInv V c hc h
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  have hme : MeasurableEmbedding (conjU V c h) := H.measurableEmbedding
  obtain ⟨hH, hfd'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain V c hc h ν fd hν hfd
  have e1 : ∫ x in conjU V c h '' fd, f x ∂(ν.map (conjU V c h)) = ∫ u in fd, f (conjU V c h u) ∂ν := by
    rw [hme.setIntegral_map, Set.preimage_image_eq _ hme.injective]
  rw [← e1]
  haveI := GlobalTheory.UnitaryVol.countable_ratU D.sp.cm.sig J
  haveI := hH
  haveI : SMulInvariantMeasure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (UB J) (ν.map (conjU V c h)) :=
    ⟨fun γ A _ => measure_preimage_mul (ν.map (conjU V c h)) γ.1 A⟩
  exact hfd'.setIntegral_eq hdom fun γ x => hf γ.1 γ.2 x

end GlobalTheory.ConjUIntegral
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB alpha beta blk)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf HasExp SplitsFully)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

namespace GlobalTheory.BigNZ.LocalPlaceUnderMembership

theorem under_locPl_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (a a' : ℕ),
    X.α = alpha G t i j → X.β = beta G i j → X.IsGood B a a' →
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ X.T := by
  classical
  intro D T L sc G μ₀ hL t i j B X a a' hα hβ hX w hw
  by_contra hn
  have hab : w ∉ GlobalTheory.LFun.above D.host.E (X.T : Set (HeightOneSpectrum (𝓞 D.host.F))) := fun h => hn h
  have hu : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
    rw [← hα, ← hβ, div_eq_mul_inv]
    exact (hX.unrα w hab).mul (hX.unrβ w hab).inv
  by_cases hs : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · rcases G.pl.mem_S0_of_sum_eq.1 hs with h | h
    · exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace hL t i j w h hu
    · exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ hL t i j w h hu
  · rcases Finset.mem_union.1 hw with h | h
    · unfold Places.W0 at h
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact hs (by rw [G.pl.under_w hv]; exact hv)
    · exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w w h rfl hs hu

end GlobalTheory.BigNZ.LocalPlaceUnderMembership
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.alpha_div_beta_ramified_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∈ S1 D →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ | exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ | (intros; apply GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ <;> assumption)
end
