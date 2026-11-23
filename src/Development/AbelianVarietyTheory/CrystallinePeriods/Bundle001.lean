module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism
open scoped Formalism.Per

namespace GlobalTheory.CrisLoc

variable (l : ℕ) [Fact l.Prime]

theorem exists_root_ne_one : ∃ e : Per.Fl l, e.untilt = 1 ∧ e ≠ 1 := by
  first | exact @CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one | exact CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one .. | (intros; apply CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one <;> assumption)

theorem bcris_away (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsLocalization.Away (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1)) (Per.Bcris l) := by
  first | exact @CrisAway.Bridge.CrisLoc.bcris_away | exact CrisAway.Bridge.CrisLoc.bcris_away .. | (intros; apply CrisAway.Bridge.CrisLoc.bcris_away <;> assumption)

theorem bdR_away (b : Per.AinfP l) (hb : Per.kerP l = Ideal.span {b}) :
    IsLocalization.Away (algebraMap (Per.AinfP l) (Per.BdRp l) b) (Per.BdR l) := by
  first | exact @DeRhamAway.Bridge.CrisLoc.bdR_away | exact DeRhamAway.Bridge.CrisLoc.bdR_away .. | (intros; apply DeRhamAway.Bridge.CrisLoc.bdR_away <;> assumption)

theorem mem_fil_neg (b : Per.AinfP l) (hb : Per.kerP l = Ideal.span {b}) (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap (Per.AinfP l) (Per.BdRp l) b) ^ n =
        algebraMap (Per.BdRp l) (Per.BdR l) y := by
  first | exact @FiltrationNeg.Bridge.CrisLoc.mem_fil_neg | exact FiltrationNeg.Bridge.CrisLoc.mem_fil_neg .. | (intros; apply FiltrationNeg.Bridge.CrisLoc.mem_fil_neg <;> assumption)

theorem unit_of_root (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) := by
  first | exact @UnitOfRootAlt.Bridge.CrisLoc.unit_of_root | exact UnitOfRootAlt.Bridge.CrisLoc.unit_of_root .. | (intros; apply UnitOfRootAlt.Bridge.CrisLoc.unit_of_root <;> assumption)

theorem unit_of_root_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) := by
  first | exact @UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB | exact UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB .. | (intros; apply UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB <;> assumption)

theorem bcris_hom_ext {R : Type*} [CommRing R] {f g : Per.Bcris l →+* R}
    (h : ∀ x : Per.Acris l, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  CrisHomExtUnit.Bridge.CrisLoc.bcris_hom_ext_u l h

theorem exists_mul_pow_eq (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) (b : Per.Bcris l) :
    ∃ (n : ℕ) (x : Per.Acris l), b * algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1)) ^ n = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  first | exact @MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq | exact MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq .. | (intros; apply MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq <;> assumption)

theorem exists_pow_mul_eq_zero (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) {x : Per.Acris l}
    (hx : algebraMap (Per.Acris l) (Per.Bcris l) x = 0) :
    ∃ n : ℕ, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n * x = 0 := by
  first | exact @PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero | exact PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero .. | (intros; apply PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero <;> assumption)

theorem bdR_hom_ext {R : Type*} [CommRing R] {f g : Per.BdR l →+* R}
    (h : ∀ x : Per.BdRp l, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  DeRhamHomExtUnit.Bridge.CrisLoc.bdR_hom_ext_u l h

theorem constantCoeff_root_ne_zero (e : Per.Fl l) (hne : e ≠ 1) :
    WittVector.constantCoeff (Per.tm e - 1 : Per.Ainf l) ≠ 0 := by
  first | exact @RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero | exact RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero .. | (intros; apply RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero <;> assumption)

end GlobalTheory.CrisLoc
end

section

namespace GlobalTheory.CrisIncl
open Formalism
open scoped Formalism.Per


open Reformulated.AutPerF in
theorem exists_incl (l : ℕ) [Fact l.Prime] : ∃ ι : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l ι := by
  exact (CrisDeRhamLog.Bridge.CrisIncl.exists_incl l).imp fun _ h => ⟨h.1, h.2⟩

theorem exists_restrict (l : ℕ) [Fact l.Prime] (ι : Per.Bcris l →+* Per.BdR l) (h : Per.IsCrisDR l ι) :
    ∃ j : Per.Acris l →+* Per.BdRp l,
      (∀ x : Per.Acris l,
        ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧
      (∀ s : Per.Acris0 l, j (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
        algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) ∧
      ∀ n : ℕ, ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Per.Ainf l,
        Per.ev l n (((l : ℕ) : Per.BdRp l) ^ N * j x) =
          Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  exact CrisRestriction.Bridge.CrisIncl.exists_restrict l ι ⟨h.1, h.2⟩

theorem factorial_mul_ev (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (y : Per.BdRp l) (he : e.untilt = 1)
    (h : Per.IsLog l e y) (n : ℕ) :
    ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * Per.ev l n y =
      Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) ^ (k + 1)) := by
  first | exact @FactorialMulEvaluation.Bridge.CrisIncl.factorial_mul_ev | exact FactorialMulEvaluation.Bridge.CrisIncl.factorial_mul_ev .. | (intros; apply FactorialMulEvaluation.Bridge.CrisIncl.factorial_mul_ev <;> assumption)

theorem isLog_of_partial (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) (y : Per.BdRp l)
    (h : ∀ n : ℕ, ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) ^ (k + 1) ∧
      Per.ev l n y = Ideal.Quotient.mk _ c) : Per.IsLog l e y := by
  first | exact @LogOfPartial.Bridge.CrisIncl.isLog_of_partial | exact LogOfPartial.Bridge.CrisIncl.isLog_of_partial .. | (intros; apply LogOfPartial.Bridge.CrisIncl.isLog_of_partial <;> assumption)

theorem log_unique (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) (y y' : Per.BdRp l)
    (h : Per.IsLog l e y) (h' : Per.IsLog l e y') : y = y' := by
  first | exact @LogUniqueAlt.Bridge.CrisIncl.log_unique | exact LogUniqueAlt.Bridge.CrisIncl.log_unique .. | (intros; apply LogUniqueAlt.Bridge.CrisIncl.log_unique <;> assumption)

theorem incl_aB (l : ℕ) [Fact l.Prime] (ι : Per.Bcris l →+* Per.BdR l) (h : Per.IsCrisDR l ι) (a : Per.Ainf l) :
    ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l)
      (algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) a)) := by
  exact CrisInclusionPeriod.Bridge.CrisIncl.incl_aB l ι ⟨h.1, h.2⟩ a

end GlobalTheory.CrisIncl
end

section

open scoped Formalism.Per

namespace GlobalTheory.AdicMaps

open Formalism

noncomputable section

section Gen
variable {R S : Type} [CommRing R] [CommRing S]

def levMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (n : ℕ) :
    R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (Reformulated.AutPerF.pow_le_comap_pow hf n)

def adicMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  Reformulated.AutPerF.adicMap I J f hf

theorem adicMap_alg (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (r : R) :
    adicMap I J f hf (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r) := by
  first | exact @AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg | exact AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg .. | (intros; apply AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg <;> assumption)

abbrev PHat (p : ℕ) (R : Type) [CommRing R] : Type := AdicCompletion (Ideal.span {(p : R)}) R

def padicMap (p : ℕ) (f : R →+* S) : PHat p R →+* PHat p S :=
  Reformulated.AutPerF.adicMap _ _ f (Reformulated.AutPerF.span_natCast_le_comap p f)

theorem padicMap_alg (p : ℕ) (f : R →+* S) (r : R) :
    padicMap p f (algebraMap R (PHat p R) r) = algebraMap S (PHat p S) (f r) := by
  first | exact @PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg | exact PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg .. | (intros; apply PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg <;> assumption)

end Gen

theorem exists_acris_completion (l : ℕ) [Fact l.Prime] :
    ∃ e : Per.Acris l ≃+* AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l),
      ∀ s : Per.Acris0 l, e (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
        algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l)) s := by
  first | exact @CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion | exact CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion .. | (intros; apply CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion <;> assumption)

theorem coeff_galois (l : ℕ) [Fact l.Prime] (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : Per.Fl l)
    (n : ℕ) (y : Per.OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    PreTilt.coeff n (Per.σF g x) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (Per.σO g y) := by
  first | exact @AdicCoeffGalois.Bridge.AdicMaps.coeff_galois | exact AdicCoeffGalois.Bridge.AdicMaps.coeff_galois .. | (intros; apply AdicCoeffGalois.Bridge.AdicMaps.coeff_galois <;> assumption)

end

end GlobalTheory.AdicMaps
end

section

noncomputable section
namespace GlobalTheory.CrisMaps
open Formalism
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

@[irreducible] def frob (l : ℕ) [Fact l.Prime] : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.frob l (Per.OC l)

@[irreducible] def gal (g : Per.Gq l) : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.map l (Per.σO g)

structure Extends (f : Per.Ainf l →+* Per.Ainf l) (F : Per.Acris l →+* Per.Acris l) : Prop where
  mem : ∀ y ∈ Per.Acris0 l, Per.extP f y ∈ Per.Acris0 l
  env : ∀ s : Per.Acris0 l, F (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
    algebraMap (Per.Acris0 l) (Per.Acris l) ⟨Per.extP f s, mem _ s.2⟩
  alg : ∀ a : Per.Ainf l, F (algebraMap (Per.Ainf l) (Per.Acris l) a) = algebraMap (Per.Ainf l) (Per.Acris l) (f a)

theorem frob_extends (l : ℕ) [Fact l.Prime] : Extends (Per.φA l) (frob l) := by
  unfold frob; first | exact (fun h => ⟨h.mem, h.env, h.alg⟩) (FrobeniusExtendsCris.Bridge.CrisMaps.frob_extends ..)

theorem gal_extends (g : Per.Gq l) : Extends (Per.σA g) (gal g) := by
  unfold gal; first | exact (fun h => ⟨h.mem, h.env, h.alg⟩) (FrobeniusExtendsStructure.Bridge.CrisMaps.gal_extends ..)

theorem frob_gal (g : Per.Gq l) (x : Per.Acris l) : frob l (gal g x) = gal g (frob l x) := by
  unfold frob gal; first | exact @FrobeniusGalois.Bridge.CrisMaps.frob_gal | exact FrobeniusGalois.Bridge.CrisMaps.frob_gal .. | (intros; apply FrobeniusGalois.Bridge.CrisMaps.frob_gal <;> assumption)

theorem φB_algebraMap (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (frob l x) := by
  unfold frob; first | exact @FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap | exact FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap .. | (intros; apply FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap <;> assumption)

theorem σB_algebraMap (g : Per.Gq l) (x : Per.Acris l) :
    Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (gal g x) := by
  unfold gal; first | exact @CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap | exact CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap .. | (intros; apply CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap <;> assumption)

end GlobalTheory.CrisMaps
end
end
