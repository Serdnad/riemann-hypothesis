module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.expansion_originValues_sum_modPow : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (D' : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal W) D' A G) (k e : ℕ) (σ' : H0 U.LG.L k) (f' : ∀ x, D'.toPre.SecB k x) (w : D'.toPre.X → W), (∀ x, OrigVal D'.toPre (f' x) (w x)) → U.ExpandsAt e k σ' f' → ∃ S : Finset D'.toPre.X, (∀ x ∉ S, w x ∈ maximalIdeal W ^ (e + 1)) ∧ ∀ J', Good U.LG.L (cpt W) J' → ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW G) (cpt W) J' = stalkOf (cpt W) (∑ x ∈ S, w x + c) * (val U.LG.rig (idW W) (cpt W) J').val ^ k := by
  first | exact @GlobalTheory.Mum.expandsAt_origVal | exact GlobalTheory.Mum.expandsAt_origVal | (intros; apply GlobalTheory.Mum.expandsAt_origVal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem famTw_eq_of_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  intro R _ _ I D N σ F₀ s hs
  have hL := D.P.isLB
  refine fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) (sec_ext' hL fun y J hJ => ?_)
  show sval (termPull D (Kb R) (TwF σ) N α (s.s α)) (𝟙 _) y J = _
  refine (sval_pullOver _ _ _ _ hJ).trans ?_
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, ← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ]
  congr 1
  have e : (famMap D (Kb R) (TwF σ)).left ≫ (DegPre.prB D (Kb R)).left = (DegPre.prB D (TwF σ)).left :=
    congrArg (fun q => q.left) (famMap_snd D (Kb R) (TwF σ))
  exact (Category.assoc _ _ _).trans (congrArg (fun q => 𝟙 _ ≫ q) e)

end GlobalTheory.Mum.Conj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_chart_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) →
    ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  intro R _ _ A N σ c t t' h j
  have ht : @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' =
      c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t :=
    GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun i => h i
  have e : secTw A N σ t' = σ c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ))))
      (secTw A N σ t) := by
    unfold secTw
    rw [show t' = @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' from rfl,
      ht, map_smulₛₗ]
    rfl
  rw [e]
  rfl

end GlobalTheory.Mum.Conj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), SecTw σ t (secTw A N σ t) := by
  first | exact @GlobalTheory.Mum.Conj.secTw_isTwist | exact GlobalTheory.Mum.Conj.secTw_isTwist | (intros; apply GlobalTheory.Mum.Conj.secTw_isTwist <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s s' s'' : Fam D (Kb R) N), (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) → ∀ α j, ((famTw D N σ s'').s α).f j = ((famTw D N σ s).s α).f j + ((famTw D N σ s').s α).f j := by
  first | exact @GlobalTheory.Mum.Conj.famTw_add_f | exact GlobalTheory.Mum.Conj.famTw_add_f | (intros; apply GlobalTheory.Mum.Conj.famTw_add_f <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N), Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  first | exact @GlobalTheory.Mum.Conj.famTw_isSmul | exact GlobalTheory.Mum.Conj.famTw_isSmul | (intros; apply GlobalTheory.Mum.Conj.famTw_isSmul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_add_chart | exact GlobalTheory.Mum.Conj.secTw_add_chart | (intros; apply GlobalTheory.Mum.Conj.secTw_add_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  first | exact @GlobalTheory.Mum.Conj.symLift_thTw | exact GlobalTheory.Mum.Conj.symLift_thTw | (intros; apply GlobalTheory.Mum.Conj.symLift_thTw <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  first | exact @GlobalTheory.Mum.Conj.txFrame_frTw | exact GlobalTheory.Mum.Conj.txFrame_frTw | (intros; apply GlobalTheory.Mum.Conj.txFrame_frTw <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R), Function.Bijective (famTw D N σ) := by
  first | exact @GlobalTheory.Mum.Conj.FamBij.famTw_bijective | exact GlobalTheory.Mum.Conj.FamBij.famTw_bijective | (intros; apply GlobalTheory.Mum.Conj.FamBij.famTw_bijective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R), Function.Bijective (secTw A N σ) := by
  first | exact @GlobalTheory.Mum.Conj.secTw_bijective | exact GlobalTheory.Mum.Conj.secTw_bijective | (intros; apply GlobalTheory.Mum.Conj.secTw_bijective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R), σ.comp τ = AlgHom.id _ _ → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (a b : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), IsActOf A.A A.L N (thTw A N τ θ) a b → IsActOf A.A A.L N θ (secTw A N σ a) (secTw A N σ b) := by
  first | exact @GlobalTheory.Mum.Conj.isActOf_secTw | exact GlobalTheory.Mum.Conj.isActOf_secTw | (intros; apply GlobalTheory.Mum.Conj.isActOf_secTw <;> assumption)
end
