module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfBis
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle009
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle003
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.Top
namespace UpperTheory.V.Aut
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def IsAut4Alt (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop := _root_.UpperTheory.V.Z.Win.IsAutQA ι r.toHomUnits
def SymplecticFourImageDense : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t →
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → OfCase D h e ψ →
      D.Fin0 ∧ D.NoEnd ∧ ∃ ι : PadicAlgCl l ≃+* ℂ, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι)
end UpperTheory.V.Aut
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi
section Type_
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
def IsTypeAlt {m : ℕ} (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) : Prop :=
  IsOpen (τ₀.ker : Set (KT n wt)) ∧
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Nontrivial M] (ρ : Representation ℂ (GV n wt) M) (σ : ∀ u, SmIrr (GLw n (wt u))),
    (∀ u, IsoSum (M := M) (by classical exact ρ.comp (MonoidHom.mulSingle (fun u => GLw n (wt u)) u)) ⊤ (σ u)) →
    ((∃ F : Fin m → M, F ≠ 0 ∧ ∀ (k : KT n wt) i, ∑ j, τ₀ k i j • ρ k (F j) = F i) ↔
      ∀ u rc, _root_.UpperTheory.Zero.LLC.IsRecT (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (σ u))))
end Type_
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
namespace CaseU
variable (l L) (n : ℕ)
variable {l L}
variable (s : HidaSetting l L Ω)
variable {s} (V : s.Lev)
variable {V} (Q : QData V)
variable {n} {c : Coef l} {m : ℕ}
variable (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)
def TypeForAlt (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : Prop :=
  ∀ t, r.IsTeich t → _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
    fun u i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))
variable (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
structure UnitaryPointProperties (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  form : ∃ P, V.frame.IsForm c.O n ρ P
  type : ∀ t, r.IsTeich t → ∀ u : s.St, ∃ g : GL (Fin n) (Qbar l), ∀ x ∈ V.frame.Iu u,
    ((g * ρ x * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => algebraMap c.O (Qbar l) (t i x)
  cusp : Af.IsIrr ρ → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧ HasWt ι s π lam
  aut : ∃ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) ∧
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ∧
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) ∧
    (∀ w, IsSplitAt w → ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
    ∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧
      fixd τ.ρ (Kc _ n 1) ≠ ⊥
variable {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
variable {r} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
structure UnitaryHeckeData : Type where
  m : ℕ
  τ₀ : KT n (wt s) →* GL (Fin m) c.O
  type : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀
  θ : (hset Q τ₀).X.I.T →* Λ.Λˣ
  theta : IsTheta Q τ₀ Λ θ
  isWt : (hset Q τ₀).IsWt θ
  a : (hset Q τ₀).Op → c.O
  res : IsRes Q r τ₀ a
variable {Q ι Λ} (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev)
abbrev UnitaryHeckeData.M := (hset Q R.τ₀).MK R.θ R.a K
def UnitaryHeckeData.IsJ (J : Ideal B.B) : Prop := (hset Q R.τ₀).IsJ R.θ R.a K B.u.D B.u.ψ (Λ.toPair B.u) J
end CaseU
end UpperTheory.V.Hi
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.J.D
def TypeVAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ : SmIrr (GLw n w)), π.IsLocComp w τ →
    ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → ∀ rc, Win.IsRecV h rc → IsTypeWD h χ (rc (algNorm τ)) →
    ∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i (g : Ine (F := L) A), ω i (artOf h (ineIncl h g)) = χ i g
def PotentiallySemistableType : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ : SmIrr (GLw n w)), π.IsLocComp w τ →
    ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → (∀ rc, UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ))) →
    ∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i (g : Ine (F := L) A), ω i (artOf h (ineIncl h g)) = χ i g
end UpperTheory.V.Z.J.D
end
end
end

section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
namespace UpperTheory.V.Af
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
def AutOnAlt (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Qbar l ≃+* ℂ) (j : ℤ)
    (a : G ℚ Ω → Matrix (Fin n) (Fin n) (Qbar l)) : Prop :=
  ∃ (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (ρ : G K Ω →* GL (Fin n) (Qbar l)),
    (∀ s : G K Ω, (ρ s : Matrix (Fin n) (Fin n) (Qbar l)) = a (s.restrictScalars ℚ)) ∧ _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw ρ (cycBar K Ω l ^ j))
end UpperTheory.V.Af
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
section Sym
variable (R : Type) [CommRing R]
variable {Γ k : Type} [Group Γ] [Field k]
end Sym
section Cong
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {n : ℕ}
end Cong
section Gal
variable {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
variable {F : Type} [Field F] [NumberField F] [Algebra F Ω]
variable [CharZero Ω] [IsAlgClosure ℚ Ω]
structure IsSeedAlt {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (ι : Qbar l ≃+* ℂ) (c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω)
    (ψ τ : Fin n → _root_.Formalism.ConjugateSelfDual.G L Ω →* (Qbar l)ˣ) (m : Fin n → ℤ) (ka : _root_.Formalism.ConjugateSelfDual.G L Ω →* (Qbar l)ˣ) (r : _root_.Formalism.ConjugateSelfDual.G L Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  irr : IsIrr r
  pair : ∃ P : GL (Fin n) (Qbar l), (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∧ IsPair c r 1 P
  res : ResSum r ψ
  away : TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka)
end Gal
end UpperTheory.V.Sd
end
end
end

section

noncomputable abbrev UpperTheory.V.Z.Win.WitA.isobaricDense := @UpperTheory.V.Z.Win.WitA.iso'
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalN.V
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}
theorem woConj'_alt (k : _root_.UpperTheory.V.Z.Win.WDT ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : _root_.UpperTheory.V.Z.Win.WDT ι r' y := k.of_conj hl P hP
end UpperTheory.GalN.V
end
end
end

section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.Pr
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
def AutPtAlt (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka)
end
end UpperTheory.V.Pr
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
def OrdVan2Alt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
    (x : B.Pt) (h : s.Wt n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), V.S' = s.S → 2 ≤ n → n ≤ 4 →
    r.V0ok → x.Arith h → x.D = GDet.ofRep (mat ρ) → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (ρ.comp V.pr) →
    Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → V.frame.IsForm c.O n ρ P → (∀ g ∈ V.frame.I0, ρ g = 1) →
    (∀ (v : Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    RegDet V.frame c.O ρ P → ∀ z, IsOrdCoc V.frame ρ P r.Ip x.psi z → ∃ Y, ∀ g, z g = dY V.frame (mat ρ) Y g
end UpperTheory.V.Th
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
abbrev _root_.UpperTheory.V.Loc.localArtinReciprocity_type : Prop := ∀ (H : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w),
    ∃ a, IsLocalArtin h a
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.P
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem toTL'_alt (_N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (k : IsRecT h rc) : IsRecT h rc := k
end UpperTheory.V.Z.Desc.P
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BcPolar
theorem bc_regAlg_polarizedPair_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  intro hL F K _ _ _ _ _ _ _ h2 a ha π χ P hreg hpol hBC
  refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ?_⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F K)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hBC.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · obtain ⟨χ', hs, hd⟩ := GlobalTheory.T.base_change_dual_compatible hL.aut.js.1 hL.aut.gk F K h2 a ha π χ P hpol hBC
    obtain ⟨k, hk⟩ := GlobalTheory.BcPolar.exists_sign_twist χ' hs a
    refine ⟨χ' * quadChar K ^ k, fun v => (hk v).trans (zpow_natCast _ _), ?_⟩
    rwa [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
end GlobalTheory.BcPolar
end
end
