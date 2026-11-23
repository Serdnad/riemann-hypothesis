module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CoordSpan
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TsubValInjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open GlobalTheory.HCChar (dsChar)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEG

open GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def OmDet : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ Q : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, ev k Q * ev k (OmP ε).det = physDet ε k

def ClassFn : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k k' : KG ε), physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
      trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k)

def GaInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ Λ m : Fin n → ℤ, gaW ε lam = (fun a => (Λ a : ℝ)) ∧ (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) ∧
      (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) ∧
      ∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)

def ToKType : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) →
    ∃ T₀ : S7.KType ε γ, ∀ k : S7.KG ε, ReciprocityTheory.ChartRestriction.TR.Weyl.kChar T₀ k = trK T (S7.toMK k)

def VdmSplit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (t : Fin n → ℂ),
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) = ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t * ((-1) ^ sDeg ε *
      ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2))

def PhysTor : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ),
    physDet ε (Matrix.diagonal (tor θ)) = (-1) ^ (pOf ε * qOf ε) * (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2)) *
      ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) ∧
    physDet ε (Matrix.diagonal (tor θ)) * conj (physDet ε (Matrix.diagonal (tor θ))) = (dMode ε θ : ℂ)

def NumShift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (c : Bool → ℤ) (t : Fin n → ℂ), (∀ a, t a ≠ 0) →
    ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (fun a => m a - c (ε a)) t =
      (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, t a ^ m (w.symm a)) * ∏ a, t a ^ (-c (ε a))

def RangeFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ), Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → ∀ d : ℕ,
    ∃ L : Submodule ℂ (smD ε σ), FiniteDimensional ℂ L ∧
      (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD (isDerivedOn_smE hσ) hk x ∈ L) ∧
      ∀ P : Poly n, P.totalDegree ≤ d → ∀ u : H,
        ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ L.map (smD ε σ).subtype

def BuildY : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (c : ℂ), (∀ v : D, casimir E v = c • v) →
    ∀ L : Submodule ℂ D, FiniteDimensional ℂ L → (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    ∃ Y : Submodule ℂ (TensorProduct ℂ D (Fock n)), FiniteDimensional ℂ Y ∧ tensFock L ⊓ physicalSubspace ε ≤ Y ∧
      Y ≤ physicalSubspace ε ∧ (∀ y ∈ Y, dD ε E y ∈ Y) ∧ (∀ y ∈ Y, gradT y ∈ Y) ∧
      ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y

def StrKer : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Y : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Y], (∀ y ∈ Y, dD ε E y ∈ Y) → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y),
    ∃ (Z : Submodule ℂ (TensorProduct ℂ D (Fock n))) (_ : FiniteDimensional ℂ Z)
      (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z) (Γ : TSub Z →ₗ[ℂ] TSub Z),
      Z ≤ Y ∧ (∀ y ∈ Z, dD ε E y = 0) ∧ ∀ (k : Mat n) (hk : k ∈ Kset ε),
        LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
          LinearMap.trace ℂ (TSub Z) (Γ ∘ₗ (tOp hD hZK k : TSub Z →ₗ[ℂ] TSub Z))

def StrIdx : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ d : ℕ,
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (L : Submodule ℂ D) [FiniteDimensional ℂ L],
    (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    (∀ Q : Poly n, Q.totalDegree ≤ d → ∀ u : H,
      ∫ k : KG ε, ev (toMK k) Q • σ (toMK k) u ∂(muK ε) ∈ L.map D.subtype) →
    ∀ (Y : Submodule ℂ (TensorProduct ℂ D (Fock n))) [FiniteDimensional ℂ Y], tensFock L ⊓ physicalSubspace ε ≤ Y →
      Y ≤ physicalSubspace ε → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y) (B : H →L[ℂ] H),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) →
      ∃ hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L.map D.subtype,
        LinearMap.trace ℂ (L.map D.subtype) ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) =
          ∫ k : KG ε, ev (toMK k) P * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (k := toMK k) k.2).restrict
            (fun y hy => hG _ (hK _ k.2 y hy))) ∂(muK ε)

def HWVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Z : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Z] (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z)
      (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T → ∀ Φ : W →ₗ[ℂ] TSub Z, Φ ≠ 0 →
      (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = tOp hD hZK k (Φ v)) →
      ∃ z ∈ Z, z ≠ 0 ∧ IsKHWVec ε (diagE ε (eT E) cpT cmT) γ z

def CoordFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))), FiniteDimensional ℂ Z →
    IsKStableSub ε (diagE ε (eT E) cpT cmT) Z →
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z)

def CasCoord : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M), IsGlRep E → ∀ z : TensorProduct ℂ M (Fock n),
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z → dD ε E z = 0 →
    ∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z

def AlgDatum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Gap3 ε lam →
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
    IsGlRep E → IsInfUnitary ε E → ∀ z : TensorProduct ℂ M (Fock n), z ≠ 0 → z ∈ physicalSubspace ε →
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z →
    (∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z) →
    ∀ S : Submodule ℂ M, FiniteDimensional ℂ S → IsKStableSub ε E S → (∀ s, tco s z ∈ S) →
    ∃ V : Submodule ℂ M, IsKIrrHW ε E (lowK ε lam) V ∧ V ≠ ⊥ ∧ ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v

def CptCase : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), pOf ε = 0 ∨ qOf ε = 0 →
    (∀ k, physDet ε k = 1) ∧ sDeg ε = 0 ∧
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
      FiniteDimensional ℂ X ∧ IsKIrr ε (gaW ε lam) D

def TorusId : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (Λ m : Fin n → ℤ), (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) →
    (∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)) →
    ∀ θ : Fin n → ℝ, Function.Injective (tor θ) → ∀ x : ℂ,
      ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x = ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) (tor θ) →
      (-1) ^ sDeg ε * x = dsChar ε lam θ * physDet ε (Matrix.diagonal (tor θ))

end GlobalTheory.PsCo.PcEG
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

namespace GlobalTheory.LowRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def AdelC (F : Face D A) : Prop :=
  GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (b : ℝ), Sizes D i b → ∀ t : T, PrimeToHost R t →
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s →
  ∀ P : LevelP R.Pg D.R.r ℂ, IsLocalLevel P →
  ∀ (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), IsConjChars R i t s cμ cη m →
  ∀ ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ),
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω →
  ∀ BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) →
  ∀ f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ,
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f →
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) →
  ∀ c : CoefA (Vc D i), c.Is →
  ∀ io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io →
  ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))),
    IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)) ν 𝓕 →
  ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y →
  ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
    HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y) →
    (∃ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th) ∧
    ∀ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th →
      ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ t P ev, th (adjLev P th x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l

def LiftIsCuspC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f c io =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ φ ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)),
      ∃ U ∈ R.Wall i σ, ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)), U (fun ρ => v ρ) g =
        Lift.thetaPInt ν 𝓕 (fun g h f => Datum.thetaKO ω h g f) (ptAt R i σ BW f) io (c.ext φ) (PiTensorProduct.tprod ℂ v) g


open Datum in
def FiniteZetaC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P _ ω _ f _ _ =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ,
        (∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2)) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (eulerOff D (finS R t) x / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))

def FormalDegreeUpperC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i _ σ _ _ _ _ _ _ _ =>
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ (ρ : D.what₂.Tau) (mR : Measure (Upq (Wc D i) ρ)), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ 0 < ∫ b, k b ∂mR ∧
        Real.log (∫ b, k b ∂mR)⁻¹ ≤
          2 + (D.R.r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (D.R.r : ℝ) ^ 2 * D.R.nV * ((degAt D i σ ρ : ℝ) + 2))

def GalOut (i : Fin D.R.m) (ph : ℂ) : Prop :=
    (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) ∧
    (∀ gramR c0R c0L,
      Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
      ∀ σ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i)) ∧
    ∀ σ, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK ((starRingEnd ℂ).comp σ) ∧
      ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
        starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ

def StdV (D : D7) : Prop := ∀ i : Fin D.R.m, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)

end

def ConjRatLift5 : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    GlobalTheory.Core5 R F → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) →
    ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
     GalOut R i ph

end GlobalTheory.LowRow

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

def OverPair (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ) : Prop :=
  (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (x : E))‖ < 1) ∨
    (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (IsCMField.complexConj E (x : E)))‖ < 1)

end GlobalTheory.CongW
end
end
