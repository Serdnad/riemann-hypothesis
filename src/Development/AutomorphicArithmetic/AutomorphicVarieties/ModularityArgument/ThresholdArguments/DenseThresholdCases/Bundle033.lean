module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ValIntLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TRigPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.SgnEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.CuspidalRankFourRegularAlgebraicTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle002
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

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
theorem UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.LinkedRigAlt := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed
  have hP : _root_.UpperTheory.V.Af.Hypotheses' := hH.toClassicalTheorems
  have hN := hP.litN
  have hA : GlobalTheory.Published.GlobalArtinReciprocity := hN.aut.art
  have hC : Pa.CohP :=
    ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hLoc : W.LocCFTAll := W.locCFT hA hC
  have hB0 : W.ProModularRingExists := W.b0Ex (W.phiAll hC)
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  have hker : η.ker = Base.galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := Pr.kaOf (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hP) Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, -⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  haveI := Pr.coefIs l c₁
  obtain ⟨R₂⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl)
    hok hbig hle hf hk2 hv2
  obtain ⟨R₃⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3
  exact ⟨_root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hL hk3,
    ka, hk2, _root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hL hk2⟩
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp
namespace UpperTheory.V.Ws
namespace Amb
variable {l : ℕ} [Fact l.Prime] (𝔞 : Amb l)
end Amb
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def PurityAtPoints (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) →
    _root_.UpperTheory.GalN.V.PureW ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
def AutmAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Irr (mapRep 𝔞.toK r) →
    _root_.UpperTheory.V.Aut.IsAut4Alt ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
namespace Tower
variable {D : Raw Ω c} (T : Tower D)
structure IsSeedAlt (ι : PadicAlgCl l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop where
  irr : Irr (P.r.comp T.G'.subtype)
  aut : ∃ (h : Fin 4 → ℤ) (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ),
    (∀ i : Fin 3, ∃ n : ℤ, 2 ≤ n ∧ h i.castSucc = h i.succ + 2 * n) ∧ T.Wts h P ∧ Continuous κ ∧ 0 < k ∧ Even (a + h 0) ∧
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) ∧
    _root_.UpperTheory.V.Z.Win.Birth.CuspidalRankFourRegularAlgebraicTotallyComplex π ∧ Af.AttC ι (Af.tw (P.r.comp (resLe T.F_le)).toHomUnits κ) π
structure SeedPairAlt (ι : PadicAlgCl l ≃+* ℂ) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O) : Prop where
  pair : (T.fr ∅).IsPair (inc h) Q
  cont : Q.Cont (maximalIdeal c₁.O)
  res : (T.fr ∅).Res ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O))
  seed : T.IsSeedAlt ι (Q.map (algebraMap c₁.O (PadicAlgCl l)))
structure PotentialModularityTower (ι : PadicAlgCl l ≃+* ℂ) {c' : Coef l} {h : c.O ≤ c'.O} (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) : Prop where
  fin : ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
    Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1}
  p1 : ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
    (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
    (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
    Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
    X.LocZero J (y : X.A →+* PowerSeries k)
  seed : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
    X.LocZero J (y : X.A →+* PadicAlgCl l)
  pur : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → _root_.UpperTheory.GalN.V.PureW ι r
  aut : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
      Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r
end Tower
def SeedIIAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    Ctx2 D → T.Ok → T.Two → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ,
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))
def PMExAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    T.Fit → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ, ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O →
      ∀ X : Space (T.fr ∅) (inc h), ∃ J, T.PotentialModularityTower ι X J
def ProModAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) : Prop :=
  ∃ (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V)
    (r₁ : G ℚ Ω →* M4 𝔞.V), T.Fit ∧ T.Deep ∧ T.PotentialModularityTower ι X J ∧ y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧
    (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧ (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧
    IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK r₁) ∧ (∀ g, IsGSp (𝔞.a c (D.th g)) (r₁ g)) ∧
    r₁.comp (resQ T.F) = (X.P.map y).r ∧
    ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), y (X.P.ψ v i s) = 𝔞.a c (D.ps i (resQ T.F s))
end UpperTheory.V.Ws
end
end
end
