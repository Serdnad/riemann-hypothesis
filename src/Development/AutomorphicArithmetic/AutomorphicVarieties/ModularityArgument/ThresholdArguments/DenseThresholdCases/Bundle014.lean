module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.BOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.ExistsScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.DcMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoCopy
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.AlgInfCharIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3
namespace UpperTheory.V.Aut
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
def AutBAlt [IsCMField K] (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)) (hr : HasMult D.η r), IsPush ξ S.r.hom r → TypeI D.η r → D.IsAutIAlt ι r hr
def LemWAlt (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)), IsPush ξ S.r.hom r → TypeII D.η r → (∀ g ∈ D.η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModularDense ι W
def AutomorphyUnramifiedCoefficientsAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ),
    eO l c.O = 1 → ∀ ι : Qbar l ≃+* ℂ, ∃ g₁ : G ℚ Ω, D.Marked g₁ ∧ FinA D g₁ ∧ _root_.UpperTheory.V.Aut.AutBAlt D ι g₁ ∧ _root_.UpperTheory.V.Aut.LemWAlt D ι g₁
end UpperTheory.V.Aut
end
end
end

section




section
open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Af.weyl_complex_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WeylC := by
  intro _ E _ _ _ n
  refine ⟨((n + 1) ^ 2) ^ (n * n * Fintype.card (E →+* ℂ)), n * n * Fintype.card (E →+* ℂ), fun m hm H hH => ?_⟩
  have hb := fun i => abs_le.1 (hH i)
  let ν : Fin n → ℕ := fun k => ((k : ℕ) + 1 + H - m k.rev : ℤ).toNat
  have hν : ∀ k, (ν k : ℤ) = (k : ℕ) + 1 + H - m k.rev := fun k => Int.toNat_of_nonneg (by have := hb k.rev; omega)
  have hanti : Antitone ν := by
    cases n with
    | zero => exact fun i => i.elim0
    | succ n =>
      refine Fin.antitone_iff_succ_le.2 fun i => ?_
      have h1 := hν i.succ
      have h2 := hν i.castSucc
      have h3 : m i.castSucc.rev < m i.succ.rev := hm (Fin.rev_lt_rev.2 Fin.castSucc_lt_succ)
      simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
  have hle : ∀ k, ν k ≤ n + 2 * H := fun k => by
    have h1 := hν k
    have h2 := hb k.rev
    have h3 := k.2
    omega
  obtain ⟨P, hP, hd, hw⟩ := UpperTheory.V.Weyl.existsScalar n ν hanti _ hle
  obtain ⟨Ξ, h1, h2⟩ := UpperTheory.V.WeylC.exists_tens (E := E) P hP _ hw (n + H)
  refine ⟨Ξ, fun τ => (UpperTheory.V.WeylC.algInfChar_iff _ _ _).2 ⟨by simp [UpperTheory.V.Af.infOf], fun u => ?_⟩, ?_⟩
  · rw [h2, UpperTheory.V.Af.infOf, Multiset.map_map, Multiset.map_map]
    congr 1
    refine (Fintype.prod_equiv Fin.revPerm _ _ fun k => ?_)
    have h3 : ((ν k : ℕ) : ℂ) = (k : ℕ) + 1 + H - m k.rev := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (hν k)
    simp only [Function.comp_apply, Fin.revPerm_apply, h3]
    push_cast
    ring
  · refine h1.trans ((Nat.pow_le_pow_left hd _).trans ?_)
    rw [← pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (n * n * H), Nat.zero_le H, Nat.zero_le n]) _
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W
section Defs
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
variable [IsAlgClosure E Ω] [IsCMField E]
end Defs
def GalAEOfAlt : Prop := _root_.UpperTheory.V.Af.Hypotheses' → RowT → GalAE
def SplitSatAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (E : Type) [Field E] [NumberField E] (n c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (w : HeightOneSpectrum (𝓞 E))
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (σ : ∀ i, SmIrr (GL (Fin (d i * a i)) (w.adicCompletion E))),
    (∀ i, 1 ≤ a i ∧ 1 ≤ d i) → (∀ i, IsSpeh (cl (ρ i)) (d i) (σ i).ρ) → ∀ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), Nonempty (τ.ρ.Equiv (locProd hn w σ)) → ∀ B, GlobalTheory.LFun.HasSatGL w τ.ρ B → B = satTot w d S
def SameOfAlt : Prop := _root_.UpperTheory.V.Af.Hypotheses' → GlobalTheory.BcSpeh.BcSpeh → SatTw → SumAE → _root_.UpperTheory.V.Z.Desc.W.SplitSatAlt → OnePart → Same
def SphTAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), (∀ s ∈ Ine (F := F) A, r s = 1) → ∀ rc, IsRecT h rc →
    ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)), GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → IsWDOf ι r (rc (algNorm σ)) →
      HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := n))
def PseudoLocalDescent : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 L))
    (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ rc, IsRecT h rc →
    ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion L)), GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) →
    ∀ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) →
      (∀ s, (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ))) → IsSubquotient σ.ρ (Hi.PS ω)
end UpperTheory.V.Z.Desc.W
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix
namespace UpperTheory.V.Cu
section Alg
variable {R : Type} [CommRing R]
end Alg
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def TauExAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (K' : IntermediateField ℚ Ω) [NumberField K'], l ≠ 2 → Module.finrank ℚ K' = 2 → IsTotallyComplex K' → ¬ (l : ℤ) ∣ discr K' →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A ≤ K'.fixingSubgroup) → (∃ cc : _root_.Formalism.ConjugateSelfDual.G ℚ Ω, Sd.IsCC cc) →
    ∀ g0 ∉ K'.fixingSubgroup, ∃ (m : ℕ) (c₁ : Coef l) (κ : _root_.Formalism.ConjugateSelfDual.G K' Ω →* (Qbar l)ˣ), ∀ c₂ : Coef l, c₁.O ≤ c₂.O → ∀ j : ℕ, 1 ≤ j →
      ∃ τ s, TauDat ι K' g0 (m * j) c₂ τ s (κ ^ j)
end UpperTheory.V.Cu
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
def KapExAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (K' : IntermediateField ℚ Ω) [NumberField K'], l ≠ 2 → Module.finrank ℚ K' = 2 → IsTotallyComplex K' → ¬ (l : ℤ) ∣ discr K' →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A ≤ K'.fixingSubgroup) → (∃ cc : _root_.Formalism.ConjugateSelfDual.G ℚ Ω, Sd.IsCC cc) →
    ∃ (m : ℕ) (κ : _root_.Formalism.ConjugateSelfDual.G K' Ω →* (Qbar l)ˣ), ∀ j : ℕ, 1 ≤ j → KapDat ι K' (m * j) (κ ^ j)
end UpperTheory.V.Cu2
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Ord
section At
variable {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {n : ℕ} (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
end At
def AutYAlt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
    (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)
    (P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.PartAltAlt ι lam ξ → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}, Y.1.Y
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)
end U
def OrdScalAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (e : ℕ), c0 ≤ e → ∀ F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K e, F ≠ 0 →
    ∀ (v : H.V) (b : Fin n → ℂ), (∀ j, b j ≠ 0 ∧ H.opC ι lam d (.inr (v, j)) F = b j • F) →
      ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient (Y.σl v).ρ (PS ω) ∧
        (∀ i (y : Uo ((H.Sl v).adicCompletion L)), (ω i y : ℂ) * ι (H.finPart θ x.toRingHom lam v i y) = 1) ∧
        ∀ j : Fin n, b j = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)
def PartPtAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → lam ∈ H.admitted →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] (y : H.TK θ a K →ₐ[c.O] Qbar l),
      y.toRingHom.comp (algebraMap A _) = x.toRingHom → ∃ (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d),
        P lam d ξ Y ∧ F ≠ 0 ∧ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 ∧ ∀ i, H.opC ι lam d i F = ι (y (H.gen θ a K i)) • F
def CoreOrdAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
      [Alg.IsCO c.O (H.TK θ a K)] (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ),
      H.IsUniv θ a K (maximalIdeal _) D ψ → ∀ lam ∈ H.admitted, ∀ y : H.TK θ a K →ₐ[c.O] Qbar l,
      H.Arith θ (y.toRingHom.comp (algebraMap A _)) lam →
      ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ), P lam d ξ Y ∧ D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧
        ∀ v, ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
          ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i))
def AutUOAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ → _root_.UpperTheory.V.Z.Ord.AutYAlt (hset Q τ₀) ι fun _ _ _ Y =>
      Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
        Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)
def EndOrdAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), ∀ J : Ideal B.B, R.IsJ B K J → ENDO B ι J
end UpperTheory.V.Z.Ord
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Win UpperTheory.GalN.V
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
end Loc
section
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
theorem AdInW.toIn_alt {ι : Qbar l ≃+* ℂ} {M m : ℕ} {r : G L Ω →* GL (Fin 2) (Qbar l)} (h : AdInW ι M m r) : _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r :=
  ⟨h.cont, _root_.UpperTheory.V.Z.Win.Birth.mkCsdW' h.aut fun _ => h.wit, h.irr, h.gap, h.unr, h.away, h.above⟩
end
structure PureWeightCompatibility : Prop where
  af : _root_.UpperTheory.V.Af.Hypotheses'
  gal : GalUnitaryT
  compat : CompatT
  same : Z.Desc.W.Same
  plain : PlainRec
  desc : Z.Desc.DescUse
def PlainOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    (∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1) → PT τ
def PsOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L))), PT τ →
    ∃ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      ∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1
def EigWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G L Ω →* GL (Fin n) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∀ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    ∀ s : Weil h, (r (s : G L Ω)).val.charpoly.map ι.toRingHom =
      psPol ψ (a s)
def AboveWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → ∀ m : ℕ, 2 ≤ m →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ HT, HasHTAt r HT w → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    (∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    (∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)) ∧
      ∃ b : ℤ, ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = {b, b + m}
def AwayWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → Unlinked (ad0 r) →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)
def GoodWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := L) A, r s = 1) → (∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)
def LocSubDAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Sig.Lev k)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
    GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ (V.J n) →
    (∀ d, Sig.SDom d → Hi.dc τ (V.J n) (V.J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ)
def GalExWAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∃ r : G L Ω →* GL (Fin n) (Qbar l), GalT ι σ r ∧
      (IsIrr r → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧ Lifts σ π)
def AboveWeightAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ M m : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M → ∀ r : G L Ω →* GL (Fin 2) (Qbar l), AdInW ι M m r →
    ∃ (σ : Submodule ℂ (UA L 2 → ℂ)) (HT : (L →+* Qbar l) → Multiset ℤ), IsAutRepU σ ∧ GalT ι σ r ∧
      (∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → PT τ ∧ HasHTAt r HT w) ∧ (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → IsUnramU σ w) ∧
      ∀ v : InfinitePlace L, ∃ lam, HasWeightAt σ v.embedding lam ∧ lam.w 0 - lam.w 1 = ((m - 1 : ℕ) : ℤ)
def Branch1WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ₃ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ₃ → (∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ₃ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) →
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧ Lifts σ₃ π
def Branch2WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ' : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ' →
    (∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ' w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2) → False
def PlainAtWAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (σ : Submodule ℂ (UA L 3 → ℂ)) (π : CuspSub L 3), IsAutRepU σ →
    Lifts σ π → ∀ w, IsSplitAt w → ∀ a : (Kw w)ˣ →* ℂˣ, NoLk a → CompSub σ w ![a, 1, a⁻¹] → ∀ τ, π.IsLocComp w τ → PT τ
end UpperTheory.V.Z.Sym.W
end
end
end

section




section
namespace UpperTheory.V.ZK
theorem lemmaK_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : ∃ CK, LemmaK CK := _root_.UpperTheory.V.ZK.lemmaK_of_litN_alt hN bOdd
end UpperTheory.V.ZK
end
end

section




section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Z.Sym.Al.exists_eigenvector_in_span_of_comp_eq_trivial :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ w : Plc L, IsSplitAt w → ∀ (W : Sig.Lev (Kw w)) ψ, CompEq π w ψ → (∀ i, ∀ u ∈ W.H, ψ i u = 1) →
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π →
        ∃ φ', φ' ≠ 0 ∧ InSpan w φ φ' ∧ (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ' (g * x) = φ' g) ∧ EigT φ' w W ψ := by
  intro hLit L _ _ _ n V _ _ _ π hπ w hw W ψ ⟨hsm, τ, hτ, ⟨e⟩⟩ hψ φ hφ hc
  obtain ⟨s1, -, s3, -⟩ := secSpec L n w hw
  let N : Submodule ℂ (UA L n → V) := Submodule.span ℂ {ψ' | ∃ x ∈ locU n w, ψ' = fun g => φ (g * x)}
  let ρ : Representation ℂ (GL (Fin n) (Kw w)) (UA L n → V) := (rightReg ℂ (UA L n) V).comp (secW n w)
  have hρ : ∀ h (a : UA L n → V) g, ρ h a g = a (g * secW n w h) := fun _ _ _ => rfl
  have hst : ∀ h, ∀ a ∈ N, ρ h a ∈ N := by
    intro h a ha
    refine Submodule.span_induction (p := fun a _ => ρ h a ∈ N) ?_ (by simp) (fun _ _ _ _ h1 h2 => by
      rw [map_add (f := _)]; exact N.add_mem h1 h2) (fun c _ _ h1 => by rw [map_smul]; exact N.smul_mem c h1) ha
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨secW n w h * x, (locU n w).mul_mem (s1 h) hx, ?_⟩
    funext g
    rw [hρ, mul_assoc]
  let ν : Representation ℂ (GL (Fin n) (Kw w)) N :=
    { toFun := fun h => (ρ h).restrict (hst h)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hν : ∀ h (a : N), ((ν h a : N) : UA L n → V) = ρ h a := fun _ _ => rfl
  have hφN : φ ∈ N := Submodule.subset_span ⟨1, (locU n w).one_mem, by funext g; rw [mul_one]⟩
  have hco : ∀ a : N, CoefIn (a : UA L n → V) π := fun a =>
    (spanKeep L n V w φ a a.2).1 π hπ hc
  let b := Module.finBasis ℂ V
  let q : Fin (Module.finrank ℂ V) → N →ₗ[ℂ] π := fun i =>
    { toFun := fun a => ⟨b.coord i ∘ (a : UA L n → V), hco a _⟩
      map_add' := fun x y => Subtype.ext (by funext g; simp)
      map_smul' := fun c x => Subtype.ext (by funext g; simp) }
  haveI : Nontrivial N := ⟨⟨⟨φ, hφN⟩, 0, fun h => hφ (congrArg Subtype.val h)⟩⟩
  obtain ⟨f, hf0, hf⟩ := (isoCopy _ _ _ τ.ρ ((repOn hπ).comp (secW n w)) τ.irred
    (isoTypic L n π hπ w hw τ hτ)).2 N (Fin (Module.finrank ℂ V)) ν q
      (fun i h x => Subtype.ext rfl)
      (fun x hx => Subtype.ext (by
        funext g
        refine b.ext_elem fun i => ?_
        have : b.repr ((x : UA L n → V) g) i = 0 := congrFun (congrArg Subtype.val (hx i)) g
        simpa using this)) inferInstance
  have hinj : Function.Injective f := by
    haveI := τ.irred
    let Φ : τ.ρ.IntertwiningMap ν :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := f.map_smul
        isIntertwining' := fun g => LinearMap.ext fun x => hf g x }
    refine (Representation.IsIrreducible.injective_or_eq_zero Φ).resolve_right fun h => hf0 ?_
    exact LinearMap.ext fun x => congrArg (fun Ψ : τ.ρ.IntertwiningMap ν => Ψ x) h
  obtain ⟨v, hv0, hvJ, hvE⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_fixd_dc_eq_expo_smul_of_equiv_prinSeries hLit (Kw w) n W ψ hsm hψ τ.V τ.ρ ⟨e⟩
  refine ⟨f v, fun h => hv0 (hinj (Subtype.ext (by simpa using h))), (f v).2, ?_, ?_⟩
  · intro x hx hJ g
    have h1 := hf (cLoc w x) v
    rw [hvJ _ hJ] at h1
    have h2 := congrFun (congrArg Subtype.val h1) g
    rw [hν, hρ, s3 x hx] at h2
    exact h2.symm
  · intro d hd
    have h1 := dcMap W τ.ρ ρ (N.subtype ∘ₗ f) (fun h x => by simp [hf, hν]) (Sig.dg d) v
    rw [hvE d hd] at h1
    simpa [EigAt, ρ] using h1.symm
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Base
namespace UpperTheory.V.Z.Bc
structure HypothesesZ' : Prop where
  af : _root_.UpperTheory.V.Af.Hypotheses'
  eg : PropEG
  up : UpSol
end UpperTheory.V.Z.Bc
end
end
end
