module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import GroundTheory.LocalFields.UnramifiedHensel
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.GalN.V

namespace UpperTheory.V.Z.Win

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def UnlAll (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → Unl1 r v

def PotAll (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → PotUnl r v

structure AdmRA [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutQA ι r
  level : Level l M m r
  dual : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ
  safe : (l ∣ M ∧ UnlAll r) ∨ ∀ i j, m i ≠ m j + 1

structure AdmPA [IsCMField F] [IsAlgClosure F Ω] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π
  unl : WitA ι r
  level : Lev.LevelF l M m r
  safe : (l ∣ M ∧ PotAll r) ∨ ∀ i j, m i ≠ m j + 1
end

def LevelPA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Lev.LevelF l M m r → ((l ∣ M ∧ PotAll r) ∨ ∀ i j, m i ≠ m j + 1) → WitA ι r →
      (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
      π ∈ Br.SigP K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

def AdmResA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ),
    StrictAnti m → ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
      AdmRA ι M m wt r → IsIrr (r.comp (Af.Bc.res ℚ Ω K)) → AdmPA ι M m (r.comp (Af.Bc.res ℚ Ω K))

def SplitIrr : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)), IsIrr r →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω),
      Module.finrank ℚ K = 2 ∧ IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x

def PotQ : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G ℚ Ω →* GL (Fin n) (Qbar l)), Continuous r → IsIrr r → IsAutQA ι r → UnlAll r → PotAll r

def UnlOfOne : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (Dec (F := F) A) κ →
      (∀ i j, κ i ≠ κ j * (GlobalTheory.GalOfCusp.cycBar F Ω l).comp (Dec (F := F) A).subtype) → Unl1 r v

end UpperTheory.V.Z.Win
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def LocRelT (l : ℕ) (x δ : kˣ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (P T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ C : Subgroup 𝓀[k]ˣ, ellC l _ ≤ C → ∀ θ, IsTheta π C θ → ∀ χ : (Fin n → kˣ) →* ℂˣ,
    (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd π (iwC k n C))) (χ t : ℂ)) ≠ ⊥ →
    ∀ α : Fin n → ℂ, (∀ i, α i = (resCard k : ℂ) ^ (i : ℕ) * χ (Pi.mulSingle i x)) →
    ((IsSpherical π ∨ ∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard k : ℂ) * α i') →
      P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) ∧
    ((∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard k : ℂ) * α i') → ∀ i,
      (List.ofFn fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
        (T - (χ (Pi.mulSingle i δ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0)

variable {l : ℕ} {x δ : kˣ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
  {P T : Matrix (Fin n) (Fin n) ℂ}

theorem relT' (h : LocRelT l x δ π P T) : LocRelT l x δ π P T := h

end Loc

def LocDataT : Prop :=
  LocP → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ x δ : (w.adicCompletion E)ˣ, IsUnif x ∧ IsGenMod _ (ellC l _) δ ∧ ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), (∀ rc : IrrGL (k := w.adicCompletion E) → WD hB, IsRecT hB rc → WDT ι r (rc (algNorm σ))) → LocRelT l x δ σ.ρ ((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι) ((r τ : Matrix (Fin n) (Fin n) (Qbar l)).map ι)

def WOT : type_of% @UpperTheory.V.Lev.WO := fun ι r y => WDT ι r y

end UpperTheory.V.Z.Win
end
end
