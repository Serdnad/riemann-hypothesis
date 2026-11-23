module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle006
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

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
open UpperTheory.Zero.LLC GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}

def Gd (y : WD h) : Prop := UpperTheory.GalStar.Tor y ∧ y.mono0

def WDT (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := ∃ x : WD h, IsWDOf ι r x ∧ (Gd y → x = y)

variable {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem WDT.of_isWDOf (k : IsWDOf ι r y) : WDT ι r y := ⟨y, k, fun _ => rfl⟩
theorem WDT.isWDOf (k : WDT ι r y) (g : Gd y) : IsWDOf ι r y := by
  obtain ⟨x, hx, k⟩ := k
  exact k g ▸ hx
theorem WDT.of_conj (k : WDT ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : WDT ι r' y := by
  obtain ⟨x, hx, k⟩ := k
  exact ⟨x, hx.of_conj hl P hP, k⟩


variable (ι r y) in
def CmpT : Prop :=
  (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → WDT ι r y) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Induces Bw),
      Gd y → IsPstAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        wdAt (Loc.PP l) ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) = y
end Local

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def ParAtT {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (p : Gu.Par Ω w) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRecT h rc → CmpT ι r (p A h rc)

def LocGlobT (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRecT h rc →
    CmpT ι r (rc (algNorm σ))


omit [IsAlgClosure F Ω] in
def HasHTAt (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (HT : (F →+* Qbar l) → Multiset ℤ) (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O), Induces Bw →
      IsdRAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) ∧
      ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) τ (HT τ)


def CompatT : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n), Continuous r →
    (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
    ∃ HT : (F →+* Qbar l) → Multiset ℤ, (∀ τ : F →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) =
        ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((n : ℂ) - 1) / 2 - z) ∧
      ∀ w σ, π.IsLocComp w σ → LocGlobT ι r w σ ∧
        (GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → HasHTAt r HT w)

def GalUnitaryT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      ∃ (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ), Continuous r ∧ IsSSRep r ∧
        (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU σ w →
          ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, r s = 1) ∧
        (∀ (τ : E →+* Qbar l) lam, HasWeightAt σ (ι.toRingHom.comp τ) lam →
          (HT τ).map (fun k : ℤ => (k : ℂ)) = (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z) ∧
        (∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → LocGlobT ι r w τ ∧
            (GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred) → HasHTAt r HT w)) ∧
        (∀ c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P) ∧
        (IsIrr r → ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧
          (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧
          (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧
          ∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w τ →
            IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ)

def CompatTOf : Prop := RowT → PlainRec → CompatT

end UpperTheory.V.Z.Win
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}


omit [NumberField F] in
def WitAQ (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

theorem guard_of (H : PlainRec) [IsCMField F] [IsAlgClosure F Ω] {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub F n} (hreg : (CG.mk π).IsRegAlg) (ha : AttC ι r π) (hW : WitA ι r) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∨ Unl1 r w ∨ PotUnl r w) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion F) → WD h} (hrc : IsRecT h rc) {σ : SmIrr (GL (Fin n) (w.adicCompletion F))}
    (hσ : π.IsLocComp w σ) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) ∧ UpperTheory.GalStar.Tor (rc (algNorm σ)) ∧ (rc (algNorm σ)).mono0 := by
  obtain ⟨t, ht⟩ := hW.2 π hreg ha
  apply H F Ω A w h rc hrc n π t (ht w (by
    by_cases e : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · exact Or.inr ((hw.resolve_left fun k => k e).elim (hW.1 w e) id)
    · exact Or.inl e)) σ hσ

def ThruAway : Prop := PlainRec → Thru false
def AIsoTwOf : Prop := FlagLaws → WinTw → AIsoTw

end UpperTheory.V.Z.Win
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

namespace UpperTheory.V.Z.Win

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def IsAutCsdA [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutCsd0 ι r ∧ (Continuous r → WitA ι r)


omit [NumberField F] in
def IsAutQA (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      (∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π) ∧
        WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

end UpperTheory.V.Z.Win
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

variable {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem WitA.iso' [IsCMField F] (e : RepIso r r') (h : WitA ι r) : WitA ι r' :=
  have u : ∀ {r r' : G F Ω →* GL (Fin n) (Qbar l)}, RepIso r r' → ∀ v, (Unl1 r v → Unl1 r' v) ∧ (PotUnl r v → PotUnl r' v) :=
    fun e _ => ⟨fun k A hA => (k A hA).imp fun _ j => ⟨j.1.of_iso e, j.2⟩, fun k A hA => (k A hA).imp fun _ j => ⟨j.1.of_iso e, j.2⟩⟩
  ⟨fun v hv k => (u e v).2 (h.1 v hv ((u e.symm' v).1 k)), fun π hreg ha =>
    (h.2 π hreg (attC_iso e.symm' ha)).imp fun _ ht v hv => ht v (hv.imp id (u e.symm' v).2)⟩

end UpperTheory.V.Z.Win
end
end
