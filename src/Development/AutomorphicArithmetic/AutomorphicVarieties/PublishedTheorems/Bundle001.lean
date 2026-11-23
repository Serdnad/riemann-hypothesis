module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af
open CategoryTheory
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Published

def ClozelCohC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (Ξ : GlobalTheory.GKCoh.AlgRep E a),
      (∀ τ, ∃ m, π.HasInfChar τ m ∧ AlgInfChar Ξ τ (m.map Neg.neg)) → GlobalTheory.GKCoh.IsCohFor π Ξ

def ClozelConjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a), (CG.mk π).IsRegAlg → ∀ σ : ℂ ≃+* ℂ,
      ∃ (π' : CuspSub E a) (τ τ' : SmIrr (GL (Fin a) (Af E))), IsFinComp π τ ∧ IsFinComp π' τ' ∧ IsConjBy σ τ τ' ∧
        ∀ (φ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar φ m → π'.HasInfChar (σ.toRingHom.comp φ) m

def BorelInjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (Ξ : GlobalTheory.GKCoh.AlgRep E a) (S : Finset (CuspSub E a)), (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
      (∀ π ∈ S, GlobalTheory.GKCoh.IsCohFor π Ξ ∧ HasFixed π.finPart U) → (S.card : Cardinal) ≤ cohDim ⊤ U (ratC Ξ)

section Real

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure IsGalRepOfR (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (F →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι r (rc (algNorm σ))
  pure : ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w),
    ∃ x : WD h, IsWDOf ι r x ∧ (x.lpTw ((wt : ℝ) / 2)).tempered
  weights : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z
  weights_sym : ∀ τ : F →+* Qbar l, HT τ = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw),
      IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) ∧
      (∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) τ (HT τ)) ∧
      (∀ σ, π.IsLocComp w σ → GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin a)) ≠ ⊥ →
        IsSstAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) ∧
          ∀ rc, IsRec h rc → wdAt P ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) = rc (algNorm σ)) ∧
      ∀ σ, π.IsLocComp w σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype)

end Real

def StrongMultOneReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ π π' : TR.CuspSub F a,
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B ∧ π'.HasSat w B) → π.Iso π'

def GelfandKazhdanReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a),
    ∃ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
      (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (.fin (invT a (Af F) k)) ψ) = B φ ψ) ∧
      (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = B φ ψ) ∧
      ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ) = 0

def AdmissibleReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a)
    (U : Subgroup (GL (Fin a) (Af F))), IsOpen (U : Set (GL (Fin a) (Af F))) →
    ∀ (d : ℕ) (ξ : TR.Kinf F a →* Matrix (Fin d) (Fin d) ℂ), ∃ W : Submodule ℂ π.V, FiniteDimensional ℂ W ∧
      ∀ f : (Fin d → ℂ) →ₗ[ℂ] π.V, (∀ k v, f (ξ k *ᵥ v) = π.op (.cpt k) (f v)) → (∀ u ∈ U, ∀ v, π.finPart u (f v) = f v) →
        LinearMap.range f ≤ W

section BC

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
  {a : ℕ}

def IsoTwist (π : TR.CuspSub F a) (η : HChar F) : Prop :=
  ∃ T : π.V ≃ₗ[ℂ] π.V, (∀ k φ, T (π.op (.fin k) φ) = ((chiDet a η (finGL F a k) : ℂˣ) : ℂ) • π.op (.fin k) (T φ)) ∧
    (∀ k φ, T (π.op (.cpt k) φ) = ((chiDet a η (TR.infGL F a (Unitary.toUnits k)) : ℂˣ) : ℂ) • π.op (.cpt k) (T φ)) ∧
    ∀ X φ, T (π.op (.lie X) φ) = π.op (.lie X) (T φ)


variable (E) in
omit [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
def IsQuadCharOf (η : HChar F) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) →
      η.UnrAt v ∧ η.val v = if normV w = normV v then 1 else -1

structure IsBC (π : TR.CuspSub F a) (P : CuspSub E a) : Prop where
  inf : ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m
  split : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
    ∀ σ σ', π.IsLocComp v σ → P.IsLocComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)
  unr : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → ∀ f : ℕ, normV w = normV v ^ f →
      ∃ B, π.HasSat v B ∧ (CG.mk P).HasSat w (B.map (· ^ f))

end BC

def NewformRep : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (j : ℤ), ∃ π : TR.CuspSub ℚ 2,
    (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) ∧
    ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ normV w ∣ f.M → ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Published
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Published

namespace Kato

section Sel

variable {l : ℕ} [Fact l.Prime] {C V : Type} [CommRing C] [Algebra ℤ_[l] C] [AddCommGroup V] [Module C V]
  [Module ℤ_[l] V] [IsScalarTower ℤ_[l] C V]

def quotRep {Γ : Type} [Group Γ] (ρ : Representation C Γ V) (T : Submodule ℤ_[l] V) (hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T) :
    Representation ℤ_[l] Γ (V ⧸ T) :=
  (Loc.resCoef ℤ_[l] ρ).quotient T fun g x hx => hT g x hx

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra ℚ_[l] C] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
  [ContinuousConstSMul ℤ_[l] V] (ρ : Representation C (G K Ω) V) (T : Submodule ℤ_[l] V) (hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T)

structure IsSel (z : G K Ω → V ⧸ T) : Prop where
  away : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ y ∈ Z1 (ρ.comp (Dec (F := K) A).subtype),
      (∃ x : V, ∀ s : ↥(Dec (F := K) A), (s : G K Ω) ∈ Ine (F := K) A → y s = ρ s x - x) ∧
      ∃ t : V ⧸ T, ∀ s : ↥(Dec (F := K) A), z s - T.mkQ (y s) = quotRep ρ T hT s t - t
  above : ∀ τ : K →+* Om l, ∃ j : Ω →+* Om l, j.comp (algebraMap K Ω) = τ ∧
    ∃ y ∈ Loc.finiteCocycles ((MonoidHom.snd _ _).comp (decJ K j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (decJ K j).subtype)),
      ∃ t : V ⧸ T, ∀ s : ↥(decJ K j), z s.1.1 - T.mkQ (y s) = quotRep ρ T hT s.1.1 t - t
  arch : ∀ (j : Ω →+* ℂ) (s : G K Ω), (∀ x, j (s x) = starRingEnd ℂ (j x)) → ∃ t : V ⧸ T, z s = quotRep ρ T hT s t - t

def Sel : Set (H1 (quotRep ρ T hT)) :=
  {x | ∃ z : ↥(Z1 (quotRep ρ T hT)), Submodule.Quotient.mk z = x ∧ IsSel ρ T hT z.1}

end Sel

variable {l : ℕ} [Fact l.Prime]

def coefField {k : ℕ} (g : Newform k) (ι : Qbar l ≃+* ℂ) : IntermediateField ℚ_[l] (Qbar l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun n => ι.symm (g.a n))

def cycE (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (E : IntermediateField ℚ_[l] (Qbar l)) : G F Ω →* (↥E)ˣ :=
  (Units.map (algebraMap ℤ_[l] ↥E : ℤ_[l] →* ↥E)).comp (cycZ F Ω l)

def toBar {Γ : Type} [Group Γ] {n : ℕ} {E : IntermediateField ℚ_[l] (Qbar l)} (r : Γ →* GL (Fin n) ↥E) :
    Γ →* GL (Fin n) (Qbar l) :=
  (Matrix.GeneralLinearGroup.map (algebraMap ↥E (Qbar l))).comp r

structure IsLat {Γ : Type} [Group Γ] {n : ℕ} {E : IntermediateField ℚ_[l] (Qbar l)} (r : Γ →* GL (Fin n) ↥E)
    (T : Submodule ℤ_[l] (Fin n → ↥E)) : Prop where
  fg : T.FG
  span : Submodule.span ℚ_[l] (T : Set (Fin n → ↥E)) = ⊤
  int : ∀ a : ↥E, ‖(a : Qbar l)‖ ≤ 1 → ∀ x ∈ T, a • x ∈ T
  stable : ∀ g, ∀ x ∈ T, Loc.colRep r g x ∈ T

end Kato


open Kato in
def Kato : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ), FiniteDimensional ℚ_[l] ↥(coefField g ι) ∧
    ∃ V : G ℚ Ω →* GL (Fin 2) ↥(coefField g ι), Continuous V ∧ g.Att ι (toBar V) ∧
      ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω] (r : ℕ),
        1 ≤ r → r ≤ k - 1 → 2 * r ≠ k →
        ∀ (T : Submodule ℤ_[l] (Fin 2 → ↥(coefField g ι))) (hT : IsLat (tw V (cycE ℚ Ω (coefField g ι) ^ r)) T),
          (Sel ((Loc.colRep (tw V (cycE ℚ Ω (coefField g ι) ^ r))).comp
              (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) T (fun s => hT.stable _)).Finite

end UpperTheory.V.Published
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial UpperTheory.V.Af

namespace UpperTheory.V.Published

def RepNewform : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (j : ℤ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) →
    ∃ f : Newform k, ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ normV w ∣ f.M → ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Published
end
end
