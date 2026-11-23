module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

abbrev Levels (E : Type) [Field E] [NumberField E] (a : ℕ) : Type :=
  ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin a) (w.adicCompletion E))

structure LocOps (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (Kw : Levels E a) (J : Type) where

  pl : J → HeightOneSpectrum (𝓞 E)
  split : ∀ j, IsSplitAt (pl j)
  away : ∀ j, ((l : ℕ) : 𝓞 E) ∉ (pl j).asIdeal

  f : ∀ j, GL (Fin a) ((pl j).adicCompletion E) →₀ ℂ
  int : ∀ j g, ‖ι.symm (f j g)‖ ≤ 1

  z : ∀ j, SmIrr (GL (Fin a) ((pl j).adicCompletion E)) → ℂ
  act : ∀ j σ, ∀ v ∈ PRep.fixed σ.ρ (Kw (pl j)), opOf σ.ρ (f j) v = z j σ • v

def SphOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ),
    (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥ → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ n : ℤ, ∃ f : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV w : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)), opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV w) B).map (· ^ n)).sum • v

structure Up (Ω : Type) [Field Ω] (l : ℕ) {E M : Type} [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [Field M] [NumberField M]
    [IsCMField M] [Algebra M Ω] [Algebra E M] [IsScalarTower E M Ω] {a : ℕ} (π : CuspSub E a) (π' : CuspSub M a) : Prop where
  scope : ∀ l' : ℕ, InScope .csd l' π (quadChar E ^ a) → InScope .csd l' π' (quadChar M ^ a)
  self : InScope .csd l π (quadChar E ^ a)
  inf : ∀ τ : M →+* ℂ, (CG.mk π').infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E M))
  weak : ∀ (l' : ℕ) [Fact l'.Prime] (ι : Qbar l' ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l')), Weak π ι r → Weak π' ι (GlobalTheory.AboveL.resTo M r)

end GlobalTheory.Cong

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def Apart (w u : HeightOneSpectrum (𝓞 E)) : Prop :=
  w.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E))


omit [IsAlgClosure E Ω] in
def SplitAtt (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ B, (CG.mk π).HasSat w B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)


omit [IsCMField E] [IsAlgClosure E Ω] in
def SstAt (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O), Pst.Induces Bw →
    IsSstAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)

def IwaAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥

def ScAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ SmGL.IsCuspidal σ.ρ

def Seed : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ScAt π w₀ →
    ∃ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), SplitAtt π ι r ∧ ∀ w, IsSplitAt w → Apart w w₀ →
      ClauseAt .ss π ι r w ∧ ClauseAt .dR π ι r w ∧ ClauseAt .crys π ι r w ∧ (IwaAt π w → SstAt r w)

structure Match (U : Submodule ℂ (UA E a → ℂ)) (π : CuspSub E a) : Prop where
  aut : IsAutRepU U
  unram : ∀ w, ¬ IsSplitAt w → IsUnramU U w
  split : ∀ w, IsSplitAt w → ∀ σ, π.IsLocComp w σ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ
  inf : ∀ τ lam, HasWeightAt U τ lam → (CG.mk π).infChar τ = infOfWeight lam

def Desc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), l.Prime → 1 ≤ a → ∀ π : CuspSub E a,
    InScope .csd l π (quadChar E ^ a) → ∃ U : Submodule ℂ (UA E a → ℂ), Match U π

structure IsLevelAway (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) : Prop where
  fin : K ≤ finU (E := E) (n := a)
  one : ∀ x ∈ K, ∀ u, ¬ Apart u w₀ → cLoc u x = 1
  compact : IsCompact (K : Set (UA E a))
  isOpen : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ ∀ x ∈ N, x ∈ finU (E := E) (n := a) → (∀ u, ¬ Apart u w₀ → cLoc u x = 1) → x ∈ K

def ActsBy {J : Type} (K : Subgroup (UA E a)) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ) : Prop :=
  ∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → ∀ j, opOf (RU E a) (t j) φ = η U j • φ

structure OfType (lam : (E →+* ℂ) → DomWeight a) (K : Subgroup (UA E a)) (U : Submodule ℂ (UA E a → ℂ)) : Prop where
  aut : IsAutRepU U
  wt : ∀ τ, HasWeightAt U τ (lam τ)
  fix : ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ

def FinU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)), IsLevelAway w₀ K →
    ∀ (lam : (E →+* ℂ) → DomWeight a) (J : Type) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ),
      (∀ j, ∀ g ∈ (t j).support, g ∈ finU (E := E) (n := a) ∧ ∃ q : ℚ, t j g = q) → ActsBy K t η → ∀ U, OfType lam K U →
      ∃ L : FinExt l, ∀ j, ι.symm (η U j) ∈ L.1

def ClosedAtL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O), Pst.Induces Bw →
    ∀ (J : (E →+* Qbar l) → Multiset ℤ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r →
    ∀ C : Set (_root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C →
      (∀ ρ ∈ C, Continuous ρ ∧ IsSstAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ (J τ)) →
      (IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ (J τ)) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype))

def Limit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∃ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), SplitAtt π ι r ∧
      ∀ w, IsSplitAt w → Apart w w₀ →
        ClauseAt .ss π ι r w ∧ ClauseAt .crys π ι r w ∧ (IwaAt π w → ClauseAt .dR π ι r w)

theorem not_apart_self (w : HeightOneSpectrum (𝓞 E)) : ¬ Apart w w := fun h => h rfl

end GlobalTheory.Cong

end
end
