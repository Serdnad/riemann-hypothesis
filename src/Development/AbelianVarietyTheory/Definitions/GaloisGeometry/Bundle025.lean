module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle053
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SeedWU4 (Rk : ℕ → Prop) (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → Rk a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ → ∀ (U : Submodule ℂ (UA E a → ℂ)) (S Y : Finset (HeightOneSpectrum (𝓞 E))),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → Ty E l a w₀ U' → Wt E l a ι w₀ v' U U' → SphOffU w₀ S U' →
        (∃ B, SatU U' v' B) → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∃ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∃ (V : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
          ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
            ∀ B, SatU U' w B → ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
              (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : _root_.Formalism.ConjugateSelfDual.G E Ω, IsFrob A (normV w) s → s ∈ V →
                ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
                  ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
        (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
          ∀ B, SatU U' w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → CrysDRU U' ι r w) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → ∀ B, SatU U' w B → Gen a (normV w) B → PhiAt ι r w B)

def CongUW4 (Rk : ℕ → Prop) (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → Rk a →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ Kw : Levels E a, HasLevelOff w₀ v' Kw U ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w (n := a)) ∧
      ∀ (Z W : Finset (HeightOneSpectrum (𝓞 E))),
        (∀ z ∈ Z, IsSplitAt z ∧ Apart z w₀ ∧ Apart z v' ∧ ∃ B, SatU U z B) →
        (∀ w ∈ W, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B) →
      ∃ c : HeightOneSpectrum (𝓞 E) → ℤ → ℂ, (∀ w n, c w n ≠ 0) ∧
      ∀ (J : Type) (O : LocOps l ι Kw J) (θ : J → Qbar l), IsSysU O U θ →
        PolyApprox (Sum.elim θ (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U p.1 p.2)))
          {ϑ | ∃ U' θ', AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ (∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧
            Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Z, GenAtU Gen U' z) ∧ (∀ w ∈ W, GenAtU Gen U' w) ∧ IsSysU O U' θ' ∧
            ϑ = Sum.elim θ' (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U' p.1 p.2))} ∧
        ((∀ j g, ∃ q : ℚ, O.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

def LimWU4 (Rk : ℕ → Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → Rk a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → CrysDRU U ι r w) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ∀ B, SatU U w B →
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O)
          (hBw : Pst.Induces Bw) (σ : Weil hA),
        ∃ (C : Set (_root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l))) (J : (E →+* Qbar l) → Multiset ℤ),
          (∀ ρ ∈ C, Continuous ρ ∧ IsCrysAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
            ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
              IsJumpsAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ (J τ)) ∧
          GlobalTheory.CongPhi.JointApprox r C (fun n => ι.symm (GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n))
            (fun ρ n => ι.symm (GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) σ n)))

def SeedFinOdd : Prop := SeedWU4 Odd GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def CongFinOdd : Prop := CongUW4 Odd GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def LimFinOdd : Prop := LimWU4 Odd

end GlobalTheory.CongL

end
end

section

noncomputable section

namespace GlobalTheory.Pdv

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host NumberField IsDedekindDomain

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def At (ex : Extra D L hT Gi Gl K Y cX) (E : KerEnt D Y ex.tw) : Prop :=
  (E.UnUnit ∧ OrbitPlaces.KmapRat E ∧ OrbitPlaces.KFi D ex.tw ∧ OrbitPlaces.Stab0 D) ∧
    ∃ (ep : _) (be : _) (sg : _),
      OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Gi K ∧ OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.Shape D L Gi (OrbitPlaces.ofKer (nuRowOK D) E ep be sg)

variable {ex : Extra D L hT Gi Gl K Y cX}

def IsEntC (t : KerEntTied ex) : Prop :=
  ∃ (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (h : KerEntHyp P t.O B Y ex.tw), t.ent = kerEntC P t.O B h

structure Duty (t : KerEntTied ex) : Prop where
  col : GlobalTheory.KerJ.ColSide t
  entC : IsEntC t
  rk : t.RK
  forms : ∃ t' : KerEntTied ex, GlobalTheory.KerJ.ColSide t' ∧ GlobalTheory.KerJ.FormsPin t'

end GlobalTheory.Pdv

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.RoadW GlobalTheory.CongL Polynomial

namespace GlobalTheory.RoadWGeo

def Lacunary (J : Finset ℤ) : Prop :=
  ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → Disjoint A B → A.Nonempty → B.Nonempty →
    (B.card : ℤ) * A.sum id ≠ (A.card : ℤ) * B.sum id

theorem lacunary_of_growth {J : Finset ℤ} (hpos : ∀ x ∈ J, 0 < x) (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * x < y) :
    Lacunary J := by
  classical
  have key : ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → B.Nonempty → ∀ m ∈ A, (∀ b ∈ B, b < m) →
      (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
    intro A B hA hB hBn m hm hlt
    have h1 : m ≤ A.sum id := Finset.single_le_sum (f := id) (fun x hx => (hpos x (hA hx)).le) hm
    have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
    have h2 : ∑ b ∈ B, (A.card : ℤ) * b < ∑ _b ∈ B, m := by
      refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
      have := hg b (hB hb) m (hA hm) (hlt b hb)
      have := mul_le_mul_of_nonneg_right hc (hpos b (hB hb)).le
      linarith
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (B.card : ℤ) * m ≤ B.card * A.sum id := mul_le_mul_of_nonneg_left h1 (by positivity)
    exact lt_of_lt_of_le h2 h3
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (key A B hA hB hBn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (key B A hB hA hAn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

theorem not_lacunary_three (k : ℤ) : ¬ Lacunary ({k, k + 1, k + 2} : Finset ℤ) := by
  intro h
  have h02 : k ≠ k + 2 := by omega
  refine h {k, k + 2} {k + 1} ?_ ?_ ?_ (by simp) (by simp) ?_
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · simp only [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton]; omega
  · rw [Finset.sum_pair h02, Finset.card_pair h02]; simp; ring

def wtJumps {a : ℕ} (lam : DomWeight a) : Finset ℤ :=
  Finset.univ.image fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k

theorem strictMono_jump {a : ℕ} (lam : DomWeight a) : StrictMono fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k := by
  intro i j hij
  have h1 := lam.anti hij.le
  have h2 : (i : ℕ) < j := hij
  simp only
  omega

theorem card_wtJumps {a : ℕ} (lam : DomWeight a) : (wtJumps lam).card = a := by
  rw [wtJumps, Finset.card_image_of_injective _ (strictMono_jump lam).injective]; simp

theorem wtJumps_val {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).val.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [wtJumps, Finset.image_val_of_injOn (strictMono_jump lam).injective.injOn, infOfWeight, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp]
  push_cast
  ring

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]

def ESAt {d : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin d) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂ) :
    Prop :=
  ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ρ s = 1) ∧
    ∀ σ : _root_.Formalism.ConjugateSelfDual.G E Ω, IsFrob A (normV w) σ →
      aeval (ρ σ⁻¹ : Matrix (Fin d) (Fin d) (Qbar l)) (((B.map fun b => X - C b).prod).map ι.symm.toRingHom) = 0

def LacWtAt {a : ℕ} (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ τ : E →+* ℂ, OverPl ι τ v' ∧ ∃ lam : DomWeight a, HasWeightAt U τ lam ∧ Lacunary (wtJumps lam)

end GlobalTheory.RoadWGeo

namespace GlobalTheory.Published

open GlobalTheory.RoadWGeo

end GlobalTheory.Published

end
end

section

noncomputable section

namespace GlobalTheory.TwV.Model

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {w : Pr.Word}


open Classical in
theorem frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, h⟩)).1 x
  · exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

private theorem mem_stdAt_iff_forall_intAt {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (w : Sp X.E n) :
    w ∈ stdAt X.E n P ↔ ∀ l, IntAt P (w l) := by
  show (∃ s ∈ P.asIdeal.primeCompl, s • w ∈ _) ↔ _
  constructor
  · rintro ⟨s, hs, hsw⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hsw l (Set.mem_univ l))
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  · intro h
    choose r s hs e using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ fun l _ => hs l, fun l _ => ?_⟩
    change ((∏ l, s l) • w) l ∈ (1 : Submodule (𝓞 X.E) X.E)
    rw [Submodule.mem_one]
    refine ⟨r l * ∏ k ∈ Finset.univ.erase l, s k, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l)]
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, map_prod]
    rw [← e l]
    ring


open Classical in
theorem sameCoset_iff {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (z y : Sp X.E (R.N j)) :
    SameCoset sel mu cst P ((frsF sel mu p P).symm z) ((frsF sel mu p P).symm y) ↔
      (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y)) ∈ p.deco.1.at P.1 := by
  have hc : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ =
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ := by
    split_ifs <;> simp
  have e : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y) =
      frsF sel mu p P (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ •
        ((frsF sel mu p P).symm z - (frsF sel mu p P).symm y)) := by
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, frsF_mem, mem_stdAt_iff_forall_intAt]
  unfold SameCoset
  simp only [hc, Pi.smul_apply, smul_eq_mul]

theorem sameCoset_trans {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n} (h : SameCoset sel mu cst P x y) (h' : SameCoset sel mu cst P y z) :
    SameCoset sel mu cst P x z := by
  intro l
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := h l
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := h' l
  refine ⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, fun hm => (P.1.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  simp only [Pi.sub_apply] at e₁ e₂ ⊢
  rw [map_add (f := _), map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem sameCoset_symm {n : ℕ} {P : rowSG Pr sel mu} {x y : Sp X.E n} (h : SameCoset sel mu cst P x y) :
    SameCoset sel mu cst P y x := by
  intro l
  obtain ⟨r, s, hs, e⟩ := h l
  refine ⟨-r, s, hs, ?_⟩
  simp only [Pi.sub_apply] at e ⊢
  rw [map_neg, ← e]
  ring

end Gen

end GlobalTheory.TwV.Model

end
end

section

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

abbrev UA (D : D7) (i : ℕ) (hi : i ≤ D.R.m) := UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def iotaOf (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal :=
  Classical.epsilon fun ι => ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1

structure IsPtAd (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) : Prop where
  lat : t.seam.lat p.deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb
  frame : ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
    (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) p P))
  fnl : ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
    IsOver v (seamP t.seam P.1) →
      FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x.1) p.deco.1

def y0At (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : SB t μ) : Sp t.X.E (D.R.N i) :=
  if h : i = t.m2 + 1 then (by subst h; exact A.y0 β P) else 0

def cosetOf (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) : Set (Sp t.X.E (D.R.N i)) :=
  {y | ∀ P : SB t μ, SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm y) (y0At A i hi β P)}

def xiPt (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1))
    (z : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) : t.X.K :=
  if h : i < t.m2 then
    XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) (by have := m_eq t μ; omega) β') p p' z
  else if i = t.m2 then XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) p p' (cosetOf A (i + 1) hi β' p') z
  else XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p (cosetOf A i (Nat.le_of_succ_le hi) β p) p' z


open Classical in
def xiAd : AdDatum St := fun i hi β β' x x' z =>
  if h : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' then
    t.seam.σ₀ (xiPt A i hi β β' h.1.choose h.2.choose (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z)))
  else 0


variable (t u μ) in
open Classical in
def muOf (j : ℕ) (x : (AfE D.host.F D.host.E)ˣ) : ℂ :=
  if h : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x then (((t.O u μ).mt j (dtU h.choose) : ℂˣ) : ℂ) else 0

def PtEx : Prop := ∀ i hi β x, ∃ p, IsPtAd A a i hi β x p

def PtAway (i : ℕ) (hi : i + 1 ≤ D.R.m) : Prop :=
  ∀ β β' x x' x₁ x₁' p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧
      bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1) → xiPt A i hi β β' p₁ p₁' = xiPt A i hi β β' p p'

def LevAt (i : ℕ) (hi : i + 1 ≤ D.R.m) : Prop :=
  ∀ β β' x x' x₁ x₁' (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 → ∀ z,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i _).K β).lev.chi κ : ℂˣ) : ℂ) * xiAd A a i hi β β' x₁ x₁' z =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * xiAd A a i hi β β' x x' z

def RatLaw : Prop :=
  ∀ i hi β β' x x' x₁ x₁', ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)),
    ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), x₁.1 = ratA D.host.F γ * x.1 → x₁'.1 = ratA D.host.F γ' * x'.1 →
    ∀ z, xiAd A a i hi β β' x₁ x₁' z = xiAd A a i hi β β' x x' (inFr
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)

def SizeLaw : Prop :=
  ∀ i hi β β' x x', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev
      (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
      (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb) (xiAd A a i hi β β' x x') ∧
    ∀ z, xiAd A a i hi β β' x x' z ≠ 0 → z ∈ divLat (t.rd u μ).lev (homAt (ssRec t u μ)
      (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
      (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb))


variable (t u μ) in
def MuLaw : Prop :=
  ∀ i (hi : i < D.R.m),
    (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ)) ∧
    (muOf t u μ dtU (i + 1) 1 = 1 ∧ ∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D),
      muOf t u μ dtU (i + 1) (x * y) = muOf t u μ dtU (i + 1) x * muOf t u μ dtU (i + 1) y) ∧
    (∀ x ∈ U1 (sigD D), muOf t u μ dtU (i + 1) x ∈ TaylorLogMetric.Qbar) ∧
    (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E →
      (∀ v, UnderSB t μ v → prV (E := D.host.E) v (x : AfE D.host.F D.host.E) = 1) → muOf t u μ dtU (i + 1) x = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧
      ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 →
        muOf t u μ dtU (i + 1) (ratId D.host.F D.host.E z) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

end GlobalTheory.TwV

def GlobalTheory.TwV.UnderTie (Q : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX}
    {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : GlobalTheory.TwU.ChainCharts D u μ}, GlobalTheory.TwU.AdData t u μ St →
    ((letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) → NumberField.RingOfIntegers D.host.E → Prop) : Prop :=
  ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX}
    {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : GlobalTheory.TwU.ChainCharts D u μ} (A : GlobalTheory.TwU.AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : NumberField.RingOfIntegers D.host.E),
    GlobalTheory.TwU.AdPins A dtU → GlobalTheory.TwU.AdTie A dtU a → Q A dtU a

end
end
