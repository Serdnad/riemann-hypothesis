module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle009
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfTypeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep

namespace UpperTheory.NonzeroTypeTheory

namespace TranslationCoordinates

variable {K : Type} [Group K] (W : Submodule ℂ (K → ℂ))
  (hW : ∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W)

def rW : Representation ℂ K W := sub (rightReg ℂ K ℂ) W (fun k φ hφ => hW φ hφ k)

def coord {m : ℕ} (c : W ≃ₗ[ℂ] (Fin m → ℂ)) : Representation ℂ K (Fin m → ℂ) where
  toFun k := c.toLinearMap ∘ₗ rW W hW k ∘ₗ c.symm.toLinearMap
  map_one' := by ext v i; simp
  map_mul' a b := by ext v i; simp [map_mul]

end TranslationCoordinates

theorem finiteDimensionalTranslation_holds : FiniteDimensionalTranslationCoordinates := by
  intro K _ _ W hfin hW hsm
  have := hfin
  let c := (Module.finBasis ℂ W).equivFun
  let V0 := TranslationCoordinates.coord W hW c
  let e : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (K → ℂ) := W.subtype ∘ₗ c.symm.toLinearMap
  have he : ∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v) := by
    intro k v
    simp [e, V0, TranslationCoordinates.coord, TranslationCoordinates.rW, sub]
  have hinj : Function.Injective e := W.injective_subtype.comp c.symm.injective
  refine ⟨_, V0, e, hinj, ?_, he, ?_⟩
  · ext φ
    constructor
    · rintro ⟨v, rfl⟩
      simp [e]
    · intro hφ
      exact ⟨c ⟨φ, hφ⟩, by simp [e]⟩
  · intro v
    have hset : {g : K | V0 g v = v} = {g : K | rightReg ℂ K ℂ g (e v) = e v} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      rw [← he]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hsm _ (by simp [e])

end UpperTheory.NonzeroTypeTheory
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace SmoothStabiliserSubgroup

theorem rightReg_apply' {K : Type} [Group K] (k' : K) (φ : K → ℂ) (g : K) :
    rightReg ℂ K ℂ k' φ g = φ (g * k') := rfl

def stab {K : Type} [Group K] (φ : K → ℂ) : Subgroup K where
  carrier := {k' | rightReg ℂ K ℂ k' φ = φ}
  one_mem' := by
    show rightReg ℂ K ℂ 1 φ = φ
    funext g
    rw [rightReg_apply', mul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : rightReg ℂ K ℂ a φ = φ := ha
    have hb' : rightReg ℂ K ℂ b φ = φ := hb
    show rightReg ℂ K ℂ (a * b) φ = φ
    funext g
    have h1 := congrFun hb' (g * a)
    have h2 := congrFun ha' g
    rw [rightReg_apply'] at h1 h2 ⊢
    rw [← mul_assoc, h1, h2]
  inv_mem' := by
    intro a ha
    have ha' : rightReg ℂ K ℂ a φ = φ := ha
    show rightReg ℂ K ℂ a⁻¹ φ = φ
    funext g
    have h1 := congrFun ha' (g * a⁻¹)
    rw [rightReg_apply', inv_mul_cancel_right] at h1
    rw [rightReg_apply']
    exact h1.symm

end SmoothStabiliserSubgroup

theorem smoothVectorsFixed_holds : SmoothVectorsFixedByCongruence := by
  intro k _ _ _ _ n G hKC h1 φ hφ
  have hU : IsOpen ((Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev) :=
    hKC.preimage continuous_subtype_val
  have hsub : (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev ⊆
      (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n))) := by
    intro u hu
    show rightReg ℂ ↥(KO k (Fin n)) ℂ u φ = φ
    funext g
    rw [SmoothStabiliserSubgroup.rightReg_apply']
    exact hφ.2 g u hu
  have h1mem : (1 : ↥(KO k (Fin n))) ∈ (Subtype.val : ↥(KO k (Fin n)) → GL (Fin n) k) ⁻¹' KC k n G.lev := h1
  have hn : (SmoothStabiliserSubgroup.stab φ : Set ↥(KO k (Fin n))) ∈ nhds (1 : ↥(KO k (Fin n))) :=
    Filter.mem_of_superset (hU.mem_nhds h1mem) hsub
  exact (SmoothStabiliserSubgroup.stab φ).isOpen_of_mem_nhds hn

end UpperTheory.NonzeroTypeTheory
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace LocalArtinBlockProduct

theorem prod_blocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (G : Grp k n) {M : Type*} [CommMonoid M] (f : Fin G.s → M) :
    ∏ i, f (G.bl i) = ∏ b, f b ^ G.d b := by
  calc ∏ i, f (G.bl i) = ∏ p : (Σ a, Fin (G.d a)), f (G.bl (G.e p)) := (G.e.prod_comp (fun i => f (G.bl i))).symm
    _ = ∏ p : (Σ a, Fin (G.d a)), f p.1 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      show f ((G.e.symm (G.e p)).1) = f p.1
      rw [Equiv.symm_apply_apply]
    _ = ∏ b, f b ^ G.d b := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun b _ => ?_
      show ∏ _y : Fin (G.d b), f b = f b ^ G.d b
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem exists_unit (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    ∃ u, unitIncl (w.adicCompletion E) u = a (ineIncl h t) := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact valuation_eq_one_iff.mp (ord_eq_zero_iff.mp h0)

end LocalArtinBlockProduct

theorem localArtinCharacterProduct_holds : LocalArtinCharacterProduct := by
  intro E Ω _ _ _ _ _ A w h a ha n χ ho μ hμ G σ hG s
  obtain ⟨u, hu⟩ := LocalArtinBlockProduct.exists_unit ha s
  have key : ∀ i, ((χ i (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h s)) : ℂˣ) : ℂ) =
      ((G.chi (σ.symm i) (a (ineIncl h s)) : ℂˣ) : ℂ) := by
    intro i
    have e := DFunLike.congr_fun (hG (σ.symm i)) u
    simp only [MonoidHom.comp_apply, Equiv.apply_symm_apply] at e
    rw [hμ i, ← hu, e]
  simp only [xOf, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd, MonoidHom.comp_apply]
  rw [Finset.prod_congr rfl fun i _ => by rw [key i]]
  rw [Equiv.prod_comp σ.symm (fun j => X - C ((G.chi j (a (ineIncl h s)) : ℂˣ) : ℂ))]
  exact LocalArtinBlockProduct.prod_blocks G (fun b => X - C ((G.μ b (a (ineIncl h s)) : ℂˣ) : ℂ))

end UpperTheory.NonzeroTypeTheory
end
end

section

noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace TwistedSphericalEquivalence

theorem isTwSphProd_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (e : ρ.Equiv ρ')
    {s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = n} {η : Fin s → kˣ →* ℂˣ}
    (h : UpperTheory.TNZ.IsTwSphProd ρ' d hd η) : UpperTheory.TNZ.IsTwSphProd ρ d hd η := by
  obtain ⟨X, i1, i2, σ, hs, hi, hv, ⟨φ⟩⟩ := h
  exact ⟨X, i1, i2, σ, hs, hi, hv, ⟨Representation.Equiv.trans e φ⟩⟩

end TwistedSphericalEquivalence

theorem twistedSphericalRepresentative_holds : TwistedSphericalRepresentative := by
  intro k _ _ _ _ n V _ _ ρ h1 h2 s d hd η
  have e := GlobalTheory.LocGL.IrrGL.equivOf ρ h1 h2
  exact ⟨fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv e h, fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv (Representation.Equiv.symm e) h⟩

end UpperTheory.NonzeroTypeTheory
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

theorem artinTransferDecomposition_holds : ArtinTransferDecompositionCharacter := by
  unfold ArtinTransferDecompositionCharacter
  intro E Ω _ _ _ _ _ A w h a ha n χ hχ
  have hs : ∀ i, GlobalTheory.WeilDeligne.IsSmooth ((χ i).comp (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h))) := by
    intro i
    have hc : Continuous fun σ : ReciprocityTheory.Gal.Ine A =>
        Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ) :=
      continuous_subtype_val.subtype_mk _
    exact (hχ i).preimage hc
  choose μ hμ hμe using fun i => ha.factor _ (hs i)
  exact ⟨μ, hμ, fun i σ => DFunLike.congr_fun (hμe i) σ⟩

end UpperTheory.NonzeroTypeTheory
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

theorem typeData_of (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct) (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia)
    (a7 : SmoothVectorsFixedByCongruence) (gm : GMain) (ge : GEmb) (gi : ArtinInertiaProp) (cm : GlobalTheory.Mem.LiteralAutomorphy.LitN → Need_CMain) (cp : Need_CProps) (gr : Need_Grp) :
    TypeData := by
  intro E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  obtain ⟨μ, hμs, hμ⟩ := a1 E Ω A w h a ha n χ ho
  obtain ⟨G, σ, hG⟩ := gr (w.adicCompletion E) n μ hμs
  have hcond : ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π ↔ IsTwSphProd π.ρ G.d G.hd G.μ := by
    intro π
    have e := gm E Ω A w h a ha ε rc H P.loc G.s G.d G.μ G.smooth (a6 gi E Ω A w h a ha n G)
      (IrrGL.of π.ρ π.smooth π.irred) G.hd
    rw [← a5 _ n π.V π.ρ π.smooth π.irred G.s G.d G.hd G.μ, ← e]
    unfold Cond
    refine and_congr_right fun _ => forall_congr' fun s => ?_
    rw [a3 E Ω A w h a ha n χ ho μ hμ G σ hG s]
  obtain ⟨hJK, h1J, hmul, hinv, hne, hKCo, h1KC, hKCJ, hlam1, hst, hfin, hv0m, hv00, hv0e⟩ := cp (w.adicCompletion E) n G
  have hK : KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := SphCompletion.KO_completion w n
  let T (K : Subgroup (GL (Fin n) (w.adicCompletion E))) : Prop :=
    ∃ (J : Subgroup ↥K) (lam : ↥J →* ℂˣ) (m : ℕ) (V0 : Representation ℂ ↥K (Fin m → ℂ))
        (v0 : Fin m → ℂ), IsOpen (J : Set ↥K) ∧ IsOpen (lam.ker : Set ↥J) ∧ GlobalTheory.PRep.IsSmooth V0 ∧
        v0 ≠ 0 ∧ (∀ j : ↥J, V0 (j : ↥K) v0 = ((lam j : ℂˣ) : ℂ) • v0) ∧
        (∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)),
          (∃ x : π.V, x ≠ 0 ∧ ∀ j : ↥J, π.ρ ((j : ↥K) : GL (Fin n) (w.adicCompletion E)) x = ((lam j : ℂˣ) : ℂ) • x) →
            Cond h rc χ ho π) ∧
        ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π →
          ∃ f : (Fin m → ℂ) →ₗ[ℂ] π.V, Function.Injective f ∧ ∀ k v, f (V0 k v) = π.ρ k (f v)
  change T _
  rw [← hK]
  dsimp only [T]
  let J : Subgroup ↥(KO (w.adicCompletion E) (Fin n)) :=
    { carrier := {j | (j : GL (Fin n) (w.adicCompletion E)) ∈ G.JSet}
      mul_mem' := fun {x y} hx hy => (hmul _ hx _ hy).1
      one_mem' := h1J
      inv_mem' := fun {x} hx => hinv _ hx }
  let lam : ↥J →* ℂˣ :=
    { toFun := fun j => Units.mk0 (G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E))) (hne _ j.2)
      map_one' := Units.ext (by simpa using hlam1 1 h1KC)
      map_mul' := fun x y => Units.ext (by simpa using (hmul _ x.2 _ y.2).2) }
  have hlamv : ∀ j : ↥J, ((lam j : ℂˣ) : ℂ) = G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E)) :=
    fun _ => rfl
  obtain ⟨m, V0, e, he, hre, heq, hsm⟩ := a4 _ G.V0sp hfin (fun φ hφ k' => hst φ hφ k') (a7 _ n G hKCo h1KC)
  obtain ⟨v0, hv0⟩ : G.v0 ∈ LinearMap.range e := hre ▸ hv0m
  have hU : IsOpen {j : ↥(KO (w.adicCompletion E) (Fin n)) | (j : GL (Fin n) (w.adicCompletion E)) ∈ KC _ n G.lev} :=
    hKCo.preimage continuous_subtype_val
  refine ⟨J, lam, m, V0, v0, ?_, ?_, hsm, fun h0 => hv00 (by rw [← hv0, h0, map_zero]), fun j => he ?_, ?_, ?_⟩
  · exact Subgroup.isOpen_of_mem_nhds J (Filter.mem_of_superset (hU.mem_nhds (show (1 : ↥(KO (w.adicCompletion E) (Fin n))) ∈ _ from h1KC)) fun j hj => hKCJ hj)
  · exact Subgroup.isOpen_of_mem_nhds lam.ker (Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds (show (1 : ↥J) ∈ _ from h1KC)) fun j hj => MonoidHom.mem_ker.2 (Units.ext (by
        rw [hlamv]; exact hlam1 _ hj)))
  · rw [heq, hv0, hv0e _ j.2, map_smul, hv0, hlamv]
  · rintro π ⟨x, hx, hxj⟩
    rw [hcond]
    refine cm P _ n G π.V π.ρ π.smooth π.irred ⟨x, hx, fun g hg => ?_⟩
    have := hxj ⟨⟨g, hJK hg⟩, hg⟩
    rwa [hlamv] at this
  · intro π hc
    rw [hcond] at hc
    obtain ⟨f, hf, hfeq⟩ := ge _ n G π.V π.ρ hc
    let e' : (Fin m → ℂ) →ₗ[ℂ] ↥G.V0sp := LinearMap.codRestrict G.V0sp e fun v => hre ▸ LinearMap.mem_range_self e v
    refine ⟨f ∘ₗ e', hf.comp fun v v' hvv => he (congrArg Subtype.val hvv), fun κ v => ?_⟩
    exact hfeq κ (e' v) (e' (V0 κ v)) (heq κ v)

theorem nz_of_steps (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) (k2 : SmoothRepIrreducibleSubcontainingVector) (k3 : SmoothRepMinimalSubrepresentation) (k4 : SchurInjectiveFromIrreducible) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct)
    (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia) (a7 : SmoothVectorsFixedByCongruence) (gm : GMain) (ge : GEmb) (gi : ArtinInertiaProp)
    (cm : GlobalTheory.Mem.LiteralAutomorphy.LitN → Need_CMain) (cp : Need_CProps) (gr : Need_Grp) : NZ :=
  nz_of_typeData k2 k3 k4 (typeData_of P a1 a3 a4 a5 a6 a7 gm ge gi cm cp gr)

end UpperTheory.NonzeroTypeTheory
end
end
