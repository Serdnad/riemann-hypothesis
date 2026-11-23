module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle202
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle203
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle173
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle140
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.isAdmissible_of_complete_DVR_charZero (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : LN.CDvr V) :
    LN.admitted V (IsLocalRing.maximalIdeal V) := by
  have := hV.1
  have := hV.2.1
  refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hV.2.1, hV.2.2, inferInstance, ?_⟩
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  infer_instance

theorem LN.uDvrSt_holds : GlobalTheory.LN.UDvrSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  intro E _ _ _ H V _ _ _ hV t hp hs
  have := hV.1
  exact GlobalTheory.T.exists_uniformisation_complete_local_normal_prime L L2 L3 L4 L5 LN.ega_holds GlobalTheory.T.uniformisation_completeDVR GlobalTheory.T.linearUniformisation_triples_torsion E H V _ (LN.isAdmissible_of_complete_DVR_charZero V hV)
    (by letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V); infer_instance) t hp hs
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt L L2 E H V t hp)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSplit

theorem exists_affine_isDomain {Z : Scheme.{0}} [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (p : Z) :
    ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ IsDomain Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hC⟩) (x := p) mem_irreducibleComponent
  exact ⟨W, hW, hpW, (GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => hle hq⟩).1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (f : S' ⟶ S) (o : Ob D l s) :
    ∃ o' : Ob D l (f ≫ s), Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (f ≫ s) f rfl rfl
    (by rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id]) o

theorem hasQuot_image (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S] [IsNoetherian S']
    (s : S ⟶ Sp (KA l)) (g : S' ⟶ S) [Etale g] (o : Ob D l s) (s' : S' ⟶ Sp (KA l)) (hs : s' = g ≫ s)
    (o' : Ob D l s') (m : ObjMap o' o g) (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K)
    (hQ : HasQuot o' p (m.toSABMap.φ ⁻¹' K)) (q : S) (hq : q ∈ Set.range g) :
    ∃ (U : S.Opens) (o₁ : Ob D l (U.ι ≫ s)) (m₁ : ObjMap o₁ o U.ι), q ∈ U ∧ HasQuot o₁ p (m₁.toSABMap.φ ⁻¹' K) := by
  let U : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  obtain ⟨g', hg'⟩ : ∃ g' : S' ⟶ U.toScheme, g' ≫ U.ι = g :=
    ⟨IsOpenImmersion.lift U.ι g (by simp [U]), IsOpenImmersion.lift_fac _ _ _⟩
  have hU : ∀ x : S, x ∈ U → x ∈ Set.range g := fun _ h => h
  have hqU : q ∈ U := hq
  clear_value U
  subst hg'
  rw [Category.assoc] at hs
  subst hs
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull s U.ι o
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 U.ι g' m₁).2 m
  have he : Etale g' := Etale.of_comp g' U.ι
  have hsur : Surjective g' := ⟨fun y => by
    obtain ⟨x, hx⟩ := hU (U.ι y) y.2
    exact ⟨x, U.ι.isOpenEmbedding.injective (by simpa using hx)⟩⟩
  refine ⟨U, o₁, m₁, hqU, GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo 𝔓 p i _ _ _ g' o₁ o' m' _ hA
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK) he hsur inferInstance ?_⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hQ
  exact hQ

end GlobalTheory.HkSplit

theorem GlobalTheory.hasQuot_of_lists_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i n S s o σ K hD hA hs hL hK
  obtain ⟨hr, hN, hn⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ S s hs
  refine GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base E H D l Xo 𝔓 p i S s o K hA hK fun q => ?_
  obtain ⟨W, hW, hq, hd⟩ := GlobalTheory.HkSplit.exists_affine_isDomain hN q
  have hR : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hj : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨x, hx⟩ : q ∈ Set.range j := by
    rw [show Set.range j = W from hW.range_fromSpec]; exact hq
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.HkSplit.exists_pull s j o
  obtain ⟨σ', -, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m₁.toSABMap.cart K _ n σ hL
  obtain ⟨R', _, π, o', m, he, ⟨y, hy⟩, hQ⟩ := GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain E H D l 𝔓 p i n Γ(S, W) (j ≫ s) o₁ σ' _ x hD hA hL'
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK)
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 j π m₁).1 m
  have : IsLocallyNoetherian (Sp R') := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian (Sp R') := {}
  refine GlobalTheory.HkSplit.hasQuot_image Xo 𝔓 p i s (π ≫ j) o _ (Category.assoc _ _ _).symm o' m' K hA hK ?_ q
    ⟨y, by rw [Scheme.Hom.comp_apply, hy, hx]⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exact hQ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ThetaFamily

theorem exists_coord_of_isLocalRing {X : Scheme.{0}} {M : LB X} {σ : Type} (th : σ → M.Sec) (hM : M.IsLB)
    {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) : ∃ v, SecCoord M th x v := by
  obtain ⟨k, hk⟩ : ∃ k, x (IsLocalRing.closedPoint R) ∈ M.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge trivial)
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  exact ((IsLocalRing.specializes_closedPoint y).map x.continuous).mem_open (M.U k).isOpen hk

theorem nonempty_thetaFam : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  intro h₁ h₂ hcrit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, hglue⟩ := GlobalTheory.T.exists_thetaFamily_over_thetaPointScheme h₁ h₂ hcrit g J Mat κ n w w' hn hodd
  obtain ⟨j₂, hrep⟩ := GlobalTheory.T.thetaIdealFamily_universal_property h₁ h₂ g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d hb hC => ?_⟩
  have := hb.1
  obtain ⟨i₁, i₂, i₃⟩ := GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous o g (n ^ j) J b em C hb.2.2
  obtain ⟨Y⟩ := GlobalTheory.ZM.nonempty_MMPre o g n (n ^ j) (thIdeal em C) (pow_pos hn.pos j) i₁ i₂ i₃
  obtain ⟨t, hd, -, hth, hfib⟩ := hglue j (le_of_max_le_left hj) o b em C d hb hC Y
  refine ⟨{ MM := Y.MM
            s := Y.s
            qproj := Y.qproj
            flat := Y.flat
            reduced := Y.reduced
            univ := t
            dense := hd
            loc := fun R _ _ β x hx => ?_
            pts := fun R _ β v hv => ?_
            rep := hrep j (le_of_max_le_right hj) o b em C d hb hC Y t hth hfib
            unram := GlobalTheory.T.tangentVector_zero_of_object_constant_along h₁ h₂ o g n (n ^ j) J b _ Y t hodd.pow hth }⟩
  · obtain ⟨v, hv⟩ := exists_coord_of_isLocalRing Y.th Y.isLB x
    exact ⟨v, (hth R x v).2 hv, Y.loc R β x v hx hv⟩
  · simpa only [hth] using Y.pts R β v hv

end GlobalTheory.ZM.ThetaFamily
end
end
