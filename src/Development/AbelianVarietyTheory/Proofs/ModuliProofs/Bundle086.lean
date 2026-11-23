module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ObjDesc

open GlobalTheory.ObjPull

theorem exists_geomPt_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [LocallyOfFiniteType π] [Surjective π]
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) : ∃ y : Sp k ⟶ X, y ≫ π = x := by

  have hJ := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (IsLocalRing.closedPoint k)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Set.nonempty_of_mem (Set.mem_univ p))
    isOpen_univ.isLocallyClosed
  have hc' : IsClosed {c} := hc
  have hpt := pointOfClosedPoint_comp (pullback.snd π x) c hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc' ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hpt, Category.id_comp]

section Sections

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem secPull_injective [Epi f] (h : IsGrpPullback G' G f φ) : Function.Injective (secPull h) := by
  intro e₁ e₂ he
  have key : f ≫ e₁.left = f ≫ e₂.left := by
    rw [← secPull_left h e₁, ← secPull_left h e₂, he]
  exact Over.OverMorphism.ext ((cancel_epi f).1 key)

theorem secPull_eq (h : IsGrpPullback G' G f φ) {e : 𝟙_ (Over S) ⟶ G} {e' : 𝟙_ (Over S') ⟶ G'}
    (he : e'.left ≫ φ = f ≫ e.left) : secPull h e = e' := by

  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
  · rw [secPull_left, he]
  · exact (Over.w _).trans (Over.w e').symm

theorem exists_sec [Epi f] (h : IsGrpPullback G' G f φ) (e' : 𝟙_ (Over S') ⟶ G') (g : S ⟶ G.left)
    (hg : f ≫ g = e'.left ≫ φ) : ∃ e : 𝟙_ (Over S) ⟶ G, e'.left ≫ φ = f ≫ e.left := by

  have hsec : g ≫ G.hom = (𝟙_ (Over S)).hom := by
    apply (cancel_epi f).1
    rw [← Category.assoc, hg, Category.assoc, h.1.w, ← Category.assoc, Over.w e']
    simp
  exact ⟨Over.homMk g hsec, hg.symm⟩

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'} {X Y : Scheme.{0}}
  {s : Y ⟶ Sp B} {s' : X ⟶ Sp B'} {π : X ⟶ Y}

def descend [Epi π] [LocallyOfFiniteType π] [Surjective π] (j : B →+* B') (hρ : j b.ρ = b'.ρ) (hζ : j b.ζ = b'.ζ)
    (hs : π ≫ s = s' ≫ spMap j) (o : Obj D l b' s') (t : SAB H Y) (m : SABMap o.t t π)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (e eA : D.La → (𝟙_ (Over Y) ⟶ t.G)) (he : ∀ a, secPull m.cart (e a) = o.eta a)
    (heA : ∀ a, secPull m.cart (eA a) = o.etaA a) : Obj D l b s where
  t := t
  proper := hp
  ample := ha
  ktriv := hk
  eta := e
  eta_add a c := secPull_injective m.cart (by rw [map_mul, he, he, he, o.eta_add])
  eta_ker a h := secPull_injective m.cart (by rw [map_one, he, o.eta_ker a h])
  etaA := eA
  etaA_add a c := secPull_injective m.cart (by rw [map_mul, heA, heA, heA, o.etaA_add])
  etaA_ker a := secPull_injective m.cart (by rw [map_one, heA, o.etaA_ker a])
  geom k _ _ x β hx := by
    obtain ⟨y, rfl⟩ := exists_geomPt_lift π k x
    obtain ⟨β', hβ'⟩ : ∃ β' : B' →+* k, y ≫ s' = spMap β' :=
      ⟨(Spec.preimage (y ≫ s')).hom, (Spec.map_preimage _).symm⟩
    obtain rfl : β = β'.comp j := by
      have : spMap β = spMap (β'.comp j) := by
        rw [← hx, Category.assoc, hs, ← Category.assoc, hβ', spMap_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have hL : LBIso o.t.PP.L (t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k y β' hβ'
    rw [RingHom.comp_apply, RingHom.comp_apply, hρ, hζ]
    refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk y)).symm (fun c g => ?_) (fun n g g' c hc => ?_) I,
      hI, fun a => ?_, fun a ha => ?_⟩
    · rw [← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ,
        ← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ]
      exact hdet τ
    · obtain ⟨g, rfl⟩ := (pushEquiv m.cart (Over.mk y)).surjective g
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
      rw [Category.assoc, ← m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X t.G o.t.G π m.cm.F t.PP.L o.t.PP.L t.PP.isLB o.t.PP.isLB m.cart hL
        (Over.mk y) n _ _ g g' _ (pushEquiv_symm_left m.cart (Over.mk y) g).symm
        (pushEquiv_symm_left m.cart (Over.mk y) g').symm).1 hc
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [heA, hA]
      rfl
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [he, hM a ha]
      rfl

def lowerBase {l₂ : Level H} (h : l.Dvd l₂) (b₂ : Base l₂ B') : Base l B' where
  unit := b₂.unit
  ρ := b₂.ρ
  ρ_sq := b₂.ρ_sq
  ζ := b₂.ζ ^ (l₂.A / l.A)
  ζ_prim := b₂.ζ_prim.pow l₂.A_pos (Nat.div_mul_cancel h.2.2).symm

end GlobalTheory.ObjDesc

theorem GlobalTheory.obj_descend_lower_level : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B B₂ : Type) [CommRing B] [CommRing B₂] (b : Base l B) (b₂ : Base l₂ B₂) (j : B →+* B₂) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp B) (s₂ : X ⟶ Sp B₂) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ob₂ : Obj D l₂ b₂ s₂) (ν : Ga → (ob₂.t.G.left ⟶ ob₂.t.G.left)) (t' : SAB H Y) (m : SABMap ob₂.t t' π), l.Dvd l₂ → j b.ρ = b₂.ρ → j b.ζ = b₂.ζ ^ (l₂.A / l.A) → π ≫ s = s₂ ≫ spMap j → IsGaloisCover Ga ρ π → (∀ a, ν a ≫ m.φ = m.φ) → (∀ a, Lowers l ob₂ (fun x => ob₂.eta x ^ (l₂.M / l.M)) (fun x => ob₂.etaA x ^ (l₂.A / l.A)) (ρ a) (ν a)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∃ (ob : Obj D l b s) (m' : SABMap ob₂.t ob.t π), (∀ a, (ob₂.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = π ≫ (ob.eta a).left) ∧ ∀ a, (ob₂.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = π ≫ (ob.etaA a).left := by
  intro _ _ E _ _ _ H D l l₂ B B₂ _ _ b b₂ j X Y π s s₂ Ga _ ρ ob₂ ν t' m hdvd hρ hζ hs hG hν hlow hp ha hk

  have : Epi π := ⟨fun g₁ g₂ hg => (hG.existsUnique_desc (π ≫ g₁)
    (fun a => by rw [← Category.assoc, hG.inv])).unique rfl hg.symm⟩
  have : IsFinite π := hG.fin
  have : Surjective π := hG.onto

  let o := GlobalTheory.ObjLower.lower (b := GlobalTheory.ObjDesc.lowerBase hdvd b₂) ob₂ hdvd rfl rfl

  have desc : ∀ u : D.La → (𝟙_ (Over X) ⟶ ob₂.t.G), (∀ c a, ρ c ≫ (u a).left = (u a).left ≫ ν c) →
      ∃ w : D.La → (𝟙_ (Over Y) ⟶ t'.G), ∀ a, (u a).left ≫ m.φ = π ≫ (w a).left := by
    intro u hu
    have hex : ∀ a, ∃ w : 𝟙_ (Over Y) ⟶ t'.G, (u a).left ≫ m.φ = π ≫ w.left := by
      intro a
      obtain ⟨g, hg, -⟩ := hG.existsUnique_desc ((u a).left ≫ m.φ)
        (fun c => by rw [← Category.assoc, hu c a, Category.assoc, hν c])
      exact GlobalTheory.ObjDesc.exists_sec m.cart (u a) g hg
    exact ⟨fun a => (hex a).choose, fun a => (hex a).choose_spec⟩
  obtain ⟨e, he⟩ := desc (fun a => ob₂.eta a ^ (l₂.M / l.M)) (fun c a => ((hlow c).1 a).symm)
  obtain ⟨eA, heA⟩ := desc (fun a => ob₂.etaA a ^ (l₂.A / l.A)) (fun c a => ((hlow c).2 a).symm)
  exact ⟨GlobalTheory.ObjDesc.descend (b' := GlobalTheory.ObjDesc.lowerBase hdvd b₂) j hρ hζ hs o t' m hp ha hk e eA
    (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (he a)) (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (heA a)),
    m, he, heA⟩

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.WeilLocal

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private theorem gm_comp_global_eq_gm_units_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (c : Γ(X, ⊤)ˣ) :
    gm (f ≫ g) z ⊤ c = gm f z ⊤ (Units.map g.appTop.hom.toMonoidHom c) := by
  unfold gm pullU
  rw [dite_eq_left (show (f ≫ g) z ∈ (⊤ : X.Opens) from trivial), dite_eq_left (show f z ∈ (⊤ : Y.Opens) from trivial)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem commIsOf_of_retract (hL : L.IsLB) {T T' : Over S} (g : T' ⟶ T) (h : T ⟶ T') (w : g ≫ h = 𝟙 T')
    {c : Γ(T.left, ⊤)ˣ} (θx' θy' : ThetaGrp A L k T')
    (H : ∀ θx θy : ThetaGrp A L k T, θx.pt = h ≫ θx'.pt → θy.pt = h ≫ θy'.pt → CommIsOf A L k θx θy c) :
    CommIsOf A L k θx' θy' (Units.map g.left.appTop.hom.toMonoidHom c) := by
  obtain ⟨θx, hx, hxv⟩ := exists_pull hL h θx'
  obtain ⟨θy, hy, hyv⟩ := exists_pull hL h θy'
  have Hc := (commIsOf_iff hL θx θy c).1 (H θx θy hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  have e := Hc Z (r ≫ (g ▷ A).left) z J hJ
  have e1 : r ≫ (g ▷ A).left ≫ (h ▷ A).left = r := by
    rw [← Over.comp_left, ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.comp_id]
  have e2 : ∀ x : T' ⟶ A, r ≫ (g ▷ A).left ≫ (translT A (h ≫ x)).left ≫ (h ▷ A).left = r ≫ (translT A x).left := by
    intro x
    rw [← Over.comp_left _ _ _ (translT A (h ≫ x)), whisker_translT, Over.comp_left, ← Category.assoc (g ▷ A).left,
      ← Over.comp_left _ _ _ (g ▷ A), ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.id_comp]
  have e3 : r ≫ (g ▷ A).left ≫ (fst T A).left = (r ≫ (fst T' A).left) ≫ g.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left, Category.assoc]
  rw [hxv _ _ _ _ hJ, hxv _ _ _ _ hJ, hyv _ _ _ _ hJ, hyv _ _ _ _ hJ, hx, hy] at e
  simp only [Category.assoc] at e
  rw [e1, e2, e2, e3, gm_comp_global_eq_gm_units_map] at e
  exact e

private theorem exists_overRes_section_image_openImmersion {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    (V' : T'.left.Opens) :
    ∃ (a : overRes V' ⟶ overRes (j.left ''ᵁ V')) (b : overRes (j.left ''ᵁ V') ⟶ overRes V'),
      b ≫ a = 𝟙 _ ∧ a ≫ overResι (j.left ''ᵁ V') = overResι V' ≫ j := by
  have he : (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left := Scheme.Hom.isoImage_hom_ι _ _
  refine ⟨Over.homMk (j.left.isoImage V').hom ?_, Over.homMk (j.left.isoImage V').inv ?_, ?_, ?_⟩
  · show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι ≫ T.hom = V'.ι ≫ T'.hom
    rw [← Category.assoc, he, Category.assoc, Over.w j]
  · show (j.left.isoImage V').inv ≫ V'.ι ≫ T'.hom = (j.left ''ᵁ V').ι ≫ T.hom
    rw [← Over.w j, ← Category.assoc V'.ι, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').inv ≫ (j.left.isoImage V').hom = 𝟙 _
    exact Iso.inv_hom_id _
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left
    exact he

theorem local_of_openImmersion (hL : L.IsLB) {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (H : WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c)) (p : T'.left) :
    ∃ V : T.left.Opens, j.left p ∈ V ∧
      (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
      ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
        CommIsOf A L k θx θy (unitRes V c) := by
  obtain ⟨V', hpV', ⟨θx₀, θy₀, hx₀, hy₀⟩, HV'⟩ := H p
  obtain ⟨a, b, hba, ha⟩ := exists_overRes_section_image_openImmersion j V'
  have hb : b ≫ overResι V' ≫ j = overResι (j.left ''ᵁ V') := by
    rw [← ha, ← Category.assoc, hba, Category.id_comp]
  refine ⟨j.left ''ᵁ V', ⟨p, hpV', rfl⟩, ?_, ?_⟩
  · obtain ⟨θx, hx, -⟩ := exists_pull hL b θx₀
    obtain ⟨θy, hy, -⟩ := exists_pull hL b θy₀
    refine ⟨θx, θy, ?_, ?_⟩
    · rw [hx, hx₀, ← hb]
      simp only [Category.assoc]
    · rw [hy, hy₀, ← hb]
      simp only [Category.assoc]
  · intro θx θy hx hy
    have key := commIsOf_of_retract hL b a hba θx θy
      (c := unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c))
      (fun θ₁ θ₂ h₁ h₂ => HV' θ₁ θ₂ (by rw [h₁, hx, ← Category.assoc, ha, Category.assoc])
        (by rw [h₂, hy, ← Category.assoc, ha, Category.assoc]))
    have hbl : b.left ≫ V'.ι ≫ j.left = (j.left ''ᵁ V').ι := congrArg Over.Hom.left hb
    have hu : Units.map b.left.appTop.hom.toMonoidHom (unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c)) =
        unitRes (j.left ''ᵁ V') c := by
      unfold unitRes
      rw [← hbl]
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app,
        CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
      rfl
    rw [hu] at key
    exact key

end GlobalTheory.WeilLocal

theorem GlobalTheory.weilIs_of_openCover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hML hA hG k x y x' y' c hx hy hW
  haveI : IsCommMonObj A := hA.comm
  unfold Out.WeilIs
  intro p
  obtain ⟨i, hi⟩ := GlobalTheory.CoverGlue.exists_mem hU p
  obtain ⟨j, hj⟩ : ∃ j : Over.mk ((Out.baseOver (U i).toScheme).hom ≫ (U i).ι) ⟶ Out.baseOver S,
      j.left = (U i).ι := ⟨Over.homMk (U i).ι (by simp [Out.baseOver]), rfl⟩
  haveI : IsOpenImmersion j.left := by
    rw [hj]
    infer_instance
  have hx₀ : (j ≫ x).left = (x' i).left ≫ ψ i := by rw [Over.comp_left, hj, hx i]
  have hy₀ : (j ≫ y).left = (y' i).left ≫ ψ i := by rw [Over.comp_left, hj, hy i]
  have H₀ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S (U i).toScheme A (G i) (U i).ι (ψ i) L (M i) hL (hM i)
    (hψ i) (hML i) (Out.baseOver (U i).toScheme) k (x' i) (y' i) (j ≫ x) (j ≫ y)
    (Units.map (U i).ι.appTop.hom.toMonoidHom c) hx₀ hy₀).1 (hW i)
  have H₁ : Out.WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c) := by
    rw [hj]
    exact H₀
  obtain ⟨V, hV, hl, hc⟩ := GlobalTheory.WeilLocal.local_of_openImmersion hL j H₁ ⟨p, hi⟩
  refine ⟨V, ?_, hl, hc⟩
  rw [hj] at hV
  exact hV
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetSpread

theorem exists_factor {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (j : Sp R ⟶ S) [IsOpenImmersion j]
    (x : Sp K ⟶ S) (q : PrimeSpectrum R) (y : Sp K) (hy : x y = j q) :
    ∃ f : R →+* K, spMap f ≫ j = x ∧ RingHom.ker f = q.asIdeal := by
  have hsub : Set.range x ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact ⟨q, by rw [← hy, Subsingleton.elim z y]⟩
  have hx : IsOpenImmersion.lift j x hsub ≫ j = x := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift j x hsub)
  rw [← hg] at hx
  have hq : Spec.map g y = q := by
    apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hx, hy]
  refine ⟨g.hom, hx, ?_⟩
  rw [← hq]
  have hy0 : PrimeSpectrum.asIdeal y = ⊥ := by
    rcases Ideal.eq_bot_or_top (PrimeSpectrum.asIdeal (R := K) y) with e | e
    · exact e
    · exact absurd e (PrimeSpectrum.isPrime y).ne_top
  change _ = Ideal.comap g.hom (PrimeSpectrum.asIdeal y)
  rw [hy0]
  rfl

theorem eq_comp_of_spMap {S : Scheme.{0}} {o R K : Type} [CommRing o] [CommRing R] [CommRing K]
    {j : Sp R ⟶ S} {s : S ⟶ Sp o} {δ : o →+* R} (hδ : j ≫ s = spMap δ) {f : R →+* K} {β : o →+* K}
    (h : (spMap f ≫ j) ≫ s = spMap β) (a : o) : β a = f (δ a) := by
  rw [Category.assoc, hδ] at h
  have h' : CommRingCat.ofHom δ ≫ CommRingCat.ofHom f = CommRingCat.ofHom β :=
    Spec.map_injective ((Spec.map_comp _ _).trans h)
  exact (congrArg (fun z => z.hom a) h').symm

theorem detCond_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {o : Type} [CommRing o] (s : S ⟶ Sp o) (ρ : o)
    (hρ : ρ ^ 2 = -(H.d : o))
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)})
    {R : Type} [CommRing R] [IsReduced R] (j : Sp R ⟶ S) [IsOpenImmersion j]
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (act' : OAct (𝓞 E) G') (hs : Smooth G'.hom)
    {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (hv : IsLieBasis v)
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ Sp R) (τ : 𝓞 E →+* K) (N : ℕ),
      LieMult act' y τ N ↔ LieMult act (y ≫ j) τ N)
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (β : o →+* K)
    (hβ : (spMap f ≫ j) ≫ s = spMap β) : DetCond D act (spMap f ≫ j) (β ρ) := by
  obtain ⟨δ₀, hδ₀⟩ := Spec.map_surjective (j ≫ s)
  have hδ : j ≫ s = spMap δ₀.hom := hδ₀.symm
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff (𝓞 E) R G' act' n v hs hv
  obtain ⟨M', hM', e⟩ := hM K f
  have hr : (δ₀.hom ρ) ^ 2 = -(H.d : R) := by
    have := congrArg δ₀.hom hρ
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have main := GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes E H D.p D.q n R M (δ₀.hom ρ) hr (by
    refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
    rintro q ⟨L, _, _, _, x, β', ⟨y, hy⟩, hx, hdet⟩
    obtain ⟨g, rfl, hg⟩ := exists_factor j x q y hy
    obtain ⟨N', hN', e'⟩ := hM L g
    refine ⟨L, inferInstance, inferInstance, inferInstance, g, N', hg, hN', fun τ => ?_⟩
    rw [← e', ← e', h, h, ← eq_comp_of_spMap hδ hx]
    exact hdet τ) K f M' hM'
  intro τ
  rw [← h, ← h, e, e, eq_comp_of_spMap hδ hβ]
  exact main τ

theorem detCond_of_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  intro E _ _ _ H D S _ G _ _ g act o _ s ρ hg hρ hd K _ _ _ x β hβ
  let y : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x y) trivial
  let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  obtain ⟨q, hq⟩ : x y ∈ Set.range j := hU.range_fromSpec.ge hs
  have hg₁ : SmoothOfRelativeDimension g ((Over.pullback j).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨r, hr, v, hv⟩ := GlobalTheory.LieLoc.lie_locally_free Γ(S, U) ((Over.pullback j).obj G) g hg₁ q
  let a : Sp (Localization.Away r) ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) (Localization.Away r))
  have : IsOpenImmersion a := IsOpenImmersion.of_isLocalization r
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(S, U) (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨f, rfl, -⟩ := exists_factor (a ≫ j) x q' y (by
    rw [← hq, ← hq']
    rfl)
  obtain ⟨a₁, h₁⟩ := GlobalTheory.DetExtend.exists_oAct_pullback j act
  obtain ⟨a₂, h₂⟩ := GlobalTheory.DetExtend.exists_oAct_pullback a a₁
  have hg₂ : SmoothOfRelativeDimension g ((Over.pullback a).obj ((Over.pullback j).obj G)).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg₁
  refine detCond_of_basis D act s ρ hρ hd (a ≫ j) a₂ (SmoothOfRelativeDimension.smooth g _) v hv
    (fun L _ z τ N => ?_) K f β hβ
  rw [LiePull.lieMult_pull _ _ _ _ _ a _ a₁ a₂ (isGrpPullback_pullback _ a)
    (fun c => by rw [h₂]; exact pullback.lift_fst _ _ _) L z τ N,
    LiePull.lieMult_pull _ _ _ _ _ j _ act a₁ (isGrpPullback_pullback _ j)
    (fun c => by rw [h₁]; exact pullback.lift_fst _ _ _) L (z ≫ a) τ N, Category.assoc]

end GlobalTheory.DetSpread
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_glue_rigidified_partial_line_bundles : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  first | exact @GlobalTheory.PartialBundleGlue.exists_glue | exact GlobalTheory.PartialBundleGlue.exists_glue | (intros; apply GlobalTheory.PartialBundleGlue.exists_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.InhabZOn


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.Models.InhabZOn.exists_dim_triple {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
    [ConnectedSpace S] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H S) : ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyIntegral t.G.hom :=
    _root_.GlobalTheory.geometricallyIntegral_of_isSemiAbelian (h := t.semi) _
  let e : S ⟶ t.G.left := (η[t.G]).left
  have he : e ≫ t.G.hom = 𝟙 S := Over.w (η[t.G])
  have hes : ∀ s, t.G.hom (e s) = s := fun s => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfib : ∀ s : S, _root_.IsPreconnected (t.G.hom ⁻¹' {s}) := fun s => by
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  have hsec : _root_.IsPreconnected (Set.range e) :=
    isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  haveI : PreconnectedSpace t.G.left := by
    refine ⟨isPreconnected_of_forall (e s₀) fun x _ => ?_⟩
    refine ⟨Set.range e ∪ t.G.hom ⁻¹' {t.G.hom x}, Set.subset_univ _, Or.inl ⟨s₀, rfl⟩,
      Or.inr rfl, ?_⟩
    exact hsec.union (e (t.G.hom x)) ⟨_, rfl⟩ (hes _) (hfib _)
  exact _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected t.G.hom (e s₀)

end GlobalTheory.Models.InhabZOn

end
end
