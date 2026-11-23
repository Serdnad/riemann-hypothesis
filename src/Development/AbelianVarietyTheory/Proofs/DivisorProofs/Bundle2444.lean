module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_of_valAt_eq : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (x : Sp K) (c : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) c)
    (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) c), P = Q := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ K _ _ t P Q PT QT hPT hQT x c hcP hcQ
  haveI hEt : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  let q := pq (IsLocalRing.closedPoint K)
  have hfq : (pullback.fst (torsion G n).hom (torsion G n).hom) q = PT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_fst]
  have hsq : (pullback.snd (torsion G n).hom (torsion G n).hom) q = QT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.snd (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_snd]
  haveI hdom : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk q) :=
    isDomain_stalk_of_etale (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q
  let Wp := pullback (torsion G n).hom (torsion G n).hom
  let R : Type := Wp.presheaf.stalk q
  let Ω := AlgebraicClosure (FractionRing R)
  let φ : R →+* Ω := algebraMap R Ω
  have hφ : Function.Injective φ := by
    have e : φ = (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) :=
      IsScalarTower.algebraMap_eq R (FractionRing R) Ω
    rw [e]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let ybar : Sp Ω ⟶ Spec (Wp.presheaf.stalk q) := Spec.map (CommRingCat.ofHom φ)
  haveI hyd : IsDominant ybar := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  let s0 : Sp Ω := IsLocalRing.closedPoint Ω
  have hgen : ∀ e, ybar s0 ⤳ e := by
    intro e
    have hr : Set.range ybar = {ybar s0} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨s0, rfl⟩, by rintro _ ⟨s, rfl⟩; rw [Subsingleton.elim s s0]⟩
    rw [specializes_iff_mem_closure, ← hr, ybar.denseRange.closure_range]
    trivial
  let f : Spec (Wp.presheaf.stalk q) ⟶ X' :=
    Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  obtain ⟨w', hw'q, hw'ξ⟩ := Flat.generalizingMap (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom)
    (genericPoint_specializes ((pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q))
  have hw'r : w' ∈ Set.range (Wp.fromSpecStalk q) := by rw [Scheme.range_fromSpecStalk]; exact hw'q
  obtain ⟨d, hd⟩ := hw'r
  have hξV : genericPoint X' ∈ Set.range ℓ := by
    rw [(genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range]
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, trivial, v, rfl⟩
  have hsp : (ybar ≫ f) s0 ⤳ genericPoint X' := by
    have h1 := (hgen d).map f.continuous
    have e2 : f d = (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) w' := by
      rw [← hd]; rfl
    rw [show (ybar ≫ f) s0 = f (ybar s0) from rfl, ← hw'ξ, ← e2]
    exact h1
  have H : Set.range (ybar ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s0]
    exact hsp.mem_open ℓ.isOpenEmbedding.isOpen_range hξV
  let z : Sp Ω ⟶ V := IsOpenImmersion.lift ℓ (ybar ≫ f) H
  have hz : z ≫ ℓ = ybar ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hcP' : ValAt G n ℓ w ((pullback.fst (torsion G n).hom (torsion G n).hom) q) c := by rw [hfq]; exact hcP
  have hcQ' : ValAt G n ℓ w ((pullback.snd (torsion G n).hom (torsion G n).hom) q) c := by rw [hsq]; exact hcQ
  have k1 : Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.fst (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have k2 : Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.snd (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have h1 := hcP' Ω (ybar ≫ Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k1])
  have h2 := hcQ' Ω (ybar ≫ Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k2, ← pullback.condition])
  rw [Category.assoc, reassoc_of% k1] at h1
  rw [Category.assoc, reassoc_of% k2] at h2
  have hu : Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
    refine ext_of_isDominant_of_isSeparated G.hom ?_ ybar (h1.trans h2.symm)
    simp only [Category.assoc, hιT, pullback.condition]
  have hpq : Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q = pq :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk pq
  apply Over.OverMorphism.ext
  rw [← hPT, ← hQT]
  calc PT ≫ (torsion.ι G n).left
      = pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [← Category.assoc, pullback.lift_fst]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [hu]
    _ = QT ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq, ← Category.assoc, pullback.lift_snd]

end GlobalTheory.TorsSpec
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section
open CartesianMonoidalCategory MonObj

namespace GlobalTheory.TorsSpec

theorem exists_etaSecL_of_torsI : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (I : Ideal (𝓞 E)) (hI : l.Mb ≤ I) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (P : Sp Ω ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left)
    (hP : P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = x ≫ ℓ)
    (hT : ∀ a ∈ I, P ≫ ((GlobalTheory.EqvAct.pullAct TF Z φ).act a).left =
      P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ GlobalTheory.EqvAct.pullG TF Z φ).left), ∃ c, P = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c := by
  intro E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ I hI Ω _ _ x P hP hT
  have cart := TF.Y.m.cart
  have hpb := GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ
  have hQw : (P ≫ GlobalTheory.EqvAct.pullψ TF Z φ) ≫ TF.Y.t.G.hom = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.jQ ≫ pullback.fst _ _) := by
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hP, Category.assoc, reassoc_of% hℓ, Category.assoc, j₀_ι]
    rfl
  let Q := cart.1.lift _ _ hQw
  have hQφ : Q ≫ TF.Y.m.φ = P ≫ GlobalTheory.EqvAct.pullψ TF Z φ := cart.1.lift_fst _ _ hQw
  have hQh : Q ≫ TF.Y.oF.t.G.hom = x ≫ i₀ TF.Y Z := cart.1.lift_snd _ _ hQw
  let Q' : Over.mk (x ≫ i₀ TF.Y Z) ⟶ TF.Y.oF.t.G := Over.homMk Q hQh
  have htu : ∀ {S : Scheme.{0}} (T : Over S), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have hcartη := eta_comp_of_isGrpPullback cart
  have hpbη := eta_comp_of_isGrpPullback hpb
  have htors : ∀ a ∈ I, Q' ≫ TF.Y.oF.t.act.act a = 1 := by
    intro a ha
    apply Over.OverMorphism.ext
    rw [Hom.one_def, Over.comp_left, Over.comp_left, htu]
    show Q ≫ _ = (x ≫ i₀ TF.Y Z) ≫ _
    apply cart.1.hom_ext
    · rw [Category.assoc, TF.Y.m.act, reassoc_of% hQφ, ← GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% (hT a ha),
        hpbη, Category.assoc, Category.assoc, hcartη, reassoc_of% hP]
      simp only [Category.assoc]
      rw [reassoc_of% hℓ, reassoc_of% j₀_ι]
      rfl
    · rw [Category.assoc, Over.w, hQh, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  let s0 : Xo.XF c ⟶ Sp (KA l) := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
  let β : KA l →+* Ω := (Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ s0)).hom
  have hβ : (x ≫ i₀ TF.Y Z) ≫ s0 = spMap β :=
    ((congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage _)).symm
  have hg := TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z) β hβ
  obtain ⟨TI, -, -, hη⟩ := hg.2
  have hMI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    apply hI
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hpow : Q' ^ l.M = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN, ← act_natCast (E := E) TF.Y.oF.t.act, htors _ hMI]
  obtain ⟨a, ha⟩ := (TI.onto l.M hM0 Q').1 hpow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have hev : Q' = TI.ev l.M (v • a) := by
    have e1 : TI.ev l.M (u • a) = 1 := by
      rw [TI.lin, ha]
      exact htors u (hI hu)
    have e2 := TI.add l.M (u • a) (v • a)
    rw [← add_smul, huv, one_smul, ha, e1, _root_.one_mul] at e2
    exact e2
  have hvm : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have hQeta : Q = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta (v • a)).left := by
    have := congrArg (fun q => q.left) (hev.trans (hη _ hvm).symm)
    simp only [Q', Over.homMk_left, Over.comp_left, htu] at this
    exact this
  refine ⟨Submodule.Quotient.mk (v • a), hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, etaSecL_ψ, ← hQφ, hQeta]
    simp only [Category.assoc]
  · rw [hP, Category.assoc, etaSecL_w]

end GlobalTheory.TorsSpec
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

open CartesianMonoidalCategory MonObj
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_comp_stalk {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) {W : Scheme.{0}} (f : W ⟶ (torsion G n).left) (q : W) (c : M)
    (h : ValAt G n ℓ w (f q) c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (z : Sp Ω ⟶ V)
    (hz : y ≫ W.fromSpecStalk q ≫ f ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ W.fromSpecStalk q ≫ f ≫ (torsion.ι G n).left = z ≫ w c := by
  have e := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
  have h1 := h Ω (y ≫ Spec.map (f.stalkMap q)) z (by rw [Category.assoc, reassoc_of% e]; exact hz)
  rwa [Category.assoc, reassoc_of% e] at h1

theorem comp_torsion_ι_mulN {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ torsion G n) :
    (a ≫ torsion.ι G n) ≫ mulN G n = 1 := by
  have e : torsion.ι G n ≫ mulN G n = toUnit (torsion G n) ≫ (η : 𝟙_ (Over X') ⟶ G) :=
    (pullback.condition (f := mulN G n) (g := (η : 𝟙_ (Over X') ⟶ G))).trans
      (congrArg (· ≫ (η : 𝟙_ (Over X') ⟶ G)) (toUnit_unique _ _))
  rw [Category.assoc, e, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem valAt_mul : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (hadd : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a b : M) (A B C : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w b → C.left = x ≫ w (a + b) → C = A * B)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hRT : RT ≫ (torsion.ι G n).left = (P * Q).left) (x : Sp K)
    (cP cQ cR : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ)
    (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = cP + cQ := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ hun hadd K _ _ t P Q PT QT RT hPT hQT hRT x cP cQ cR hcP hcQ hcR
  haveI : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  let h : pullback (torsion G n).hom (torsion G n).hom ⟶ X' :=
    pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  haveI : Etale h := inferInstance
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  haveI : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x)) :=
    isDomain_stalk_of_etale h (pq x)
  obtain ⟨Ω, _, _, y, hy, -⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x))
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat h (pq x) ℓ Ω y hy
  let WO : Over X' := Over.mk h
  let A' : WO ⟶ torsion G n := Over.homMk (pullback.fst (torsion G n).hom (torsion G n).hom) rfl
  let B' : WO ⟶ torsion G n :=
    Over.homMk (pullback.snd (torsion G n).hom (torsion G n).hom) pullback.condition.symm
  let A : WO ⟶ G := A' ≫ torsion.ι G n
  let B : WO ⟶ G := B' ≫ torsion.ι G n
  have hs : (A * B) ≫ mulN G n = 1 := by
    letI : CommGroup (WO ⟶ G) := Hom.commGroup
    rw [GlobalTheory.GrpTangent.comp_mulN, mul_pow, ← GlobalTheory.GrpTangent.comp_mulN, ← GlobalTheory.GrpTangent.comp_mulN,
      comp_torsion_ι_mulN, comp_torsion_ι_mulN, _root_.one_mul]
  obtain ⟨sT, hsT⟩ := exists_lift_torsion n (A * B) hs
  let g : Over.mk t ⟶ WO := Over.homMk pq (by
    show pq ≫ pullback.fst _ _ ≫ _ = t
    rw [pullback.lift_fst_assoc, hPt])
  have hgA : g ≫ A = P := by
    ext1
    simp only [A, A', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_fst_assoc, hPT]
  have hgB : g ≫ B = Q := by
    ext1
    simp only [B, B', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_snd_assoc, hQT]
  have hRT' : pq ≫ sT.left = RT := by
    haveI := mono_torsion_ι G n
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, ← Over.comp_left, hsT, hRT, ← hgA, ← hgB,
      ← MonObj.comp_mul]
    rfl
  have e1 : (pullback.fst (torsion G n).hom (torsion G n).hom) (pq x) = PT x := by
    show (pq ≫ pullback.fst _ _) x = _
    rw [pullback.lift_fst]
  have e2 : (pullback.snd (torsion G n).hom (torsion G n).hom) (pq x) = QT x := by
    show (pq ≫ pullback.snd _ _) x = _
    rw [pullback.lift_snd]
  have e3 : sT.left (pq x) = RT x := by
    show (pq ≫ sT.left) x = _
    rw [hRT']
  rw [← e1] at hcP
  rw [← e2] at hcQ
  rw [← e3] at hcR
  have hP' := valAt_comp_stalk G n ℓ w _ (pq x) cP hcP Ω y z hz
  have hQ' := valAt_comp_stalk G n ℓ w _ (pq x) cQ hcQ Ω y z (by rw [← pullback.condition]; exact hz)
  have hR' := valAt_comp_stalk G n ℓ w sT.left (pq x) cR hcR Ω y z (by rw [Over.w sT]; exact hz)
  let k : Over.mk (z ≫ ℓ) ⟶ WO :=
    Over.homMk (y ≫ (pullback (torsion G n).hom (torsion G n).hom).fromSpecStalk (pq x))
      (by simpa [WO] using hz)
  have hC := hadd Ω z cP cQ (k ≫ A) (k ≫ B) (Over.homMk (z ≫ w (cP + cQ)) (by simp [hw]))
    (by simpa [k, A, A'] using hP') (by simpa [k, B, B'] using hQ') rfl
  rw [← MonObj.comp_mul, ← hsT] at hC
  have hC' := congrArg (fun u => u.left) hC
  simp only [Over.homMk_left, Over.comp_left, k] at hC'
  refine hun Ω z cR (cP + cQ) ?_
  rw [← hR']
  simp only [Category.assoc] at hC'
  exact hC'.symm

end GlobalTheory.TorsSpec
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

variable {D : Formalism.BasicNotions.D7}

theorem other_of_not_thick (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau)
    (hv : GlobalTheory.ExpTie.Lift.ValsAt L j τ) (hT : τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2) :
    ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  classical
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m

  have hw : ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ L.Sc + (GlobalTheory.ExpTie.Lift.wts L j).c τ := by
    have hU := U_last L j τ
    have h0 := hv.1 0 (by omega)
    have hcv := (L.cloud_v τ ⟨0, by omega⟩).2
    have hwd : (GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ = (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 := by
      show (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 - (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ ((Vc D j).rank - 1) = _
      rw [hU, sub_zero]
    rw [hwd]
    linarith
  have hc := c_le L j τ hv
  have hnt : (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces := by
    intro h
    apply hT
    simp only [wts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have he : (GlobalTheory.ExpTie.Lift.wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
      unfold Host.topPlaces at htop
      simpa using htop
    have x1 := L.sc.one_lt_alt
    have x0 : 0 < L.sc.x := by linarith
    have hb0 : 0 < L.sc.b' := by
      have hX : 0 < L.sc.X' := by unfold Scale.X'; positivity
      have hb : 0 < L.sc.b := by unfold Scale.b; positivity
      unfold Scale.b' Scale.a
      positivity
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    have hLa : 0 < L.LaG := by
      have h1 := P5.S_le
      have h2 := L.Sc_pos
      by_contra hn
      push_neg at hn
      have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hb0.le) hk0.le
      linarith
    have hbT : ((L.bT ⟨t, ht1⟩ : ℝ)) ≤ L.sc.b' * (1 + 1 / L.sc.x ^ 2) := by
      have h1 := P5.bT_le ⟨t, ht1⟩
      have h2 := P5.rho_le
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      unfold LevelStarExponents.rhoP at h2
      rw [hx2] at h2
      have hq : 0 ≤ 1 / L.sc.x ^ 2 := by positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        linarith
      have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h6 := mul_le_mul_of_nonneg_right h5 hb0.le
      nlinarith
    have a := L.bT_ge ⟨t, ht1⟩
    have wj1 := L.win_top ((j : ℕ) + 1) (by omega) (by omega) τ ⟨t, ht1⟩ ht2.symm
    have wjm := L.win_top D.R.m (by omega) le_rfl τ ⟨t, ht1⟩ ht2.symm
    refine ⟨⟨(L.bT ⟨t, ht1⟩ : ℝ), a, hbT, ?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' * (1 + 1 / L.sc.x ^ 2) + L.sc.b' / L.sc.x := by ring
      linarith [wjm.2]
  · right
    have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, htop, hnt⟩
    have wj1 := L.win_thin ((j : ℕ) + 1) (by omega) (by omega) τ hthin
    have wjm := L.win_thin D.R.m (by omega) le_rfl τ hthin
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.w'' D.R.n + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      linarith [wjm.2]

end GlobalTheory.ExpTie.Lift
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi


theorem _root_.GlobalTheory.T.eq_of_torsionPointClassAtStalk_eq : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (x : Sp K) (c : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) c)
    (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) c), P = Q := by
  first | exact @GlobalTheory.TorsSpec.eq_of_valAt_eq | exact GlobalTheory.TorsSpec.eq_of_valAt_eq | (intros; apply GlobalTheory.TorsSpec.eq_of_valAt_eq <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi


theorem _root_.GlobalTheory.T.exists_levelSection_of_ideal_torsion_at_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (I : Ideal (𝓞 E)) (hI : l.Mb ≤ I) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (P : Sp Ω ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left)
    (hP : P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = x ≫ ℓ)
    (hT : ∀ a ∈ I, P ≫ ((GlobalTheory.EqvAct.pullAct TF Z φ).act a).left =
      P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ GlobalTheory.EqvAct.pullG TF Z φ).left), ∃ c, P = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c := by
  first | exact @GlobalTheory.TorsSpec.exists_etaSecL_of_torsI | exact GlobalTheory.TorsSpec.exists_etaSecL_of_torsI | (intros; apply GlobalTheory.TorsSpec.exists_etaSecL_of_torsI <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi


theorem _root_.GlobalTheory.T.torsionPoint_class_mul_eq_add : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (hadd : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a b : M) (A B C : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w b → C.left = x ≫ w (a + b) → C = A * B)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hRT : RT ≫ (torsion.ι G n).left = (P * Q).left) (x : Sp K)
    (cP cQ cR : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ)
    (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = cP + cQ := by
  first | exact @GlobalTheory.TorsSpec.valAt_mul | exact GlobalTheory.TorsSpec.valAt_mul | (intros; apply GlobalTheory.TorsSpec.valAt_mul <;> assumption)

end
end
