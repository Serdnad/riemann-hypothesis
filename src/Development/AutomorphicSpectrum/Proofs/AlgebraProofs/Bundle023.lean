module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

section Abstract

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def ptSub {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1)
    (T : C) : Subgroup (T ⟶ A) where
  carrier := {f | ∃ a : T ⟶ X, a ≫ h = f}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨lift a b ≫ m, ?_⟩
    rw [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  one_mem' := ⟨toUnit T ≫ e, by rw [Category.assoc, he, MonObj.comp_one]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a ≫ i, ?_⟩
    rw [eq_inv_iff_mul_eq_one, Category.assoc, ← MonObj.comp_mul, hi, MonObj.comp_one]

def ptFunctor {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (ptSub h m e i hm he hi (unop T))
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨f.unop ≫ a, by rw [Category.assoc, ha]⟩⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.id_comp x.1))
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.assoc _ _ x.1))

def ptRep {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    (ptFunctor h m e i hm he hi ⋙ forget _).RepresentableBy X where
  homEquiv {T} := Equiv.ofBijective
    (fun a => (⟨a ≫ h, a, rfl⟩ : ptSub h m e i hm he hi T))
    ⟨fun a b hab => (cancel_mono h).1 (congrArg Subtype.val hab),
      fun x => by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨a, Subtype.ext ha⟩⟩
  homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _)

theorem exists_grpObj_of_mono {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by
  let α := ptRep h m e i hm he hi
  letI G : GrpObj X := GrpObj.ofRepresentableBy X _ α
  have key : ∀ {T : C} (a b : T ⟶ X), (a * b) ≫ h = (a ≫ h) * (b ≫ h) := fun {T} a b =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_mul a b)
  have key1 : ∀ {T : C}, (1 : T ⟶ X) ≫ h = 1 := fun {T} =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_one)
  refine ⟨G, ⟨?_, ?_⟩⟩
  · have := key1 (T := 𝟙_ C)
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using this
  · have := key (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this, Hom.mul_def]
    congr 1
    ext <;> simp

end Abstract

section Scheme

variable {R : Type} [CommRing R]

theorem exists_eq_spMap {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩

theorem exists_sp_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by
  have hU := isAffineOpen_top T.left
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, ⊤) := ρ.hom.toAlgebra
  let j : sp (R₀ := R) Γ(T.left, ⊤) ⟶ T := Over.homMk hU.fromSpec hρ.symm
  have : IsIso j.left := by
    change IsIso hU.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hj : IsIso ((Over.forget _).map j) := ‹IsIso j.left›
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, j, isIso_of_reflects_iso j (Over.forget _)⟩

variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}

theorem affine_mono (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) (hab : a ≫ h = b ≫ h) : a = b := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  have := H.mono S φ φ' (by rw [← hφ, ← hφ', Category.assoc, Category.assoc, hab])
  rw [← cancel_epi j, hφ, hφ', this]

theorem affine_mul (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = (a ≫ h) * (b ≫ h) := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  obtain ⟨χ, hχ⟩ := H.mul S φ φ'
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [Category.assoc, hχ, ← hφ, ← hφ', MonObj.comp_mul, Category.assoc, Category.assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]

theorem affine_one (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] :
    ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨χ, hχ⟩ := H.one S
  exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩

theorem affine_inv (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, (c ≫ h) * (a ≫ h) = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨χ, hχ⟩ := H.inv S φ
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [← hφ] at hχ
  have := congrArg (inv j ≫ ·) hχ
  simp only [MonObj.comp_mul, MonObj.comp_one, Category.assoc, IsIso.inv_hom_id_assoc] at this
  simpa [Category.assoc] using this

theorem mono_of_isFinFlatSub (H : IsFinFlatSub A B h) : Mono h := by
  constructor
  intro T a b hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineCover _ _ fun i => ?_
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f i ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
  haveI : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have := affine_mono H (j ≫ a) (j ≫ b) (by rw [Category.assoc, Category.assoc, hab])
  exact congrArg (·.left) this

theorem grpObj_of_isFinFlatSub (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type)
    [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A) (H : IsFinFlatSub A B h) :
    ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  have hmono := mono_of_isFinFlatSub H
  haveI : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
    inferInstanceAs (IsAffine (pullback (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom))
  obtain ⟨m, hm⟩ := affine_mul H (fst _ _) (snd _ _)
  obtain ⟨e, he⟩ := affine_one H (T := 𝟙_ _)
  obtain ⟨i, hi⟩ := affine_inv H (𝟙 _)
  rw [Category.id_comp] at hi
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e i hm he hi
  exact ⟨G, hG, hmono⟩

end Scheme

end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem tors_pts_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : TorsRep G p) (N : Type) [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → Finite N := by
  intro R _ _ p G _ T N _ pt h
  haveI := T.free
  haveI := T.fin
  have hx : ∀ x, ∃ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x := fun x =>
    (T.univ R (pt x) ((h.range _).2 ⟨x, rfl⟩)).exists
  choose f hf using hx
  refine Finite.of_injective f fun x y e => h.inj ?_
  rw [← hf x, ← hf y, e]

end GlobalTheory.CompanionTheory.Ar.GR
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

namespace PtBasic

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem ht_surjective : Function.Surjective P.ht := by
  have : P.om.IsFullLattice C := P.om_lat
  have hspan : Submodule.span C (P.om : Set Ω) = ⊤ := Submodule.IsFullLattice.span_eq_top
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  intro y hy
  obtain ⟨x, -, hx⟩ := P.κ_mem y hy
  show y ∈ LinearMap.range P.ht
  rw [LinearMap.mem_range]
  refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
  rw [map_smul, hx, ← algebraMap_smul C κ y, smul_smul, inv_mul_cancel₀ P.κ_ne, one_smul]

theorem T_lattice : P.T.IsLattice C := by
  obtain ⟨hli, -, hT⟩ := P.free
  have hfg : P.T.FG := by
    rw [hT]
    exact Submodule.fg_span (Set.finite_range _)
  refine ⟨hfg, ?_⟩
  intro s hs hliO
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact linearIndepOn_empty C id
  have hinj : Function.Injective (algebraMap O C) := by
    intro a b hab
    apply hliO.linearIndependent.smul_left_injective ⟨x, hx⟩
    change a • x = b • x
    rw [← algebraMap_smul C a x, ← algebraMap_smul C b x, hab]
  have : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).mpr hinj
  have : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine Submodule.linearIndepOn_of_finrank_le_finrank_span P.T hfg ?_ hs hliO
  rw [hT, Submodule.span_span_of_tower O, finrank_span_eq_card hli,
    finrank_span_eq_card (hli.restrict_scalars' O)]

theorem rho_t_mem (a : 𝓞 E) (i : Fin N) : P.ρ a (P.t i) ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hmem : ∀ k, P.ρ (RingOfIntegers.basis E k) (P.t i) ∈ P.T := fun k => by
    rw [hT]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  rw [← (RingOfIntegers.basis E).sum_repr a]

  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun k _ => zsmul_mem (hmem k) _

theorem T_stable (a : 𝓞 E) : ∀ x ∈ P.T, P.ρ a x ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hle : P.T ≤ P.T.comap ((P.ρ a).restrictScalars O) := by
    nth_rewrite 1 [hT]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∈ P.T
    rw [show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) =
        (P.ρ a * P.ρ (RingOfIntegers.basis E q.2)) (P.t q.1) from rfl, ← map_mul]
    exact rho_t_mem P _ _
  exact fun x hx => hle hx

theorem ht_eigProj (σ : E →+* C) (x : V) :
    P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x) := by

  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, P.ht_lin]

theorem om'_lattice : P.om'.IsLattice C := by
  have : P.om.IsFullLattice C := P.om_lat
  apply Submodule.IsLattice.mono_of_fg C (show P.om' ≤ P.om from ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact P.ht_mem x hx
  · rw [HTPoint.om']
    exact (T_lattice P).fg.map _

theorem omHT_eq (σ : E →+* C) :
    P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O) := by
  have hcomm : ((eigProj P.ρΩ σ).restrictScalars O) ∘ₗ (P.ht.restrictScalars O) =
      (P.ht.restrictScalars O) ∘ₗ ((eigProj P.ρ σ).restrictScalars O) :=
    LinearMap.ext fun x => (ht_eigProj P σ x).symm
  show (P.T.map (P.ht.restrictScalars O)).map ((eigProj P.ρΩ σ).restrictScalars O) =
    (P.T.map ((eigProj P.ρ σ).restrictScalars O)).map (P.ht.restrictScalars O)
  rw [← Submodule.map_comp, ← Submodule.map_comp, hcomm]

theorem e_skew (x y : V) : P.e x y = - P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem dualLat_flip : dualLat P.e.flip P.T = P.T := by
  conv_rhs => rw [← P.perfect]
  ext y
  simp only [LatBasic.mem_dualLat, LinearMap.flip_apply]
  refine forall₂_congr fun x _ => ?_
  rw [e_skew P y x, neg_mem_iff]
include P in
theorem finite_V : Module.Finite C V := by
  obtain ⟨s, hs⟩ := (T_lattice P).fg
  refine ⟨⟨s, ?_⟩⟩
  rw [← Submodule.span_span_of_tower O, hs, P.free.2.1]
include P in
theorem two_mul_finrank : 2 * finrank C Ω = finrank C V := by
  haveI := finite_V P
  have hrefl : LinearMap.BilinForm.IsRefl P.e := fun x y h => by rw [e_skew P y x, h, neg_zero]
  have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
    ext x
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker]
    rw [P.lagr x]
    refine forall₂_congr fun y _ => ?_
    rw [e_skew P y x, neg_eq_zero]
  have htop : LinearMap.BilinForm.orthogonal P.e ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    exact (Submodule.mem_bot C).mpr (P.nondeg x fun y => hx y Submodule.mem_top)
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl (LinearMap.ker P.ht)
  rw [horth, htop, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker P.ht
  rw [LinearMap.range_eq_top.mpr (ht_surjective P), finrank_top] at h2
  omega

end PtBasic

theorem htPoint_basic : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω), Function.Surjective P.ht ∧ P.T.IsLattice C ∧ (∀ (a : 𝓞 E), ∀ x ∈ P.T, P.ρ a x ∈ P.T) ∧ (∀ (σ : E →+* C) x, P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x)) ∧ P.om'.IsLattice C ∧ (∀ σ : E →+* C, P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O)) ∧ dualLat P.e.flip P.T = P.T ∧ 2 * Module.finrank C Ω = Module.finrank C V := by
  intro C _ v O _ _ _ _ _ E _ _ c _ κ N V _ _ _ _ Ω _ _ _ _ P
  exact ⟨PtBasic.ht_surjective P, PtBasic.T_lattice P, PtBasic.T_stable P, PtBasic.ht_eigProj P,
    PtBasic.om'_lattice P, PtBasic.omHT_eq P, PtBasic.dualLat_flip P, PtBasic.two_mul_finrank P⟩

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ _ _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj
  haveI := hj
  have hex : ∀ x : N, ∃ y : N', pt' y = pt x ≫ j := by
    intro x
    apply (hpt'.range _).1
    have hx : (pt x) ^ p = 1 := (hpt.range _).2 ⟨x, rfl⟩
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  choose f hf using hex
  have hadd : ∀ x y : N, f (x + y) = f x + f y := by
    intro x y
    apply hpt'.inj
    rw [hpt'.add, hf, hf, hf, hpt.add, MonObj.mul_comp]
  let jN : N →+ N' :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        simpa using h.symm
      map_add' := hadd }
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  refine ⟨jN, ψ, fun x => hf x, hψ, ?_⟩
  intro g hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨ψ a, ?_⟩
  intro x φ hφ
  have key : spMap (φ.comp ψ) ≫ T'.y = pt' (jN x) := by
    rw [← Chart.spMap_comp ψ φ]
    change (spMap φ ≫ spMap ψ) ≫ T'.y = pt' (f x)
    rw [Category.assoc, hψ, ← Category.assoc, hφ, hf]
  exact ha (jN x) (φ.comp ψ) key
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.dual_lattice_degree_neg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K), IsBun C L → Function.Bijective B → IsBun C (dualLat C L B) ∧ deg C (dualLat C L B) = - deg C L ∧ dualLat C (dualLat C L B) B.flip = L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | exact GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.frobenius_lattice_degree_mul_p : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L → IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat <;> assumption)
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem _root_.GlobalTheory.T.different_generator_dual_integral : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E] [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → algebraMap A K d ≠ 0 ∧ (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧ ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A, ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | exact GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot


theorem _root_.GlobalTheory.T.finite_free_pullback_affine : ∀ {P Q D W : Scheme.{0}} {u : P ⟶ Q} {v : P ⟶ D} {g : Q ⟶ W} {h : D ⟶ W} [IsAffine P] [IsAffine Q] [IsAffine D] [IsAffine W], IsPullback u v g h → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom g.appTop.hom → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom v.appTop.hom := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback <;> assumption)
end
