module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) := by
  first | exact @GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | exact GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | (intros; apply GlobalTheory.PrimVan.acyclic_cechLB_of_primitive <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.SpecialPairing

local instance (priority := high) grpObjPullbackForSpecialPairing {S T : Scheme.{0}}
    (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

theorem card_map {A₀ A A' : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] (r : A →* A₀) (j : A →* A') (N : ℕ)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (K : Subgroup A₀) :
    Nat.card (((powMonoidHom N).ker ⊓ K.comap r).map j) = Nat.card {x : A₀ // x ^ N = 1 ∧ x ∈ K} := by
  rw [Subgroup.card_map_of_injective hj]
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨r y.1, by rw [← map_pow, show y.1 ^ N = 1 from y.2.1, map_one],
    y.2.2⟩) ⟨fun y y' h => Subtype.ext (ri _ _ y.2.1 y'.2.1 (congrArg Subtype.val h)), fun x => ?_⟩)
  obtain ⟨y, hy, e⟩ := rs x.1 x.2.1
  exact ⟨⟨y, hy, show r y ∈ K from e ▸ x.2.2⟩, Subtype.ext e⟩

theorem core {A₀ A A' B : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] [CommGroup B] (r : A →* A₀)
    (j : A →* A') (q : A₀ →* B) (N M : ℕ) (P' : A' → A' → Prop) (P : B → B → Prop)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (qs : ∀ b, b ^ N = 1 → ∃ x, x ^ N = 1 ∧ q x = b)
    (hP : ∀ y y', y ^ N = 1 → y' ^ N = 1 → P (q (r y)) (q (r y')) → P' (j y) (j y'))
    (h1 : ∀ b, b ^ N = 1 → P 1 b)
    (hc : Nat.card {x : A₀ // x ^ N = 1 ∧ q x = 1} * Nat.card {x : A₀ // x ^ N = 1} = M)
    (rad : ∀ T H : Subgroup A', (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = M →
      (∀ x ∈ T, ∀ y ∈ H, P' x y) → ∀ x, x ^ N = 1 → (∀ y ∈ H, P' x y) → x ∈ T)
    (b : B) (hb : b ^ N = 1) (h : ∀ b', b' ^ N = 1 → P b b') : b = 1 := by
  have tq : ∀ y : A, y ^ N = 1 → q (r y) ^ N = 1 := fun y hy => by rw [← map_pow, ← map_pow, hy, map_one, map_one]
  have tj : ∀ y : A, y ^ N = 1 → j y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨x, hx, rfl⟩ := qs b hb
  obtain ⟨y, hy, rfl⟩ := rs x hx
  obtain ⟨y', hy', e⟩ := rad (((powMonoidHom N).ker ⊓ q.ker.comap r).map j)
    (((powMonoidHom N).ker ⊓ (⊤ : Subgroup A₀).comap r).map j)
    (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1) (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1)
    (by
      rw [card_map r j N ri rs hj, card_map r j N ri rs hj, ← hc]
      simp only [Subgroup.mem_top, and_true, MonoidHom.mem_ker])
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      refine hP z z' hz.1 hz'.1 ?_
      rw [show q (r z) = 1 from hz.2]
      exact h1 _ (tq _ hz'.1))
    (j y) (tj y hy) (by
      rintro _ ⟨z', hz', rfl⟩
      exact hP y z' hy hz'.1 (h _ (tq _ hz'.1)))
  obtain rfl := hj e
  exact hy'.2

theorem exists_embedding (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Algebra V W]
    [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure (FractionRing V), Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure (FractionRing V))) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V)]
    exact (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure (FractionRing V)) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure (FractionRing V) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    change Ideal.comap (algebraMap V W) (RingHom.ker φ.toRingHom) = ⊥
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem torsion_ext (W : Type) [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (p : Spec (CommRingCat.of W) ⟶ S) (N : ℕ)
    (hN : IsUnit (N : W)) {Ω : Type} [Field Ω] (f : W →+* Ω) [IsLocalHom f] (y y' : Over.mk p ⟶ G) (hy : y ^ N = 1)
    (hy' : y' ^ N = 1) (e : Spec.map (CommRingCat.ofHom f) ≫ y.left = Spec.map (CommRingCat.ofHom f) ≫ y'.left) :
    y = y' := by
  have := GlobalTheory.TorsionSeparable.epi_specMap (IsLocalRing.ResidueField.lift f)
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Category.assoc, cancel_epi] at e
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W))) rfl
  exact (GlobalTheory.existsUnique_torsion_lift W S G p N hN (ρ ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])).unique ⟨hy, rfl⟩ ⟨hy', e.symm⟩

theorem toBase_bijective {S S' : Scheme.{0}} (G : Over S) (f : S' ⟶ S) (T : Over S') :
    Function.Bijective (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f)
      pullback.condition (T := T)) :=
  ⟨fun x y h => Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun z => z.left) h)
    ((Over.w x).trans (Over.w y).symm)), fun x =>
    ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩⟩



theorem pairing_nondegenerate : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ x : Over.mk p ⟶ (t.l 0).Q.B, x ^ N = 1 → (∀ y : Over.mk p ⟶ (t.l 0).Q.B, y ^ N = 1 → CubWeil (t.l 0).D.M.c N x y 1) → x = 1 := by
  intro hAb hL V _ _ _ A G _ _ s t Ω _ _ p N hN
  obtain ⟨dvr, cpl, -⟩ := s.cdvr
  have := s.semi.smooth
  have := s.semi.separated
  have := (t.l 0).Q.q_hom
  obtain ⟨φ₀, rfl⟩ : ∃ φ₀ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* Ω, p = Spec.map (CommRingCat.ofHom φ₀) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  let f : V →+* Ω := φ₀.comp (Ideal.Quotient.mk _)
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra h
    have : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact h)
    exact ha.ne_zero (by rw [RingHom.comp_apply, this, map_zero])⟩
  have hNΩ : (N : Ω) ≠ 0 := by simpa using (hN.map f).ne_zero
  have hN0 : N ≠ 0 := by rintro rfl; simp at hNΩ
  obtain ⟨g', hg'⟩ : ∃ g', SmoothOfRelativeDimension g' (t.l 0).Q.B.hom := by
    have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := φ₀.domain_nontrivial
    have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact GlobalTheory.AbelianDim.exists_relDim _ _ (t.l 0).Q.isAb
  have hd := (GlobalTheory.UU.Tower.dim_eq_add_finrank V A G s t g').1 hg'
  obtain ⟨c₁, c₂⟩ := torusQuotient_card_torsion _ _ _ (t.l 0).Q Ω (Spec.map (CommRingCat.ofHom φ₀)) N hNΩ
  rw [GlobalTheory.card_torsion_geometricPoint_of_field hAb _ _ (t.l 0).Q.isAb g' hg' Ω _ N hNΩ] at c₂
  let T₀ : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) :=
    Over.mk (Spec.map (CommRingCat.ofHom φ₀))
  have hpf : Spec.map (CommRingCat.ofHom f) = T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  let β : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) ≃*
      (Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ G) :=
    MulEquiv.ofBijective (toBaseHom (toBase_mul_pullback G _) T₀) (toBase_bijective G _ T₀)
  have hβ : ∀ x, (β x).left = x.left ≫ (fstG _ 0 G).left := fun _ => rfl
  let ι₀ : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hpf.symm)
  have fin : Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  have fin' := (show Set.Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G | x ^ N = 1} from fin).image
    (fun x => ι₀ ≫ β x)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V G N
    hN Ω f hf fin'.toFinset (by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := fin'.mem_toFinset.1 hx
      show (ι₀ ≫ β u) ^ N = 1
      rw [← MonObj.comp_pow, ← map_pow, show u ^ N = 1 from hu, map_one, MonObj.comp_one])
  obtain ⟨φ, φi, hφ⟩ := exists_embedding V W inj
  let TW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let ρ : Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) (by
      refine Eq.trans ?_ hpf
      rw [← hf', CommRingCat.ofHom_comp, Spec.map_comp]; rfl)
  let σ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
      have e := congrArg (fun z => Spec.map (CommRingCat.ofHom z)) hφ
      simp only [CommRingCat.ofHom_comp, Spec.map_comp] at e
      exact e)
  let r : (TW ⟶ G) →* (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) := β.symm.toMonoidHom.comp (preHom ρ)
  have hr : ∀ y, (r y).left ≫ (fstG _ 0 G).left = Spec.map (CommRingCat.ofHom f') ≫ y.left := fun y =>
    (hβ _).symm.trans (congrArg (fun z => z.left) (β.apply_symm_apply (ρ ≫ y)))
  let q : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) →* (T₀ ⟶ (t.l 0).Q.B) :=
    MonoidHom.mk' (· ≫ (t.l 0).Q.q) fun x y => MonObj.mul_comp x y _
  refine core r (preHom σ) q N (N ^ (2 * A.g)) (fun x y => CubWeil s.P.c N x y 1)
    (fun x y => CubWeil (t.l 0).D.M.c N x y 1) (fun y y' hy hy' e => ?_) (fun x hx => ?_) (fun y y' e => ?_)
    ?_ (fun y y' hy hy' h => ?_) (fun b hb => cubWeil_one_left _ hb) ?_
    (mem_of_cubWeil_orthogonal hL V A G s _ N (Nat.one_le_iff_ne_zero.2 hN0))
  · refine torsion_ext W G _ N (by simpa using hN.map (algebraMap V W)) f' y y' hy hy' ?_
    rw [← hr, ← hr, e]
  · obtain ⟨y, hy, e⟩ := lifts (ι₀ ≫ β x) (fin'.mem_toFinset.2 ⟨x, hx, rfl⟩)
    refine ⟨y, hy, β.injective (Over.OverMorphism.ext ?_)⟩
    have e' : (ι₀ ≫ β x).left = (β x).left := Category.id_comp _
    rw [hβ, hr y, e, e']
  · exact GlobalTheory.over_points_ext_of_injective _ G W _ φ φi _ y y' (congrArg (fun z => z.left) e)
  · refine (torusQuotient_points_lift _ _ _ (t.l 0).Q Ω _).2 N fun a => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a.val (Nat.pos_of_ne_zero hN0)
    have hz0 : z ≠ 0 := by rintro rfl; exact a.ne_zero (by rw [← hz, zero_pow hN0])
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  · have := ((cubWeil_one_iff_closedFibre V A G s t W Ω f' inferInstance _ N hN y y' (r y) (r y') hy hy' (hr y) (hr y')).2 h).comp σ
    rwa [map_one] at this
  · have e : N ^ (2 * A.g) = N ^ Module.finrank ℤ s.X * (N ^ Module.finrank ℤ s.X * N ^ (2 * g')) := by
      rw [hd]; ring
    rw [e]
    exact congrArg₂ (· * ·) ((Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans c₁) c₂

end GlobalTheory.UU.SpecialPairing
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.TowerEx

theorem toBase_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (hw : F ≫ G.hom = G'.hom ≫ f) (T : Over S') (x y : T ⟶ G') :
    toBase hw (x * y) = toBase hw x * toBase hw y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f f' : S' ⟶ S} {F F' : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) (e : f = f') (e' : F = F') (hw') : ∃ w', IsCPMap P' P f' F' hw' w' := by
  subst e e'
  exact ⟨w, h⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left}
    {hw w hw'' w''} (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P f'' F'' hw'' w'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') :
    ∃ w', IsCPMap P'' P' f' F' hF.1.w w' := by
  subst e e'
  exact ((isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF.1.w _ h).2 (toBase_mul hF _) _ h'').imp fun _ => And.left

theorem exists_even_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    [IsMonHom i'] (hi : TorusCompat f F i' i) (σ : CubTriv P.c i) (hσ : σ.Even) :
    ∃ σ' : CubTriv P'.c i', σ'.Even := by
  have hE := SplitTorus.isGrpPullback_bcMap f X
  rw [torusCompat_iff] at hi
  have hc : ∀ k : Fin 2, ![i'.left, (1 : splitTorus S' X ⟶ G').left] k ≫ F =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus S X ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · show (1 : splitTorus S' X ⟶ G').left ≫ F = SplitTorus.bcMap f X ≫ (1 : splitTorus S X ⟶ G).left
      rw [one_left_comp h.mul, one_left, ← Category.assoc, hE.1.w]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 h.gen) P.L.isLB P'.L.isLB _ hc σ.s σ.gen
  let β := toBaseHom (toBase_mul hE hE.1.w)
  have hβ : ∀ {T : Over S'} (t : T ⟶ splitTorus S' X), β T t ≫ i = toBase hw (t ≫ i') := fun t =>
    Over.OverMorphism.ext (by
      show (t.left ≫ SplitTorus.bcMap f X) ≫ i.left = (t.left ≫ i'.left) ≫ F
      rw [Category.assoc, hi, Category.assoc])
  have vs : ∀ (T : Over S') (z : T.left) (J') (J), Good P'.L.L z J' → Good P.L.L z J →
      ∀ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left)) →
      ∀ t : T ⟶ splitTorus S' X, @id (T.left.presheaf.stalk z)ˣ (val σ.s (β T t).left z J) =
        W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := by
    intro T z J' J hJ' hJ W hW t
    refine (CubTransport.val_pmaps hc Hs t.left hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    rw [hW, hW]
    exact CubTrivTorus.prod_cubTriv i' t (fun q => gw w q z (J (q ≫ F)) (J' q))
  refine ⟨⟨s, hs, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.2 (x ≫ i') (y ≫ i') (u ≫ i')
    obtain ⟨Z, hZ⟩ : ∃ Z : (T ⟶ splitTorus S' X) → (T.left.presheaf.stalk z)ˣ,
      ∀ t, Z t = val σ.s (β T t).left z J := ⟨_, fun _ => rfl⟩
    have b := σ.cub _ (β T x) (β T y) (β T u) z J hJ
    simp only [← map_mul, hβ] at b
    have b' : Z (x * y * u) * Z x * Z y * Z u = @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) *
        Z (x * y) * Z (x * u) * Z (y * u) := by
      simp only [hZ]; exact b
    have v : ∀ t, Z t = W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := fun t => (hZ t).trans (vs T z J' J hJ' hJ W hW t)
    generalize @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) = C
      at a b'
    simp only [v, MonObj.mul_comp] at b'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.1 (x ≫ i')
    have b := hσ _ (β T x) z J hJ
    rw [← map_inv, hβ] at b
    have b' : W (x⁻¹ ≫ i') * (W 1)⁻¹ * val s (x⁻¹).left z J' =
        val P.sym ((x ≫ i').left ≫ F) z J * (W (x ≫ i') * (W 1)⁻¹ * val s x.left z J') := by
      rw [← vs T z J' J hJ' hJ W hW, ← vs T z J' J hJ' hJ W hW]; exact b
    rw [GrpObj.inv_comp] at b'
    show val s _ z J' = _ * val s _ z J'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''

theorem nonempty_biTriv (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (i : splitTorus _ X ⟶ G)
    (hi : IsMonHom i) : Nonempty (BiTriv P.c i) := by
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let f := red (IsLocalRing.maximalIdeal A)
  have hF := isGrpPullback_pullback G f
  have : Smooth ((Over.pullback f).obj G).hom := by show Smooth (pullback.snd G.hom f); infer_instance
  have : GeometricallyConnected ((Over.pullback f).obj G).hom := by
    show GeometricallyConnected (pullback.snd G.hom f); infer_instance
  have : ConnectedSpace (Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A))) :=
    SplitTorus.connectedSpace_of_isLocalRing _
  letI : ConnectedSpace ((Over.pullback f).obj G).left :=
    (GroupConn.connectedSpace_group _ ((Over.pullback f).obj G)).1
  obtain ⟨i₀, h₀, -⟩ := existsUnique_torusCompat (G' := (Over.pullback f).obj G) hF.1 i
  obtain ⟨_, _, _, _, _, _, _, hP⟩ := exists_isCPMap P (toBase_mul hF hF.1.w) _ (pull_isLB P.L.isLB _) _
    (pullIso_isGen P.L.isLB _)
  exact T.nonempty_biTriv_of_nonempty_biTriv_reduction A _ hA X G _ _ _ hF P _ _ hP i i₀ hi (h₀.isMonHom hF) h₀
    (BiextTriv.main _ X _ _ _ i₀ (h₀.isMonHom hF))

theorem nonempty_desc (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (Q : TQ G X)
    (h : ∃ σ : CubTriv P.c Q.i, σ.Even) : Nonempty (Q.Desc P) := by
  have : ConnectedSpace (Spec (CommRingCat.of A)) := SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ G).1
  exact UU.nonempty_desc _ X G Q P (nonempty_biTriv A hA G P Q.i Q.i_hom) h

theorem exists_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    {P : CP G} {P' : CP G'} {hw} {w} (hP : IsCPMap P' P (Spec.map (CommRingCat.ofHom φ)) F hw w) (Q' : TQ G' X)
    (h : ∃ σ : CubTriv P'.c Q'.i, σ.Even) :
    ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i ∧ ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hJ : RingHom.ker φ ≠ ⊤ := RingHom.ker_ne_top φ
  have hN : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hJ) n).trans hn.le)⟩
  let e := (RingHom.quotientKerEquivOfSurjective hφ).symm
  let g : Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) ⟶ Spec (CommRingCat.of A') := Spec.map e.toCommRingCatIso.hom
  have hg : g ≫ Spec.map (CommRingCat.ofHom φ) = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    exact (RingHom.quotientKerEquivOfSurjective hφ).symm_apply_eq.2 rfl
  have hG := isGrpPullback_pullback G' g
  have hF₀ := (hG.comp hF).congr hg rfl
  obtain ⟨Q₀, h₀⟩ := exists_tq_baseChange _ _ g X G' _ _ hG Q'
  obtain ⟨Q, hQ⟩ := TorusQuotLift.main A _ hN X G _ _ hF₀ Q₀
  refine ⟨Q, ?_, ?_⟩
  · have : IsIso (SplitTorus.bcMap g X) := (SplitTorus.isGrpPullback_bcMap g X).1.isIso_fst_of_isIso
    rw [torusCompat_iff] at h₀ hQ ⊢
    rw [← cancel_epi (SplitTorus.bcMap g X), ← Category.assoc, ← bcMap_comp, hg, hQ, ← Category.assoc, ← h₀,
      Category.assoc]
  · obtain ⟨_, _, _, _, _, _, _, hP₀⟩ := exists_isCPMap P' (toBase_mul hG hG.1.w) _ (pull_isLB P'.L.isLB _) _
      (pullIso_isGen P'.L.isLB _)
    obtain ⟨_, -, h₁⟩ := hP.exists_comp hP₀ (hG.comp hF).1.w
    obtain ⟨_, h₂⟩ := exists_congr h₁ hg rfl hF₀.1.w
    obtain ⟨σ, hσ⟩ := h
    have := Q₀.i_hom
    exact T.exists_even_cubicalTrivialisation_lift_nilpotent A _ hN hJ X G _ _ _ hF₀ P _ _ h₂ Q.i Q₀.i Q.i_hom Q₀.i_hom hQ
      (nonempty_biTriv A hA G P Q.i Q.i_hom) (exists_even_pull hP₀ h₀ σ hσ)

theorem exists_transition {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {P : CP G} {P' : CP G'} {hw} {w}
    (hP : IsCPMap P' P f F hw w) {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P)
    (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨β, hq, hβ⟩ := TQ.exists_isGrpPullback _ _ f X G G' F hF Q Q' h
  obtain ⟨_, -, h₁⟩ := D.map.exists_comp hP (by rw [Category.assoc, Over.w, Category.comp_id, hw])
  obtain ⟨_, h₂⟩ := exists_congr h₁ (Category.comp_id f) hq.symm (by
    rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w])
  exact ⟨β, ⟨hβ, isCPMap_descends _ _ f X G' Q' P' D' Q.B D.M β hβ.1.w _ _ (toBase_mul hβ _) h₂⟩, hq⟩

end GlobalTheory.UU.TowerEx
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddTensor

theorem full_left_support : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S), (2 : F) ≠ 0 → ∀ (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∀ π : EA P p 2 →ₗ[F] EA P p 2, TensorProduct.map π (LinearMap.id : EA P p 2 →ₗ[F] EA P p 2) (∑ i, TensorProduct.tmul F (t i) (t' i)) = 0 → π = 0 := by
  intro h1 h2 S _ P F _ _ p h2F th n t t' hadd hth
  choose Φ hΦ hΦu _ using GlobalTheory.ThetaLin.main S P F p 2
  refine GlobalTheory.eigenTensor_full_left_support F (EA P p 2) (EA P p 2)
    {θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p) // θ.pt ^ 2 = 1}
    (fun θ => (Φ θ.1 : EA P p 2 →ₗ[F] EA P p 2)) (fun θ => Φ θ.1) ?_ _
    (GlobalTheory.T.additionFormula_tensor_ne_zero S P F p th n t t' hadd hth) ?_
  · intro U hU
    refine (GlobalTheory.T.abelian_sections_irreducible_theta_group h1 h2 S P F p 2 (by exact_mod_cast h2F)).2 U ?_
    intro θ hθ v v' hvv' hv
    have e : v' = Φ θ v := hΦu θ v.sec v'.sec hvv'
    rw [e]
    exact hU ⟨θ, hθ⟩ v hv
  · intro θ
    obtain ⟨r, hr⟩ := GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two h1.globalFns S P F p th n t t' (fun i => Φ θ.1 (t i)) (fun i => Φ θ.1 (t' i))
      hadd θ.1 θ.2 (fun i => ⟨hΦ θ.1 (t i), hΦ θ.1 (t' i)⟩)
    refine ⟨r, Eq.trans ?_ hr⟩

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.map_tmul _ _ _ _

end GlobalTheory.AddTensor
end
