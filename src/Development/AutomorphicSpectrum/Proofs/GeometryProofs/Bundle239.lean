module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle231
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle235
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle145
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicPointOverNumberField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle135
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle136
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle224
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle236
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle220
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle141
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle237
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ToricQuot

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem exists_denominator {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (δ : X →+ K) :
    ∃ (a : O) (δ' : X →+ O), a ≠ 0 ∧ (algebraMap O K).toAddMonoidHom.comp δ' = algebraMap O K a • δ := by
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (fun i => δ (b i))
  choose g hg using ha
  refine ⟨a, (b.constr ℤ g).toAddMonoidHom, nonZeroDivisors.coe_ne_zero a, ?_⟩
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun i => ?_
  have := hg i
  simp only [Algebra.smul_def] at this
  simp [this, Algebra.smul_def]

theorem lattice_step {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {E E' T T' : Type} [AddCommGroup E] [Module O E] [AddCommGroup E'] [Module O E'] [Module.Projective O E']
    [AddCommGroup T] [Module K T] [Module O T] [IsScalarTower O K T]
    [AddCommGroup T'] [Module K T'] [Module O T'] [IsScalarTower O K T']
    (j : E →ₗ[O] T) (j' : E' →ₗ[O] T') (hj : IsBaseChange K j) (hj' : IsBaseChange K j')
    (I : (X →+ K) →ₗ[K] T) (A : T →ₗ[K] T') (hex : ∀ t, A t = 0 ↔ ∃ δ, I δ = t) (hA : Function.Surjective A)
    (io : (X →+ O) →ₗ[O] E) (f : E →ₗ[O] E')
    (hio : ∀ δ, j (io δ) = I ((algebraMap O K).toAddMonoidHom.comp δ)) (hf : ∀ e, j' (f e) = A (j e))
    (hsat : ∀ (a : O) (y : E), a ≠ 0 → a • y ∈ LinearMap.range io → y ∈ LinearMap.range io) :
    LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  have : IsLocalizedModule (nonZeroDivisors O) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j).2 hj
  have : IsLocalizedModule (nonZeroDivisors O) j' :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j').2 hj'
  have hinj : Function.Injective j' := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j') hxy
    exact smul_right_injective E' (nonZeroDivisors.coe_ne_zero c) hc
  refine ⟨le_antisymm ?_ ?_, fun e' => ?_⟩
  · intro e he
    have h0 : A (j e) = 0 := by rw [← hf, show f e = 0 from he, map_zero]
    obtain ⟨δ, hδ⟩ := (hex _).1 h0
    obtain ⟨a, δ', ha, hδ'⟩ := exists_denominator (O := O) δ
    have h1 : j (a • e) = j (io δ') := by
      rw [hio, hδ', map_smul, map_smul, hδ, algebraMap_smul]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j) h1
    refine hsat a e ha (hsat c _ (nonZeroDivisors.coe_ne_zero c) ⟨(c : O) • δ', ?_⟩)
    rw [map_smul]
    exact hc.symm
  · rintro _ ⟨δ, rfl⟩
    apply hinj
    rw [hf, hio, map_zero]
    exact (hex _).2 ⟨_, rfl⟩
  · obtain ⟨t, ht⟩ := hA (j' e')
    obtain ⟨⟨e, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) j t
    refine ⟨s, e, nonZeroDivisors.coe_ne_zero s, hinj ?_⟩
    have hs' : (s : O) • t = j e := hs
    rw [hf, ← hs', map_smul j', ← ht, ← algebraMap_smul K (s : O) t, map_smul, algebraMap_smul]

theorem exists_model_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S}
    (h : x = y) {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∃ M' : LieModel G y E, ∀ e, (M'.pt e).left = (M.pt e).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_fibre_model {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (G₁ : Over (Sp R')) [GrpObj G₁] (φ : G₁.left ⟶ G.left)
    (h : IsGrpPullback G₁ G (spMap (algebraMap R R')) φ) {V : Type} [AddCommGroup V] [Module R V]
    (M : LieModel G (𝟙 _) V) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T)
      (M₁ : LieModel G₁ (𝟙 _) T) (j : V →ₗ[R] T),
      (∀ e, ((M₁.pt (j e)).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  obtain ⟨T, iT, mT, ⟨M'⟩⟩ := lieModel_exists _ G R' (spMap (algebraMap R R') ≫ 𝟙 _)
  letI mR : Module R T := Module.compHom T (algebraMap R R')
  have hsm : ∀ (a : R) (t : T), a • t = algebraMap R R' a • t := fun _ _ => rfl
  have tower : IsScalarTower R R' T :=
    ⟨fun a b t => by rw [Algebra.smul_def, hsm, mul_smul]⟩
  let c := algebraMap R R'
  have halg : (dualMap c).comp (algebraMap R (DualNumber R)) =
      (algebraMap R' (DualNumber R')).comp c := by
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
    all_goals simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hfst : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  have hscale (r : R) : (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    all_goals simp [dualMap, epsMul, mul_comm]
  let base : epsAt (spMap c ≫ 𝟙 (Sp R)) ⟶ epsAt (𝟙 (Sp R)) :=
    Over.homMk (spMap (dualMap c)) (by
      change spMap (dualMap c) ≫ Spec.map _ ≫ 𝟙 (Sp R) = Spec.map _ ≫ spMap c ≫ 𝟙 (Sp R)
      simp only [spMap]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg])
  have htan (v : epsAt (𝟙 (Sp R)) ⟶ G) (hv : IsTanAt G (𝟙 _) v) :
      IsTanAt G (spMap c ≫ 𝟙 _) (base ≫ v) := by
    have h1 : (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ 𝟙 (Sp R)) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := MonObj.comp_one _
    have h2 : spMap c ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = (1 : Over.mk (spMap c ≫ 𝟙 (Sp R)) ⟶ G).left := by
      rw [← h1]; rfl
    unfold IsTanAt at hv ⊢
    rw [← h2, ← hv]
    change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hfst]
  have ex : ∀ e, ∃ t, M'.pt t = base ≫ M.pt e :=
    fun e => M'.onto _ (htan _ (M.tan e))
  choose f hf using ex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap c) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : V →ₗ[R] T :=
    { toFun := f
      map_add' := fun a b => M'.inj (by rw [M'.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, hsm, M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hscale])) }
  have hl : ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    change (M'.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf]
    exact Category.comp_id _
  obtain ⟨M'', h''⟩ := exists_model_of_eq (y := 𝟙 (Sp R') ≫ spMap (algebraMap R R'))
    (by rw [Category.comp_id, Category.id_comp]) M'
  obtain ⟨M₁, h₁⟩ := (LiePull.lieModel_pullback _ _ G G₁ _ φ h R' (𝟙 _) T).1 M''
  refine ⟨T, iT, mT, mR, tower, M₁, j, fun e => ?_, GlobalTheory.T.lie_model_isBaseChange _ G R R' _ V T M M' j hl⟩
  have := hl e
  rw [h₁, h'', ← this]
  exact (Category.comp_id _).symm

theorem lifts_unique {R R' : Type} [CommRing R] [CommRing R'] {c : R →+* R'} {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] {φ : G₁.left ⟶ G.left} (h : IsGrpPullback G₁ G (spMap c) φ)
    {V : Type} [AddCommGroup V] [Module R V] {M : LieModel G (𝟙 _) V} {e : V} {v w : epsAt (𝟙 (Sp R')) ⟶ G₁}
    (hv : (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left)) (hw : (w.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left)) : v = w := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext (hv.trans hw.symm) ?_
  rw [Over.w v, Over.w w]

theorem lie_quot_full : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (τ : TorusExtension GK) (φ : GK.left ⟶ G.left) (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback τ.B G' (spMap (algebraMap O K)) φ' → ∀ (MT : LieModel (splitTorus (Sp K) τ.X) (𝟙 _) (τ.X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ (io : (τ.X →+ O) →ₗ[O] E) (f : E →ₗ[O] E'), (∀ δ, ((MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt (io δ)).left)) ∧ (∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M'.pt (f e)).left)) ∧ Function.Injective io ∧ LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  intro O K _ _ _ _ _ G G' _ _ GK _ τ φ φ'
  letI := τ.addCommGroup
  letI := τ.grpB
  intro hG hG' hφ hφ' MT hMT E _ _ E' _ _ M M'
  have := τ.free
  have := τ.finite
  have := τ.q_hom
  have := τ.i_hom
  have := hG.comm
  have := hG.smooth
  have := hG'.comm
  have := hG'.smooth
  have : Mono τ.i := ⟨fun a b hab => τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  obtain ⟨io, hio, hinj, hsat⟩ := GlobalTheory.T.semiabelian_torus_lie_sub O K G GK φ hG hφ τ.X τ.i MT hMT E M
  obtain ⟨f, hf⟩ := GlobalTheory.T.semiabelian_hom_lie_extends O K G G' GK τ.B φ φ' hG hG' hφ hφ' τ.q E E' M M'
  have := (GlobalTheory.T.lie_model_finite_projective _ G' O _ E' M').2
  obtain ⟨T, _, _, _, _, MK, j, hj, hbc⟩ := exists_fibre_model G GK φ hφ M
  obtain ⟨T', _, _, _, _, MK', j', hj', hbc'⟩ := exists_fibre_model G' τ.B φ' hφ' M'
  obtain ⟨I, hI, -⟩ := lieModel_exists_unique_diff _ _ GK K _ _ T MT MK τ.i
  obtain ⟨A, hA, -⟩ := lieModel_exists_unique_diff _ GK τ.B K _ T T' MK MK' τ.q
  have hex := GlobalTheory.T.torus_extension_tangent_exact K GK τ K (RingHom.id K)
  have hid : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  rw [hid] at hex
  refine ⟨io, f, hio, hf, hinj, lattice_step j j' hbc hbc' I A (fun t => ?_) (fun t' => ?_) io f
    (fun δ => ?_) (fun e => ?_) hsat⟩
  · have h1 : A t = 0 ↔ MK.pt t ≫ τ.q = 1 := by
      rw [← hA, ← MK'.pt_zero]
      exact MK'.inj.eq_iff.symm
    rw [h1, hex.1 _ (MK.tan t)]
    constructor
    · rintro ⟨w, hw, e⟩
      obtain ⟨δ, rfl⟩ := MT.onto w hw
      exact ⟨δ, MK.inj (by rw [hI, e])⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨_, MT.tan δ, (hI δ).symm⟩
  · obtain ⟨v, hv, e⟩ := hex.2 _ (MK'.tan t')
    obtain ⟨t, rfl⟩ := MK.onto v hv
    exact ⟨t, MK'.inj (by rw [hA, e])⟩
  · apply MK.inj
    rw [hI]
    exact lifts_unique hφ (hj _) (hio δ)
  · apply MK'.inj
    rw [hA]
    exact lifts_unique hφ' (hj' _) (hf e _ (hj e))

end GlobalTheory.CompanionTheory.Ar.ToricQuot
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

instance locallyOfFiniteType_spInt (L : Type) [Field L] [NumberField L] :
    LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.Finite.finiteType (RingHom.finite_algebraMap.2 inferInstance)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem isClosed_of_maximal (G : Over (Sp (𝓞 L))) [LocallyOfFiniteType G.hom] {W : G.left.Opens} (hW : IsAffineOpen W)
    (m : Ideal Γ(G.left, W)) [hm : m.IsMaximal] :
    IsClosed ({hW.fromSpec (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(G.left, W))} : Set G.left) := by
  have := (GlobalTheory.jacobson_closedPoints_tools_int G.left (G.hom ≫ spMap (algebraMap ℤ (𝓞 L)))).1
  refine isClosed_singleton_of_isLocallyClosed_singleton ?_
  have h1 : IsClosed ({(⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(G.left, W))} : Set (PrimeSpectrum Γ(G.left, W))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have h2 := h1.isLocallyClosed.image (f := hW.fromSpec) hW.fromSpec.isOpenEmbedding.isInducing
    hW.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
  convert h2 using 1
  exact Set.image_singleton.symm

instance isDominant_spMap_field {K C : Type} [Field K] [Field C] (e : K →+* C) : IsDominant (spMap e) :=
  ⟨Function.Surjective.denseRange fun z => ⟨default, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩

theorem point_bound (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (d : 𝓞 L) (hd : d ≠ 0)
    (Hy : ∀ (K : Type) [Field K] [NumberField K] (c : 𝓞 L →+* K) (y : Over.mk (spMap c) ⟶ D.t.G) (N : ℕ) (T : K),
      TorsVal D.t.PP s y N T → IsIntegral ℤ (T / c d ^ (N ^ 2)))
    (i : D.t.PP.L.ι) (W : D.t.G.left.Opens) (hW : IsAffineOpen W)
    (hWU : W ≤ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i))
    (m : Ideal Γ(D.t.G.left, W)) (hm : m.IsMaximal) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : Γ(D.t.G.left, W) →+* O),
      (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧ Function.Injective (ψ.comp (sc D.t.G.hom W)) ∧
        ∃ c, ψ ((D.t.G.left.presheaf.map (homOfLE hWU).op).hom (s.f fun _ => i)) = ψ (sc D.t.G.hom W d) * c := by
  have hS := D.t.semi
  have := hS.smooth
  have := hS.separated
  let w : D.t.G.left := hW.fromSpec (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(D.t.G.left, W))
  have hwc : IsClosed ({w} : Set D.t.G.left) := isClosed_of_maximal D.t.G hW m
  have hwW : w ∈ W := by
    have : w ∈ Set.range hW.fromSpec := ⟨_, rfl⟩
    rwa [hW.range_fromSpec] at this
  have hmem : ∀ b : Γ(D.t.G.left, W), w ∈ D.t.G.left.basicOpen b ↔ b ∉ m := fun b => by
    have h1 : w ∈ D.t.G.left.basicOpen b ↔ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(D.t.G.left, W)) ∈ hW.fromSpec ⁻¹ᵁ D.t.G.left.basicOpen b := Iff.rfl
    rw [h1, hW.fromSpec_preimage_basicOpen]
    rfl
  obtain ⟨N, O, ρ, y, hN, hyN, hyw, hρ⟩ := GlobalTheory.T.torsion_point_valuation_ring_lift L D.t.G hS w hwc
  let C := AlgebraicClosure L
  let yO : Sp O ⟶ D.t.G.left := y.left
  have hyO : yO ≫ D.t.G.hom = spMap ρ := Over.w y
  have hyw' : yO (IsLocalRing.closedPoint O) = w := hyw
  have htop : ⊤ ≤ yO ⁻¹ᵁ W := top_le_of_closedPoint _ (by change yO _ ∈ W; rw [hyw']; exact hwW)
  have hi : ⊤ ≤ yO ⁻¹ᵁ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i) :=
    fun x hx => hWU (htop hx)
  haveI : Algebra.IsAlgebraic ℚ C := Algebra.IsAlgebraic.trans ℚ L C
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 Subtype.val_injective
  obtain ⟨K, _, _, e, x', hx⟩ := GlobalTheory.T.algebraic_point_over_number_field C D.t.G.left (D.t.G.hom ≫ spMap (algebraMap ℤ (𝓞 L)))
    (spMap (algebraMap O C) ≫ yO)
  obtain ⟨c', hc⟩ := Spec.map_surjective (x' ≫ D.t.G.hom)
  let c : 𝓞 L →+* K := c'.hom
  have hc' : spMap c = x' ≫ D.t.G.hom := hc
  let yK : Over.mk (spMap c) ⟶ D.t.G := Over.homMk x' hc'.symm
  have hb : spMap e ≫ spMap c = spMap (algebraMap O C) ≫ spMap ρ := by
    rw [hc', ← Category.assoc, hx, Category.assoc, hyO]
  let yC : Over.mk (spMap e ≫ spMap c) ⟶ D.t.G := Over.homMk (spMap e ≫ x') (by
    change (spMap e ≫ x') ≫ D.t.G.hom = spMap e ≫ spMap c
    rw [hc', Category.assoc])
  have hyC : yC.left = spMap (algebraMap O C) ≫ y.left := hx
  let v : Over.mk (spMap e ≫ spMap c) ⟶ Over.mk (spMap ρ) := Over.homMk (spMap (algebraMap O C)) hb.symm
  have hvy : v ≫ y = yC := Over.OverMorphism.ext hyC.symm
  have hyCN : yC ^ N = 1 := by rw [← hvy, ← MonObj.comp_pow, hyN, MonObj.comp_one]
  let u : Over.mk (spMap e ≫ spMap c) ⟶ Over.mk (spMap c) := Over.homMk (spMap e) rfl
  have huy : u ≫ yK = yC := Over.OverMorphism.ext rfl
  have hyKN : yK ^ N = 1 := by
    have h1 : u ≫ yK ^ N = u ≫ 1 := by rw [MonObj.comp_pow, huy, hyCN, MonObj.comp_one]
    have h2 : spMap e ≫ (yK ^ N).left = spMap e ≫ (1 : Over.mk (spMap c) ⟶ D.t.G).left := congrArg (·.left) h1
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp K) D.t.G.hom ((Over.w _).trans (Over.w _).symm) (spMap e) h2)
  obtain ⟨⟨T, hT, -⟩, hmap⟩ := GlobalTheory.T.torsion_value_unique_base_change E H L D n s K (spMap c) yK N hN hyKN
  have hC := hmap C e yC T rfl hT
  have hI := Hy K c yK N T hT
  obtain ⟨ε, hε⟩ := GlobalTheory.T.torsion_point_line_bundle_unit E H L D n s O C ρ y N hN hyN i hi _ hb yC hyC (e T) hC
  have hρi : Function.Injective ρ := fun a b hab => by
    have h1 := congrArg (Subtype.val) hab
    have h2 : algebraMap L C (a : L) = algebraMap L C (b : L) := by
      rw [← hρ, ← hρ]; exact h1
    exact RingOfIntegers.ext ((algebraMap L C).injective h2)
  let ψ : Γ(D.t.G.left, W) →+* O := valR yO W htop
  have hψd : ψ (sc D.t.G.hom W d) = ρ d := valR_sc yO D.t.G.hom ρ hyO W htop d
  have hψf : ψ ((D.t.G.left.presheaf.map (homOfLE hWU).op).hom (s.f fun _ => i)) =
      valR yO _ hi (s.f fun _ => i) := valR_res yO hWU htop hi _
  refine ⟨O, inferInstance, inferInstance, ψ, fun b hb' => ?_, fun b hb' hu => ?_, ?_, ?_⟩
  · exact (valR_isUnit_iff yO W htop b).2 (by rw [hyw']; exact (hmem b).2 hb')
  · have := (valR_isUnit_iff yO W htop b).1 hu
    rw [hyw'] at this
    exact (hmem b).1 this hb'
  · have : ψ.comp (sc D.t.G.hom W) = ρ := RingHom.ext fun a => valR_sc yO D.t.G.hom ρ hyO W htop a
    rw [this]; exact hρi
  · rw [hψf, hψd]
    set θ : O := valR yO _ hi (s.f fun _ => i) with hθ
    have he : e (c d) = algebraMap O C (ρ d) := by
      have h1 : Spec.map (CommRingCat.ofHom (e.comp c)) = Spec.map (CommRingCat.ofHom ((algebraMap O C).comp ρ)) := by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
        exact hb
      have h2 : e.comp c = (algebraMap O C).comp ρ := by
        have := Spec.map_injective h1
        exact congrArg CommRingCat.Hom.hom this
      exact congrArg (· d) h2
    have hr0 : algebraMap O C (ρ d) ≠ 0 := by
      intro h0
      have : ρ d = 0 := (FaithfulSMul.algebraMap_injective O C) (by rw [h0, map_zero])
      exact hd (hρi (by rw [this, map_zero]))
    have hI' : IsIntegral ℤ (e T / e (c d) ^ (N ^ 2)) := by
      have h1 := hI.map e.toIntAlgHom
      have h2 : e.toIntAlgHom (T / c d ^ (N ^ 2)) = e T / e (c d) ^ (N ^ 2) := by
        change e _ = _
        simp [map_div₀, map_pow]
      rwa [h2] at h1
    rw [he, hε] at hI'
    let z : C := algebraMap O C θ / algebraMap O C (ρ d)
    have hz1 : IsIntegral O (z ^ (N ^ 2) * algebraMap O C ε) := by
      have h2 : algebraMap O C (θ ^ (N ^ 2) * ε) / algebraMap O C (ρ d) ^ (N ^ 2) = z ^ (N ^ 2) * algebraMap O C ε := by
        simp only [z, map_mul, map_pow, div_pow]; ring
      rw [h2] at hI'
      exact hI'.tower_top
    have hz2 : IsIntegral O (z ^ (N ^ 2)) := by
      have h3 : z ^ (N ^ 2) = (z ^ (N ^ 2) * algebraMap O C ε) * algebraMap O C (ε⁻¹ : Oˣ) := by
        rw [_root_.mul_assoc, ← map_mul]; simp
      rw [h3]
      exact hz1.mul isIntegral_algebraMap
    have hz3 : IsIntegral O z := IsIntegral.of_pow (by positivity) hz2
    obtain ⟨c₀, hc₀⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz3
    refine ⟨c₀, (FaithfulSMul.algebraMap_injective O C) ?_⟩
    rw [map_mul, hc₀, mul_comm]
    exact (div_mul_cancel₀ _ hr0).symm

end GlobalTheory.CompanionTheory.Ar.Sl.Reg

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

theorem section_dvd_of_torsVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (d : 𝓞 L), d ≠ 0 → (∀ (K : Type) [Field K] [NumberField K] (c : 𝓞 L →+* K) (y : Over.mk (spMap c) ⟶ D.t.G) (N : ℕ) (T : K), TorsVal D.t.PP s y N T → IsIntegral ℤ (T / c d ^ (N ^ 2))) → ∃ s' : Out.H0 D.t.PP.L n, ∀ j, s.f j = constFn D.t.G.hom _ d * s'.f j := by
  intro E _ _ _ H L _ _ D n s d hd Hy
  have hS := D.t.semi
  obtain ⟨hInt, hring⟩ := GlobalTheory.T.group_scheme_integral_noetherian L D.t.G hS
  haveI := hInt
  have hδ : sc D.t.G.hom ⊤ d ≠ 0 := by
    intro h0
    let e : Sp (𝓞 L) ⟶ D.t.G.left := η[D.t.G].left
    have he : e ≫ D.t.G.hom = spMap (RingHom.id (𝓞 L)) := by
      have : e ≫ D.t.G.hom = 𝟙 _ := Over.w η[D.t.G]
      rw [this]; simp [spMap]
    have := valR_sc e D.t.G.hom (RingHom.id _) he ⊤ (fun _ _ => trivial) d
    rw [h0, map_zero] at this
    exact hd this.symm
  obtain ⟨s', hs'⟩ := GlobalTheory.T.line_bundle_section_divisible D.t.G.left (𝓞 L) D.t.G.hom _ s d hδ (by
    intro j W hWU hW
    obtain ⟨i₀, rfl⟩ : ∃ i₀, j = fun _ => i₀ := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    by_cases hne : (W : Set D.t.G.left).Nonempty
    · obtain ⟨hNo, hft, hp⟩ := hring W hW
      haveI : Nonempty W := hne.to_subtype
      exact GlobalTheory.T.prime_ideal_extension_local_domain (𝓞 L) Γ(D.t.G.left, W) (sc D.t.G.hom W) hft hp _ d hd fun m hm =>
        point_bound D n s d hd Hy i₀ W hW hWU m hm
    · have hW0 : W = ⊥ := by
        ext x
        simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hne ⟨x, hx⟩
      subst hW0
      haveI : Subsingleton Γ(D.t.G.left, ⊥) := inferInstance
      exact ⟨0, Subsingleton.elim _ _⟩)
  exact ⟨s', hs'⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_bilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ P : Matrix (Fin d') (Fin d) k, Q.IsDiff g gB P → ∃ Z : Matrix (Fin d) (Fin d) k, ∀ a, bil (g.B.ad a) 1 1 + (rho g.B a).transpose * Z - Z * rho g.B (star a) = P.transpose * bil (gB.B.ad a) 1 1 * P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.torsion_embedding_geometric_points : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (T : Type) [CommGroup T] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ), 1 ≤ N → ∀ τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G), Function.Injective τ → (∀ t, τ t ^ N = 1) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (a : FractionRing R →+* Ω) (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) ⟶ G), g ^ N = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion <;> assumption)
end
