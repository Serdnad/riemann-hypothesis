module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.CongrOrbit

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {S : Type} [CommRing S]

theorem scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem exists_unit_of_generators {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul, mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

theorem frBor_of_eq [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) (hu : y'.u = y.u) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hx hu
  subst hx
  subst hu
  obtain ⟨u0, hu0⟩ := exists_unit_of_generators (x := y.x) y.s s' y.gen gen'
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
  choose b hb using hb
  have hu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  classical
  refine ⟨fun o => match o with
    | none => u0
    | some _ => 1, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩,
      𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · dsimp only
    rw [hu τ, hcomb]
    simp [Pi.single_apply]
  · intro i h
    simp only
    rw [← hu0 i]
    simp only [Scheme.Hom.appLE]
    have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
    rw [e]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

end Frames

theorem perFr_lact {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
      Formalism.L2.PjFree.perFr X x v τ i := by
  have hm : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := fun _ => rfl
  unfold Formalism.L2.PjFree.perFr
  simp only [hm, PerMove.emb_mulVec]
  split_ifs with h1 h2 h3 h4
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map τ.mapMatrix)
    rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  · rfl
  · rw [PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl

noncomputable def latAut {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) : Λ ≃ₗ[𝓞 E] Λ where
  toFun a := ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ a, (h _).1 a.2⟩
  invFun a := ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ a, (h _).2 (by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact a.2)⟩
  map_add' a b := Subtype.ext (Matrix.mulVec_add (γ : Matrix (Fin r) (Fin r) E) (a : Fin r → E) (b : Fin r → E))
  map_smul' s a := Subtype.ext (Matrix.mulVec_smul (γ : Matrix (Fin r) (Fin r) E) s (a : Fin r → E))
  left_inv a := Subtype.ext (by
    simp only
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
  right_inv a := Subtype.ext (by
    simp only
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])

end GlobalTheory.CongrOrbit

namespace GlobalTheory


open CongrOrbit in
theorem congr_lact_mem_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → l.A = 1 → ∀ k (γ : GL (Fin r) E), IsUStab (U.X k).Gm (U.X k).Λ γ → (∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (l.M : E) • y) → ∀ x ∈ (U.X k).dom, ∃ γ' ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  intro E _ _ _ H Dw l Xo c σ r U hU hA k γ hγ hM x hx
  obtain ⟨-, -, -, hfib, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  have hx' := dom_lact (U.X k) hx hγ
  obtain ⟨P, hP, hPer, hu, hd, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', hPer', hu', hd', -⟩ := hpt k ⟨_, hx'⟩
  let gam := (φ k).trans ((latAut (U.X k).Λ γ hγ.2).trans (φ k).symm)
  have hgam : ∀ a, (φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := by
    intro a
    simp only [gam, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨-, hpt, hex⟩ := FamRigid.ex_eq_of_level_group latMinkowski E H Dw l Xo _ g _ F (ik k) P P' gam 1
    hPer hPer' (fun a b => by
      have := hEF k (gam a) (gam b)
      rw [hgam, hgam, hγ.1, ← hEF] at this
      exact_mod_cast this)
    (fun a _ => by
      obtain ⟨y, hy, he⟩ := hM _ (φ k a).2
      refine ⟨(φ k).symm ⟨y, hy⟩, (φ k).injective (Subtype.ext ?_)⟩
      rw [hgam, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Submodule.coe_add, ← sub_eq_iff_eq_add', he,
        Nat.cast_smul_eq_nsmul]
      rfl)
    (fun a => ⟨gam a - a, by rw [hA, one_smul]; abel⟩)
    (fun a => by
      funext j
      rw [Matrix.one_mulVec, hP, hP', hgam]
      exact perFr_lact _ _ _ hγ.1 _ _ _)
  simp only [Matrix.one_mulVec] at hex
  obtain ⟨γ', hγ', b, hb, he⟩ := (hfib k k ⟨x, hx⟩ ⟨_, hx'⟩).1 (frBor_of_eq _ _
    (hu'.trans (hpt.symm.trans hu.symm)) (by
      funext τ i
      have h1 := hd' τ i
      simp only [hex] at h1
      exact VerticalDeriv.isDerivAt0_unique h1 (hd τ i)))
  exact ⟨γ', hγ', b, hb, eq_of_heq (Sigma.mk.inj he).2⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace SurjIsogeny

theorem eq_bot_of_comap_eq_bot {K R S : Type} [Field K] [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra K R] [Algebra K S] (φ : R →+* S)
    (hφ : φ.comp (algebraMap K R) = algebraMap K S) {g : ℕ}
    (hR : Algebra.trdeg K R = g) (hS : Algebra.trdeg K S = g) {p : Ideal S}
    (hp : p.comap φ = ⊥) : p = ⊥ := by
  algebraize [φ]
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq' hφ.symm
  have : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← hp]
    exact Ideal.comap_mono bot_le
  have h := trdeg_add_eq K R (A := S)
  rw [hR, hS] at h
  have h0 : Algebra.trdeg R S = 0 := by
    have h1 : Algebra.trdeg R S + g = 0 + g := by rw [add_comm, h, zero_add]
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).1 h1
  have halg := trdeg_eq_zero_iff.1 h0
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hx (halg.1 x) hp

theorem eq_genericPoint_iff {X : Scheme.{0}} [IsIntegral X] {R : CommRingCat.{0}} [IsDomain R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (p : Spec R) :
    j p = genericPoint X ↔ p.asIdeal = ⊥ := by
  rw [← genericPoint_eq_of_isOpenImmersion j, j.isOpenEmbedding.injective.eq_iff,
    genericPoint_eq_bot_of_affine]
  exact ⟨fun h => h ▸ rfl, fun h => PrimeSpectrum.ext h⟩

theorem eq_genericPoint_of_apply_eq {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (s : Y ⟶ Spec (CommRingCat.of K)) {g : ℕ}
    (hY : SmoothOfRelativeDimension g s) (hX : SmoothOfRelativeDimension g (f ≫ s)) {x : X}
    (hx : f x = genericPoint Y) : x = genericPoint X := by
  obtain ⟨R, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq (f x)
  obtain ⟨S, k, hk, ⟨p, rfl⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := f ⁻¹ᵁ j.opensRange) ⟨y, hy⟩
  have hr : Set.range (k ≫ f) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hsub ⟨z, rfl⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j (k ≫ f) hr)
  have hw : Spec.map φ ≫ j = k ≫ f := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := Spec.map_surjective (j ≫ s)
  have : Nonempty (Spec R) := ⟨y⟩
  have : Nonempty (Spec S) := ⟨p⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec S) := isIntegral_of_isOpenImmersion k
  have : IsDomain R := (affine_isIntegral_iff R).1 inferInstance
  have : IsDomain S := (affine_isIntegral_iff S).1 inferInstance
  letI : Algebra K R := α.hom.toAlgebra
  letI : Algebra K S := (α ≫ φ).hom.toAlgebra
  have hR := trdeg_eq_of_smoothOfRelativeDimension K Y s g hY R j hj hα.symm
  have hS := trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ s) g hX S k hk (by
    rw [← reassoc_of% hw, ← hα, ← Spec.map_comp]; rfl)
  rw [eq_genericPoint_iff]
  refine eq_bot_of_comap_eq_bot φ.hom rfl hR hS ?_
  refine (eq_genericPoint_iff j (Spec.map φ p)).1 ?_
  rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hx]

theorem isPullback_kernel_mul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Z A B : C} [GrpObj A] [GrpObj B] {i : Z ⟶ A} {ψ : A ⟶ B} [IsMonHom ψ]
    (hp : IsPullback i (toUnit Z) ψ η[B]) :
    IsPullback ((fst Z A ≫ i) * snd Z A) (snd Z A) ψ ψ := by
  have hi : i ≫ ψ = 1 := hp.w
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (hp.lift (s.fst * s.snd⁻¹) (toUnit _) ?_) s.snd) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel, Hom.one_def]
  · rw [MonObj.comp_mul, lift_fst_assoc, hp.lift_fst, lift_snd, inv_mul_cancel_right]
  · exact lift_snd _ _
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ (by rw [lift_snd, h2])
    refine hp.hom_ext ?_ (toUnit_unique _ _)
    rw [lift_fst, hp.lift_fst, ← h1, ← h2, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]

theorem locallyQuasiFinite_of_finite_fibre {S : Scheme.{0}} [Subsingleton S] {A B : Over S}
    [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left]
    [LocallyOfFiniteType ψ.left] [QuasiCompact ψ.left] (a : A.left)
    (h : (ψ.left ⁻¹' {ψ.left a}).Finite) : LocallyQuasiFinite ψ.left := by
  have hp : IsPullback (pullback.fst ψ η[B]) (toUnit _) ψ η[B] := by
    have := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit _)] at this
  generalize pullback.fst ψ η[B] = i at hp
  generalize pullback ψ η[B] = Z at i hp
  have hl := hp.map (Over.forget S)
  have hZ1 : LocallyOfFiniteType Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hl ‹_›
  have hZ2 : QuasiCompact Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @QuasiCompact) hl ‹_›
  have h1 : IsPullback ((fst Z A ≫ i) * snd Z A).left (pullback.snd Z.hom A.hom) ψ.left ψ.left :=
    (isPullback_kernel_mul hp).map (Over.forget S)
  let j := A.left.fromSpecResidueField a
  have h2 := IsPullback.of_hasPullback (pullback.snd Z.hom A.hom) j
  have h3 := h2.paste_horiz h1
  have h4 := h2.paste_horiz (IsPullback.of_hasPullback Z.hom A.hom)
  have hF : LocallyQuasiFinite (ψ.left.fiberToSpecResidueField (ψ.left a)) := by
    have : Finite (ψ.left.fiber (ψ.left a)) :=
      (ψ.left.fiberHomeo (ψ.left a)).toEquiv.finite_iff.2 h.to_subtype
    have : LocallyOfFiniteType (ψ.left.fiberToSpecResidueField (ψ.left a)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
    exact LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h3
  have h5 := h3.of_right' (IsPullback.of_hasPullback ψ.left
    (B.left.fromSpecResidueField (ψ.left a)))
  have h6 : LocallyQuasiFinite (pullback.snd (pullback.snd Z.hom A.hom) j) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h5 hF
  have h7 : LocallyQuasiFinite Z.hom :=
    Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h4
      ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩ hZ1 hZ2 h6
  exact Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h1 ‹_› ‹_› ‹_›
    inferInstance

end SurjIsogeny


open SurjIsogeny IsogenyModel in
theorem isogeny_of_surjective_of_dim_eq : Out.Laws → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (B : Over (Sp K)) [GrpObj B] (ψ : P.A ⟶ B), IsAbelianScheme B → SmoothOfRelativeDimension P.g B.hom → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 := by
  intro hL K _ P B _ ψ hB hg _ _
  have := hB.proper
  have := P.isAb.proper
  have := P.isAb.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom
    P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA : SmoothOfRelativeDimension P.g (ψ.left ≫ B.hom) := by rw [Over.w]; exact P.smoothDim
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hg hA (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main K Z hZ inferInstance
  obtain ⟨A, _, hA', q, _, _, _, _, hq⟩ := hL.quotient K P Z i ‹_› hm hZ inferInstance
  have := hA'.proper
  obtain ⟨e, -, he⟩ := exists_iso_of_same_kernel q ψ i hq hk
  refine ⟨hf, ?_, N, hN, fun T x hx => ?_⟩
  · have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [← he, Over.comp_left]
    infer_instance
  · have h1 : i ^ N = 1 := by
      rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
    rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem isogeny_of_surjective_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (ψ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 :=
  fun _ hL K _ _ P P' ψ hg => isogeny_of_surjective_of_dim_eq hL K P P'.A ψ P'.isAb
    (hg ▸ P'.smoothDim)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace TorsionKernelModel

theorem exists_kernel {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] [IsSeparated H.hom] (f : G ⟶ H)
    [IsMonHom f] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsPullback i (toUnit Z) f η[H] := by
  have hk : IsPullback (pullback.fst f η[H]) (toUnit _) f η[H] := by
    have := IsPullback.of_hasPullback f η[H]
    rwa [toUnit_unique (pullback.snd f η[H]) (toUnit _)] at this
  generalize pullback.fst f η[H] = i at hk
  generalize pullback f η[H] = Z at i hk
  have h₁ : IsClosedImmersion (η[H].left ≫ H.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[H].left := IsClosedImmersion.of_comp _ H.hom
  have h₃ : IsClosedImmersion i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂
  have hm : Mono i := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hi : i ≫ f = 1 := hk.w
  obtain ⟨_, hG⟩ := exists_grpObj_of_mono i
    (hk.lift η[G] (toUnit _) (by simp))
    (hk.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one, _root_.mul_one,
        Hom.one_def]))
    (hk.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))
    (hk.lift_fst _ _ _) ((hk.lift_fst _ _ _).trans (by rw [Hom.mul_def, lift_fst_comp_snd_comp]))
    ((hk.lift_fst _ _ _).trans (Hom.inv_def _))
  exact ⟨Z, _, i, hG, h₃, hk⟩

theorem isPullback_kernel_baseChange {S S' : Scheme.{0}} (j : S' ⟶ S) {Z G H : Over S} [GrpObj H]
    {i : Z ⟶ G} {f : G ⟶ H} (h : IsPullback i (toUnit Z) f η[H]) :
    IsPullback ((Over.pullback j).map i) (toUnit _) ((Over.pullback j).map f) η[(Over.pullback j).obj H] := by
  refine (h.map (Over.pullback j)).of_iso (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback j)).symm
    (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_
  simp [Functor.obj.η_def]

theorem isFinite_of_pow_eq_one {S : Scheme.{0}} {Z G : Over S} [GrpObj G] [IsSeparated G.hom] (i : Z ⟶ G)
    [IsClosedImmersion i.left] (n : ℕ) [hn : IsFinite (𝟙 G ^ n).left] (h : i ^ n = 1) : IsFinite Z.hom := by
  have h₁ : IsClosedImmersion (η[G].left ≫ G.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  have e₁ : i ≫ (𝟙 G ^ n) = toUnit Z ≫ η[G] := by
    rw [MonObj.comp_pow, Category.comp_id, h, Hom.one_def]
  have e₂ : i.left ≫ (𝟙 G ^ n).left = Z.hom ≫ η[G].left := by
    rw [← Over.comp_left, e₁]; simp
  let l : Z.left ⟶ pullback (𝟙 G ^ n).left η[G].left := pullback.lift i.left Z.hom e₂
  have h₃ : IsClosedImmersion (l ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]; infer_instance
  have h₄ : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.fst _ _)
  have e₃ : l ≫ pullback.snd _ _ = Z.hom := pullback.lift_snd _ _ _
  rw [← e₃]
  infer_instance

end TorsionKernelModel


open TorsionKernelModel in
theorem exists_abelianScheme_model_of_isogeny_dedekind :
    Out.Laws → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (A₀ B₀ : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] (φ : A₀.left ⟶ P.A.left) (ψ : A₀ ⟶ B₀) (n : ℕ), IsGrpPullback A₀ P.A (spMap (algebraMap R K)) φ → IsAbelianScheme B₀ → IsMonHom ψ → IsFinite ψ.left → Flat ψ.left → Surjective ψ.left → 1 ≤ n → (∀ (T : Over (Sp K)) (x : T ⟶ A₀), x ≫ ψ = 1 → x ^ n = 1) →
  ∃ (B : Over (Sp R)) (_ : GrpObj B) (φB : B₀.left ⟶ B.left) (Ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsGrpPullback B₀ B (spMap (algebraMap R K)) φB ∧ IsMonHom Ψ ∧ IsFinite Ψ.left ∧ Flat Ψ.left ∧ Surjective Ψ.left ∧ ψ.left ≫ φB = φ ≫ Ψ.left := by
  intro hL R K _ _ _ _ _ P A₀ B₀ _ _ φ ψ n hφ hB _ _ _ _ hn hker
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := P.isAb.proper
  have := hB.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback P.A _) hφ
  have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
  obtain ⟨Z, _, i, _, hi, hZ⟩ := exists_kernel (a.hom ≫ ψ)
  obtain ⟨Ga, io, e, _, _, he⟩ := IsogenyModel.exists_flat_closure R K P.A Z i hi
  obtain ⟨_, _, -⟩ := exists_grpObj_of_flat_closed _ P.A Ga io Z i e he
  have hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀] := by
    rw [← he, Category.assoc, hZ.w, comp_toUnit_assoc]
  have hpow : io ^ n = 1 := by
    apply ExtUnique.pullback_map_injective (spMap (algebraMap R K))
    have h₁ := hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by
      rw [Category.assoc, hkill, Hom.one_def])
    rw [← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono] at h₁
    exact (map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans
      (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)
  have := (hL.mulN _ P n hn).1
  have hfin : IsFinite Ga.hom := isFinite_of_pow_eq_one io n hpow
  have hm : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  obtain ⟨B, _, hab, q, _, hq₁, hq₂, hq₃, hq⟩ := hL.quotient R P Ga io ‹_› hm hfin ‹_›
  have hq' := isPullback_kernel_baseChange (spMap (algebraMap R K)) hq
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨β, _, hβ⟩ := flatQuotient_iso_of_same_kernel _ _ _ _ _ _
    ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i
    inferInstance inferInstance
    (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂)
    (MorphismProperty.overPullbackMap (P := @Surjective) _ q hq₃)
    (MorphismProperty.overPullbackMap (P := @QuasiCompact) _ q hqc) hq' inferInstance inferInstance
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hZ
    (by rw [← e.inv_hom_id_assoc i, he, Category.assoc, hq'.w, comp_toUnit_assoc]) hkill
  refine ⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), q, hab,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl,
    ‹_›, hq₁, hq₂, hq₃, ?_⟩
  rw [← cancel_epi a.hom.left, ← Category.assoc a.hom.left φ, ha', ← ExtUnique.pullback_map_left_fst, ← hβ]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory
end
