module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle531
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle188
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle210
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle209
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle202
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReduction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

theorem endChar_exists_of_isMonHom (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hB : GlobalTheory.Mum.Base R)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (_hG : IsSemiAbelian G) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (hfm : IsMonHom f) :
    ∃ m, EndChar U f m := by
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map f).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G.hom (spMap (residue R)) ≫ f.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map f) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp hp f _ e
  obtain ⟨m, hm⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp ≫ (Over.pullback (spMap (residue R))).map f) inferInstance
  refine ⟨m, fun κ _ a ha G₀ _ φ h f₀ hf => ?_⟩
  let σ : ResidueField R →+* κ := Ideal.Quotient.lift _ a fun x hx => ha x (by simpa using hx)
  have ea : a = σ.comp (residue R) := RingHom.ext fun _ => rfl
  have es : spMap a = spMap σ ≫ spMap (residue R) := by rw [← Spec.map_comp]; rfl
  let ψ : G₀.left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift φ (G₀.hom ≫ spMap σ) (by rw [Category.assoc, ← es, h.1.w])
  have hψ : ψ ≫ pullback.fst G.hom (spMap (residue R)) = φ := pullback.lift_fst _ _ _
  have k : IsGrpPullback G₀ ((Over.pullback (spMap (residue R))).obj G) (spMap σ) ψ :=
    hp.cancel (h.congr es hψ.symm) (pullback.lift_snd _ _ _)
  have e₀ : f₀.left ≫ ψ = ψ ≫ ((Over.pullback (spMap (residue R))).map f).left := hp.1.hom_ext
    (by rw [Category.assoc, hψ, hf, Category.assoc, e, ← Category.assoc, hψ])
    (by rw [Category.assoc, k.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, k.1.w])
  rw [← GlobalTheory.TorusPart.pullTorus_gtTorus (U.gt 0) hr ha hp h k ea hψ.symm,
    ← GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e₀, hm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegMin

theorem finite_of_finite_closedPoints {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    (h : (closedPoints T).Finite) : Finite T := by
  have hc : IsClosed (closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx
  have e := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := T))
  rw [Set.univ_inter, hc.closure_eq] at e
  rw [← Set.finite_univ_iff, ← e]
  exact h

theorem exists_embedding_closedPoint_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (hz : IsClosed ({z} : Set (f.fiber y))) :
    ∃ σ : (f.fiber y).residueField z ⟶ CommRingCat.of (AlgebraicClosure (Y.residueField y)),
      Spec.map σ ≫ (f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have := isClosed_singleton_iff_isClosedImmersion.mp hz
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    ((f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y)
  have h1 : LocallyOfFiniteType (Spec.map ψ) := hψ ▸ inferInstance
  have h2 : IsFinite (Spec.map ψ) := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr h1
  rw [IsFinite.SpecMap_iff] at h2
  letI := ψ.hom.toAlgebra
  haveI : Module.Finite (Y.residueField y) ((f.fiber y).residueField z) := h2
  let σ : (f.fiber y).residueField z →ₐ[Y.residueField y] AlgebraicClosure (Y.residueField y) :=
    IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  rw [← hψ]
  refine (Spec.map_comp _ _).symm.trans ?_
  congr 1
  ext a
  exact σ.commutes a

theorem finite_preimage_singleton_of_qFin {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : QFin f) (y : Y) : (f ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.residueField y)
  choose σ hσ using exists_embedding_closedPoint_fiber f y
  let Φ : closedPoints (f.fiber y) → (Sp K ⟶ X) := fun z ↦
    Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y
  have hΦf (z) : Φ z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
      Y.fromSpecResidueField y := by
    simp only [Φ, Category.assoc, Scheme.Hom.fiber_fac]
    rw [← hσ z.1 z.2]
    simp only [Category.assoc]
  have hΦpt (z) : Φ z (IsLocalRing.closedPoint K : Sp K) = f.fiberι y z.1 := by
    have hm : (f.fiber y).fromSpecResidueField z.1 (Spec.map (σ z.1 z.2)
        (IsLocalRing.closedPoint K : Sp K)) ∈ Set.range ((f.fiber y).fromSpecResidueField z.1) :=
      ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hm
    show (Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y)
      (IsLocalRing.closedPoint K : Sp K) = _
    exact congrArg (f.fiberι y) (Set.mem_singleton_iff.mp hm)
  have hΦinj : Function.Injective Φ := by
    intro z z' h
    have := hΦpt z
    rw [h, hΦpt z'] at this
    exact Subtype.ext ((f.fiberι y).isEmbedding.injective this).symm
  have hcp : (closedPoints (f.fiber y)).Finite := by
    rcases (closedPoints (f.fiber y)).eq_empty_or_nonempty with he | ⟨z₀, hz₀⟩
    · rw [he]; exact Set.finite_empty
    · have hS := hf K (Φ ⟨z₀, hz₀⟩)
      haveI := hS.to_subtype
      have : Finite (closedPoints (f.fiber y)) :=
        Finite.of_injective (β := {w : Sp K ⟶ X | w ≫ f = Φ ⟨z₀, hz₀⟩ ≫ f})
          (fun z ↦ ⟨Φ z, by simp only [Set.mem_setOf_eq, hΦf]⟩)
          (fun a b h ↦ hΦinj (congrArg Subtype.val h))
      exact Set.toFinite _
  haveI := finite_of_finite_closedPoints hcp
  exact Set.finite_coe_iff.mp ((f.fiberHomeo y).finite_iff.mp inferInstance)

theorem exists_finite_openImmersion_of_qFin : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra.FiniteType ℤ o] (N : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp o) (f : X ⟶ PSpace o N), IsIntegral X → Geo.Tor.IsNormalScheme X → LocallyOfFiniteType s → QuasiCompact s → IsSeparated s → f ≫ PSpace.str o N = s → QFin f → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o N) (i : X ⟶ Z), IsFinite p ∧ IsOpenImmersion i ∧ i ≫ p = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧ Dense (Set.range i) := by
  intro o _ _ _ N X s f hX hN _ _ _ hfs hq
  subst hfs
  haveI := isProper_str o N
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str o N)
  haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o N)
  haveI : IsSeparated f := IsSeparated.of_comp f (PSpace.str o N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (finite_preimage_singleton_of_qFin f hq)
  exact GlobalTheory.ZMain.exists_finite_openImmersion_pSpace o N X f hX hN inferInstance inferInstance
    inferInstance inferInstance

end GlobalTheory.SiegMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SiegJoin

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isUnit_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {z : M.Z} {y : Ω}
    (hy : y ∈ X.O (f z)) (hu : IsUnit (⟨y, hf.map_mem_O hy⟩ : M.O z)) : IsUnit (⟨y, hy⟩ : X.O (f z)) := by
  obtain ⟨U, a, hz, rfl⟩ := hy
  rw [RatModel.isUnit_valF_iff hz]
  have hz' : z ∈ f ⁻¹ᵁ U := hz
  have e : (⟨valF X.pt U a, hf.map_mem_O ⟨U, a, hz, rfl⟩⟩ : M.O z) =
      ⟨valF M.pt (f ⁻¹ᵁ U) (f.app U a), RatModel.valF_mem_O hz' _⟩ :=
    Subtype.ext (hf.valF_app ⟨_, hz⟩ a).symm
  rw [e, RatModel.isUnit_valF_iff hz', ← Scheme.preimage_basicOpen] at hu
  exact hu

theorem div_iff_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {J : Type}
    {t : J → Ω} (hX : X.HasDiv t) (z : M.Z) (x : J) : M.Div t x z ↔ X.Div t x (f z) := by
  obtain ⟨i, hi⟩ := hX (f z)
  have hi' : M.Div t i z := hf.div hi
  refine ⟨fun hx => ?_, fun hx => hf.div hx⟩
  rw [hi.div_iff_isUnit]
  exact isUnit_of_isHom hf (hi.2 x) ((hi'.div_iff_isUnit x).1 hx)

end GlobalTheory.SiegJoin

namespace GlobalTheory.SiegJoin

theorem minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE), MinorAt S X M U₀ EE f Xab ∧ IsOpen (abLocus Zh.G) ∧ (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
  intro o Ω _ _ _ _ S ρ hB hfin
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hT : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point GlobalTheory.T.semistableReduction_ppav_padicField GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 hL.1 hL.2 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2 o Ω S ρ).1
  obtain ⟨n, a, GG, X, M, U₀, EE, f, Xab, hNm, hP, -, hO, hE, hH, hXab, hI, hgen, -⟩ := GlobalTheory.T.exists_normal_model_theta_tuple_maximal_minors o Ω S hT hfin
  obtain ⟨Zh⟩ := GlobalTheory.T.zarhinGeometric_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField o Ω S ρ hB M U₀ EE hO hE ⟨n, a, GG, hgen⟩
  have hsupI : ∀ z : M.Z, S.supI M z = S.supI X (f z) := fun z =>
    Set.ext fun x => div_iff_of_isHom hH hNm.1 z x
  have key : (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
    rw [Zh.ab, hXab]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ThetaSys.TT, ThetaSys.HH, hsupI z]
  refine ⟨X, M, U₀, EE, f, Xab, Zh, ⟨hNm, hP, hNm.isNormalScheme, hO, hE, hH, hXab, hI⟩, ?_, key⟩
  rw [key]
  exact Xab.isOpen.preimage f.continuous

end GlobalTheory.SiegJoin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem RatModel.stalkMap_pt_surjective {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (y : Sp Ω) : Function.Surjective (M.pt.stalkMap y).hom := by
  obtain rfl : y = closedPoint Ω := Subsingleton.elim _ _
  intro t
  obtain ⟨U, f, hU, hf⟩ := M.onto ((stalkClosedPointIso (CommRingCat.of Ω)).hom.hom t)
  have h : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt hU
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap M.pt U h
  refine ⟨(M.Z.presheaf.germ U _ ((GlobalTheory.Points.le_preimage_iff M.pt U).1 h)).hom f, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).1
  have e2 := congrArg (fun φ => φ.hom f) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_eq _ _ h] at hf
  rw [← hf, ← e2]
  rfl

theorem stalkMap_spMap_finite {K L : Type} [Field K] [Field L] (φ : K →+* L) (hφ : φ.Finite) (y : Sp L) :
    ((spMap φ).stalkMap y).hom.Finite := by
  obtain rfl : y = closedPoint L := Subsingleton.elim _ _
  have e := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom φ)
  have hc : (Scheme.stalkClosedPointTo (spMap φ)).hom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial).hom)
    have : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo (spMap φ)) =
        CommRingCat.ofHom φ := by
      rw [e, Iso.inv_hom_id_assoc]
    rw [← CommRingCat.hom_comp, Category.assoc, this]
    exact hφ
  have : (spMap φ).stalkMap (closedPoint L) =
      Scheme.stalkClosedPointTo (spMap φ) ≫ (stalkClosedPointIso (CommRingCat.of L)).inv := by
    rw [Scheme.stalkClosedPointTo, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of L)).inv).2) hc

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.exists_model_of_finiteDimensional : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ}
    {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (o₂ Ω₂ : Type) [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
    [ArithBase o₂ Ω₂] [Algebra X₁.Ω₁ Ω₂] [FiniteDimensional X₁.Ω₁ Ω₂] (κ : X₁.o₁ →+* o₂), κ.Finite →
    (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) →
    ∃ (M : RatModel o₂ Ω₂) (q : M.Z ⟶ X₁.M.Z), GlobalTheory.IsNormalScheme M.Z ∧ IsFinite q ∧
      M.pt ≫ q = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt := by
  intro g n F W Z i X₁ o₂ Ω₂ _ _ _ _ _ _ κ hκ hc
  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.M.s = spMap ((algebraMap o₂ Ω₂).comp κ) := by
    rw [Category.assoc, X₁.M.pt_s, hc]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))
      (CommRingCat.ofHom (algebraMap X₁.Ω₁ Ω₂))).symm
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M, q, hn, hq, hpt⟩ := exists_ratModel_normalization X₁.o₁ o₂ Ω₂ κ hκ X₁.M.Z X₁.M.s X₁.M.lft X₁.M.qc
    X₁.M.sep _ hp hst
  exact ⟨M, q, GlobalTheory.IsNormalScheme.of_pred hn, hq, hpt⟩

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem rescale_psiEven : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ),
    EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  intro R _ _ D h eta hD hadd hsq
  have h0 : eta 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_eq_left.1 e.symm
  have key : ∀ χ : D.X, eta (-χ) * h χ = eta χ := fun χ => by
    rw [← hsq, pow_two, ← _root_.mul_assoc, ← hadd, neg_add_cancel, h0, _root_.one_mul]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul _ a b
  refine fun (χ : D.X) => corr_of_val D.P.isLB fun y J hJ => ?_
  show val (LB.mulGen D.P.L _ _ _ _ (GlobalTheory.UU.scaleGen (unitOn (eta (-χ))) (D.psi (-χ)))
      (LB.pullGen D.P.L _ _ D.sym (D.xK χ))) (𝟙 _) y J = val (GlobalTheory.UU.scaleGen (unitOn (eta χ)) (D.psi χ)) (𝟙 _) y J
  refine (val_mul hJ _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen _ _ _ hJ)
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val D.sym r y J) (Category.id_comp _)))).trans ?_
  refine (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) (hD χ y J hJ)).trans ?_)
  refine (_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) ((map_mul _ _ _).symm.trans
    (congrArg (gm _ y ⊤) ((hu _ _).symm.trans (congrArg unitOn (key χ)))))).trans (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)

end GlobalTheory.PolDeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valF_spMap_comp {F F' : Type} [Field F] [Field F'] (σ : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valF (spMap σ ≫ x) U f = σ (valF x U f) := by
  classical
  have h' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => h (show (spMap σ).base y ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top]
  exact congrArg (fun q => q.hom ((Scheme.Hom.appLE x U ⊤ h).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem toStk_valF_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  classical
  rw [valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

variable {K : Type} [Field K] (k₀ : Subfield K) {X Y Y' : Scheme.{0}}

theorem valF_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : valF x U a ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hx
  have h₀ : ⊤ ≤ P₀ ⁻¹ᵁ U := (top_le_iff_mem P₀ U ((spMap k₀.subtype).base z)).2 h
  rw [valF_spMap_comp k₀.subtype P₀ U h₀ a]
  exact (valF P₀ U a).2

theorem gs_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : ∃ c ∈ k₀, gs x z U a = toStk z c :=
  ⟨valF x U a, valF_mem_of_defOver k₀ hx U z h a, (toStk_valF_gs x U z h a).symm⟩

variable {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_mem_of_defOver (t : LB.Gen (LB.LinComb L φ ε)) {r : Sp K ⟶ Y} (hr : DefOver k₀ r) (z : Sp K)
    {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) : ∃ c ∈ k₀, (val t r z J).val = toStk z c := by
  have hm := hJ.mem φ r
  obtain ⟨c, hc, e⟩ := gs_mem_of_defOver k₀ hr _ z hm (t.s fun k => J (r ≫ φ k)).val
  exact ⟨c, hc, (gs_unit r z _ hm _).symm.trans e⟩

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem spMap_subtype_cancel {R : Type} [CommRing R] {a b : Sp k₀ ⟶ Sp R}
    (h : spMap k₀.subtype ≫ a = spMap k₀.subtype ≫ b) : a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b] at h ⊢
  congr 1
  simp only [spMap, ← Spec.map_comp] at h
  have e := Spec.map_injective h
  ext y
  exact congrArg (fun q => q.hom y) e
end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem defOver_comp {X Y : Scheme.{0}} {P : Sp K ⟶ X} (hP : DefOver k₀ P) (g : X ⟶ Y) : DefOver k₀ (P ≫ g) := by
  obtain ⟨P₀, rfl⟩ := hP
  exact ⟨P₀ ≫ g, (Category.assoc _ _ _).symm⟩

theorem defOver_spMap {R : Type} [CommRing R] (f : R →+* K) (hf : ∀ a, f a ∈ k₀) : DefOver k₀ (spMap f) :=
  ⟨spMap (f.codRestrict k₀ hf), by simp only [spMap, ← Spec.map_comp]; rfl⟩

theorem defOver_pullback {R : Type} [CommRing R] {A B : Scheme.{0}} {f : A ⟶ Sp R} {g : B ⟶ Sp R}
    {x : Sp K ⟶ pullback f g} (h₁ : DefOver k₀ (x ≫ pullback.fst f g)) (h₂ : DefOver k₀ (x ≫ pullback.snd f g)) :
    DefOver k₀ x := by
  obtain ⟨Q₁, hQ₁⟩ := h₁
  obtain ⟨Q₂, hQ₂⟩ := h₂
  have hw : Q₁ ≫ f = Q₂ ≫ g := spMap_subtype_cancel k₀ (by
    rw [← Category.assoc, hQ₁, ← Category.assoc, hQ₂, Category.assoc, Category.assoc, pullback.condition])
  refine ⟨pullback.lift Q₁ Q₂ hw, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hQ₁]
  · rw [Category.assoc, pullback.lift_snd, hQ₂]

variable {X Y : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_spMap_mem {R : Type} [CommRing R] {L : LB X} {φ : Ix → (Sp R ⟶ X)} (t : LB.Gen (LB.LinComb L φ ε))
    (f : R →+* K) (hf : ∀ a, f a ∈ k₀) (z : Sp K) {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ c ∈ k₀, (val t (spMap f) z J).val = toStk z c :=
  val_mem_of_defOver k₀ t (defOver_spMap k₀ f hf) z hJ

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem hasPolChart_of_preChart_of_extension : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}}
    (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    IsGrpPullback F.univ.A G j e → abLocus G = Set.range j → PreChart F s j φ BD d x → HasPolChart F s j e φ BD d x :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hG _ he _ h => h.hasPolChart hG he

end GlobalTheory.PolDeg
end
