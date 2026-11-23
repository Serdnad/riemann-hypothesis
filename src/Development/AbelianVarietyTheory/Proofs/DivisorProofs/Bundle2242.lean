module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridKernelPairingIndependentOfExpansion
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechKS.isTangent_of_fibre : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  intro E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a

  have hunit : η[A].left ≫ m = x0 ≫ η[t.G].left := by
    have hw : (η[A].left ≫ m) ≫ t.G.hom = (𝟙_ (Over (Sp K))).hom ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w η[A]]
    let p : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk (η[A].left ≫ m) hw
    have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    have hpp := hm.2 (𝟙_ (Over (Sp K))) 1 1 p p (by rw [h1]; rfl) (by rw [h1]; rfl)
    rw [_root_.mul_one, h1] at hpp
    have hp : p * p = p := Over.OverMorphism.ext hpp
    have hp1 : p = 1 := mul_eq_left.mp hp
    have := congrArg (fun q => q.left) hp1
    simp only [p, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom] at this
    rw [this]
    simp
  show spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (u a).left = η[A].left
  apply hm.1.hom_ext
  · rw [Category.assoc, hu a, hunit, ← Category.assoc, ← Spec.map_comp]
    have hr : CommRingCat.ofHom (dualMap (ev x0 U.1 hU)) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ CommRingCat.ofHom (ev x0 U.1 hU) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp [dualMap, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
    rw [hr, Spec.map_comp, Category.assoc, (hv a).2, Hom.one_def, Over.comp_left, Over.toUnit_left,
      ← Category.assoc]
    congr 1
    exact GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  · rw [Category.assoc, Over.w (u a), Over.w η[A]]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    show _ = 𝟙 (Sp K)
    rw [← Spec.map_id]
    congr 1
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.intersection_number_multilinear_symm : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim → (∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ, ∀ c, M c = inter A c) ∧ ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  have hMultilinear : ∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ,
      ∀ c, M c = inter A c := by
    refine ⟨MultilinearMap.mk' (fun c => inter A c) (inter_update_add A hJ) ?_, fun c => rfl⟩
    intro c i n a
    exact map_zsmul (interAdd A hJ c i) n a
  exact ⟨hMultilinear, fun J' _ e c => inter_comp_equiv A e c⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem surjective_of_isFinite_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  intro K _ A B f hdim hfin
  obtain ⟨hBi, -, -⟩ := GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B
  set g := f.hom.left
  have eA : topologicalKrullDim A.X.left = Order.krullDim A.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := A.X.left))
  have eB : topologicalKrullDim B.X.left = Order.krullDim B.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B.X.left))
  have dA := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A
  have dB := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B
  rw [eA] at dA
  rw [eB] at dB

  have hm : StrictMono (g : A.X.left → B.X.left) := by
    intro a b hab
    have h1 : g a ≤ g b := (show b ⤳ a from hab.1).map g.continuous
    refine lt_of_le_not_ge h1 fun h2 ↦ hab.2 ?_
    have e : g b = g a := ((show g b ⤳ g a from h1).antisymm h2).eq
    have hd := (g.isDiscrete_preimage_singleton (g a)).to_subtype
    have : (⟨b, e⟩ : g ⁻¹' {g a}) ⤳ ⟨a, rfl⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp hab.1
    have hba : b = a := congrArg Subtype.val this.eq
    rw [hba]
  refine ⟨?_⟩
  by_contra hns
  have hη : genericPoint B.X.left ∉ Set.range g := by
    intro hη
    apply hns
    have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    intro y
    exact (genericPoint_specializes y).mem_closed hc hη
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 dA.ge
  have hlast : (l.map g hm).last < genericPoint B.X.left := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun h2 ↦ hη ?_
    have e := ((genericPoint_specializes ((l.map g hm).last)).antisymm h2).eq
    rw [e, LTSeries.last_map]
    exact ⟨_, rfl⟩
  have := Order.LTSeries.length_le_krullDim ((l.map g hm).snoc _ hlast)
  rw [dB, RelSeries.snoc_length, LTSeries.map_length, hl, ← hdim] at this
  norm_cast at this
  omega

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem cancel_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left →
    ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  intro K _ A B p hp C f g h
  have hB : IsIntegral B.X.left := (GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B).1
  have hsep : IsSeparated C.X.hom := C.ab.proper.toIsSeparated
  apply Subtype.ext
  change f.hom = g.hom
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated C.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) p.hom.left ?_)
  have := congrArg (fun u => (Hom.hom u).left) h
  simpa only [comp_hom, Over.comp_left] using this

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_apply_ne_origin' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 → ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  first | exact @GlobalTheory.AV.AbVar.exists_apply_ne_origin | exact GlobalTheory.AV.AbVar.exists_apply_ne_origin | (intros; apply GlobalTheory.AV.AbVar.exists_apply_ne_origin <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.intersection_number_pullback_not_surjective_eq_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ¬ Surjective f.hom.left → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = 0 := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_eq_zero_of_not_surjective) | (exact GlobalTheory.AV.AbVar.inter_pull_eq_zero_of_not_surjective) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_eq_zero_of_not_surjective  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_quotient_finite :
    ∀ (K : Type) [Field K] (A : AbVar K) (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A.X), IsMonHom i → Mono i →
      IsFinite H.hom → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧
        ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 ↔ ∃ y, y ≫ i = x := by
  intro K _ A H _ i hi hmono hfin
  have hflat : Flat H.hom := inferInstance
  obtain ⟨B', inst, q, -, hB, hq, hqfin, -, hqsurj, -, hsq⟩ :=
    AbQuotientAny.exists_quotient_abelianScheme K A.X H i A.ab hi hmono hfin hflat
  obtain ⟨g, hg⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K B' hB
  let B : AbVar K := ⟨B', hB, g, hg⟩
  refine ⟨B, Hom.mk (B := B) q, ⟨hqfin, hqsurj⟩, fun T x => ⟨fun hx => ?_, ?_⟩⟩
  · have e : x ≫ q = (1 : T ⟶ A.X) ≫ q := by
      rw [MonObj.one_comp]; exact hx
    have h1 := hsq.lift_fst x 1 e
    have h2 := hsq.lift_snd x 1 e
    rw [MonObj.comp_mul, h2, _root_.mul_one, ← Category.assoc] at h1
    exact ⟨_, h1⟩
  · rintro ⟨y, rfl⟩
    have hw := congrArg (fun f => lift y (1 : T ⟶ A.X) ≫ f) hsq.w
    rw [← Category.assoc, ← Category.assoc, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst,
      _root_.mul_one] at hw
    rw [MonObj.one_comp] at hw
    exact hw

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_factor_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  intro K _ A B f
  obtain ⟨Z, p, i, hpi, hp, hi, hg⟩ := GlobalTheory.T.exists_geometricallyIntegral_image_of_hom K A B f
  obtain ⟨hG, hpm, him⟩ := GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image K A B f Z p i hpi hp hi hg
  letI := hG
  have hmono : Mono i := by
    have : Mono i.left := inferInstance
    exact Over.mono_of_mono_left i
  have hcomm : IsCommMonObj Z := ⟨by
    apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  have hw : i.left ≫ B.X.hom = Z.hom := Over.w i
  have hB := B.ab
  have : Smooth B.X.hom := hB.smooth
  have : IsProper B.X.hom := hB.proper
  have hlft : LocallyOfFiniteType Z.hom := by rw [← hw]; infer_instance
  have hpr : IsProper Z.hom := by rw [← hw]; infer_instance
  have hsm : Smooth Z.hom := GlobalTheory.grpObj_smooth_of_geometricallyReduced K Z hlft inferInstance
  have hgc : GeometricallyConnected Z.hom := ⟨fun L _ y W fst snd h => by
    have : IsIntegral W := hg.geometrically_isIntegral y fst snd h
    infer_instance⟩
  have hab : IsAbelianScheme Z := ⟨hcomm, hsm, hpr, hgc⟩
  obtain ⟨g, hd⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K Z hab
  let C : AbVar K := { X := Z, ab := hab, dim := g, smooth := hd }
  refine ⟨C, Hom.mk (B := C) p, Hom.mk (A := C) i, hp, hi, ?_⟩
  exact Subtype.ext hpi

end GlobalTheory.AV.AbVar
end

section

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.gridKernelPairing_independent_of_expansion : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (μ₀ : T), L.Is μ₀ → ∀ t ∈ U, ∀ Φ : G.Datum, (∀ β τ, S.IsExpansion t Φ β τ → ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) ∧ ∀ β τ τ', S.IsExpansion t Φ β τ → S.IsExpansion t Φ β τ' → ∀ c : S.Classes t Φ β, S.pairAt τ c = S.pairAt τ' c := by
  first | exact @GlobalTheory.FunObj.sumOK_vec_indep | exact GlobalTheory.FunObj.sumOK_vec_indep | (intros; apply GlobalTheory.FunObj.sumOK_vec_indep <;> assumption)
end

section

open GlobalTheory.LKTrip
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKTrip.HTGroup.LocPBij

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem starT_starT (x : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (starT G.star ℚ_[p] x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem starT_algebraMap (a : ℚ_[p]) :
    (starT G.star ℚ_[p] (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a)).unop = algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
    MulOpposite.unop_one]

theorem starT_mul (x y : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (x * y)).unop = (starT G.star ℚ_[p] y).unop * (starT G.star ℚ_[p] x).unop := by
  rw [map_mul, MulOpposite.unop_mul]

def starL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C where
  toFun x := (starT G.star ℚ_[p] x).unop
  map_add' x y := by rw [map_add (f := _), MulOpposite.unop_add]
  map_smul' a x := by
    rw [Algebra.smul_def, starT_mul, starT_algebraMap, RingHom.id_apply, Algebra.smul_def]
    exact (Algebra.commutes _ _).symm

def psiL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]]
    ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) :=
  LinearMap.prod (LinearMap.pi fun i => (G.locW i).toLinearMap)
    ((LinearMap.pi fun i => (G.locW i).toLinearMap).comp (starL G))

theorem psiL_injective : Function.Injective (psiL G) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact GlobalTheory.HTGroupLocInj.locW_inj G x (fun i => congrFun (congrArg Prod.fst hx) i)
    (fun i => congrFun (congrArg Prod.snd hx) i)

theorem finrank_eq : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) = Module.finrank ℚ_[p]
    (((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i))) := by
  rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_prod,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Fintype.card_fin]
  rw [← HTGroup.two_mul_sum_finrank_Fw p G, ← Finset.mul_sum]
  ring

theorem psiL_bijective : Function.Bijective (psiL G) := by
  haveI : ∀ i, FiniteDimensional ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => inferInstance
  exact ⟨psiL_injective G,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq G)).1 (psiL_injective G)⟩

end GlobalTheory.LKTrip.HTGroup.LocPBij

theorem GlobalTheory.LKTrip.HTGroup.bijective_locP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  intro p _ G
  have key : ∀ d : ℚ_[p] ⊗[ℚ] G.C, (starT G.star ℚ_[p] d).unop = d → (∀ i, G.locW i d = 0) → d = 0 :=
    fun d hd h0 => GlobalTheory.HTGroupLocInj.locW_inj G d h0 (fun i => by rw [hd]; exact h0 i)
  constructor
  · rintro ⟨⟨x, c⟩, hx⟩ ⟨⟨y, d⟩, hy⟩ h
    have hx' : (x : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := hx
    have hy' : (y : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] y).unop = algebraMap ℚ_[p] _ (d : ℚ_[p]) := hy
    have hc : c = d := congrArg Prod.fst h
    subst hc
    have hu := fun i => congrFun (congrArg Prod.snd h) i
    have sx : (starT G.star ℚ_[p] x).unop = ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hx', ← mul_assoc, Units.inv_mul, one_mul]
    have sy : (starT G.star ℚ_[p] y).unop = ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hy', ← mul_assoc, Units.inv_mul, one_mul]
    have hw : ∀ i, G.locW i x = G.locW i y := fun i => congrArg Units.val (hu i)
    have hwi : ∀ i, G.locW i ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) = G.locW i ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) := by
      intro i
      have := congrArg (fun u => ((u⁻¹ : (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ˣ) : Matrix (Fin G.n) (Fin G.n) (G.Fw i))) (hu i)
      exact this
    have hxy : x = y := by
      apply Units.ext
      apply GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_injective G
      refine Prod.ext (funext hw) (funext fun i => ?_)
      show G.locW i (starT G.star ℚ_[p] x).unop = G.locW i (starT G.star ℚ_[p] y).unop
      rw [sx, sy, map_mul, map_mul, hwi]
    subst hxy
    rfl
  · rintro ⟨c, a⟩
    obtain ⟨x, hx⟩ := (GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_bijective G).2
      (fun i => ((a i : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)),
       fun i => algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)))
    have h1 : ∀ i, G.locW i x = a i := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => congrFun (congrArg Prod.snd hx) i
    have hyy := GlobalTheory.LKTrip.HTGroup.LocPBij.starT_starT G x
    have hxy : x * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, Algebra.left_comm, Units.mul_inv, mul_one, sub_self]
    have hyx : (starT G.star ℚ_[p] x).unop * x = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, mul_assoc, Units.inv_mul, mul_one, sub_self]
    let u : (ℚ_[p] ⊗[ℚ] G.C)ˣ := ⟨x, algebraMap ℚ_[p] _ ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (starT G.star ℚ_[p] x).unop,
      by rw [Algebra.left_comm, hxy, ← map_mul, Units.inv_mul, map_one],
      by rw [mul_assoc, hyx, ← map_mul, Units.inv_mul, map_one]⟩
    refine ⟨⟨(u, c), hxy⟩, Prod.ext rfl (funext fun i => Units.ext (h1 i))⟩
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_basicOpen_topFormFrame_of_stalkKaehlerBasis : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  first | exact @GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn | exact GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn | (intros; apply GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical


theorem _root_.GlobalTheory.T.exists_kaehlerBasis_differentials_of_topFormFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ), SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)), GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) → ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)), ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  first | exact @GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame | exact GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame | (intros; apply GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame <;> assumption)
end
