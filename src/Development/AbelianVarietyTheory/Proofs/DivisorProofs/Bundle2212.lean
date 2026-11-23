module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle313
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem eq_comp_section_of_apply_eq {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (t : X ⟶ Sp K)
    (e : Sp K ⟶ X) (he : e ≫ t = 𝟙 _) (q : Sp L ⟶ Sp K) (y : Sp L ⟶ X) (hy : y ≫ t = q)
    (p : Sp L) (p' : Sp K) (h : y p = e p') : y = q ≫ e := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective y
  obtain ⟨⟨z', α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective e
  simp only [Scheme.SpecToEquivOfField_symm_apply] at he hy h ⊢
  have hz : z = z' := by simpa using h
  subst hz
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField z ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at he
  rw [Category.assoc, ← hc, ← Spec.map_comp] at hy
  have h₁ := Spec.map_injective he
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun r => r.hom k) h₁
  subst hy
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  ext w
  have e₂ : c.hom (α.hom w) = w := α.hom.injective (e₁ _)
  simp [e₂]

theorem exists_apply_ne_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 →
    ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  intro K _ A B f hf
  by_contra hcon
  push_neg at hcon
  apply hf
  refine ext_of_pt_eq K A B f 0 fun x => ?_
  rw [zero_hom]
  let e : Sp K ⟶ B.X.left := (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X)
  have h1 : (x ≫ (1 : A.X ⟶ B.X)).left = (ptOver K (AlgebraicClosure K)).hom ≫ e := by
    have hP : (toUnit (ptOver K (AlgebraicClosure K))).left = (ptOver K (AlgebraicClosure K)).hom := by
      simpa using Over.w (toUnit (ptOver K (AlgebraicClosure K)))
    have hU : toUnit (Over.mk (𝟙 (Sp K))) = 𝟙 _ := toUnit_unique _ _
    simp only [e, Hom.one_def, ← Category.assoc, comp_toUnit, hU, Category.id_comp, Over.comp_left, hP]
  apply Over.OverMorphism.ext
  rw [h1]
  exact eq_comp_section_of_apply_eq B.X.hom e he _ _ (Over.w (x ≫ f.hom))
    (IsLocalRing.closedPoint _) (IsLocalRing.closedPoint K) (hcon _)

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.poincareClass_additive_in_dual_variable : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X), AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  first | (exact @GlobalTheory.AbDual.poincare_evc_mul_right) | (exact GlobalTheory.AbDual.poincare_evc_mul_right) | (intros; apply GlobalTheory.AbDual.poincare_evc_mul_right  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.topologicalKrullDim_abVar_eq_dim : ∀ (K : Type) [Field K] (A : AbVar K), topologicalKrullDim A.X.left = (A.dim : ℕ) := by
  first | exact @GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim | exact GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim | (intros; apply GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact : ∀ (K : Type) [Field K] (A : AbVar K), IsIntegral A.X.left ∧ IsLocallyNoetherian A.X.left ∧ CompactSpace A.X.left := by
  first | exact @GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace | exact GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace | (intros; apply GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isFinite_iff_finite_ker' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | exact GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_finite_ker <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem hom_genericPoint_ne {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIntegral A.X.left]
    [IsIntegral B.X.left] (hns : ¬ Surjective f.hom.left) :
    f.hom.left (genericPoint A.X.left) ≠ genericPoint B.X.left := by
  intro h
  apply hns
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
  have hcl : IsClosed (Set.range f.hom.left) := by
    rw [← Set.image_univ]; exact f.hom.left.isClosedMap _ isClosed_univ
  have hsub : closure ({genericPoint B.X.left} : Set B.X.left) ⊆ Set.range f.hom.left :=
    hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨_, h⟩)
  rw [(genericPoint_spec B.X.left).def] at hsub
  exact ⟨fun y => hsub (Set.mem_univ y)⟩

theorem inter_pull_eq_zero_of_not_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ¬ Surjective f.hom.left → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = 0 := by
  intro K _ A B f hdim hns J _ hJ c
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A).1
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B).1
  letI := A.algΓ
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  choose L hL hc using fun j => cls_surj (c j)
  have hne := hom_genericPoint_ne f hns
  have hη : genericPoint B.X.left ∈ (closure ({f.hom.left (genericPoint A.X.left)} : Set B.X.left))ᶜ :=
    fun h => hne (((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes _)).eq)
  have h1 := GlobalTheory.PullVanish.dim_closure_add_one_le (genericPoint_specializes (f.hom.left (genericPoint A.X.left)))
    isClosed_closure.isOpen_compl hη (fun h => h (subset_closure rfl))
  have h2 : topologicalKrullDim (closure ({genericPoint B.X.left} : Set B.X.left)) = topologicalKrullDim B.X.left := by
    rw [(genericPoint_spec B.X.left).def]
    exact (Homeomorph.Set.univ B.X.left).isHomeomorph.topologicalKrullDim_eq
  have hB : topologicalKrullDim B.X.left ≤ (A.dim : ℕ) := by
    rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K B, hdim]
  have h3 := GlobalTheory.PullVanish.withBot_lt_of_add_one_le_nat (h1.trans (h2.trans_le hB))
  have hA : topologicalKrullDim A.X.left ≤ ((0 + A.dim : ℕ) : WithBot ℕ∞) := by
    rw [Nat.zero_add, GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]
  let e : Fin 0 ⊕ Fin A.dim ≃ J := (Equiv.emptySum (Fin 0) (Fin A.dim)).trans (Fintype.equivFinOfCardEq hJ).symm
  have h := GlobalTheory.PullVanish.interNum_pull_eq_zero K 0 A.dim A.X.left B.X.left (hs ▸ hp) hA f.hom.left h3
    (fun i => i.elim0) (fun i => i.elim0) (fun a => L (e (.inr a))) (fun a => hL _)
  have hL' : ∀ j, ((L j).pull f.hom.left).IsLB := fun j => pull_isLB (hL j) _
  have hcl : (fun j => CechPic.pull f.hom.left (c j)) = fun j => cls ((L j).pull f.hom.left) (hL' j) := by
    funext j; rw [← hc j]; rfl
  rw [inter, hcl, ← interNum_eq_multiDiff K _ hL', ← interNum_comp_equiv K _ hL' e, ← h]
  congr 1
  funext x
  rcases x with i | a
  · exact i.elim0
  · rfl

end GlobalTheory.AV.AbVar
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_geometricallyIntegral_image_of_hom : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom ∧ Surjective p.left ∧ IsClosedImmersion i.left ∧ GeometricallyIntegral Z.hom := by
  first | (exact @GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral) | (exact GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral) | (intros; apply GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom → Surjective p.left → IsClosedImmersion i.left → GeometricallyIntegral Z.hom → ∃ _ : GrpObj Z, IsMonHom p ∧ IsMonHom i := by
  first | (exact @GlobalTheory.AV.AbVar.exists_grpObj_of_image) | (exact GlobalTheory.AV.AbVar.exists_grpObj_of_image) | (intros; apply GlobalTheory.AV.AbVar.exists_grpObj_of_image  <;> assumption)
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

namespace GlobalTheory.LogPole.VertDet

theorem det_eq_one_of_key {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (A : Matrix ι ι R) (k : ι → ℕ)
    (h : ∀ a b, a ≠ b → k a ≤ k b → A a b = 0) (hd : ∀ a, A a a = 1) : A.det = 1 := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp [hd]
  · intro s _ hs
    obtain ⟨i, hi, hk⟩ : ∃ i, s i ≠ i ∧ k (s i) ≤ k i := by
      by_contra hc
      push_neg at hc
      obtain ⟨i₀, hi₀⟩ : ∃ i, s i ≠ i := by
        by_contra h0
        push_neg at h0
        exact hs (Equiv.ext h0)
      have hlt : ∑ i, k i < ∑ i, k (s i) := by
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, hc i₀ hi₀⟩
        by_cases e : s i = i
        · rw [e]
        · exact (hc i e).le
      rw [Equiv.sum_comp s k] at hlt
      exact lt_irrefl _ hlt
    rw [Finset.prod_eq_zero (f := fun j => A (s j) j) (Finset.mem_univ i) (h _ _ hi hk), smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

theorem snd_unip_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {K : Type} [Field K] (N : GlobalTheory.FlagTan.FIx Dw → K) (σ : E →+* ℂ)
    (M : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (p q : Fin (Dw.mult σ)) :
    ((GlobalTheory.FlagTan.unip K N σ * M.map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) p q).snd
      = ∑ r, N (some ⟨σ, p, r⟩) * M r q := by
  rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [GlobalTheory.FlagTan.unip, TrivSqZeroExt.snd_mul, mul_comm]

theorem det_vert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (M : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ i j, j < i → M σ i j = 0) → (∀ σ i, M σ i i = 1) → (Matrix.of fun a b : VIx Dw => ((GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) a.1 * (M a.1).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) a.2.1.1 a.2.1.2).snd).det = 1 := by
  intro E _ _ _ H Dw K _ M hM hM1
  refine det_eq_one_of_key _ (fun a => (a.2.1.2 : ℕ)) ?_ ?_
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩ ⟨τ, ⟨i, j⟩, hij⟩ hne hk
    rw [Matrix.of_apply, snd_unip_mul]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases e : (some ⟨σ, p, r⟩ : GlobalTheory.FlagTan.FIx Dw) = GlobalTheory.FlagTan.VIx.toF ⟨τ, ⟨(i, j), hij⟩⟩
    · obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq e')
      have hlt : q < r := lt_of_le_of_ne hk (by rintro rfl; exact hne rfl)
      rw [hM _ _ _ hlt, mul_zero]
    · rw [Pi.single_eq_of_ne e, zero_mul]
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩
    rw [Matrix.of_apply, snd_unip_mul, Finset.sum_eq_single q]
    · rw [hM1, mul_one]
      exact Pi.single_eq_same _ _
    · intro r _ hr
      rw [Pi.single_eq_of_ne, zero_mul]
      intro e
      obtain ⟨-, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      exact hr (Prod.mk.inj (eq_of_heq e')).2
    · intro h1
      exact absurd (Finset.mem_univ _) h1

end GlobalTheory.LogPole.VertDet
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

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRowsFil

theorem isKSRow_of_isKSValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  intro E _ _ _ H Dw K _ A _ A' _ i h hA ψ ub hb n e θ s htan hθ hKS τ a₀ hrow
  obtain ⟨w₀, f, hfF, hf, -⟩ := hrow
  haveI : IsCommMonObj A := hA.comm
  have hcc : ∀ σ : E →+* ℂ, conjEmb (conjEmb σ) = σ := fun σ ↦ RingHom.ext fun x ↦ Complex.conj_conj _
  have hc : ∀ a, s * ∑ b, θ a b * ψ f (hb (e.symm b)) = s * θ a (e ⟨conjEmb τ, a₀⟩) := by
    intro a
    congr 1
    rw [Finset.sum_eq_single (e ⟨conjEmb τ, a₀⟩)]
    · rw [hf, Equiv.symm_apply_apply, if_pos rfl, mul_one]
    · intro b _ hb'
      rw [hf, if_neg, mul_zero]
      intro hq
      exact hb' (by rw [← hq, Equiv.apply_symm_apply])
    · intro hn; exact absurd (Finset.mem_univ _) hn
  refine ⟨GlobalTheory.SqZero.tanExp (ub τ) (fun b ↦ s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)),
    (GlobalTheory.LieComb.isLieComb_iff_tanExp _ _).2 rfl, f, hfF, hf, hKS f hfF _ ?_⟩
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp]
  symm
  simp only [GlobalTheory.SqZero.tanExp, GlobalTheory.SqZero.lieExp, hc]
  rw [Fintype.prod_equiv e.symm _ (fun p : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) ↦
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (TrivSqZeroExt.inr (s * θ (e p) (e ⟨conjEmb τ, a₀⟩)) : DualNumber K)
        (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ ub p.1 p.2) (fun a ↦ by simp only [Equiv.apply_symm_apply]),
    Fintype.prod_sigma, Finset.prod_eq_single τ]
  · intro σ _ hσ
    refine Finset.prod_eq_one fun k _ ↦ GlobalTheory.SqZero.epsTo_zero_comp ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (htan σ k)) _ ?_ _
    rw [hθ _ _ (by simpa [hcc] using hσ), mul_zero, TrivSqZeroExt.inr_zero]
  · intro hn; exact absurd (Finset.mem_univ _) hn

end GlobalTheory.KSRowsFil
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport


open GlobalTheory.FrameTransport in
theorem exists_surj_cls {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (u : GfC V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ (finG V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hK : congLev D.sp.cm V.gram Λ 𝔪 ≤ K) :
    ∃ f : GlobalTheory.NormSum.Cls D V.rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) → FinCl V K, Function.Surjective f := by
  classical
  obtain ⟨uf, huf_def⟩ : ∃ uf, uf = finG V u := ⟨_, rfl⟩
  rw [← huf_def] at hu
  have hufU : uf ∈ UA D.sp.cm V.gram := by rw [huf_def]; exact GlobalTheory.LevSplit.finE_mem_UA V u.1
  have lift : ∀ h : StandardLatticesGL3.GA D V.rank, ∃ g : GfC V, finG V g = frConj fr h.1 * uf⁻¹ := fun h =>
    GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V _ (mul_mem (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr h) (inv_mem hufU))
  choose φ hφ using lift

  have hC : ∀ c ∈ GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank, uf * frConj fr c.1 * uf⁻¹ ∈ K := by
    let ρ : StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D) :=
      (MulAut.conj uf).toMonoidHom.comp ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
    have hle : GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank ≤ K.comap ρ := by
      refine (Subgroup.closure_le _).2 fun k hk => ?_
      have hU : uf * frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram :=
        mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr k)) (inv_mem hufU)
      exact hK (GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence V fr uf Λ hu 𝔪 k hk.1 hk.2 hU)
    intro c hc
    exact hle hc
  refine ⟨fun q => DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out q)), ?_⟩
  intro p
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (ratFin V) (K.comap (finG V)) x = p := ⟨Quotient.out p, DoubleCoset.out_eq' p⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_standardUnitary_frameConj_eq V fr hfr (finG V x * uf) (mul_mem (GlobalTheory.LevSplit.finE_mem_UA V x.1) hufU)
  refine ⟨DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h, ?_⟩
  show DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))) = _
  obtain ⟨γ, hγ, c, hc, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
    (DoubleCoset.out_eq'
      (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))
  generalize Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h) = h' at e ⊢
  obtain ⟨q, hq, hqe⟩ := GlobalTheory.T.frameConj_standardRational_mem_unitaryRational V fr hfr γ hγ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V (uf * frConj fr c.1 * uf⁻¹)
    (mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr c)) (inv_mem hufU))
  refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨q, hq, k, ?_, ?_⟩
  · show finG V k ∈ K
    rw [hk]; exact hC c hc
  · apply finG_injective V
    have e1 : finG V x = frConj fr h.1 * uf⁻¹ := by rw [hh]; group
    have e2 : frConj fr h.1 = frConj fr γ.1 * frConj fr h'.1 * frConj fr c.1 := by
      rw [e]; simp only [Subgroup.coe_mul, map_mul]
    have e3 := hφ h'
    simp only [map_mul, hqe, e3, hk, e1, e2]
    group

theorem finCl_card_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  intro D T L sc G U hS X hX 𝔪 h𝔪 K hK
  obtain ⟨f, hf⟩ := exists_surj_cls (G.V X) (hS.fr X) (hS.fr_on X hX) (hS.u X) (G.Λ X) (hS.u_lat X hX) 𝔪 K hK
  obtain ⟨-, hI, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D (G.V X).rank
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 (G.V X).rank
  obtain ⟨hfin, hcard⟩ := hJ _ (GlobalTheory.FunObj.StdDatum.congLev_le 𝔪 _) hne
  have h1 := Nat.card_le_card_of_surjective f hf
  have hI' : (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) ≤ hBd D (G.V X).rank := hI
  calc (Nat.card (FinCl (G.V X) K) : ℝ)
      ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank)) : ℝ) := by
        exact_mod_cast h1
    _ ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) *
          ((GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank).relIndex (GlobalTheory.NormSum.intG D (G.V X).rank) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
        apply mul_le_mul hI' (by exact_mod_cast hle) (by positivity)
        exact le_trans (Nat.cast_nonneg _) hI'

end GlobalTheory.FrameTransport

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ᶠ w in cofinite, Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1 := by
  first | exact @GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one | exact GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one | (intros; apply GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one <;> assumption)
end
