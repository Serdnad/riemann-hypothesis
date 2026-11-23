module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle123
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle041
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle167
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ParTranslate
open GlobalTheory.UT GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaTranslate ReciprocityTheory.ChartRestriction.G.DVR

theorem toStk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem isAdd_comm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [C.s12, h.2 χ y J hJ, mul_comm]

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
  (w : W0 U)

abbrev Carries (t : SecA A F k) (σ : U.SecGF F k) : Prop :=
  GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
    (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ

theorem exists_carries (hw : w.IsGen) (σ : U.SecGF F k) : ∃ t, Carries U F k w t σ := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨-, i₂⟩ := isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')
  exact (i₂ σ).exists

theorem exists_unit_carries (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (l : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l) (y : Sp F)
    (J : (Sp F ⟶ A.A.left) → A.L.ι) (hJ : Good A.L y J) :
    ∃ c : ((Sp F).presheaf.stalk y)ˣ, ∀ t σ, Carries U F k w t σ →
      toStk y (valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ.f (fun _ => l))) =
        c.val * secVal t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) y J := by
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : r ≫ (U.genF F).left = r' := by
    have : lift (𝟙 (TFK (R := R) F)) a ≫ U.genF F = ptSecT A.A (a ≫ U.gen.hom) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
    exact congrArg (fun q => q.left) this
  have e₂ : r' ≫ (snd (TFK (R := R) F) A.A).left =
      (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left := by
    rw [e₀]
    exact congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) (a ≫ U.gen.hom))
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := by
    rw [e₀]
    exact (top_le_iff_mem _ _ y).1 hl
  have m₁ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left) y ∈
      A.L.U (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) := by
    rw [← e₂]
    exact hJ _
  refine ⟨isoVal w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) y l
    (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) ^ (k : ℤ), fun t σ h => ?_⟩
  have H := (isoRelM_iff w _ k _ h.1 _ h.2.1 t σ).1 h (Sp F) r y l _ m₂ m₁
  rw [Category.comp_id, e₁] at H
  exact (toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans H

theorem exists_const_actVal (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F))
    (a a' : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (h : a' ≫ U.gen.hom = θ.pt * (a ≫ U.gen.hom))
    (l l' : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l)
    (hl' : ⊤ ≤ (show Sp F ⟶ G.left from a'.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l') :
    ∃ c : F, c ≠ 0 ∧ ∀ t t' σ σ', Carries U F k w t σ → Carries U F k w t' σ' → ActVal θ t t' →
      valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ'.f (fun _ => l)) =
        c * valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a').left) _ (σ.f (fun _ => l')) := by
  let y : Sp F := IsLocalRing.closedPoint F
  obtain ⟨J, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨c, hc⟩ := exists_unit_carries U F k w a l hl y J hJ
  obtain ⟨c', hc'⟩ := exists_unit_carries U F k w a' l' hl' y J hJ
  let r : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e : r ≫ (translT A.A θ.pt).left = (ptSecT A.A (a' ≫ U.gen.hom)).left := by
    rw [h]
    exact congrArg (fun q => q.left) (ptSecT_translT (a ≫ U.gen.hom) θ.pt)
  obtain ⟨d, hd⟩ := toStk_onto y (c * thetaVal θ r y J * c'⁻¹).val
  refine ⟨d, fun h0 => ?_, fun t t' σ σ' h₁ h₂ h₃ => (toStk y).injective ?_⟩
  · have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd
    exact Units.ne_zero _ hd.symm
  · have a₁ := h₃ (Sp F) r y J hJ
    rw [e] at a₁
    rw [map_mul, hd, hc t' σ' h₂, hc' t σ h₁, Units.val_mul, Units.val_mul, _root_.mul_assoc,
      Units.inv_mul_cancel_left, _root_.mul_assoc]
    exact congrArg _ a₁

end

theorem parAt_translate : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (a a' : u.PtC) (g g' : GtPtF u.D.toPre (PadicAlgCl p)), 1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → a' ≫ u.U.gen.hom = x * (a ≫ u.U.gen.hom) → GtPtF.IsAdd pk.g g g' → u.ParAt k a g → u.ParAt k a' g' := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k pk x a a' g g' hk hx ha hg hpar w' hw' l' hl'
  have hG := hL.1.globalFns
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  obtain ⟨v, hv⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k pk.g.b
  obtain ⟨ω₀, h₀⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k g.b
  obtain ⟨ω₁, h₁, -, hco⟩ := CoefPhi.coef_phi hL u.V _ hA u.D (PadicAlgCl p) k hk pk v hv g g' (isAdd_comm hg) ω₀ h₀
  replace hco := hco 1 k le_rfl (mul_one k).symm pk (one_smul _ _).symm rfl v ω₀ ω₁
    ⟨hv, fun _ _ _ => (pow_one _).symm⟩ ⟨h₀, fun _ _ _ => (pow_one _).symm⟩ ⟨h₁, fun _ _ _ => (pow_one _).symm⟩
  obtain ⟨c₁, hc₁, -, hfr⟩ := ((CoefBasic.coef_basic u.V u.D.toPre (PadicAlgCl p) k g').2.2 ω₁ h₁).2.2.1 w' hw'
  obtain ⟨θ, rfl, hθ⟩ := exists_theta_actVal u.U (PadicAlgCl p) hG hL.1.kerPow hk pk x hx w₀ hw₀ v hv
  obtain ⟨l, hl⟩ := exists_chart u.U.LG.isLB (u.toG a (IsLocalRing.closedPoint (PadicAlgCl p)))
  replace hl := (top_le_iff_mem _ _ _).2 hl
  obtain ⟨κ, hκ, hsum⟩ := hpar ω₀ h₀ l hl
  obtain ⟨c₂, hc₂, hval⟩ := exists_const_actVal u.U.toUnifPre (PadicAlgCl p) k w₀ θ a a' ha l l' hl hl'
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG u.U (PadicAlgCl p) hk w₀ hw₀
  refine ⟨c₁ * (κ * c₂), mul_ne_zero hc₁ (mul_ne_zero hκ hc₂), fun σ s hs => ?_⟩
  obtain ⟨t, ht⟩ := exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀ σ
  obtain ⟨t', ht'⟩ := exists_actVal u.A.isLB θ t
  have hE : u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ t' (e t') := (he _ _).2 rfl
  have hΦ := (hθ t t' s (e t') ⟨σ, ht, hs⟩ hE).2 ht'
  obtain ⟨σ', hσ', hs'⟩ := hE
  have H := hsum σ' _ hs'
  rw [hval t t' σ σ' ht hσ' ht', ← (Equiv.addRight pk.y).hasSum_iff] at H
  have H' := H.mul_left c₁
  rw [_root_.mul_assoc, _root_.mul_assoc]
  refine (congrArg (HasSum · _) (funext fun χ => ?_)).mp H'
  exact (congrArg (c₁ * ·) (hco s _ hΦ χ)).trans (hfr s χ).symm

end GlobalTheory.ZH.ParTranslate
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FibreImm

theorem le_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U V : X.Opens}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  intro z hz
  by_contra hV
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set X) ∩ (V : Set X)ᶜ) ⟨z, hz, hV⟩
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  have e := pointOfClosedPoint_apply π y hc (IsLocalRing.closedPoint k)
  have h1 := (CrdCalc.top_le_iff _ _).1 (h _ (pointOfClosedPoint_comp π y hc)
    ((CrdCalc.top_le_iff _ _).2 (e.symm ▸ hy)))
  exact hy' (e ▸ h1)

theorem eq_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U : X.Opens} {f g : Γ(X, U)}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = GlobalTheory.ZH.valR x U g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  refine le_of_points π fun x hx hb => ?_
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le _))
  refine absurd ?_ ((CrdCalc.isUnit_valR_iff _ U hU _).2 hb).ne_zero
  rw [CrdCalc.valR_eq x U hU, map_sub, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, h x hx hU, sub_self]

theorem isClosedImmersion_of_surjective {V U : Scheme.{0}} [IsAffine V] [U.IsSeparated] (f : V ⟶ U)
    (hf : Function.Surjective f.appTop) : IsClosedImmersion f := by
  have : IsClosedImmersion (f ≫ U.toSpecΓ) := by
    refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2
  exact IsClosedImmersion.of_comp f U.toSpecΓ

theorem isClosedImmersion_of_crd {k : Type} [Field k] [IsAlgClosed k] {X T : Scheme.{0}} [IsReduced X]
    (pX : X ⟶ Sp k) (pT : T ⟶ Sp k) [LocallyOfFiniteType pX] [IsSeparated pT] (h : X ⟶ T) (hp : h ≫ pT = pX)
    {HX : LB X} {HT : LB T} (hX : HX.IsLB) (hT : HT.IsLB) {J : Type} (F : J → HX.Sec) (s : J → HT.Sec)
    (J₀ : Set J) (imm : ImmBy pX HX F J₀) (cov : ⨆ i : J₀, Out.nonzeroLocus (s i) = ⊤)
    (crd : ∀ (x : Sp k ⟶ X) (v : J → k), x ≫ pX = 𝟙 _ → Crd HX F x v → Crd HT s (x ≫ h) v) :
    IsClosedImmersion h := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ cov fun i => ?_
  obtain ⟨haff, r, hr, hgen⟩ := imm.2 i i.2
  have hV : h ⁻¹ᵁ Out.nonzeroLocus (s i) = Out.nonzeroLocus (F i) := by
    refine le_antisymm (le_of_points pX fun x hx hU => ?_) (le_of_points pX fun x hx hU => ?_)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ hv).1 ((CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).2 hU)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).1 ((CrdCalc.crd_isUnit_iff _ hv).2 hU)
  have hsurj : Function.Surjective (h.appLE _ _ hV.ge).hom := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨constFn pT _ a, eq_of_points pX fun x hx hU => ?_⟩
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU, GlobalTheory.Points.valR_constFn_of_section pX x hx _ hU,
        GlobalTheory.Points.valR_constFn_of_section pT (x ≫ h) (by rw [Category.assoc, hp, hx])
          (Out.nonzeroLocus (s i)) (hU.trans (x.preimage_mono hV.ge))]
    · obtain ⟨r', hr', -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hT (s j) (s i) _ le_rfl
      refine ⟨r', eq_of_points pX fun x hx hU => ?_⟩
      obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      have h1 := CrdCalc.crd_ratio hv (hr j) hU
      have h2 := CrdCalc.crd_ratio (crd x v hx hv) hr' (hU.trans (x.preimage_mono hV.ge))
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU]
      exact ((CrdCalc.crd_isUnit_iff _ hv).2 hU).mul_right_cancel (h2.symm.trans h1)
  have hsurj' : Function.Surjective (h.app (Out.nonzeroLocus (s i))).hom := by
    revert hsurj
    generalize Out.nonzeroLocus (F i) = V at hV
    subst hV
    rw [Scheme.Hom.appLE_eq_app]
    exact id
  have : IsAffine (h ⁻¹ᵁ Out.nonzeroLocus (s i)).toScheme := by rw [hV]; exact haff
  have : T.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from pT]; infer_instance
  have : (Out.nonzeroLocus (s i)).toScheme.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (Out.nonzeroLocus (s i)).ι]; infer_instance
  refine isClosedImmersion_of_surjective _ ?_
  rw [morphismRestrict_appTop]
  have h₁ : Function.Surjective (h.app ((Out.nonzeroLocus (s i)).ι ''ᵁ ⊤)).hom := by
    rw [Scheme.Opens.ι_image_top]
    exact hsurj'
  exact (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom _).op)).2.comp h₁

abbrev pullLB {X Y : Scheme.{0}} (f : Y ⟶ X) (L : LB X) : LB Y :=
  ⟨L.ι, fun l => f ⁻¹ᵁ L.U l, fun l l' => pullU f (L.U l ⊓ L.U l') (L.g l l')⟩

def pullSection {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} (s : L.Sec) : (pullLB f L).Sec where
  f l := (f.app (L.U l)).hom (s.f l)
  compat i j := by
    have e := congrArg (f.app (L.U i ⊓ L.U j)).hom (s.compat i j)
    rw [map_mul] at e
    have e₁ := congrArg (fun φ => φ.hom (s.f i)) (f.naturality (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op)
    have e₂ := congrArg (fun φ => φ.hom (s.f j)) (f.naturality (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op)
    exact e₁.symm.trans (e.trans (congrArg (_ * ·) e₂))

theorem crd_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} {J : Type} (s : J → L.Sec) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y) (v : J → R) : Crd (pullLB f L) (fun j => pullSection f (s j)) x v ↔ Crd L s (x ≫ f) v := by
  refine exists_congr fun l => exists_congr fun c => and_congr Iff.rfl (forall_congr' fun j => ?_)
  rw [GlobalTheory.Points.valR_comp x f]
  rfl

theorem crd_lin {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X} {I J : Type} [Fintype J]
    {s : J → H.Sec} {s' : I → H.Sec} {n : Matrix I J k} (hn : ∀ i, IsLin p s (n i) (s' i)) {x : Sp k ⟶ X}
    (hx : x ≫ p = 𝟙 _) {v : J → k} (hv : Crd H s x v) : Crd H s' x (n.mulVec v) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  refine ⟨l, c, hl, fun i => ?_⟩

  rw [hn i l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, GlobalTheory.Points.valR_constFn_of_section p x hx _ hl, hv,
    mul_left_comm]

theorem isClosedImmersion_special_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (f' : t.u.G.left ⟶ Q.G.toScheme), f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι → ∀ h : pullback t.u.G.hom (rPt p ≫ spMap t.u.j) ⟶ pullback (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y), h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f' → h ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion h := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hbf Q p _ y y₀ t c tm hBig f' hf' h h1 h2
  have : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(utest_dim_and_split L o Ω S ρ p y₀ t.u).2.2.2.1, hBig.1, hBig.2.1⟩
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have : IsReduced t.mod.Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced t.mod.Φ.G.hom
  have := Q.proper
  suffices IsClosedImmersion (pb.isoPullback.hom ≫ h) from
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).1 this
  have hrange : Set.range (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι) ⊆
      Set.range (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z =
        (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ rPt p ≫ y) z := by rw [pullback.condition]
    have e₂ : rPt p (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) = cPt p := by
      rw [Subsingleton.elim (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) (IsLocalRing.closedPoint (kb p))]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    change (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z ∈ Q.W tm.l
    rw [e]
    exact (congrArg (fun w => y w ∈ Q.W tm.l) e₂).mpr tm.mem
  let e := IsOpenImmersion.lift (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι _ hrange
  have he : e ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ Q.G.ι := IsOpenImmersion.lift_fac _ _ _
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : rPt p ≫ spMap t.u.j = spMap ψ := (Spec.map_comp _ _).symm
  have hm : IsUnit (tm.m.map ψ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map ψ
  have hH : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := DVR.linComb_isLB _ Q.isLB _ _
  have hT := pullChart_isLB e hH
  choose s hs using fun i => (GlobalTheory.SecRatio.existsUnique_isLin (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y))
    (fun j => pullSection e (Q.σ tm.l j)) ((tm.m.map ψ)⁻¹ i)).exists
  have hsnd : (pb.isoPullback.hom ≫ h) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h2, IsPullback.isoPullback_hom_snd]
  have hhe : (pb.isoPullback.hom ≫ h) ≫ e = t.mod.r ≫ tm.f := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, he, Category.assoc, Category.assoc,
      reassoc_of% h1, hf', IsPullback.isoPullback_hom_fst_assoc]
  refine isClosedImmersion_of_crd t.mod.Φ.G.hom (pullback.snd _ _) _ hsnd (t.mod.Φ.H_isLB 1) hT t.mod.F s _
    (GlobalTheory.T.immBy_weight_zero' L.1 L.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol hB t.mod.good t.mod.dim) ?_ ?_
  · refine top_le_iff.1 (le_of_points (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y)) fun x hx _ => ?_)
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH (Q.σ tm.l) (x ≫ e)
    have hw := crd_lin hs hx ((crd_pull e _ x v).2 hv)
    have hv' : v = (tm.m.map ψ).mulVec ((tm.m.map ψ)⁻¹.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm, Matrix.one_mulVec]
    rw [hv'] at hv
    obtain ⟨i, hi, hne⟩ := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hbf Q p y y₀ t c tm hBig (x ≫ e) _ (by
      rw [Category.assoc, reassoc_of% he, pullback.condition, reassoc_of% hx]) hv).1 (by
      rw [Category.assoc, he, ← Category.assoc, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
      exact le_rfl)
    exact ((CrdCalc.crd_isUnit_iff i hw).1 hne.isUnit).trans (x.preimage_mono
      (le_iSup (fun i : {i | t.mod.xe.symm (t.cls i) = 0} => Out.nonzeroLocus (s i))
        ⟨i, t.mod.xe.symm.map_eq_zero_iff.2 hi⟩))
  · intro x v hx hv
    have h₁ := t.mod.red (Over.homMk x hx) v hv
    have h₂ := tm.crd (kb p) ψ (x ≫ t.mod.r) v (by rw [Category.assoc, pb.w, reassoc_of% hx, hψ]) h₁
    rw [Category.assoc, ← hhe, ← Category.assoc] at h₂
    have h₃ := crd_lin hs (by rw [Category.assoc, hsnd, hx]) ((crd_pull e _ _ _).2 h₂)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec] at h₃

end GlobalTheory.ZH.FibreImm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (s : Fam D.toPre F k) (α : D.toPre.X), VGe D F v k α (s.s α) 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (i : ℕ) (g o : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul (n ^ i) g o ∧ ∀ w : Frm D.toPre F k g.b, w.IsGen → GenV hϖ hv w 0 → v (coef s g w α) = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | exact GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | (intros; apply GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.PrimitiveExpansion

theorem secLin_one {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem main : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : H0 U.LG.L 1, (∃ g, G.hom g = closedPoint V ∧ g ∈ nonzeroLocus σ) → (∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s σ) ∧ ∀ σ' : U.SecGF F 1, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) → ∃ ϑ, U.ExpandsG F 1 σ' ϑ ∧ Prim D Q v ϑ := by
  intro hL V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U σ ⟨x, hx, hn⟩
  obtain ⟨g, hE, hnd, H⟩ := GlobalTheory.NonzeroClosedFibre.main hL.1.globalFns V ϖ hϖ D Q hQ A G U σ
    (ThetaUnit.nonzeroOnSpecial_of_mem U σ x hx hn)
  have hgen := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd hL.1.secBaseChange V ϖ hϖ D (g 0)
    (fun ⟨g', h'⟩ => hnd ⟨g', fun j => (h' j).trans rfl⟩)
  refine ⟨fun s => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨Φ, hΦ, -⟩ := H (FractionRing V) (GlobalTheory.FamInt.ordVal hϖ) (GlobalTheory.FamInt.valOver_ordVal hϖ)
    obtain ⟨b, hb⟩ := ThetaUnit.exists_eq_smul_group hL.1.globalFns le_rfl U hE
      (fun α => (ThetaUnit.secScal_one_iff D.toPre Φ α _).1 (hΦ α))
      (fun t => (hgen t).exists.imp fun b hb => (ThetaUnit.secIsMul_iff _ _ _ _).1 hb) s
    exact ⟨b, (ThetaUnit.secIsMul_iff _ _ _ _).2 hb⟩
  · obtain ⟨ϑ, hϑ, h₀, h₁⟩ := H F v hv
    refine ⟨ϑ, ⟨1, fun _ => 1, fun _ => σ, fun _ => g, fun _ => hE, secLin_one _
      (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_), fun α => secLin_one _ (hϑ α)⟩, h₀,
      fun r hr h => h₁ ⟨r, hr, h⟩⟩
    rw [Category.id_comp]
    exact (hσ' y J hJ).symm

end GlobalTheory.Ex.PrimitiveExpansion
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.exists_descended_torsion_isometry_theta_coordinates : Laws → AllD fun {E} _ _ _ {H} D => ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (o : Full D K) (o' : Full D C), FullExt f o o' → ∀ (I' : FullI o') (ζ : ℕ → Kˣ), (∀ n, 0 < n → (I'.ζ n : C) = f (ζ n)) → ∃ I : FullI o, (∀ n, 0 < n → I.ζ n = ζ n) ∧ ∀ m, Odd m → (∀ (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Theta m v' → (withI o I).Theta m v) ∧ ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := by
  first | exact @GlobalTheory.DescendIso.exists_descend | exact GlobalTheory.DescendIso.exists_descend | (intros; apply GlobalTheory.DescendIso.exists_descend <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generic_iso_of_uniformisations_isoData : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D D' : DegData R I) (A A' : PolAV (Sp (FractionRing R))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ ψ : A'.A ≅ A.A, IsMonHom ψ.hom ∧ LBIso A'.L (A.L.pull ψ.hom.left) ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := R) F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF (RingHom.id R) hD F p.g p'.g → (QkToAkU U'.toUnifPre F k p' x' ↔ QkToAkU U.toUnifPre F k p (x' ≫ ψ.hom))) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.OAct O) (o' : D'.OAct O) (oA : A.OAct O) (oA' : A'.OAct O) (oG : RingAct G O) (oG' : RingAct G' O), U.OLinear O o oA oG → U'.OLinear O o' oA' oG' → (∀ (x : O) y, hD.xe (x • y) = x • hD.xe y) → (∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x)) → ∀ x, oA'.act x ≫ ψ.hom = ψ.hom ≫ oA.act x := by
  first | exact @GlobalTheory.exists_generic_iso_of_unif | exact GlobalTheory.exists_generic_iso_of_unif | (intros; apply GlobalTheory.exists_generic_iso_of_unif <;> assumption)
end
