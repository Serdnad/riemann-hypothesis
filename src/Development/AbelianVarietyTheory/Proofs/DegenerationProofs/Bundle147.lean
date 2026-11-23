module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle138
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section

namespace GlobalTheory.LevelField

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcDataDescent

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F₁ F₂ : Type} [Field F₀] [Field F₁]
    [Field F₂] [Algebra (FractionRing R) F₀] [Algebra (FractionRing R) F₁] [Algebra (FractionRing R) F₂]
    {f : F₀ →+* F₁} {g : F₁ →+* F₂} {k : ℕ} {p₀ : QkPt D F₀ k} {p₁ : QkPt D F₁ k} {p₂ : QkPt D F₂ k}
    (h : QkExt f p₀ p₁) (h' : QkExt g p₁ p₂) : QkExt (g.comp f) p₀ p₂ := by
  refine ⟨h'.1.trans h.1, ?_, fun χ => corr_of_val D.P.isLB fun (y : Sp F₂) J hJ => ?_⟩
  · exact h'.2.1.trans ((congrArg (spMap g ≫ ·) h.2.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ p₀.g.b.left) (spMap_comp f g).symm)))
  · refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    exact congrArg (fun q => val (p₀.g.s χ) q y J) ((Category.assoc _ _ _).trans
      (congrArg (𝟙 (Sp F₂) ≫ ·) (spMap_comp f g).symm))

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {K : Type} [Fintype K] {pt pt' : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (hp : pt = pt') (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x)
    (z : Sp F) {J} (hJ : Good M z J) : val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  subst hp
  choose J₀ hJ₀ using fun χ : Sp F ⟶ B₀ => exists_chart hM₀ (χ z)
  have e := ((genRel_iff w t t₀ x z).1 h).2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  have e' := ((genRel_iff w t' t₀ x z).1 h').2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t' _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  exact mul_left_cancel (Units.ext (e.trans e'.symm))

variable {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {D : DegPre R} {D₀ : DegPre O'}
  {ψ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull ψ)} {k : ℕ}

theorem genRel_ext {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing O') F] [Algebra (FractionRing O') F'] {σ : F →+* F'}
    (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hσ₀ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')
    {q : QkPt D F k} {q' : QkPt D F' k} {q₀ : QkPt D₀ F k} {q₀' : QkPt D₀ F' k} (h : QkExt σ q q')
    (h₀ : QkExt σ q₀ q₀') {χ : D.X} {χ₀ : D₀.X} {x : F} (H : GenRel w (q.g.s χ) (q₀.g.s χ₀) x) :
    GenRel w (q'.g.s χ) (q₀'.g.s χ₀) (σ x) :=
  (genRel_congr D.P.isLB D₀.P.isLB w (gtφ_ext hσ h χ) (gtφ_ext hσ₀ h₀ χ₀) (q'.g.isGen _)
    (pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
    (fun _ _ hJ => val_corr hJ (h.2.2 χ) _) (fun _ _ hJ => val_corr hJ (h₀.2.2 χ₀) _) _).2
    ((genRel_pull_iff σ w _ _ x).2 H)

theorem eq_of_genRel {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] {f : O' →+* R}
    (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) ψ) (e : D₀.X ≃+ D.X) {q q' : QkPt D F k} {q₀ : QkPt D₀ F k}
    {x : D₀.X → F} (hy : q.y = q'.y) (H : ∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (x χ))
    (H' : ∀ χ, GenRel w (q'.g.s (e χ)) (q₀.g.s χ) (x χ)) : q = q' := by
  have hb : q.g.b = q'.g.b :=
    Over.OverMorphism.ext (gp.1.hom_ext (((H 0).1 2).trans ((H' 0).1 2).symm) (by rw [Over.w, Over.w]))
  refine TorusExt.qk_ext hy (TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_)
  obtain ⟨χ, rfl⟩ := e.surjective χ
  exact val_eq_of_genRel D₀.P.isLB (by rw [hb]) (H χ) (H' χ) y hJ

theorem toA_of_toA : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  intro hL E _ _ _ H R O' _ _ _ _ _ I _ t P D₀ hB f ψ w e gp _ k hk p₀ s x₀ C _ _ _ _ hC q₀ q x h₀ hy hg hx hA
    F _ _ _ _ hF q₀' q' x' h₀' hy' hg' hx'
  obtain ⟨F', _, _, σ, τ, hστ⟩ := exists_common_field (algebraMap (FractionRing R) C) (algebraMap (FractionRing R) F)
  letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap _ C)).toAlgebra
  letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap _ C)).toAlgebra
  have hσ : σ.comp (algebraMap (FractionRing R) C) = algebraMap (FractionRing R) F' := rfl
  have hσ₀ : σ.comp (algebraMap (FractionRing O') C) = algebraMap (FractionRing O') F' := rfl
  have hτ : τ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := hστ.symm
  have hτ₀ : τ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' :=
    IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun a =>
      (congrArg τ (hF a).symm).trans ((RingHom.congr_fun hστ _).symm.trans (congrArg σ (hC a))))
  obtain ⟨r, hr, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ hσ q
  obtain ⟨r', hr', -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult τ hτ q'
  obtain ⟨r₀, hr₀, -⟩ := TorusExt.existsUnique_qkExt hB σ hσ₀ q₀
  obtain ⟨r₀', hr₀', -⟩ := TorusExt.existsUnique_qkExt hB τ hτ₀ q₀'
  have a := qkExt_trans h₀ hr₀
  have a' := qkExt_trans h₀' hr₀'
  rw [hσ₀] at a
  rw [hτ₀] at a'
  obtain rfl : r₀ = r₀' :=
    (TorusExt.existsUnique_qkExt hB (algebraMap (FractionRing O') F') (RingHom.ext fun _ => rfl) p₀).unique a a'
  obtain rfl : r = r' := eq_of_genRel gp e (q₀ := r₀) (x := fun χ => algebraMap (FractionRing R) F' (s χ))
    (by rw [hr.1, hr'.1, hy, hy', h₀.1, h₀'.1]) (fun χ => genRel_ext hσ hσ₀ hr hr₀ (hg χ))
    (fun χ => by
      have b := genRel_ext hτ hτ₀ hr' hr₀' (hg' χ)
      rwa [show τ (algebraMap (FractionRing R) F (s χ)) = algebraMap (FractionRing R) F' (s χ) from
        RingHom.congr_fun hτ _] at b)
  letI : Algebra C F' := σ.toAlgebra
  letI : Algebra F F' := τ.toAlgebra
  haveI : IsScalarTower (FractionRing R) C F' := IsScalarTower.of_algebraMap_eq' hσ.symm
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq' hτ.symm
  have hj : spMap σ ≫ jFK (R := R) C = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hσ)
  have hj' : spMap τ ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hτ)
  have ex : TorsionExt.fieldMap (R := R) C F' ≫ x = TorsionExt.fieldMap (R := R) F F' ≫ x' := by
    refine Over.OverMorphism.ext ?_
    show spMap σ ≫ x.left = spMap τ ≫ x'.left
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hj, hj']
  refine (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr' x').2 ?_
  rw [← ex]
  exact (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr x).1 hA

end GlobalTheory.LevelField
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.FitMatch
open GlobalTheory.ArcPull GlobalTheory.ArcDataDescent

section General
variable {F F' : Type} [Field F] [Field F'] {B B₀ Y Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀}

theorem genRel_of_gauge {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) (hp : ∀ k, pt k ≫ φ = pt₀ k) (z : Sp F) {J J'} (hJ : Good M₀ z J)
    (hJ' : Good M z J')
    (H : (∏ k, om w z J J' (pt k) ^ ε k) * val t (𝟙 _) z J' = Units.map (toStk z).toMonoidHom x * val t₀ (𝟙 _) z J) :
    GenRel w t t₀ (x : F) := by
  obtain rfl : (fun k => pt k ≫ φ) = pt₀ := funext hp
  refine (genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
  rw [val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t₀ _ z J (fun k => J (pt k ≫ φ)) (fun k => by rw [Category.id_comp])] at H
  have m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ (pt k ≫ φ)
  have n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (pt k)) :=
    Set.mem_iInter.2 fun k => hJ' (pt k)
  have a := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z m₀ n₀ m₁ n₁
  simp only [pw, Category.id_comp] at a
  have key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j) =
      Units.map (toStk z).toMonoidHom x * gm (𝟙 _) z (LB.wchart M₀ (fun k => pt k ≫ φ) j₀) (t₀.s j₀) := by
    rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul H
    simp only [om, ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact congrArg Units.val key

theorem genRel_ext_iff (hM : M.IsLB) (hM₀ : M₀.IsLB) (w : LB.Iso M (M₀.pull φ)) {K : Type} [Fintype K]
    {pt : K → (Y ⟶ B)} {pt₀ : K → (Y₀ ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (σ : F →+* F') (r : Sp F ⟶ Y) (r₀ : Sp F ⟶ Y₀)
    {s : Sp F' ⟶ Y} {s₀ : Sp F' ⟶ Y₀} (h : s = spMap σ ≫ r) (h₀ : s₀ = spMap σ ≫ r₀) (x : F) :
    GenRel w (LB.pullGen _ _ _ t s) (LB.pullGen _ _ _ t₀ s₀) (σ x) ↔
      GenRel w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x := by
  subst h h₀
  refine Iff.trans ?_ (genRel_pull_iff σ w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x)
  have p : (fun k => (spMap σ ≫ r) ≫ pt k) = fun k => spMap σ ≫ r ≫ pt k := funext fun _ => Category.assoc _ _ _
  have p₀ : (fun k => (spMap σ ≫ r₀) ≫ pt₀ k) = fun k => spMap σ ≫ r₀ ≫ pt₀ k := funext fun _ => Category.assoc _ _ _
  refine genRel_congr hM hM₀ w p p₀ (t := LB.pullGen _ _ _ t (spMap σ ≫ r))
    (t' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t r) (spMap σ)) (t₀ := LB.pullGen _ _ _ t₀ (spMap σ ≫ r₀))
    (t₀' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t₀ r₀) (spMap σ))
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) _)
    (DVR.pullGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₀ _) _)
    (fun y J hJ => ?_) (fun y J hJ => ?_) _ <;>
  rw [val_pull hJ, val_pull hJ, val_pull hJ, Category.assoc]

theorem toStk_vF {K : Type} [Fintype K] {pt : K → (Y ⟶ B)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (r : Sp F ⟶ Y)
    {z : Sp F} {J} (hJ : Good M z J) : toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem pt r) _
end General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R} {D' : DegPre R'}
  {f : R →+* R'} {C : Type} [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing R') C]

theorem tf_comp (hf : Along f C) : (TF (R := R') C).hom ≫ spMap f = (TF (R := R) C).hom :=
  (congrArg (· ≫ spMap f) (Geo.Tor.spMap_comp _ _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans
    ((congrArg spMap (RingHom.ext fun x => hf x)).trans (Geo.Tor.spMap_comp _ _)))

theorem c_of_field (hf : Along f C) {ψ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap f) ψ)
    (x : D'.X) (y : D.X) (h : (DegPre.cF D' C x).left ≫ ψ = (DegPre.cF D C y).left) :
    (D'.c x).left ≫ ψ = spMap f ≫ (D.c y).left := by
  have := D.P.isAb.proper
  let g : R' →+* C := (algebraMap (FractionRing R') C).comp (algebraMap R' _)
  have hg : Function.Injective g := (algebraMap (FractionRing R') C).injective.comp (IsFractionRing.injective _ _)
  have e : spMap g = (TF (R := R') C).hom := Geo.Tor.spMap_comp _ _
  refine ext_of_injective hg (X := Sp R') (π := spMap g) (p := 𝟙 _) (p' := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
    D.P.A.hom ?_ ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Category.assoc]
    exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (Over.w (D.c y)).symm))
  · rw [e, ← Category.assoc _ (spMap f), tf_comp hf, ← Category.assoc]
    exact h

theorem genRel_field (hf : Along f C) {N N' : NumD C} (ν : NumOf D C N) (ν' : NumOf D' C N')
    {ψ : D'.P.A.left ⟶ D.P.A.left} (he : eSec D'.P.A ≫ ψ = spMap f ≫ eSec D.P.A) {w : LB.Iso D'.P.L (D.P.L.pull ψ)}
    (hw : w.IsGen) (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf ψ (spMap f) he D.P.L D.rig)) (x : N'.X) (y : N.X) (h s : Cˣ)
    (hc : (DegPre.cF D' C (ν'.eX x)).left ≫ ψ = (DegPre.cF D C (ν.eX y)).left)
    (hψ : N'.ψ x * h = N.ψ y * s) (hh : (h : C) * wVal ν' ν w (N'.c x) = wVal ν' ν w 1) :
    GenRel w (LB.pullGen _ _ _ (D'.psi (ν'.eX x)) (jFK (R := R') C)) (LB.pullGen _ _ _ (D.psi (ν.eX y)) (jFK (R := R) C))
      (s : C) := by
  have z : Sp C := (default : PrimeSpectrum C)
  have hJ : Good D.P.L z ν.J := fun p => (top_le_iff_mem _ _ z).1 (ν.good p)
  have hJ' : Good D'.P.L z ν'.J := fun p => (top_le_iff_mem _ _ z).1 (ν'.good p)
  have hv : ∀ a, toStk z (wVal ν' ν w a) = (om w z ν.J ν'.J (ν'.eA a).left).val := fun a =>
    toStk_valF _ ((D.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA a).left ≫ ψ)) ⊓ D'.P.L.U (ν'.J (ν'.eA a).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA a).left ≫ ψ)), hJ' _⟩ _
  have c₀ : ∀ a, (DegPre.cF D C a).left = jFK (R := R) C ≫ D.xK a := fun a => Category.assoc _ _ _
  have c₁ : ∀ a, (DegPre.cF D' C a).left = jFK (R := R') C ≫ D'.xK a := fun a => Category.assoc _ _ _
  have pm := (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _
    (rigPull_le ψ (spMap f) he D.P.L) (fun _ => rfl)).1 hr
  have e := pmaps_om (fun _ => he) pm (TF (R := R') C).hom z hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at e
  replace e := (congrArg (fun q => val D.rig q z ν.J) (tf_comp hf).symm).trans e
  have a₀ := (congrArg (toStk z) (ν.ψ_eq y)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ) ((toStk_vF _ _ hJ).trans (congrArg Units.val e))))
  have a₁ := (congrArg (toStk z) (ν'.ψ_eq x)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ') (toStk_vF _ _ hJ')))
  have a₂ := congrArg (toStk z) hh
  rw [map_mul, hv, hv, ν'.c_eq, c₁, map_one] at a₂
  let U := Units.map (toStk z).toMonoidHom
  have b₀ : U (N.ψ y) = _ * (_ * _) := Units.ext a₀
  have b₁ : U (N'.ψ x) = _ * _ := Units.ext a₁
  have b₂ : U h * _ = om w z ν.J ν'.J ((TF (R := R') C).hom ≫ eSec D'.P.A) := Units.ext a₂
  have b₃ := congrArg U hψ
  rw [map_mul, map_mul, b₀, b₁, ← b₂] at b₃
  refine genRel_of_gauge hw (DVR.pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen _) _) s
    (fun _ => (congrArg (· ≫ ψ) (c₁ _).symm).trans (hc.trans (c₀ _))) z hJ hJ' ?_
  rw [Fintype.prod_unique, val_pull hJ, val_pull hJ', Category.id_comp, Category.id_comp, zpow_neg_one]
  have e' := congrArg Additive.ofMul b₃
  apply Additive.ofMul.injective
  simp only [U, ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem match_of_fit : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  intro _ E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J _ hf u₀ hu ψ he w e
    ⟨gp, hw, hp, hx, _, hh⟩ hr ha
  have hc : ∀ χ : A.N.X, (DegPre.cF M.P.D.toPre C (ν'.eX (J.e χ))).left ≫ ψ = (DegPre.cF a.D₀ C (A.ν.eX χ)).left :=
    fun χ => by
      rw [← ν'.c_eq, ← A.ν.c_eq]
      exact (congrArg (fun q => (ν'.eA q).left ≫ ψ) (J.c_eq χ)).trans (hp _)
  have inj : Function.Injective f := fun x y h => IsFractionRing.injective O' (FractionRing O')
    ((algebraMap (FractionRing O') C).injective ((hf x).symm.trans (by rw [h]; exact hf y)))
  refine ⟨gp, hw, hr, ha, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    rw [hx]
    exact c_of_field hf gp _ _ (hc χ)
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    have k := genRel_field hf A.ν ν' he hw hr (J.e χ) χ (J.h (A.N.c χ)) (u ^ (A.be.be χ χ / 2)) (hc χ) (J.ψ_eq χ)
      ((congrArg (fun q => (J.h (A.N.c χ) : C) * wVal ν' A.ν w q) (J.c_eq χ)).trans (hh _))
    have lift : ∀ (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L], Along f L →
        jFK (R := O') L = spMap (algebraMap (FractionRing M.W) L) ≫ genMap inj := fun L _ _ _ h =>
      (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x =>
        (h x).symm.trans (congrArg (algebraMap (FractionRing M.W) L) (fracMap_algebraMap inj x).symm)))).trans
        (Geo.Tor.spMap_comp _ _)
    have t := fun (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L] (h : Along f L) =>
      genRel_ext_iff M.P.D.toPre.P.isLB a.D₀.P.isLB w (M.P.D.toPre.psi_gen (ν'.eX (J.e χ))) (a.D₀.psi_gen (A.ν.eX χ))
        (algebraMap (FractionRing M.W) L) (𝟙 _) (genMap inj) (s := jFK (R := M.W) L) (Category.comp_id _).symm (lift L h)
        (algebraMap M.W _ u₀ ^ (A.be.be χ χ / 2))
    rw [Units.val_zpow_eq_zpow_val, hu, ← map_zpow₀] at k
    have k' := (t F fun x => (hF x).symm).2 ((t C hf).1 k)
    rw [hx, huF, ← A.be_eq, ← map_zpow₀]
    exact k'

end GlobalTheory.FitMatch
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_normalised_unit (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (d : Γ(T.left, ⊤)ˣ),
      α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val α r z J = gm (r ≫ (fst T A).left) z ⊤ d * val α₀ r z J := by
  have hγ := DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ (ptSecT A 1).left)) (NormTheta.rigT_isGen (T := T) hρ c)
  obtain ⟨d, hd⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero]) hγ
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ hγ _))
  refine ⟨α, d, hα, corr_of_val hL fun y J hJ => ?_, fun Z r z J hJ => ?_⟩
  · rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormTheta.ptSec_fst, Category.comp_id,
      val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]
  · rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, hd _ _ z J hJ, Category.comp_id, mul_comm]

theorem isGenSec_smul {k : ℤ} {th : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (e : Γ(T.left, ⊤)ˣ) :
    IsGenSec A L k (SecM.toSec A ((e : Γ(T.left, ⊤)) • SecM.ofSec A th)) := fun s => by
  obtain ⟨r, hr⟩ := H s
  have e₁ : SecM.ofSec A s = r • SecM.ofSec A th := Subtype.ext (funext hr)
  have e₂ : SecM.ofSec A s = (r * (e⁻¹ : Γ(T.left, ⊤)ˣ)) • ((e : Γ(T.left, ⊤)) • SecM.ofSec A th) := by
    rw [← mul_smul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, e₁]
  exact ⟨_, fun j => congrArg (fun q => q.1 j) e₂⟩

theorem exists_thG (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a : ℤ)
    (ha : a = ((m ^ 2 : ℕ) : ℤ)) {I : Type} {x : I → (T ⟶ A)} (hx : ∀ i, x i ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) T)} {s₁ : LB.Sec (LPow A L a T)}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => a))}
    {U : I → ThetaGrp A L a T} {s₂ : I → LB.Sec (LPow A L a T)} {w : I → Γ(T.left, ⊤)}
    (hα : α.IsGen) (hτ : τ.IsGen)
    (h₁ : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a ((1 : ℕ) : ℤ) α th s₁)
    (hU : ∀ i, SymLift A L a (m ^ 2) (x i) (U i)) (h₂ : ∀ i, IsActOf A L a (U i) s₁ (s₂ i))
    (hw : ∀ i, IsValueAt A L a (s₂ i) 1 τ (w i)) :
    ∃ e : Γ(T.left, ⊤)ˣ, ∀ i, ThG A L ρ m th (x i) (e * w i) := by
  subst ha
  obtain ⟨α', d, hα', hn, hv⟩ := exists_normalised_unit hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α hα
  obtain ⟨b, hb⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, NormTheta.one_left, zpow_neg,
        mul_inv_cancel])
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (NormTheta.rigT_isGen (T := T) hρ ((m ^ 2 : ℕ) : ℤ))))
  refine ⟨d * b, fun i => ⟨hx i, SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i)), α',
    SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁), U i, hα', hn, ?_, hU i, ?_, fun y J hJ => ?_⟩⟩
  · refine VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A h₁ (𝟙 _) y hJ, hv _ _ y J hJ, gs_unit _ _ ⊤ trivial, Units.val_mul, _root_.mul_assoc]
  · refine VVRank.isTwistPull_of_sv A hL (U i).isGen fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A (h₂ i) (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, translT, lift_fst, mul_left_comm]
  · have q := ThetaPtMove.sv_of_isValueAt (hw i) (𝟙 _) y hJ
    have q' := hb _ (𝟙 _) y J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, mul_inv_eq_iff_eq_mul] at q'
    rw [Category.id_comp, q', Units.val_mul, ← gs_unit _ _ ⊤ trivial] at q
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      q, ptSecT_fst, Units.val_mul, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
    ring

end

theorem exists_gen_thG_of_isThetaPt : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  intro K _ P ρ hρ m Ix x v hx H
  have : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, h₁, hU, h₂, hw, hv⟩ := ThetaCoord.isThetaPtOver_of_subsingleton P H
  obtain ⟨e, he⟩ := exists_thG P.isLB hρ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hx (th := th) (α := α) hα hτ h₁ hU h₂ hw
  refine ⟨_, isGenSec_smul hth (u * e⁻¹), fun i => ?_⟩
  have q := ThG.smul P.isLB (a := ((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)))
    (th' := SecM.toSec P.A (((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)) • SecM.ofSec P.A th))
    rfl (he i)
  rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, ← hv i] at q
  exact q

end GlobalTheory.Ex.OneGen
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch


open GlobalTheory.PointUnif GlobalTheory.EigenSplit in
theorem fibLie_of_laws : Laws → FibLieSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hfib O _ act F hF τ n hn
  obtain ⟨-, P', φ, w, u, -, hφ, -, -, h1, h2, -, hex, -⟩ := hfib
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hx : ∀ z, Φ (u.ex z) = ex z := fun z => Over.OverMorphism.ext ((hΦ _).trans (hex z).symm)
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  have hF' : ∀ a z, Φ (u.ex (F a z)) = Φ (u.ex z) ≫ act.act a := fun a z => by
    rw [hx, hx]; exact hF a z
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => ⟨F a, hF' a⟩
  have hρF : ∀ a, ρ a = F a := fun a => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (hker _).1 ?_)
    have := he.1 ((ρ a - F a) z) (F a z)
    simp only [LinearMap.sub_apply, sub_add_cancel] at this
    rw [hρ, ← hF'] at this
    exact mul_eq_right.1 this.symm
  have hy : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _)) :=
    (Spec.map_comp _ _).symm
  rw [← hy] at hn
  have hE : (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = eigenSub ρ τ := by
    ext z
    simp only [mem_eigenSub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hρF]
  rw [hE]
  exact he.finrank_eigenSub act ρ hρ hn

end GlobalTheory.Ex.Arch
end
end

section


theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_centred_at_prime : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  first | exact @GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime | exact GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime | (intros; apply GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime <;> assumption)
end
