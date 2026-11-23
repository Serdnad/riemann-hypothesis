module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitLevels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.JetGeo

open ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums

section Val
variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem valR_app (x : Sp A ⟶ Y) (q : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valR x (q ⁻¹ᵁ W) ((q.app W).hom f) = valR (x ≫ q) W f := by
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ W)
  · rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.ZH.FormCount.valR_appLE x q W _ le_rfl f hx
  · have hx' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ W := hx
    unfold valR
    rw [dite_eq_right hx, dite_eq_right hx']

theorem valR_res' (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U) (e' : U ≤ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ V
  · exact GlobalTheory.ZH.CrdCalc.valR_res x e h f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ U := fun hU => h (hU.trans (x.preimage_mono e'))
    unfold valR
    rw [dite_eq_right h, dite_eq_right h']

theorem valR_pullGen (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (x : Sp A ⟶ Z) (j : K → L.ι) :
    valR x (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val =
      valR (x ≫ h) (LB.wchart L φ j) (c.s j).val := by
  have e' : h ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => h ≫ φ k) j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  change valR x _ (resG Z e ((h.app _).hom (c.s j).val)) = _
  rw [valR_res' x e e']
  exact valR_app x h _ _

end Val

theorem ex_zero {B : NumB ℂ} {g : ℕ} (d : AB B g) : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem ex_sum {B : NumB ℂ} {g : ℕ} (d : AB B g) {J : Type} (s : Finset J) (v : J → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ex_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem thφ_pt (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, psum_eq_prod, comp_prod]
  have h3 : ∀ i, lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))) ≫ x3 D.P.A i =
      ν.eA (d.ex (![x, y, z] i)) := by
    intro i; fin_cases i <;> simp [x3]
  simp_rw [h3, ← map_prod, ← ex_sum]

end Pts

theorem jet_geo : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  intro R _ _ D _ N g ν d gm ⟨o, ho, hp⟩ χ χ' x y hx hy
  classical

  have hρ : redE ℂ ≫ (TE R ℂ).hom = (TF (R := R) ℂ).hom := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext; simp
    simp only [TE, Over.mk_hom, redE, spMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) hρ
  let P3 : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ G3 D.P.A) := fun z =>
    lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))
  let q : DegPre.BF D ℂ ⟶ G3 D.P.A :=
    lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (DegPre.prB D ℂ))
  let h := (lift (DegPre.cT D (TE R ℂ) χ) (lift (DegPre.cT D (TE R ℂ) χ') gm.b))
  have hb : ρ ≫ gm.b = ν.eA (d.ex 0) := by
    rw [ex_zero, map_one]
    ext1
    show redE ℂ ≫ gm.b.left = _
    rw [← hp.1, ho.1]
    rfl
  have hred : ρ ≫ h = P3 0 := by
    simp only [h, P3, comp_lift, hb, DegPre.cT, comp_toUnit_assoc]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have hq : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b ≫ q = h := by
    simp only [q, h, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd, DegPre.cT]
  have hpt : ∀ z, ptB ν d z ≫ q.left = (P3 z).left := by
    intro z
    rw [ptB, ← Over.comp_left]
    congr 1
    simp only [q, P3, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have e3 : ∀ z I, (P3 z).left ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left :=
    fun z I => thφ_pt ν d x y z I
  let j0 : thK.{0} → D.P.L.ι := fun I => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left
  let W0 := LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j0
  refine ⟨q.left ⁻¹ᵁ W0, (q.left.app W0).hom (D.cub.t.s j0).val, ?_, ?_, ?_⟩
  ·
    have hj : (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ h.left ≫ thφ D.P.A (x3 D.P.A) k)) = j0 := by
      funext I
      rw [Category.id_comp, ← Category.assoc, show redE ℂ ≫ h.left = (P3 0).left from congrArg Over.Hom.left hred,
        e3]
    refine Eq.trans ?_ (valR_app _ q.left W0 _).symm
    rw [← Over.comp_left, hq]
    unfold vE DegPre.cubAtT
    refine (valR_pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t h.left (𝟙 _) _).trans ?_
    rw [Category.id_comp]
    have key : ∀ j j' : thK.{0} → D.P.L.ι, j = j' → valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j') (D.cub.t.s j').val := by
      rintro _ _ rfl; rfl
    exact key _ _ hj
  · intro p _
    change (ptB ν d 0 ≫ q.left).base p ∈ W0
    rw [hpt]
    refine Set.mem_iInter.2 fun I => ?_
    have := ν.good ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I) (Set.mem_univ p)
    rw [e3] at this
    change ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I).base p ∈ D.P.L.U (j0 I)
    rw [e3]
    exact this
  · intro z hz
    refine ⟨fun I p _ => ?_, ?_⟩
    · have hm : (ptB ν d z ≫ q.left).base p ∈ W0 := hz (Set.mem_univ p)
      rw [hpt] at hm
      have := LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j0 I hm
      rw [← e3 z I]
      exact this
    · change valR (ptB ν d z) _ _ = valR _ _ _
      refine (valR_app (ptB ν d z) q.left W0 _).trans ?_
      rw [hpt]

end GlobalTheory.MBLow.JetGeo
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

def trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι) (n : ℤ) : A :=
  valR y (L.U a ⊓ L.U b) ((L.g a b) ^ n).val

def pickJ {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) : Ix :=
  jf (Classical.epsilon fun i' => φs i' = φs i)

theorem pickJ_congr {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) {i₁ i₂ : Fin 4}
    (h : φs i₁ = φs i₂) : pickJ φs jf i₁ = pickJ φs jf i₂ := by
  unfold pickJ; rw [h]

theorem pickJ_spec {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) :
    ∃ i', φs i' = φs i ∧ pickJ φs jf i = jf i' :=
  ⟨_, Classical.epsilon_spec (p := fun i' => φs i' = φs i) ⟨i, rfl⟩, rfl⟩

theorem trV_add {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n m : ℤ) : trV L y a b n * trV L y a b m = trV L y a b (n + m) := by
  unfold trV
  rw [zpow_add, Units.val_mul, GlobalTheory.ZH.CrdCalc.valR_mul y _ h]

theorem isUnit_trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) : IsUnit (trV L y a b n) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h]
  exact (Units.isUnit _).map _

theorem top_le_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j :=
  fun q _ => Set.mem_iInter.2 fun k => h k (x := q) trivial

theorem wchart_top_le {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j) (k : K) : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  fun q _ => Set.mem_iInter.1 (h (x := q) trivial) k

theorem trV_zero {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) : trV L y a b 0 = 1 := by
  unfold trV
  rw [zpow_zero, Units.val_one, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, map_one]

theorem trV_pow {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) (m : ℕ) : trV L y a b n ^ m = trV L y a b (n * m) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, ← map_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
    ← zpow_mul]

end GlobalTheory.MBLow.TanGauge

namespace GlobalTheory.MBLow.TanGauge

theorem gl_corr : ∀ {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')),
    LB.Gen.Corr L φ ε φ' ε' t t' → ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' →
    (∀ k k', φ k = φ' k' → j k = j' k') → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ' j' →
    valR y (LB.wchart L φ j) (t.s j).val = valR y (LB.wchart L φ' j') (t'.s j').val := by
  intro X Y L K K' _ _ φ ε φ' ε' t t' hc j j' hj hj' hx A _ y h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun q hq => ⟨h hq, h' hq⟩
  have e := congrArg Units.val (hc j j' hj hj' hx)
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') hh (t'.s j').val
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact congrArg (valR y _) e

theorem gl_pullGen : ∀ {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (j : K → L.ι) {A : Type} [CommRing A] (y : Sp A ⟶ Z),
    ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ j →
    valR y (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val = valR (y ≫ h) (LB.wchart L φ j) (c.s j).val := by
  intro X Y Z L K _ φ ε c h j A _ y hy
  have hy' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j :=
    top_le_wchart L _ _ _ fun k => by rw [← Category.assoc]; exact wchart_top_le L _ _ _ hy k
  have e := GlobalTheory.ZH.CrdCalc.valR_res y ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j) hy' (pullU h _ (c.s j)).val
  refine e.trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ j) (fun q hq => hy hq) _

theorem gl_gtφT_pull : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T T' : Over (Sp R)) (h : T'.left ⟶ T.left),
    h ≫ T.hom = T'.hom → ∀ (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A), b'.left = h ≫ b.left → ∀ (α : D.X) (i : Fin 4),
    DegPre.gtφT D T' b' α i = h ≫ DegPre.gtφT D T b α i := by
  intro R _ _ D T T' h hh b b' hb α i
  have hb' : b' = Over.homMk h hh ≫ b := by
    ext; simpa using hb
  subst hb'
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T' α) (Over.homMk h hh ≫ b)).left = (Over.homMk h hh : T' ⟶ T).left ≫
      (padd D.P.A (DegPre.cT D T α) b).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T' ≫ D.c α).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · show (Over.homMk h hh ≫ b).left = h ≫ b.left
    simp
  · change (toUnit T' ≫ η[D.P.A]).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_gtφT_famφB : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (b : T ⟶ D.P.A) (α : D.X) (i : Fin 4),
    DegPre.gtφT D T b α i = b.left ≫ D.famφB α (![1, 2, 0, 3] i) := by
  intro R _ _ D T b α i
  have pc : ∀ (x y : T ⟶ D.P.A), padd D.P.A x y = padd D.P.A y x := fun x y => by
    show x * y = y * x
    exact mul_comm x y
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T α) b).left = b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left, pc]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T ≫ D.c α).left = b.left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · exact (Category.comp_id _).symm
  · change (toUnit T ≫ η[D.P.A]).left = b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_prB' : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A),
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫ (DegPre.prB D C).left =
      b.left := by
  intro R _ _ D C _ _ b
  rw [← Over.comp_left, lift_snd]

theorem gl_scal : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A) (c : C),
    valR (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ⊤
      (scal (fst (TF (R := R) C) D.P.A).left c) = TrivSqZeroExt.inl c := by
  intro R _ _ D C _ _ b c
  have hq : (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫
      (fst (TF (R := R) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h := GlobalTheory.ZH.FormCount.valR_scal (algebraMap C (DualNumber C)) _ _ hq ⊤ (fun _ _ => trivial) c
  have e : resTop ⊤ (scal (fst (TF (R := R) C) D.P.A).left c) = scal (fst (TF (R := R) C) D.P.A).left c := by
    simp [resTop]
  rw [e] at h
  rw [h, TrivSqZeroExt.algebraMap_eq_inl]

theorem gl_tan : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (gm₀ : GtPt D (epsR R)), GtTan gm₀ →
    redE R ≫ gm₀.b.left = eSec D.P.A := by
  intro R _ _ D gm₀ hT
  obtain ⟨o, ⟨hb, -⟩, h1, -⟩ := hT
  rw [← h1, hb]
  have hw := Over.w (toUnit (baseOver (Sp R)))
  have e : (toUnit (baseOver (Sp R))).left = 𝟙 _ := by simpa using hw
  simp only [DegPre.zeroT, Over.comp_left, e, Category.id_comp]
  rfl

theorem gl_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    (TF (R := R) C).hom = spMap (toF R C) := by
  intro R _ _ C _ _
  simp only [TF, jFK, jK, Over.mk_hom, spMap, toF, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gl_redE : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    redE C ≫ spMap (dualMap (toF R C)) = spMap (toF R C) ≫ redE R := by
  intro R _ _ C _ _
  simp only [redE, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  simp [dualMap, toF]

theorem gl_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    spMap (dualMap (toF R C)) ≫ (epsR R).hom = (TE R C).hom := by
  intro R _ _ C _ _
  simp only [TE, epsR, Over.mk_hom, gl_TF, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.MBLow.TanGauge

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanLift

theorem isLocalRing_dualNumber (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem dualMap_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ (epsR R).hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem redE_over (R : Type) [CommRing R] : redE R ≫ (epsR R).hom = 𝟙 _ := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 2

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R]
  {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem exists_tan (U : UnifPre I D A G) (y : epsR R ⟶ G) (hy : IsTangent y) :
    ∃ gm : GtPt D.toPre (epsR R), TanRel U y gm ∧ GtTan gm ∧ IsTangent gm.b := by
  have hL := D.toPre.P.isLB
  have := isLocalRing_dualNumber R
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := isAdicComplete_map_of_finite I (DualNumber R)
  obtain ⟨g, hg⟩ := IntegralGt.exists_gtPt U (φ := algebraMap R (DualNumber R)) y
  have hz := fun e => hg e _ (thick R I e ≫ redE R) (eSec (thickObj R I e G))
    ((UnitValue.eSec_fGl (G := G) e).trans ((congrArg (thick R I e ≫ ·) hy.symm).trans (Category.assoc _ _ _).symm))
  have hb : redE R ≫ g.b.left = η[D.toPre.P.A].left := hom_ext_of_isHausdorff I fun e =>
    (Category.assoc _ _ _).symm.trans ((hz e).1.symm.trans (UnitValue.eSec_pGl U e))
  refine ⟨g, fun e => ?_, ?_, hb⟩
  · have w : (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left) ≫ G.hom =
        spMap (algebraMap _ (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e := by
      rw [Category.assoc, Over.w y]; exact dualMap_over _
    have h₁ : pullback.lift _ _ w ≫ (fstG I e G).left = _ := pullback.lift_fst _ _ _
    obtain ⟨h₂, h₃⟩ := hg e _ _ _ h₁
    refine ⟨_, h₁, h₂, fun χ => corr_of_val hL fun z J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp, Category.id_comp]
    exact h₃ χ z J hJ
  · obtain ⟨o, ho⟩ := FormalValue.exists_isZero D.toPre (baseOver (Sp R))
    have hob : o.b.left = redE R ≫ g.b.left := by
      rw [hb, ho.1]
      exact (congrArg (· ≫ η[D.toPre.P.A].left)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (baseOver (Sp R)))))).trans (Category.id_comp _)
    have e₁ := TorusCoord.comp_eq_of_left g.b o.b (redE R) (𝟙 _) (hob.symm.trans (Category.id_comp _).symm)
    refine ⟨o, ho, hob, fun χ => RedTotal.corr_of_levels I hL (fun W _ f => ?_) (o.isGen χ)
      (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) fun e z J hJ => ?_⟩
    · exact Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
        ((e₁.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq o.b χ) k).symm)).symm
    · refine ((val_corr hJ (ho.2 χ) _).trans (val_one _)).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      refine Eq.trans ?_ ((hz e).2 χ z J hJ)
      have := (val_corr hJ ((U.gt e).t_unit χ) (𝟙 _)).trans (val_one _)
      rw [val_pull hJ, Category.id_comp] at this
      exact this.symm

end GlobalTheory.MBLow.TanLift

end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.encard_complexPointFibre_eq_encard_ringHom_extensions : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U), (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  first | exact @GlobalTheory.encard_fibre_eq_encard_ringHom | exact GlobalTheory.encard_fibre_eq_encard_ringHom | (intros; apply GlobalTheory.encard_fibre_eq_encard_ringHom <;> assumption)
end
