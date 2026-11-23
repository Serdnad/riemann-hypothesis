module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
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
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GtCount

open GlobalTheory.TorusExt


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.GtCount.card_torsion_eq_mul {G B : Type} [AddCommGroup G] [AddCommGroup B] (p : G →+ B) (n : ℕ)
    (h : ∀ b : B, n • b = 0 → ∃ g, p g = b ∧ n • g = 0) :
    Nat.card {g : G // n • g = 0} = Nat.card {b : B // n • b = 0} * Nat.card {g : G // n • g = 0 ∧ p g = 0} := by
  have h' : ∀ b : {b : B // n • b = 0}, ∃ g, p g = b ∧ n • g = 0 := fun b => h b b.2
  choose s hs using h'
  have hp : ∀ g : {g : G // n • g = 0}, n • p g = 0 := fun g => by
    rw [← map_nsmul, g.2, map_zero]
  have hsec : ∀ (b b' : {b : B // n • b = 0}), (b : B) = b' → s b = s b' := by
    rintro b b' hbb
    rw [Subtype.ext hbb]
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun g => (⟨p g, hp g⟩, ⟨g - s ⟨p g, hp g⟩, ?_, ?_⟩)
      invFun := fun x => ⟨s x.1 + x.2.1, by rw [nsmul_add, (hs _).2, x.2.2.1, add_zero]⟩
      left_inv := fun g => Subtype.ext (add_sub_cancel _ _)
      right_inv := fun x => ?_ }
  · rw [nsmul_sub, g.2, (hs _).2, sub_zero]
  · rw [map_sub, (hs _).1, sub_self]
  · have hx : p (s x.1 + x.2.1) = x.1 := by rw [map_add (f := _), (hs _).1, x.2.2.2, add_zero]
    refine Prod.ext (Subtype.ext hx) (Subtype.ext ?_)
    change s x.1 + x.2.1 - s ⟨p (s x.1 + x.2.1), _⟩ = x.2.1
    rw [hsec ⟨p (s x.1 + x.2.1), _⟩ x.1 hx, add_sub_cancel_left]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.GtCount.card_torus_torsion (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ n = 1} = n ^ Module.finrank ℤ X := by
  haveI : NeZero (n : F) := ⟨hn⟩
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have hroots : Nat.card (rootsOfUnity n F) = n := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
    exact hζ.card_rootsOfUnity
  let b := Module.Free.chooseBasis ℤ X
  let e₁ : {t : Multiplicative X →* Fˣ // t ^ n = 1} ≃ (Multiplicative X →* rootsOfUnity n F) :=
    { toFun := fun t => (t.1).codRestrict (rootsOfUnity n F) fun x => by
        have := DFunLike.congr_fun t.2 x
        simpa [MonoidHom.pow_apply, mem_rootsOfUnity] using this
      invFun := fun s => ⟨(rootsOfUnity n F).subtype.comp s, by
        refine MonoidHom.ext fun x => ?_
        simpa [MonoidHom.pow_apply] using (mem_rootsOfUnity _ _).1 (s x).2⟩
      left_inv := fun t => Subtype.ext (MonoidHom.ext fun x => rfl)
      right_inv := fun s => MonoidHom.ext fun x => Subtype.ext rfl }
  let e := e₁.trans (MonoidHom.toAdditiveRight.trans
    ((addMonoidHomLequivInt ℤ).toEquiv.trans (b.constr ℤ).symm.toEquiv))
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr Additive.toMul, hroots,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

attribute [local instance] gtGroup

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.gtTors_iff {R : Type} [CommRing R] [IsDomain R] {D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (n : ℕ) (g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) : _root_.GlobalTheory.UU.GtTors D n g ↔ n • g = 0 := by
  unfold _root_.GlobalTheory.UU.GtTors
  simp [_root_.GlobalTheory.TorusExt.isNsmul_iff_eq, _root_.GlobalTheory.TorusExt.isZero_iff_eq]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.card_torsion_over_zero {R : Type} [CommRing R] [IsDomain R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} = n ^ D.rank := by
  let φ := _root_.GlobalTheory.TorusExt.torusPt D F
  have hinj : Function.Injective φ := _root_.GlobalTheory.TorusExt.torusPt_injective
  let e : {t : Multiplicative D.X →* Fˣ // t ^ n = 1} → {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} :=
    fun t => ⟨φ (Additive.ofMul t.1), by
      rw [← map_nsmul, ← ofMul_pow, t.2, ofMul_one, map_zero], _root_.GlobalTheory.TorusExt.torusPt_b _⟩
  have he : Function.Bijective e := by
    refine ⟨fun t t' htt => Subtype.ext ?_, fun g => ?_⟩
    · exact Additive.ofMul.injective (hinj (congrArg Subtype.val htt))
    · obtain ⟨t, ht⟩ := _root_.GlobalTheory.TorusExt.exists_torusPt_eq g.2.2
      refine ⟨⟨t, ?_⟩, Subtype.ext ht.symm⟩
      apply Additive.ofMul.injective
      apply hinj
      rw [ofMul_pow, map_nsmul, ← ht, g.2.1, ofMul_one, map_zero]
  rw [← Nat.card_congr (Equiv.ofBijective e he), _root_.GlobalTheory.GtCount.card_torus_torsion D.X F n hn]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.card_gtTors : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), (N : F) ≠ 0 → Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g} = N ^ (2 * D.P.g + D.rank) ∧ Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g ∧ g.b = _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F} = N ^ D.rank) := by
  intro hL _ R _ _ _ D F _ _ _ N hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hz : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F = 1 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF; rfl
  have h0 : (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F).b = 1 := by
    simpa using _root_.GlobalTheory.TorusExt.nsmul_b 0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F)
  let p : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F →+ Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) :=
    { toFun := fun g => Additive.ofMul g.b
      map_zero' := by rw [h0]; rfl
      map_add' := fun g g' => by rw [_root_.GlobalTheory.TorusExt.add_b]; rfl }
  have hsurj : ∀ b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A), N • b = 0 → ∃ g, p g = b ∧ N • g = 0 := by
    intro b hb
    obtain ⟨g, hgb, hg⟩ := _root_.GlobalTheory.TorusExt.exists_nsmul_eq_of_pow_eq hN0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) (b := Additive.toMul b)
      (by rw [h0]; exact hb)
    exact ⟨g, by simp [p, hgb], hg⟩
  have hB : Nat.card {b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) // N • b = 0} = N ^ (2 * D.P.g) := by
    have := (hL.mulN (Spec (CommRingCat.of R)) D.P N (Nat.one_le_iff_ne_zero.2 hN0)).2.2.2.2 F
      (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F).hom hN
    rw [← this]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun b => Iff.rfl)
  simp only [_root_.GlobalTheory.GtCount.gtTors_iff, hz]
  refine ⟨?_, _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN⟩
  rw [_root_.GlobalTheory.GtCount.card_torsion_eq_mul p N hsurj, hB, pow_add]
  congr 1
  rw [← _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [p])

end GlobalTheory.GtCount
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_zero_mul_rigV : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1), PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * rigV D z J = 1 := by
  intro R _ _ D F _ _ s₀ H hs z J hJ
  have hc : cT D (DegPre.BF D F) 0 = 1 := by
    have h := DVR.cPoint_add D (DegPre.BF D F) 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let ζ : (TF (R := R) F).left ⟶ (DegPre.BF D F).left := (DegPre.zF D F).left
  let p : DegPre.BF D F ⟶ TF (R := R) F := fst _ _
  have hζ : ζ ≫ p.left = 𝟙 _ := by
    show (DegPre.zF D F ≫ p).left = _
    rw [show DegPre.zF D F ≫ p = 𝟙 _ from lift_fst _ _]
    rfl
  let κ₀ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  let J' : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ => J (ζ ≫ ψ)
  have hJ' : Good D.P.L (ζ z) J' := fun ψ => hJ (ζ ≫ ψ)
  have e := H 0 (DegPre.BF D F) p (p ≫ κ₀) (snd _ _) (ζ z) J' hJ'
  rw [hc, _root_.mul_one, show lift p (snd _ _) = 𝟙 (DegPre.BF D F) from lift_fst_snd] at e
  have hne : sval (s₀ 0) (𝟙 (DegPre.BF D F).left) (ζ z) J' ≠ 0 :=
    sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) hs _ (𝟙 _) (ζ z) J' hJ'
  have e1 : (val (D.psi 0) (p ≫ κ₀).left (ζ z) J' * rigV D (ζ z) J').val = 1 :=
    (mul_eq_right₀ hne).1 e.symm
  have n1 := (values_natural _ _ _ _ D.P.L _ _ _ (p ≫ κ₀).left ζ z J hJ).2.2.1 (D.psi 0)
  have n2 := (values_natural _ _ _ _ D.P.L PUnit (fun _ => eSec D.P.A) (fun _ => 1)
    (DegPre.BF D F).hom ζ z J hJ).2.2.1 D.rig
  have a1 : ζ ≫ (p ≫ κ₀).left = jFK (R := R) F := by
    show ζ ≫ p.left ≫ jFK (R := R) F = _
    rw [← Category.assoc, hζ, Category.id_comp]
  have a2 : ζ ≫ (DegPre.BF D F).hom = (TF (R := R) F).hom := Over.w (DegPre.zF D F)
  rw [a1] at n1
  rw [a2] at n2
  apply Units.ext
  have e2 := congrArg (ζ.stalkMap z).hom e1
  rw [map_one, Units.val_mul, map_mul] at e2
  rw [Units.val_mul, Units.val_one]
  exact (congrArg₂ (· * ·) n1 n2).trans e2

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem cT_add (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (a b : D.X) :
    cT D T (a + b) = cT D T a * cT D T b := by
  rw [cT, D.c_add]
  exact MonObj.comp_mul _ _ _

theorem comp_cT (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) :
    ρ ≫ cT D T a = cT D T' a := by
  rw [cT, cT, ← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]

theorem kapV_one (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) :
    kapV D a b z J x 1 = (val D.sym (1 : T ⟶ D.P.A).left z J)⁻¹ * rigV D z J ^ 2 *
      cubV D.cub z J (cT D T a) (cT D T b) x := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  rw [kapV, kap0, inv_one]
  simp only [h.face₃, _root_.mul_one, _root_.one_mul, inv_one]
  rfl

theorem compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (a b mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (x : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : ∀ χ, sval (s₀ 0) (lift ρ (x * cT D T χ)).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J =
      C * (sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (a + mu)) (cT D T (b + mu)) x).val *
        ((val (D.psi (a + mu)) κ.left z J).val * (val (D.psi (b + mu)) κ.left z J).val) =
      C * (U * (cubV D.cub z J (cT D T a) (cT D T b) (x * cT D T mu)).val * (val (D.psi a) κ.left z J).val *
        (val (D.psi b) κ.left z J).val) := by
  have e₁ := (hA T ρ x 1 z J hJ).1 (a + mu) (b + mu) (a + b + 2 • mu) (a - b) (by rw [two_smul]; abel) (by abel)
  have e₂ := (hA T ρ (x * cT D T mu) 1 z J hJ).1 a b (a + b) (a - b) rfl rfl
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one x, hP _ T ρ κ _ z J hJ, hP (b + mu) T ρ κ _ z J hJ] at e₁
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one (x * cT D T mu), hP _ T ρ κ _ z J hJ, hP b T ρ κ _ z J hJ,
    _root_.mul_assoc x, _root_.mul_assoc x, ← cT_add, ← cT_add, add_comm mu a, add_comm mu b] at e₂
  have e₃ : ∑ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J * sval (s' i (a - b)) (lift ρ 1).left z J =
      C * U * ∑ i, sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * sval (s' i (a - b)) (lift ρ 1).left z J := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]; ring
  rw [e₁, e₂] at e₃
  have hne : gs (𝟙 _) z ⊤ (scal T.hom r) * ((val D.sym (1 : T ⟶ D.P.A).left z J)⁻¹ * rigV D z J ^ 2).val *
      (rigV D z J).val * (rigV D z J).val * sval (s₀ 0) (lift ρ (x * cT D T (a + mu))).left z J *
      sval (s₀ 0) (lift ρ (x * cT D T (b + mu))).left z J ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hr (Units.ne_zero _)) (Units.ne_zero _))
      (Units.ne_zero _)) (h0 _)) (h0 _)
  refine mul_left_cancel₀ hne ?_
  simp only [Units.val_mul] at e₃ ⊢
  linear_combination e₃

theorem gs_scal_ne_zero {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Y) {r : R}
    (hr : r ≠ 0) : gs (𝟙 _) z ⊤ (scal (q ≫ jK R) r) ≠ 0 := by
  have h2 : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
    have e := congrArg (fun φ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e.symm
  have h3 : scal (q ≫ jK R) r = scal q (algebraMap R (FractionRing R) r) := congrArg q.appTop.hom h2
  have hu : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  rw [h3, gs_eq _ z ⊤ trivial]
  exact ((((hu.map _).map q.appTop.hom).map _).map _).ne_zero

theorem isIso_transl (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) (snd T D.P.A * cT D (T ⊗ D.P.A) χ)) := by
  refine ⟨lift (fst T D.P.A) (snd T D.P.A * (cT D (T ⊗ D.P.A) χ)⁻¹), ?_, ?_⟩
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, comp_cT, mul_inv_cancel_right,
        Category.id_comp]
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, lift_snd, comp_cT, inv_mul_cancel_right, Category.id_comp]

end FirstSlot


open FirstSlot in
theorem psi_mul_psi_of_addition_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (a b mu α : D.X), α = a + b → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (a + mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + mu)) (jFK (R := R) F) z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ mu) * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J).val := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA hP h0 a b mu α hα c u hs z J hJ
  subst hα
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hint : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let κF : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have zf : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have zs : DegPre.zF D F ≫ snd _ _ = 1 := lift_snd _ _
  have zκ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A ≫ κF).left = jFK (R := R) F := by
    rw [← Over.comp_left, ← Category.assoc, zf, Category.id_comp]; rfl
  have hJ' : Good D.P.L ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) := fun ψ => hJ _
  have hhom : (DegPre.BF D F).hom = (fst (TF (R := R) F) D.P.A ≫ κF).left ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A ≫ κF)).symm
  have key := FirstSlot.compare D (TF (R := R) F) s₀ r s s' hA hP a b mu (DegPre.BF D F) (fst _ _) (fst _ _ ≫ κF)
    (snd _ _) ((DegPre.zF D F).left z) _ hJ' (by rw [hhom]; exact gs_scal_ne_zero _ _ hr)
    (fun χ => by
      have := isIso_transl D (TF (R := R) F) χ
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (DegPre.BF D F) χ)).left :=
        (Over.forget _).map_isIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (TF (R := R) F ⊗ D.P.A) χ))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    _ _ (fun i => by
      rw [lift_fst_snd]
      exact hs i _ _ hJ')
  have ψn : ∀ χ, ((DegPre.zF D F).left.stalkMap z).hom (val (D.psi χ) (fst (TF (R := R) F) D.P.A ≫ κF).left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J).val := fun χ => by
    rw [← zκ]
    exact ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 (D.psi χ)).symm
  have cn : ∀ x x' y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (cubV D.cub
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) x x' y).val =
      (cubV D.cub z J (DegPre.zF D F ≫ x) (DegPre.zF D F ≫ x') (DegPre.zF D F ≫ y)).val := fun x x' y => by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.cub.t).symm.trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
  have un : ((DegPre.zF D F).left.stalkMap z).hom (val u (𝟙 _)
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val u (DegPre.zF D F).left z J).val := by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 u).symm.trans ?_
    rw [Category.comp_id]
  have kn : ((DegPre.zF D F).left.stalkMap z).hom (gs (𝟙 _) ((DegPre.zF D F).left z) ⊤ (DegPre.constBF D F c ⊤)) =
      gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) := by
    refine (gs_comp_stalkMap (𝟙 _) (DegPre.zF D F).left z ⊤ trivial _).symm.trans ?_
    refine (gs_res ((DegPre.zF D F).left ≫ 𝟙 _) z (U := ⊤) (V := ⊤) le_top trivial _).trans ?_
    refine (gs_pull ((DegPre.zF D F).left ≫ 𝟙 _) (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
    rw [Category.comp_id, ← Over.comp_left, zf]
    rfl
  have k2 := congrArg ((DegPre.zF D F).left.stalkMap z).hom key
  simp only [map_mul] at k2
  rw [ψn, ψn, ψn, ψn, cn, cn, un, kn, MonObj.comp_mul, zs, comp_cT, comp_cT, comp_cT, comp_cT, comp_cT,
    _root_.one_mul, (isCub_cubV D.cub (T := TF (R := R) F) (z := z) (J := J) hJ).face₃, Units.val_one,
    _root_.one_mul] at k2
  simp only [Units.val_mul]
  exact k2

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isUnit_scal_comp_specMap {R F : Type} [CommRing R] [CommRing F] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (r : R) (h : IsUnit (φ r)) :
    IsUnit (scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r) := by
  have e : scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
    have := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    unfold scal
    rw [this]
    rfl
  rw [e]
  exact (h.map _).map _

theorem sval_eq_zero_of_forall_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_lift_pair {S : Scheme.{0}} (T₀ B : Over S) {T : Scheme.{0}} (r₁ r₂ : T ⟶ (T₀ ⊗ B).left)
    (h : r₁ ≫ (fst T₀ B).left = r₂ ≫ (fst T₀ B).left) :
    ∃ (q : T ⟶ S) (ρ : Over.mk q ⟶ T₀) (x y : Over.mk q ⟶ B), (lift ρ x).left = r₁ ∧ (lift ρ y).left = r₂ := by
  have w : r₂ ≫ (T₀ ⊗ B).hom = r₁ ≫ (T₀ ⊗ B).hom := by
    rw [← Over.w (fst T₀ B), ← Category.assoc, ← Category.assoc, h]
  let u₁ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₁ rfl
  let u₂ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₂ w
  have e : u₁ ≫ fst T₀ B = u₂ ≫ fst T₀ B := Over.OverMorphism.ext h
  refine ⟨_, u₁ ≫ fst T₀ B, u₁ ≫ snd T₀ B, u₂ ≫ snd T₀ B, ?_, ?_⟩
  · rw [lift_comp_fst_snd]; rfl
  · rw [e, lift_comp_fst_snd]; rfl

theorem addB_tensor_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA
  have := D.P.isAb.proper
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsProper (fst (TF (R := R) F) D.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (TF (R := R) F ⊗ D.P.A).left := isIntegral_tensor_left_of_smooth_grpObj _ _ _
  have key := fun α β : D.X => GlobalTheory.tensor_sections_eq_zero_iff F _ D.P.L D.P.isLB _ _ (fst (TF (R := R) F) D.P.A).left
    (fst (TF (R := R) F) D.P.A).left _ _ (DegPre.famφ D F α) (DegPre.famε 2) (DegPre.famφ D F β) (DegPre.famε 2) n
    (fun i => SecMod.mk _ (s i α)) (fun i => SecMod.mk _ (s' i β))
  refine ⟨fun a b => ⟨fun hne => ?_, fun ⟨ha, hb⟩ h0 => ?_⟩, fun α β hαβ => ?_⟩
  · by_contra hc
    refine hne ((key _ _).2 fun T r₁ r₂ h z J hJ => ?_)
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    refine ((hA (Over.mk q) ρ x y z J hJ).1 a b _ _ rfl rfl).trans ?_
    rcases not_and_or.1 hc with hc | hc
    · have := sval_eq_zero_of_forall_eq_zero (s₀ a) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y)).left z J
      exact (congrArg (_ * ·) ((congrArg (· * _) this).trans (zero_mul _))).trans (mul_zero _)
    · have := sval_eq_zero_of_forall_eq_zero (s₀ b) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y⁻¹)).left z J
      exact (congrArg (_ * ·) ((congrArg (_ * ·) this).trans (mul_zero _))).trans (mul_zero _)
  · let z := genericPoint (TF (R := R) F ⊗ D.P.A).left
    choose J hJ using fun χ : (TF (R := R) F ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have hG : Good D.P.L z J := hJ
    have h1 := (key _ _).1 h0 _ (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left
      (lift (fst (TF (R := R) F) D.P.A) (1 : _ ⟶ D.P.A)).left
      (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z J hG
    have h2 := ((hA (TF (R := R) F ⊗ D.P.A) (fst _ _) (snd _ _) 1 z J hG).1 a b _ _ rfl rfl).symm.trans h1
    rw [inv_one, _root_.mul_one, lift_fst_snd] at h2
    have hu : IsUnit (scal (TF (R := R) F ⊗ D.P.A).hom r) := by
      have e : (TF (R := R) F ⊗ D.P.A).hom = (fst (TF (R := R) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom
          ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
        rw [← Over.w (fst (TF (R := R) F) D.P.A), CommRingCat.ofHom_comp, Spec.map_comp]; rfl
      rw [e]
      refine isUnit_scal_comp_specMap _ _ r (IsUnit.mk0 _ ?_)
      exact (map_ne_zero (algebraMap (FractionRing R) F)).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    have hu' : IsUnit (gs (𝟙 _) z ⊤ (scal (TF (R := R) F ⊗ D.P.A).hom r)) := by
      rw [gs_eq _ z ⊤ trivial]
      exact (hu.map _).map _
    exact mul_ne_zero (mul_ne_zero hu'.ne_zero (Units.ne_zero _))
      (mul_ne_zero ((exists_ne_zero_iff_sval_ne_zero (s₀ a) hG).1 ha)
        ((exists_ne_zero_iff_sval_ne_zero (s₀ b) hG).1 hb)) h2
  · refine (key _ _).2 fun T r₁ r₂ h z J hJ => ?_
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    exact (hA (Over.mk q) ρ x y z J hJ).2 α β hαβ

end GlobalTheory
end
