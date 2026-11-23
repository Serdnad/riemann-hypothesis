module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section HrelGen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem hr_secScal_sval {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hc : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e
  have e := H _ _ hc
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  refine ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ?_)
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))

theorem hr_gs_zero (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

end HrelGen

section HrelInj

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))

end HrelInj

section HrelForm

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end HrelForm

section HrelMain

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end HrelMain

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def TwistBaseChangeStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R)
    (k : ℕ), 1 ≤ k →
    ∀ (α : D.X), ∃ (m : ℕ) (b : Fin m → D.SecB k α), m = k ^ D.P.g ∧
      ∀ (R' : Type) [CommRing R'] (f : R →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b'

theorem twistBCSpan_of (h : TwistBaseChangeStatement) : TwistBCSpanStatement := by
  intro R _ _ _ _ D k hk α R' _ _ f _ s'
  obtain ⟨m, b, -, hb⟩ := h R D k hk α
  have hbasis := hb R' f (fun i => pullSec (L := D.P.L) (DegPre.famφB D α) (DegPre.famε k) (b i)
      (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left) (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hbasis s'
  exact ⟨m, r, b, hr⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section BoxG

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}

lemma boxG_le_b (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) :
    (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤ LB.wchart LG' (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL) := by
  unfold LB.div boxLB
  refine le_trans inf_le_right ?_
  intro x hx
  first
    | exact Set.mem_iInter.2 fun _ => hx
    | simpa [LB.wchart] using hx

lemma boxG_le_c (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) (i : Fin j) :
    (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤
      (pG.pr i).left ⁻¹ᵁ LB.wchart LG (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i) := by
  unfold LB.div boxLB
  refine le_trans inf_le_left (le_trans (LB.wchart_le LG _ jN i) ?_)
  intro x hx
  first
    | exact Set.mem_iInter.2 fun _ => hx
    | simpa [LB.wchart] using hx

def IsBoxSecG (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ) (σ' : H0 LG' k)
    (σ : Fin j → H0 LG k) : Prop :=
  ∀ (jN : Fin j → LG.ι) (jL : LG'.ι),
    ((w.s (jN, jL)) ^ k).val * rs (boxG_le_b pG jN jL) (σ'.f (fun _ => jL)) =
      ∏ i, rs (boxG_le_c pG jN jL i) (((pG.pr i).left.app _).hom ((σ i).f (fun _ => jN i)))

end BoxG

section BoxB

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}

def IsBoxFamB {D' D : DegPre R} (pD : IsPowDeg D' D j) (k : ℕ) (f' : ∀ α' : D'.X, D'.SecB k α')
    (f : Fin j → ∀ α : D.X, D.SecB k α) : Prop :=
  ∀ α' : D'.X, ∃ hφ : ∀ (i : Fin j) (a : Fin 4),
      D'.famφB α' a ≫ (pD.pw.pr i).left = (pD.pw.pr i).left ≫ D.famφB (pD.xe α' i) a,
    ∀ (jN : Fin 4 → Fin j → D.P.L.ι) (jM : Fin 4 → D'.P.L.ι),
      (@id (Γ(D'.P.A.left, LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓
          LB.wchart D'.P.L (D'.famφB α') jM)ˣ)
        ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM))).val *
        rs (inf_le_right : LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓
            LB.wchart D'.P.L (D'.famφB α') jM ≤ LB.wchart D'.P.L (D'.famφB α') jM) ((f' α').f jM) =
      ∏ i, rs (inf_le_left.trans (box_le_of_comp D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α')
            (D.famφB (pD.xe α' i)) (pD.pw.pr i).left i (hφ i) jN))
        (((pD.pw.pr i).left.app _).hom (((f i) (pD.xe α' i)).f (fun a => jN a i)))

end BoxB

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

end Exp

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
