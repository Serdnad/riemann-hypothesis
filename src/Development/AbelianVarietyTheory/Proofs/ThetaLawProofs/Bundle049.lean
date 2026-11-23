module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulSectionsExactAlgClosedPolarisedAV
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SymRoot

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def rigCls (c : Pic A.left) : Pic A.left := c - pull (1 : A ⟶ A).left c

theorem pull_rigCls (c : Pic A.left) (x : T ⟶ A) :
    pull x.left (rigCls c) = pull x.left c - pull (1 : T ⟶ A).left c := by
  rw [rigCls, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_one]

theorem lam_rigCls (c : Pic A.left) (x y : T ⟶ A) : lam (rigCls c) x y = lam c x y := by
  simp only [lam, pull_rigCls]
  abel

theorem lam_diag [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hs : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) :
    lam (cls L hL) (𝟙 A) (𝟙 A) = 2 • rigCls (cls L hL) := by
  have h := lam_mul_left hL hΘ (𝟙 A) (𝟙 A)⁻¹ (𝟙 A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls L hL) (𝟙 A)⁻¹ (𝟙 A) = -(2 • rigCls (cls L hL)) := by
    rw [lam, inv_mul_cancel, Hom.inv_def, Category.id_comp, hs, Over.id_left, pull_id, rigCls]
    abel
  rw [e] at h
  exact add_neg_eq_zero.1 h.symm

theorem exists_polAV_sqOf : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  intro laws h k o _ ζ R _ _ β c L ⟨ha, hk⟩ hdim hL hΛ hs
  have hA := c.ab
  have hd : c.diag.IsLB := pull_isLB c.isLB _
  have hp : IsProjBy c.A.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ c.A c.diag hA hd ha R (𝟙 _) _ (𝟙 _) c.A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ : ∃ t : LB.Gen (Theta c.A L), t.IsGen := CubeAffine.triv_theta_of_isProjBy laws R c.A hA hp L hL
  have s₁ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls L hL) = cls L hL :=
    ((cls_eq_iff hL (pull_isLB hL _)).2 hs).symm
  have e₀ : cls c.P c.isLB = lam (cls L hL) (fst c.A c.A) (snd c.A c.A) :=
    ((cls_eq_iff (LB.isLB_linComb hL _ _) c.isLB).2 hΛ).symm.trans (cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  obtain ⟨M, hM, e⟩ := cls_surj (rigCls (cls L hL))
  have e₁ : cls c.P c.isLB = lam (cls M hM) (fst c.A c.A) (snd c.A c.A) := by rw [e, lam_rigCls, e₀]
  have e₂ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls M hM) = cls M hM := by
    rw [e, pull_rigCls, s₁, rigCls]
  have e₃ : cls c.diag hd = 2 • cls M hM := by
    refine (cls_pull c.isLB _ _).trans ?_
    rw [e₀, pull_lam, lift_fst, lift_snd, lam_diag hL hΘ s₁, e]
  have hr : Out.Rigidified c.A M := by
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ((cls_pull hM _ _).trans ?_)
    have e₄ : (η[c.A] : 𝟙_ _ ⟶ c.A) = 1 := by rw [Hom.one_def]; simp
    have := pull_rigCls (cls L hL) η[c.A]
    rw [← e₄, sub_self, ← e] at this
    exact this
  have hsym : Out.Sym c.A M := fun s => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, e₂, one_smul, neg_smul, add_neg_cancel]⟩
  have hamp : Out.RelAmple c.A M := by
    have f : IsFinite (𝟙 c.A : c.A ⟶ c.A).left := by rw [Over.id_left]; infer_instance
    refine (relAmple_finite_pow_iso _ c.A c.A (𝟙 _) M 2 two_pos hA hA hM f).2.1.1
      ((relAmple_finite_pow_iso _ c.A c.A (𝟙 _) _ 2 two_pos hA hA hd f).2.2.2 _ (isLB_lbPow hM 2) ?_ ha)
    exact (cls_eq_iff hd (isLB_lbPow hM 2)).1 (e₃.trans (cls_lbPow hM 2 _).symm)
  have hid : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  refine ⟨{ A := c.A, isAb := hA, g := h, smoothDim := hdim, L := M, isLB := hM, rigid := hr, sym := hsym,
            ample := hamp, ktriv := ThetaExtend.kTriv_of_lam hM c.isLB e₁ hk }, 𝟙 _,
    (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl, rfl, 𝟙 _, ⟨by simp, by simp⟩, ?_⟩
  refine (cls_eq_iff (LB.isLB_linComb hM _ _) (pull_isLB c.isLB _)).1 ?_
  exact (cls_cube_two hM _ _ (LB.isLB_linComb hM _ _)).trans (e₁.symm.trans (pull_id _).symm)

end GlobalTheory.SymRoot
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory


theorem _root_.GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (c : x.P.A.left → x.P.L.ι), 1 ≤ n → x.P.g * n < l → FinZ x s → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ y, y ∈ x.P.L.U (c y)) → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧ (∀ a : ∀ y : x.P.A.left, x.P.A.left.presheaf.stalk y, ∃ sg : RR x l, ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) ∧ ∀ sg : RR x l, (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) → ∃ ta : Fin x.P.g → RR x (l - 1 * n), ∀ c', (show Γ(x.P.A.left, x.P.L.U c') from sg.f c') = ∑ i, (show Γ(x.P.A.left, x.P.L.U c') from (s i).f c') * (show Γ(x.P.A.left, x.P.L.U c') from (ta i).f c') := by
  first | exact @GlobalTheory.koszul_sections_exact_field | exact GlobalTheory.koszul_sections_exact_field | (intros; apply GlobalTheory.koszul_sections_exact_field <;> assumption)
end
