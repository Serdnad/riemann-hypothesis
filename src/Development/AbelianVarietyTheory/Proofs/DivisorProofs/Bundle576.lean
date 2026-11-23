module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle522
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle524
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle525
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle520
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

abbrev sq : A ⟶ A := (𝟙 A) ^ 2

theorem comp_sq {T : Over S} (x : T ⟶ A) : x ≫ sq A = x ^ 2 := by
  rw [sq, MonObj.comp_pow, Category.comp_id]

abbrev Two : Over S := pullback (sq A) η[A]

abbrev incl : Two A ⟶ A := pullback.fst _ _

variable {A}

theorem incl_sq {T : Over S} (u : T ⟶ Two A) : (u ≫ incl A) ^ 2 = 1 := by
  rw [← comp_sq, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

def kpt {T : Over S} (x : T ⟶ A) (hx : x ^ 2 = 1) : T ⟶ Two A :=
  pullback.lift x (toUnit _) (by rw [comp_sq, hx, Hom.one_def])

@[simp, reassoc] theorem kpt_incl {T : Over S} (x : T ⟶ A) (hx : x ^ 2 = 1) : kpt x hx ≫ incl A = x :=
  pullback.lift_fst _ _ _

theorem two_ext {T : Over S} {u v : T ⟶ Two A} (h : u ≫ incl A = v ≫ incl A) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

variable (A)

def twoFun : (Over S)ᵒᵖ ⥤ CommGrpCat.{0} where
  obj T := CommGrpCat.of (MonoidHom.ker (powMonoidHom 2 : (Opposite.unop T ⟶ A) →* (Opposite.unop T ⟶ A)))
  map φ := CommGrpCat.ofHom
    { toFun := fun x => ⟨φ.unop ≫ x.1, by
        show (φ.unop ≫ x.1) ^ 2 = 1
        rw [← MonObj.comp_pow, show x.1 ^ 2 = 1 from x.2, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp φ ψ := by ext x; exact Category.assoc _ _ _

def twoRep : (twoFun A ⋙ forget _).RepresentableBy (Two A) where
  homEquiv {T} :=
    { toFun := fun u => (⟨u ≫ incl A, incl_sq u⟩ : MonoidHom.ker (powMonoidHom 2 : (T ⟶ A) →* (T ⟶ A)))
      invFun := fun x => kpt x.1 x.2
      left_inv := fun u => two_ext (kpt_incl _ _)
      right_inv := fun x => Subtype.ext (kpt_incl _ _) }
  homEquiv_comp {T T'} f u := Subtype.ext (Category.assoc _ _ _)

instance : CommGrpObj (Two A) := CommGrpObj.ofRepresentableBy _ (twoFun A) (twoRep A)

variable {A}

theorem mul_incl {T : Over S} (x y : T ⟶ Two A) : (x * y) ≫ incl A = (x ≫ incl A) * (y ≫ incl A) := by
  have h := ((yonedaGrpObjIsoOfRepresentableBy (Two A) (twoFun A ⋙ forget₂ CommGrpCat GrpCat)
    (twoRep A)).hom.app (Opposite.op T)).hom.map_mul x y
  exact congrArg Subtype.val h

end GlobalTheory.TwoTors

namespace GlobalTheory.TwoTors

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem sq_w : (sq A).left ≫ A.hom = A.hom := Over.w _

abbrev pairO : Over S := Over.mk (pullback.fst (sq A).left (sq A).left ≫ A.hom)

abbrev tripO : Over S :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (sq A).left (sq A).left ≫ A.hom :
    GlobalTheory.LBDescent.Triple (sq A).left ⟶ S)

theorem snd_w : pullback.snd (sq A).left (sq A).left ≫ A.hom = pullback.fst (sq A).left (sq A).left ≫ A.hom := by
  rw [← sq_w A, pullback.condition_assoc]

def s₁ : pairO A ⟶ A := Over.homMk (pullback.fst _ _) rfl

def s₂ : pairO A ⟶ A := Over.homMk (pullback.snd _ _) (snd_w A)

theorem s_sq : s₁ A ≫ sq A = s₂ A ≫ sq A := Over.OverMorphism.ext pullback.condition

def t₁ : tripO A ⟶ A := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) rfl

def t₂ : tripO A ⟶ A := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  show (pullback.fst _ _ ≫ pullback.snd _ _) ≫ A.hom = _
  rw [Category.assoc, snd_w]; rfl)

def t₃ : tripO A ⟶ A := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  show (pullback.snd _ _ ≫ pullback.snd _ _) ≫ A.hom = _
  rw [Category.assoc, snd_w, ← pullback.condition_assoc, snd_w]; rfl)

theorem t₁₂_sq : t₁ A ≫ sq A = t₂ A ≫ sq A :=
  Over.OverMorphism.ext (by
    show (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (sq A).left = (pullback.fst _ _ ≫ pullback.snd _ _) ≫ (sq A).left
    rw [Category.assoc, Category.assoc, pullback.condition])
theorem t₂₃_sq : t₂ A ≫ sq A = t₃ A ≫ sq A :=
  Over.OverMorphism.ext (by
    show (pullback.fst _ _ ≫ pullback.snd _ _) ≫ (sq A).left = (pullback.snd _ _ ≫ pullback.snd _ _) ≫ (sq A).left
    simp only [Category.assoc]
    have e := pullback.condition (f := pullback.snd (sq A).left (sq A).left) (g := pullback.fst (sq A).left (sq A).left)
    rw [reassoc_of% e, pullback.condition])

variable {A}

def dif {T : Over S} (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) : T ⟶ Two A :=
  kpt (a⁻¹ * b) (by rw [mul_pow, inv_pow, ← comp_sq, ← comp_sq, h, inv_mul_cancel])

@[simp, reassoc] theorem dif_incl {T : Over S} (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) :
    dif a b h ≫ incl A = a⁻¹ * b := kpt_incl _ _

variable (A)

def ψ : tripO A ⟶ Two A ⊗ Two A := lift (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))

def δ : pairO A ⟶ Two A := dif (s₁ A) (s₂ A) (s_sq A)

end GlobalTheory.TwoTors
end
end

section

open GlobalTheory.SliceSchwartz
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOp
open GlobalTheory.SliceSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem contDiff_qOp_nat (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ), ContDiff ℝ n (qOp P f) := by
  induction n with
  | zero => intro P f; exact contDiff_zero.2 (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).1.continuous
  | succ n ih =>
    intro P f
    obtain ⟨hd, hf⟩ := GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f
    have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiff_succ_iff_fderiv_apply]
    refine ⟨hd, by simp, fun v => ?_⟩
    have : (fun s => fderiv ℝ (qOp P f) s v) = fun s =>
        qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s :=
      funext fun s => hf s v
    rw [this]
    exact (ih _ _).add (ih _ _)

theorem contDiff_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) : ContDiff ℝ ∞ (qOp P f) :=
  contDiff_infty.2 fun n => contDiff_qOp_nat n P f

theorem decay_qOp (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ),
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P f) z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by
  induction n with
  | zero =>
    intro P k
    obtain ⟨s, C, hC, h⟩ := GlobalTheory.T.partial_operator_schwartz_seminorm_bound V κ κ' κ₁' P k
    exact ⟨s, C, hC, fun f z => by rw [norm_iteratedFDeriv_zero]; exact h f z⟩
  | succ n ih =>
    intro P k
    obtain ⟨CE, hCE, hE⟩ := GlobalTheory.T.iterated_derivative_bound_by_partials (κ ⊕ κ₁' → V)
    set b := Module.finBasis ℝ (κ ⊕ κ₁' → V)
    obtain ⟨s1, C1, hC1, h1⟩ := ih P k
    choose s1' C1' hC1' h1' using fun i => clm_sup_bound (pd (padL (κ' := κ') (b i ∘ Sum.inl))) s1
    choose s2 C2 hC2 h2 using fun i => ih ((pd (b i ∘ Sum.inr)).comp P) k
    refine ⟨Finset.univ.sup (fun i => s1' i ∪ s2 i), CE * ∑ i, (C1 * C1' i + C2 i),
      mul_nonneg hCE (Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg hC1 (hC1' i)) (hC2 i)), fun f z => ?_⟩
    set p := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ
    set S := (Finset.univ.sup (fun i => s1' i ∪ s2 i)).sup p f
    have hmono : ∀ i (t : Finset (ℕ × ℕ)), t ⊆ s1' i ∪ s2 i → t.sup p f ≤ S := by
      intro i t ht
      exact Seminorm.le_def.1 (Finset.sup_mono (ht.trans
        (Finset.le_sup (f := fun i => s1' i ∪ s2 i) (Finset.mem_univ i)))) f
    have key : ∀ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖
        ≤ (C1 * C1' i + C2 i) * S := by
      intro i
      have hfun : (fun w => fderiv ℝ (qOp P f) w (b i)) =
          qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) + qOp ((pd (b i ∘ Sum.inr)).comp P) f :=
        funext fun w => (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).2 w (b i)
      rw [hfun, iteratedFDeriv_add_apply (contDiff_qOp_nat n _ _).contDiffAt (contDiff_qOp_nat n _ _).contDiffAt]
      have e1 := h1 (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) z
      have e1' := h1' i f
      have e2 := h2 i f z
      have m1 := hmono i (s1' i) Finset.subset_union_left
      have m2 := hmono i (s2 i) Finset.subset_union_right
      have hz : 0 ≤ ‖z‖ ^ k := by positivity
      calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z +
              iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖
          ≤ ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z‖ +
              ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖ := by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hz
        _ ≤ C1 * (C1' i * S) + C2 i * S := by
            refine add_le_add (e1.trans (mul_le_mul_of_nonneg_left (e1'.trans
              (mul_le_mul_of_nonneg_left m1 (hC1' i))) hC1)) (e2.trans (mul_le_mul_of_nonneg_left m2 (hC2 i)))
        _ = (C1 * C1' i + C2 i) * S := by ring
    have hz : 0 ≤ ‖z‖ ^ k := by positivity
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (qOp P f) z‖
        ≤ ‖z‖ ^ k * (CE * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖) :=
          mul_le_mul_of_nonneg_left (hE _ (contDiff_qOp P f) n z) hz
      _ = CE * ∑ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ CE * ∑ i, (C1 * C1' i + C2 i) * S :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i) hCE
      _ = (CE * ∑ i, (C1 * C1' i + C2 i)) * S := by rw [mul_assoc, Finset.sum_mul]

end GlobalTheory.SliceOp

open GlobalTheory.SliceOp in
theorem GlobalTheory.SliceOp.exists_tensor_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  intro V _ _ _ κ κ' κ₁' _ _ _ P
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f => qOp P f) ?_ ?_ ?_ ?_, fun f s => rfl⟩
  · intro f g s
    simp only [qOp, ← sliceRL_apply, map_add (f := _), SchwartzMap.add_apply]
  · intro a f s
    simp only [qOp, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]
  · intro f; exact contDiff_qOp P f
  · rintro ⟨k, n⟩; exact decay_qOp n P k
end
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

abbrev upPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2

theorem relIndex_unipLat {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c C : Fin n → Fin n → ℤ}
    (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) = q ^ ∑ p ∈ upPairs n, (C p.1 p.2 - c p.1 p.2).toNat := by
  rw [Cayley.relIndex_unipLat L ϖ σ q n h c C hc hC hI]
  have h1 := relIndex_upLat_eq_sq L ϖ σ q n h c C hc.1 hC.1 hI.1
  rw [UpLatIndex.relIndex_upLat L ϖ σ q n h c C hI.1, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm, pow_mul] at h1
  exact (Nat.pow_left_injective two_ne_zero h1).symm

theorem v_eq_exp {x : L} (hx : x ≠ 0) : Valued.v x = WithZero.exp (-ordL x) := by
  rw [ordL_eq, neg_neg, WithZero.exp_log (by simpa using hx)]

theorem exists_idealWeight {c : Fin n → Fin n → ℤ} :
    ∃ C : Fin n → Fin n → ℤ, IsWeight C ∧ IsIdealWeight c C ∧ IsIdealWeight (fun _ _ => 0) C := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i j, |c i j| ≤ M := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun p : Fin n × Fin n => (c p.1 p.2).natAbs).bddAbove
    exact ⟨M, fun i j => by
      have : (c i j).natAbs ≤ M := hM ⟨(i, j), rfl⟩
      rw [← Int.natCast_natAbs]; exact_mod_cast this⟩
  have key : ∀ d : Fin n → Fin n → ℤ, (∀ i j, |d i j| ≤ M) →
      IsIdealWeight d fun i j => (M : ℤ) * (n + i.val - j.val) := by
    intro d hd
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    refine ⟨fun i j _ => ?_, fun i j k h1 _ => ?_, fun i j k _ h2 => ?_⟩
    · have h1 : (1 : ℤ) ≤ n + i.val - j.val := by have := j.2; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ j.val - i.val := by have := Fin.lt_def.1 h1; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ k.val - j.val := by have := Fin.lt_def.1 h2; omega
      nlinarith [abs_le.1 (hd j k)]
  refine ⟨_, ⟨fun i j => ?_, fun i j k _ _ => ?_⟩, key c hM, key _ fun _ _ => by simp⟩
  · have := i.2
    have := j.2
    simp only [Fin.val_rev]
    congr 1
    omega
  · have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    have h1 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith

theorem sum_upPairs (a : Fin n → ℤ) :
    ∑ p ∈ upPairs n, (a p.1 - a p.2) = ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ p ∈ upPairs n, a p.1 = ∑ i, a i * ((n : ℤ) - 1 - i.val) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul, mul_comm]
    congr 1
    have := i.2
    omega
  have h2 : ∑ p ∈ upPairs n, a p.2 = ∑ i, a i * (i.val : ℤ) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_half (a : Fin n → ℤ) (ha : ∀ i, a i.rev = -a i) :
    ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) =
      2 * ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) =
      ∑ i : Fin n, if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => Fin.castLE (Nat.div_le_self n 2) i) (fun i _ => by simp)
      (fun i _ j _ e => Fin.castLE_injective _ e) (fun j hj => ⟨⟨j.val, by simpa using hj⟩, by simp, rfl⟩)
      fun i _ => rfl
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin n => if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0),
    h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  have hr : ((i.rev.val : ℕ) : ℤ) = n - 1 - i.val := by rw [Fin.val_rev]; omega
  simp only [Fin.revPerm_apply, ha, hr]
  split_ifs with h1 h2 h2
  · omega
  · ring
  · ring
  · have : (n : ℤ) - 1 - 2 * i.val = 0 := by omega
    simp [this]

theorem zpow_finset_sum {ι : Type} {z : ℂ} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFirst.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFirst.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFirst.main ..)

end GlobalTheory.BorelUMod
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem twoCocycle_coboundary_of_basisFunctor_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T z hz
  classical
  obtain ⟨n, d, hd, hcT⟩ := hcov T
  have hpt : ∀ i : Fin n, ∃ (p : C') (_ : T ⟶ G.obj p), ∀ S (u : T ⟶ S),
      IsUnit (mp F u (d i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H T (d i)
    obtain ⟨p, v, w, -⟩ := hcT i T' l hl
    exact ⟨p, v, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p v hp using hpt
  obtain ⟨f, hf⟩ := GlobalTheory.T.twoCocycle_comma_coboundary_of_standardCover_alt F G H hcov hdir T n d hd z hz
    fun i ↦ GlobalTheory.T.twoCocycle_coboundary_on_unitLocus_piece F G H hdir T (d i) (p i) (v i) (hp i) z hz
  have hup : ∀ t (u : T ⟶ G.obj t) t' t'' (a : t ⟶ t') (b : t' ⟶ t''),
      (∃ i, IsUnit (mp F (u ≫ G.map a) (d i))) → ∃ i, IsUnit (mp F (u ≫ G.map (a ≫ b)) (d i)) := by
    rintro t u t' t'' a b ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [G.map_comp, ← Category.assoc, mp_comp]
    exact hi.map _
  obtain ⟨h, hh⟩ := Desc.coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t)
    (fun u a ↦ u ≫ G.map a) (fun u a b ↦ by simp only [Functor.map_comp, Category.assoc])
    (fun _ _ ↦ True) (fun t u ↦ ∃ i, IsUnit (mp F u (d i))) (fun _ _ _ _ _ ↦ trivial)
    (fun t u _ ↦ GlobalTheory.T.eq_zero_of_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c) f
    (fun t t' t'' u a b hi ↦ hf t t' t'' u a b hi)
  exact ⟨h, fun t t' t'' u a b ↦ hh t t' t'' u a b trivial⟩

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.exists_integral_closedBall_addChar_eq_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  first | exact @GlobalTheory.KSp.exists_integral_cball_char_eq_zero | exact GlobalTheory.KSp.exists_integral_cball_char_eq_zero | (intros; apply GlobalTheory.KSp.exists_integral_cball_char_eq_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin

theorem _root_.GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation : ∀ {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X) (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K) (m : ι → K), (∀ a s, (θc a s).fst = ψ s) → (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) → ∀ (O : X.Opens) (f : Γ(X, O)) (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O), (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  first | exact @GlobalTheory.DualEval.evalPt_snd_sum | exact GlobalTheory.DualEval.evalPt_snd_sum | (intros; apply GlobalTheory.DualEval.evalPt_snd_sum <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.norm_trace_form_det_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → |((Algebra.norm ℚ (Matrix.of fun i j => Matrix.trace (e i * e j)).det : ℚ) : ℝ)| = (((lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) : ℝ) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2) ^ 2 := by
  first | exact @GlobalTheory.LieIndex.abs_norm_gram_eq_index | exact GlobalTheory.LieIndex.abs_norm_gram_eq_index | (intros; apply GlobalTheory.LieIndex.abs_norm_gram_eq_index <;> assumption)
end
