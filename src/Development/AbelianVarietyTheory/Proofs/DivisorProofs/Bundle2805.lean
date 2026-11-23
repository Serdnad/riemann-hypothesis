module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorAdd

open GlobalTheory.CechPic

variable {S S' : Scheme.{0}}

theorem comp_psum {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G))
    (x' : Fin n → (T' ⟶ G)) (h : ∀ i, u ≫ x i = x' i) (I : Finset (Fin n)) :
    u.left ≫ (psum G x I).left = (psum G x' I).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom u) x I).trans (congrArg (fun q => psum G q I) (funext h)))

theorem pull_lam {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (h : (abelian₂ G L).IsLB)
    (x y : T ⟶ G) :
    pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L) h) =
      pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
        pull (1 : T ⟶ G).left (cls L hL) := by
  have e := cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum G (x2 G) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) h
  refine (congrArg (pull (lift x y : T ⟶ G2 G).left) e).trans ?_

  rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left (cls L hL)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x y : T ⟶ G2 G) (x2 G) ![x, y] (fun i => by fin_cases i <;> simp [x2])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem cube {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (x x' y : T ⟶ G) :
    pull (x * x' * y).left (cls L.L L.isLB) - pull (x * x').left (cls L.L L.isLB) - pull (x * y).left (cls L.L L.isLB)
      - pull (x' * y).left (cls L.L L.isLB) + pull x.left (cls L.L L.isLB) + pull x'.left (cls L.L L.isLB)
      + pull y.left (cls L.L L.isLB) - pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have h : (Theta G L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have z : cls (Theta G L.L) h = 0 := (cls_eq_zero_iff h).2 ⟨c.t, c.isGen⟩
  have e := cls_linComb L.isLB (K := ULift.{0} (Finset (Fin 3))) (fun I => (psum G (x3 G) I.down).left)
    (fun I => (-1) ^ (3 - I.down.card)) h
  have e' := (congrArg (pull (lift x (lift x' y) : T ⟶ G3 G).left) (e.symm.trans z)).trans (map_zero _)
  refine Eq.trans (Eq.symm ?_) e'

  rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, x', y] I).left (cls L.L L.isLB)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x (lift x' y) : T ⟶ G3 G) (x3 G) ![x, x', y]
      (fun i => by fin_cases i <;> simp [x3])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, x', y] ∅ = 1 := rfl
  have p₁ : psum G ![x, x', y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x', y] {1} = x' := _root_.mul_one x'
  have p₃ : psum G ![x, x', y] {2} = y := _root_.mul_one y
  have p₄ : psum G ![x, x', y] {0, 1} = x * x' := congrArg (x * ·) (_root_.mul_one x')
  have p₅ : psum G ![x, x', y] {0, 2} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₆ : psum G ![x, x', y] {1, 2} = x' * y := congrArg (x' * ·) (_root_.mul_one y)
  have p₇ : psum G ![x, x', y] {0, 1, 2} = x * x' * y :=
    (congrArg (fun q => x * (x' * q)) (_root_.mul_one y)).trans (_root_.mul_assoc _ _ _).symm
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [neg_smul, one_smul]
  abel

theorem lam_add {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (h : (abelian₂ G L.L).IsLB)
    (x x' y : T ⟶ G) :
    pull (lift (x * x') y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) - pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h)
      - pull (lift x' y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) = 0 := by
  rw [pull_lam L.isLB, pull_lam L.isLB, pull_lam L.isLB, ← cube c x x' y]
  abel

theorem lift_square {G : Over S} {H : Over S'} [GrpObj G] [GrpObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x y : T ⟶ H) :
    (lift x y : T ⟶ G2 H).left ≫ κ = (lift (pushHom hp T x) (pushHom hp T y) : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
  have A : ∀ (p q : Over.mk (T.hom ≫ f) ⟶ G), p.left = x.left ≫ φ → q.left = y.left ≫ φ →
      (lift x y : T ⟶ G2 H).left ≫ κ = (lift p q : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
    intro p q hp' hq'
    apply pullback.hom_ext
    · show (_ ≫ κ) ≫ (fst G G).left = (lift p q ≫ fst G G).left
      rw [lift_fst, hp', Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ κ) ≫ (snd G G).left = (lift p q ≫ snd G G).left
      rw [lift_snd, hq', Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  exact A _ _ rfl rfl

theorem exists_gen {G G' : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj H]
    {L : RigLB G'} (c : CubicalStr G' L) (a b : G ⟶ G') [IsMonHom a] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x x' y : T ⟶ H) (ψ : Fin 3 → (T.left ⟶ (G2 H).left))
    (h₀ : ψ 0 = (lift (x * x') y : T ⟶ G2 H).left) (h₁ : ψ 1 = (lift x y : T ⟶ G2 H).left)
    (h₂ : ψ 2 = (lift x' y : T ⟶ G2 H).left) :
    ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' L.L).pull (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left).pull κ)
      (K := Fin 3) ψ ![1, -1, -1]), u.IsGen := by
  have hΛ : (abelian₂ G' L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have hP := pull_isLB (pull_isLB hΛ (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left) κ
  have key : ∀ p q : T ⟶ H, pull (lift p q : T ⟶ G2 H).left (cls _ hP) =
      pull (lift (pushHom hp T p ≫ a) (pushHom hp T q ≫ b) : Over.mk (T.hom ≫ f) ⟶ G2 G').left (cls _ hΛ) := by
    intro p q
    rw [cls_pull (pull_isLB hΛ _), cls_pull hΛ, ← pull_comp, ← pull_comp, lift_square hp hκ]
    refine congrArg (fun m => pull m (cls _ hΛ)) ?_
    refine congrArg (fun m : Over.mk (T.hom ≫ f) ⟶ G2 G' => m.left)
      (show lift (pushHom hp T p) (pushHom hp T q) ≫ lift (fst G G ≫ a) (snd G G ≫ b) = _ from ?_)
    simp
  refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
  rw [cls_linComb hP, Fin.sum_univ_three, h₀, h₁, h₂, key, key, key, map_mul, MonObj.mul_comp]
  have e := lam_add c hΛ (pushHom hp T x ≫ a) (pushHom hp T x' ≫ a) (pushHom hp T y ≫ b)
  refine Eq.trans ?_ e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    one_smul, neg_smul, sub_eq_add_neg]

end GlobalTheory.Mum.FactorAdd

theorem GlobalTheory.Mum.factorPairing_add : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F A' G' _ _ _ U' oA oG _ G _ _ _ inc pr hinc _ _ _ κ₀ hκ
  exact GlobalTheory.Mum.FactorAdd.exists_gen U'.cubG inc (inc ≫ oG.act F.f) (isGrpPullback_pullback G (jK R)) hκ
    (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) _ rfl rfl
    (by rw [lift_comp_fst_snd]; rfl)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Emb.chart_injective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ z w : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over w = pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over z → w = z := by
  intro R _ _ _ _ M G' _ _ _ E z w hz hwz

  set p := PSpace.str R E.N
  set Φ : E.H.toScheme ⟶ pullback p M.π := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over with hΦ
  set s := G'.hom (E.H.ι z) with hs

  let Ω := M.S.residueField s
  let x : Sp Ω ⟶ M.S := M.S.fromSpecResidueField s
  let φ : R →+* Ω := (Spec.preimage (x ≫ M.π)).hom
  have hφ : spMap φ = x ≫ M.π := by unfold spMap; simp [φ]
  have hker : ∀ r ∈ maximalIdeal R, φ r = 0 := by
    intro r hr
    obtain ⟨pt⟩ : Nonempty (Sp Ω) := inferInstance
    have h1 : (x ≫ M.π) pt = closedPoint R := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hz
    rw [← hφ] at h1
    have h2 : (spMap φ) pt = PrimeSpectrum.comap φ pt := rfl
    have h3 : pt.asIdeal = ⊥ := by haveI := pt.isPrime; exact Ideal.eq_bot_of_prime _
    have h4 : r ∈ ((spMap φ) pt).asIdeal := by rw [h1]; exact hr
    rw [h2] at h4
    change φ r ∈ pt.asIdeal at h4
    rw [h3] at h4
    exact h4
  let κ : ResidueField R →+* Ω := Ideal.Quotient.lift (maximalIdeal R) φ hker
  have hκ : κ.comp (residue R) = φ := by ext r; rfl
  have hx : x ≫ M.π = spMap (κ.comp (residue R)) := by rw [hκ, hφ]
  obtain ⟨Ω', _, io, e, l, -, hl, hlf⟩ := E.fib Ω x κ hx

  have hx'π : (spMap io ≫ x) ≫ M.π = spMap (io.comp κ) ≫ spMap (residue R) := by
    rw [Category.assoc, hx]; unfold spMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hψ : (l ≫ Φ) ≫ pullback.snd p M.π = pullback.snd G'.hom (spMap io ≫ x) ≫ (spMap io ≫ x) := by
    have : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    rw [Category.assoc, this, ← Category.assoc, hl]; exact pullback.condition
  let ψ : pullback G'.hom (spMap io ≫ x) ⟶ pullback (pullback.snd p M.π) (spMap io ≫ x) :=
    pullback.lift (l ≫ Φ) (pullback.snd _ _) hψ

  have hψinj : Function.Injective ψ := by
    haveI : IsImmersion E.j := E.imm
    let h : pullback (pullback.snd p M.π) (spMap io ≫ x) ⟶ PSpace R E.N := pullback.fst _ _ ≫ pullback.fst _ _
    have hΦf : Φ ≫ pullback.fst p M.π = E.f := by rw [hΦ]; exact pullback.lift_fst _ _ _
    have hψ1 : ψ ≫ pullback.fst _ _ = l ≫ Φ := pullback.lift_fst _ _ _
    have hψh : ψ ≫ h = l ≫ E.f := by
      show ψ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
      rw [← Category.assoc, hψ1, Category.assoc, hΦf]
    have hθ : (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = ψ ≫ h := by
      rw [hψh, hlf, Category.assoc]
    let θ : pullback G'.hom (spMap io ≫ x) ⟶ pullback E.j h := pullback.lift _ _ hθ
    haveI : Mono (spMap (residue R)) := by
      have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
      infer_instance
    have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    have hρ : pullback.fst E.j h ≫ E.Y.hom = (pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ) := by
      rw [← cancel_mono (spMap (residue R))]
      calc pullback.fst E.j h ≫ E.Y.hom ≫ spMap (residue R) = pullback.fst E.j h ≫ E.j ≫ p := by rw [E.j_over]
        _ = pullback.snd E.j h ≫ h ≫ p := by rw [← Category.assoc, pullback.condition, Category.assoc]
        _ = pullback.snd E.j h ≫ pullback.fst _ _ ≫ pullback.snd p M.π ≫ M.π := by
          simp only [h, Category.assoc]; rw [pullback.condition]
        _ = pullback.snd E.j h ≫ pullback.snd _ _ ≫ (spMap io ≫ x) ≫ M.π := by
          rw [← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]
        _ = ((pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ)) ≫ spMap (residue R) := by
          rw [hx'π]; simp only [Category.assoc]
    let ρ : pullback E.j h ⟶ pullback E.Y.hom (spMap (io.comp κ)) := pullback.lift _ _ hρ
    have hθ1 : θ ≫ pullback.fst E.j h = e.hom.left ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hθ2 : θ ≫ pullback.snd E.j h = ψ := pullback.lift_snd _ _ _
    have hρ1 : ρ ≫ pullback.fst _ _ = pullback.fst E.j h := pullback.lift_fst _ _ _
    have hρ2 : ρ ≫ pullback.snd _ _ = pullback.snd E.j h ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
    have hψ2 : ψ ≫ pullback.snd _ _ = pullback.snd G'.hom (spMap io ≫ x) := pullback.lift_snd _ _ _
    have hθρ : θ ≫ ρ = e.hom.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hρ1, hθ1]
      · rw [Category.assoc, hρ2, ← Category.assoc, hθ2, hψ2]
        exact (Over.w e.hom).symm
    intro a b hab
    have h1 : θ a = θ b := by
      apply (pullback.snd E.j h).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hab
    have h2 : e.hom.left a = e.hom.left b := by
      rw [← hθρ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1]
    have h3 := congrArg e.inv.left h2
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, e.hom_inv_id, Over.id_left] at h3

  obtain ⟨τ⟩ : Nonempty (Sp Ω') := inferInstance
  have hτ : (spMap io ≫ x) τ = s := by
    rw [Scheme.Hom.comp_apply]; exact Scheme.fromSpecResidueField_apply _ _
  have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
  have hq : pullback.snd p M.π (Φ z) = (spMap io ≫ x) τ := by
    rw [hτ, ← Scheme.Hom.comp_apply, hΦs, Scheme.Hom.comp_apply]
  obtain ⟨c, hc1, hc2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd p M.π) (g := spMap io ≫ x) _ _ hq

  have hm : (pullback.fst Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ E.H.ι) ≫ G'.hom =
      (pullback.snd Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ pullback.snd _ _) ≫ (spMap io ≫ x) := by
    rw [Category.assoc, ← hΦs, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
      Category.assoc]
  let m : pullback Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ⟶ pullback G'.hom (spMap io ≫ x) :=
    pullback.lift _ _ hm
  have hm1 : m ≫ l = pullback.fst _ _ := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl]; exact pullback.lift_fst _ _ _
  have hm2 : m ≫ ψ = pullback.snd _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hm1, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd]; exact pullback.lift_snd _ _ _
  have lift_pt : ∀ u : E.H.toScheme, Φ u = Φ z → ∃ a, l a = u ∧ ψ a = c := by
    intro u hu
    obtain ⟨pu, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Φ) (g := pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) u c (hu.trans hc1.symm)
    exact ⟨m pu, by rw [← Scheme.Hom.comp_apply, hm1, h1], by rw [← Scheme.Hom.comp_apply, hm2, h2]⟩
  obtain ⟨a, ha1, ha2⟩ := lift_pt w hwz
  obtain ⟨b, hb1, hb2⟩ := lift_pt z rfl
  rw [← ha1, ← hb1, hψinj (ha2.trans hb2.symm)]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem emb_lift_sep_loft_qc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G',
    IsSeparated (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      LocallyOfFiniteType (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      QuasiCompact (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) := by
  intro R _ _ _ hR M G' _ _ hG E
  have : IsNoetherianRing R := hR.1
  have : Smooth G'.hom := hG.smooth
  have : IsSeparated G'.hom := hG.separated
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : IsProper M.π := M.proper
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : IsProper (PSpace.str R E.N) := isProper_str R E.N
  set φ := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over
  have hφ : φ ≫ pullback.snd (PSpace.str R E.N) M.π = E.H.ι ≫ G'.hom := pullback.lift_snd _ _ _
  have h1 : IsSeparated (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h2 : LocallyOfFiniteType (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h3 : QuasiCompact (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  exact ⟨IsSeparated.of_comp φ (pullback.snd _ _), locallyOfFiniteType_of_comp φ (pullback.snd _ _),
    QuasiCompact.of_comp φ (pullback.snd _ _)⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finpt_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  intro R _ _ _ hR Z π _ k hk
  obtain ⟨⟨hN, -, -, hC⟩, -⟩ := hR
  haveI := hN
  haveI := hC
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let i : Spec Γ(Z, ⊤) ≅ Z := Z.isoSpec.symm
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (i.hom ≫ π)
  have h₁ : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ i.inv)
  have hc : θ ≫ ψ = CommRingCat.ofHom (algebraMap R (Kb R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hθ, Category.assoc, i.inv_hom_id_assoc, hk]
    simp only [TF, jFK, jK, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let _ : Algebra R Γ(Z, ⊤) := θ.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) := h₁
  let φ : Γ(Z, ⊤) →ₐ[R] Kb R := ⟨ψ.hom, fun r => congr(($hc).hom r)⟩
  let S : Subalgebra R (Kb R) := φ.range
  have hfin : Module.Finite R S :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hloc : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  refine ⟨S, hfin, hloc, spMap (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ i.hom, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    congr 1
    ext r
    exact congrArg Subtype.val (φ.rangeRestrict.commutes r)
  · rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ CommRingCat.ofHom (S.val : S →+* Kb R) = ψ := by
      ext b; rfl
    rw [this, hψ, Category.assoc, i.inv_hom_id, Category.comp_id]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CompletedStalk

theorem essFiniteType_int_stalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o' := M.s x
  letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h := ((h₀.comp h₂).comp h₁)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  exact RingHom.ext_int _ _

end GlobalTheory.Poinc.CompletedStalk

theorem GlobalTheory.Poinc.CompletedStalk.exists_completion_unif : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧ ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  intro o' Ω _ _ _ hA S ρ hB M U₀ EE FinalForm hAdm hEE x hx
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hAdm.1.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _,
    isGrpPullback_pullback _ _, hL, hP⟩
end
end
