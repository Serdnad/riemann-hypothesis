module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum

theorem exists_secK_of_iso_pull : ∀ {X X' : Scheme.{0}} (L : LB X) (L' : LB X') (f : X' ⟶ X) (w : LB.Iso L' (L.pull f)), L.IsLB → L'.IsLB → w.IsGen → ∀ (N : ℕ) (t : H0 L' N), ∃ s : SecK L f N, ∀ (Z : Scheme.{0}) (p : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' → sval s p z J = (gw w p z (J (p ≫ f)) (J' p) ^ N).val * sval t p z J' := by
  intro X X' L L' f w hL hL' hw N t
  have hp := (isGen_iff w).1 hw
  have mL : ∀ (j : Fin 1 → L.ι) (x : X'), x ∈ LB.wchart L (fun _ : Fin 1 => f) j → f x ∈ L.U (j 0) :=
    fun j x hx => Set.mem_iInter.1 hx 0
  have mL' : ∀ (k : L'.ι) (x : X'), x ∈ L'.U k → x ∈ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) :=
    fun k x hx => Set.mem_iInter.2 fun _ => hx
  have indep : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k k' : L'.ι), f (r z) ∈ L.U j → r z ∈ L'.U k →
      r z ∈ L'.U k' →
      (gw w r z j k ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) =
      (gw w r z j k' ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k')) (t.f (fun _ => k')) := by
    intro Z r z j k k' hj hk hk'
    rw [sec_trans t r z (mL' k _ hk) (mL' k' _ hk'), hp Z r z j j k k' hj hj hk hk', gm_self hL (r ≫ f) z hj,
      ← _root_.mul_assoc, ← Units.val_mul, trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast, ← mul_pow, _root_.one_mul,
      mul_right_comm, inv_mul_cancel, _root_.one_mul]
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X', LB.wchart L (fun _ : Fin 1 => f) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (k : L'.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => f) j → r z ∈ L'.U k →
      gs r z _ a = (gw w r z (j 0) k ^ N).val *
        gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) := by
    intro j
    let W : L'.ι → X'.Opens := fun k => LB.wchart L (fun _ : Fin 1 => f) j ⊓ L'.U k
    have l₁ : ∀ k, W k ≤ (L.pull f).U (fun _ => j 0) ⊓ L'.U k := fun k x hx => ⟨mem_pull.2 (mL j x hx.1), hx.2⟩
    have l₂ : ∀ k, W k ≤ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) := fun k x hx => mL' k x hx.2
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) k, r z ∈ W k →
        gs r z (W k) (u k) = (gw w r z (j 0) k ^ N).val *
          gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) :=
      ⟨fun k => (res (l₁ k) (w.s (fun _ => j 0, k)) ^ N).val *
          (X'.presheaf.map (homOfLE (l₂ k)).op).hom (t.f (fun _ => k)), fun Z r z k hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_pow _ _ _).trans (congrArg (· ^ N) (gm_res r z (l₁ k) hz _)))))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (LB.wchart L (fun _ : Fin 1 => f) j)
      (fun k => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' y
        exact Opens.mem_iSup.2 ⟨k, hy, hk⟩) u
      (fun k k' => fn_ext (V := W k ⊓ W k') fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu _ _ y k hy.1, hu _ _ y k' hy.2]
        exact indep _ (𝟙 X') y (j 0) k k' (mL j y hy.1.1) hy.1.2 hy.2.2)
    refine ⟨a, fun Z r z k h₁ h₂ => ?_⟩
    have hz : r z ∈ W k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W k)) (ha k)).trans (hu Z r z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X') y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X') y j j' hy.1 hy.2)))
      (gs_res (𝟙 X') y _ hy _))).symm)
    refine (ha j _ (𝟙 X') y k hy.1 hk).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 X') y k hy.2 hk)).symm)
    rw [hp _ (𝟙 X') y (j 0) (j' 0) k k (mL j y hy.1) (mL j' y hy.2) hk hk, gm_self hL' (𝟙 X') y hk, inv_one, _root_.mul_one,
      mul_pow, Units.val_mul, _root_.mul_assoc, Fin.prod_univ_one, zpow_natCast]
  · rw [sval_of t r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => f) r) (hJ' r)

end GlobalTheory.Mum
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeStep

section Gens

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def zpowGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ) :
    LB.Gen (LB.LinComb L φ (fun k => n * ε k)) where
  s := fun j => t.s j ^ n

theorem zpowGen_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    (zpowGen L φ ε t n).IsGen := fun i j => by
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _)))

theorem val_zpowGen {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ)
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) : val (zpowGen L φ ε t n) r z J = val t r z J ^ n :=
  map_zpow _ _ _

theorem finProdGen_isGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProdGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Gens

theorem prod_zpow_mul {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) (n : ℤ) :
    ∏ k, f k ^ (n * e k) = (∏ k, f k ^ e k) ^ n := by
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem prod_finset_fin_two_ulift_expand {U : Type} [CommMonoid U] (f : ULift.{0} (Finset (Fin 2)) → U) :
    ∏ I, f I = f ⟨{0, 1}⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨∅⟩ := by
  refine (Fintype.prod_equiv Equiv.ulift f (fun I => f ⟨I⟩) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ac_rfl

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

theorem groupSchemePartialSum_pair_both : psum B' (x2 B') {0, 1} = fst B' B' * snd B' B' := congrArg (fst B' B' * ·) (_root_.mul_one _)
theorem psum0 : psum B' (x2 B') {0} = fst B' B' := _root_.mul_one _
theorem psum1 : psum B' (x2 B') {1} = snd B' B' := _root_.mul_one _
theorem psumE : psum B' (x2 B') ∅ = 1 := rfl

theorem pair_eq {r : ℕ} (pr : Fin r → (B' ⟶ B)) (hpr : ∀ i, IsMonHom (pr i)) (w : ℤ) (i j : Fin r) {U : Type}
    [CommGroup U] (h : ((G2 B').left ⟶ B.left) → U) :
    ∏ k : thK.{0} ⊕ (thK.{0} ⊕ thK.{0}), h (Sum.elim
      (fun k => (lift (fst B' B' ≫ pr i) (lift (snd B' B' ≫ pr i) ((fst B' B' ≫ pr j) * (snd B' B' ≫ pr j)))).left ≫
        thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (fst B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (snd B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)) k) ^
      (-w * Sum.elim thε (Sum.elim thε thε) k) =
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr i) (snd B' B' ≫ pr j) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr j) (snd B' B' ≫ pr i) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
      h ((psum B' (x2 B') I.down).left ≫ tensφ pr ((i, j), k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-w) := by
  haveI := hpr i
  haveI := hpr j
  refine (prod_zpow_mul (U := U) _ (Sum.elim thε (Sum.elim thε thε)) (-w)).trans ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_cub, prod_cub, prod_cub]
  simp only [prod_finset_fin_two_ulift_expand, Fin.prod_univ_four, GlobalTheory.PolDeg.lamPts, tensφ, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, groupSchemePartialSum_pair_both, psum0, psum1, psumE]
  have q2 : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  have q0 : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q1 : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have qe : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  simp only [q2, q0, q1, qe, ← Over.comp_left, MonObj.comp_mul, MonObj.mul_comp, MonObj.one_comp, MonObj.comp_one,
    _root_.mul_one, _root_.one_mul]
  generalize fst B' B' ≫ pr i = a
  generalize snd B' B' ≫ pr i = b
  generalize fst B' B' ≫ pr j = c
  generalize snd B' B' ≫ pr j = d
  rw [mul_comm (c * d) a, mul_comm c a, mul_comm d a, mul_comm (c * d) b, mul_comm d b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

def lamV {T : Over S} {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) (u v : T ⟶ B) : U :=
  ∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts u v k) ^ Oε k

def pairGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B))
    (p : Fin r × Fin r) :=
  zpowGen L.L _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε cb.t
      (lift (fst B' B' ≫ pr p.1) (lift (snd B' B' ≫ pr p.1) ((fst B' B' ≫ pr p.2) * (snd B' B' ≫ pr p.2)))).left)
    (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (fst B' B' ≫ pr p.1))).left)
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1))).left)))
    (-W p.1 p.2)

theorem pairGen_isGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (pr : Fin r → (B' ⟶ B)) (p : Fin r × Fin r) : (pairGen cb W pr p).IsGen :=
  zpowGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _) (DVR.pullGen_isGen _ _ _ _ cb.isGen _))) _

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum


open CubeStep in
theorem cube_step : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  intro S B B' _ _ _ _ L cb r W pr hpr
  have hfe : FormEq (fun q : (Fin r × Fin r) × (thK.{0} ⊕ (thK.{0} ⊕ thK.{0})) => Sum.elim
      (fun k => (lift (fst B' B' ≫ pr q.1.1) (lift (snd B' B' ≫ pr q.1.1)
        ((fst B' B' ≫ pr q.1.2) * (snd B' B' ≫ pr q.1.2)))).left ≫ thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (fst B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (snd B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)) q.2)
      (fun q => -W q.1.1 q.1.2 * Sum.elim thε (Sum.elim thε thε) q.2)
      (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2)
        (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2))
      (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)
        (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2))) := by
    intro U _ h
    have h1 : ∏ q : (Fin r × Fin r) × Fin 4,
        h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr q.1.1) (snd B' B' ≫ pr q.1.2) q.2) ^ ((W + W.transpose) q.1.1 q.1.2 * Oε q.2) =
        (∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ Oε k) ^
          W p.1 p.2) *
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1) k) ^ Oε k) ^
          W p.1 p.2 := by
      calc _ = ∏ p : Fin r × Fin r, ∏ k : Fin 4,
            h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ ((W + W.transpose) p.1 p.2 * Oε k) :=
          Fintype.prod_prod_type _
        _ = ∏ p : Fin r × Fin r, (lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.1 p.2 *
            lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.2 p.1) :=
          Finset.prod_congr rfl fun p _ => by
            rw [prod_zpow_mul, Matrix.add_apply, Matrix.transpose_apply, zpow_add]; rfl
        _ = _ := by
          rw [Finset.prod_mul_distrib]
          exact congrArg _ (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl)
    have h2 : ∏ q : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4),
        h ((psum B' (x2 B') q.1.down).left ≫ tensφ pr q.2) ^ (-((-1) ^ (2 - q.1.down.card) * tensε W q.2)) =
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
          h ((psum B' (x2 B') I.down).left ≫ tensφ pr (p, k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-W p.1 p.2) := by
      rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← zpow_mul]
      congr 1
      simp only [tensε]
      ring
    refine (Fintype.prod_prod_type _).trans (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) h1 h2)).symm)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => pair_eq pr hpr (W p.1 p.2) p.1 p.2 h
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB hfe (GeneratorPullback.finProdGen L.L _ _ (pairGen cb W pr))
    (finProdGen_isGen _ _ _ _ (pairGen_isGen cb W pr))
  refine ⟨t, ht, fun T ρ z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_finProdGen _ _ _ (pairGen cb W pr) _ _ hJ).trans
    ((Fintype.prod_prod_type _).trans ?_))
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only [pairGen]
  refine (val_zpowGen _ _ _ _ _ _ _ _).trans (congrArg (· ^ (-W i j)) ?_)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) (val_cub cb ρ hJ _ _ _))))).trans ?_
  rw [MonObj.comp_mul, ← _root_.mul_assoc]

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem toProj_secPull_of_gs {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} [Subsingleton Z] {A : LB Y} {A' : LB Y'}
    {N : ℕ} (σ : Fin (N + 1) → A.Sec) (τ : Fin (N + 1) → A'.Sec) (s : Y' ⟶ Sp R)
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Z ⟶ Y) (y : Z ⟶ Y')
    (H : ∀ z : Z, ∃ (a : A.ι) (a' : A'.ι) (c : (Z.presheaf.stalk z)ˣ), p z ∈ A.U a ∧ y z ∈ A'.U a' ∧
      ∀ i, gs p z _ ((σ i).f a) = c.val * gs y z _ ((τ i).f a')) :
    (∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧
      ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  have h1 : ∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i) := by
    intro i z
    obtain ⟨a, a', c, ha, ha', e⟩ := H z
    rw [GlobalTheory.mem_nonzeroLocus_iff_pull (σ i) p z ha, GlobalTheory.mem_nonzeroLocus_iff_pull (τ i) y z ha', e i,
      IsUnit.mul_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.isUnit, h⟩⟩
  have hs : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) p) = ⊤ := by
    refine top_le_iff.1 fun z _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y z)))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (GlobalTheory.nonzeroLocus_secPull (σ i) p).ge ((h1 i z).2 hi)⟩
  refine ⟨h1, hs, GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hτ y hs fun z => ?_⟩
  obtain ⟨a, a', c, ha, ha', e⟩ := H z
  obtain ⟨W, hW, u, hu⟩ := Z.presheaf.exists_germ_eq c.val
  have hall : ∀ {U : Z.Opens}, z ∈ U → W ≤ U := fun hU x _ => (Subsingleton.elim z x) ▸ hU
  have hl : z ∈ (A.pull p).U fun _ => a := Set.mem_iInter.2 fun _ => ha
  refine ⟨W, hW, a', hall ha', fun _ => a, hall hl, u, fun j => fn_ext fun x hx => ?_⟩
  obtain rfl : z = x := Subsingleton.elim _ _
  have e₁ : gs (𝟙 Z) z W (resG Z (hall hl) ((GlobalTheory.secPull (σ j) p).f fun _ => a)) = gs p z _ ((σ j).f a) :=
    (gs_res (𝟙 Z) z (hall hl) hW _).trans
      ((GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull A p) (σ j) (𝟙 Z) z (fun _ => a) hl).trans (by rw [Category.id_comp]; rfl))
  have e₂ : gs (𝟙 Z) z W u = c.val := (gs_eq (𝟙 Z) z W hW u).trans hu
  have e₃ : gs (𝟙 Z) z W ((y.appLE _ W (hall ha')).hom ((τ j).f a')) = gs y z _ ((τ j).f a') :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE y _ _ _ (𝟙 Z) z hW _).trans (by rw [Category.id_comp])
  rw [e₁, gs_mul (𝟙 Z) z W hW, e₂, e₃, e j]

theorem toProj_secPull_of_sval : ∀ (R Ω : Type) [CommRing R] [Field Ω] (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (h : Y ⟶ X) (h' : Y' ⟶ X') (k N : ℕ) (σ : Fin (N + 1) → SecK L h k) (τ : Fin (N + 1) → SecK L' h' k) (s : Y' ⟶ Sp R) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Sp Ω ⟶ Y) (y : Sp Ω ⟶ Y'), L.IsLB → L'.IsLB → (∀ z J J', Good L z J → Good L' z J' → ∃ c : ((Sp Ω).presheaf.stalk z)ˣ, ∀ i, sval (σ i) p z J = c.val * sval (τ i) y z J') → (∀ i (z : Sp Ω), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧ ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  intro R Ω _ _ X X' Y Y' L L' h h' k N σ τ s hτ p y hL hL' H
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  refine toProj_secPull_of_gs σ τ s hτ p y fun z => ?_
  choose J hJ using fun χ : Sp Ω ⟶ X => exists_chart hL (χ z)
  choose J' hJ' using fun χ : Sp Ω ⟶ X' => exists_chart hL' (χ z)
  obtain ⟨c, hc⟩ := H z J J' hJ hJ'
  exact ⟨_, _, c, Good.mem hJ _ p, Good.mem hJ' _ y, hc⟩

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj GrpObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

def diagPrecomp {T : Scheme.{0}} {X Y M : Over T} [MonObj M] (f : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) where
  toFun := (f ≫ ·)
  map_one' := by
    change f ≫ toUnit Y ≫ η = toUnit X ≫ η
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y)]
  map_mul' g h := by
    change f ≫ lift g h ≫ μ = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [← Category.assoc, comp_lift]

theorem exists_diagEnd_isMonHom (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Scheme.{0})
    (P : PolAV T) (u : T ⟶ F.X) (h : SharpOver F W P u) :
    ∃ ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A), IsDiagEnd F W P u ε ∧ ∀ E, IsMonHom (ε E) := by
  obtain ⟨c, hc, pr, hpr, huniq, hL⟩ := h
  choose ε hε _ using fun E : Matrix (Fin 8) (Fin 8) ℤ =>
    huniq P.A (fun a => ((List.finRange 8).map fun b => pr b ^ E a b).prod)
  have ext : ∀ (T' : Over T) (x x' : T' ⟶ P.A), (∀ a, x ≫ pr a = x' ≫ pr a) → x = x' := fun T' x x' hx =>
    (huniq T' (fun a => x' ≫ pr a)).unique hx (fun _ => rfl)
  refine ⟨ε, ⟨c, hc, pr, hpr, huniq, hL, hε⟩, fun E => ?_⟩
  have key : ∀ (T' : Over T) (x : T' ⟶ P.A) (a : Fin 8),
      (x ≫ ε E) ≫ pr a = ((List.finRange 8).map fun b => (x ≫ pr b) ^ E a b).prod := by
    intro T' x a
    rw [Category.assoc, hε]
    change diagPrecomp (M := c.A) x _ = _
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    exact map_zpow (diagPrecomp (M := c.A) x) (pr b) (E a b)
  refine isMonHom_of_mul _ fun T' x z => ext T' _ _ fun a => ?_
  have hm : ∀ (b : Fin 8) (x z : T' ⟶ P.A), (x * z) ≫ pr b = (x ≫ pr b) * (z ≫ pr b) := fun b x z =>
    map_mul (IsMonHom.monoidHom (pr b) T') x z
  have hm' : ((x ≫ ε E) * (z ≫ ε E)) ≫ pr a = ((x ≫ ε E) ≫ pr a) * ((z ≫ ε E) ≫ pr a) :=
    map_mul (IsMonHom.monoidHom (pr a) T') (x ≫ ε E) (z ≫ ε E)
  rw [key, hm', key, key, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [hm, mul_zpow]

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharpRef_relDim : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → D.P.g = 8 * Q.g := by
  intro W V V₁ _ _ _ _ Q ρ D e h
  obtain ⟨pr, w, hmon, huniv, -⟩ := h
  have lim : IsLimit (Fan.mk D.P.A pr) :=
    mkFanLimit _ (fun s => (huniv s.pt s.proj).choose)
      (fun s i => (huniv s.pt s.proj).choose_spec.1 i)
      (fun s m hm => (huniv s.pt s.proj).unique hm (huniv s.pt s.proj).choose_spec.1)
  let eI : D.P.A ≅ powObj ((Over.pullback (spMap ρ)).obj Q.B) 8 :=
    lim.conePointUniqueUpToIso (powIsLimit _ 8)
  have hB : SmoothOfRelativeDimension Q.g ((Over.pullback (spMap ρ)).obj Q.B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback Q.B.hom (spMap ρ)) Q.smoothDim
  have h8 := GlobalTheory.smoothOfRelativeDimension_powObj _ Q.g hB 8
  have hne : Nonempty (Sp V₁) := inferInstance
  exact GlobalTheory.relDim_unique_of_iso_grp (Sp V₁) hne D.P.A _ eI.hom inferInstance _ _ D.P.smoothDim h8

end GlobalTheory.Poinc.Sep
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lie_image_iff_lie_correspondence_deRham_extension : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (E : primDR A ≃ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (E c)) → ∀ (h : HdR A) (v : epsR R ⟶ A), IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie (E.symm.dualMap h)) v := by
  first | exact @GlobalTheory.PtExt.isLieImage_iff_lieCorr | exact GlobalTheory.PtExt.isLieImage_iff_lieCorr | (intros; apply GlobalTheory.PtExt.isLieImage_iff_lieCorr <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  first | exact @GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | exact GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham <;> assumption)
end
