module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle011
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.KerPair

theorem exists_pow_gen {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  induction n with
  | zero =>
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (0 : ℕ))
      (fun U _ h => by simp) (LB.oneGen L (Y := Y))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t', ht', fun Z r z J hJ => (hv _ _ z J hJ).trans ((val_one _).trans (pow_zero _).symm)⟩
  | succ n ih =>
    obtain ⟨s, hs, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (n + 1 : ℕ)) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← zpow_add]
        congr 1
        push_cast
        ring)
      (LB.mulGen L _ _ _ _ s t) (DVR.mulGen_isGen _ _ _ _ _ _ _ hs ht)
    refine ⟨t', ht', fun Z r z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
    rw [hv Z r z J hJ, pow_succ]

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}

abbrev trφ (x : T ⟶ B) : Fin 2 → ((T ⊗ B).left ⟶ B.left) := ![((fst T B ≫ x) * snd T B).left, (snd T B).left]


omit [IsCommMonObj B] in
theorem prod_tr {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) (m : ℤ) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ ((![1, -1] : Fin 2 → ℤ) k * m) =
      h ((ρ ≫ x) * b).left ^ m * h b.left ^ (-m) := by
  have e₀ : (lift ρ b).left ≫ trφ x 0 = ((ρ ≫ x) * b).left := by
    show (lift ρ b ≫ ((fst T B ≫ x) * snd T B)).left = _
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
  have e₁ : (lift ρ b).left ≫ trφ x 1 = b.left := by
    show (lift ρ b ≫ snd T B).left = _
    rw [lift_snd]
  rw [Fin.prod_univ_two, e₀, e₁]
  simp


omit [IsCommMonObj B] in
theorem prod_tr_one {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h ((ρ ≫ x) * b).left * (h b.left)⁻¹ := by
  simpa using prod_tr (x := x) ρ b h 1

theorem val_mul_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) (a b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    val u (lift (𝟙 T) (a * b)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J =
      cubV c z J x a b * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) b).left z J := by
  let p := fst T B
  let q := snd T B
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ u (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hu _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans (by rw [← Over.comp_left, comp_lift])
  let t₁ := LB.mulGen L.L _ _ _ _ (uu ((p ≫ a) * q)) (uu 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε c.t (lift (p ≫ x) (lift (p ≫ a) q)).left) (uu (p ≫ a))) (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J =
        val u (lift (𝟙 T) (a * w)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ∧
      val t₂ (lift (𝟙 T) w).left z J =
        cubV c z J x a w * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) w).left z J := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vu _ hJ _) (vu _ hJ _))).trans ?_
      rw [MonObj.comp_mul, MonObj.comp_one, hp, hq, hp']
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub c _ hJ _ _ _) (vu _ hJ _))) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp', hp']
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gu _) (gu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (gu _)) (gu _))
    (fun y I hI => ?_) _ _ z J hJ
  · refine (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
      (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub (p ≫ x) (p ≫ a) q k) (prod_tr_one p (p ≫ a) k))
      (prod_tr_one p q k)).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_tr_one p ((p ≫ a) * q) k) (prod_tr_one p 1 k)).symm)
    rw [_root_.mul_one, ← _root_.mul_assoc (p ≫ x)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [_root_.mul_one, (isCub_cubV c (T := T) hI).face₃, _root_.one_mul]

theorem val_pow_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) {N : ℕ} (hx : x ^ N = 1) (b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    cubN (cubV c z J) N 1 x b * val u (lift (𝟙 T) b).left z J ^ N = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := by
  let p := fst T B
  let q := snd T B
  have hx' : (p ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, hv⟩ := WeilCube.exists_gen_torsion c N (p ≫ x) q hx'
  obtain ⟨s, hs, hsv⟩ := exists_pow_gen L.isLB u hu N
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ s (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hs _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J ^ N := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans ((hsv _ _ z J hJ).trans (by rw [← Over.comp_left, comp_lift]))
  let t₁ := LB.mulGen L.L _ _ _ _ t (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J = cubN (cubV c z J) N 1 x w * val u (lift (𝟙 T) w).left z J ^ N ∧
      val (uu 1) (lift (𝟙 T) w).left z J = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ z J hJ) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp']
    · refine (vu _ hJ _).trans ?_
      rw [MonObj.comp_one, hp]
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (gu _)) (gu _) (fun y I hI => ?_) _ _ z J hJ
  · refine (prod_tr p 1 k N).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ rfl (prod_tr p q k N)).symm)
    rw [_root_.mul_one]
    simp only [Fin.prod_univ_succ, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [(isCub_cubV c (T := T) hI).N_one, _root_.one_mul]

theorem cubWeil_of_gen : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ) (T : Over S) (x y : T ⟶ B), x ^ N = 1 → y ^ N = 1 → (∃ u : LB.Gen (translDiff B L.L x), u.IsGen) → CubWeil c N x y 1) := by
  intro hG S B _ _ hB L c N T x y hx hy ⟨u, hu⟩
  refine ⟨hx, hy, fun z J hJ => ?_⟩
  have C := isCub_cubV c hJ
  obtain ⟨U, hU⟩ : ∃ U : (T ⟶ B) → (T.left.presheaf.stalk z)ˣ,
      ∀ b, U b = val (L := L.L) (φ := trφ x) (ε := ![1, -1]) u (lift (𝟙 T) b).left z J := ⟨_, fun _ => rfl⟩
  have m : ∀ a b, U (a * b) * U 1 = cubV c z J x a b * U a * U b := fun a b => by
    simp only [hU]; exact val_mul_pt c hG hB u hu a b z J hJ
  have k : cubN (cubV c z J) N 1 x y * U y ^ N = U 1 ^ N := by
    simp only [hU]; exact val_pow_pt c hG hB u hu hx y z J hJ
  have b : ∀ n : ℕ, U (y ^ n) * U 1 ^ n = U 1 * (cubN (cubV c z J) n 1 y x * U y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have e := m (y ^ n) y
      rw [C.s01, C.s12] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at e' ih' ⊢
      linear_combination (norm := abel) e' + ih'
  have b' := b N
  rw [hy] at b'
  rw [(gm (𝟙 T.left) z ⊤).map_one, _root_.one_mul]
  exact mul_right_cancel (k.trans (mul_left_cancel b'))

end GlobalTheory.UU.KerPair
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

theorem IsCPMap.cancel {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    {hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f} {w'' : LB.Iso P''.L.L (P.L.L.pull (F' ≫ F))}
    (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'')
    (mul : ∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y)
    (Tw : Tri w w' w'') : IsCPMap P'' P' f' F' hw' w' := by
  have key : ∀ (T : Over S''), ∃ ρ : Over.mk (T.hom ≫ f' ≫ f) ⟶ Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f),
      ρ.left = 𝟙 T.left ∧ ∀ x : T ⟶ G'', toBase hw'' x = ρ ≫ toBase hw (toBase hw' x) := fun T =>
    ⟨Over.homMk (𝟙 T.left) (by simp), rfl, fun x => Over.OverMorphism.ext
      ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm)⟩
  refine ⟨mul, (isGen_iff _).2 (Tw.pgen_cancel P.L.isLB ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)),
    fun T z J'' J' hJ'' hJ' B hB => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  obtain ⟨ρ, hρ, e⟩ := key T
  obtain ⟨a₁, a₂, a₃⟩ := h.vals (Over.mk (T.hom ≫ f')) z J' J hJ' hJ _ (fun _ => rfl)
  let β := toBaseHom mul T
  let A : (Over.mk (T.hom ≫ f') ⟶ G') → (T.left.presheaf.stalk z)ˣ :=
    fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left)
  have hAB : ∀ x : T ⟶ G'', A (β x) * B x = gw w'' x.left z (J (x.left ≫ F' ≫ F)) (J'' x.left) := fun x => by
    rw [hB, ← Category.assoc]
    exact (Tw _ x.left z _ _ _ (hJ ((x.left ≫ F') ≫ F)) (hJ' (x.left ≫ F')) (hJ'' x.left)).symm
  obtain ⟨b₁, b₂, b₃⟩ := h''.vals T z J'' J hJ'' hJ (fun x => A (β x) * B x) hAB
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [map_one, ← Category.assoc, _root_.mul_assoc] at b₁
    exact mul_left_cancel (a := A 1) (a₁.symm.trans b₁)
  · have a : val P.sym ((x.left ≫ F') ≫ F) z J * A (β x) = A (β x)⁻¹ * val P'.sym (x.left ≫ F') z J' := a₂ (β x)
    have b := b₂ x
    rw [map_inv, ← Category.assoc, ← _root_.mul_assoc, a, _root_.mul_assoc, _root_.mul_assoc] at b
    exact mul_left_cancel b
  · have c : @_root_.id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f' ≫ f)) z J (toBase hw'' x)
        (toBase hw'' y) (toBase hw'' u)) = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := by
      have e' : (lift (toBase hw'' x) (lift (toBase hw'' y) (toBase hw'' u))).left =
          (lift (toBase hw (β x)) (lift (toBase hw (β y)) (toBase hw (β u)))).left := by
        rw [e, e, e, ← comp_lift, ← comp_lift, Over.comp_left, hρ]; exact Category.id_comp _
      exact congrArg (fun r => val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t r z J) e'
    obtain ⟨C, hC⟩ : ∃ C : (T.left.presheaf.stalk z)ˣ, C = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := ⟨_, rfl⟩
    obtain ⟨C', hC'⟩ : ∃ C' : (T.left.presheaf.stalk z)ˣ, C' = cubV P'.c (T := Over.mk (T.hom ≫ f')) z J'
        (β x) (β y) (β u) := ⟨_, rfl⟩
    have a : C * A (β x * β y) * A (β x * β u) * A (β y * β u) * A 1 =
        A (β x * β y * β u) * A (β x) * A (β y) * A (β u) * C' := by
      rw [hC, hC']; exact a₃ (β x) (β y) (β u)
    have b := b₃ x y u
    rw [c.trans hC.symm] at b
    simp only [map_mul, map_one] at b
    have g : C' * B (x * y) * B (x * u) * B (y * u) * B 1 =
        B (x * y * u) * B x * B y * B u * cubV P''.c z J'' x y u := by
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul] at a' b' ⊢
      linear_combination (norm := abel) b' - a'
    rw [hC'] at g
    exact g

theorem isCPMap_comp_cancel :
    (∀ (S S' S'' : Scheme.{0}) (f : S' ⟶ S) (f' : S'' ⟶ S') (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G'' : Over S'') [GrpObj G''] [IsCommMonObj G''] (P : CP G) (P' : CP G') (P'' : CP G'') (F : G'.left ⟶ G.left) (hw) (w) (F' : G''.left ⟶ G'.left) (hw' : F' ≫ G'.hom = G''.hom ≫ f') (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f), IsCPMap P' P f F hw w → (∀ w', IsCPMap P'' P' f' F' hw' w' → ∃ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' ∧ Tri w w' w'') ∧ ((∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y) → ∀ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' → ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ Tri w w' w'')) := by
  intro S S' S'' f f' G _ _ G' _ _ G'' _ _ P P' P'' F hw w F' hw' hw'' h
  refine ⟨fun w' h' => ?_, fun mul w'' h'' => ?_⟩
  · obtain ⟨w'', Tw, H⟩ := h.exists_comp h' hw''
    exact ⟨w'', H, Tw⟩
  · obtain ⟨w', Tw⟩ := Geo.Tor.exists_cancel P.L.isLB w w'' ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)
      P'.L.isLB P''.L.isLB
    exact ⟨w', h.cancel h'' mul Tw, Tw⟩

end GlobalTheory.UU
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.UnitRigid

theorem coeff_inl_mul_inr {B X : Type} [CommRing B] [AddCommGroup X] (a b : AddMonoidAlgebra B X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) a *
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) b).coeff (x, y) = a.coeff x * b.coeff y := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' h h' => simp only [map_add (f := _), add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
  | single p r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' h h' => simp only [map_add (f := _), mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
    | single q s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h₁ : p = x <;> by_cases h₂ : q = y <;> simp [h₁, h₂]

theorem eq_one_of_groupLike {B X : Type} [CommRing B] [AddCommGroup X] (I : Ideal B) (hI : ∀ b ∈ I, IsNilpotent b)
    (g : AddMonoidAlgebra B X)
    (h : AddMonoidAlgebra.mapDomainRingHom B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) g =
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) g *
        AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) g)
    (h₁ : AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I) g = 1) : g = 1 := by
  classical
  have idem : ∀ x, IsIdempotentElem (g.coeff x) := fun x => by
    have e := congrArg (fun a => a.coeff (x, x)) h
    simp only [coeff_inl_mul_inr] at e
    refine e.symm.trans ?_
    exact Finsupp.mapDomain_apply_of_injective (f := fun x : X => (x, x)) (fun _ _ q => congrArg Prod.fst q) g.coeff x
  ext x
  have e := congrArg (fun a => a.coeff x) h₁
  simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at e ⊢
  split_ifs at e ⊢ with hx
  · have m : 1 - g.coeff x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self]
    exact (sub_eq_zero.1 ((idem x).one_sub.eq_zero_of_isNilpotent (hI _ m))).symm
  · exact (idem x).eq_zero_of_isNilpotent (hI _ (Ideal.Quotient.eq_zero_iff_mem.1 e))

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem point_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

theorem exists_point (Z : Over S) (c : Multiplicative X →* Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, ∀ χ, (chV t χ).val = c (Multiplicative.ofAdd χ) :=
  ⟨(splitTorusPointsEquiv S X Z).symm c.toHomUnits, fun χ => by rw [chV, MulEquiv.apply_symm_apply]; rfl⟩

theorem exists_universal {Y W : Over S} [IsAffine W.left] (y : W ⟶ Y) (u : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ g : AddMonoidAlgebra Γ(W.left, ⊤) X, ∀ (Z : Over S) (s : Z ⟶ W) (t : Z ⟶ splitTorus S X)
      (θ : AddMonoidAlgebra Γ(W.left, ⊤) X →+* Γ(Z.left, ⊤)),
      (∀ b, θ (AddMonoidAlgebra.single 0 b) = s.left.appTop.hom b) →
      (∀ χ, θ (AddMonoidAlgebra.single χ 1) = (chV t χ).val) → (lift t (s ≫ y)).left.appTop.hom u = θ g := by
  obtain ⟨U, y₀, e, -, -, H⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) X)
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, ht₀⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
  refine ⟨e ((lift t₀ (y₀ ≫ y)).left.appTop.hom u), fun Z s t θ h₁ h₂ => ?_⟩
  obtain ⟨σ, hσ, hθ⟩ := H Z s θ h₁
  have ht : σ ≫ t₀ = t := point_ext fun χ => by
    rw [chV_comp, hθ, ht₀, ← h₂]
    exact congrArg θ (e.apply_symm_apply _)
  rw [← hθ, ← ht, ← hσ, Category.assoc, ← comp_lift, Rosenlicht.over_appTop_comp]

theorem eq_one_affine {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) {Y W : Over (Spec (CommRingCat.of A))}
    [IsAffine W.left] (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤))
    (hm : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u = (lift t y).left.appTop.hom u * (lift t' y).left.appTop.hom u)
    (h₁ : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift t y).left.appTop.hom u = 1) (t : W ⟶ splitTorus _ X) (y : W ⟶ Y) : (lift t y).left.appTop.hom u = 1 := by
  obtain ⟨g, hg⟩ := exists_universal y u
  let I : Ideal Γ(W.left, ⊤) := J.map (RingPoint.strMap W)
  have hI : ∀ b ∈ I, IsNilpotent b := fun b hb => by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hb n
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot] at this
    exact this
  have one : g = 1 := by
    refine eq_one_of_groupLike I hI g ?_ ?_
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) (X × X))
        AddMonoidAlgebra.singleZeroRingHom
      have key : ∀ (f : X →+ X × X) (t : U ⟶ splitTorus _ X),
          (∀ χ, (chV t χ).val = e.symm (AddMonoidAlgebra.single (f χ) 1)) →
          (lift t (s ≫ y)).left.appTop.hom u = e.symm (AddMonoidAlgebra.mapDomainRingHom _ f g) := fun f t ht =>
        hg U s t (e.symm.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom _ f))
          (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [ht]; simp)
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inl X X))))
      obtain ⟨t₂, ht₂⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr X X))))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inl X X χ) 1) := ht₁
      have a₂ : ∀ χ, (chV t₂ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inr X X χ) 1) := ht₂
      apply e.symm.injective
      rw [map_mul, ← key _ t₁ a₁, ← key _ t₂ a₂, ← hm, key]
      intro χ
      rw [chV_mul, Units.val_mul, a₁, a₂, ← map_mul, AddMonoidAlgebra.single_mul_single]
      simp
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra (Γ(W.left, ⊤) ⧸ I) X)
        (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single χ 1) := ht₁
      have hU : ∃ s, s ≫ red J = U.hom := (RingPoint.exists_comp_red_iff J U).2 fun a ha => by
        apply e.injective
        rw [← RingPoint.appTop_strMap s, he, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero, map_zero]
      have k := hg U s t₁ (e.symm.toRingHom.comp (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I)))
        (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [a₁]; simp)
      apply e.symm.injective
      rw [map_one]
      exact k.symm.trans (h₁ U hU _ _)
  have k := hg W (𝟙 W) t (AddMonoidAlgebra.liftNCRingHom (RingHom.id _)
    ((Units.coeHom _).comp (splitTorusPointsEquiv _ X W t)) fun _ _ => Commute.all _ _)
    (fun b => by simp) (fun χ => by simp [chV])
  rwa [Category.id_comp, one, map_one] at k

theorem unit_eq_one : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') y).left z ⊤ u = gm (lift t y).left z ⊤ u * gm (lift t' y).left z ⊤ u) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ u = 1) → u = 1 := by
  intro A _ J hJ X _ Y u hm h₁
  have hm' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u.val =
        (lift t y).left.appTop.hom u.val * (lift t' y).left.appTop.hom u.val := fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom u =
        Units.map (lift t y).left.appTop.hom.toMonoidHom u * Units.map (lift t' y).left.appTop.hom.toMonoidHom u :=
      unit_ext fun z _ => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, hm]
    exact congrArg Units.val e
  have h₁' : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), (lift t y).left.appTop.hom u.val = 1 := fun Z hZ t y => by
    have e : Units.map (lift t y).left.appTop.hom.toMonoidHom u = 1 :=
      unit_ext fun z _ => by rw [map_one, ← gm_top, h₁ Z hZ]
    exact congrArg Units.val e
  refine unit_ext fun z _ => ?_
  let 𝒰 := (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left.affineCover
  obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq z
  let W : Over (Spec (CommRingCat.of A)) := Over.mk (𝒰.f i ≫ (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).hom)
  haveI : IsAffine W.left := inferInstanceAs (IsAffine (𝒰.X i))
  let κ : W ⟶ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y := Over.homMk (𝒰.f i) rfl
  have e := eq_one_affine J hJ u.val hm' h₁' (κ ≫ fst _ _) (κ ≫ snd _ _)
  rw [lift_comp_fst_snd] at e
  have e' : Units.map (𝒰.f i).appTop.hom.toMonoidHom u = 1 := Units.ext e
  refine gm_inj (U := ⊤) (U' := ⊤) (𝒰.f i) w trivial trivial ?_
  rw [gm_top, e', map_one, map_one]

end GlobalTheory.UU.UnitRigid
end
end
