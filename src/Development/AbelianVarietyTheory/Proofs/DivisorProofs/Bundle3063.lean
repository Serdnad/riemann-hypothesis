module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBack
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensCube

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def tensHom (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : D'.P.A ⟶ D.P.A :=
  ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2

theorem tensφ_eq (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : tensφ T.pr k = (tensHom T k).left := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m <;> rfl

theorem tensHom_mul (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))}
    (a b : Z ⟶ D'.P.A) : (a * b) ≫ tensHom T k = (a ≫ tensHom T k) * (b ≫ tensHom T k) := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  haveI := T.pr_hom i
  haveI := T.pr_hom j
  fin_cases m
  · show (a * b) ≫ (T.pr i * T.pr j) = (a ≫ (T.pr i * T.pr j)) * (b ≫ (T.pr i * T.pr j))
    rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _
  · show (a * b) ≫ T.pr i = (a ≫ T.pr i) * (b ≫ T.pr i)
    exact MonObj.mul_comp _ _ _
  · show (a * b) ≫ T.pr j = (a ≫ T.pr j) * (b ≫ T.pr j)
    exact MonObj.mul_comp _ _ _
  · show (a * b) ≫ (1 : D'.P.A ⟶ D.P.A) = (a ≫ 1) * (b ≫ 1)
    rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one]

def tensHomH (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) (Z : Over (Spec (CommRingCat.of R))) :
    (Z ⟶ D'.P.A) →* (Z ⟶ D.P.A) :=
  MonoidHom.mk' (· ≫ tensHom T k) (tensHom_mul T k)

def cubeρ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : (G3 D'.P.A).left ⟶ (G3 D.P.A).left :=
  (lift (x3 D'.P.A 0 ≫ tensHom T k) (lift (x3 D'.P.A 1 ≫ tensHom T k) (x3 D'.P.A 2 ≫ tensHom T k))).left

theorem cube_comm (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) (I : thK) :
    thφ D'.P.A (x3 D'.P.A) I ≫ tensφ T.pr k = cubeρ T k ≫ thφ D.P.A (x3 D.P.A) I := by
  rw [tensφ_eq]
  show (psum D'.P.A (x3 D'.P.A) I.down).left ≫ (tensHom T k).left = _ ≫ (psum D.P.A (x3 D.P.A) I.down).left
  rw [cubeρ, ← Over.comp_left, ← Over.comp_left]
  congr 1
  show tensHomH T k _ (psum D'.P.A (x3 D'.P.A) I.down) = preHom _ (psum D.P.A (x3 D.P.A) I.down)
  rw [psum_hom, psum_hom]
  congr 1
  funext n
  fin_cases n <;> simp [x3, tensHomH, preHom]

end GlobalTheory.Mum.TensCube

namespace GlobalTheory.Mum.TensCube

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem one_tensHom (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))} :
    (1 : Z ⟶ D'.P.A) ≫ tensHom T k = 1 := map_one (tensHomH T k Z)

theorem lift_cubeρ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))}
    (a b c : Z ⟶ D'.P.A) : (lift a (lift b c)).left ≫ cubeρ T k =
      (lift (a ≫ tensHom T k) (lift (b ≫ tensHom T k) (c ≫ tensHom T k))).left := by
  rw [cubeρ, ← Over.comp_left]
  congr 1
  simp [x3]

theorem cube_tens (hG : GlobalFnsSt) (T : Tens D D' W) {Z : Scheme.{0}} (q : Z ⟶ (G3 D'.P.A).left) (z : Z)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    (∏ a : thK.{0}, GlobalTheory.TensEven.bwE T.w (q ≫ thφ D'.P.A (x3 D'.P.A) a) z
        (fun i => J ((q ≫ thφ D'.P.A (x3 D'.P.A) a) ≫ tensφ T.pr i)) (J' (q ≫ thφ D'.P.A (x3 D'.P.A) a)) ^ thε a) *
      val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t q z J' =
      ∏ k, val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (q ≫ cubeρ T k) z J ^ tensε W k := by
  have hA := D'.P.isAb
  have he : (lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left ≫
      (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w _
  refine GlobalTheory.TensEven.box_uniqueE (pr := tensφ T.pr) (εp := tensε W) D.P.isLB D'.P.isLB T.w T.w_gen
    (φ' := thφ D'.P.A (x3 D'.P.A)) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) (ρ := cubeρ T)
    (fun k I => cube_comm T k I) D'.cub.isGen D.cub.isGen _ _ he
    (surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)) (fun y I I' hI hI' => ?_) Z q z J J' hJ hJ'
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
    (fun ψ => GlobalTheory.TensEven.bwE T.w ψ y (fun i => I (ψ ≫ tensφ T.pr i)) (I' ψ))
  simp only [_root_.mul_one, mul_inv_cancel, inv_mul_cancel] at p
  have c' : val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t
      (lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left y I' = 1 :=
    (isCub_cubV D'.cub hI').face 1 1
  have c : ∀ k, val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
      ((lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left ≫ cubeρ T k) y I = 1 := fun k => by
    rw [lift_cubeρ, one_tensHom]
    exact (isCub_cubV D.cub hI).face 1 1
  refine (congrArg₂ (· * ·) p c').trans ?_
  simp only [c, one_zpow, Finset.prod_const_one]
  group

end GlobalTheory.Mum.TensCube

namespace GlobalTheory.Mum.TensCube

theorem alg {U : Type} [CommGroup U] (Θ P hxyu hxy hxu hyu hx hy hu h1 : U)
    (key : hxyu * hxy⁻¹ * hxu⁻¹ * hyu⁻¹ * hx * hy * hu * h1⁻¹ * Θ = P) :
    Θ * hxyu * hx * hy * hu = P * hxy * hxu * hyu * h1 := by
  subst key
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem theta_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ x y u, (N'.θ x y u : F) * wv T ν ν' (x * y * u) * wv T ν ν' x * wv T ν ν' y * wv T ν ν' u =
    ((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j) (cmp T ν ν' u i * cmp T ν ν' u j) /
        (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) * N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F) *
      wv T ν ν' (x * y) * wv T ν ν' (x * u) * wv T ν ν' (y * u) * wv T ν ν' 1 := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' x y u
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.toPre.P.L z ν.J := fun ψ => ν.good ψ trivial
  have hJ' : Good D'.toPre.P.L z ν'.J := fun ψ => ν'.good ψ trivial
  let h : ((TF (R := R) F).left ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ := fun ψ =>
    GlobalTheory.TensEven.bwE T.w ψ z (fun i => ν.J (ψ ≫ tensφ T.pr i)) (ν'.J ψ)
  let τ : Fˣ →* ((Sp F).presheaf.stalk z)ˣ := Units.map (toStk z).toMonoidHom
  have vw : ∀ a, toStk z (wv T ν ν' a) = (h (ν'.eA a).left).val := fun a =>
    toStk_valF (ν'.eA a).left (LB.wchart D.toPre.P.L (tensφ T.pr) (fun k => ν.J ((ν'.eA a).left ≫ tensφ T.pr k)) ⊓
      D'.toPre.P.L.U (ν'.J (ν'.eA a).left)) z ⟨hJ.mem (tensφ T.pr) _, hJ' _⟩ _
  have vθ' : toStk z (N'.θ x y u : F) =
      (cubV D'.toPre.cub (T := TF (R := R) F) z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u)).val :=
    (congrArg (toStk z) (ν'.θ_eq x y u)).trans (toStk_valF _ _ z (hJ'.mem _ _) _)
  have tθ : ∀ a b c, τ (N.θ a b c) = cubV D.toPre.cub (T := TF (R := R) F) z ν.J (ν.eA a) (ν.eA b) (ν.eA c) := fun a b c =>
    Units.ext ((Units.coe_map _ _).trans ((congrArg (toStk z) (ν.θ_eq a b c)).trans (toStk_valF _ _ z (hJ.mem _ _) _)))
  have ecmp : ∀ a j, ν.eA (cmp T ν ν' a j) = ν'.eA a ≫ T.pr j := fun a j => ν.eA.apply_symm_apply _
  have key := cube_tens GlobalTheory.globalFns_holds T (Z := Sp F) (lift (ν'.eA x) (lift (ν'.eA y) (ν'.eA u))).left z hJ hJ'
  have key' := (congrArg₂ (· * ·) (prod_cub (ν'.eA x) (ν'.eA y) (ν'.eA u) h) rfl).symm.trans key
  have c1 := (isCub_cubV D.toPre.cub hJ).face (1 : TF (R := R) F ⟶ D.toPre.P.A) 1
  have hP : τ (∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j)
      (cmp T ν ν' u i * cmp T ν ν' u j) / (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) *
        N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j) =
      ∏ k, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        ((lift (ν'.eA x) (lift (ν'.eA y) (ν'.eA u))).left ≫ cubeρ T k) z ν.J ^ tensε W k := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_four]
    simp only [lift_cubeρ]
    haveI := T.pr_hom i
    haveI := T.pr_hom j
    have m0 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 0) = ν.eA (cmp T ν ν' a i * cmp T ν ν' a j) := fun a => by
      rw [map_mul, ecmp, ecmp]; exact MonObj.comp_mul _ _ _
    have m1 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 1) = ν.eA (cmp T ν ν' a i) := fun a => (ecmp a i).symm
    have m2 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 2) = ν.eA (cmp T ν ν' a j) := fun a => (ecmp a j).symm
    have m3 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 3) = 1 := fun a => MonObj.comp_one _
    change _ = cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ * cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ *
      cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ * cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _
    rw [m0, m0, m0, m1, m1, m1, m2, m2, m2, m3, m3, m3, c1, ← tθ, ← tθ, ← tθ, map_zpow, map_div, map_mul]
    simp only [tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, one_zpow, _root_.mul_one, zpow_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_div, ofMul_one]
    module
  rw [← hP] at key'
  apply (toStk z).injective
  have eq1 : toStk z (((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j)
      (cmp T ν ν' u i * cmp T ν ν' u j) / (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) *
        N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F)) = (τ _).val :=
    (Units.coe_map _ _).symm
  simp only [map_mul, vw, vθ', eq1, map_one]
  simp only [← Units.val_mul]
  congr 1
  refine alg _ _ _ _ _ _ _ _ _ _ ?_
  exact key'

end GlobalTheory.Mum.TensCube
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.PolTensBimult

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TensCub

theorem interchange {U X : Type} [CommGroup U] [AddCommGroup X] (t : X → X → U) (hs : ∀ u v, t u v = t v u)
    (hc : ∀ u u' v, t u' v * (t (u + u') v)⁻¹ * t u v = t v u' * (t (u + v) u')⁻¹ * t u u') (x x' y y' : X) :
    t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹ := by
  have h₁ := hc y y' (x + x')
  have h₂ := hc x' y' (x + y)
  have h₃ := hc x x' y
  rw [hs (y + y'), hs y' (x + x'), hs y (x + x')] at h₁
  rw [hs (x' + y'), hs y' (x + y), hs x' (x + y), show x' + (x + y) = y + (x + x') by abel] at h₂
  rw [hs y x'] at h₃
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  have k₃ := congrArg Additive.ofMul h₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at k₁ k₂ k₃ ⊢
  rw [← sub_eq_zero] at k₁ k₂ k₃ ⊢
  have k := congrArg₂ (· - ·) (congrArg₂ (· - ·) k₂ k₁) k₃
  simp only [sub_zero] at k
  rw [← k]
  abel

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (h0 : t 0 0 = 1)
    (ht : ∀ x x' y y', t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  have hτ' : ∀ u v, τ' u v = O (u + v) * (O u)⁻¹ * (O v)⁻¹ * O 0 *
      ∏ i, ∏ j, (t (e u i + e u j) (e v i + e v j) * (t (e u i) (e v i))⁻¹ * (t (e u j) (e v j))⁻¹) ^ W i j := by
    intro u v
    rw [hτ, hr']
    simp only [hψ, map_add (f := _), Pi.add_apply, map_zero, Pi.zero_apply, h0, one_zpow, Finset.prod_const_one, ← ht (e u _) (e v _)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, ofMul_one]
    abel
  rw [eq_mul_inv_of_mul_eq hc, hτ', hτ', hτ']
  simp only [Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply,
    add_zero, h0]
  have e1 : ∀ i j, e a i + e a j + (e a' i + e a' j) = e a i + e a' i + (e a j + e a' j) := fun i j => by abel
  simp only [e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul, ofMul_one, smul_zero, Finset.sum_const_zero]
  abel

theorem cubV_prod (hG : GlobalFnsSt) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {M' : RigLB A} {M : RigLB B} (c' : CubicalStr A M') (c : CubicalStr B M) {N : Type} [Fintype N]
    (P : N → (A ⟶ B)) (hP : ∀ k, IsMonHom (P k)) (φ : N → (A.left ⟶ B.left)) (hφ : ∀ k, (P k).left = φ k) (n : N → ℤ)
    (w : LB.Iso M'.L (LB.LinComb M.L φ n)) (hw : w.IsGen) {T : Over S} (z : T.left) (J J') (hJ : Good M.L z J)
    (hJ' : Good M'.L z J') (x x' y : T ⟶ A) (om : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ)
    (hom : om = fun p => bwg w p.left z (fun k => J (p.left ≫ φ k)) (J' p.left)) :
    cubV c' z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y *
      (om 1)⁻¹) = ∏ k, cubV c z J (x ≫ P k) (x' ≫ P k) (y ≫ P k) ^ n k := by
  subst hom
  let ρ : N → ((G3 A).left ⟶ (G3 B).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ A (x3 A) a ≫ φ k = ρ k ≫ thφ B (x3 B) a := fun k a => by
    rw [← hφ k]
    letI := hP k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over S} (a b c : T ⟶ A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := φ) (εp := n) M.isLB M'.isLB w hw (ε := thε) hψ
    c'.isGen c.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV c' (T := 𝟙_ (Over S)) s I') := isCub_cubV c' hI'
      have C : IsCub (cubV c (T := 𝟙_ (Over S)) s I) := isCub_cubV c hI
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A) 1 1
        (fun q => bwg w q s (fun i => I (q ≫ φ i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := hP k
      have o : (1 : 𝟙_ (Over S) ⟶ A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ n k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bwg w q z (fun i => J (q ≫ φ i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ Q D' r W pr xe T hn a a' b
  obtain ⟨hpr, -, hcp, w, hw, hpsi⟩ := T
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.M.L y J :=
    ⟨fun ψ => (exists_chart Q.M.isLB (ψ y)).choose, fun ψ => (exists_chart Q.M.isLB (ψ y)).choose_spec⟩
  let P : (Fin r × Fin r) × Fin 4 → (D'.P.A ⟶ Q.B) := fun k => ![pr k.1.1 * pr k.1.2, pr k.1.1, pr k.1.2, 1] k.2
  have hPh : ∀ k, IsMonHom (P k) := by
    rintro ⟨⟨i, j⟩, m⟩
    have := hpr i
    have := hpr j
    fin_cases m
    · exact GlobalTheory.Serre.isMonHom_mul _ _
    · exact hpr i
    · exact hpr j
    · exact GlobalTheory.Serre.isMonHom_one
  have hPl : ∀ k, (P k).left = tensφ pr k := by
    rintro ⟨⟨i, j⟩, m⟩
    fin_cases m <;> rfl
  have key := cubV_prod hG D'.P.isAb D'.cub Q.cub P hPh (tensφ pr) hPl (tensε W) w hw (T := TK R) y J J' hJ hJ'
    (cP D' _ a) (cP D' _ a') (cP D' _ b) _ rfl
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left) * ∏ i, ∏ j, val (Q.tau (xe u i) (xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => hpsi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have c0 : cP D' (TK R) 0 = 1 := by
    have := cPoint_add D' (TK R) 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hP : ∀ u k, cP D' (TK R) u ≫ P k = toUnit (TK R) ≫ Q.c (![xe u k.1.1 + xe u k.1.2, xe u k.1.1, xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ pr i = toUnit (TK R) ≫ Q.c (xe u i) := fun i => by
      rw [cP, Category.assoc, hcp]
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · show cP D' (TK R) u ≫ (pr i * pr j) = toUnit (TK R) ≫ Q.c (xe u i + xe u j)
      rw [MonObj.comp_mul, e, e, Q.c_add, MonObj.comp_mul]
    · exact e i
    · exact e j
    · show cP D' (TK R) u ≫ 1 = toUnit (TK R) ≫ Q.c 0
      rw [q0, MonObj.comp_one, MonObj.comp_one]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV Q.cub y J (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v) = val (Q.tau u v) (𝟙 _) y J * val (Q.tau u' v) (𝟙 _) y J * (val (Q.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← Q.tau_add u u' v y J hJ, mul_comm, inv_mul_cancel_left]
  have hI := interchange (fun u v => val (Q.tau u v) (𝟙 _) y J) (fun u v => Q.tau_symm u v y J hJ) (fun u u' v => by
    have := (isCub_cubV Q.cub hJ).s12 (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v)
    rw [hC, hC, _root_.mul_assoc, _root_.mul_assoc, mul_comm, mul_comm (val (Q.tau u _) (𝟙 _) y J)] at this
    first | exact this | exact this.symm)
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0] at key
  refine alg W xe
    (fun u => bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (Q.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b
    (Q.val_tau_zero 0 y J hJ) hI hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.PolTensBimult
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

theorem uAct_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  intro E _ _ _ H Dw l Xo c o Ω _ _ _ R R' h P P' φ hφ hL act u hact hU

  have inj : ∀ {T : Over (Sp R')} {x y : T ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y := fun {T x y} e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  let act' : 𝓞 E → (P'.A ⟶ P'.A) := fun a => Over.homMk (hφ.1.lift (φ ≫ (act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hφ.1.w])) (hφ.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hφ.1.lift_fst _ _ _
  have pa : ∀ {T : Over (Sp R')} (x : T ⟶ P'.A) a, pushPt hφ.1.w (x ≫ act' a) = pushPt hφ.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have hact' : ∀ a, IsMonHom (act' a) := fun a => isMonHom_of_mul _ fun T x y => inj (by
    have := hact a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  refine ⟨act', hact', ha, ?_⟩

  obtain ⟨G, _, α, β, hα, hβ, hLG, hf⟩ := hU
  set g := (Subalgebra.inclusion (ratHull_mono h)).toRingHom with hg
  have hG := isGrpPullback_pullback G (spMap g)
  have e : spMap g ≫ spMap (toRat R) = spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hα₀ : IsGrpPullback ((Over.pullback (spMap g)).obj G) P.A
      (spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom) (pullback.fst _ _ ≫ α) := (hG.comp hα).congr e rfl
  have w : (pullback.fst G.hom (spMap g) ≫ α) ≫ P.A.hom =
      (((Over.pullback (spMap g)).obj G).hom ≫ spMap (toRat R')) ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [Category.assoc]; exact hα₀.1.w
  have e₁ := hφ.1.lift_fst _ _ w
  have hα' := hφ.cancel (hα₀.congr rfl e₁.symm) (hφ.1.lift_snd _ _ w)
  have hβ' := (hG.comp hβ).congr (Category.assoc _ _ _).symm rfl
  refine ⟨_, _, hφ.1.lift _ _ w, pullback.fst _ _ ≫ β, hα', hβ', ?_, fun a => ?_⟩
  · exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _)
      (GenSpread.lbIso_pull_of_lbIso hL _ e₁.symm) (GenSpread.lbIso_pull_comp _ rfl rfl hLG)
  · obtain ⟨f, hfα, hfβ⟩ := hf a
    have hfl : ((Over.pullback (spMap g)).map f).left ≫ pullback.fst G.hom (spMap g) = pullback.fst G.hom (spMap g) ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (spMap g)).map f, ?_, ?_⟩
    · apply hφ.1.hom_ext
      · rw [Category.assoc, e₁, Category.assoc, ha, ← Category.assoc (hφ.1.lift _ _ w), e₁,
          ← Category.assoc _ (pullback.fst _ _), hfl, Category.assoc, hfα, Category.assoc]
      · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, Over.w, hφ.1.lift_snd, ← Category.assoc, Over.w]
    · rw [← Category.assoc, hfl, Category.assoc, hfβ, Category.assoc]

end GlobalTheory.UCovSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_add_chart : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  intro R _ _ A N σ t t' t'' h j
  show GlobalTheory.FieldBaseChange.pullFn _ _ (t''.f j) =
    GlobalTheory.FieldBaseChange.pullFn _ _ (t.f j) + GlobalTheory.FieldBaseChange.pullFn _ _ (t'.f j)
  rw [h j]
  exact map_add _ _ _

end GlobalTheory.Mum.Conj
end
