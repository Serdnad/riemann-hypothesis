module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle036
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def valHom (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = valHom x U h f := by
  unfold valR
  rw [dite_eq_left h]
  rfl

theorem valR_mul (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_res (x : Sp R ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_eq x V h, valR_eq x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]
  rfl

theorem valR_spMap {R' : Type} [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U ∧ ∀ f, valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap φ) y))
  refine ⟨h', fun f => ?_⟩
  rw [valR_eq _ U h', valR_eq x U h]
  have e : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ).hom f
  rw [e, Category.assoc, n]

theorem isUnit_valR_iff (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    IsUnit (valR x U f) ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  rw [valR_eq x U h]
  have e : IsUnit (valHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv _
  rw [e]
  have b := Scheme.basicOpen_appLE x ⊤ U h f
  constructor
  · intro hu
    rw [Scheme.basicOpen_of_isUnit _ hu] at b
    exact b.le.trans inf_le_right
  · intro hu
    rw [inf_eq_left.2 hu] at b
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => ?_
    exact (Scheme.mem_basicOpen _ _ y hy).1 (b.ge hy)

theorem top_le_iff [IsLocalRing R] (x : Sp R ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint R) ∈ U :=
  ⟨fun h => h (Set.mem_univ _), fun h =>
    ((IsLocalRing.closed_point_mem_iff (R := R) (U := x ⁻¹ᵁ U)).1 h).ge⟩

theorem exists_unit_charts (H : LB X) (x : Sp R ⟶ X) (l l' : H.ι) (h : ⊤ ≤ x ⁻¹ᵁ H.U l)
    (h' : ⊤ ≤ x ⁻¹ᵁ H.U l') :
    ∃ c : Rˣ, ∀ s : H.Sec, valR x (H.U l) (s.f l) = c * valR x (H.U l') (s.f l') := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (H.U l ⊓ H.U l') := fun y hy => ⟨h hy, h' hy⟩
  refine ⟨Units.map (valHom x _ hh).toMonoidHom (H.g l l'), fun s => ?_⟩
  rw [← valR_res x (inf_le_left : H.U l ⊓ H.U l' ≤ H.U l) hh,
    ← valR_res x (inf_le_right : H.U l ⊓ H.U l' ≤ H.U l') hh]
  have := s.compat l l'
  change valR x _ ((X.presheaf.map _).hom _) = _
  rw [this, valR_mul x _ hh, valR_eq x _ hh]
  rfl

variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem crd_exists [IsLocalRing R] (hH : H.IsLB) (s : J → H.Sec) (x : Sp R ⟶ X) : ∃ v, Crd H s x v := by
  have : x (IsLocalRing.closedPoint R) ∈ ⨆ i, H.U i := by rw [hH.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨_, l, 1, (top_le_iff x _).2 hl, fun _ => rfl⟩

theorem crd_unique {x : Sp R ⟶ X} {v v' : J → R} (h : Crd H s x v) (h' : Crd H s x v') :
    ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨l', c', hl', hv'⟩ := h'
  obtain ⟨u, hu⟩ := exists_unit_charts H x l' l hl' hl
  refine ⟨c' * u * c⁻¹, fun j => ?_⟩
  rw [hv, hv', hu, Units.val_mul, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]

theorem crd_isUnit_iff [IsLocalRing R] {x : Sp R ⟶ X} {v : J → R} (j : J) (h : Crd H s x v) :
    IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j) := by
  obtain ⟨l, c, hl, hv⟩ := h
  rw [hv, Units.isUnit_units_mul]
  constructor
  · intro hu
    exact ((isUnit_valR_iff x _ hl _).1 hu).trans
      (x.preimage_mono (le_iSup (fun k => X.basicOpen ((s j).f k)) l))
  · intro hu
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_iff x _).1 hu)
    have hk' := (top_le_iff x _).2 hk
    have hU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
    obtain ⟨u, hu⟩ := exists_unit_charts H x l k hl hU
    rw [hu, Units.isUnit_units_mul]
    exact (isUnit_valR_iff x _ hU _).2 hk'

theorem crd_map {R' : Type} [CommRing R'] (φ : R →+* R') {x : Sp R ⟶ X} {v : J → R} (h : Crd H s x v) :
    Crd H s (spMap φ ≫ x) (fun j => φ (v j)) := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨h₁, h₂⟩ := valR_spMap φ x _ hl
  refine ⟨l, Units.map φ.toMonoidHom c, h₁, fun j => ?_⟩
  beta_reduce
  rw [h₂, hv, map_mul]
  rfl

theorem crd_smul {x : Sp R ⟶ X} {v : J → R} (c : Rˣ) (h : Crd H s x v) :
    Crd H s x (fun j => (c : R) * v j) := by
  obtain ⟨l, c', hl, hv⟩ := h
  exact ⟨l, c * c', hl, fun j => by beta_reduce; rw [hv, Units.val_mul, _root_.mul_assoc]⟩

theorem crd_ratio {x : Sp R ⟶ X} {v : J → R} {i j : J} {W : X.Opens} {r : Γ(X, W)} (h : Crd H s x v)
    (hr : IsRatio (s j) (s i) W r) (hW : ⊤ ≤ x ⁻¹ᵁ W) : v j = valR x W r * v i := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ H.U l) := fun y hy => ⟨hW hy, hl hy⟩
  have := congrArg (valR x (W ⊓ H.U l)) (hr l)
  rw [valR_mul x _ hh, valR_res x _ hh, valR_res x _ hh, valR_res x _ hh] at this
  rw [hv, hv, this, mul_left_comm]

theorem crd_calculus : (∀ (X : Scheme.{0}) (H : LB X) (J : Type) (s : J → H.Sec), H.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), (∃ v, Crd H s x v) ∧ (∀ v v', Crd H s x v → Crd H s x v' → ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j) ∧ ∀ v j, Crd H s x v → (IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j))) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (v : J → R), Crd H s x v → Crd H s (spMap φ ≫ x) (fun j => φ (v j))) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (c : Rˣ), Crd H s x v → Crd H s x (fun j => (c : R) * v j)) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (i j : J) (W : X.Opens) (r : Γ(X, W)), Crd H s x v → IsRatio (s j) (s i) W r → ⊤ ≤ x ⁻¹ᵁ W → v j = valR x W r * v i) :=
  fun _ _ _ s hH =>
    ⟨fun _ _ _ x => ⟨crd_exists hH s x, fun _ _ => crd_unique, fun _ j => crd_isUnit_iff j⟩,
      fun _ _ _ _ φ _ _ => crd_map φ, fun _ _ _ _ c => crd_smul c, fun _ _ _ _ _ _ _ _ => crd_ratio⟩

end GlobalTheory.ZH.CrdCalc
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm : ∀ (C : Type) [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → (∀ (k : ℕ) (p : N.QT k), k ≠ 0 → ∀ χ, ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k))) ∧ ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) χ, ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ := by
  first | exact @GlobalTheory.Ex.norm_QT_s_and_norm_txT | exact GlobalTheory.Ex.norm_QT_s_and_norm_txT | (intros; apply GlobalTheory.Ex.norm_QT_s_and_norm_txT <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

section Cube
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cub_rot (h : IsCub θ) (x y z : A) : θ x y z = θ z x y := by rw [h.s12, h.s01]

theorem cub_four (h : IsCub θ) (p q r s z : A) :
    θ (p * q) (r * s) z * θ p q z * θ r s z = θ (p * r) (q * s) z * θ p r z * θ q s z := by
  have a := h.coc (p * q) r s z
  have b := h.coc (p * r) q s z
  have c := h.coc q p r z
  rw [mul_right_comm p r q] at b
  rw [mul_comm q p, h.s01 q p, h.s01 q (p * r)] at c
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b c ⊢
  linear_combination (norm := abel) b - a + c

theorem cubN_mul_point (h : IsCub θ) (a : ℕ) (x y z : A) :
    cubN θ a 1 (x * y) z * θ x y z ^ a = cubN θ a 1 x z * cubN θ a 1 y z * θ (x ^ a) (y ^ a) z := by
  induction a with
  | zero => simp [cubN, h.face]
  | succ a ih =>
    have f := cub_four h (x ^ a) (y ^ a) x y z
    simp only [CubeBalance.cubN_succ, mul_pow, pow_succ]
    replace ih := congrArg Additive.ofMul ih
    replace f := congrArg Additive.ofMul f
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at ih f ⊢
    linear_combination (norm := abel) ih + f

theorem mulq_succ (θ : A → A → A → U) (σ : A → U) (n : ℕ) (x : A) :
    mulq θ σ (n + 1) x = mulq θ σ n x * (cubN θ n 1 x x / dbl θ σ x ^ n) := by
  rw [mulq, Finset.prod_range_succ, mulq]

theorem mulq_add (h : IsCub θ) (σ : A → U) (m n : ℕ) (x : A) :
    mulq θ σ (m + n) x * dbl θ σ x ^ (m * n) =
      mulq θ σ m x * mulq θ σ n x * (cubN θ m 1 x (x ^ n) * cubN θ n 1 x x ^ m) := by
  induction m with
  | zero => simp [mulq, cubN]
  | succ m ih =>
    have c := CubeBalance.cubN_add h m n x x
    rw [h.s12] at c
    rw [Nat.add_right_comm, mulq_succ, mulq_succ, CubeBalance.cubN_succ]
    replace ih := congrArg Additive.ofMul ih
    replace c := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih c ⊢
    linear_combination (norm := module) ih + c

end Cube

namespace NumB
variable {O : Type} [CommRing O] (B : NumB O)

theorem θ_mul_inv_inv (x y : B.A) : B.θ (x * y) x⁻¹ y⁻¹ * B.θ x x⁻¹ y = B.θ y y⁻¹ x⁻¹ := by
  have a := B.cub.coc x y y⁻¹ x⁻¹
  rwa [mul_inv_cancel, B.cub.face₂, one_mul, B.cub.s12, B.cub.s12 x y] at a

theorem σ_mul_symm (x y : B.A) : B.σ (x * y) * B.θ (x * y) x⁻¹ y⁻¹ = B.σ x * B.σ y := by
  have a := B.θ_mul_inv_inv y x
  have b := B.σ_mul x y
  rw [mul_comm y x, B.cub.s12] at a
  rw [← a, ← mul_assoc] at b
  exact mul_right_cancel b

theorem dbl_mul (x y : B.A) :
    dbl B.θ B.σ (x * y) * (B.θ (x * y) x y * B.θ x x y * B.θ y x y) =
      dbl B.θ B.σ x * dbl B.θ B.σ y := by
  have c := B.cub.coc x y (x * y)⁻¹ (x * y)
  have d := B.cub.coc y y⁻¹ x⁻¹ (x * y)
  rw [show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm, inv_mul_cancel_right], cub_rot B.cub x y] at c
  rw [mul_inv_cancel, B.cub.face, mul_comm y⁻¹, ← mul_inv, B.cub.s01 y⁻¹, cub_rot B.cub x⁻¹ y⁻¹] at d
  have a := B.cub.compat x x⁻¹ x y
  have b := B.cub.compat y y⁻¹ x y
  rw [mul_inv_cancel, B.cub.face, B.cub.s01 x⁻¹ x y] at a
  rw [mul_inv_cancel, B.cub.face, B.cub.s12 y⁻¹ x y, B.cub.s01 y⁻¹ y x] at b
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have a := E a; have b := E b; have c := E c; have d := E d; have s := E (B.σ_mul_symm x y)
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_one] at a b c d s ⊢
  linear_combination (norm := abel) c - d - a - b - s

theorem dbl_pow (a : ℕ) (x : B.A) :
    dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) =
      dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 := by
  induction a with
  | zero => simp [dbl, mulq, cubN, B.cub.face, B.σ_one]
  | succ a ih =>
    have d := B.dbl_mul (x ^ a) x
    rw [B.cub.s01 x (x ^ a), ← cub_rot B.cub (x ^ a) x] at d
    have n := B.cub.N_add a 1 x (x ^ a) x
    rw [B.cub.face, mul_one, one_mul, B.cub.s01 x (x ^ a)] at n
    rw [mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have n := E n
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d n ⊢
    linear_combination (norm := module) ih + d + n

theorem mulq_mul (a b : ℕ) (x : B.A) :
    mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) := by
  induction a with
  | zero => simp [mulq]
  | succ a ih =>
    have m := mulq_add B.cub B.σ (a * b) b x
    have c := CubeBalance.cubN_mul B.cub a b x (x ^ b)
    have d := B.dbl_pow b x
    rw [Nat.succ_mul, mulq_succ]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have m := E m; have c := E c; have d := E d
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih m c d ⊢
    linear_combination (norm := module) ih + m + c + a • d

theorem mulq_mul_point (a : ℕ) (x y : B.A) :
    mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y *
      (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) := by
  induction a with
  | zero => simp [mulq, cubN]
  | succ a ih =>
    have d := B.dbl_mul x y
    have f := cubN_mul_point B.cub a x y (x * y)
    have n₁ := B.cub.N_add a 1 x x y
    have n₂ := B.cub.N_add a 1 y x y
    have n₃ := B.cub.N_add a 1 x (y ^ a) y
    rw [B.cub.face, mul_one, one_mul] at n₁ n₂ n₃
    rw [cub_rot B.cub x y] at f
    rw [← cub_rot B.cub (y ^ a) y x] at n₃
    have c₁ := B.cub.compat (x ^ a) (y ^ a) x y
    have c₂ := B.cub.coc (x ^ a) (y ^ a) y x
    rw [B.cub.s12 (x ^ a * y ^ a), B.cub.s12 (x ^ a) (y ^ a * y)] at c₂
    rw [mulq_succ, mulq_succ, mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ y]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have f := E f; have n₁ := E n₁; have n₂ := E n₂; have n₃ := E n₃
    have c₁ := E c₁; have c₂ := E c₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d f n₁ n₂ n₃ c₁ c₂ ⊢
    linear_combination (norm := module) ih + f + n₁ + n₂ - n₃ - a • d - c₁ + c₂

theorem cubN_inv_inv (a : ℕ) (x : B.A) :
    cubN B.θ a 1 x⁻¹ x⁻¹ * B.θ x x⁻¹ x ^ a * (B.σ x * B.σ (x ^ a)) =
      cubN B.θ a 1 x x * B.θ x⁻¹ x x⁻¹ ^ a * B.σ (x ^ a * x) := by
  induction a with
  | zero => simp [cubN, B.σ_one]
  | succ a ih =>
    have s := B.σ_cub (x ^ a) x x
    have t := B.σ_cub x x x⁻¹
    have u := B.σ_inv x
    rw [inv_inv, mul_inv_cancel, mul_inv_cancel_right, B.σ_one, B.cub.s12 x⁻¹, B.cub.s12 x] at t
    rw [CubeBalance.cubN_succ, CubeBalance.cubN_succ, inv_pow, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have s := E s; have t := E t; have u := E u
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_one] at ih s t u ⊢
    linear_combination (norm := module) ih + s - t - u

theorem mulq_inv (a : ℕ) (x : B.A) :
    mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) := by
  induction a with
  | zero => simp [mulq, B.σ_one]
  | succ a ih =>
    have g := B.cubN_inv_inv a x
    have u := B.σ_inv x
    rw [mulq_succ, mulq_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have g := E g; have u := E u
    apply Additive.ofMul.injective
    simp only [dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at ih g u ⊢
    linear_combination (norm := module) ih + g + a • u

end NumB

theorem mulq_laws : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) :=
  fun _ _ B a b x y => ⟨B.mulq_mul a b x, B.mulq_mul_point a x y, B.dbl_pow a x, B.mulq_inv a x⟩

end GlobalTheory.Ex
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_vt_QT_le (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) (χ : N.X) :
    ‖N.vt p.1.2 χ‖ ≤ Real.exp (-((q (p.1.1.toAdd + k • χ) - q p.1.1.toAdd) / (k : ℝ) ^ 2)) := by
  rw [NumD.vt]
  simp only [Units.val_mul, norm_mul, h.ψ, h.norm_rep_generators_eq_exp p hk]
  refine (mul_le_of_le_one_right (by positivity) (h.th _)).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  have e : q (p.1.1.toAdd + k • χ) =
      q p.1.1.toAdd + (k : ℝ) ^ 2 * q χ + k * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (k • χ) = k * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (k • χ) = (k : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [e]
  field_simp
  ring

theorem tendsto_vt_QT (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) :
    Filter.Tendsto (N.vt p.1.2) Filter.cofinite (nhds 0) := by
  have inj : Function.Injective fun χ : N.X => p.1.1.toAdd + k • χ := fun a b e => by
    have e' : k • a = k • b := add_left_cancel e
    rw [← natCast_zsmul, ← natCast_zsmul] at e'
    exact smul_right_injective N.X (Int.natCast_ne_zero.2 hk) e'
  have t₁ := h.pos.comp inj.tendsto_cofinite
  have kp : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) 2
  have t₂ := (Filter.tendsto_atTop_add_const_right _ (-q p.1.1.toAdd) t₁).atTop_div_const kp
  have t₃ := Real.tendsto_exp_neg_atTop_nhds_zero.comp t₂
  refine squeeze_zero_norm (h.norm_vt_QT_le hk p) ?_
  simpa only [Function.comp_def, sub_eq_add_neg] using t₃

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem summable_vt_QT : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) :=
  fun _ _ _ _ _ _ h _ hk p =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (h.tendsto_vt_QT hk p)
end GlobalTheory.Ex
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.potModel_trans : ∀ (V K V₁ K₁ : Type) [CommRing V] [Field K] [Algebra V K] [CommRing V₁] [Field K₁] [Algebra V₁ K₁] [Algebra V V₁] [Algebra K K₁], (algebraMap V₁ K₁).comp (algebraMap V V₁) = (algebraMap K K₁).comp (algebraMap V K) → Module.Finite V V₁ → IsLocalHom (algebraMap V V₁) → ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (A₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₁)) [GrpObj A₁] (φ : A₁.left ⟶ A.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A₁ A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K₁)) φ → ∀ Q, _root_.GlobalTheory.SS.PotModel V₁ K₁ A₁ Q → _root_.GlobalTheory.SS.PotModel V K A Q := by
  intro V K V₁ K₁ _ _ _ _ _ _ _ _ hcomm hfin hloc A _ A₁ _ φ hφ Q hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, h1, h2, h3, h4, G, _, ⟨e, he⟩, hQ⟩ := hP
  letI : Algebra V W := ((algebraMap V₁ W).comp (algebraMap V V₁)).toAlgebra
  letI : Algebra K L := ((algebraMap K₁ L).comp (algebraMap K K₁)).toAlgebra
  have hA : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L))).obj A₁) A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L)) (pullback.fst A₁.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L)) ≫ φ) := by
    refine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.comp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A₁ _) hφ).congr ?_ rfl
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  obtain ⟨e', he', -⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso hA (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _)
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, h4, G, inferInstance, ⟨e ≪≫ e', ?_⟩, hQ⟩
  · show (algebraMap W L).comp ((algebraMap V₁ W).comp (algebraMap V V₁)) = ((algebraMap K₁ L).comp (algebraMap K K₁)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, h1, RingHom.comp_assoc, hcomm, RingHom.comp_assoc]
  · exact (RingHom.finite_algebraMap.mpr h2).comp (RingHom.finite_algebraMap.mpr hfin)
  · show IsLocalHom ((algebraMap V₁ W).comp (algebraMap V V₁))
    infer_instance
  · rw [Iso.trans_hom]
    infer_instance

end GlobalTheory.SS
end
