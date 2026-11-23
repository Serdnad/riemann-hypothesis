module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Heat

theorem fractionField_derivation_pow_logDeriv {Ω : Type} [CommRing Ω] [IsDomain Ω] (D : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) {c : FractionRing Ω} (hc : c ≠ 0) (k : ℕ) :
    D (c ^ k) = c ^ k * ((k : FractionRing Ω) * (D c / c)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, smul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
    ring

theorem fractionField_derivation_pow_mul_logDeriv {Ω : Type} [CommRing Ω] [IsDomain Ω] (D : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) {c : FractionRing Ω} (hc : c ≠ 0) (k : ℕ) (g : FractionRing Ω) :
    D (c ^ k * g) = c ^ k * (D g + (k : FractionRing Ω) * (D c / c) * g) := by
  rw [Derivation.leibniz, fractionField_derivation_pow_logDeriv D hc, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.Heat


open GlobalTheory.Heat in
theorem GlobalTheory.Heat.ringOp_conj_pow : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Θᵀ = Θ → (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  intro Ω _ _ n d δ Θ hΘ h2 u p p' c hc
  have hs : ∀ (s : Finset (Fin n)) (D : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
    intro s D x
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  refine ⟨d - ∑ a, ∑ b, (Θ a b * (δ a c / c)) • δ b, u,
    p + d c / c - (1 / 2) * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c),
    p' - (1 / 2) * ∑ a, ∑ b, Θ a b * δ a (δ b c / c) + ∑ a, u a * (δ a c / c), ?_, ?_⟩
  · intro y hy
    rw [Derivation.sub_apply, hs, Finset.sum_eq_zero, sub_zero]
    intro a _
    rw [hs]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Derivation.smul_apply, hy, smul_zero]
  · intro k f
    have e1 : ∀ b, δ b (c ^ k * f) = c ^ k * (δ b f + (k : FractionRing Ω) * (δ b c / c) * f) :=
      fun b => fractionField_derivation_pow_mul_logDeriv (δ b) hc k f
    have e2 : ∀ a b, δ a (δ b (c ^ k * f)) = c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f) := by
      intro a b
      rw [e1, fractionField_derivation_pow_mul_logDeriv (δ a) hc]
      simp only [map_add (f := _), Derivation.leibniz, Derivation.map_natCast, smul_eq_mul]
      ring
    have e3 : d (c ^ k * f) = c ^ k * (d f + (k : FractionRing Ω) * (d c / c) * f) := fractionField_derivation_pow_mul_logDeriv d hc k f
    have hsym : ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f) = ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have := congrFun (congrFun hΘ a) b
      rw [Matrix.transpose_apply] at this
      rw [this]
    unfold ringOp
    simp only [e2, e3]
    simp only [e1, Derivation.sub_apply, hs, Derivation.smul_apply, smul_eq_mul]
    have hL : ∑ a, ∑ b, Θ a b * (c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f)) =
        c ^ k * (∑ a, ∑ b, Θ a b * δ a (δ b f) + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
          + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
          + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c)
          + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hU : ∑ a, u a * (c ^ k * (δ a f + (k : FractionRing Ω) * (δ a c / c) * f)) =
        c ^ k * (∑ a, u a * δ a f + (k : FractionRing Ω) * f * ∑ a, u a * (δ a c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hD : ∑ a, ∑ b, Θ a b * (δ a c / c) * δ b f = ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_assoc _ _ _
    have hh : (2 : FractionRing Ω) * (1 / 2) = 1 := mul_one_div_cancel h2
    rw [hL, hU, hD, hsym]
    linear_combination (c ^ k * f * ((k : FractionRing Ω) ^ 2 * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)
      + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * δ a (δ b c / c))) * hh
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

def VS {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k : ℕ) (s : FractionRing Ω) : Prop :=
  ∃ (r : R) (σ : SecM (𝟙 Y) L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) L x g k σ ω ∧
    (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * s

theorem VS.half {R Ω : Type} [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}}
    {L : LB Y} {x : Sp Ω ⟶ Y} {g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)} {k : ℕ} {s : FractionRing Ω}
    (h : VS φ L x g k (2 * s)) : VS φ L x g k s := by
  haveI : CharZero R := algebraRat.charZero R
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  refine ⟨2 * r, σ, ω, mul_ne_zero two_ne_zero hr, hv, ?_⟩
  rw [he, map_mul, map_mul, map_ofNat, map_ofNat]
  ring

theorem ringOp_sub {Ω : Type} [CommRing Ω] {n : ℕ} (d₁ d₂ : Ω → Ω) (dd : Fin n → Ω → Ω)
    (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) Ω) (u₁ u₂ : Fin n → Ω) (p₁ p₁' p₂ p₂' : Ω) (k : ℕ) (f : Ω) :
    ringOp d₁ dd Θ₁ u₁ p₁ p₁' k f - ringOp d₂ dd Θ₂ u₂ p₂ p₂' k f =
      ringOp (fun y => d₁ y - d₂ y) dd (Θ₁ - Θ₂) (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k f := by
  simp only [ringOp, Matrix.sub_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem bracket {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (hl : ∀ a x y, dd a (x * y) = x * dd a y + y * dd a x)
    (ha : ∀ a x y, dd a (x + y) = dd a x + dd a y)
    (Θ : Matrix (Fin n) (Fin n) Ω) (hΘ : Θᵀ = Θ) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (b c : Ω) :
    b * (ringOp d dd Θ u p p' (k + k) (b * c) - b * ringOp d dd Θ u p p' k c -
        c * ringOp d dd Θ u p p' k b) -
      c * (ringOp d dd Θ u p p' (k + k) (b * b) - b * ringOp d dd Θ u p p' k b -
        b * ringOp d dd Θ u p p' k b) =
      2 * ((k : Ω) * b * (b * d c - c * d b) - ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b)) := by
  have sym : ∀ a e, Θ e a = Θ a e := fun a e => by
    have := congrFun (congrFun hΘ a) e
    simpa [Matrix.transpose_apply] using this
  have swap : ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = ∑ a, ∑ e, Θ a e * (dd a b * dd e c) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [sym]; ring
  have s2 : ∀ f h : Ω, ∑ a, ∑ e, Θ a e * dd a (dd e (f * h)) =
      f * ∑ a, ∑ e, Θ a e * dd a (dd e h) + h * ∑ a, ∑ e, Θ a e * dd a (dd e f) +
        (∑ a, ∑ e, Θ a e * (dd a f * dd e h) + ∑ a, ∑ e, Θ a e * (dd a h * dd e f)) := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hl, ha, hl, hl]
    ring
  have s1 : ∀ f h : Ω, ∑ a, u a * dd a (f * h) = f * ∑ a, u a * dd a h + h * ∑ a, u a * dd a f := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hl]
    ring
  have swap' : ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = 0 := by
    rw [swap]; ring
  have t1 : ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b) =
      b * ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - c * ∑ a, ∑ e, Θ a e * (dd a b * dd e b) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  simp only [ringOp]
  rw [s2, s2, s1, s1, t1, hd, hd]
  push_cast
  linear_combination b * swap'

end GlobalTheory.HeatSym
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntegralShift

theorem trF_prB {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) :
    (DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R)).left =
      (DegPre.prB Q (FractionRing R)).left ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left := by
  rw [← Over.comp_left]
  congr 1
  have e₁ : DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R) =
      DegPre.prB Q (FractionRing R) * (toUnit _ ≫ Q.c y) := lift_snd _ _
  have e₂ : (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]) = (toUnit Q.P.A ≫ Q.c y) * 𝟙 Q.P.A := rfl
  rw [e₁, e₂, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (DegPre.prB Q (FractionRing R) ≫ toUnit _) (toUnit _), mul_comm]

theorem sval_constFn_smul {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R) (s : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (constFn p ⊤ a • s) r z J =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval s r z J := by
  have hm := hJ.mem φ r
  refine (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans ((GlobalTheory.HeatMod.gs_constFn_eq_germConstHom p r z a).trans ?_)) rfl)
  exact (gs_eq (r ≫ p) z ⊤ trivial _).symm

theorem exists_shift_of_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) (N : ℕ) (c : R) (uR : LB.Gen (LB.LinComb Q.P.L (Sum.elim (Q.famφB (0 + N • y)) (fun i => (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left ≫ Q.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen → (∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) N y 0) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * (val uR (DegPre.prB Q (FractionRing R)).left z J).val) → ∃ (w : ∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), (Q.P.A.left.presheaf.stalk z)ˣ) (Sh : Q.SecB N 0 → Q.SecB N (0 + N • y)), ∀ x : Q.SecB N 0, (∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval (Sh x) (𝟙 _) z J = sval x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left z J * (w z J).val) ∧ ∃ x₁ : Q.SecB N (0 + N • y), ShiftEq Q N y 0 x x₁ 0 x₁ ∧ ∀ (Z : Scheme.{0}) (X : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval x₁ X z J = gs (X ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval (Sh x) X z J := by
  intro R _ _ Q y N c uR huR H
  have ex : ∀ x : Q.SecB N 0, ∃ s₁ : Q.SecB N (0 + N • y),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Q.P.A.left) (z : Z) (J), Good Q.P.L z J →
        sval s₁ r z J = sval x (r ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left) z J *
          (val uR r z J).val := fun x => by
    obtain ⟨s₁, h⟩ := exists_sec Q.P.isLB (φ' := Q.famφB (0 + N • y)) (ε' := DegPre.famε N) (fun U _ h => by
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left uR huR)
    exact ⟨s₁, fun Z r z J hJ => (h Z r z J hJ).trans (sval_pullMulSec _ _ _ _ _ _ hJ)⟩
  choose Sh hSh using ex
  refine ⟨fun z J => val uR (𝟙 _) z J, Sh, fun x => ⟨fun z J hJ => ?_, constFn Q.P.A.hom ⊤ c • Sh x, ?_,
    fun Z X z J hJ => sval_constFn_smul _ _ _ _ _ hJ⟩⟩
  · rw [hSh x _ _ z J hJ, Category.id_comp]
  · intro u hu hc z J hJ
    rw [GlobalTheory.HeatMod.gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero, sval_constFn_smul _ _ _ _ _ hJ,
      hSh x _ _ z J hJ, H u hu hc z J hJ, trF_prB]
    ring

end GlobalTheory.IntegralShift
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecQuot

open TopologicalSpace

variable {X : Scheme.{0}} {L : LB X}

abbrev ch1 (L : LB X) (j : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) j

theorem mem_finOnePowerChartOpen_iff {j : Fin 1 → L.ι} {x : X} : x ∈ ch1 L j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem gm_secM_g {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z (ch1 L j ⊓ ch1 L j') ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) r z j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast]

abbrev M1 (L : LB X) (k : ℕ) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))

theorem germ_finOnePowerLineBundle_transition_eq_pow {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z ((M1 L k).U j ⊓ (M1 L k).U j') ((M1 L k).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := gm_secM_g k r z j j' hj hj'

theorem lineBundlePowChartOpen_le_finOnePowerChartOpen (J : PUnit → L.ι) : powChart L J ≤ ch1 L (fun _ => J PUnit.unit) :=
  fun _ h => mem_finOnePowerChartOpen_iff.2 (mem_powChart.1 h)

def toPow {k : ℕ} (s : SecM (𝟙 X) L k) : (lbPow L k).Sec :=
  powSecOfGerm k (fun J => resG X (lineBundlePowChartOpen_le_finOnePowerChartOpen J) (s.f fun _ => J PUnit.unit)) fun y J J' hJ hJ' => by
    have e := gs_compat s (𝟙 X) y (j := fun _ => J PUnit.unit) (j' := fun _ => J' PUnit.unit)
      (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    have e2 := germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    refine (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _).trans (e.trans ?_)
    refine (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J') hJ' _).symm).trans ?_
    rw [Units.val_pow_eq_pow_val]

theorem gs_toPow {k : ℕ} (s : SecM (𝟙 X) L k) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (J : PUnit → L.ι)
    (hJ : r z ∈ powChart L J) : gs r z _ (powFn (toPow s) J) = gs r z _ (s.f fun _ => J PUnit.unit) :=
  gs_res r z (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _

theorem exists_secM_of_pow {n N : ℕ} (hn : n = N) (u : (lbPow L n).Sec) :
    ∃ c : SecM (𝟙 X) L N, ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ ch1 L j →
      gs r z _ (c.f j) = gs r z _ (powFn u (fun _ => j 0)) := by
  subst hn
  have le : ∀ j : Fin 1 → L.ι, ch1 L j ≤ powChart L (fun _ => j 0) := fun j _ h => mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 h)
  refine ⟨GlobalTheory.LBGerm.secOfGerm (M := M1 L n) (fun j => resG X (le j) (powFn u (fun _ => j 0)))
    fun y (j j' : Fin 1 → L.ι) hj hj' => ?_, fun r z j hj => gs_res r z (le j) hj _⟩
  have e := gs_powFn_compat u (𝟙 X) y _ _ (le j hj) (le j' hj')
  have e2 := germ_finOnePowerLineBundle_transition_eq_pow n (𝟙 X) y j j' hj hj'
  refine (gs_res (𝟙 X) y (le j) hj _).trans (e.trans ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res (𝟙 X) y (le j') hj' _)).symm
  rw [Units.val_pow_eq_pow_val]

theorem gs_appLE₁ {Y Z : Scheme.{0}} (F : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ F ⁻¹ᵁ U) (r : Z ⟶ Y)
    (z : Z) (hz : r z ∈ V) (a : Γ(X, U)) : gs r z V ((F.appLE U V h).hom a) = gs (r ≫ F) z U a :=
  (gs_res r z h hz _).trans (gs_pull r F z U (h hz) a)

theorem valR_congr₁ {A : Type} [CommRing A] (x : Sp A ⟶ X) {U U' : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hU' : ⊤ ≤ x ⁻¹ᵁ U') (a : Γ(X, U)) (a' : Γ(X, U')) (h : ∀ z, gs x z U a = gs x z U' a') :
    valR x U a = valR x U' a' := by
  rw [valR, valR, dite_eq_left hU, dite_eq_left hU']
  refine congrArg _ (fn_ext fun z hz => ?_)
  rw [gs_appLE₁ _ _ _ _ _ _ hz, gs_appLE₁ _ _ _ _ _ _ hz]
  simp only [Category.id_comp]
  exact h z

theorem mem_of_top_le {A : Type} [CommRing A] {x : Sp A ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp A) :
    x z ∈ U := h (show z ∈ (⊤ : (Sp A).Opens) from trivial)

theorem valR_mul_pow_of_gs {A : Type} [CommRing A] (x : Sp A ⟶ X) {U V W : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (hW : ⊤ ≤ x ⁻¹ᵁ W) (c : Γ(X, U)) (f : Γ(X, V)) (s : Γ(X, W)) (m : ℕ)
    (h : ∀ z, gs x z U c = gs x z V f * gs x z W s ^ m) : valR x U c = valR x V f * valR x W s ^ m := by
  have hO : ⊤ ≤ x ⁻¹ᵁ (V ⊓ W) := fun z hz => ⟨hV hz, hW hz⟩
  have e1 : valR x V f = valR x (V ⊓ W) (resG X inf_le_left f) :=
    valR_congr₁ x hV hO _ _ fun z => (gs_res x z inf_le_left (mem_of_top_le hO z) f).symm
  have e2 : valR x W s = valR x (V ⊓ W) (resG X inf_le_right s) :=
    valR_congr₁ x hW hO _ _ fun z => (gs_res x z inf_le_right (mem_of_top_le hO z) s).symm
  have e3 : valR x U c = valR x (V ⊓ W) (resG X inf_le_left f * resG X inf_le_right s ^ m) :=
    valR_congr₁ x hU hO _ _ fun z => by
      rw [h z, gs_mul _ z _ (mem_of_top_le hO z), GlobalTheory.LBGerm.gs_pow _ z _ (mem_of_top_le hO z),
        gs_res x z inf_le_left (mem_of_top_le hO z), gs_res x z inf_le_right (mem_of_top_le hO z)]
  rw [e1, e2, e3, valR, valR, valR, dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_mul, map_mul, map_pow, map_pow]

theorem nonzeroLocus_toPow {k : ℕ} (s : SecM (𝟙 X) L k) : nonzeroLocus (toPow s) = nonzeroLocus s := by
  refine nonzeroLocus_eq_of (toPow s) _ (fun y hy => ?_) fun y J hJ => ?_
  · have ⟨j, hj⟩ : ∃ j : Fin 1 → L.ι, y ∈ ch1 L j := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j 0, mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 hj)⟩
  · have e : gs (𝟙 X) y _ ((toPow s).f J) = gs (𝟙 X) y _ (s.f fun _ => J PUnit.unit) := gs_toPow s (𝟙 X) y J hJ
    rw [e]
    exact (mem_nonzeroLocus_iff_isUnit s (k := fun _ => J PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ)).symm

theorem extend_part [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) {k : ℕ} (s : SecM (𝟙 X) L k)
    (f : Γ(X, nonzeroLocus s)) : ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N,
      ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i → r z ∈ nonzeroLocus s →
        gs r z _ (c.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  have hs' := nonzeroLocus_toPow s
  have le : ∀ J : PUnit → L.ι, nonzeroLocus (toPow s) ⊓ powChart L J ≤ nonzeroLocus s :=
    fun J => inf_le_left.trans hs'.le
  obtain ⟨N₀, hN₀⟩ := exists_sec_eq_pow_mul (m := 0) hL (toPow s) (fun J => resG X (le J) f)
    (GlobalTheory.LBGerm.mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' hy hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
      exact (gs_res (𝟙 X) y (le J) ⟨hy, hJ⟩ f).trans (gs_res (𝟙 X) y (le J') ⟨hy, hJ'⟩ f).symm)
  refine ⟨N₀, fun m N hm hN => ?_⟩
  obtain ⟨u, hu⟩ := hN₀ m hm
  obtain ⟨c, hc⟩ := exists_secM_of_pow (show 0 + k * m = N by omega) u
  refine ⟨c, fun r z i hi hz => ?_⟩
  have hJ : r z ∈ powChart L (fun _ => i) := mem_powChart.2 hi
  have hy : r z ∈ nonzeroLocus (toPow s) ⊓ powChart L (fun _ => i) := ⟨by rw [hs']; exact hz, hJ⟩
  have e := congrArg (gs r z _) (hu (fun _ => i))
  rw [gs_res r z _ hy, gs_mul r z _ hy, GlobalTheory.LBGerm.gs_pow r z _ hy, gs_res r z _ hy, gs_res r z _ hy] at e
  rw [hc r z (fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi), e, gs_toPow s r z _ hJ, _root_.mul_comm]

theorem quot_part {k : ℕ} (s : SecM (𝟙 X) L k) (m N : ℕ) (hN : N = k * m) (ρ : SecM (𝟙 X) L N) :
    ∃ f : Γ(X, nonzeroLocus s), ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i →
      r z ∈ nonzeroLocus s →
      gs r z _ (ρ.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  subst hN
  have loc : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X, X.basicOpen (s.f j)),
      resG X (X.basicOpen_le _) (ρ.f j) = a * resG X (X.basicOpen_le _) (s.f j) ^ m := fun j => by
    obtain ⟨b, hb⟩ := (show IsUnit (resG X (X.basicOpen_le (s.f j)) (s.f j)) from
      X.toRingedSpace.isUnit_res_basicOpen (s.f j)).exists_left_inv
    refine ⟨resG X (X.basicOpen_le _) (ρ.f j) * b ^ m, ?_⟩
    have key : ∀ {R : Type} [CommRing R] (x y c : R), c * y = 1 → x = x * c ^ m * y ^ m := fun x y c h => by
      rw [_root_.mul_assoc, ← _root_.mul_pow, h, _root_.one_pow, _root_.mul_one]
    exact key _ _ _ hb
  choose a ha using loc
  have hga : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ X.basicOpen (s.f j) →
      gs r z _ (ρ.f j) = gs r z _ (a j) * gs r z _ (s.f j) ^ m := fun r z j hz => by
    have e := congrArg (gs r z _) (ha j)
    have e1 := gs_res r z (X.basicOpen_le (s.f j)) hz (ρ.f j)
    have e2 := gs_res r z (X.basicOpen_le (s.f j)) hz (s.f j)
    have e3 := gs_mul r z _ hz (a j) (resG X (X.basicOpen_le (s.f j)) (s.f j) ^ m)
    have e4 := GlobalTheory.LBGerm.gs_pow r z _ hz (resG X (X.basicOpen_le (s.f j)) (s.f j)) m
    exact e1.symm.trans (e.trans (e3.trans (congrArg _ (e4.trans (congrArg (· ^ m) e2)))))
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (s.f j)) (nonzeroLocus s)
    (fun j => homOfLE (GlobalTheory.basicOpen_le_nonzeroLocus s j)) le_rfl a (fun i j => fn_ext fun y hy => by
      have hi : y ∈ ch1 L i := X.basicOpen_le _ hy.1
      have hj : y ∈ ch1 L j := X.basicOpen_le _ hy.2
      refine (gs_res (𝟙 X) y inf_le_left hy (a i)).trans
        (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy (a j)).symm)
      have u : IsUnit (gs (𝟙 X) y _ (s.f i) ^ m) :=
        ((GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y _ hi _).2 hy.1).pow m
      refine u.mul_right_cancel ?_
      rw [← hga (𝟙 X) y i hy.1, gs_compat ρ (𝟙 X) y hi hj, gs_compat s (𝟙 X) y hi hj, hga (𝟙 X) y j hy.2,
        germ_finOnePowerLineBundle_transition_eq_pow (k * m) (𝟙 X) y i j hi hj, germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y i j hi hj, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val]
      ring)
  refine ⟨f, fun r z i hi hz => ?_⟩
  have hz' : r z ∈ X.basicOpen (s.f fun _ => i) := (mem_nonzeroLocus_iff_basicOpen s (k := fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi)).1 hz
  rw [hga r z _ hz', ← hf (fun _ => i)]
  exact congrArg (· * _) (gs_res r z (GlobalTheory.basicOpen_le_nonzeroLocus s _) hz' f)

theorem valR_secM_eq_mul_pow : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  intro X _ _ L hL F _ ξ j₀ hj₀ k s hs
  have hc : ⊤ ≤ ξ ⁻¹ᵁ ch1 L (fun _ => j₀) := fun z hz => mem_finOnePowerChartOpen_iff.2 (hj₀ hz)
  refine ⟨fun f => ?_, fun m N hN ρ => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := extend_part hL s f
    refine ⟨m₀, fun m N hm hN => ?_⟩
    obtain ⟨c, hc'⟩ := hm₀ m N hm hN
    exact ⟨c, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hc' ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩
  · obtain ⟨f, hf⟩ := quot_part s m N hN ρ
    exact ⟨f, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hf ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩

end GlobalTheory.SecQuot
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperator_conj_unitPow_corrections : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  first | exact @GlobalTheory.HeatConj.op_pow_mul | exact GlobalTheory.HeatConj.op_pow_mul | (intros; apply GlobalTheory.HeatConj.op_pow_mul <;> assumption)
end
