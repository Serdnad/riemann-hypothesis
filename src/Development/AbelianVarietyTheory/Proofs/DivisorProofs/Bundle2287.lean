module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem sgn_mem_rel_of_mem {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [sgn_ι]; exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem mul_ι_mem_rel {x : DR R B} (hx : x ∈ rel R δ) (ω : Ω[B⁄R]) : x * ι1 ω ∈ rel R δ := by
  have h := ι_mul ω (sgn x)
  rw [sgn_sgn] at h
  rw [← h]; exact Ideal.mul_mem_left _ _ (sgn_mem_rel_of_mem δ hx)

theorem mem_divPowerCompatFormRelSubmodule_two_iff {x : Om R B 2} : x ∈ N R δ 2 ↔ (x : DR R B) ∈ rel R δ := Iff.rfl

theorem wedge_mem_N {x y : Ω[B⁄R]} (h : x ∈ N1 R δ ∨ y ∈ N1 R δ) : wedge R B x y ∈ N R δ 2 := by
  rw [mem_divPowerCompatFormRelSubmodule_two_iff, coe_wedge]
  rcases h with h | h
  · exact mul_ι_mem_rel δ h y
  · exact Ideal.mul_mem_left _ _ h


variable (R) in
def kwedge : K1 R δ →ₗ[B] K1 R δ →ₗ[B] K R δ 2 :=
  LinearMap.liftQ₂ _ _ ((wedge R B).compr₂ (N R δ 2).mkQ)
    (fun x hx ↦ LinearMap.ext fun y ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inl hx)))
    (fun y hy ↦ LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inr hy)))

theorem kwedge_mk (x y : Ω[B⁄R]) :
    kwedge R δ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (wedge R B x y) := rfl

end Ring

section Ring2

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem kwedge_swap (x y : K1 R δ) : kwedge R δ x y = -kwedge R δ y x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, kwedge_mk, wedge_swap, Submodule.Quotient.mk_neg]

theorem divPowerCompatFunctionDifferential_mul (a b : B) : kd0 R δ (a * b) = a • kd0 R δ b + b • kd0 R δ a := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.leibniz, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul_eq_wedge_add (b : B) (x : K1 R δ) : kd1 R δ (b • x) = kwedge R δ (kd0 R δ b) x + b • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, divPowerCompatFunctionDifferential_apply, kwedge_mk, dOne_smul, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_wedge_of_closed {x y : K1 R δ} (hx : kd1 R δ x = 0) (hy : kd1 R δ y = 0) : kd2 R δ (kwedge R δ x y) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [divPowerCompatOneFormDerivative_mk, Submodule.Quotient.mk_eq_zero, mem_divPowerCompatFormRelSubmodule_two_iff, coe_dOne] at hx hy
  rw [kwedge_mk, divPowerCompatTwoFormDerivative_mk, Submodule.Quotient.mk_eq_zero]
  change dDR R B (ι1 x * ι1 y) ∈ rel R δ
  rw [dDR_mul, sgn_ι, neg_mul]
  exact add_mem (neg_mem (Ideal.mul_mem_left _ _ hy)) (mul_ι_mem_rel δ hx y)

variable {δ} {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul_function (b : B) (x : K1 R δ) : km1 h hd (b • x) = α b • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, h.oneFormMap_smul_semilinear, Submodule.Quotient.mk_smul]

theorem km_kwedge (x y : K1 R δ) : km h hd 2 (kwedge R δ x y) = kwedge R' δ' (km1 h hd x) (km1 h hd y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, km_mk, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, kwedge_mk, h.mOm_wedge]

end Ring2

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

def cupK (a b : (KK κ t).T1) : (KK κ t).T2 :=
  (fun _ T' T'' φ ψ ↦ (show T''.B from (KK κ t).M0.map ψ (a.1 _ T' φ)) * (show T''.B from b.1 T' T'' ψ),
    fun T T' φ ↦ (show T'.B from a.1 T T' φ) • b.2 T' - (show T'.B from b.1 T T' φ) • (KK κ t).M1.map φ (a.2 T),
    fun T ↦ kwedge R T.δ (a.2 T) (b.2 T))

theorem crystallineCompatibleFormsComplex_cocycleOne_components (k : (KK κ t).Z1) :
    (∀ {T T' T'' : Thick κ t} (φ : T ⟶ T') (ψ : T' ⟶ T''),
      (k.1.1 T T'' (φ ≫ ψ) : T''.B) = ψ.φ (k.1.1 T T' φ) + k.1.1 T' T'' ψ) ∧
    (∀ {T T' : Thick κ t} (φ : T ⟶ T'), k.1.2 T' = (KK κ t).M1.map φ (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ)) ∧
    ∀ T : Thick κ t, kd1 R T.δ (k.1.2 T) = 0 := by
  have h : (KK κ t).D1 k.1 = 0 := k.2
  refine ⟨fun {T T' T''} φ ψ ↦ ?_, fun {T T'} φ ↦ ?_, fun T ↦ ?_⟩
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change ψ.φ (k.1.1 T T' φ) - k.1.1 T T'' (φ ≫ ψ) + k.1.1 T' T'' ψ = 0 at this
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrArg (fun c ↦ c.2.1) h) T) T') φ
    change k.1.2 T' - (KK κ t).M1.map φ (k.1.2 T) - kd0 R T'.δ (k.1.1 T T' φ) = 0 at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · exact congrFun (congrArg (fun c ↦ c.2.2) h) T

end Site

section Site2

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem cupK_mem (a b : (KK κ t).Z1) : cupK a.1 b.1 ∈ (KK κ t).Z2 := by
  obtain ⟨ha1, ha2, ha3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components a
  obtain ⟨hb1, hb2, hb3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components b
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · change χ.φ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ) + χ.φ (a.1.1 T T'' (φ ≫ ψ)) * b.1.1 T'' T''' χ =
      (ψ ≫ χ).φ (a.1.1 T T' φ) * b.1.1 T' T''' (ψ ≫ χ) + χ.φ (a.1.1 T' T'' ψ) * b.1.1 T'' T''' χ
    rw [ha1 φ ψ, hb1 ψ χ, Thick.comp_φ, map_mul, map_add (f := _)]
    ring
  · have hs : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B) (x : K1 R T.δ),
        (KK κ t).M1.map φ (r • x) = φ.φ r • (KK κ t).M1.map φ x := fun φ r x ↦ divPowerCompatOneFormMap_smul_function (SemiHom.of_algHom φ.φ) φ.dp r x
    have hd : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B),
        (KK κ t).M1.map φ (kd0 R T.δ r) = kd0 R T'.δ (φ.φ r) := fun φ r ↦ divPowerCompatOneFormMap_functionDifferential (SemiHom.of_algHom φ.φ) φ.dp r
    change (a.1.1 T T'' (φ ≫ ψ) : T''.B) • b.1.2 T'' - (b.1.1 T T'' (φ ≫ ψ) : T''.B) • (KK κ t).M1.map (φ ≫ ψ) (a.1.2 T) =
      (KK κ t).M1.map ψ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T)) +
      ((a.1.1 T' T'' ψ : T''.B) • b.1.2 T'' - (b.1.1 T' T'' ψ : T''.B) • (KK κ t).M1.map ψ (a.1.2 T')) +
      kd0 R T''.δ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ)
    rw [ha1 φ ψ, hb1 φ ψ, (KK κ t).M1.map_comp, hb2 ψ, ha2 φ]
    simp only [map_add (f := _), map_sub, hs, hd, divPowerCompatFunctionDifferential_mul, smul_add, smul_sub, add_smul]
    module
  · have hd1 : kd1 R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) = 0 :=
      ((KK κ t).diffOne_natural φ _).trans (by rw [show (KK κ t).d1 T (a.1.2 T) = 0 from ha3 T, map_zero])
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = (KK κ t).M2.map φ (kwedge R T.δ (a.1.2 T) (b.1.2 T)) +
      kd1 R T'.δ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T))
    rw [map_sub, divPowerCompatOneFormDerivative_smul_eq_wedge_add, divPowerCompatOneFormDerivative_smul_eq_wedge_add, hb3 T', hd1, smul_zero, smul_zero, add_zero, add_zero]
    change _ = km (SemiHom.of_algHom φ.φ) φ.dp 2 _ + _
    rw [km_kwedge]
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = kwedge R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) ((KK κ t).M1.map φ (b.1.2 T)) + _
    rw [ha2 φ, hb2 φ]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [kwedge_swap T'.δ (kd0 R T'.δ (b.1.1 T T' φ))]
    abel
  · exact divPowerCompatTwoFormDerivative_wedge_of_closed T.δ (ha3 T) (hb3 T)

end Site2

section Main

variable {D : Data} (Λ : Lift D)

theorem Lift.lift_res2_cup {k k' : (KK D.κ D.t).T1} {w w' : Tot1 (OAff D.s)}
    (hk : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k) w) (hk' : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k') w') :
    Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 (cupK k k')) (cupTot (OAff D.s) w w') := by
  have e1 : ∀ U V a, (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w.1 U V a) := hk.1
  have e1' : ∀ U V a, (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w'.1 U V a) := hk'.1
  have e2 : ∀ U, k.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w.2 U)) := hk.2
  have e2' : ∀ U, k'.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w'.2 U)) := hk'.2
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · change (Λ.L.map b).φ (k.1 _ _ (Λ.L.map a)) * (k'.1 _ _ (Λ.L.map b) : (Λ.L.obj W).B) =
      Λ.e W (mp (OAff D.s) b (w.1 U V a) * w'.1 V W b)
    rw [e1, e1', map_mul, Λ.nat]
  · have key : ∀ x, (SemiHom.of_algHom (Λ.L.map a).φ).m1 ((Λ.semi U).m1 x) = (Λ.semi V).m1 (p1 (OAff D.s) a x) :=
      fun x ↦ (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom _) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
        (fun b ↦ (Λ.nat a b).symm) x).trans
        (SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
          (fun _ ↦ rfl) x).symm
    change (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • k'.2 (Λ.L.obj V) -
        (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (k.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi V).m1 (w.1 U V a • w'.2 V - w'.1 U V a • p1 (OAff D.s) a (w.2 U)))
    rw [e1, e1', e2' V, e2 U, divPowerCompatOneFormMap_mk, key, map_sub, SemiHom.oneFormMap_smul_semilinear, SemiHom.oneFormMap_smul_semilinear, Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
    rfl
  · change kwedge D.R (Λ.L.obj U).δ (k.2 (Λ.L.obj U)) (k'.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi U).mOm 2 (wedge D.R _ (w.2 U) (w'.2 U)))
    rw [e2, e2', kwedge_mk, SemiHom.mOm_wedge]

theorem Lift.lift_rel2_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' →
    Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  intro D Λ a b h h' ha hb
  obtain ⟨k, f, w, hf, hw, hkf, hr⟩ := ha
  obtain ⟨k', g, w', hg, hw', hkg, hr'⟩ := hb
  refine ⟨⟨cupK k.1 k'.1, cupK_mem k k'⟩, cupZ _ f g, cupZZ _ w w', ?_, ?_, ?_, Λ.lift_res2_cup hr hr'⟩
  · rw [← hf, ← hg]; rfl
  · rw [← hw, ← hw']; rfl
  · funext T T' T'' φ ψ
    change ψ.φ (k.1.1 T T' φ) * (k'.1.1 T' T'' ψ : T''.B) = ψ.φ (f.1 T T' φ) * g.1 T' T'' ψ
    rw [hkf, hkg]

end Main

end GlobalTheory.PDForm
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem rel_mul_mem_right {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
    (δ : DividedPowers J) {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [ι_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

section Poly

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
  {Q : PDPoly B} [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
  (h : SemiHom (RingHom.id R) (algebraMap B Q.P))

def pdGen : Set (DR R Q.P) :=
  {x | ∃ n α, x = Q.e n • h.mDR α} ∪ {x | ∃ n α, x = Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)} ∪
    (rel R η : Set (DR R Q.P))

theorem pdGen_mem_one (n : ℕ) (α : DR R B) : Q.e n • h.mDR α ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_left _ ⟨n, α, rfl⟩)

theorem pdGen_mem_two (n : ℕ) (α : DR R B) : Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨n, α, rfl⟩)

theorem pdGen_mem_rel {x : DR R Q.P} (hx : x ∈ rel R η) : x ∈ pdGen η h :=
  Set.mem_union_right _ hx

theorem smul_gen_mem (b : Q.P) : ∀ α : DR R B,
    b • h.mDR α ∈ AddSubgroup.closure (pdGen η h) ∧
      b • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    exact fun α ↦ ⟨AddSubgroup.subset_closure (pdGen_mem_one η h n α),
      AddSubgroup.subset_closure (pdGen_mem_two η h n α)⟩
  | zero => intro α; simp only [zero_smul]; exact ⟨zero_mem _, zero_mem _⟩
  | add x y _ _ hx hy =>
    intro α
    rw [add_smul, add_smul]
    exact ⟨add_mem (hx α).1 (hy α).1, add_mem (hx α).2 (hy α).2⟩
  | smul c x _ ih =>
    intro α
    have e1 : (c • x) • h.mDR α = x • h.mDR (c • α) := by
      rw [h.mDR_smul, Algebra.smul_def c x, mul_comm, mul_smul]
    have e2 : (c • x) • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) = x • (ι1 (D R Q.P (Q.e 1)) * h.mDR (c • α)) := by
      rw [h.mDR_smul, mul_smul_comm, Algebra.smul_def c x, mul_comm, mul_smul]
    rw [e1, e2]
    exact ih (c • α)

theorem smul_mem_closure (b : Q.P) {x : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h)) :
    b • x ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).1
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).2
    · refine AddSubgroup.subset_closure (pdGen_mem_rel η h ?_)
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem D_mem_closure {δ : DividedPowers J} (hs : Q.IsStd δ η) (b : Q.P) :
    ι1 (D R Q.P b) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    cases n with
    | zero => rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]; exact zero_mem _
    | succ n =>
      have hr : ι1 (D R Q.P (η.dpow (n + 1) (Q.e 1)) - η.dpow n (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
        Ideal.subset_span ⟨n, Q.e 1, Q.e_one_mem_ext J, rfl⟩
      rw [hs.var, hs.var] at hr
      have e : ι1 (D R Q.P (Q.e (n + 1))) = ι1 (D R Q.P (Q.e (n + 1)) - Q.e n • D R Q.P (Q.e 1)) +
          Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR 1) := by
        rw [map_one h.mDR, mul_one, map_sub, map_smul, sub_add_cancel]
      rw [e]
      exact add_mem (AddSubgroup.subset_closure (pdGen_mem_rel η h hr))
        (AddSubgroup.subset_closure (pdGen_mem_two η h n 1))
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  | smul c x _ ih =>
    rw [Algebra.smul_def, Derivation.leibniz, map_add (f := _), map_smul, map_smul]
    refine add_mem (smul_mem_closure η h _ ih) ?_
    have e : ι1 (D R Q.P (algebraMap B Q.P c)) = h.mDR (ι1 (D R B c)) := by rw [h.mDR_ι, h.m1_D]
    rw [e]; exact (smul_gen_mem η h x _).1


omit [IsScalarTower R B Q.P] in
theorem mDR_mul_dtau (α β : DR R B) :
    h.mDR α * (ι1 (D R Q.P (Q.e 1)) * h.mDR β) = ι1 (D R Q.P (Q.e 1)) * h.mDR (sgn α * β) := by
  rw [← mul_assoc, map_mul, h.mDR_sgn, ← mul_assoc, ι_mul (D R Q.P (Q.e 1)) (sgn (h.mDR α)), sgn_sgn]

theorem gen_mul_gen {x y : DR R Q.P} (hx : x ∈ pdGen η h) (hy : y ∈ pdGen η h) :
    x * y ∈ AddSubgroup.closure (pdGen η h) := by
  have base : ∀ α : DR R B, h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).1; rwa [one_smul] at this
  have base2 : ∀ α : DR R B, ι1 (D R Q.P (Q.e 1)) * h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).2; rwa [one_smul] at this
  have relL : ∀ {z : DR R Q.P} (w : DR R Q.P), z ∈ rel R η → w * z ∈ AddSubgroup.closure (pdGen η h) :=
    fun w hz ↦ AddSubgroup.subset_closure (pdGen_mem_rel η h (Ideal.mul_mem_left _ w hz))
  rcases hx with (⟨m, α, rfl⟩ | ⟨m, α, rfl⟩) | hx
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base _))
    · rw [smul_mul_assoc, mul_smul_comm, mDR_mul_dtau]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · exact relL _ hy
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, mDR_mul_dtau, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
        zero_mul, smul_zero, smul_zero]
      exact zero_mem _
    · exact relL _ hy
  · exact AddSubgroup.subset_closure (pdGen_mem_rel η h (rel_mul_mem_right η hx _))

theorem mul_mem_closure {x y : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h))
    (hy : y ∈ AddSubgroup.closure (pdGen η h)) : x * y ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => exact gen_mul_gen η h hx hy
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

end Poly

theorem pdPoly_forms_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
    (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η →
    (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) →
    (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop),
    (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) →
    (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  intro R B _ _ _ J δ Q _ _ η _ h hs _ _ _ p hrel hadd h1 h2 x
  have hS : ∀ x, x ∈ AddSubgroup.closure (pdGen η h) := fun x ↦ by
    induction x using indDR with
    | h b =>
      have := (smul_gen_mem η h b 1).1
      rwa [map_one, ← Algebra.algebraMap_eq_smul_one] at this
    | hd b => exact D_mem_closure η h hs b
    | hm x y hx hy => exact mul_mem_closure η h hx hy
    | ha x y hx hy => exact add_mem hx hy
  have key : ∀ x ∈ AddSubgroup.closure (pdGen η h), p x ∧ p (-x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
      · exact ⟨h1 n α, by rw [← smul_neg, ← map_neg]; exact h1 n (-α)⟩
      · exact ⟨h2 n α, by rw [← smul_neg, ← mul_neg, ← map_neg]; exact h2 n (-α)⟩
      · exact ⟨hrel x hx, hrel _ (neg_mem hx)⟩
    | zero => exact ⟨hrel 0 (zero_mem _), by rw [neg_zero]; exact hrel 0 (zero_mem _)⟩
    | add x y _ _ hx hy => exact ⟨hadd _ _ hx.1 hy.1, by rw [neg_add]; exact hadd _ _ hx.2 hy.2⟩
    | neg x _ hx => exact ⟨hx.2, by rw [neg_neg]; exact hx.1⟩
  exact (key x (hS x)).1

end GlobalTheory.PDForm
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CxCoh.CxMap

universe u u'

variable {C : Type u} [Category.{0} C] {C' : Type u'} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

def pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : CxMap K K' where
  G := G
  a0 T := (m.a0 T).comp (K.M0.map (θ.app T))
  a1 T := (m.a1 T).comp (K.M1.map (θ.app T))
  a2 T := (m.a2 T).comp (K.M2.map (θ.app T))
  a3 T := (m.a3 T).comp (K.M3.map (θ.app T))
  compDegreeZero_natural {T T'} φ x := by
    change m.a0 T' (K.M0.map (θ.app T') (K.M0.map (G.map φ) x)) =
      K'.M0.map φ (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.M0.map_comp, θ.naturality, K.M0.map_comp, m.compDegreeZero_natural]
  compDegreeOne_natural {T T'} φ x := by
    change m.a1 T' (K.M1.map (θ.app T') (K.M1.map (G.map φ) x)) =
      K'.M1.map φ (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.M1.map_comp, θ.naturality, K.M1.map_comp, m.compDegreeOne_natural]
  compDegreeTwo_natural {T T'} φ x := by
    change m.a2 T' (K.M2.map (θ.app T') (K.M2.map (G.map φ) x)) =
      K'.M2.map φ (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.M2.map_comp, θ.naturality, K.M2.map_comp, m.compDegreeTwo_natural]
  comp_commutes_diffZero T x := by
    change m.a1 T (K.M1.map (θ.app T) (K.d0 _ x)) = K'.d0 T (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.diffZero_natural, m.comp_commutes_diffZero]
  comp_commutes_diffOne T x := by
    change m.a2 T (K.M2.map (θ.app T) (K.d1 _ x)) = K'.d1 T (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.diffOne_natural, m.comp_commutes_diffOne]
  comp_commutes_diffTwo T x := by
    change m.a3 T (K.M3.map (θ.app T) (K.d2 _ x)) = K'.d2 T (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.diffTwo_natural, m.comp_commutes_diffTwo]

theorem joined_pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : (m.pre θ).Joined m θ :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end GlobalTheory.CxCoh.CxMap

namespace GlobalTheory.PDForm

def pairB {D D' : Data} (Λ' : Lift D') {σ : D.R →+* D'.R} (φ : D'.X ⟶ D.X) {φ₀ : D'.X₀ ⟶ D.X₀}
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) : CxMap (KK D.κ D.t) ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)) :=
  (morMap m).comp ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L))

end GlobalTheory.PDForm
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.bertini_simple_zeros_generic_sections : Quoted → Bertini := by
  first | exact @GlobalTheory.BertiniTop.bertini | exact GlobalTheory.BertiniTop.bertini | (intros; apply GlobalTheory.BertiniTop.bertini <;> assumption)
end
