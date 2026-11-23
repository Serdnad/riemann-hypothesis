module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section PSHelp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}}

theorem ps_gm_linCombIso {L M : LB X} (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    gm r z _ ((LB.linCombIso w φ ε).s p) = ∏ a, gm (r ≫ φ a) z ((LB.div M L).U (p.1 a, p.2 a)) (w.s (p.1 a, p.2 a)) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ M.U (p.1 a) ⊓ L.U (p.2 a) :=
    ⟨LB.wchart_le M φ p.1 a hz.1, LB.wchart_le L φ p.2 a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z ((LB.div M L).U (p.1 a, p.2 a)) hm _)

theorem ps_gs_secOfIso {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB)
    (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  refine (gs_res r z inf_le_left hz _).symm.trans ?_
  refine (congrArg (gs r z (A.U a ⊓ B.U b)) (secOfIso_spec t hu hA hB a b)).trans ?_
  unfold isoCand
  refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z inf_le_right hz _))
  rw [gs_unit r z _ hz, map_inv, gm_res r z (divLe a b) hz]

end PSHelp

section ScalB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

end ScalB

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

lemma hasVal_mul {c d : FractionRing V} {n m : ℤ} (hc : HasVal ϖ c n) (hd : HasVal ϖ d m) (hϖ : Irreducible ϖ) :
    HasVal ϖ (c * d) (n + m) := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨w, hw⟩ := hd
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  refine ⟨u * w, ?_⟩
  rw [hu, hw, zpow_add₀ hπ, Units.val_mul, map_mul]
  ring


open scoped Classical in
def valE (hϖ : Irreducible ϖ) (c : FractionRing V) : ℤ :=
  if h : c = 0 then 0 else (hasVal_of_ne_zero hϖ h).choose

lemma hasVal_valE (hϖ : Irreducible ϖ) {c : FractionRing V} (hc : c ≠ 0) : HasVal ϖ c (valE hϖ c) := by
  unfold valE
  rw [dite_eq_right hc]
  exact (hasVal_of_ne_zero hϖ hc).choose_spec


open scoped Classical in
def vK (hϖ : Irreducible ϖ) : AddValuation (FractionRing V) (WithTop ℚ) :=
  AddValuation.of (fun c => if c = 0 then ⊤ else ((valE hϖ c : ℚ) : WithTop ℚ))
    (by simp)
    (by
      have h1 : HasVal ϖ (1 : FractionRing V) 0 := ⟨1, by simp⟩
      simp [hasVal_unique hϖ (hasVal_valE hϖ one_ne_zero) h1])
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
      have key : ∀ {a b : FractionRing V}, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → valE hϖ a ≤ valE hϖ b →
          valE hϖ a ≤ valE hϖ (a + b) := by
        intro a b ha hb hab hle
        have hva := hasVal_valE hϖ ha
        have hvb := hasVal_valE hϖ hb
        have hvab := hasVal_valE hϖ hab
        generalize valE hϖ a = na at hva hle ⊢
        generalize valE hϖ b = nb at hvb hle
        generalize valE hϖ (a + b) = nab at hvab ⊢
        obtain ⟨u, hu⟩ := hva
        obtain ⟨w, hw⟩ := hvb
        obtain ⟨d, hd⟩ : ∃ d : ℕ, nb = na + d := ⟨(nb - na).toNat, by omega⟩
        set r : V := (u : V) + ϖ ^ d * (w : V)
        have hab' : a + b = algebraMap V (FractionRing V) ϖ ^ na * algebraMap V (FractionRing V) r := by
          rw [hu, hw, hd, zpow_add₀ hπ, zpow_natCast]
          simp only [r, map_add (f := _), map_mul, map_pow]
          ring
        have hr : r ≠ 0 := by
          rintro h0
          apply hab
          rw [hab', h0, map_zero, mul_zero]
        obtain ⟨k, z, hz⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
        have hv : HasVal ϖ (a + b) (na + k) :=
          ⟨z, by rw [hab', hz, zpow_add₀ hπ, zpow_natCast, map_mul, map_pow]; ring⟩
        rw [hasVal_unique hϖ hvab hv]
        omega
      rcases le_total (valE hϖ x) (valE hϖ y) with h | h
      · have := key hx hy hxy h
        exact min_le_of_left_le (by exact_mod_cast this)
      · have := key hy hx (by rwa [add_comm]) h
        rw [add_comm] at this
        exact min_le_of_right_le (by exact_mod_cast this))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      simp only [hx, hy, hxy, if_false]
      rw [hasVal_unique hϖ (hasVal_valE hϖ hxy) (hasVal_mul (hasVal_valE hϖ hx) (hasVal_valE hϖ hy) hϖ)]
      push_cast
      rfl)

lemma valOver_vK (hϖ : Irreducible ϖ) : ValOver ϖ (FractionRing V) (vK hϖ) := by
  intro c n hc
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  have hc0 : c ≠ 0 := by
    obtain ⟨u, hu⟩ := hc
    rw [hu]
    refine mul_ne_zero (zpow_ne_zero _ hπ) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr u.ne_zero
  change vK hϖ c = _
  simp only [vK, AddValuation.of_apply, if_neg hc0]
  rw [hasVal_unique hϖ (hasVal_valE hϖ hc0) hc]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def NuExtSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V)))
      [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
      (U : Unif (maximalIdeal V) D A G) (k : ℕ), 1 ≤ k →
      ∀ (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E →
        NuGe D Q (FractionRing V) vK k E 0 →
        ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))),
          GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s
            (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) 1

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWO

open ReciprocityTheory.ChartRestriction.G.Out

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem exists_weight_basis_filtration {a b : WithTop ℚ} (h : a + b = 0) (ha : a ≤ 0) : 0 ≤ b := by
  rcases eq_or_ne b ⊤ with rfl | hbt
  · exact le_top
  rcases eq_or_ne a ⊤ with rfl | hat
  · simp at h
  lift a to ℚ using hat
  lift b to ℚ using hbt
  norm_cast at h ha ⊢
  linarith

theorem le_zero_of_add_eq_zero_nonneg {a b : WithTop ℚ} (h : a + b = 0) (hb : 0 ≤ b) : a ≤ 0 := by
  rcases eq_or_ne b ⊤ with rfl | hbt
  · simp at h
  rcases eq_or_ne a ⊤ with rfl | hat
  · simp at h
  lift a to ℚ using hat
  lift b to ℚ using hbt
  norm_cast at h hb ⊢
  linarith

def Ov : ValuationSubring F where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    show 0 ≤ v (a * b)
    rw [AddValuation.map_mul]; exact add_nonneg ha hb
  one_mem' := by show 0 ≤ v 1; rw [AddValuation.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (AddValuation.map_add v a b)
  zero_mem' := by show 0 ≤ v 0; rw [AddValuation.map_zero]; exact le_top
  neg_mem' {a} ha := by show 0 ≤ v (-a); rw [AddValuation.map_neg]; exact ha
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left; show 0 ≤ v x; rw [hx, AddValuation.map_zero]; exact le_top
    rcases le_total 0 (v x) with h | h
    · exact Or.inl h
    · right
      show 0 ≤ v x⁻¹
      refine exists_weight_basis_filtration ?_ h
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]

theorem mem_Ov {x : F} : x ∈ Ov v ↔ 0 ≤ v x := Iff.rfl

theorem v_nonneg (r : Ov v) : (0 : WithTop ℚ) ≤ v (r : F) := (mem_Ov v).1 r.2

theorem v_unit (r : (Ov v)ˣ) : v ((r : Ov v) : F) = 0 := by
  have h1 := v_nonneg v (r : Ov v)
  have h2 := v_nonneg v ((r⁻¹ : (Ov v)ˣ) : Ov v)
  have hm : ((r : Ov v) : F) * (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 1 := congrArg Subtype.val r.mul_inv
  have hs : v ((r : Ov v) : F) + v (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 0 := by
    rw [← AddValuation.map_mul, hm, AddValuation.map_one]
  exact le_antisymm (le_zero_of_add_eq_zero_nonneg hs h2) h1

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  [Algebra (FractionRing V) F]

abbrev algVF : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))

theorem v_of_V (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (x : V) : (0 : WithTop ℚ) ≤ v (algVF x) ∧
    (¬ IsUnit x → x ≠ 0 → (1 : WithTop ℚ) ≤ v (algVF x)) := by
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, fun _ h => absurd rfl h⟩
    rw [map_zero, AddValuation.map_zero]
    exact le_top
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hH : HasVal ϖ (algebraMap V (FractionRing V) x) (n : ℤ) :=
    ⟨u, by rw [hu, map_mul, map_pow, zpow_natCast, mul_comm]⟩
  have hval : v (algVF x) = (((n : ℤ) : ℚ) : WithTop ℚ) := hv _ _ hH
  rw [hval]
  refine ⟨?_, fun hnu _ => ?_⟩
  · have h0 : (0 : ℚ) ≤ ((n : ℤ) : ℚ) := by positivity
    exact_mod_cast h0
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact (hnu (by rw [hu, h0, pow_zero, mul_one]; exact u.isUnit)).elim
    · have h1 : (1 : ℚ) ≤ ((n : ℤ) : ℚ) := by exact_mod_cast hpos
      exact_mod_cast h1

def fO (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) : V →+* Ov v :=
  (algVF (F := F) (V := V)).codRestrict (Ov v).toSubring fun x => (v_of_V v hϖ hv x).1

theorem fO_comp (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) :
    (algebraMap (Ov v) F).comp (fO v hϖ hv) = algVF := rfl

instance isLocalHom_fO (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) : IsLocalHom (fO v hϖ hv) where
  map_nonunit x hx := by
    by_contra hxu
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have h1 := (v_of_V v hϖ hv x).2 hxu hx0
    have h0 := v_unit v hx.unit
    rw [IsUnit.unit_spec] at h0
    have : v (algVF x) = 0 := h0
    rw [this] at h1
    exact absurd h1 (by decide)

theorem exists_lift (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    [IsProper p] (x : Spec (CommRingCat.of F) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom algVF)) :
    ∃ x' : Spec (CommRingCat.of (Ov v)) ⟶ X, x' ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x' = x := by
  have hE : ValuativeCriterion.Existence p := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let S : ValuativeCommSq p :=
    { R := Ov v, K := F, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)),
      commSq := ⟨by rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp]⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

theorem lift_unique (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    [IsSeparated p] (x₁ x₂ : Spec (CommRingCat.of (Ov v)) ⟶ X)
    (h₁ : x₁ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv))) (h₂ : x₂ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)))
    (h : Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁ = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₂) :
    x₁ = x₂ := by
  let S : ValuativeCommSq p :=
    { R := Ov v, K := F, i₁ := Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁,
      i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)),
      commSq := ⟨by rw [Category.assoc, h₁]⟩ }
  have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion p S
  have hl : (⟨x₁, rfl, h₁⟩ : S.commSq.LiftStruct) = ⟨x₂, h.symm, h₂⟩ := @Subsingleton.elim _ hU _ _
  exact congrArg CommSq.LiftStruct.l hl

end ReciprocityTheory.ChartRestriction.G.DVR.TWO
end
end
