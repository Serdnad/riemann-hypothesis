module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Lemmata.MiscLemmasN.Imports
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Cube

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def cQ (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

theorem cQ_add (T : Over (Spec (CommRingCat.of R))) (a b : D.X) : cQ D T (a + b) = cQ D T a * cQ D T b := by
  unfold cQ
  rw [D.c_add, padd, ← Hom.mul_def, MonObj.comp_mul]

theorem cQ_nsmul (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (a : D.X) : cQ D T (k • a) = cQ D T a ^ k := by
  induction k with
  | zero =>
    rw [zero_smul, pow_zero]
    have h0 : cQ D T 0 * cQ D T 0 = cQ D T 0 := by rw [← cQ_add, add_zero]
    simpa using h0
  | succ k ih => rw [succ_nsmul, cQ_add, ih, pow_succ]

theorem comp_cQ {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) : ρ ≫ cQ D T a = cQ D T' a := by
  unfold cQ
  rw [← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]

theorem prod_famB {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (χ : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB χ i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cQ D T χ).left * (h (cQ D T χ).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e1 : ρ.left ≫ (𝟙 D.P.A.left) = ρ.left := Category.comp_id _
  have e2 : ρ.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = (ρ * cQ D T χ).left := by
    rw [← Over.comp_left]
    congr 1
    rw [padd, Hom.mul_def, comp_lift_assoc, Category.comp_id, cQ, ← Category.assoc, comp_toUnit]
  have e3 : ρ.left ≫ (toUnit D.P.A ≫ D.c χ).left = (cQ D T χ).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    rfl
  have e4 : ρ.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit, Hom.one_def]
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_one, zpow_neg, e1, e2, e3, e4]

theorem prod_neg' {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) {c : U} (h : ∏ i, f i ^ e i = c) :
    ∏ i, f i ^ (-e i) = c⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib, h]

theorem exists_eB (k : ℕ) (α mu : D.X) {Ix : Type} [Fintype Ix]
    {φV : Ix → (Spec (CommRingCat.of R) ⟶ D.P.A.left)} {εV : Ix → ℤ}
    (w : LB.Gen (LB.LinComb D.P.L φV εV)) (hw : w.IsGen)
    (hC : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), ∏ i, h (D.P.A.hom ≫ φV i) ^ εV i =
      (h (cQ D D.P.A α * cQ D D.P.A mu).left)⁻¹ * h (cQ D D.P.A α).left * h (cQ D D.P.A mu).left *
        (h (1 : D.P.A ⟶ D.P.A).left)⁻¹ * (h (cQ D D.P.A mu).left ^ k)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ k) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu))
        (fun i => (𝟙 D.P.A * cQ D D.P.A mu).left ≫ D.famφB α i)) (DegPre.deltaε k)), eB.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val eB ρ.left z J = cubN (cubV D.cub z J) k (cQ D T α) (cQ D T mu) ρ *
          (cubV D.cub z J (cQ D T α) ρ (cQ D T mu))⁻¹ * val w (ρ.left ≫ D.P.A.hom) z J := by
  set a : D.P.A ⟶ D.P.A := cQ D _ α with ha
  set m : D.P.A ⟶ D.P.A := cQ D _ mu with hm
  have hα' : cQ D D.P.A (α + k • mu) = a * m ^ k := by rw [cQ_add, cQ_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m (𝟙 D.P.A) k
  obtain ⟨e, he, ve⟩ := exists_gen D.P.isLB (φ' := Sum.elim (D.famφB (α + k • mu))
      (fun i => (𝟙 D.P.A * m).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a (𝟙 D.P.A) m h
      have p₂ := hC U h
      have p₃ := prod_famB D (𝟙 _) (α + k • mu) k h
      have p₄ := prod_famB D (𝟙 D.P.A * m) α k h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (α + k • mu) i = D.famφB (α + k • mu) i := fun i => by simp
      simp only [e₃] at p₃
      rw [hα'] at p₃
      rw [← ha] at p₄
      have q₁ : 𝟙 D.P.A * (a * m ^ k) = a * m ^ k * 𝟙 D.P.A := mul_comm _ _
      have q₂ : 𝟙 D.P.A * m * a = a * 𝟙 D.P.A * m := by rw [mul_comm _ a, ← _root_.mul_assoc]
      have q₃ : m * 𝟙 D.P.A = 𝟙 D.P.A * m := mul_comm _ _
      rw [q₁] at p₃
      rw [q₂] at p₄
      have S : ∀ {K K' : Type} {_ : Fintype K} {_ : Fintype K'} (f : K ⊕ K' → U),
          ∏ i, f i = (∏ i, f (.inl i)) * ∏ i, f (.inr i) := fun f => Fintype.prod_sum_type f
      rw [S, S]
      erw [S]
      simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε]
      erw [prod_neg' _ _ p₁]
      rw [p₂, p₃, prod_neg' _ _ p₄]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, q₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift (𝟙 D.P.A) m)).left)))
      (LB.pullGen D.P.L _ _ w D.P.A.hom))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hw _))
  refine ⟨e, he, fun T ρ z J hJ => ?_⟩
  have E := (ve _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _))))) (val_pull hJ _ _ _)))
  refine E.trans ?_
  rw [ha, hm, comp_cQ, comp_cQ, Category.comp_id]

end Cube

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] {X : Scheme.{0}}

def strMap (p : X ⟶ Sp V) (U : X.Opens) : V →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom

theorem constFn_eq_strMap (p : X ⟶ Sp V) (U : X.Opens) (a : V) : constFn p U a = strMap p U a := rfl

theorem fromSpec_appLE_top {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem appLE_top_eq {Y W : Scheme.{0}} (f : Y ⟶ W) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

theorem mem_map_of_app_fst_eq_zero (p : X ⟶ Sp V) (J : Ideal V) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U))
    (ha : ((pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom a = 0) :
    a ∈ J.map (strMap p U) := by
  let I₀ : Ideal Γ(X, U) := J.map (strMap p U)
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I₀ := Ideal.Quotient.mk I₀
  let ψ : V ⧸ J →+* Γ(X, U) ⧸ I₀ := Ideal.quotientMap I₀ (strMap p U) Ideal.le_comap_map
  let z : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  have hz : ⊤ ≤ z ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : z.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : z.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp, fromSpec_appLE_top]
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (z.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  have m1 : (z ≫ p).appTop = p.appLE ⊤ U le_top ≫ z.appLE U ⊤ hz :=
    ((Scheme.Hom.appLE_comp_appLE z p ⊤ U ⊤ le_top hz).trans (appLE_top_eq _ _)).symm
  have m5 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))).symm
  have m6 : (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv ≫ (Spec.map (CommRingCat.ofHom ψ)).appTop =
      CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)).symm
  have e5 : ∀ c : V, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J c) :=
    fun c => congrArg (fun φ => φ.hom c) m5
  have e6 : ∀ c : V ⧸ J, (Spec.map (CommRingCat.ofHom ψ)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (ψ c) :=
    fun c => congrArg (fun φ => φ.hom c) m6
  have hsq : z ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    apply ext_of_isAffine
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1
    ext b
    show (z ≫ p).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b) =
      (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)
    rw [m1, Scheme.Hom.comp_appTop]
    show (z.appLE U ⊤ hz).hom ((p.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)) =
      (Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b))
    rw [k1, e5, e6, Ideal.quotientMap_mk]
    rfl
  let l := pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) hsq
  have hl : l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = z := pullback.lift_fst _ _ _
  have tr : ∀ (w : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X) (hw : w = z) (e : ⊤ ≤ w ⁻¹ᵁ U),
      (w.appLE U ⊤ e).hom a = (z.appLE U ⊤ hz).hom a := by
    intro w hw e
    subst hw
    rfl
  have k2 : ((l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).appLE U ⊤
      (hl ▸ hz)).hom a = 0 := by
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]
  rw [tr _ hl, k1] at k2
  have h1 : q a = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).hom.hom k2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem loc_div {P : Scheme.{0}} (p' : P ⟶ Sp V) (W : P.Opens) (f : Γ(P, W)) (r : V) (x : P) (hx : x ∈ W)
    (h : cst p' x r ∣ gs (𝟙 P) x W f) : ∃ (U : P.Opens) (_ : U ≤ W) (_ : x ∈ U) (g : Γ(P, U)),
      ∀ y ∈ U, gs (𝟙 P) y W f = cst p' y r * gs (𝟙 P) y U g := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨U, hU, g, rfl⟩ := P.presheaf.exists_germ_eq t
  have hm : x ∈ W ⊓ U := ⟨hx, hU⟩
  have e : gs (𝟙 P) x (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) x (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := by
    rw [gs_res _ x _ hm, gs_mul _ x _ hm, gs_res _ x _ hm, gs_constFn p' _ _ x hm, Category.id_comp, ht,
      gs_eq _ x U hU]
    rfl
  rw [gs_eq _ x _ hm, gs_eq _ x _ hm] at e
  obtain ⟨U', hU', i₁, i₂, e'⟩ := P.presheaf.germ_eq x hm hm _ _ e
  have le : U' ≤ W ⊓ U := i₁.le
  refine ⟨U', le.trans inf_le_left, hU', (P.presheaf.map (homOfLE (le.trans inf_le_right)).op).hom g, fun y hy => ?_⟩
  have e'' := congrArg (gs (𝟙 P) y U') e'
  have k := (gs_res (𝟙 P) y le hy _).symm.trans (e''.trans (gs_res (𝟙 P) y le hy _))
  have hy' : (𝟙 P : P ⟶ P) y ∈ W ⊓ U := le hy
  have k' : gs (𝟙 P) y (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) y (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := k
  rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_constFn p' _ _ y hy', Category.id_comp] at k'
  rw [k', gs_res _ y _ hy]

theorem dvd_germ_of_thick (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) {W : X.Opens}
    (a : Γ(X, W)) (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hx : pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ W)
    (h : cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
      gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' W a) :
    cst p (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') r ∣
      gs (𝟙 X) (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') W a := by
  let P := pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  let f : P ⟶ X := pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of V) J
  have : IsClosedImmersion f := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have h' : cst (f ≫ p) x' r ∣ gs (𝟙 P) x' (f ⁻¹ᵁ W) ((f.app W).hom a) := by
    rw [gs_pull (𝟙 P) f x' W hx, Category.id_comp]; exact h
  obtain ⟨U', hU'W, hxU', t', ht'⟩ := loc_div (f ≫ p) (f ⁻¹ᵁ W) ((f.app W).hom a) r x' hx h'
  obtain ⟨O, hO, hOeq⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.1 U'.isOpen
  have hxO : f x' ∈ O := by
    have : x' ∈ f.base ⁻¹' O := by rw [hOeq]; exact hxU'
    exact this
  obtain ⟨U, hU, hxU, hUsub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
    (show f x' ∈ (⟨O, hO⟩ ⊓ W : X.Opens) from ⟨hxO, hx⟩)
  have hUW : U ≤ W := hUsub.trans inf_le_right
  have hfU : f ⁻¹ᵁ U ≤ U' := fun y hy => by
    have hyO : f y ∈ O := (hUsub hy).1
    have : y ∈ f.base ⁻¹' O := hyO
    rw [hOeq] at this
    exact this
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective f U hU ((P.presheaf.map (homOfLE hfU).op).hom t')
  have hd : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a) = (f.app U).hom (constFn p U r * b) := by
    apply fn_ext
    intro y hy
    have hyW : f y ∈ W := hUW hy
    have L1 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy ((X.presheaf.map (homOfLE hUW).op).hom a)
      rw [Category.id_comp, gs_res f y hUW hy] at e1
      have e2 := gs_pull (𝟙 P) f y W hyW a
      rw [Category.id_comp] at e2
      rw [e1, ← e2]
      exact ht' y (hfU hy)
    have L2 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom (constFn p U r * b)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy (constFn p U r * b)
      rw [Category.id_comp, gs_mul f y U hy, gs_constFn p U f y hy] at e1
      have e3 := gs_pull (𝟙 P) f y U hy b
      rw [Category.id_comp, hb, gs_res (𝟙 P) y hfU hy] at e3
      rw [e1, e3]
    exact L1.trans L2.symm
  have hd0 : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a - constFn p U r * b) = 0 := by
    rw [map_sub, hd, sub_self]
  have hmem := mem_map_of_app_fst_eq_zero p J hU _ hd0
  have hle : J.map (strMap p U) ≤ Ideal.span {strMap p U r} := by
    refine (Ideal.map_mono hJ).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hle hmem)
  have ha : (X.presheaf.map (homOfLE hUW).op).hom a = constFn p U r * (b + c) := by
    rw [mul_add, ← constFn_eq_strMap] at *
    linear_combination -hc
  refine ⟨gs (𝟙 X) (f x') U (b + c), ?_⟩
  rw [← gs_res (𝟙 X) (f x') hUW hxU, ha, gs_mul (𝟙 X) (f x') U hxU, gs_constFn p U (𝟙 X) (f x') hxU, Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem away_fractionRing {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.SecondBlockLemmaO.goal1 .. | (apply Bl.SecondBlockLemmaO.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaO.goal1 <;> assumption)

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem eq_zero_of_app_fst_open {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X T : AlgebraicGeometry.Scheme.{0}} (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.Flat p]
    (t : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.IsOpenImmersion t] [Nonempty T]
    (W : X.Opens) (d : Γ(X, W)) (h : ((CategoryTheory.Limits.pullback.fst p t).app W).hom d = 0) : d = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ' : Γ(Sp V, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ
  have hrange : ∀ t' : Sp V, t' ∈ (Sp V).basicOpen ϖ' → t' ∈ Set.range t.base := by
    intro t' ht
    have ht' : t' ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V)) := by
      have := basicOpen_eq_of_affine (R := CommRingCat.of V) ϖ
      rw [← this]; exact ht
    have hbot : PrimeSpectrum.asIdeal (R := V) t' = ⊥ := by
      by_contra hne
      have hmax := Ideal.IsPrime.isMaximal (PrimeSpectrum.isPrime (R := V) t') hne
      have hm := IsLocalRing.eq_maximalIdeal hmax
      apply (PrimeSpectrum.mem_basicOpen _ _).1 ht'
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    obtain ⟨y⟩ := ‹Nonempty T›
    have hle : PrimeSpectrum.asIdeal (R := V) t' ≤ PrimeSpectrum.asIdeal (R := V) (t.base y) := by
      rw [hbot]; exact bot_le
    have hsp : t' ⤳ t.base y := (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 hle)
    exact hsp.mem_open t.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  let O : X.Opens := p ⁻¹ᵁ (Sp V).basicOpen ϖ'
  let q := IsOpenImmersion.lift t (O.ι ≫ p) (by
    rintro _ ⟨a, rfl⟩
    exact hrange _ a.2)
  let s : O.toScheme ⟶ pullback p t :=
    pullback.lift O.ι q (IsOpenImmersion.lift_fac _ _ _).symm
  have hs : s ≫ pullback.fst p t = O.ι := pullback.lift_fst _ _ _
  have hO : ∀ x ∈ W, x ∈ O → gs (𝟙 X) x W d = 0 := by
    intro x hxW hxO
    have hm : (s ≫ pullback.fst p t) ⟨x, hxO⟩ ∈ W := by rw [hs]; exact hxW
    have e1 : gs O.ι ⟨x, hxO⟩ W d = 0 := by
      rw [← hs, ← gs_pull s (pullback.fst p t) ⟨x, hxO⟩ W hm, h]
      exact gs_zero' _ _ _
    rw [gs_stalkMap O.ι ⟨x, hxO⟩ W hxW] at e1
    have : IsIso (O.ι.stalkMap ⟨x, hxO⟩) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    exact (ConcreteCategory.bijective_of_isIso (O.ι.stalkMap ⟨x, hxO⟩)).1 (e1.trans (map_zero _).symm)
  refine fn_ext fun x hx => ?_
  rw [gs_zero']
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hU' : IsAffineOpen (U : X.Opens) := hU
  let g : Γ(X, U) := constFn p U ϖ
  let dU : Γ(X, U) := (X.presheaf.map (homOfLE hUW).op).hom d
  have hgs : ∀ x' ∈ U, gs (𝟙 X) x' U g = cst p x' ϖ := fun x' hx' =>
    (gs_constFn p U (𝟙 X) x' hx' ϖ).trans (by rw [Category.id_comp])
  refine (exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU'.isCompact dU g ?_).elim
    fun n hn => ?_
  · refine fn_ext fun x' hx' => ?_
    have hx'U : x' ∈ U := X.basicOpen_le g hx'
    have hunit : IsUnit (X.presheaf.germ U x' hx'U g) := (X.mem_basicOpen g x' hx'U).1 hx'
    have h2 : IsUnit (cst p x' ϖ) := by
      rw [← hgs x' hx'U, gs_eq (𝟙 X) x' U hx'U]; exact hunit
    have h3 : IsUnit (gs (𝟙 (Sp V)) (p x') ⊤ ϖ') := by
      rw [cst, gs_stalkMap p x' ⊤ trivial] at h2
      exact (isUnit_map_iff (p.stalkMap x').hom _).1 h2
    have hxO : x' ∈ O := by
      show p x' ∈ (Sp V).basicOpen ϖ'
      rw [gs_eq (𝟙 (Sp V)) (p x') ⊤ trivial] at h3
      exact ((Sp V).mem_basicOpen ϖ' (p x') trivial).2 h3
    change gs (𝟙 X) x' _ ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom dU) = gs (𝟙 X) x' _ 0
    rw [gs_zero', gs_res (𝟙 X) x' (X.basicOpen_le g) hx']
    exact (gs_res (𝟙 X) x' hUW hx'U d).trans (hO x' (hUW hx'U) hxO)
  · have e := congrArg (gs (𝟙 X) x U) hn
    have hdU : gs (𝟙 X) x U dU = gs (𝟙 X) x W d := gs_res (𝟙 X) x hUW hxU d
    rw [gs_zero', gs_mul (𝟙 X) x U hxU, hdU] at e
    have hpow : gs (𝟙 X) x U (g ^ n) = cst p x ϖ ^ n := by
      rw [gs_eq (𝟙 X) x U hxU, map_pow, map_pow, ← gs_eq (𝟙 X) x U hxU, hgs x hxU]
    rw [hpow] at e
    exact ((cst_regular p x hϖ.ne_zero).pow n) (e.trans (mul_zero _).symm)

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
