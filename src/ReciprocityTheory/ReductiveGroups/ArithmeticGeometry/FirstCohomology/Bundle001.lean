module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.SectionDivision

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

theorem exists_section {k : Type} [Field k] [IsAlgClosed k] {P' : Scheme.{0}}
    (p : P' ⟶ Spec (CommRingCat.of k)) [IsFinite p] [Surjective p] :
    ∃ t : Spec (CommRingCat.of k) ⟶ P', t ≫ p = 𝟙 _ := by
  have : IsAffine P' := isAffine_of_isAffineHom p
  obtain ⟨w, -⟩ := Surjective.surj (f := p) (IsLocalRing.closedPoint k)
  have : Nonempty (⊤ : P'.Opens) := ⟨⟨w, trivial⟩⟩
  let θ := Scheme.ΓSpecIso (CommRingCat.of k)
  let ψ : k →+* Γ(P', ⊤) := (p.appTop).hom.comp θ.inv.hom
  let _ : Algebra k Γ(P', ⊤) := ψ.toAlgebra
  have hfin : ψ.Finite := (IsFinite.finite_app p ⊤ (isAffineOpen_top _)).comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso θ.inv).2)
  have : Module.Finite k Γ(P', ⊤) := hfin
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(P', ⊤)
  let _ : Field (Γ(P', ⊤) ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite k (Γ(P', ⊤) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k M).toLinearMap (Ideal.Quotient.mkₐ_surjective k M)
  have : Algebra.IsIntegral k (Γ(P', ⊤) ⧸ M) := Algebra.IsIntegral.of_finite k _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(P', ⊤) ⧸ M)
  let e : k ≃+* Γ(P', ⊤) ⧸ M := RingEquiv.ofBijective (algebraMap k (Γ(P', ⊤) ⧸ M)) hb
  let φ' : Γ(P', ⊤) →+* k := e.symm.toRingHom.comp (Ideal.Quotient.mk M)
  have hφ : ∀ c, φ' (ψ c) = c := fun c => by
    show e.symm (Ideal.Quotient.mk M (algebraMap k Γ(P', ⊤) c)) = c
    rw [← Ideal.Quotient.algebraMap_eq, ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq]
    exact e.symm_apply_apply c
  let φ : Γ(P', ⊤) ⟶ Γ(Spec (CommRingCat.of k), ⊤) := CommRingCat.ofHom φ' ≫ θ.inv
  have hret : p.appTop ≫ φ = 𝟙 _ := by
    ext c
    obtain ⟨d, rfl⟩ : ∃ d, θ.inv.hom d = c := (ConcreteCategory.bijective_of_isIso θ.inv).2 c
    show θ.inv.hom (φ' (ψ d)) = θ.inv.hom d
    rw [hφ]
  refine ⟨(Spec (CommRingCat.of k)).isoSpec.hom ≫ Spec.map φ ≫ P'.isoSpec.inv, ?_⟩
  have nat' : P'.isoSpec.inv ≫ p = Spec.map p.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Category.assoc, Category.assoc, nat', ← Category.assoc (Spec.map φ), ← Spec.map_comp, hret, Spec.map_id,
    Category.id_comp, Iso.hom_inv_id]

theorem exists_div (hmul : MulNSt) {k : Type} [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (a₀ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (r : ℕ)
    (hr : 1 ≤ r) : ∃ b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, b ^ r = a₀ := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hmul (Spec (CommRingCat.of k)) P r hr
  obtain ⟨t, ht⟩ := exists_section (pullback.snd (mulA P.A r).left a₀.left)
  have hb' : (t ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ (mulA P.A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ P.A.hom = (baseOver (Spec (CommRingCat.of k))).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

end ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section Grp

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

lemma one_comp_hom (f : A ⟶ A) (hf : IsMonHom f) : (1 : T ⟶ A) ≫ f = 1 := by
  haveI := hf
  exact MonObj.one_comp f

lemma comp_act_nat {O : Type} [Ring O] (ρ : RingAct A O) (x : T ⟶ A) :
    ∀ n : ℕ, 1 ≤ n → x ≫ ρ.act (n : O) = x ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [ρ.map_one]
    · rw [Nat.cast_succ, ρ.map_add, ρ.map_one, padd, ← Category.assoc,
        CartesianMonoidalCategory.comp_lift, Category.comp_id, ih hpos, pow_succ, Hom.mul_def]

end Grp

section Weil

lemma weil_one_left (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (y : T ⟶ P.A) (hy : y ^ k = 1) : WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨H1, H2, -, -⟩ := hW S P k T
  obtain ⟨c, hc, -⟩ := H1 1 y (one_pow k) hy
  have hcc : WeilIs P.A P.L k 1 y (c * c) := by simpa using H2 1 1 y c c hc hc
  have huniq := (H1 1 y (one_pow k) hy).unique hc hcc

  have hc1 : c = 1 := mul_left_cancel (huniq.symm.trans (mul_one c).symm)
  rw [← hc1]
  exact hc

lemma weil_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ n : ℕ, WeilIs P.A P.L k (x ^ n) y (c ^ n) := by
    intro n
    induction n with
    | zero => simpa using weil_one_left hW P k y hy
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (hW S P k T).2.1 _ _ _ _ _ ih hc
  have h1 := hpow k
  rw [hx] at h1
  exact ((hW S P k T).1 1 y (one_pow k) hy).unique h1 (weil_one_left hW P k y hy)

lemma weil_unique (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c c' : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) (hc' : WeilIs P.A P.L k x y c') : c = c' :=
  ((hW S P k T).1 x y hx hy).unique hc hc'

end Weil

section Gen

open ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace

lemma top_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  exact (IsLocalRing.specializes_closedPoint (R := V) y).mem_open U.isOpen hU

theorem gen_local {V : Type} [CommRing V] [IsLocalRing V]
    (M : LB (Spec (CommRingCat.of V))) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by

  have hp : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ ⨆ i, M.U i := by
    rw [hM.cover]
    exact TopologicalSpace.Opens.mem_top _
  obtain ⟨i0, hi0⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  have htop : M.U i0 = ⊤ := top_of_closedPoint (M.U i0) hi0
  have hle : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i0 := fun W => by
    rw [htop]
    exact le_top
  have hid : ∀ {W : (Spec (CommRingCat.of V)).Opens} (h0 : W ≤ W) (z : Γ(Spec (CommRingCat.of V), W)ˣ), res h0 z = z := by
    intro W h0 z
    have h1 : homOfLE h0 = 𝟙 W := rfl
    ext
    simp [res, h1]

  refine ⟨⟨fun i => res (le_inf le_rfl (hle _) : M.U i ≤ M.U i ⊓ M.U i0) (M.g i i0)⟩, ?_⟩
  intro i j
  have hc := hM.cocycle i j i0
  have h' : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i0 := le_inf le_rfl (hle _)
  have hc' := congrArg (fun z => res h' z) hc
  simp only [map_mul, res_res', hid] at hc'
  simp only [res_res']
  exact hc'.symm

theorem gen_local_linComb {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X)
    (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen :=
  gen_local _ (by
    first
      | exact linComb_isLB
      | exact linComb_isLB hL
      | exact linComb_isLB (hL := hL)
      | exact linComb_isLB hL φ ε
      | exact linComb_isLB L hL φ ε
      | exact linComb_isLB (L := L) (φ := φ) (ε := ε) hL
      | exact linComb_isLB L φ ε hL)

end Gen

end ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
end
end
