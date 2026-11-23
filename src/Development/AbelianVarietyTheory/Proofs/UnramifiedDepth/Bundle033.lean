module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Mathlib.RingTheory.PowerSeries.Exp
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle030
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.GaugeCocycle ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.RowVal

open MvPowerSeries

variable {C : Type} [Field C]

theorem mvExp_eq_subst [CharZero C] {σ : Type} {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    mvExp F = PowerSeries.subst F (PowerSeries.exp C) := by
  classical
  ext m
  have hS : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · show (∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C)) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    rw [Function.mem_support] at hk
    by_contra hk'
    apply hk
    have h1 : m.degree < k := by simpa using hk'
    have h0 : coeff m (F ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hF)
      exact_mod_cast h1
    rw [h0, smul_zero]

theorem mvExp_add [CharZero C] {σ : Type} {F G : MvPowerSeries σ C} (hF : constantCoeff F = 0)
    (hG : constantCoeff G = 0) : mvExp (F + G) = mvExp F * mvExp G := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst hG, mvExp_eq_subst (by rw [map_add (f := _), hF, hG, add_zero]),
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hF hG]

theorem mvExp_zero' [CharZero C] {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  rw [mvExp_eq_subst (map_zero _), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]

theorem mvExp_sum [CharZero C] {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C}
    (hF : ∀ i, constantCoeff (F i) = 0) : mvExp (∑ i ∈ s, F i) = ∏ i ∈ s, mvExp (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero']
  | insert a s ha ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert ha, Finset.prod_insert ha, mvExp_add (hF a) (by simp [map_sum, hF]), ih]

theorem cc_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (F : MvPowerSeries σ C) : constantCoeff (subst a F) = constantCoeff F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [e, subst_add hs, map_add (f := _), constantCoeff_subst_zero ha (by simp), subst_C]
  simp

theorem subst_mvExp [CharZero C] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    subst a (mvExp F) = mvExp (subst a F) := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst (by rw [cc_subst ha, hF]), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hF]

theorem intS_subst {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C} (hF : IntS V F) :
    IntS V (subst a F) :=
  (intS_iff_ig V _).2 (ig_subst (fun s => (intS_iff_ig V _).1 (hi s)) ha ((intS_iff_ig V _).1 hF))

theorem intS_X {V : VF C} {σ : Type} (s : σ) : IntS V (X s : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (ig_X s)

theorem intS_one {V : VF C} {σ : Type} : IntS V (1 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (one_mem _)

theorem intS_zero {V : VF C} {σ : Type} : IntS V (0 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (zero_mem _)

theorem intS_mul {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F) (hG : IntS V G) :
    IntS V (F * G) :=
  (intS_iff_ig V _).2 (mul_mem ((intS_iff_ig V _).1 hF) ((intS_iff_ig V _).1 hG))

theorem intS_prod {V : VF C} {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C} (hF : ∀ i, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) :=
  (intS_iff_ig V _).2 (prod_mem fun i _ => (intS_iff_ig V _).1 (hF i))

theorem intS_of_mul_eq_one {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F)
    (h1 : constantCoeff F = 1) (hFG : F * G = 1) : IntS V G := by
  obtain ⟨U, hU⟩ := RingHom.mem_range.1 ((intS_iff_ig V _).1 hF)
  have hU1 : constantCoeff U = 1 := by
    apply Subtype.ext
    have e := congrArg constantCoeff hU
    rw [constantCoeff_map, h1] at e
    exact e
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 := MvPowerSeries.mul_invOfUnit U 1 (by simp [hU1])
  have e : G = MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1) := by
    have h2 := congrArg (MvPowerSeries.map (σ := σ) (algebraMap (valRing V) C)) hinv
    rw [map_mul, map_one, hU] at h2
    calc G = G * (F * MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1)) := by
          rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, mul_comm G F, hFG, one_mul]
  rw [e]
  exact (intS_iff_ig V _).2 (ig_map _)

def logInt [CharZero C] (V : VF C) (σ : Type) : AddSubgroup (MvPowerSeries σ C) where
  carrier := {F | constantCoeff F = 0 ∧ IntS V (mvExp F)}
  zero_mem' := ⟨map_zero _, by rw [mvExp_zero']; exact intS_one⟩
  add_mem' := fun {F G} hF hG => ⟨by rw [map_add (f := _), hF.1, hG.1, add_zero], by
    rw [mvExp_add hF.1 hG.1]; exact intS_mul hF.2 hG.2⟩
  neg_mem' := fun {F} hF => ⟨by rw [map_neg, hF.1, neg_zero], by
    refine intS_of_mul_eq_one hF.2 ?_ ?_
    · rw [mvExp_eq_subst hF.1, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp hF.1]
    · rw [← mvExp_add hF.1 (by rw [map_neg, hF.1, neg_zero]), add_neg_cancel, mvExp_zero']⟩

theorem mem_logInt [CharZero C] {V : VF C} {σ : Type} {F : MvPowerSeries σ C} :
    F ∈ logInt V σ ↔ constantCoeff F = 0 ∧ IntS V (mvExp F) := Iff.rfl

theorem logInt_subst [CharZero C] {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C}
    (hF : F ∈ logInt V σ) : subst a F ∈ logInt V τ :=
  ⟨by rw [cc_subst ha, hF.1], by rw [← subst_mvExp ha hF.1]; exact intS_subst ha hi hF.2⟩

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def IntEnd (X : RawChart C d I κ) (V : VF C) (A : Matrix κ κ C) : Prop :=
  ∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)

def hEnd (X : RawChart C d I κ) (A B : Matrix κ κ C) : MvPowerSeries κ C :=
  hAt X (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C)) (endP X B (MvPowerSeries.X : κ → MvPowerSeries κ C))

end GlobalTheory.RowVal
end
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem isCv_of_subst_X_pow {C : Type} [Field C] (V : VF C) {σ : Type} {m : ℕ} (hm : 0 < m)
    (δ γ : σ → PowerSeries C) (hγ : IsCv V γ)
    (h : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (δ i) = γ i) : IsCv V δ := by
  intro i
  have hc : ∀ n, PowerSeries.coeff n (δ i) = PowerSeries.coeff (m * n) (γ i) := by
    intro n
    rw [← h i, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm]
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hγ i).1
  · rw [hc]
    exact (hγ i).2 _

theorem cvRoot_alongCv_comp {C : Type} [Field C] {σ τ : Type} [Finite σ] [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {f : σ → MvPowerSeries τ C}
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) (F : MvPowerSeries σ C) :
    alongCv (fun i => alongCv γ (f i)) F = alongCv γ (MvPowerSeries.subst f F) := by
  unfold alongCv
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hf)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)]

theorem cvRoot_alongCv_X {C : Type} [Field C] {τ : Type} [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : τ) :
    alongCv γ (MvPowerSeries.X i : MvPowerSeries τ C) = γ i := by
  unfold alongCv
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ) i

theorem mem_Cv_of_subst_X_pow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (m : ℕ), 0 < m → ∀ a : ((κ → PowerSeries C) × (JJ I g → PowerSeries C)), ((fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i), fun q => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g → a ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X H g m hm a ha
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hτ : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ m) = 0 := by simp [hm.ne']
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp)]
    simp
  have h1' : ∀ i, alongCv γ (X.lg i) = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i) := h1
  have h2' : ∀ q, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) := h2
  have ha0 : ∀ i, PowerSeries.constantCoeff (a.1 i) = 0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm, ← h1' i, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (τ := Unit) hγ0 (hlg i)
  have hsub : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (alongCv a.1 (X.ex i)) = γ i := by
    intro i
    rw [← alongCv_repar ha0 hτ]
    have : (fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i)) =
        fun i => alongCv γ (X.lg i) := funext fun i => (h1' i).symm
    rw [this, cvRoot_alongCv_comp hγ0 hlg, H.exlg, cvRoot_alongCv_X hγ0]
  have hcv : IsCv V (fun i => alongCv a.1 (X.ex i)) := isCv_of_subst_X_pow V hm _ γ hγ hsub
  refine ⟨fun i => alongCv a.1 (X.ex i),
    fun q => a.2 q + alongCv (fun i => alongCv a.1 (X.ex i)) (X.sg (X.u (1 - g) q)), hcv,
    isCv_of_subst_X_pow V hm _ lam hlam ?_, ?_, ?_⟩
  · intro q
    rw [PowerSeries.subst_add hS, h2', ← alongCv_repar (fun i => (hcv i).1) hτ, funext hsub, sub_add_cancel]
  · intro i
    rw [cvRoot_alongCv_comp ha0 H.exc, H.lgex, cvRoot_alongCv_X ha0]
  · intro q
    simp

end GlobalTheory.RowLaw
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ChF

private theorem exists_leftInv {O OE : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CommRing OE] {d n : ℕ}
    (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O) (h : EigB ρ τ W) :
    ∃ G : Matrix (Fin n) (Fin d) O, ∀ i, G *ᵥ W i = Pi.single i 1 := by
  classical
  let φ : (Fin n → O) →ₗ[O] (Fin d → O) := Fintype.linearCombination O W
  have hφ : ∀ c, φ c = ∑ i, c i • W i := fun c => Fintype.linearCombination_apply O W c
  have heig : ∀ c a, (ρ a) *ᵥ φ c = τ a • φ c := by
    intro c a
    rw [hφ, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, h.1, smul_comm]
  have hinj : Function.Injective φ := by
    intro c c' hc
    obtain ⟨c₀, -, hu⟩ := h.2 (φ c) (heig c)
    rw [hu c (hφ c).symm, hu c' (by rw [hc]; exact (hφ c').symm)]
  have htf : Submodule.torsion O ((Fin d → O) ⧸ LinearMap.range φ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨t, ht⟩, hx⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hx' : (Submodule.Quotient.mk (t • y) : (Fin d → O) ⧸ LinearMap.range φ) = 0 := by
      rw [Submodule.Quotient.mk_smul]; exact hx
    rw [Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨c, hc⟩ := hx'
    have hy : ∀ a, (ρ a) *ᵥ y = τ a • y := by
      intro a
      have := heig c a
      rw [hc, Matrix.mulVec_smul, smul_comm] at this
      exact smul_right_injective _ ht0 this
    obtain ⟨c₀, hc₀, -⟩ := h.2 y hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨c₀, (hφ c₀).trans hc₀⟩
  haveI : Module.Flat O ((Fin d → O) ⧸ LinearMap.range φ) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htf
  haveI : Module.Free O ((Fin d → O) ⧸ LinearMap.range φ) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y, (LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ : (Fin d → O) →ₗ[O] (Fin d → O)) y ∈ LinearMap.range φ := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this, sub_self]
  let g : (Fin d → O) →ₗ[O] (Fin n → O) :=
    (LinearEquiv.ofInjective φ hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hmem
  have hg : ∀ c, g (φ c) = c := by
    intro c
    have h0 : (LinearMap.range φ).mkQ (φ c) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨c, rfl⟩
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    ext1
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, h0,
      map_zero, sub_zero, LinearEquiv.ofInjective_apply]
  refine ⟨LinearMap.toMatrix' g, fun i => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, ← hg (Pi.single i 1), hφ]
  congr 1
  simp [Pi.single_apply]

theorem eigB_res_surjective : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  classical
  intro C _ v O _ _ hv OE _ d n ρ τ W h
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨G, hG⟩ := exists_leftInv ρ τ W h
  refine ⟨fun c => ⟨Gᵀ *ᵥ c, ?_⟩, fun a f => ?_, ?_⟩
  · have h1 : Matrix.of W * Gᵀ = 1 := by
      ext i k
      have := congrFun (hG i) k
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm (a := i), ← this, mul_comm]
    simp only [Pdiv.ChartF.res, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · ext i
    have : Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) i = W i ⬝ᵥ ((ρ a)ᵀ *ᵥ f) := rfl
    rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h.1, smul_dotProduct]
    rfl
  · let W' : Fin n → Fin d → C := fun i => algebraMap O C ∘ W i
    have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin d) O) (y : Fin d → O),
        M.map (algebraMap O C) *ᵥ (algebraMap O C ∘ y) = algebraMap O C ∘ (M *ᵥ y) := by
      intro m M y
      ext k
      exact (RingHom.map_mulVec (algebraMap O C) M y k).symm
    have hli : LinearIndependent C W' := by
      refine LinearIndependent.of_comp (Matrix.mulVecLin (G.map (algebraMap O C))) ?_
      have : (Matrix.mulVecLin (G.map (algebraMap O C))) ∘ W' = Pi.basisFun C (Fin n) := by
        funext i
        simp only [Function.comp_apply, Matrix.mulVecLin_apply, W', hmap, hG]
        ext k
        simp [Pi.single_apply, apply_ite]
      rw [this]
      exact (Pi.basisFun C (Fin n)).linearIndependent
    have hsp : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (((algebraMap O C).comp τ) a)) = Submodule.span C (Set.range W') := by
      apply le_antisymm
      · intro x hx
        simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
        obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
        choose y hy using hbx
        have hb0 : algebraMap O C b ≠ 0 := by
          rw [map_ne_zero_iff _ hv.hom_inj]; exact nonZeroDivisors.ne_zero hb
        have hyx : algebraMap O C ∘ y = algebraMap O C b • x := by
          ext k
          simp only [Function.comp_apply, hy k, Pi.smul_apply, Algebra.smul_def]
          rfl
        have hye : ∀ a, (ρ a) *ᵥ y = τ a • y := by
          intro a
          ext k
          apply hv.hom_inj
          have := congrFun (hmap (ρ a) y) k
          rw [hyx, Matrix.mulVec_smul, hx a, smul_comm, ← hyx] at this
          simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.comp_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← this]
        obtain ⟨c, hc, -⟩ := h.2 y hye
        rw [← Submodule.smul_mem_iff _ hb0, ← hyx, ← hc]
        have : algebraMap O C ∘ (∑ i, c i • W i) = ∑ i, algebraMap O C (c i) • W' i := by
          ext k
          simp [W', Finset.sum_apply, Algebra.smul_def]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        intro a
        simp only [W', hmap, h.1]
        ext k
        simp
    unfold eigDim
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem existsUnique_lift_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {OE : Type} [CommRing OE] [Module.Finite ℤ OE]
    (τ : OE →+* C) : ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ := by
  have h : ∀ x : OE, ∃ y : O, algebraMap O C y = τ x := fun x => by
    have h1 : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    have h2 : IsIntegral ℤ (τ x) := h1.map τ.toIntAlgHom
    have h3 : IsIntegral O (τ x) := h2.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h3)
  choose f hf using h
  refine ⟨{ toFun := f
            map_one' := hv.hom_inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hv.hom_inj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hv.hom_inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hv.hom_inj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }, ?_, ?_⟩
  · exact RingHom.ext hf
  · intro g hg
    refine RingHom.ext fun x => hv.hom_inj ?_
    change algebraMap O C (g x) = algebraMap O C (f x)
    rw [hf, ← hg]
    rfl

theorem embeddings_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  refine ⟨existsUnique_lift_integers hv, fun e τ he => ?_, ?_⟩
  · have h : IsIdempotentElem (tauExt τ e) := by
      unfold IsIdempotentElem
      rw [← map_mul, he]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h
  · intro _ τ x
    have h2 : sig p OE x = sigE p OE x := rfl
    refine ⟨?_, h2⟩
    rw [← h2]
    clear h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tauExt, sig]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

end GlobalTheory.ChF
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem thickMap_comp_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    Out.thickMap R I e G ≫ (Out.fstG I (e + 1) G).left = (Out.fstG I e G).left :=
  pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)

theorem qRel_succ : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] z y, QRel (U.gt k) S z y → QRel (U.gt (k + 1)) S z y := by
  intro R _ _ I D A G _ _ U k S _ _ z y h
  obtain ⟨w, h₁, h₂⟩ := h
  refine ⟨w ≫ Out.thickMap R I k G, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) (thickMap_comp_fstG I k G)).trans h₁)
  · exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) (U.gt_q k)).trans h₂)

end GlobalTheory.ChF
end
end
