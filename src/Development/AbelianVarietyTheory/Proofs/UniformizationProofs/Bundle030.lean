module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem le_v_sum_sub_sum {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F}
    (q : ℚ) {S T : Finset Ix} (hST : S ⊆ T) (hS : ∀ i, i ∉ S → (q : WithTop ℚ) ≤ v (x i)) :
    (q : WithTop ℚ) ≤ v (∑ i ∈ T, x i - ∑ i ∈ S, x i) := by
  classical
  rw [← Finset.sum_sdiff hST, add_sub_cancel_right]
  exact v.map_le_sum fun i hi => hS i (Finset.mem_sdiff.1 hi).2

theorem partial_sum_convolution {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X : Type} [AddCommGroup X]
    {a b c : X → F} (ha : NullV v a) (hb : NullV v b)
    (hc : ∀ α, SumV v (fun χ => a χ * b (α - χ)) (c α)) (q : ℚ) :
    ∀ᶠ T : Finset X in Filter.atTop,
      (q : WithTop ℚ) ≤ v (∑ i ∈ T, c i - (∑ i ∈ T, a i) * ∑ i ∈ T, b i) := by
  classical
  obtain ⟨ma, hma⟩ := nullV_bdd v ha
  obtain ⟨mb, hmb⟩ := nullV_bdd v hb
  set Sa := (ha (q - mb)).toFinset with hSa
  set Sb := (hb (q - ma)).toFinset with hSb
  have hSa' : ∀ χ, χ ∉ Sa → ((q - mb : ℚ) : WithTop ℚ) ≤ v (a χ) := fun χ hχ =>
    not_lt.1 fun h => hχ ((Set.Finite.mem_toFinset _).2 h)
  have hSb' : ∀ β, β ∉ Sb → ((q - ma : ℚ) : WithTop ℚ) ≤ v (b β) := fun β hβ =>
    not_lt.1 fun h => hβ ((Set.Finite.mem_toFinset _).2 h)
  filter_upwards [Filter.eventually_ge_atTop Sa, Filter.eventually_ge_atTop Sb,
    Filter.eventually_ge_atTop (Finset.image₂ (· + ·) Sa Sb)] with T hTa hTb hTU
  have h1 : ∀ α, (q : WithTop ℚ) ≤ v (c α - ∑ χ ∈ Sa, a χ * b (α - χ)) := fun α =>
    sumV_tail v (hc α) q Sa fun χ hχ => le_v_mul v (hSa' χ hχ) (hmb _) (by ring)
  have h4 : (q : WithTop ℚ) ≤ v (∑ α ∈ T, (c α - ∑ χ ∈ Sa, a χ * b (α - χ))) :=
    v.map_le_sum fun α _ => h1 α
  have h5 : ∀ χ ∈ Sa, ((q - ma : ℚ) : WithTop ℚ) ≤ v (∑ α ∈ T, b (α - χ) - ∑ α ∈ T, b α) := by
    intro χ hχ
    have e : ∑ α ∈ T, b (α - χ) = ∑ β ∈ T.image (· - χ), b β :=
      (Finset.sum_image (f := b) (g := (· - χ)) fun x _ y _ h => sub_left_injective h).symm
    have hsub : Sb ⊆ T.image (· - χ) := fun β h =>
      Finset.mem_image.2 ⟨χ + β, hTU (Finset.mem_image₂.2 ⟨χ, hχ, β, h, rfl⟩), by simp⟩
    have := v.map_le_sub (le_v_sum_sub_sum v _ hsub hSb') (le_v_sum_sub_sum v _ hTb hSb')
    rwa [sub_sub_sub_cancel_right, ← e] at this
  have h6 : (q : WithTop ℚ) ≤ v (∑ χ ∈ Sa, a χ * (∑ α ∈ T, b (α - χ) - ∑ α ∈ T, b α)) :=
    v.map_le_sum fun χ hχ => le_v_mul v (hma χ) (h5 χ hχ) (by ring)
  have h7 : (q : WithTop ℚ) ≤ v ((∑ i ∈ T, a i - ∑ i ∈ Sa, a i) * ∑ i ∈ T, b i) :=
    le_v_mul v (le_v_sum_sub_sum v _ hTa hSa') (v.map_le_sum fun i _ => hmb i) (by ring)
  have h8 := v.map_le_sub (v.map_le_add h4 h6) h7
  have e : ∑ i ∈ T, c i - (∑ i ∈ T, a i) * ∑ i ∈ T, b i =
      ∑ α ∈ T, (c α - ∑ χ ∈ Sa, a χ * b (α - χ)) +
        ∑ χ ∈ Sa, a χ * (∑ α ∈ T, b (α - χ) - ∑ α ∈ T, b α) -
        (∑ i ∈ T, a i - ∑ i ∈ Sa, a i) * ∑ i ∈ T, b i := by
    have e2 : ∑ α ∈ T, ∑ χ ∈ Sa, a χ * b (α - χ) = ∑ χ ∈ Sa, a χ * ∑ α ∈ T, b (α - χ) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    simp only [Finset.sum_sub_distrib, mul_sub, ← Finset.sum_mul]
    rw [e2]
    ring
  rw [e]
  exact h8

theorem partial_sum_convolution_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X : Type}
    [AddCommGroup X] {a : X → F} {c : ℕ → X → F} (h0 : c 0 = a) (hn : ∀ j, NullV v (c j))
    (hc : ∀ j α, SumV v (fun χ => c j χ * a (α - χ)) (c (j + 1) α)) (j : ℕ) (q : ℚ) :
    ∀ᶠ T : Finset X in Filter.atTop,
      (q : WithTop ℚ) ≤ v (∑ i ∈ T, c j i - (∑ i ∈ T, a i) ^ (j + 1)) := by
  have ha : NullV v a := h0 ▸ hn 0
  obtain ⟨ma, hma⟩ := nullV_bdd v ha
  induction j generalizing q with
  | zero => exact Filter.Eventually.of_forall fun T => by simp [h0]
  | succ j ih =>
    filter_upwards [ih (q - ma), partial_sum_convolution v (hn j) ha (hc j) q] with T h1 h2
    have h3 : (q : WithTop ℚ) ≤ v ((∑ i ∈ T, c j i - (∑ i ∈ T, a i) ^ (j + 1)) * ∑ i ∈ T, a i) :=
      le_v_mul v h1 (v.map_le_sum fun i _ => hma i) (by ring)
    have h4 := v.map_le_add h2 h3
    convert h4 using 2
    ring

theorem v_multiset_prod_le {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (Q : ℚ) (s : Multiset F)
    (h : ∀ x ∈ s, v x ≤ (Q : WithTop ℚ)) : v s.prod ≤ (((s.card : ℚ) * Q : ℚ) : WithTop ℚ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.prod_cons, v.map_mul, Multiset.card_cons]
    have e : (((s.card + 1 : ℕ) : ℚ) * Q : ℚ) = Q + (s.card : ℚ) * Q := by push_cast; ring
    rw [e, WithTop.coe_add]
    exact add_le_add (h x (Multiset.mem_cons_self _ _)) (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

theorem sumV_root_of_convolution_pow : ∀ (F : Type) [Field F] [IsAlgClosed F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] (a : X → F) (c : ℕ → X → F), c 0 = a → (∀ j, NullV v (c j)) → (∀ j α, SumV v (fun χ => c j χ * a (α - χ)) (c (j + 1) α)) → ∀ (m : ℕ) (β : F), SumV v (c m) β → ∃ r : F, SumV v a r ∧ r ^ (m + 1) = β := by
  classical
  intro F _ _ v X _ a c h0 hn hc m β hβ
  have ha : NullV v a := h0 ▸ hn 0
  by_contra hcon
  set p : Polynomial F := Polynomial.X ^ (m + 1) - Polynomial.C β with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_sub_C β (Nat.succ_ne_zero m)
  have hroot : ∀ r ∈ p.roots, r ^ (m + 1) = β := by
    intro r hr
    have := (Polynomial.mem_roots hmon.ne_zero).1 hr
    simpa [hp, sub_eq_zero] using this
  have hfar : ∀ r : F, ∃ q : ℚ, r ∈ p.roots →
      ∀ᶠ T : Finset X in Filter.atTop, v (∑ i ∈ T, a i - r) ≤ (q : WithTop ℚ) := by
    intro r
    by_cases hr : r ∈ p.roots
    · have h1 : ¬ SumV v a r := fun h => hcon ⟨r, h, hroot r hr⟩
      obtain ⟨q, hq⟩ := not_forall.1 h1
      refine ⟨q, fun _ => ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (ha q).toFinset] with T hT
      by_contra hlt
      refine hq ⟨T, fun T' hT' => ?_⟩
      have h2 := le_v_sum_sub_sum v q hT' (x := a) fun i hi =>
        not_lt.1 fun h => hi (hT ((Set.Finite.mem_toFinset _).2 h))
      have h3 := v.map_le_add h2 (not_le.1 hlt).le
      rw [sub_add_sub_cancel, v.map_sub_swap] at h3
      exact h3
    · exact ⟨0, fun h => absurd h hr⟩
  choose qf hqf using hfar
  obtain ⟨Q, hQ⟩ := (p.roots.toFinset.image qf).finite_toSet.bddAbove
  have hQ' : ∀ r ∈ p.roots, qf r ≤ Q := fun r hr =>
    hQ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Multiset.mem_toFinset.2 hr)))
  have e1 : ∀ᶠ T : Finset X in Filter.atTop, ∀ r ∈ p.roots.toFinset,
      v (∑ i ∈ T, a i - r) ≤ (qf r : WithTop ℚ) :=
    (Filter.eventually_all_finset _).2 fun r hr => hqf r (Multiset.mem_toFinset.1 hr)
  set q : ℚ := (p.roots.card : ℚ) * Q + 1 with hq
  have e2 := partial_sum_convolution_pow v h0 hn hc m q
  have e3 : ∀ᶠ T : Finset X in Filter.atTop, (q : WithTop ℚ) ≤ v (β - ∑ i ∈ T, c m i) :=
    Filter.eventually_atTop.2 (hβ q)
  obtain ⟨T, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  have h4 := v.map_le_add h3 h2
  rw [sub_add_sub_cancel, v.map_sub_swap] at h4
  have h5 : (∑ i ∈ T, a i) ^ (m + 1) - β = (p.roots.map fun r => ∑ i ∈ T, a i - r).prod := by
    have := (IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmon (∑ i ∈ T, a i)
    simpa [hp] using this
  have h6 := v_multiset_prod_le v Q (p.roots.map fun r => ∑ i ∈ T, a i - r) (by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    exact (h1 r (Multiset.mem_toFinset.2 hr)).trans (WithTop.coe_le_coe.2 (hQ' r hr)))
  rw [← h5, Multiset.card_map] at h6
  have h7 := WithTop.coe_le_coe.1 (h4.trans h6)
  linarith

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
  {X : Scheme.{0}} {L : LB X}

theorem isDominant_ι : IsDominant (ιS hϖ hv).left := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap (algebraMap (Ov v) F))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (Ov v) F)]
  exact bot_le

theorem ι_inj [X.IsSeparated] : Function.Injective fun ψ : (TO hϖ hv).left ⟶ X => (ιS hϖ hv).left ≫ ψ := by
  intro a b h
  have := isDominant_ι hϖ hv
  have : IsReduced (TO hϖ hv).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (Ov v))))
  exact ext_of_isDominant (ιS hϖ hv).left h

theorem gs_ι (z : (TF (R := V) F).left) (a : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ιS hϖ hv).left z ⊤ a = cst F z (ιr (v := v) a) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := V) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap (Ov v) F)) a)

theorem sec_int [X.IsSeparated] (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = 1) :
    ∃ a : F, 0 ≤ v a ∧ ∀ z J, Good L z J → sval s (ιS hϖ hv).left z J = cst F z a := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιS hϖ hv).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj hϖ hv).extend_apply]) s
  have le : (⊤ : (TO hϖ hv).left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → ((TO hϖ hv).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨ιr (v := v) (((TO hϖ hv).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), v_ιr _,
    fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι hϖ hv]
  exact (gs_res _ z le trivial _).symm

abbrev FS (V F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra (FractionRing V) F] (X : Scheme.{0}) : Type 1 :=
  ∀ (U : Type) [CommGroup U], (((TF (R := V) F).left ⟶ X) → U) → U

def HV (L : LB X) (σ : FS V F X)
    (f : ∀ z : (TF (R := V) F).left, (((TF (R := V) F).left ⟶ X) → L.ι) → (TF (R := V) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TO hϖ hv).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιS hϖ hv).left z J).val

variable {hϖ hv}

theorem HV.mul {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x) (H' : HV hϖ hv L σ' f' x') :
    HV hϖ hv L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HV.one : HV hϖ hv L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TO hϖ hv).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HV.congr {σ σ' : FS V F X} {f f'} {x : F} (H : HV hϖ hv L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HV hϖ hv L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HV.pow {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (n : ℕ) :
    HV hϖ hv L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HV.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HV.smul {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (c : F) :
    HV hϖ hv L σ (fun z J => cst F z c * f z J) (c * x) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  refine ⟨K, _, φ, ε, t, ht, hs, fun z J hJ => ?_⟩
  simp only [e z J hJ, cst_eq, map_mul, _root_.mul_assoc]

theorem HV.le [X.IsSeparated] (hL : L.IsLB) {σ : FS V F X} {f} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ f x') : v x ≤ v x' := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', mul_inv_cancel])
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : x' = x * a := by
    apply cstH_inj (R := V) z
    have d := (e z J hJ).symm.trans (e' z J hJ)
    rw [map_mul, ← cst_eq, ← cst_eq, ← cst_eq, ← b, Units.val_mul, ← _root_.mul_assoc, d, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]
  rw [c, AddValuation.map_mul]
  exact le_add_of_nonneg_right ha

theorem HV.cmp [X.IsSeparated] (hL : L.IsLB) {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h)
    (hf : ∀ z J, Good L z J → f' z J = f z J) : v x = v x' :=
  le_antisymm ((H.congr hσ hf).le hL H') (H'.le hL (H.congr hσ hf))

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem hv_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem hv_sec [X.IsSeparated] (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    ∃ x, 0 ≤ v x ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) x := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := Ov v) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, ha, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem hv_of_genV {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} {r : ℚ}
    (H : GenV hϖ hv t r) :
    ∃ x, v x = r ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  obtain ⟨φ₀, h₀, t₀, ht₀, x, hx, e⟩ := H
  exact ⟨x, hx, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], e⟩

theorem genV_unique [X.IsSeparated] (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)}
    {t : LB.Gen (LB.LinComb L φ ε)} {r r' : ℚ} (H : GenV hϖ hv t r) (H' : GenV hϖ hv t r') : r = r' := by
  obtain ⟨x, hx, a⟩ := hv_of_genV H
  obtain ⟨x', hx', a'⟩ := hv_of_genV H'
  have := a.cmp hL a' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [hx, hx'] at this
  exact_mod_cast this

theorem exists_genV (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιS hϖ hv).left ≫ ψ) : ∃ r, GenV hϖ hv t r := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := Ov v) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) hc
  refine ⟨q, φ₀, h₀, t₀, ht₀, c, hq, fun z J hJ => ?_⟩
  have := e (TF (R := V) F).left (𝟙 (TF (R := V) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end GlobalTheory.UT.CoefVal
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.NonVan
open GlobalTheory.UT.CoefBasic

theorem val_powFrame {S : Scheme.{0}} {A : Over S} (L : LB A.left) {T : Over S} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame A L x τ k) r z J = val τ r z J ^ k :=
  map_zpow _ _ _

theorem exists_sec_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 4 ≤ k → ∀ (x : TFK (R := R) F ⟶ A.A) (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), e.IsGen → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) := by
  intro hL R _ _ A F _ _ k hk x e he
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  obtain ⟨t, ht⟩ := GlobalTheory.TwistUnit.unitAt_pow hL.1.ample A k hk (snd (TFK (R := R) F) A.A).left
    ((ptSecT A.A x).left z)
  have hu := GlobalTheory.TwistUnit.isUnit_sval_of A.isLB t (ptSecT A.A x).left z ht J' hJ'
  obtain ⟨c, hc⟩ := cstH_surj z (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val
  refine ⟨t, c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq (R := R) z z'
    have a₁ := sval_tr t (ptSecT A.A x).left hJ hJ'
    have a₂ := val_tr he (𝟙 _) hJ hJ'
    have hx : (ptSecT A.A x).left ≫ (snd (TFK (R := R) F) A.A).left = x.left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [Fin.prod_univ_one, hx, ← hu.unit_spec] at a₁
    rw [Fin.prod_univ_one, Category.id_comp, zpow_one] at a₂
    have a₃ : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) =
        (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val := (cst_eq z c).trans hc
    refine a₁.trans ?_
    rw [a₃, val_powFrame, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module

end GlobalTheory.UT.NonVan
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefFE
open GlobalTheory.UT.CoefBasic

theorem coef_fe : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (h o : GtPtF D F), GtPtF.IsIota y h → o.IsZero → ∀ (w : Frm D F k h.b) (w₁ : Frm D F k o.b), w.IsGen → FrmOne w₁ → (∀ z J, Good D.P.L z J → val w (𝟙 _) z J = (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) ^ k) → ∀ (s : Fam D F k) (α : D.X), coef s o w₁ (α + k • y) = coef s h w α := by
  intro hL R _ _ D F _ _ k y h o hh ho w w₁ hw hw₁ vw s α
  obtain ⟨hb, hs⟩ := (isIota_iff _ _).1 hh
  obtain ⟨ob, os⟩ := (isZero_iff _).1 ho
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hL.1.globalFns k y α
  refine coef_eq fun z J hJ => ?_
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _ (DegPre.zF D F).left z J hJ
  have u₀ := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at u₀
  have m := val_famMult (𝟙 (TF (R := R) F)) hJ k y α
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val (D.psi y) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val D.rigK ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  rw [p₁, p₂, Over.id_left, Category.id_comp] at m
  have r : val D.rigK (jFK (R := R) F) z J = rigV D (TF (R := R) F).hom z J := val_pull hJ _ _ _
  have z₁ : lift (𝟙 (TF (R := R) F)) o.b = DegPre.zF D F := by rw [ob]; rfl
  have z₂ : DegPre.zF D F ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) h.b := by
    have a₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    have a₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, a₁, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, a₂, ← Category.assoc, a₁, Category.id_comp, _root_.one_mul]
  rw [← Over.comp_left, z₂, u₀] at e
  have t := hs α z J hJ
  rw [Category.id_comp] at t
  rw [isCoef_coef h hw α s z J hJ, z₁, e, os _ z J hJ, hw₁.2 z J hJ, t, vw z J hJ]
  have m' := congrArg Units.val m
  rw [r] at m'
  simp only [Units.val_one, _root_.mul_one, id, mul_pow, _root_.mul_assoc]
  exact congrArg₂ (· * ·) rfl m'.symm

end GlobalTheory.UT.CoefFE
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem expandsF_total : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → (∀ s : Fam D.toPre F k, ∃ t, U.toUnifPre.ExpandsF F k w t s) ∧ ∀ t, ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  intro h₁ _ R _ _ I _ D A G _ _ _ U F _ _ k hk w hw
  have h := FieldBaseChange.expandsF_bijective U.toUnifPre F h₁.globalFns hk (U.expand k hk) hw
  exact ⟨fun s => (h.2 s).exists, fun t => (h.1 t).exists⟩

end GlobalTheory
end
