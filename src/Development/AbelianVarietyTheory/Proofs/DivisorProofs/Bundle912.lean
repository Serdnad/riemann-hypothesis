module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle789
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle882
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Shift.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem int_comb_unit_norm_single {ι G : Type} [Fintype ι] [Fintype G] (l : ℕ) (hl : l.Prime)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ l) (f : ι → G → ℂ) (c : ι → ℤ) (R : ι → ι → Prop)
    (hR : Equivalence R) (hG : (Fintype.card G : ℂ) ≠ 0)
    (hnorm : ∀ i, ∑ g, f i g * star (f i g) = Fintype.card G)
    (horth : ∀ i j, ∑ g, f i g * star (f j g) ≠ 0 → R i j)
    (hrel : ∀ i j, R i j → ∃ a < l, ∀ g, f i g = ζ ^ a * f j g)
    (hsum : ∑ g, (∑ i, (c i : ℂ) * f i g) * star (∑ i, (c i : ℂ) * f i g) = Fintype.card G) :
    ∃ i₀ e, ∀ g, ∑ i, (c i : ℂ) * f i g = e * f i₀ g := by
  letI S : Setoid ι := ⟨R, hR⟩
  let rep : Quotient S → ι := Quotient.out
  have hrep : ∀ t : ι, R t (rep ⟦t⟧) := fun t => hR.symm (Quotient.mk_out t)
  choose a ha hfa using fun t => hrel t _ (hrep t)
  let n : Quotient S → ℕ → ℤ := fun i b => ∑ t, if (⟦t⟧ : Quotient S) = i ∧ a t = b then c t else 0
  let C : Quotient S → ℂ := fun i => ∑ b ∈ Finset.range l, (n i b : ℂ) * ζ ^ b
  have hF : ∀ g, ∑ t, (c t : ℂ) * f t g = ∑ i, C i * f (rep i) g := by
    intro g
    have h1 : ∀ i, C i * f (rep i) g =
        ∑ t, if (⟦t⟧ : Quotient S) = i then (c t : ℂ) * (ζ ^ a t * f (rep i) g) else 0 := by
      intro i
      simp only [C, n, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : (⟦t⟧ : Quotient S) = i
      · simp only [h, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_range, ha t, if_true]
        ring
      · simp [h]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp [hfa t g]
  have hort : ∀ i j, i ≠ j → ∑ g, f (rep i) g * star (f (rep j) g) = 0 := by
    intro i j hij
    by_contra h
    apply hij
    rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound (horth _ _ h)
  have hexp : ∀ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      ∑ i, ∑ j, C i * star (C j) * (f (rep i) g * star (f (rep j) g)) := by
    intro g
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have h2 : ∑ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      (∑ i, C i * star (C i)) * Fintype.card G := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · rw [← Finset.mul_sum, hnorm]
    · intro j _ hji
      rw [← Finset.mul_sum, hort i j (Ne.symm hji), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hF] at hsum
  rw [h2] at hsum
  have h3 : ∑ i, C i * star (C i) = 1 := by
    have := hsum
    rw [← one_mul (Fintype.card G : ℂ)] at this
    exact mul_right_cancel₀ hG (by simpa using this)
  obtain ⟨i₀, -, hi₀⟩ := GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero l ζ hl hζ (Quotient S) Finset.univ n h3
  refine ⟨rep i₀, C i₀, fun g => ?_⟩
  rw [hF, Finset.sum_eq_single i₀]
  · intro i _ hi
    have : C i = 0 := hi₀ i (Finset.mem_univ i) hi
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i₀) h

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem virt_coset_norm_one_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ),
    ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
    ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
      ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  intro G Γ _ _ _ _ φ s hp hs X hX hXn
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  obtain ⟨c, hirr, hXc, -⟩ := GlobalTheory.BI.virt_expand (G ⋊[φ] Γ) X hX
  let T := c.support.filter (fun χ : G ⋊[φ] Γ → ℂ => ¬ ∀ δ, χ (inl δ * inr s) = 0)
  have hT : ∀ t : T, IsIrrChar ℂ ℂ t.1 ∧ ¬ ∀ δ, t.1 (inl δ * inr s) = 0 := fun t =>
    ⟨hirr _ (Finset.mem_filter.1 t.2).1, (Finset.mem_filter.1 t.2).2⟩
  let f : T → G → ℂ := fun t g => t.1 (inl g * inr s)
  have hX' : ∀ g, X (inl g * inr s) = ∑ t : T, (c t.1 : ℂ) * f t g := by
    intro g
    rw [hXc, Finsupp.sum, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    rw [Finset.sum_coe_sort T (fun χ => (c χ : ℂ) * χ (inl g * inr s))]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rw [h g, mul_zero]
    · rfl
  let R : T → T → Prop := fun t u => ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧
    ∀ x, t.1 x = u.1 x * (η x : ℂ)
  have hR : Equivalence R := by
    refine ⟨fun t => ⟨1, fun g => rfl, fun x => by simp⟩, ?_, ?_⟩
    · rintro t u ⟨η, h1, h2⟩
      refine ⟨η⁻¹, fun g => by simp [h1 g], fun x => ?_⟩
      rw [h2 x, MonoidHom.inv_apply, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
    · rintro t u v ⟨η, h1, h2⟩ ⟨η', h1', h2'⟩
      refine ⟨η' * η, fun g => by simp [h1 g, h1' g], fun x => ?_⟩
      rw [h2 x, h2' x, MonoidHom.mul_apply, Units.val_mul, mul_assoc]
  haveI : NeZero (Nat.card Γ) := ⟨hp.ne_zero⟩
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  have hnorm : ∀ t, ∑ g, f t g * star (f t g) = Fintype.card G := by
    intro t
    rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t.1 (hT t).1 with h | ⟨-, h⟩
    · exact absurd h (hT t).2
    · rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at h
      exact h
  have horth : ∀ t u, ∑ g, f t g * star (f u g) ≠ 0 → R t u := by
    intro t u h
    rcases GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist G Γ φ s hp hs t.1 u.1 (hT t).1 (hT u).1 with h' | h'
    · rw [finsum_eq_sum_of_fintype] at h'
      exact absurd h' h
    · exact h'
  have hrel : ∀ t u, R t u → ∃ a < Nat.card Γ, ∀ g,
      f t g = Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) ^ a * f u g := by
    rintro t u ⟨η, h1, h2⟩
    have hpow : ((η (inr s) : ℂˣ) : ℂ) ^ Nat.card Γ = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one,
        Units.val_one]
    obtain ⟨a, ha, hb⟩ := hζ.eq_pow_of_pow_eq_one hpow
    refine ⟨a, ha, fun g => ?_⟩
    simp only [f]
    rw [h2, map_mul, h1, one_mul, hb, mul_comm]
  have hsum : ∑ g, (∑ t : T, (c t.1 : ℂ) * f t g) * star (∑ t : T, (c t.1 : ℂ) * f t g) =
      Fintype.card G := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at hXn
    simp_rw [← hX']
    exact hXn
  obtain ⟨t₀, e, he⟩ := int_comb_unit_norm_single (Nat.card Γ) hp _ hζ f (fun t => c t.1) R hR
    (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hnorm horth hrel hsum
  refine ⟨t₀.1, e, (hT t₀).1, ?_, fun δ => by rw [hX', he]⟩
  rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t₀.1 (hT t₀).1 with h | ⟨h, -⟩
  · exact absurd h (hT t₀).2
  · exact h

end GlobalTheory.Shin
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH

namespace GlobalTheory.UMin.NormIso

def toFld (K : Type) [Field K] : ((Sp K).presheaf.stalk (IsLocalRing.closedPoint K))ˣ →* Kˣ :=
  Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom

theorem toFld_gm {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    (toFld K (gm x _ U a)).val = valF x U a.val := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x U hU
  refine Eq.trans ?_ ((congrArg (fun φ => φ.hom a.val) e).trans (GlobalTheory.Points.valR_eq x U hU _).symm)
  exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((gm_val x _ U h a).trans
    (Scheme.Hom.germ_stalkMap_apply x U (IsLocalRing.closedPoint K) h a.val).symm)

theorem toFld_gm_spMap {K K' : Type} [Field K] [Field K'] (σ : K →+* K') {X : Scheme.{0}} (x : Sp K ⟶ X)
    (U : X.Opens) (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    toFld K' (gm (spMap σ ≫ x) _ U a) = Units.map σ.toMonoidHom (toFld K (gm x _ U a)) := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  apply Units.ext
  rw [toFld_gm (spMap σ ≫ x) U (hU (x := spMap σ (IsLocalRing.closedPoint K')) trivial)]
  show _ = σ (toFld K (gm x _ U a)).val
  rw [toFld_gm x U h]
  exact GlobalTheory.Points.valR_spMap_comp σ x U hU _

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] {M : RatModel k Ω}

theorem pt_mem {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) : M.pt (IsLocalRing.closedPoint Ω) ∈ U :=
  M.top_le_preimage_pt hU (x := IsLocalRing.closedPoint Ω) trivial

theorem unit_ext_pt {U : M.Z.Opens} {a b : Γ(M.Z, U)ˣ}
    (h : M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = toFld Ω (gm M.pt _ U b)) : a = b := by
  by_cases hU : (U : Set M.Z).Nonempty
  · have e := congrArg Units.val (h (pt_mem hU))
    rw [toFld_gm _ _ (pt_mem hU), toFld_gm _ _ (pt_mem hU)] at e
    exact Units.ext (M.valF_injective hU e)
  · exact unit_ext fun x hx => absurd ⟨x, hx⟩ hU

theorem exists_unit {U : M.Z.Opens} (c : Ωˣ) (h : ∀ z ∈ U, c.val ∈ M.O z ∧ (c⁻¹).val ∈ M.O z) :
    ∃ a : Γ(M.Z, U)ˣ, M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = c := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).1)
    obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).2)
    have e : f * g = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, M.res_apply, M.res_apply, hf, hg, c.mul_inv])
    exact ⟨⟨f, g, e, (mul_comm _ _).trans e⟩, fun hp => Units.ext ((toFld_gm _ _ hp _).trans hf)⟩
  · exact ⟨1, fun hp => absurd ⟨_, hp⟩ hU⟩

variable {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] {M' : RatModel k Ω'}
  {π : M'.Z ⟶ M.Z}

theorem norm_mem_O [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) {W : M'.Z.Opens}
    (hW : π ⁻¹ᵁ U ≤ W) (f : Γ(M'.Z, W)) : Algebra.norm Ω (valF M'.pt W f) ∈ M.O z := by
  have hH : M.IsHom M' (IsScalarTower.toAlgHom k Ω Ω') π := hπ
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle' : π ⁻¹ᵁ V ≤ W := fun y hy => hW (hle hy)
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have hne' : ((π ⁻¹ᵁ V : M'.Z.Opens) : Set M'.Z).Nonempty := by
    refine ⟨M'.pt (IsLocalRing.closedPoint Ω'), ?_⟩
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ V
    rw [hπ]
    exact M.top_le_preimage_pt hne (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hfin : (π.app V).hom.Finite := IsFinite.finite_app π V hV
  have hint := hfin.to_isIntegral (resG M'.Z hle' f)
  let ρ : Γ(M.Z, V) →+* M.O z := (M.res V hne).codRestrict (M.O z) fun a => by
    rw [M.res_apply]; exact RatModel.valF_mem_O hzV a
  have hc : (algebraMap (M.O z) Ω').comp ρ = (M'.res _ hne').comp (π.app V).hom := by
    ext a
    show algebraMap Ω Ω' (M.res V hne a) = M'.res _ hne' (π.app V a)
    rw [M.res_apply, M'.res_apply, hH.valF_app hne]
    rfl
  have h1 : IsIntegral (M.O z) (valF M'.pt W f) := by
    obtain ⟨P, hP, hP0⟩ := hint
    refine ⟨P.map ρ, hP.map ρ, ?_⟩
    rw [Polynomial.eval₂_map, hc, ← M'.valF_resG hle' hne', ← M'.res_apply _ hne', ← Polynomial.hom_eval₂, hP0,
      map_zero]
  have := M.isIntegrallyClosed_O hN z
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm Ω h1)
  exact hy ▸ y.2

theorem lbIso_lbPow_finrank [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) (A B : LB M.Z) (e : ℕ)
    (H : LBIso (A.pull π) (B.pull π)) :
    LBIso (lbPow A (Module.finrank Ω Ω' * e)) (lbPow B (Module.finrank Ω Ω' * e)) := by
  obtain ⟨w, hw⟩ := H
  set d := Module.finrank Ω Ω' * e with hd
  let N : Ω'ˣ →* Ωˣ := Units.map (Algebra.norm Ω)
  have hNa : ∀ c : Ωˣ, N (Units.map (algebraMap Ω Ω').toMonoidHom c) = c ^ Module.finrank Ω Ω' := fun c =>
    Units.ext (Algebra.norm_algebraMap c.val)
  have hle : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), π ⁻¹ᵁ ((LB.div (lbPow B d) (lbPow A d)).U p) ≤
      (LB.div (B.pull π) (A.pull π)).U p := fun p y hy =>
    ⟨mem_pull.2 (mem_powChart.1 hy.1), mem_pull.2 (mem_powChart.1 hy.2)⟩
  have hpt : ∀ {U : M.Z.Opens}, M.pt (IsLocalRing.closedPoint Ω) ∈ U →
      π (M'.pt (IsLocalRing.closedPoint Ω')) ∈ U := fun {U} h => by
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ U
    rw [hπ]
    exact M.top_le_preimage_pt ⟨_, h⟩ (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hex : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), ∃ a : Γ(M.Z, (LB.div (lbPow B d) (lbPow A d)).U p)ˣ,
      M.pt (IsLocalRing.closedPoint Ω) ∈ (LB.div (lbPow B d) (lbPow A d)).U p →
      toFld Ω (gm M.pt _ _ a) = N (toFld Ω' (gm M'.pt _ _ (w.s p))) ^ e := fun p => by
    refine exists_unit _ fun z hz => ?_
    have hp := hle p (hpt (pt_mem ⟨z, hz⟩))
    have key : ∀ u : Γ(M'.Z, (LB.div (B.pull π) (A.pull π)).U p)ˣ,
        (N (toFld Ω' (gm M'.pt _ _ u)) ^ e).val ∈ M.O z := fun u => by
      rw [Units.val_pow_eq_pow_val]
      refine pow_mem ?_ e
      show Algebra.norm Ω (toFld Ω' (gm M'.pt _ _ u)).val ∈ _
      rw [toFld_gm _ _ hp]
      exact norm_mem_O hN hπ hz (hle p) _
    refine ⟨key _, ?_⟩
    rw [← inv_pow, ← map_inv, ← map_inv, ← map_inv]
    exact key _
  choose s hs using hex
  refine ⟨⟨s⟩, fun p q => unit_ext_pt fun hy => ?_⟩
  have hy' : M'.pt (IsLocalRing.closedPoint Ω') ∈ (LB.div (B.pull π) (A.pull π)).U p ⊓
      (LB.div (B.pull π) (A.pull π)).U q := ⟨hle p (hpt hy.1), hle q (hpt hy.2)⟩
  have e₁ := congrArg (gm M'.pt (IsLocalRing.closedPoint Ω') _) (hw p q)
  rw [gm_res _ _ _ hy', map_mul, gm_res _ _ _ hy'] at e₁
  replace e₁ := e₁.trans (congrArg (· * _) (gm_div (A.pull π) (B.pull π) _ _ p q hy'))
  rw [gm_pull_g B π _ _ _ _ hy'.1.1 hy'.2.1, gm_pull_g A π _ _ _ _ hy'.1.2 hy'.2.2, hπ] at e₁
  have e₂ := congrArg (fun u => N (toFld Ω' u) ^ e) e₁
  simp only [map_mul, map_inv] at e₂
  have hB : M.pt (IsLocalRing.closedPoint Ω) ∈ B.U (p.1 PUnit.unit) ⊓ B.U (q.1 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.1, mem_powChart.1 hy.2.1⟩
  have hA : M.pt (IsLocalRing.closedPoint Ω) ∈ A.U (p.2 PUnit.unit) ⊓ A.U (q.2 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.2, mem_powChart.1 hy.2.2⟩
  rw [toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hB, toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hA, hNa, hNa] at e₂
  rw [gm_res _ _ _ hy, map_mul, gm_res _ _ _ hy]
  refine Eq.trans ?_ (congrArg (fun u => toFld Ω (u * _)) (gm_div (lbPow A d) (lbPow B d) _ _ p q hy)).symm
  rw [gm_lbPow_g d _ _ _ _ hy.1.1 hy.2.1, gm_lbPow_g d _ _ _ _ hy.1.2 hy.2.2, map_mul, map_mul, map_inv, map_pow,
    map_pow, hs p hy.1, hs q hy.2, e₂, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]

theorem lbIso_lbPow_of_pull : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'] (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z) (A B : LB M.Z) (d : ℕ), Geo.Tor.IsNormalScheme M.Z → IsFinite π → M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt → A.IsLB → B.IsLB → Module.finrank Ω Ω' ∣ d → LBIso (A.pull π) (B.pull π) → LBIso (lbPow A d) (lbPow B d) := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ M' π A B d hN _ hπ _ _ ⟨e, he⟩ H
  subst he
  exact lbIso_lbPow_finrank hN hπ A B e H

end GlobalTheory.UMin.NormIso
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem log_cocycle_cohomologous : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by

  intro I _ g Λ _ F K a lg β ha hdw hsh hlgsh hlgadd e uu ℓ huu hℓ
  have hnil : ∀ T : K.Obj, IsNilDP T.δ := fun T ↦ by letI := T.ratAlg; exact isPDNilpotent_of_rat _ T.nil
  have hdp : ∀ {T T' : K.Obj} (ψ : T ⟶ T'), DividedPowers.IsDPMorphism T.δ T'.δ (ψ.φ : T.C →+* T'.C) := fun {T T'} ψ ↦ by
    letI := T'.ratAlg; exact isDPMorphism_of_rat T.δ T'.δ (ψ.φ : T.C →+* T'.C) ψ.mem
  have hw : ∀ (T T' : K.Obj) (φ : T ⟶ T'), ∃ n ∈ T'.J, dpExp T'.δ n =
      uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) := by
    intro T T' φ
    have hm : uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) - 1 ∈ T'.J := by
      have := T'.J.mul_mem_right (((e T')⁻¹ : (T'.C)ˣ) : T'.C) (huu T T' φ)
      convert this using 1
      rw [sub_mul, Units.mul_inv]
    obtain ⟨x, hx, hx'⟩ := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T'.C T'.J T'.δ (hnil T')).surjOn hm
    exact ⟨x, hx, hx'⟩
  choose n hnJ hn using hw
  refine ⟨fun T T' φ ↦ (n T T' φ - T'.ρ (lg φ.deg T'.k) : T'.C), ?_⟩
  intro T T' T'' φ ψ
  obtain ⟨hℓJ, hℓe⟩ := hℓ T T' T'' φ ψ
  have hce := close_exp T''.J T''.δ (hnil T'') _ _ (a φ.deg T'.k) (lg φ.deg T'.k) (hdw φ.deg T'.k) ψ.close
  have hxJ := ψ.close.sub_mem (lg φ.deg T'.k)
  simp only [RingHom.comp_apply, AlgHom.coe_toRingHom] at hce hxJ
  have hnat : ∀ c ∈ T'.J, ψ.φ (dpExp T'.δ c) = dpExp T''.δ (ψ.φ c) := fun c hc ↦
    (dpExp_add_and_natural _ _ _ _ T'.δ T''.δ (hnil T')).2 _ (hdp ψ) c hc
  have hadd := (dpExp_add_and_natural _ _ _ _ T''.δ T''.δ (hnil T'')).1
  have hQ : ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * ψ.φ (e T' : T'.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have haa : T''.ρ (a (φ ≫ ψ).deg T''.k) = T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) := by
    rw [Charts.comp_deg, hsh _ _ _ _ (Charts.Hom.le ψ), map_mul]
  have hn1 := hn T T'' (φ ≫ ψ)
  have hn2 := hn T T' φ
  have hn3 := hn T' T'' ψ
  rw [Charts.comp_φ, haa] at hn1
  set x := ψ.φ (T'.ρ (lg φ.deg T'.k)) - T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) with hx
  have key : dpExp T''.δ (ℓ T T' T'' φ ψ + n T T'' (φ ≫ ψ) + x) = dpExp T''.δ (ψ.φ (n T T' φ) + n T' T'' ψ) := by
    rw [hadd _ (T''.J.add_mem hℓJ (hnJ _ _ _)) _ hxJ, hadd _ hℓJ _ (hnJ _ _ _),
      hadd _ (ψ.mem _ (hnJ _ _ _)) _ (hnJ _ _ _), ← hnat _ (hnJ _ _ _), hn1, hn2, hn3]
    simp only [map_mul]
    linear_combination (ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) *
        (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hℓe
      - (ψ.φ (uu T T' φ) * ψ.φ (φ.φ (e T : T.C)) * ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * uu T' T'' ψ * ψ.φ (e T' : T'.C) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C)) * hce
      - (ψ.φ (uu T T' φ) * uu T' T'' ψ * ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hQ
  have hinj := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T''.C T''.J T''.δ (hnil T'')).injOn
    (T''.J.add_mem (T''.J.add_mem hℓJ (hnJ _ _ _)) hxJ) (T''.J.add_mem (ψ.mem _ (hnJ _ _ _)) (hnJ _ _ _)) key
  have hb : T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) = T''.ρ (lg φ.deg T''.k) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
    rw [hlgsh _ _ _ _ (Charts.Hom.le ψ), T''.ρ.map_add, T''.ρ_cst]
  show ℓ T T' T'' φ ψ = (ψ.φ (n T T' φ - T'.ρ (lg φ.deg T'.k)) - (n T T'' (φ ≫ ψ) - T''.ρ (lg (φ ≫ ψ).deg T''.k)) +
    (n T' T'' ψ - T''.ρ (lg ψ.deg T''.k))) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)
  rw [Charts.comp_deg, hlgadd, map_sub, T''.ρ.map_add]
  rw [hx, hb] at hinj
  linear_combination hinj

end GlobalTheory.AnPer
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.quotient_line_degree_le_of_triangular_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → (∀ (v : Place k F) (i : Fin r), g v i.succ 0 = 0) → admitted (fun v => (g v).submatrix Fin.succ Fin.succ) → ∀ b : ℝ, LinesLE g b → LinesLE (fun v => (g v).submatrix Fin.succ Fin.succ) (2 * b - (∑ᶠ v, ord v (g v 0 0) : ℤ)) := by
  first | exact @GlobalTheory.Nef.QuotLine.quot_line_le | exact GlobalTheory.Nef.QuotLine.quot_line_le | (intros; apply GlobalTheory.Nef.QuotLine.quot_line_le <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_etale_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G) (W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative], P f → (∀ (Z : Scheme.{0}) (π : Z ⟶ V), P π → ContCone R F ((bc (sch.map (π ≫ f ≫ r))).mapCone c)) → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F S I _ _ G c W V r f hE hS P _ _ hf hZ
  have hstep : ContCone R F ((bc (cechAug f ≫ sch.map r)).mapCone c) := by
    refine GlobalTheory.T.cohomologyContinuous_base_change_of_levels R F S (cech f) (cechAug f ≫ sch.map r) I G c (fun k => ?_)
    obtain ⟨Z, π, e, hP, he⟩ := GlobalTheory.EtC.cech_level_representable P V W f hf k
    refine ⟨Z, π ≫ f ≫ r, e, ?_, hZ Z π hP⟩
    rw [NatTrans.comp_app, ← Category.assoc, he]
    change yoneda.map (π ≫ f) ≫ yoneda.map r = _
    rw [← yoneda.map_comp, Category.assoc]
  refine (ContCone.iff_of_eqv R F I _ _ ((bc (cechAug f ≫ sch.map r)).mapCone c) ((bc (sch.map r)).mapCone c)
    (Functor.whiskerLeft G (bcMap (cechAug f) (sch.map r))) ((bcMap (cechAug f) (sch.map r)).app c.pt) (fun i => ?_)
    (fun i => GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS (G.obj i)) (GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS c.pt)).mp hstep
  exact ((bcMap (cechAug f) (sch.map r)).naturality (c.π.app i))

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.acycF_of_pi_sh' : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) → AcycF R (sp B) F := by
  first | exact @GlobalTheory.EtC.acycF_of_pi_sh | exact GlobalTheory.EtC.acycF_of_pi_sh | (intros; apply GlobalTheory.EtC.acycF_of_pi_sh <;> assumption)
end
