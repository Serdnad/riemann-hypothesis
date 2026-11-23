module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle042
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

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isLocallyNoetherian [IsNoetherianRing o] : IsLocallyNoetherian M.Z :=
  have := M.lft
  LocallyOfFiniteType.isLocallyNoetherian M.s

def ptOpen (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : Sp Ω ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι M.pt (by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hV))

theorem ptOpen_ι (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : M.ptOpen V hV ≫ V.ι = M.pt :=
  IsOpenImmersion.lift_fac _ _ _

def openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : RatModel o Ω :=
  haveI : Nonempty V.toScheme := ⟨⟨hV.some, hV.some_mem⟩⟩
  haveI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  { Z := V.toScheme
    s := V.ι ≫ M.s
    sep := have := M.sep; inferInstance
    lft := have := M.lft; inferInstance
    qc := have := M.qc; have := M.isLocallyNoetherian; inferInstance
    pt := M.ptOpen V hV
    pt_s := by rw [← Category.assoc, ptOpen_ι, M.pt_s]
    gen := by
      have h : ∀ w : Sp Ω, M.ptOpen V hV w = genericPoint V.toScheme := fun w => by
        apply V.ι.isOpenEmbedding.injective
        rw [genericPoint_eq_of_isOpenImmersion, ← M.pt_apply w, ← M.ptOpen_ι V hV]
        rfl
      exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, h (IsLocalRing.closedPoint Ω)⟩, by
        rintro _ ⟨w, rfl⟩
        exact h w⟩
    onto := fun x => by
      obtain ⟨U, f, hU, rfl⟩ := M.onto x
      obtain ⟨z, hz, hz'⟩ := M.nonempty_inf hU hV
      refine ⟨V.ι ⁻¹ᵁ U, V.ι.app U f, ⟨⟨z, hz'⟩, hz⟩, ?_⟩
      refine (valR_comp _ _ U f).symm.trans ?_
      rw [ptOpen_ι]
      rfl }

theorem isHom_openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) :
    M.IsHom (M.openPart V hV) (AlgHom.id o Ω) V.ι :=
  (M.ptOpen_ι V hV).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ M.pt) (Spec.map_id _).symm))

variable {M}

theorem IsHom.O_eq {N : RatModel o Ω} {j : N.Z ⟶ M.Z} (h : M.IsHom N (AlgHom.id o Ω) j) [IsOpenImmersion j]
    (z : N.Z) : N.O z = M.O (j z) := by
  refine le_antisymm ?_ fun x hx => h.map_mem_O hx
  rintro _ ⟨U, g, hz, rfl⟩
  have hz' : j z ∈ j ''ᵁ U := ⟨z, hz, rfl⟩
  refine ⟨j ''ᵁ U, (j.appIso U).inv g, hz', ?_⟩
  refine (h.valF_app ⟨_, hz'⟩ _).symm.trans ?_
  have e := congrArg (fun φ => φ.hom g) (j.appIso_inv_app U)
  refine (congrArg _ e).trans ?_
  exact N.valF_resG (j.preimage_image_eq U).le ⟨z, hz'⟩ g

variable (M)

structure GenTriv (H : LB M.Z) (d : H.ι → Ω) : Prop where
  ne : ∀ k, d k ≠ 0
  g_eq : ∀ k k', ((H.U k ⊓ H.U k' : M.Z.Opens) : Set M.Z).Nonempty →
    valF M.pt (H.U k ⊓ H.U k') (H.g k k' : Γ(M.Z, H.U k ⊓ H.U k')) = d k' / d k

def HasVal {H : LB M.Z} (d : H.ι → Ω) (σ : H.Sec) (x : Ω) : Prop :=
  ∀ k, (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) (σ.f k) = x / d k

def ProjChart {Ω' : Type} [Field Ω'] [Algebra o Ω'] (N : RatModel o Ω') (φ : Ω →ₐ[o] Ω') (q : N.Z ⟶ M.Z)
    (W : M.Z.Opens) {J : Type} (t : J → Ω') : Prop :=
  (∀ z', q z' ∈ W → ∃ i, N.Div t i z') ∧ ∀ i, t i ≠ 0 → ∃ U : N.Z.Opens, IsAffineOpen U ∧
    (U : Set N.Z) = {z' | q z' ∈ W ∧ N.Div t i z'} ∧
    N.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => t j / t i)

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH
namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem isIntegrallyClosed_stalk_of_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) {z : M.Z} (hz : z ∈ U)
    (h : ∀ x : Ω, IsIntegral (M.ringOn U) x → x ∈ M.ringOn U) :
    IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have : Nonempty U := ⟨⟨z, hz⟩⟩
  have : IsFractionRing (M.ringOn U) Ω := isFractionRing_ringOn hU hne
  have : IsIntegrallyClosed (M.ringOn U) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, h x hx⟩, rfl⟩
  have : IsIntegrallyClosed Γ(M.Z, U) := IsIntegrallyClosed.of_equiv (M.sectionsEquiv U hne).symm
  let _ := TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (⟨z, hz⟩ : U)
  have := hU.isLocalization_stalk ⟨z, hz⟩
  exact isIntegrallyClosed_of_isLocalization (M.Z.presheaf.stalk z) _
    (Ideal.primeCompl_le_nonZeroDivisors (hU.primeIdealOf ⟨z, hz⟩).asIdeal)

theorem IsNm.isNormalScheme {J : Type} {t : J → Ω} (h : M.IsNm t) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z := by
  obtain ⟨hd, hU⟩ := h
  have key : ∀ z : M.Z, IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
    intro z
    obtain ⟨i, hi⟩ := hd z
    obtain ⟨U, hUa, hUeq, hmem⟩ := hU i hi.1
    have hz : z ∈ (U : Set M.Z) := hUeq ▸ hi
    refine isIntegrallyClosed_stalk_of_ringOn hUa hz fun x hx => ?_
    set A := Algebra.adjoin o (Set.range fun j => t j / t i)
    have hle : A ≤ M.ringOn U := fun y hy => (hmem y).2 (isIntegral_algebraMap (x := (⟨y, hy⟩ : A)))
    let : Algebra A (M.ringOn U) := (Subalgebra.inclusion hle).toRingHom.toAlgebra
    have : IsScalarTower A (M.ringOn U) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.IsIntegral A (M.ringOn U) := ⟨fun y =>
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (M.ringOn U) Ω) Subtype.val_injective).1
        ((hmem y).1 y.2)⟩
    exact (hmem x).2 (isIntegral_trans x hx)
  exact fun z => ⟨(M.stalkHom_injective z).isDomain _, key z⟩

theorem div_prod_iff {J J' : Type} {t : J → Ω} {t' : J' → Ω} {i : J} {i' : J'} {z : M.Z} :
    M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hi : t i ≠ 0 := left_ne_zero_of_mul h0
    have hi' : t' i' ≠ 0 := right_ne_zero_of_mul h0
    refine ⟨⟨hi, fun j => ?_⟩, ⟨hi', fun j' => ?_⟩⟩
    · simpa [mul_div_mul_right _ _ hi'] using h (j, i')
    · simpa [mul_div_mul_left _ _ hi] using h (i, j')
  · rintro ⟨⟨hi, h⟩, ⟨hi', h'⟩⟩
    refine ⟨mul_ne_zero hi hi', fun q => ?_⟩
    rw [mul_div_mul_comm]
    exact mul_mem (h q.1) (h' q.2)

theorem div_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} {q : ∀ a, JJ a} {z : M.Z} :
    M.Div (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) q z ↔ ∀ a, M.Div (tt a) (q a) z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hne : ∀ a, tt a (q a) ≠ 0 := fun a => Finset.prod_ne_zero_iff.1 h0 a (Finset.mem_univ a)
    intro a
    refine ⟨hne a, fun j => ?_⟩
    have hj := h (Function.update q a j)
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single a] at hj
    · simpa using hj
    · intro b _ hb
      simp [Function.update_of_ne hb, div_self (hne b)]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · intro h
    refine ⟨Finset.prod_ne_zero_iff.2 fun a _ => (h a).1, fun q' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun a _ => (h a).2 (q' a)

theorem hasDiv_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} :
    M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a) := by
  simp only [RatModel.HasDiv]
  constructor
  · intro h a z
    obtain ⟨q, hq⟩ := h z
    exact ⟨q a, div_finprod_iff.1 hq a⟩
  · intro h z
    choose q hq using fun a => h a z
    exact ⟨q, div_finprod_iff.2 hq⟩

end RatModel

theorem isNm_normal_and_div_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) (t : J → Ω), (M.IsNm t → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) ∧ (∀ (J' : Type) (t' : J' → Ω) (i : J) (i' : J') (z : M.Z), M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z) ∧ (∀ (A : Type) [Fintype A] (JJ : A → Type) (tt : ∀ a, JJ a → Ω), M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a)) := by
  intro o Ω _ _ _ M J t
  exact ⟨fun h => h.isNormalScheme, fun J' t' i i' z => RatModel.div_prod_iff,
    fun A _ JJ tt => RatModel.hasDiv_finprod_iff⟩

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem isNm_of_isCl_veronese : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] (t : J → Ω) (e n : ℕ) (z : Fin (n + 1) → Ω), 1 ≤ e → M.IsCl z → (∀ i, ∃ k, z k = t i ^ e) → (∀ i, t i ≠ 0 → ∀ x, x ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ↔ IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) → (∀ k, z k ≠ 0 → ∃ c : J → Algebra.adjoin o (Set.range fun l => z l / z k), ∑ i, (c i : Ω) * (t i ^ e / z k) = 1) → M.IsNm t := by
  intro o Ω _ _ _ M J _ t e n z he hcl hk hint hsum
  choose κ hκ using hk
  have hle : ∀ k p, M.Div z k p → Algebra.adjoin o (Set.range fun l => z l / z k) ≤ M.O p :=
    fun k p h => Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact h.2 l)
  have hA : ∀ i p, M.Div z (κ i) p → M.Div t i p := by
    intro i p h
    have h0 : t i ≠ 0 := fun h0 => h.1 (by rw [hκ, h0, zero_pow (by omega)])
    refine ⟨h0, fun j => hle _ _ h ?_⟩
    rw [hκ, hint i h0]
    exact isIntegral_algebraMap (R := Algebra.adjoin o (Set.range fun j => t j / t i))
      (x := ⟨t j / t i, Algebra.subset_adjoin ⟨j, rfl⟩⟩)
  have hB : ∀ p, ∃ i, M.Div z (κ i) p := by
    intro p
    obtain ⟨k, hk⟩ := hcl.1 p
    obtain ⟨c, hc⟩ := hsum k hk.1
    have h1 : IsUnit (∑ i, (⟨c i, hle _ _ hk (c i).2⟩ : M.O p) * ⟨z (κ i) / z k, hk.2 _⟩) := by
      convert isUnit_one
      apply Subtype.ext
      simpa [hκ] using hc
    obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h1
    exact ⟨i, (hk.div_iff_isUnit _).2 (isUnit_of_mul_isUnit_right hi)⟩
  have hC : ∀ i p, M.Div t i p → M.Div z (κ i) p := by
    intro i p h
    obtain ⟨i', hi'⟩ := hB p
    have h0 : z (κ i) ≠ 0 := by rw [hκ]; exact pow_ne_zero _ h.1
    refine ⟨h0, fun l => ?_⟩
    have h1 := mul_mem (hi'.2 l) (pow_mem (h.2 i') e)
    rwa [div_pow, ← hκ, ← hκ, div_mul_div_cancel₀ hi'.1] at h1
  refine ⟨fun p => (hB p).imp fun i hi => hA i p hi, fun i hi => ?_⟩
  obtain ⟨U, hU, hD, hR⟩ := hcl.2 (κ i) (by rw [hκ]; exact pow_ne_zero _ hi)
  refine ⟨U, hU, hD.trans (Set.ext fun p => ⟨hA i p, hC i p⟩), fun x => ?_⟩
  rw [hR, hκ]
  exact hint i hi x

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

section

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_of_mul_pow_mem_of_inv_mem {S : Subalgebra o Ω} {d x : Ω} (hd : d ≠ 0) (hi : d⁻¹ ∈ S) {n : ℕ}
    (h : x * d ^ n ∈ S) : x ∈ S := by
  have := S.mul_mem h (S.pow_mem hi n)
  rwa [_root_.mul_assoc, ← mul_pow, mul_inv_cancel₀ hd, one_pow, _root_.mul_one] at this

theorem exists_mul_eq_of_eq_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (x : Ω) :
    ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  by_cases h0 : b = 0
  · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by simp [h0]⟩
  · exact ⟨a, ha, b, hb, h0, div_mul_cancel₀ a h0⟩

theorem exists_adjoin_inv_eq (R B : Subalgebra o Ω) (A : Set Ω) (hR : R.FG) (hB : B.FG)
    (hRf : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (hBf : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) (hA : A.Finite) :
    ∃ a ∈ R, ∃ c ∈ B, a ≠ 0 ∧ c ≠ 0 ∧
      Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧
      A ⊆ Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) := by
  obtain ⟨d, hdR, hd0, hd⟩ := exists_mul_pow_mem_of_fg (B ⊔ Algebra.adjoin o A) R
    (hB.sup (Subalgebra.fg_def.2 ⟨_, hA, rfl⟩)) hRf
  obtain ⟨c, hcB, hc0, hc⟩ := exists_mul_pow_mem_of_fg (R ⊔ Algebra.adjoin o {d⁻¹}) B
    (hR.sup (Subalgebra.fg_def.2 ⟨_, Set.finite_singleton _, rfl⟩)) hBf
  obtain ⟨m, hm⟩ := hd c (le_sup_left (a := B) hcB)
  have ha0 : d * (c * d ^ m) ≠ 0 := mul_ne_zero hd0 (mul_ne_zero hc0 (pow_ne_zero _ hd0))
  set S := Algebra.adjoin o (insert (d * (c * d ^ m))⁻¹ (R : Set Ω)) with hS
  set S' := Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) with hS'
  have hRS : ∀ x ∈ R, x ∈ S := fun x hx => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have haS : (d * (c * d ^ m))⁻¹ ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hdS : d⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ hm)
    convert this using 1
    field_simp
  have hcS : c⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ (R.mul_mem hdR (R.pow_mem hdR m)))
    convert this using 1
    field_simp
  have h1 : ∀ x ∈ B ⊔ Algebra.adjoin o A, x ∈ S := fun x hx => by
    obtain ⟨n, hn⟩ := hd x hx
    exact mem_of_mul_pow_mem_of_inv_mem hd0 hdS (hRS _ hn)
  have hcS' : c⁻¹ ∈ S' := Algebra.subset_adjoin (Set.mem_insert _ _)
  have h2 : ∀ x ∈ R ⊔ Algebra.adjoin o {d⁻¹}, x ∈ S' := fun x hx => by
    obtain ⟨n, hn⟩ := hc x hx
    exact mem_of_mul_pow_mem_of_inv_mem hc0 hcS' (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hn))
  have hdS' : d⁻¹ ∈ S' := h2 _ (le_sup_right (a := R) (Algebra.subset_adjoin (Set.mem_singleton _)))
  refine ⟨_, R.mul_mem hdR hm, c, hcB, ha0, hc0, le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_),
    fun x hx => h1 x (le_sup_right (a := B) (Algebra.subset_adjoin hx))⟩
  · rintro x (rfl | hx)
    · exact hcS
    · exact h1 x (le_sup_left (a := B) hx)
  · rintro x (rfl | hx)
    · have := S'.mul_mem hdS' (S'.mul_mem hcS' (S'.pow_mem hdS' m))
      rwa [inv_pow, ← mul_inv, ← mul_inv] at this
    · exact h2 x (le_sup_left (a := R) hx)

namespace RatModel

variable {M : RatModel o Ω}

theorem fg_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) :
    (M.ringOn V).FG := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ V le_top).hom.FiniteType := M.s.finiteType_appLE (isAffineOpen_top _) hV _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (M.sectionsEquiv V hne).toRingHom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (M.sectionsEquiv V hne).surjective
  have h4 := h3.comp (h1.comp h2)
  have e : (M.sectionsEquiv V hne).toRingHom.comp ((M.s.appLE ⊤ V le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom) = algebraMap o (M.ringOn V) :=
    RingHom.ext fun a => Subtype.ext ((coe_sectionsEquiv V hne _).trans (M.valF_constFn hne a))
  rw [e, RingHom.finiteType_algebraMap] at h4
  exact (Subalgebra.fg_iff_finiteType _).2 h4

theorem nonempty_basicOpen {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg : valF M.pt V g ≠ 0) : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  apply hg
  rw [(basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h), ← M.res_apply V hne, map_zero]

theorem ringOn_basicOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg0 : valF M.pt V g ≠ 0) :
    M.ringOn (M.Z.basicOpen g) = Algebra.adjoin o (insert (valF M.pt V g)⁻¹ (M.ringOn V : Set Ω)) := by
  have hg := nonempty_basicOpen hne hg0
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg).1 hx
    have := hV.isLocalization_basicOpen g
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
    have h1 := congrArg (M.res _ hg) ha
    have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
      fun t => M.res_resG (M.Z.basicOpen_le g) hg t
    rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
    refine mem_of_mul_pow_mem_of_inv_mem hg0 (Algebra.subset_adjoin (Set.mem_insert _ _)) (n := n) ?_
    rw [h1]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ((mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
  · rintro x (rfl | hx)
    · exact mem_ringOn.2 fun z hz =>
        ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2
    · exact ringOn_anti (M.Z.basicOpen_le g) hx

end RatModel

end

theorem exists_affineOpen_ringOn_eq_adjoin_inv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (R : Subalgebra o Ω) (A : Set Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → A.Finite → ∀ W : M.Z.Opens, (W : Set M.Z).Nonempty → ∃ (U₀ : M.Z.Opens) (a : Ω), U₀ ≤ W ∧ (U₀ : Set M.Z).Nonempty ∧ IsAffineOpen U₀ ∧ a ∈ R ∧ a ≠ 0 ∧ M.ringOn U₀ = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧ A ⊆ M.ringOn U₀ := by
  intro o Ω _ _ _ M R A hR hRf hA W ⟨w, hw⟩
  obtain ⟨V, hV, hwV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := W) hw
  have hne : (V : Set M.Z).Nonempty := ⟨w, hwV⟩
  obtain ⟨a, ha, c, hc, ha0, hc0, he, hAS⟩ := exists_adjoin_inv_eq R (M.ringOn V) A hR
    (RatModel.fg_ringOn hV hne) (exists_mul_eq_of_eq_div hRf) (exists_mul_eq_of_eq_div fun x => by
      obtain ⟨a, b, -, h⟩ := RatModel.exists_eq_div hV hne x
      exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _,
        (RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩, h⟩) hA
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hc
  have h := (RatModel.ringOn_basicOpen hV hne hc0).trans he
  exact ⟨M.Z.basicOpen g, a, (M.Z.basicOpen_le g).trans hVW, RatModel.nonempty_basicOpen hne hc0,
    hV.basicOpen g, ha, ha0, h, h ▸ hAS⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_point_of_ringHom {o Ω K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] (M : RatModel o Ω)
    {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) (φ : M.ringOn U →+* K) :
    ∃ x : Sp K ⟶ M.Z, Set.range x ⊆ U ∧ (∀ a : M.ringOn U, φ a = M.val x a) ∧
      x ≫ M.s = spMap (φ.comp (algebraMap o _)) := by
  let ψ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (φ.comp (M.sectionsEquiv U hne).toRingHom)
  have hx := le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, valR (Spec.map ψ ≫ hU.fromSpec) U f = φ (M.sectionsEquiv U hne f) := fun f => by
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hr := (top_le_preimage_iff _ _).1 hx
  refine ⟨Spec.map ψ ≫ hU.fromSpec, hr, fun a => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := (M.sectionsEquiv U hne).surjective a
    rw [coe_sectionsEquiv, val_valF hr]
    exact (hv f).symm
  · rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← valR_constFn M.s _ U hx, hv]
    exact congrArg φ (Subtype.ext ((coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b)))

theorem exists_cen_of_ringHom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens), IsProper M.s → IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime]
    (y' : M.ringOn U →+* PadicAlgCl p), (∀ b : o, ‖y' (algebraMap o _ b)‖ ≤ 1) →
    ∃ (z : M.Z) (y : Sp (OO p) ⟶ M.Z), M.Cen U z y ∧ ∀ a : M.ringOn U, y' a = M.val (gPt p ≫ y) a := by
  intro o Ω _ _ _ M U hs hU hne p _ y' hy'
  obtain ⟨x, hx, hv, hxs⟩ := M.exists_point_of_ringHom hU hne y'
  let σ : o →+* OO p := (y'.comp (algebraMap o _)).codRestrict (OO p).toSubring
    fun b => (mem_OO_iff _).2 (hy' b)
  obtain ⟨y, hy, -⟩ := exists_valuativeExtension (V := OO p) (K := PadicAlgCl p) M.s (spMap σ) x (by
    rw [hxs, ← Spec.map_comp]
    rfl)
  have hy2 : gPt p ≫ y = x := hy
  exact ⟨_, y, ⟨rfl, hy2 ▸ hx⟩, hy2 ▸ hv⟩

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.lineBundleIso_extend_of_normal_base : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → ∀ (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → ∀ (L M : LB H), L.IsLB → M.IsLB → LBIso (L.pull jH) (M.pull jH) → (LBIso (L.pull e) (M.pull e) → LBIso L M) ∧ ∀ s : S, ∃ N : S.Opens, s ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι) := by
  first | exact @GlobalTheory.lbIso_extend_of_normal | exact GlobalTheory.lbIso_extend_of_normal | (intros; apply GlobalTheory.lbIso_extend_of_normal <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.groupScheme_model_finite_ring_extension : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  first | exact @GlobalTheory.SS.model_finite_ext | exact GlobalTheory.SS.model_finite_ext | (intros; apply GlobalTheory.SS.model_finite_ext <;> assumption)
end
