module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.HopLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) {g : G} (h : g ∈ H) : toSub H g = ⟨g, h⟩ := by
  unfold toSub; rw [dif_pos h]

def comp (hU : Unr E) (n : ℕ) (w : Pl E) : finU (E := E) (n := n) →* UL n w :=
  ((cLoc w).comp (finU (E := E) (n := n)).subtype).codRestrict (UL n w) (fun x => cLoc_mem_UL E hU n w x)

theorem comp_eq (hU : Unr E) (w : Pl E) (x : finU (E := E) (n := n)) :
    comp hU n w x = toSub (UL n w) (cLoc w (x : UA E n)) :=
  (toSub_of_mem _ (cLoc_mem_UL E hU n w x)).symm

theorem mem_globLev (hU : Unr E) (S : Set (Pl E)) (L : ∀ w : Pl E, Subgroup (UL n w)) (x : finU (E := E) (n := n)) :
    x ∈ globLev S L ↔ ∀ w ∈ S, comp hU n w x ∈ L w := by
  unfold globLev
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]
  refine forall_congr' fun w => forall_congr' fun _ => ⟨fun ⟨k, hk, e⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  have : k = comp hU n w x := Subtype.ext e
  rwa [← this]

theorem globFn_indicator (hU : Unr E) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (hK : ∀ᶠ w in cofinite, K' w = KL n w) (x : finU (E := E) (n := n)) :
    globFn S (fun w => (K' w : Set (UL n w)).indicator 1) x = if x ∈ globLev S K' then 1 else 0 := by
  unfold globFn
  simp_rw [← comp_eq hU]
  by_cases hx : x ∈ globLev S K'
  · rw [if_pos hx]
    refine finprod_mem_of_eqOn_one fun w hw => ?_
    rw [Set.indicator_of_mem ((mem_globLev hU S K' x).1 hx w hw)]
    rfl
  · rw [if_neg hx, finprod_mem_def]
    obtain ⟨w₀, hw₀, hn⟩ : ∃ w ∈ S, comp hU n w x ∉ K' w := by
      by_contra h; push_neg at h; exact hx ((mem_globLev hU S K' x).2 h)
    refine finprod_eq_zero _ w₀ ?_ ?_
    · rw [Set.mulIndicator_of_mem hw₀, Set.indicator_of_notMem hn]
    · have h1 := Filter.eventually_cofinite.1 hK
      have h2 := Filter.eventually_cofinite.1 (LocAE.eventually_mem_KL E hU n x)
      refine (h1.union h2).subset fun w hw => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
      apply hw
      rw [Set.mulIndicator_apply]
      split_ifs
      · rw [Set.indicator_of_mem]
        · rfl
        · rw [hc.1, comp_eq hU]; exact hc.2
      · rfl

end GlobalTheory.BCT.HopLev

noncomputable section

namespace GlobalTheory.BCT.HopLev2

open GlobalTheory.BCT.HopLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod {ι : Type} [Fintype ι] {G : Type} [Group G] {M : ι → Type} [∀ i, Group (M i)]
    (φ : G →* ((i : ι) → M i)) (Up U : Subgroup G) (K H : ∀ i, Subgroup (M i))
    (hK : ∀ g ∈ Up, ∀ i, φ g i ∈ K i) (hs : ∀ x : (i : ι) → M i, (∀ i, x i ∈ K i) → ∃ g ∈ Up, φ g = x)
    (hU : ∀ g, g ∈ U ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i) : U.relIndex Up = ∏ i, (H i).relIndex (K i) := by
  let ψ : Up →* ((i : ι) → K i) :=
    { toFun := fun g i => ⟨φ g.1 i, hK g.1 g.2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg, e⟩ := hs (fun i => (x i).1) (fun i => (x i).2)
    exact ⟨⟨g, hg⟩, by ext i; simp [ψ, e]⟩
  have e : U.subgroupOf Up = (Subgroup.pi Set.univ fun i => (H i).subgroupOf (K i)).comap ψ := by
    ext g
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_pi, hU, g.2, ψ]
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ hψ, index_pi_univ]
  rfl

theorem relIndex_globLev (hU : Unr E) (S : Set (Pl E)) (hS : IsSection S) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (hle : ∀ w, K' w ≤ KL n w) (hK : ∀ᶠ w in cofinite, K' w = KL n w) :
    (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ) = ∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ) := by
  have hfin := Filter.eventually_cofinite.1 hK
  obtain ⟨T, hTS, hnT⟩ : ∃ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) ∧ ∀ w ∈ S, w ∉ T → K' w = KL n w :=
    ⟨hfin.toFinset.filter (· ∈ S), fun w hw => (Finset.mem_filter.1 hw).2, fun w hw h => by
      by_contra hc
      exact h (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hc, hw⟩)⟩
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq _ (t := T)]
  · rw [← Finset.prod_coe_sort T]
    rw [relIndex_eq_prod (MonoidHom.pi fun i : T => comp hU n i.1) (globLev S (KL n)) (globLev S K')
      (fun i => KL n i.1) (fun i => K' i.1)]
    · push_cast; rfl
    · intro g hg i
      exact (mem_globLev hU S (KL n) g).1 hg i.1 (hTS _ i.2)
    · intro x hx
      obtain ⟨y, hyT, hyn⟩ : ∃ y : ∀ w : Pl E, UL n w, (∀ i : T, y i.1 = x i) ∧ ∀ w, w ∉ T → y w = 1 :=
        ⟨fun w => if h : w ∈ T then x ⟨w, h⟩ else 1, fun i => dif_pos i.2, fun w h => dif_neg h⟩
      have hy : ∀ w, y w ∈ KL n w := fun w => by
        by_cases h : w ∈ T
        · have := hx ⟨w, h⟩
          rw [hyT ⟨w, h⟩]
          exact this
        · rw [hyn w h]; exact one_mem _
      obtain ⟨g, hg⟩ := exists_finU_of_loc E hU n S hS y (Filter.Eventually.of_forall hy)
      have hg' : ∀ w ∈ S, comp hU n w g = y w := fun w hw => by rw [comp_eq]; exact hg w hw
      refine ⟨g, (mem_globLev hU S (KL n) g).2 fun w hw => by rw [hg' w hw]; exact hy w, ?_⟩
      funext i
      show comp hU n i.1 g = x i
      rw [hg' i.1 (hTS _ i.2)]
      exact hyT i
    · intro g
      rw [mem_globLev hU S K' g, mem_globLev hU S (KL n) g]
      refine ⟨fun h => ⟨fun w hw => hle w (h w hw), fun i => h i.1 (hTS _ i.2)⟩, fun ⟨h1, h2⟩ w hw => ?_⟩
      by_cases hwT : w ∈ T
      · exact h2 ⟨w, hwT⟩
      · rw [hnT w hw hwT]; exact h1 w hw
  · ext w
    simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe]
    refine ⟨fun ⟨hw, h⟩ => ⟨?_, h⟩, fun ⟨hw, h⟩ => ⟨hTS w hw, h⟩⟩
    by_contra hwT
    apply h
    rw [hnT w hw hwT, Subgroup.relIndex_self]
    simp

end GlobalTheory.BCT.HopLev2


open GlobalTheory.BCT.HopLev GlobalTheory.BCT.HopLev2 in
theorem GlobalTheory.BCT.hop_indicator_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ φ ∈ fixed (RF E n) (globLev S K'),
    hop S K' (fun w => (K' w : Set (UL n w)).indicator 1) φ = (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ • φ := by
  intro E _ _ _ hU n _ S hS K' hK φ hφ
  rw [← relIndex_globLev hU S hS K' (fun w => (hK.1 w).2.1) hK.2]
  unfold hop levOp
  rw [LinearMap.smul_apply]
  congr 1
  set H := globLev S K'
  have hq : ∀ q : finU (E := E) (n := n) ⧸ H, q ≠ ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H) → Quotient.out q ∉ H := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q, QuotientGroup.eq]
    simpa using hm
  have h1 : Quotient.out ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H) ∈ H := by
    have := QuotientGroup.out_eq' ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H)
    rw [QuotientGroup.eq] at this
    simpa using this
  rw [finsum_eq_single _ ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H)]
  · rw [globFn_indicator hU S K' hK.2, if_pos h1, one_smul, LinearMap.comp_id]
    have := hφ ⟨_, h1⟩
    simpa using this
  · intro q hne
    rw [globFn_indicator hU S K' hK.2, if_neg (hq q hne), zero_smul]
end
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder Matrix.Norms.L2Operator

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dite_eq_left (map_mem_UL hU w γ)]

theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 := by
  let A : Matrix (Fin n) (Fin n) ℂ := (γ.1 : GL (Fin n) E).val.map τ
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom
      (γ.1 : GL (Fin n) E).val * (γ.1 : GL (Fin n) E).val = 1 := by
    have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom
        (γ.1 : GL (Fin n) E).val * 1 * (γ.1 : GL (Fin n) E).val = 1 := γ.2
    simpa only [Matrix.mul_one] using h
  have hstar : star A * A = 1 := by
    have hm := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map τ) hγ
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at hm
    convert hm using 1
    apply congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M * A)
    ext i j
    simp [A, cT, IsCMField.complexEmbedding_complexConj]
  have hu : A ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    apply IsUnit.mem_unitary_of_star_mul_self _ hstar
    exact ⟨GeneralLinearGroup.map τ γ.1, rfl⟩
  apply spectrum.norm_eq_one_of_unitary hu
  apply Matrix.mem_spectrum_of_isRoot_charpoly
  apply Polynomial.isRoot_of_mem_roots
  simpa [A, Matrix.charpoly_map] using hz

theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses

def gramOn {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (V : Submodule K (Fin n → K)) :
    Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
  Matrix.of fun i j => hform σ H (Module.finBasis K V i).1 (Module.finBasis K V j).1

def sgnOn {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (Q : K[X]) (A : Matrix (Fin n) (Fin n) K) : ℂ :=
  (-1) ^ ordL (gramOn σ H (LinearMap.ker (Matrix.toLin' (aeval A Q)))).det

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Gen
variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ}

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) K) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cT_units (k : GL (Fin n) K) : cT σ (k⁻¹).val * cT σ k.val = 1 := by
  rw [← cT_mul, Units.mul_inv, cT_one]

theorem cT_units' (k : GL (Fin n) K) : cT σ k.val * cT σ (k⁻¹).val = 1 := by
  rw [← cT_mul, Units.inv_mul, cT_one]

theorem cT_units_left (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ (k⁻¹).val * (cT σ k.val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units, Matrix.one_mul]

theorem cT_units_left' (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units', Matrix.one_mul]

theorem herm_of (hσ : ∀ x, σ (σ x) = x) (k : GL (Fin n) K) : IsHerm σ (cT σ (k⁻¹).val * (k⁻¹).val) := by
  unfold IsHerm; rw [cT_mul, cT_cT σ hσ]

theorem det_ne (k : GL (Fin n) K) : (cT σ (k⁻¹).val * (k⁻¹).val).det ≠ 0 := by
  have h1 : ((k⁻¹).val).det ≠ 0 := ((k⁻¹).isUnit.map Matrix.detMonoidHom).ne_zero
  have h2 : (cT σ (k⁻¹).val).det = σ ((k⁻¹).val).det := by
    unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [Matrix.det_mul, h2]
  exact mul_ne_zero ((map_ne_zero σ).2 h1) h1

theorem one_of (k : GL (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * (k⁻¹).val) * k.val = 1 := by
  simp only [Matrix.mul_assoc, cT_units_left', Units.inv_mul]

theorem inv_of_unit (k a : GL (Fin n) K) (hy : cT σ (k⁻¹ * a * k).val * 1 * (k⁻¹ * a * k).val = 1) :
    cT σ a.val * (cT σ (k⁻¹).val * (k⁻¹).val) * a.val = cT σ (k⁻¹).val * (k⁻¹).val := by
  have ha : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
  rw [ha]
  generalize k⁻¹ * a * k = y at hy ⊢
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one] at hy ⊢
  simp only [cT_units_left', Units.inv_mul_cancel_left]
  rw [← Matrix.mul_assoc (cT σ y.val), hy, Matrix.one_mul]

theorem unit_of_form (γ₀ h : GL (Fin n) K) (hinv : cT σ γ₀.val * (cT σ h.val * h.val) * γ₀.val = cT σ h.val * h.val) :
    cT σ (h * γ₀ * h⁻¹).val * 1 * (h * γ₀ * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) hinv
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

theorem unit_of_two (k c h : GL (Fin n) K) (H' : Matrix (Fin n) (Fin n) K)
    (h1 : H' = cT σ c.val * (cT σ (k⁻¹).val * (k⁻¹).val) * c.val) (h2 : H' = cT σ h.val * h.val) :
    cT σ (k⁻¹ * c * h⁻¹).val * 1 * (k⁻¹ * c * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) (h1.symm.trans h2)
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

end Gen

theorem cT_map (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (algebraMap E (w.adicCompletion E)) =
      cT (cj w) (M.map (algebraMap E (w.adicCompletion E))) := by
  have h := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hw).1
  ext i j; simp [cT, h]

theorem locPt_val (hU : Unr E) {n : ℕ} (w : Pl E) (γ : UE E n) :
    ((locPt w γ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  have hm : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
    unfold UL
    split_ifs with hs
    · trivial
    · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 * γ.1 = 1 := γ.2
      show cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val *
        (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = 1
      have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hγ
      simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hs] at this
      simpa using this
  unfold locPt toSub
  rw [dite_eq_left hm]

theorem aeval_map_mat {n : ℕ} (w : Pl E) (M : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    aeval (M.map (algebraMap E (w.adicCompletion E))) (atPl w p) = (aeval M p).map (algebraMap E (w.adicCompletion E)) := by
  rw [atPl, aeval_map_algebraMap]
  have := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E (w.adicCompletion E))) M p
  have e : (⇑(Algebra.ofId E (w.adicCompletion E)) : E → _) = algebraMap E _ := rfl
  simpa [AlgHom.mapMatrix_apply, e] using this

theorem kapSign_eq {n : ℕ} (w : Pl E) (hw : ¬ IsSplitAt w) (Q : (w.adicCompletion E)[X]) (γ : GLw n w) :
    kapSign n w Q γ = sgnOn (cj w) 1 Q γ.val := by
  unfold kapSign sgnOn gramOn hform
  rw [if_neg hw]
  simp [Matrix.one_apply]

theorem mem_S {S : Set (Pl E)} (hS : IsSection S) {w : Pl E} (hw : ¬ IsSplitAt w) : w ∈ S := by
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
  by_contra h
  exact hw ⟨u, fun e => h (e ▸ hu), hu'⟩

end GlobalTheory.UnitaryClasses
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_block_levels_twistedConstantTerm_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w)) (K'' : Subgroup (GLw n w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧ IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧ ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) → K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧ IsOpen (K'' : Set (GLw n w)) ∧ K'' ≤ K'.map (UL n w).subtype ∧ (K''.subgroupOf (GlobalTheory.LFun.KGL w (n := n))).Normal ∧ (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, blk (Nat.add_sub_cancel' ha) w (m₁, m₂) 0 ∈ K'') ∧ (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, μ (GeneralLinearGroup.det m₁ ^ (n - a) * GeneralLinearGroup.det m₂ ^ a) = 1) ∧ ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
  first | exact @GlobalTheory.BCT.SplitLevels.levels_split | exact GlobalTheory.BCT.SplitLevels.levels_split | (intros; apply GlobalTheory.BCT.SplitLevels.levels_split <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  first | exact @GlobalTheory.BCT.FinPart.finPt_props | exact GlobalTheory.BCT.FinPart.finPt_props | (intros; apply GlobalTheory.BCT.FinPart.finPt_props <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.choose_mul_intersectionNumber_le_sectionDim : ∀ (k : Type) [Field k] [Infinite k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (N : ℕ) (b : Fin N → L.Sec), (∀ y : Y, ∃ i, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i)) → ∀ (d : ℕ) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ d → ∀ (j₀ : ℤ), VanishFrom L F j₀ → ∀ m : ℕ, (m.choose d : ℤ) * GlobalTheory.interNum k F (fun _ : Fin d => L) ≤ GlobalTheory.hdim k (GlobalTheory.twistZ F L (j₀ + m)) 0 := by
  first | exact @GlobalTheory.HSCore.choose_mul_interNum_le_hdim | exact GlobalTheory.HSCore.choose_mul_interNum_le_hdim | (intros; apply GlobalTheory.HSCore.choose_mul_interNum_le_hdim <;> assumption)
end
