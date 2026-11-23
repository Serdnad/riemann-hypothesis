module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Continuity
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.GradedAlgebra.Radical
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace FiltrationStepHilb

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem finiteDimensional_piece (n : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) n) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have hfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = n}.Finite := by
    refine (Finsupp.finite_of_nat_weight_eq (fun _ => (1 : ℕ)) (fun _ => one_ne_zero)
      (∑ k, n k)).subset ?_
    intro d hd
    simp only [Set.mem_ofPred_eq] at hd ⊢
    rw [← hd]
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWeight, smul_eq_mul,
      mul_one]
    rw [Finset.sum_comm]
    simp [Pi.single_apply]
  have := hfin.to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = n})


open Classical in
theorem component_mul {f : MRing ι F} {s : K → ℕ} (hf : IsMultiHomog f s) (c : MRing ι F)
    (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (f * c) =
      if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c else 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := c) n hf
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact h


open Classical in
theorem mem_sup_span {L : Ideal (MRing ι F)} {f : MRing ι F} {s : K → ℕ}
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) {n : K → ℕ} {x : MRing ι F}
    (hx : x ∈ weightedHomogeneousSubmodule F (blockWeight ι) n) (hx' : x ∈ L ⊔ Ideal.span {f}) :
    ∃ c : MRing ι F, x - (if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c
      else 0) ∈ L := by
  obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨c, ?_⟩
  have hx2 := weightedHomogeneousComponent_eq_self
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hx)
  rw [← hx2, map_add (f := _), mul_comm c f, component_mul hf, add_sub_cancel_right]
  exact hL l hl n


open Classical in
theorem finrank_step (L : Ideal (MRing ι F)) (f : MRing ι F) (s : K → ℕ)
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) (n : K → ℕ) :
    Module.finrank F (gradedPiece L n) =
      Module.finrank F (gradedPiece (L ⊔ Ideal.span {f}) n) +
        if s ≤ n then Module.finrank F (gradedPiece (L.colon {f}) (n - s)) else 0 := by
  have : ∀ d : K → ℕ, FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) d) :=
    fun d => finiteDimensional_piece d
  have : FiniteDimensional F (gradedPiece L n) := by unfold gradedPiece; infer_instance
  let q := (Ideal.Quotient.factorₐ F (le_sup_left : L ≤ L ⊔ Ideal.span {f})).toLinearMap
  let g := q.domRestrict (gradedPiece L n)
  have hrange : LinearMap.range g = gradedPiece (L ⊔ Ideal.span {f}) n := by
    rw [LinearMap.range_domRestrict]
    unfold gradedPiece
    rw [← Submodule.map_comp]
    rfl
  have hker_mem : ∀ a : gradedPiece L n, g a = 0 → ∃ c : MRing ι F,
      (a : MRing ι F ⧸ L) = Ideal.Quotient.mk L
        (if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c else 0) := by
    rintro ⟨a, ha⟩ hga
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    have hx0 : Ideal.Quotient.mk (L ⊔ Ideal.span {f}) x = 0 := hga
    obtain ⟨c, hc⟩ := mem_sup_span hL hf hx (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
    exact ⟨c, Ideal.Quotient.eq.mpr hc⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange] at h1
  by_cases hsn : s ≤ n
  · let T := weightedHomogeneousSubmodule F (blockWeight ι) (n - s)
    have hmem : ∀ y : T, ((Ideal.Quotient.mkₐ F L).toLinearMap ∘ₗ LinearMap.mulLeft F f ∘ₗ
        T.subtype) y ∈ gradedPiece L n := fun y => by
      refine Submodule.mem_map_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_)
      have := IsWeightedHomogeneous.mul hf y.2
      rwa [add_tsub_cancel_of_le hsn] at this
    let μ := LinearMap.codRestrict (gradedPiece L n) ((Ideal.Quotient.mkₐ F L).toLinearMap ∘ₗ
      LinearMap.mulLeft F f ∘ₗ T.subtype) hmem
    let ν := (Ideal.Quotient.mkₐ F (L.colon {f})).toLinearMap.domRestrict T
    have hν : LinearMap.range ν = gradedPiece (L.colon {f}) (n - s) :=
      LinearMap.range_domRestrict _ _
    have hker : LinearMap.ker μ = LinearMap.ker ν := by
      ext y
      simp only [LinearMap.mem_ker]
      rw [← Subtype.coe_inj]
      change Ideal.Quotient.mk L (f * (y : MRing ι F)) = 0 ↔
        Ideal.Quotient.mk (L.colon {f}) (y : MRing ι F) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
        Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
    have hμg : LinearMap.range μ = LinearMap.ker g := by
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        change Ideal.Quotient.mk (L ⊔ Ideal.span {f}) (f * (y : MRing ι F)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨y, mul_comm _ _⟩)
      · intro a ha
        obtain ⟨c, hc⟩ := hker_mem a ha
        rw [if_pos hsn] at hc
        exact ⟨⟨_, weightedHomogeneousComponent_mem _ c (n - s)⟩, Subtype.ext hc.symm⟩
    have h2 := LinearMap.finrank_range_add_finrank_ker μ
    have h3 := LinearMap.finrank_range_add_finrank_ker ν
    rw [hker] at h2
    have e : Module.finrank F (LinearMap.range μ) = Module.finrank F (LinearMap.range ν) :=
      Nat.add_right_cancel (h2.trans h3.symm)
    rw [hμg, hν] at e
    rw [if_pos hsn, ← e]
    exact h1.symm
  · have hk : LinearMap.ker g = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro a ha
      obtain ⟨c, hc⟩ := hker_mem a ha
      rw [if_neg hsn, map_zero] at hc
      exact Subtype.ext hc
    rw [hk, finrank_bot] at h1
    rw [if_neg hsn]
    omega

end FiltrationStepHilb

theorem FiltrationStepHilb.proof : FiltrationStepHilb.Statement.{u} := by
  intro F _ K _ _ ι _ L f s hL hf m
  by_cases hm : ∀ k, 0 ≤ m k
  · have key := FiltrationStepHilb.finrank_step L f s hL hf (fun k => (m k).toNat)
    have hms : (∀ k, 0 ≤ (m - fun k => (s k : ℤ)) k) ↔ s ≤ fun k => (m k).toNat := by
      constructor
      · intro h k
        have h1 := h k
        have h2 := hm k
        simp only [Pi.sub_apply] at h1
        show s k ≤ (m k).toNat
        omega
      · intro h k
        have h1 := h k
        have h2 := hm k
        simp only [Pi.sub_apply]
        change s k ≤ (m k).toNat at h1
        omega
    unfold hilbFn
    rw [if_pos hm, if_pos hm]
    by_cases hsn : s ≤ fun k => (m k).toNat
    · have hn : (fun k => ((m - fun k => (s k : ℤ)) k).toNat) = (fun k => (m k).toNat) - s := by
        funext k
        have h1 := hsn k
        have h2 := hm k
        change s k ≤ (m k).toNat at h1
        simp only [Pi.sub_apply]
        omega
      rw [if_pos (hms.mpr hsn), hn, key, if_pos hsn]
      push_cast
      rfl
    · rw [if_neg (fun h => hsn (hms.mp h)), key, if_neg hsn]
      simp
  · have hm' : ¬ ∀ k, 0 ≤ (m - fun k => (s k : ℤ)) k := fun h => hm fun k => by
      have h1 := h k
      simp only [Pi.sub_apply] at h1
      omega
    unfold hilbFn
    simp only [if_neg hm, if_neg hm']
    simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DimStrictDrop.proof : DimStrictDrop.Statement.{u} := by
  intro A _ Q Q' _ _ hlt
  let q : PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    ⟨⟨Q, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q' : Set A)) :=
    ⟨⟨⟨Q', inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q : Set A)) := ⟨q⟩
  let f : PrimeSpectrum.zeroLocus (R := A) (Q' : Set A) → PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    fun x => ⟨x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (le_trans (show (Q : Set A) ⊆ Q' from hlt.le) ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩
  have hf : StrictMono f := fun a b h => h
  rw [ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  have hq : q < f l.head := by
    show Q < (l.head.1.asIdeal)
    exact lt_of_lt_of_le hlt ((PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2)
  refine le_trans ?_ (le_iSup _ ((l.map f hf).cons q hq))
  have hlen : ((l.map f hf).cons q hq).length = l.length + 1 := by
    simp [RelSeries.cons_length, LTSeries.map]
  rw [hlen]
  simp

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace MultiHomogPrimeCriterion

variable {K : Type} [Fintype K] [DecidableEq K]

def lexDeg : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex fun j => b ((Fintype.equivFin K).symm j)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq K] in
lemma lexDeg_injective : Function.Injective (lexDeg (K := K)) := by
  intro a b h
  funext k
  have := congrFun (congrArg ofLex h) (Fintype.equivFin K k)
  change a ((Fintype.equivFin K).symm (Fintype.equivFin K k)) =
    b ((Fintype.equivFin K).symm (Fintype.equivFin K k)) at this
  simpa using this

omit [DecidableEq K] in
lemma lexDeg_surjective : Function.Surjective (lexDeg (K := K)) := by
  intro i
  refine ⟨fun k => ofLex i (Fintype.equivFin K k), ?_⟩
  show toLex _ = i
  rw [← toLex_ofLex i]
  congr 1
  funext j
  simp

variable {ι : K → Type} {R : Type u} [CommRing R]

lemma weight_lexDeg (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexDeg ∘ blockWeight ι) d = lexDeg (Finsupp.weight (blockWeight ι) d) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]

lemma component_lexDeg (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (lexDeg ∘ blockWeight ι) (lexDeg b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by
  ext d
  simp only [coeff_weightedHomogeneousComponent, weight_lexDeg, lexDeg_injective.eq_iff]

lemma isMultiHomog_of_lex {x : MRing ι R} {i : Lex (Fin (Fintype.card K) → ℕ)}
    (hx : IsWeightedHomogeneous (lexDeg ∘ blockWeight ι) x i) : ∃ s, IsMultiHomog x s := by
  obtain ⟨b, rfl⟩ := lexDeg_surjective i
  refine ⟨b, fun d hd => ?_⟩
  have h := hx hd
  rw [weight_lexDeg] at h
  exact lexDeg_injective h


omit [Fintype K] [DecidableEq K] in
lemma coe_decompose {σ M : Type*} [AddCommMonoid M] {_ : DecidableEq M} (w : σ → M)
    [GradedRing (weightedHomogeneousSubmodule R w)] (r : MvPolynomial σ R) (i : M) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R w) r i : MvPolynomial σ R) =
      weightedHomogeneousComponent w i r := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := w) r
  conv_lhs => rw [← sum_weightedHomogeneousComponent w r, finsum_eq_sum _ hfin]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single i]
  · exact DirectSum.decompose_of_mem_same _ (weightedHomogeneousComponent_mem w r i)
  · intro m _ hm
    exact DirectSum.decompose_of_mem_ne _ (weightedHomogeneousComponent_mem w r m) hm
  · intro hi
    have h0 : weightedHomogeneousComponent w i r = 0 := by
      by_contra h
      exact hi ((Set.Finite.mem_toFinset hfin).2 h)
    rw [h0, DirectSum.decompose_zero]
    rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem proof : MultiHomogPrimeCriterion.Statement := by
  intro R _ K _ _ ι Q hQ hne hform
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := weightedHomogeneousSubmodule R (lexDeg ∘ blockWeight ι)) ?_ hne ?_
  · intro i r hr
    obtain ⟨b, rfl⟩ := lexDeg_surjective i
    rw [coe_decompose, component_lexDeg]
    exact hQ r hr b
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    obtain ⟨sa, ha⟩ := isMultiHomog_of_lex hx
    obtain ⟨sb, hb⟩ := isMultiHomog_of_lex hy
    exact hform x y sa sb ha hb hxy

end MultiHomogPrimeCriterion

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def HsymmShift.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
    ∀ d : ℕ, FieldNumbers.relDim W = (d : WithBot (WithTop ℤ)) →
    ∀ (N : ℕ), 0 < N → ∀ (x : Fin N → K → ℤ) (s : K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
      r + Y.length = d →
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (fun i => x i + s) α ++ Y) =
        ∑ k ∈ Finset.range (r + 1), ((N - 1 + r).choose k : ℤ) *
          ∑ α ∈ Finset.Nat.antidiagonalTuple N (r - k),
            intNumL F W (rootList x α ++ List.replicate k s ++ Y)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def truncCoord {N : ℕ} {Φ : Type*} [Zero Φ] (t : Fin N → Φ) (i : ℕ) : Fin N → Φ :=
  fun j => if (j : ℕ) < i then t j else 0

def FlagBundleDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsMultiProjPrime (projIdeal F y w φ (truncCoord t i)) ∧
        FieldNumbers.relDim (projIdeal F y w φ (truncCoord t i)) =
          ((e + i - 1 : ℕ) : WithBot (WithTop ℤ))

def FlagBundleCut.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N, 1 ≤ (i : ℕ) → ∀ L : List (Option K → ℤ), L.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)))
          ((zetaDeg + liftDeg (b i - a)) :: L) =
        intNumL F (projIdeal F y w φ (truncCoord t i)) L

def FlagBundlePullbackVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ L : List (K → ℤ), L.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t i)) (L.map liftDeg) = 0

def FlagBundleLineBase.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (h0 : 0 < N) (n : ℕ) (Y : List (K → ℤ)), n + Y.length = e →
      intNumL F (projIdeal F y w φ (truncCoord t 1)) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        intNumL F (pointIdeal F y) (List.replicate n (a - b ⟨0, h0⟩) ++ Y)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
