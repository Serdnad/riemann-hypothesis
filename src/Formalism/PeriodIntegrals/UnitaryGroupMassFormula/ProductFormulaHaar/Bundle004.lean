module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel
open scoped Pointwise ENNReal NNReal

namespace PI.ProdFormulaE

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem isOpen_integers : IsOpen ((𝒪[K] : Subring K) : Set K) := by
  exact Valuation.isOpen_integer

theorem isCompact_integers : IsCompact ((𝒪[K] : Subring K) : Set K) := by
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K]))

private theorem measurableEmbedding_coe_integers :
    MeasurableEmbedding (Subtype.val : 𝒪[K] → K) :=
  MeasurableEmbedding.subtype_coe isOpen_integers.measurableSet

private theorem measurable_integers_const_add (c : 𝒪[K]) :
    Measurable (fun x : 𝒪[K] => c + x) := by
  exact Measurable.subtype_mk ((measurable_const_add (c : K)).comp measurable_subtype_coe)

private theorem measurable_integers_add_const (c : 𝒪[K]) :
    Measurable (fun x : 𝒪[K] => x + c) := by
  exact Measurable.subtype_mk ((measurable_add_const (c : K)).comp measurable_subtype_coe)

private theorem measurableAdd_integers : MeasurableAdd 𝒪[K] :=
  ⟨fun c => measurable_integers_const_add c, fun c => measurable_integers_add_const c⟩

theorem comap_isAddLeftInvariant (μ : Measure K) [μ.IsAddLeftInvariant] :
    (μ.comap (Subtype.val : 𝒪[K] → K)).IsAddLeftInvariant := by
  have he : MeasurableEmbedding (Subtype.val : 𝒪[K] → K) := measurableEmbedding_coe_integers
  constructor
  intro g
  ext s hs
  rw [Measure.map_apply (measurable_integers_const_add g) hs, he.comap_apply, he.comap_apply]
  have hset : Subtype.val '' ((fun x : 𝒪[K] => g + x) ⁻¹' s) =
      (fun y : K => (g : K) + y) ⁻¹' (Subtype.val '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show (g : K) + x ∈ Subtype.val '' s
      exact ⟨g + x, hx, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hy : y ∈ 𝒪[K] := by
        have hyz : y = (z : K) - g := by rw [hzy]; ring
        rw [hyz]
        exact sub_mem z.2 g.2
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      show g + ⟨y, hy⟩ ∈ s
      have hgz : g + ⟨y, hy⟩ = z := by
        apply Subtype.ext
        rw [hzy]
        try rfl
      rw [hgz]
      exact hz
  rw [hset, measure_preimage_add]

end

private theorem index_span_mul_distribHaarChar_eq_one {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (t : 𝒪[K]) (htK : (t : K) ≠ 0) :
    ((Ideal.span {t}).toAddSubgroup.index : ℝ≥0∞) *
      (distribHaarChar K (Units.mk0 (t : K) htK) : ℝ≥0∞) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, u = Units.mk0 (t : K) htK := ⟨_, rfl⟩
  rw [← hu]
  have hut : (u : K) = t := by rw [hu, Units.val_mk0]
  have hsmul : ∀ x : K, u • x = (t : K) * x := fun x => by
    rw [Units.smul_def, hut, smul_eq_mul]
  have hSo : IsOpen ((𝒪[K] : Subring K) : Set K) := isOpen_integers
  have hSc : IsCompact ((𝒪[K] : Subring K) : Set K) := isCompact_integers
  have huS : IsOpen (u • ((𝒪[K] : Subring K) : Set K)) := hSo.smul u
  have hsub : u • ((𝒪[K] : Subring K) : Set K) ⊆ ((𝒪[K] : Subring K) : Set K) := by
    rintro x ⟨s, hs, rfl⟩
    have h1 : (t : K) * s ∈ ((𝒪[K] : Subring K) : Set K) := (𝒪[K]).mul_mem t.2 hs
    rw [← hsmul] at h1
    exact h1
  have hrange : u • ((𝒪[K] : Subring K) : Set K) ⊆ Set.range (Subtype.val : 𝒪[K] → K) := by
    intro x hx
    exact ⟨⟨x, hsub hx⟩, rfl⟩
  have hR : Set.range (Subtype.val : 𝒪[K] → K) = ((𝒪[K] : Subring K) : Set K) := by
    exact Subtype.range_coe
  have hmem : ∀ y : 𝒪[K], y ∈ Ideal.span {t} ↔ (y : K) ∈ u • ((𝒪[K] : Subring K) : Set K) := by
    intro y
    rw [Ideal.mem_span_singleton', Set.mem_smul_set]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨(a : K), a.2, ?_⟩
      rw [hsmul]
      rw [mul_comm]
      rfl
    · rintro ⟨s, hs, hy⟩
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      rw [← hy, hsmul]
      show s * (t : K) = (t : K) * s
      ring
  obtain ⟨H, hHdef⟩ : ∃ H : AddSubgroup 𝒪[K], H = (Ideal.span {t}).toAddSubgroup := ⟨_, rfl⟩
  rw [← hHdef]
  have hH : (H : Set 𝒪[K]) = Subtype.val ⁻¹' (u • ((𝒪[K] : Subring K) : Set K)) := by
    ext y
    rw [hHdef]
    exact hmem y
  have hHo : IsOpen (H : Set 𝒪[K]) := by
    rw [hH]
    exact huS.preimage continuous_subtype_val
  have hHm : MeasurableSet (H : Set 𝒪[K]) := by
    rw [hH]
    exact measurable_subtype_coe huS.measurableSet
  have : Finite (𝒪[K] ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hHo
  have : H.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have : MeasurableAdd 𝒪[K] := measurableAdd_integers
  have := comap_isAddLeftInvariant (K := K) μ
  have he : MeasurableEmbedding (Subtype.val : 𝒪[K] → K) := measurableEmbedding_coe_integers
  have key := AddSubgroup.index_mul_measure H hHm (μ.comap (Subtype.val : 𝒪[K] → K))
  rw [he.comap_apply, he.comap_apply, hH, Set.image_preimage_eq_inter_range,
    Set.inter_eq_left.mpr hrange, Set.image_univ, hR,
    ← distribHaarChar_mul μ u ((𝒪[K] : Subring K) : Set K), ← mul_assoc] at key
  have hpos : μ ((𝒪[K] : Subring K) : Set K) ≠ 0 :=
    (hSo.measure_pos μ ⟨0, (𝒪[K]).zero_mem⟩).ne'
  have hfin : μ ((𝒪[K] : Subring K) : Set K) ≠ ∞ := (hSc.measure_lt_top (μ := μ)).ne
  have hdiv := ENNReal.mul_div_cancel_right
    (a := (H.index : ℝ≥0∞) * (distribHaarChar K u : ℝ≥0∞)) hpos hfin
  rw [key, ENNReal.div_self hpos hfin] at hdiv
  exact hdiv.symm

theorem modulus_mul_card_quotient : IndexFormula := by
  unfold IndexFormula
  intro K _ _ _ _ t ht
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have htK : (t : K) ≠ 0 := by simpa using ht
  have key := index_span_mul_distribHaarChar_eq_one (K := K) (Measure.addHaar : Measure K) t htK
  rw [modF_of_ne htK]
  show ((distribHaarChar K (Units.mk0 (t : K) htK) : ℝ≥0) : ℝ) *
    ((Ideal.span {t}).toAddSubgroup.index : ℝ) = 1
  have key' : ((Ideal.span {t}).toAddSubgroup.index : ℝ≥0) *
      distribHaarChar K (Units.mk0 (t : K) htK) = 1 := by
    exact_mod_cast key
  rw [mul_comm]
  exact_mod_cast key'

end PI.ProdFormulaE
end
end

section

noncomputable section

open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem finrank_pos (L : LocAt F E sig p) : 0 < Module.finrank L.Fp L.Ep := by
  rw [L.rank]; norm_num

theorem nontrivial (L : LocAt F E sig p) : Nontrivial L.Ep :=
  Module.nontrivial_of_finrank_pos (finrank_pos L)

theorem finite (L : LocAt F E sig p) : Module.Finite L.Fp L.Ep :=
  Module.finite_of_finrank_pos (finrank_pos L)

theorem isUnit_ιE (L : LocAt F E sig p) {x : E} (hx : x ≠ 0) : IsUnit (L.ιE x) :=
  (isUnit_iff_ne_zero.mpr hx).map L.ιE

theorem ιE_smul (L : LocAt F E sig p) (a : F) (y : E) : L.ιE (a • y) = L.ιF a • L.ιE y := by
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]

theorem ιE_eq_sum (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) (y : E) :
    L.ιE y = ∑ i, L.ιF (b.repr y i) • L.ιE (b i) := by
  conv_lhs => rw [← b.sum_repr y]

  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => ιE_smul L _ _

theorem span_basis (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) :
    Submodule.span L.Fp (Set.range (L.ιE ∘ b)) = ⊤ := by
  rw [eq_top_iff, ← L.span, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [ιE_eq_sum L b y]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def basisE (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) : Module.Basis ι L.Fp L.Ep :=
  haveI := finite L
  basisOfTopLeSpanOfCardEqFinrank (L.ιE ∘ b) (span_basis L b).ge
    (by rw [L.rank, ← h, Module.finrank_eq_card_basis b])

theorem basisE_apply (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) (i : ι) : basisE L b h i = L.ιE (b i) := by
  simp [basisE]

theorem basisE_repr (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) (y : E) (i : ι) :
    (basisE L b h).repr (L.ιE y) i = L.ιF (b.repr y i) := by
  have hy : L.ιE y = ∑ j, L.ιF (b.repr y j) • basisE L b h j := by
    simp only [basisE_apply]; exact ιE_eq_sum L b y
  rw [hy, Module.Basis.repr_sum_self]

theorem leftMulMatrix_ιE (L : LocAt F E sig p) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) (h : Module.finrank F E = 2) (x : E) :
    Algebra.leftMulMatrix (basisE L b h) (L.ιE x) = (Algebra.leftMulMatrix b x).map L.ιF := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    basisE_apply, ← map_mul, basisE_repr]

theorem trace_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.trace L.Fp L.Ep (L.ιE x) = L.ιF (Algebra.trace F E x) := by
  classical
  let b := Module.finBasisOfFinrankEq F E h

  rw [Algebra.trace_eq_matrix_trace (basisE L b h), Algebra.trace_eq_matrix_trace b,
  leftMulMatrix_ιE, Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem norm_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.norm L.Fp (L.ιE x) = L.ιF (Algebra.norm F x) := by
  classical
  let b := Module.finBasisOfFinrankEq F E h
  rw [Algebra.norm_eq_matrix_det (basisE L b h), Algebra.norm_eq_matrix_det b,
    leftMulMatrix_ιE, RingHom.map_det]
  rfl

theorem trace_tower (L : LocAt F E sig p) (y : L.Ep) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep y) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (Algebra.trace L.Fp L.Ep y)) := by
  have := L.ellPrime
  let _ : Algebra ℚ_[resChar p] L.Ep :=
    ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
  have : IsScalarTower ℚ_[resChar p] L.Fp L.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L.free
  have := finite L
  have := L.qlFin
  exact (Algebra.trace_trace (R := ℚ_[resChar p]) (S := L.Fp) (T := L.Ep) y).symm

theorem trace_ιE_ql (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep (L.ιE x)) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x))) := by
  rw [trace_tower, trace_ιE L h]

theorem psiE_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    letI := L.ellPrime
    ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
      ‖Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x)) - (a : ℚ_[resChar p])‖ ≤ 1 ∧
      L.psiE (L.ιE x) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
  obtain ⟨a, ha, hn, he⟩ := L.psiE_def (L.ιE x)
  exact ⟨a, ha, by rwa [trace_ιE_ql L h] at hn, he⟩

end PI.ProdFormulaE.Base

end
end

section

noncomputable section

open MeasureTheory ValuativeRel IsDedekindDomain NumberField

namespace PI.ProdFormulaE

section Local

variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K)

theorem iota_mem_integer (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y)
    (a : 𝓞 F) : ι (a : F) ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation K), ← Valuation.Compatible.vle_iff_le,
    ← map_one ι, hv, map_one]
  exact p.valuation_le_one a

theorem modF_iota_int (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (a : 𝓞 F) (ha : a ≠ 0) :
    modF K (ι (a : F)) = HeightOneSpectrum.adicAbv F p (a : F) := by
  set t : 𝒪[K] := ⟨ι (a : F), iota_mem_integer p ι hv a⟩ with ht
  have ht0 : t ≠ 0 := by
    intro h
    have : ι (a : F) = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff ι ι.injective] at this
    exact ha (by exact_mod_cast this)
  have h1 := hI K t ht0
  rw [hC F p K ι hd hv a ha t rfl] at h1
  have h3 := HeightOneSpectrum.embedding_mul_absNorm (K := F) p ha
  rw [FinitePlace.norm_embedding] at h3
  have hN : ((Ideal.absNorm (p.maxPowDividing (Ideal.span {a})) : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ hN (h1.trans h3.symm)

theorem modF_iota (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (z : F) :
    modF K (ι z) = HeightOneSpectrum.adicAbv F p z := by
  by_cases hz : z = 0
  · simp [hz, modF_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hz
  rw [map_div₀, modF_div, map_div₀]
  have e1 := modF_iota_int p ι hI hC hd hv a ha0
  have e2 := modF_iota_int p ι hI hC hd hv b hb0
  simp only [RingOfIntegers.coe_eq_algebraMap] at e1 e2 ⊢
  rw [e1, e2]

end Local

section Global

variable {F : Type} [Field F] [NumberField F]

end Global

section LocAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem modF_locAt (hI : IndexFormula) (hC : CardStep) (L : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    [IsNonarchimedeanLocalField L.Fp] (z : F) :
    modF L.Fp (L.ιF z) = HeightOneSpectrum.adicAbv F p z :=
  modF_iota p L.ιF hI hC L.dense L.val z

end LocAt

theorem modF_iota_finitePlace {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K) (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (z : F) :
    modF K (ι z) = FinitePlace.mk p z := by
  rw [modF_iota p ι hI hC hd hv z, FinitePlace.mk_apply, FinitePlace.norm_embedding]

end PI.ProdFormulaE
end
end
