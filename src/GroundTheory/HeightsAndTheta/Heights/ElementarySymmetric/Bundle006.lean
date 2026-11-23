module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def diagWordMomentPoly (k i : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
      (pderiv 0 (pderiv 1 ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ))))

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem SubSystem.twist_sub_fg (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x)
    (hF : (F.sub I).FG) (hQ : (Q.sub I).FG) : ((F.twist Q).sub I).FG := by
  obtain ⟨sF, hsF⟩ := hF
  obtain ⟨sQ, hsQ⟩ := hQ
  classical
  refine ⟨Finset.image₂ (fun q y => q • y) sQ sF, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Finset.coe_image₂] at hz
    obtain ⟨q, hq, y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨q, hsQ ▸ Submodule.subset_span hq, y, hsF ▸ Submodule.subset_span hy, rfl⟩
  · change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hsQ] at hq
    rw [← hsF] at hy
    refine Submodule.span_induction (p := fun q _ => q • y ∈
      Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hq
    · intro q hq
      refine Submodule.span_induction (p := fun y _ => q • y ∈
        Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hy
      · intro y hy
        exact Submodule.subset_span (by rw [Finset.coe_image₂]; exact ⟨q, hq, y, hy, rfl⟩)
      · rw [smul_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        rw [Subalgebra.smul_def, smul_comm]
        exact Submodule.smul_mem _ a hz
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq
      rw [smul_assoc]
      exact Submodule.smul_mem _ a hq

end

theorem SubFamilyTwist.proof : SubFamilyTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q hF
  exact ⟨F.twistFam Q.toSubFamily, rfl, fun I =>
    SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Algebra Cardinal

noncomputable section

universe u w

namespace DimTie

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

abbrev ratioRing (y : Fin (N + 1) → Ω) : Subalgebra k Ω :=
  Algebra.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}

theorem ratio_mem (y : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : y i ≠ 0) (j : Fin (N + 1)) :
    y j / y i ∈ ratioRing (k := k) y :=
  Algebra.subset_adjoin ⟨i, j, hi, rfl⟩


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem trdeg_funField (y : Fin (N + 1) → Ω) :
    trdeg k (funField (k := k) y) = trdeg k (ratioRing (k := k) y) := by
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  show trdeg k (IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}) = _
  rw [← trdeg_add_eq k (ratioRing (k := k) y)
    (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}),
    trdeg_eq_zero (R := ratioRing (k := k) y)
      (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}), add_zero]

theorem trdeg_polynomial (D : Type w) [CommRing D] [IsDomain D] [Algebra k D] [FaithfulSMul k D] :
    trdeg k (Polynomial D) = trdeg k D + 1 := by
  have : FaithfulSMul D (Polynomial D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Polynomial.C_injective
  rw [← trdeg_add_eq k D (A := Polynomial D), Polynomial.trdeg_of_isDomain]

theorem aeval_C_mul_X_injective {c : Ω} (hc : c ≠ 0) :
    Function.Injective (Polynomial.aeval (R := Ω) (Polynomial.C c * Polynomial.X)) := by
  have h : (Polynomial.aeval (R := Ω) (Polynomial.C c⁻¹ * Polynomial.X)).comp
      (Polynomial.aeval (Polynomial.C c * Polynomial.X)) = AlgHom.id Ω (Polynomial Ω) := by
    refine Polynomial.algHom_ext ?_
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
  exact Function.LeftInverse.injective (g := Polynomial.aeval (Polynomial.C c⁻¹ * Polynomial.X))
    fun p => by rw [← AlgHom.comp_apply, h, AlgHom.id_apply]

section Cone

variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)

def ratio (j : Fin (N + 1)) : ratioRing (k := k) y := ⟨y j / y i₀, ratio_mem y hi₀ j⟩

def dehom : Poly k N →ₐ[k] Polynomial (ratioRing (k := k) y) :=
  aeval fun j => Polynomial.C (ratio y hi₀ j) * Polynomial.X


variable (i₀) in
def rehom : Polynomial (ratioRing (k := k) y) →ₐ[k] Polynomial Ω :=
  ((Polynomial.aeval (R := Ω) (Polynomial.C (y i₀) * Polynomial.X)).restrictScalars k).comp
    (Polynomial.mapAlgHom (ratioRing (k := k) y).val)

include hi₀ in
theorem rehom_injective : Function.Injective (rehom (k := k) y i₀) := by
  rw [rehom, AlgHom.coe_comp]
  exact (aeval_C_mul_X_injective hi₀).comp (Polynomial.map_injective _ Subtype.val_injective)

theorem rehom_comp_dehom : (rehom (k := k) y i₀).comp (dehom y hi₀) = cone (S := k) y := by
  refine MvPolynomial.algHom_ext fun j => ?_
  have hc : (cone (S := k) y) (X j) = Polynomial.C (y j) * Polynomial.X := by
    simp [cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rw [hc]
  simp [rehom, dehom, ratio]
  rw [← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ _ hi₀]

theorem primeOf_eq_ker : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀) := by
  ext f
  rw [primeOf_eq, RingHom.mem_ker, RingHom.mem_ker, ← rehom_comp_dehom (k := k) y hi₀, AlgHom.comp_apply,
    map_eq_zero_iff _ (rehom_injective (k := k) y hi₀)]

theorem isAlgebraic_range :
    Algebra.IsAlgebraic (dehom (k := k) y hi₀).range (Polynomial (ratioRing (k := k) y)) := by
  set R := (dehom (k := k) y hi₀).range
  have hmem : ∀ j, Polynomial.C (ratio (k := k) y hi₀ j) * Polynomial.X ∈ R :=
    fun j => ⟨X j, by simp [dehom]⟩
  have h1 : ratio (k := k) y hi₀ i₀ = 1 := Subtype.ext (div_self hi₀)
  have hX : IsAlgebraic R (Polynomial.X : Polynomial (ratioRing (k := k) y)) := by
    have h := hmem i₀
    rw [h1, Polynomial.C_1, one_mul] at h
    exact isAlgebraic_algebraMap (⟨_, h⟩ : R)
  have hb : ∀ j, IsAlgebraic R (Polynomial.C (ratio (k := k) y hi₀ j)) := fun j =>
    IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) hX
      (by rw [mul_comm]; exact isAlgebraic_algebraMap (⟨_, hmem j⟩ : R))
  have hgen : ∀ i j (hi : y i ≠ 0),
      IsAlgebraic R (Polynomial.C (⟨y j / y i, ratio_mem y hi j⟩ : ratioRing (k := k) y)) := by
    intro i j hi
    have hne : ratio (k := k) y hi₀ i ≠ 0 := fun h =>
      div_ne_zero hi hi₀ (congrArg Subtype.val h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (Polynomial.C_ne_zero.mpr hne))
      (hb i) ?_
    have he : ratio (k := k) y hi₀ i * ⟨y j / y i, ratio_mem y hi j⟩ = ratio (k := k) y hi₀ j := by
      apply Subtype.ext
      change y i / y i₀ * (y j / y i) = y j / y i₀
      field_simp
    rw [← Polynomial.C_mul, he]
    exact hb j
  have hCD : ∀ d : ratioRing (k := k) y, IsAlgebraic R (Polynomial.C d) := by
    let M : Subalgebra k (ratioRing (k := k) y) :=
      ((Subalgebra.algebraicClosure R (Polynomial (ratioRing (k := k) y))).restrictScalars k).comap
        (Polynomial.CAlgHom (R := k) (A := ratioRing (k := k) y))
    have hM : ratioRing (k := k) y ≤ M.map (ratioRing (k := k) y).val := Algebra.adjoin_le (by
      rintro _ ⟨i, j, hi, rfl⟩
      exact ⟨⟨y j / y i, ratio_mem y hi j⟩, hgen i j hi, rfl⟩)
    intro d
    obtain ⟨d', hd', he⟩ := hM d.2
    rw [show d = d' from Subtype.ext he.symm]
    exact hd'
  refine ⟨fun p => ?_⟩
  induction p using Polynomial.induction_on with
  | C a => exact hCD a
  | add p q hp hq => exact hp.add hq
  | monomial n a h => rw [pow_succ, ← mul_assoc]; exact h.mul hX

theorem trdeg_range :
    trdeg k (dehom (k := k) y hi₀).range = trdeg k (ratioRing (k := k) y) + 1 := by
  have := isAlgebraic_range (k := k) y hi₀
  have : FaithfulSMul k (dehom (k := k) y hi₀).range :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  have := (faithfulSMul_iff_algebraMap_injective (dehom (k := k) y hi₀).range
    (Polynomial (ratioRing (k := k) y))).2 Subtype.val_injective
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  rw [← trdeg_polynomial (k := k) (ratioRing (k := k) y), ← trdeg_add_eq k (dehom (k := k) y hi₀).range
    (A := Polynomial (ratioRing (k := k) y)),
    trdeg_eq_zero (R := (dehom (k := k) y hi₀).range) (A := Polynomial (ratioRing (k := k) y)),
    add_zero]

end Cone

theorem ringKrullDim_eq (y : Fin (N + 1) → Ω) (hy : y ≠ 0) :
    ringKrullDim (Poly k N ⧸ primeOf (S := k) y) =
      (((trdeg k (funField (k := k) y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have : Algebra.FiniteType k (Poly k N ⧸ primeOf (S := k) y) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _)
      (Ideal.Quotient.mkₐ_surjective k _)
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k]
  have hk : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀).rangeRestrict := by
    rw [primeOf_eq_ker (k := k) y hi₀]
    ext f
    simp only [RingHom.mem_ker]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let e : (Poly k N ⧸ primeOf (S := k) y) ≃ₐ[k] (dehom (k := k) y hi₀).range :=
    (Ideal.quotientEquivAlgOfEq k hk).trans
      (Ideal.quotientKerAlgEquivOfSurjective (dehom (k := k) y hi₀).rangeRestrict_surjective)
  have h := AlgEquiv.lift_trdeg_eq (R := k) (A := Poly k N ⧸ primeOf (S := k) y)
    (A' := (dehom (k := k) y hi₀).range) e
  rw [trdeg_range (k := k) y hi₀, ← trdeg_funField] at h
  have h2 := congrArg Cardinal.toENat h
  simp only [toENat_lift, map_add (f := _), map_one] at h2
  rw [h2]

end DimTie

theorem DimTie.proof : DimTie.Statement := by
  intro k _ Ω _ _ N y hy e
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have hdim := DimTie.ringKrullDim_eq (k := k) y hy
  constructor
  · intro h
    have h' := h.dim
    rw [hdim] at h'
    have h3 : (trdeg k (funField (k := k) y)).toENat + 1 = (e : ℕ∞) + 1 := by exact_mod_cast h'
    exact Cardinal.toENat_eq_natCast.mp ((ENat.add_left_injective_of_ne_top ENat.one_ne_top) h3)
  · intro h
    have h' : trdeg k (funField (k := k) y) = e := h
    refine ⟨inferInstance, fun p hp d => homogeneousComponent_mem_primeOf y hp d, le_rfl, ⟨i₀, ?_⟩, ?_⟩
    · rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i₀), aeval_X]
      exact hi₀
    · rw [hdim, Cardinal.toENat_eq_natCast.mpr h']
      push_cast
      rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Symmetry

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_eq_foldl_map {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (((List.finRange n).filter (· ∈ T)).map L).foldl
      (fun F Q => F.twist Q) (twistSys S x 0) := by
  unfold tensorSub
  rw [List.foldl_map]

theorem tensorSub_comp_perm {n : ℕ} (L : Fin n → SubSystem S x Ω) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) :
    tensorSub (fun i => L (σ i)) T = tensorSub L (T.map σ.toEmbedding) := by
  rw [tensorSub_eq_foldl_map, tensorSub_eq_foldl_map]
  have hp : (((List.finRange n).filter (· ∈ T)).map σ).Perm
      ((List.finRange n).filter (· ∈ T.map σ.toEmbedding)) := by
    rw [List.perm_ext_iff_of_nodup (((List.nodup_finRange n).filter _).map σ.injective)
      ((List.nodup_finRange n).filter _)]
    intro a
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Finset.mem_map_equiv]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro ha
      exact ⟨σ.symm a, ha, by simp⟩
  have hfun : (fun i => L (σ i)) = L ∘ σ := rfl
  rw [hfun, ← List.map_map]
  exact (hp.map L).foldl_eq' (fun F _ P _ Q => by
    rw [SubSystem.twist_assoc, SubSystem.twist_comm F, ← SubSystem.twist_assoc]) _

theorem interSum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) (c : ℕ) :
    interSum pp (fun i => L (σ i)) c = interSum pp L c := by
  unfold interSum
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun T => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, tensorSub_comp_perm]

theorem interNum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) :
    interNum pp (fun i => L (σ i)) = interNum pp L := by
  unfold interNum
  congr 1
  funext c
  exact interSum_comp_perm pp L σ c

theorem interSum_eventually_eq_interNum (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    {m : ℤ} (h : ∀ᶠ c : ℕ in atTop, interSum pp L c = m) :
    ∀ᶠ c : ℕ in atTop, interSum pp L c = interNum pp L := by
  have ht : Tendsto (interSum pp L) atTop (nhds m) :=
    tendsto_const_nhds.congr' (h.mono fun _ hc => hc.symm)
  have hm : interNum pp L = m := ht.limUnder_eq
  rw [hm]
  exact h

end Symmetry

theorem GenericPointSectionInput.proof (hE : InterNumEventual.Statement.{u, w})
    (hA : InterNumAdditive.Statement.{u, w}) (hC : InterNumCut.Statement.{u, w})
    (hP : InterNumPointDeg.Statement.{u, w}) : GenericPointSectionInput.Statement.{u, w} := by
  intro k _ Ω _ _ N x
  refine ⟨fun n pp L hW => ?_, fun n pp L σ _ => ?_, fun n pp L i L' L'' hW => ?_,
    fun n pp L Lc s hW hs hne => ?_, fun pp hW => ?_⟩
  · obtain ⟨m, hm⟩ := hE k Ω N x n pp L hW
    exact interSum_eventually_eq_interNum pp _ hm
  · exact interNum_comp_perm pp (fun i => (L i).toSubSystem) σ
  · exact hA k Ω N x n pp L i L' L'' hW
  · exact hC k Ω N x n pp L Lc s hW hs hne
  · exact hP k Ω N x pp hW

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallGenHeightsNonneg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι)
    (II : IntersectionSystem) (q : ℕ) (w : Fin q → MRing ι),
    IsIntersectionSystem II → IsSmoothHerm A → (∀ k, 0 ≤ A.a k) →
    (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (w j) fun k ↦ (A.a k).toNat) →
    (∀ Q : Ideal (MRing ι), IsMultiProjPrime Q → P ≤ Q → ∃ j, w j ∉ Q) →
    (∀ j, ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ A.h z) →
    HeightsNonneg II P A

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def wwLinPot {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (X₀ X₁ A₀ : HermLine ι) (k : ℕ)
    (u : ℕ → Fin 2 → ℝ) : Fin e → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z =>
    if (j : ℕ) < 2 * k then u j 0 * Real.log (X₀.h z) + u j 1 * Real.log (X₁.h z) else Real.log (A₀.h z)

def wwLinProd (k : ℕ) (u : ℕ → Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∏ n ∈ Finset.range (2 * k), (C (u n 0) * X 0 + C (u n 1) * X 1)

def wwLogWeight (p : S2 × S2) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2)

end

end GroundTheory.Heights₂.Heights.Inter
end
