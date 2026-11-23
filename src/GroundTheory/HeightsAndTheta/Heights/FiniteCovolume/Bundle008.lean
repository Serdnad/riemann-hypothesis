module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle004
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace GramDetermines


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem sesq_linearCombination (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c d : Fin n → E) :
    h.toSesq (Fintype.linearCombination E e' c) (Fintype.linearCombination E e' d) =
      h.toSesq (Fintype.linearCombination E e c) (Fintype.linearCombination E e d) := by

  simp only [Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
  LinearMap.smul_apply, hG]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem linearCombination_surjective {n : ℕ} {e : Fin n → W}
    (hL : IsLattice E (AddSubgroup.closure (Set.range e))) :
    Function.Surjective (Fintype.linearCombination E e) := by
  have hle : AddSubgroup.closure (Set.range e) ≤
      (LinearMap.range (Fintype.linearCombination E e)).toAddSubgroup := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨Pi.single a 1, by simp⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  exact hle hx


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem linearCombination_eq_zero (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hL' : IsLattice E (AddSubgroup.closure (Set.range e')))
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c : Fin n → E)
    (hc : Fintype.linearCombination E e c = 0) : Fintype.linearCombination E e' c = 0 := by
  apply h.nonsingular.1
  refine LinearMap.ext fun y => ?_
  obtain ⟨d, rfl⟩ := linearCombination_surjective hL' y
  rw [sesq_linearCombination h hG, hc, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

theorem proof (h : HermitianForm F E W) : GramDetermines.Statement h := by
  intro n e e' hL hL' hG
  have hG' : ∀ a b, h.toSesq (e' a) (e' b) = h.toSesq (e a) (e b) := fun a b => (hG a b).symm
  have hs := linearCombination_surjective hL
  have hs' := linearCombination_surjective hL'
  have hker : LinearMap.ker (Fintype.linearCombination E e) =
      LinearMap.ker (Fintype.linearCombination E e') := by
    ext c
    simp only [LinearMap.mem_ker]
    exact ⟨linearCombination_eq_zero h hL' hG c, linearCombination_eq_zero h hL hG' c⟩
  let γ : W ≃ₗ[E] W := ((Fintype.linearCombination E e).quotKerEquivOfSurjective hs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      ((Fintype.linearCombination E e').quotKerEquivOfSurjective hs'))
  have hγ : ∀ c, γ (Fintype.linearCombination E e c) = Fintype.linearCombination E e' c :=
    fun c => by simp [γ, Submodule.quotEquivOfEq_mk]
  refine ⟨⟨γ, fun x y => ?_⟩, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hs x
    obtain ⟨d, rfl⟩ := hs y
    rw [hγ, hγ]
    exact sesq_linearCombination h hG c d
  · simpa using hγ (Pi.single a 1)

end GramDetermines

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem BoundedGenerators.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : BoundedGenerators.Statement h v := by
  intro M D t ht
  obtain ⟨c, hc⟩ := hA D
  obtain ⟨d, κ, hκ⟩ := hT M
  obtain ⟨C, hC⟩ := hR d t (|κ| * c) ht
  refine ⟨d, C, fun La g hLa hmin => ?_⟩
  obtain ⟨_, _, hcov⟩ := hc La hLa
  obtain ⟨T, hTn, hTc⟩ := hκ g

  let Φ : W →+ EuclideanSpace ℝ (Fin d) :=
    ((T : (InfinitePlace E → ι → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin d)) : _ →ₗ[ℝ] _).toAddMonoidHom.comp
      (vecAtHom v)
  have hΦ : ∀ x, Φ x = T (vecAt v x) := fun x => rfl
  have hvec : Function.Injective (vecAt v) := by
    intro x y hxy
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    apply v.repr.injective
    ext i
    exact w.embedding.injective (congrFun (congrFun hxy w) i)
  have hΦinj : Function.Injective Φ := T.injective.comp hvec
  let L := ZLattice.comap ℝ (archLattice v La) T.symm.toLinearMap
  have hmemL : ∀ z, z ∈ L ↔ ∃ x ∈ La, Φ x = z := by
    intro z
    rw [← SetLike.mem_coe, ZLattice.coe_comap, Set.mem_preimage, SetLike.mem_coe, mem_archLattice]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [hΦ]
    constructor
    · intro hx; rw [hx]; simp
    · intro hx; rw [← hx]; simp
  have hLmin : ∀ z ∈ L, z ≠ 0 → t ≤ ‖z‖ := by
    intro z hz hz0
    obtain ⟨x, hx, rfl⟩ := (hmemL z).1 hz
    have hx0 : x ≠ 0 := by rintro rfl; exact hz0 (map_zero Φ)
    rw [hΦ, hTn]
    exact hmin x hx hx0
  have hLcov : ZLattice.covolume L ≤ |κ| * c := by
    rw [hTc]
    have h0 : 0 ≤ ZLattice.covolume (archLattice v La) := ENNReal.toReal_nonneg
    exact (mul_le_mul_of_nonneg_right (le_abs_self κ) h0).trans
      (mul_le_mul_of_nonneg_left hcov (abs_nonneg κ))
  obtain ⟨b, hb⟩ := hC L hLmin hLcov
  choose e he heb using fun i => (hmemL (b i)).1 (b i).2
  refine ⟨e, le_antisymm ((AddSubgroup.closure_le La).2 (Set.range_subset_iff.2 he)) ?_,
    fun i => ?_⟩
  · intro x hx
    have hxL : Φ x ∈ L := (hmemL _).2 ⟨x, hx, rfl⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨Φ x, hxL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    set r := b.repr ⟨Φ x, hxL⟩
    have hx' : x = ∑ i, r i • e i := by
      apply hΦinj

      rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, heb i]
    rw [hx']
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [← hTn, ← hΦ, heb i]
    exact hb i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : CoordEmbedBasis.Statement E ι)
    (h₂ : IntegralFormCovolume.Statement (ι → E) (InfinitePlace E → ι → ℂ)
      (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E)))
    (h₃ : TraceHermNondegenerate.Statement h v) (h₄ : DualLatticeMultiple.Statement h)
    (h₅ : CoordLatticeFullRank.Statement v) : ArchCovolumeBound.Statement h v := by
  intro D
  obtain ⟨k, hk0, hk⟩ := h₄ D
  let e := Pi.basis fun _ : ι => integralBasis E
  obtain ⟨C, hC⟩ := h₂ (coordEmbed E ι) e (traceHerm h v) volume (Measure.pi.isAddHaarMeasure _) h₃ h₁.1
    (by rw [h₁.2, finrank_eq_card_basis e])
  refine ⟨Real.sqrt (C * |(k : ℝ)| ^ Fintype.card (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E))),
    fun La hLa => ?_⟩
  let φ : W →+ (ι → E) := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have hφ : ∀ x, v.equivFun.symm (φ x) = x := fun x => v.equivFun.symm_apply_apply x
  have hmem : ∀ y, y ∈ La.map φ ↔ v.equivFun.symm y ∈ La := by
    intro y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [hφ]
    · intro hy
      exact ⟨_, hy, v.equivFun.apply_symm_apply y⟩
  have harch : archLattice v La = AddSubgroup.toIntSubmodule ((La.map φ).map (coordEmbed E ι)) := by
    rw [archLattice, AddSubgroup.map_map]
    rfl
  obtain ⟨hfg, hspan⟩ := h₅ La hLa.isLattice
  obtain ⟨hint, hdual⟩ := hk La hLa
  obtain ⟨hD, hZ, hcov⟩ := hC (La.map φ) k hk0 hfg hspan
    (fun x hx y hy => hint _ ((hmem x).1 hx) _ ((hmem y).1 hy))
    (fun y hy => by
      rw [hmem, map_zsmul]
      refine hdual _ fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (φ x) (AddSubgroup.mem_map_of_mem φ hx)
      exact ⟨n, by rw [traceHerm_apply, hφ] at hn; exact hn⟩)
  rw [harch]
  exact ⟨hD, hZ, (le_abs_self _).trans (Real.abs_le_sqrt hcov)⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def ArchUnimodular.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure], μ.IsMulRightInvariant

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def MajorantStabCompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ M : Majorant h v, IsCompact (M.stab : Set (archUnitary h v))

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnfoldingTorus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ)
    (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ∀ FD : Set (archUnitary h v),
      IsFundamentalDomain (vecStabGroup h v La x₀) FD μ → ∀ t : ℝ, 0 < t →
        μ (FD ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) =
          c * ∫⁻ b : InfinitePlace E → ℂ,
            {b : InfinitePlace E → ℂ | M.len (fun w => b w • vecAt v x₀ w) < t}.indicator
              (fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) b

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Units

variable (E : Type*) [Field E] [NumberField E]

def congruenceUnits (N : ℕ) : Subgroup (𝓞 E)ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})).toMonoidHom).ker

omit [NumberField E] in
variable {E} in
theorem mem_congruenceUnits {N : ℕ} {ε : (𝓞 E)ˣ} :
    ε ∈ congruenceUnits E N ↔ (ε : 𝓞 E) - 1 ∈ Ideal.span {(N : 𝓞 E)} := by
  rw [congruenceUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq]

def CongruenceUnitsFiniteIndex.Statement : Prop :=
  ∀ N : ℕ, 0 < N → (congruenceUnits E N).index ≠ 0

end Units

section Groups

def BoundedIndexSubgroupsFinite.Statement (G : Type*) [AddCommGroup G] : Prop :=
  ∀ A B : AddSubgroup G, B.FG → A ≤ B → ∀ C : ℕ,
    {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}.Finite

end Groups

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsotropicScaling.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ : W), IsLattice E La → IsIntegralOn h La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∃ N : ℕ, 0 < N ∧ ∀ ε ∈ congruenceUnits E N,
      ∃ γ ∈ latticeStab h La, γ • x₀ = ((ε : 𝓞 E) : E) • x₀

end Spaces

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def ComplementArchCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ w₀ : W) (m : ℕ),
    IsLattice (E := E) La → IsHyperbolicPair h x₀ w₀ → 0 < m →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ Y : InfinitePlace E → ι → ℂ,
      (∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 ∧
        star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0) →
      ∃ y ∈ hypComplement h x₀ w₀, (∃ z ∈ La, y = m • z) ∧ Y - vecAt v y ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def RationalUnipotent.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ →
    ∃ m : ℕ, 0 < m ∧ ∀ (y : W) (c : E), y ∈ hypComplement h x₀ w₀ → (∃ z ∈ La, y = m • z) →
      (∃ a : 𝓞 E, c = (m : E) * a) → c + conj F E c = -h.toSesq y y →
      ∃ γ ∈ latticeStab h La, γ • x₀ = x₀ ∧ γ • w₀ = w₀ + y + c • x₀ ∧
        ∀ z ∈ hypComplement h x₀ w₀, γ • z = z - h.toSesq y z • x₀

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
