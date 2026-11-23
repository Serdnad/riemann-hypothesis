module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.level :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (J : Ideal A) (u v : A) (b c : Ideal R), Reg2 J u v → b * c ≤ J.map (algebraMap A R) →
      algebraMap A R u ∈ b ⊔ c → algebraMap A R v ∈ b ⊔ c → ∀ l : Module.Dual A R,
        ∃ a : A, ∀ (y : A) (β γ : R), β ∈ b → γ ∈ c → algebraMap A R y = β + γ → l β - y * a ∈ J := by
  intro A R _ _ _ J u v b c hreg hbc hu hv l
  have hl : ∀ x ∈ J.map (algebraMap A R), ∀ r : R, l (r * x) ∈ J := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact J.mul_mem_right _ hj
    | zero => intro r; simp
    | add x y _ _ hx hy => intro r; rw [mul_add, map_add (f := _)]; exact J.add_mem (hx r) (hy r)
    | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have key : ∀ (y y' : A) (β γ β' γ' : R), β ∈ b → γ ∈ c → β' ∈ b → γ' ∈ c →
      algebraMap A R y = β + γ → algebraMap A R y' = β' + γ' → y' * l β - y * l β' ∈ J := by
    intro y y' β γ β' γ' hβ hγ hβ' hγ' hy hy'
    have h1 : algebraMap A R y' * β - algebraMap A R y * β' ∈ J.map (algebraMap A R) := by
      apply hbc
      have e : algebraMap A R y' * β - algebraMap A R y * β' = β * γ' - β' * γ := by
        rw [hy, hy']; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_mul hβ hγ') (Ideal.mul_mem_mul hβ' hγ)
    have h2 := hl _ h1 1
    rwa [one_mul, map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h2
  obtain ⟨βu, hβu, γu, hγu, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨βv, hβv, γv, hγv, hv'⟩ := Submodule.mem_sup.mp hv
  have k := key u v βu γu βv γv hβu hγu hβv hγv hu'.symm hv'.symm
  have hm : v * l βu ∈ J ⊔ Ideal.span {u} := by
    have e : v * l βu = (v * l βu - u * l βv) + u * l βv := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left k)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨l βv, mul_comm _ _⟩))
  obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.mp (hreg.2 _ hm)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine ⟨a, fun y β γ hβ hγ hy => hreg.1 _ ?_⟩
  have k2 := key y u β γ βu γu hβ hγ hβu hγu hy hu'.symm
  have e : u * (l β - y * a) = (u * l β - y * l βu) + y * j := by
    rw [← hjs]; ring
  rw [e]
  exact J.add_mem k2 (J.mul_mem_left _ hj)
end

section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.etaleCohomology_simplicialCochain_representation_step {R : Type} [CommRing R] (a I : Ideal R) :
    IsConnected (PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)) ↔
    IsConnected ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ :
        Set (PrimeSpectrum (R ⧸ a))) := by
  have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
  have hemb := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  have hr := range_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  rw [Ideal.mk_ker] at hr
  have hpre : (PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a))) =
      PrimeSpectrum.comap (Ideal.Quotient.mk a) ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_preimage, SetLike.coe_subset_coe,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_le_iff_le_comap
  have him : PrimeSpectrum.comap (Ideal.Quotient.mk a) '' ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ) =
      PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [hpre, ← Set.preimage_compl, Set.image_preimage_eq_inter_range, hr, Set.diff_eq,
      Set.inter_comm]
  rw [← him]
  unfold IsConnected
  rw [Set.image_nonempty, hemb.isInducing.isPreconnected_image]

theorem UpperTheory.V.AlgebraTools.Conn.bridge :
    ∀ {R : Type} [CommRing R] (a : Ideal R) (k : WithBot ℕ∞), ConnOn a k ↔ ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro R _ a k
  constructor
  · intro h J hJ
    have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
    have hle : a ≤ J.comap (Ideal.Quotient.mk a) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hJ' : (J.comap (Ideal.Quotient.mk a)).map (Ideal.Quotient.mk a) = J :=
      Ideal.map_comap_of_surjective _ hs J
    rw [← hJ'] at hJ ⊢
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hJ
    exact (etaleCohomology_simplicialCochain_representation_step a _).mp (h _ hle hJ)
  · intro h I hle hI
    rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hI
    exact (etaleCohomology_simplicialCochain_representation_step a I).mpr (h _ hI)
end

section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.dvrBase :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O], IsBase O := by
  intro O _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI : Nontrivial (QuotSMulTop ϖ O) := by
    open Pointwise in
    refine Submodule.Quotient.nontrivial_iff.mpr ?_
    intro h
    have h1 : (1 : O) ∈ ϖ • (⊤ : Submodule O O) := by rw [h]; exact Submodule.mem_top
    obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one x (by simpa [smul_eq_mul] using hx))
  refine ⟨inferInstance, inferInstance, ⟨inferInstance, 1, ?_, [ϖ], rfl, ?_, ?_⟩, inferInstance⟩
  · rw [IsDiscreteValuationRing.ringKrullDim_eq_one]; rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · rw [RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨fun a b hab => mul_left_cancel₀ hϖ.ne_zero (by simpa [smul_eq_mul] using hab), ?_⟩
    exact RingTheory.Sequence.IsRegular.nil _ _
end
