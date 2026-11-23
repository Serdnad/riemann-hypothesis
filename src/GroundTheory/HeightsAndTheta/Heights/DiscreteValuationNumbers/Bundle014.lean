module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem HilbFnCut.proof (h1 : GradedPieceQuot.Statement.{u}) (h2 : CutPieces.Statement.{u}) :
    HilbFnCut.Statement.{u} := by
  intro F _ K _ _ ι _ I x e hI hx hnzd m
  by_cases hm : ∀ k, 0 ≤ m k
  · set n : K → ℕ := fun k => (m k).toNat with hn
    have hA := h1 F K ι (I ⊔ Ideal.span {x}) n
    have hB := h1 F K ι I n
    have hC := h2 F K ι I x e n hI hx hnzd
    have hL : hilbFn (I ⊔ Ideal.span {x}) m =
        (Module.finrank F (gradedPiece (I ⊔ Ideal.span {x}) n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    have hM : hilbFn I m = (Module.finrank F (gradedPiece I n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    rw [hL, hM, hA, hB]
    by_cases he : e ≤ n
    · have hme : ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hq : (fun k => ((m - fun k => (e k : ℤ)) k).toNat) = n - e := by
        funext k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) =
          (Module.finrank F (gradedPiece I (n - e)) : ℤ) := by
        unfold hilbFn; rw [if_pos hme, hq]
      rw [hN, h1 F K ι I (n - e)]
      rw [if_pos he] at hC
      rw [hC]
      ring
    · have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro hall
        apply he
        intro k
        have h1k := hall k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) = 0 := by
        unfold hilbFn; rw [if_neg hme]
      rw [hN]
      rw [if_neg he] at hC
      rw [hC]
      ring
  · obtain ⟨k, hk⟩ := not_forall.mp hm
    have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
      intro hall
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    unfold hilbFn
    rw [if_neg hm, if_neg hm, if_neg hme, sub_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem SpecialIdealSurj.proof : SpecialIdealSurj.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ V hV
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hπ : Function.Surjective π :=
    MvPolynomial.map_surjective _ (IsLocalRing.residue_surjective)
  refine ⟨V.comap π, Ideal.comap_isPrime π V, ?_, ?_⟩
  · have h0 : IsLocalRing.residue O ϖ = 0 :=
      (IsLocalRing.residue_eq_zero_iff ϖ).2
        ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
    rw [Ideal.mem_comap]
    have : π (C ϖ) = 0 := by
      simp only [π, MvPolynomial.map_C, h0, map_zero]
    rw [this]
    exact V.zero_mem
  · exact Ideal.map_comap_of_surjective π hπ V

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem TopDimMinimal.proof (h1 : DimStrictDrop.Statement.{u}) : TopDimMinimal.Statement.{u} := by
  intro A _ J Q _ N hJQ hJ hQ
  by_contra hmin
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hWne : W ≠ Q := fun h => hmin (h ▸ hW)
  have hWlt : W < Q := lt_of_le_of_ne hWQ hWne
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := hW.1.2
  have h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W) := h1 A W Q hWlt
  have h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)
  have h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1 :=
    add_le_add (not_lt.mp hQ) le_rfl
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1 := Nat.cast_succ N
  exact lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem RelevantDimGe.proof (h1 : BlockAdjoinPrime.Statement.{u}) : RelevantDimGe.Statement.{u} := by
  intro R _ K _ _ ι Q hQ
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let B : ℕ → Set K := fun j => {k | (e k : ℕ) < j}
  let J : ℕ → Ideal (MRing ι R) := fun j =>
    Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B j ∧ p = X v}
  have hJ : ∀ j, (J j).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B j → (X v ∈ J j ↔ X v ∈ Q) :=
    fun j => h1 R K ι Q (B j) hQ.isPrime hQ.multiHomog
  have hle : ∀ j, Q ≤ J j := fun j => le_sup_left
  have hmono : ∀ j, J j ≤ J (j + 1) := fun j =>
    sup_le_sup_left (Ideal.span_mono (by
      rintro p ⟨v, hv, rfl⟩
      exact ⟨v, lt_trans hv (Nat.lt_succ_self _), rfl⟩)) _
  have hstrict : ∀ j (hj : j < Fintype.card K), J j < J (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hmono j) ?_
    obtain ⟨i, hi⟩ := hQ.relevant (e.symm ⟨j, hj⟩)
    intro heq
    have hmem : (X ⟨e.symm ⟨j, hj⟩, i⟩ : MRing ι R) ∈ J (j + 1) :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨⟨e.symm ⟨j, hj⟩, i⟩, by simp [B], rfl⟩)
    rw [← heq] at hmem
    exact hi (((hJ j).2 ⟨e.symm ⟨j, hj⟩, i⟩ (by simp [B])).1 hmem)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (R := MRing ι R) (Q : Set (MRing ι R)) :=
    fun j => ⟨⟨J j, (hJ j).1⟩, hle j⟩
  have hf : StrictMono f := by
    refine Fin.strictMono_iff_lt_succ.2 fun j => ?_
    show J j < J (j + 1)
    exact hstrict j j.isLt
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk (Fintype.card K) f hf)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem FiltrationStepLength.proof : FiltrationStepLength.Statement := by
  intro R _ K ι L W _ f
  let g₁ : (MRing ι R ⧸ L.colon {f}) →ₗ[MRing ι R] MRing ι R ⧸ L :=
    Submodule.mapQ _ _ (LinearMap.mulRight (MRing ι R) f) (fun x hx => by
      have := Submodule.mem_colon_singleton.mp hx
      simpa [smul_eq_mul] using this)
  let g₂ : (MRing ι R ⧸ L) →ₗ[MRing ι R] MRing ι R ⧸ (L ⊔ Ideal.span {f}) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => Submodule.mem_sup_left hx)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with | _ c => ?_
    rw [LinearMap.mem_ker] at hy
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_colon_singleton.mpr (by simpa [smul_eq_mul] using hy)
  have hsurj : Function.Surjective g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply]
      rw [Submodule.Quotient.eq]
      have e : c * f - (l + c * f) = -l := by ring
      rw [e]
      exact L.neg_mem hl
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply] at hx
      rw [Submodule.Quotient.eq] at hx
      have e : a = -(c * f - a) + c * f := by ring
      rw [e]
      exact Submodule.add_mem_sup (L.neg_mem hx) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have key := Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)
  unfold multAt
  rw [add_comm]
  exact key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace CutPieces

variable {F : Type*} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem weightedHomogeneousSubmodule_le_total (m : K → ℕ) :
    weightedHomogeneousSubmodule F (blockWeight ι) m ≤
      weightedHomogeneousSubmodule F (fun _ : (Σ k, ι k) => (1 : ℕ)) (∑ k, m k) := by
  intro f hf
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  intro d hd
  rw [← hf hd, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockWeight, Pi.single_apply]

instance finiteDimensional [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  have : Module.Finite F
      (weightedHomogeneousSubmodule F (fun _ : (Σ k, ι k) => (1 : ℕ)) (∑ k, m k)) :=
    Module.Finite.iff_fg.mpr (weightedHomogeneousSubmodule_fg (R := F) (w := fun _ => 1) (hw := fun _ => one_ne_zero) (n := _))
  exact Submodule.finiteDimensional_of_le (weightedHomogeneousSubmodule_le_total m)

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open Classical in
theorem component_mul {x : MRing ι F} {e : K → ℕ} (hx : IsMultiHomog x e) (y : MRing ι F)
    (m : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) m (x * y) =
      if e ≤ m then x * weightedHomogeneousComponent (blockWeight ι) (m - e) y else 0 := by
  have key : ∀ (p : MRing ι F) (n : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) p n : MRing ι F) =
        weightedHomogeneousComponent (blockWeight ι) n p :=
    fun p n => weightedDecomposition.decompose'_apply F _ p n
  have hx' : x ∈ weightedHomogeneousSubmodule F (blockWeight ι) e := hx
  split_ifs with h
  · have := DirectSum.coe_decompose_mul_of_left_mem_of_le
      (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := y) hx' h
    rwa [key, key] at this
  · have := DirectSum.coe_decompose_mul_of_left_mem_of_not_le
      (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := y) (n := m) hx' h
    rwa [key] at this

end CutPieces

theorem CutPieces.proof : CutPieces.Statement := by
  intro F _ K _ _ ι _ I x e m hI hx hnzd
  set S := weightedHomogeneousSubmodule F (blockWeight ι) with hS
  by_cases hx0 : x = 0
  · have hI1 : I = ⊤ := (Ideal.eq_top_iff_one I).2 (hnzd 1 (by simp [hx0]))
    subst hI1
    have e1 : S m ⊓ ((⊤ : Ideal (MRing ι F)) ⊔ Ideal.span {x}).restrictScalars F = S m := by
      rw [top_sup_eq, Submodule.restrictScalars_top, inf_top_eq]
    have e2 : ∀ n, S n ⊓ (⊤ : Ideal (MRing ι F)).restrictScalars F = S n := fun n => by
      rw [Submodule.restrictScalars_top, inf_top_eq]
    rw [e1, e2, e2]
    split_ifs <;> simp

  set μ := LinearMap.mulLeft F x with hμ
  have hμinj : Function.Injective μ := fun a b h => mul_left_cancel₀ hx0 h
  have hx' : x ∈ S e := hx

  have hsplit : ∀ f ∈ S m, f ∈ I ⊔ Ideal.span {x} →
      ∃ i ∈ S m ⊓ I.restrictScalars F, ∃ y : MRing ι F,
        f = i + weightedHomogeneousComponent (blockWeight ι) m (x * y) := by
    intro f hf hfI
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.mp hfI
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨weightedHomogeneousComponent (blockWeight ι) m i,
      ⟨weightedHomogeneousComponent_mem _ _ _, hI i hi m⟩, y, ?_⟩
    classical
    have h1 := weightedHomogeneousComponent_of_mem (m := m) hf
    rw [if_pos rfl, map_add (f := _)] at h1
    exact h1.symm
  by_cases hem : e ≤ m
  · rw [if_pos hem]
    set A := S m ⊓ I.restrictScalars F
    set B := (S (m - e)).map μ
    have hsup : S m ⊓ (I ⊔ Ideal.span {x}).restrictScalars F = A ⊔ B := by
      apply le_antisymm
      · rintro f ⟨hf, hfI⟩
        obtain ⟨i, hi, y, rfl⟩ := hsplit f hf hfI
        rw [CutPieces.component_mul hx, if_pos hem]
        exact Submodule.add_mem_sup hi
          ⟨_, weightedHomogeneousComponent_mem _ _ _, rfl⟩
      · refine sup_le (inf_le_inf_left _ (Submodule.restrictScalars_mono F le_sup_left)) ?_
        rintro _ ⟨s, hs, rfl⟩
        refine ⟨?_, Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (dvd_mul_right x s))⟩
        have := IsWeightedHomogeneous.mul hx' hs
        rwa [add_tsub_cancel_of_le hem] at this
    have hinf : A ⊓ B = (S (m - e) ⊓ I.restrictScalars F).map μ := by
      apply le_antisymm
      · rintro _ ⟨⟨_, hI'⟩, ⟨s, hs, rfl⟩⟩
        exact ⟨s, ⟨hs, hnzd s hI'⟩, rfl⟩
      · rintro _ ⟨s, ⟨hs, hsI⟩, rfl⟩
        refine ⟨⟨?_, I.mul_mem_left x hsI⟩, ⟨s, hs, rfl⟩⟩
        have := IsWeightedHomogeneous.mul hx' hs
        rwa [add_tsub_cancel_of_le hem] at this
    have hA : FiniteDimensional F A := Submodule.finiteDimensional_of_le inf_le_left
    have key := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h1 : Module.finrank F B = Module.finrank F (S (m - e)) :=
      (Submodule.equivMapOfInjective μ hμinj _).finrank_eq.symm
    have h2 : Module.finrank F ↥((S (m - e) ⊓ I.restrictScalars F).map μ) =
        Module.finrank F ↥(S (m - e) ⊓ I.restrictScalars F) :=
      (Submodule.equivMapOfInjective μ hμinj _).finrank_eq.symm
    rw [hinf, h1, h2] at key
    rw [hsup]
    omega
  · rw [if_neg hem, add_zero]
    have hsup : S m ⊓ (I ⊔ Ideal.span {x}).restrictScalars F = S m ⊓ I.restrictScalars F := by
      apply le_antisymm
      · rintro f ⟨hf, hfI⟩
        obtain ⟨i, hi, y, rfl⟩ := hsplit f hf hfI
        rw [CutPieces.component_mul hx, if_neg hem, add_zero]
        exact hi
      · exact inf_le_inf_left _ (Submodule.restrictScalars_mono F le_sup_left)
    rw [hsup]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem finite_blockWeight_eq {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun v : (Σ k, ι k) => m v.1)).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_Iic]
  intro v
  have hcoord : (Finsupp.weight (blockWeight ι) d) v.1 =
      Finsupp.weight (fun x => blockWeight ι x v.1) d := by
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  have hle : d v ≤ Finsupp.weight (fun x => blockWeight ι x v.1) d :=
    Finsupp.le_weight _ (by simp [blockWeight]) d
  rw [← hcoord, hd] at hle
  simpa using hle

theorem finiteDimensional_weightedHomogeneousSubmodule (F : Type u) [Field F] {K : Type}
    [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_blockWeight_eq ι m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})

theorem GradedPieceQuot.proof : GradedPieceQuot.Statement.{u} := by
  intro F _ K _ _ ι _ I m
  have := finiteDimensional_weightedHomogeneousSubmodule F ι m
  set S := weightedHomogeneousSubmodule F (blockWeight ι) m with hS
  set J : Submodule F (MRing ι F) := I.restrictScalars F with hJ
  let π : MRing ι F →ₗ[F] MRing ι F ⧸ I := (Ideal.Quotient.mkₐ F I).toLinearMap
  let q : S →ₗ[F] MRing ι F ⧸ I := π ∘ₗ S.subtype
  have hrange : LinearMap.range q = gradedPiece I m := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hkerπ : LinearMap.ker π = J := by
    ext x
    simp [π, hJ, Ideal.Quotient.eq_zero_iff_mem]
  have hker : (LinearMap.ker q).map S.subtype = S ⊓ J := by
    rw [LinearMap.ker_comp, hkerπ, Submodule.map_comap_subtype]
  have hkerdim : Module.finrank F (LinearMap.ker q) = Module.finrank F ↥(S ⊓ J) := by
    rw [← hker]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker q
  rw [hrange, hkerdim] at hrn
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end
