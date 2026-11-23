module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem integral_eq_sum_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) (f : G → ℂ) (hf : ∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) :
    ∃ t : Finset (G ⧸ K), ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K := by
  classical
  set q : G → G ⧸ K := QuotientGroup.mk

  have hcov : S ⊆ ⋃ s ∈ S, s • (K : Set G) := fun s hs =>
    Set.mem_biUnion hs ⟨1, one_mem K, by simp⟩
  obtain ⟨b, hbS, hbf, hb⟩ := hS.elim_finite_subcover_image (fun s _ => hKo.smul s) hcov
  have hfin : (q '' S).Finite := by
    refine (hbf.image q).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hy⟩ := Set.mem_iUnion₂.1 (hb hs)
    refine ⟨g, hg, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [smul_eq_mul, q]
    exact (QuotientGroup.mk_mul_of_mem g hy).symm
  have hout : ∀ Q ∈ q '' S, Q.out ∈ S := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hh]; exact hSK s hs h h.2
  obtain ⟨T, hT⟩ : ∃ T : Finset (G ⧸ K), ∀ Q, Q ∈ T ↔ Q ∈ q '' S :=
    ⟨hfin.toFinset, fun Q => hfin.mem_toFinset⟩
  have hSeq : S = ⋃ Q ∈ T, Q.out • (K : Set G) := by
    ext g
    simp only [Set.mem_iUnion, hT, exists_prop]
    constructor
    · intro hg
      refine ⟨q g, ⟨g, hg, rfl⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨h⁻¹, (h⁻¹).2, ?_⟩
      simp [q, hh, mul_assoc]
    · rintro ⟨Q, hQ, y, hy, rfl⟩
      exact hSK _ (hout Q hQ) y hy
  have hconst : ∀ Q ∈ q '' S, ∀ y ∈ Q.out • (K : Set G), f y = f Q.out := by
    rintro Q hQ _ ⟨y, hy, rfl⟩
    exact hf _ (hout Q hQ) y hy
  refine ⟨T, ?_⟩
  rw [hSeq, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [hT] at hQ
    rw [setIntegral_congr_fun (hKo.smul _).measurableSet (hconst Q hQ), setIntegral_const,
      measureReal_def, measure_smul, ← measureReal_def, Complex.real_smul, mul_comm]
  · exact fun Q _ => (hKo.smul _).measurableSet
  · intro Q _ Q' _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
    apply hne
    have h1 : q (Q.out * y) = Q := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy]; exact QuotientGroup.out_eq' Q
    have h2 : q (Q'.out * y') = Q' := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy']; exact QuotientGroup.out_eq' Q'
    simp only [smul_eq_mul] at he
    rw [← h1, ← h2, he]
  · intro Q hQ
    rw [hT] at hQ
    refine (integrableOn_congr_fun (hconst Q hQ) (hKo.smul _).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_smul]; exact hKt

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem measureReal_eq_inv_natCast {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] {J K : Subgroup G}
    (hJc : IsCompact (J : Set G)) (hJ1 : μ J = 1) (hKo : IsOpen (K : Set G)) (hKJ : K ≤ J) :
    ∃ n : ℕ, μ.real K = (n : ℝ)⁻¹ := by
  have hKt : μ K ≠ ⊤ := ((measure_mono (show (K : Set G) ⊆ J from hKJ)).trans_lt (by simp [hJ1])).ne
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv μ K hKo hKt hJc (fun s hs k hk => J.mul_mem hs (hKJ hk))
    (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, measureReal_def, hJ1, Finset.sum_const, nsmul_eq_mul, one_mul] at ht
  simp only [ENNReal.toReal_one, one_smul] at ht
  refine ⟨t.card, eq_inv_of_mul_eq_one_right ?_⟩
  exact_mod_cast ht.symm

def rightStab {G : Type} [Group G] (S : Set G) : Subgroup G where
  carrier := {k | ∀ g, g ∈ S ↔ g * k ∈ S}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [ha g, hb (g * a), mul_assoc]
  inv_mem' := fun {a} ha g => by rw [ha (g * a⁻¹), inv_mul_cancel_right]

theorem isOpen_rightStab {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {S : Set G}
    (hSc : IsCompact S) (hSo : IsOpen S) : IsOpen (rightStab S : Set G) := by
  obtain ⟨V, hV, hSV⟩ := compact_open_separated_mul_right hSc hSo subset_rfl
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem hV (inv_mem_nhds_one G hV)) ?_)
  rintro k ⟨hk, hk'⟩ g
  refine ⟨fun hg => hSV (Set.mul_mem_mul hg hk), fun hg => ?_⟩
  have := hSV (Set.mul_mem_mul hg hk')
  rwa [mul_inv_cancel_right] at this

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A' : Type} [Fintype A'] [DecidableEq A']

def matBall (x : Matrix A' A' k) (c : kˣ) : Set (Matrix A' A' k) :=
  {y | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)}

theorem matBall_eq_preimage (x : Matrix A' A' k) (c : kˣ) :
    matBall x c = ⋂ i, ⋂ j, (fun y : Matrix A' A' k => (y i j - x i j) / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  ext y
  simp only [matBall, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
    Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]

theorem isOpen_matBall (x : Matrix A' A' k) (c : kˣ) : IsOpen (matBall x c) := by
  rw [matBall_eq_preimage]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    IsOpen.preimage (by fun_prop) Valuation.isOpen_integer

theorem isCompact_matBall (x : Matrix A' A' k) (c : kˣ) : IsCompact (matBall x c) := by
  have hc : (c : k) ≠ 0 := c.ne_zero
  have e : matBall x c = (fun A : Matrix A' A' k => (c : k) • A + x) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨fun i j => (y i j - x i j) / (c : k), fun i j => ?_, ?_⟩
      · have := (matBall_eq_preimage x c ▸ hy : y ∈ _)
        simp only [Set.mem_iInter, Set.mem_preimage] at this
        exact this i j
      · ext i j
        show (c : k) * ((y i j - x i j) / (c : k)) + x i j = y i j
        rw [mul_div_cancel₀ _ hc, sub_add_cancel]
    · rintro ⟨A, hA, rfl⟩ i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_right, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))
  rw [e]
  exact isCompact_intMatrix.image (by fun_prop)

theorem isCompact_isOpen_glBall (x : Matrix A' A' k) (c : kˣ) (hdet : ∀ y ∈ matBall x c, y.det ≠ 0) :
    IsCompact {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} ∧
    IsOpen {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
  have e : {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} =
      (fun g : GL A' k => g.val) ⁻¹' matBall x c := rfl
  rw [e]
  refine ⟨?_, (isOpen_matBall x c).preimage Units.continuous_val⟩
  rw [isEmbedding_val_GL.isInducing.isCompact_iff]
  convert isCompact_matBall x c using 1
  ext y
  refine ⟨fun ⟨g, hg, hgy⟩ => hgy ▸ hg, fun hy => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero y (hdet y hy), hy, rfl⟩⟩

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

theorem integral_glBall_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (ν : kˣ →* ℂˣ) (z : ℂ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u z ∈ F) → ∀ (c : kˣ) (x : Matrix A' A' k), (∀ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)) → y.det ≠ 0) → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
  intro k _ _ _ _ _ _ A' _ _ F J hJo hJK ν z ϖ e _ hcond hνF hapF c x hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := isCompact_isOpen_glBall x c hdet
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  set K : Subgroup (GL A' k) := J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (stdLat k A') ⊓ rightStab S with hKdef
  have hKo : IsOpen (K : Set (GL A' k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (isOpen_rightStab hSc hSo)
  have hKJ : K ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A' k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K ≠ ⊤ :=
    ((measure_mono (show (K : Set (GL A' k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K, ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) z) =
      (ν (gdet s) : ℂ) * apow (gdet s) z := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv (haarVol J) K hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs) (fun g => (ν (gdet g) : ℂ) * apow (gdet g) z) hinv
  rw [ht]
  obtain ⟨n, hn⟩ := measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  refine Subfield.sum_mem _ fun Q _ => F.mul_mem (F.mul_mem (hνF _) (hapF _)) ?_
  rw [hn]
  push_cast
  exact F.inv_mem (natCast_mem F n)

end GlobalTheory.GLBallInt
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.TrCopy

theorem eq_bot_or_eq_of_starProjection_eq_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U U' : Submodule ℂ H} [U'.HasOrthogonalProjection] (hle : U' ≤ U) (a : ℂ)
    (hPU : ∀ v ∈ U, U'.starProjection v = a • v) {u0 : H} (hu0 : u0 ∈ U) (hne : u0 ≠ 0) : U' = ⊥ ∨ U' = U := by
  have haa : a * a = a := by
    have h1 : U'.starProjection (U'.starProjection u0) = U'.starProjection u0 :=
      (Submodule.starProjection_eq_self_iff (K := U')).2 (U'.starProjection_apply_mem _)
    rw [hPU _ hu0, map_smul, hPU _ hu0, smul_smul] at h1
    exact smul_left_injective ℂ hne h1
  rcases mul_eq_zero.1 (show a * (a - 1) = 0 by rw [mul_sub, haa, mul_one, sub_self]) with h0 | h1
  · left
    refine (Submodule.eq_bot_iff U').2 fun v hv => ?_
    rw [← (Submodule.starProjection_eq_self_iff (K := U')).2 hv, hPU v (hle hv), h0, zero_smul]
  · right
    refine le_antisymm hle fun v hv => ?_
    have hv' : U'.starProjection v = v := by rw [hPU v hv, sub_eq_zero.1 h1, one_smul]
    exact hv' ▸ U'.starProjection_apply_mem v

theorem eq_smul_on_closure_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : Set H) (P : H →L[ℂ] H) (a : ℂ)
    (hP : ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v ∈ (Submodule.span ℂ s).topologicalClosure)
    (h : ∀ u ∈ s, ∀ u' ∈ s, ⟪u', P u - a • u⟫_ℂ = 0) :
    ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v = a • v := by
  set A := Submodule.span ℂ s with hA
  let Q : H →L[ℂ] H := P - a • ContinuousLinearMap.id ℂ H
  have hQ : ∀ v, Q v = P v - a • v := fun v => rfl
  have hQA : ∀ v ∈ A, Q v ∈ Aᗮ := by
    intro v hv
    refine (Submodule.span_le (p := Aᗮ.comap (Q : H →ₗ[ℂ] H))).2 ?_ hv
    intro u hu
    show Q u ∈ Aᗮ
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hle : A ≤ (ℂ ∙ Q u)ᗮ := Submodule.span_le.2 (by
      intro u' hu'
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hQ]
      exact h u hu u' hu')
    exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hx))
  have hQcl : ∀ v ∈ A.topologicalClosure, Q v ∈ Aᗮ := fun v hv =>
    (Submodule.topologicalClosure_minimal (s := A) (t := Aᗮ.comap (Q : H →ₗ[ℂ] H)) (fun u hu => hQA u hu)
      ((Submodule.isClosed_orthogonal A).preimage Q.continuous)) hv
  have hcl : A.topologicalClosure ≤ Aᗮᗮ :=
    Submodule.topologicalClosure_minimal _ A.le_orthogonal_orthogonal (Submodule.isClosed_orthogonal _)
  intro v hv
  have h1 : Q v ∈ A.topologicalClosure := by
    rw [hQ]
    exact sub_mem (hP v hv) (Submodule.smul_mem _ _ hv)
  have h2 : ⟪Q v, Q v⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal (hQcl v hv) (hcl h1)
  rw [inner_self_eq_zero, hQ, sub_eq_zero] at h2
  exact h2

theorem isIrredSubrep_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : Type)
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)),
    IsUnitaryRep ρ → ∀ U : Submodule ℂ H, IsCopyFinDS σ M ρ U → IsIrredSubrep ρ U := by
  intro D V S M W _ _ σ hirr hadm H _ _ _ ρ hρ U hU
  classical
  obtain ⟨T, hT, hinj, rfl⟩ := hU
  have hTm := mem_homTensorPi.1 hT
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M

  have hgen : ∀ g w y, ρ g (T w y) ∈ Submodule.span ℂ {v | ∃ w y, v = T w y} := by
    intro g w y
    have e1 := GlobalTheory.TrAct.toInf_apply_homDS D V S M H ρ ⊤ (T (σ (toFin V g) w)) (hT.1 _) g y
    rw [hTm.2.1] at e1
    have e2 : ρ g (T w y) = ρ (toInf V g : GA D V) (ρ ((GfC V).subtype (toFin V g)) (T w y)) := by
      conv_lhs => rw [← toInf_mul_toFin g]
      rw [map_mul]
      rfl
    rw [e2, e1]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  have hsub : IsSubrep ρ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    isSubrep_topologicalClosure fun g v hv => Submodule.mem_comap.1
      ((Submodule.span_le (p := Submodule.comap (ρ g : H →ₗ[ℂ] H) _)).2
        (by rintro _ ⟨w, y, rfl⟩; exact hgen g w y) hv)

  obtain ⟨w0, hw0⟩ : ∃ w : W, w ≠ 0 := by
    by_contra h
    push Not at h
    have hne : (⊥ : Subrepresentation σ) ≠ ⊤ := bot_ne_top
    exact hne (by ext v; simp [h v])
  have hTw0 : T w0 ≠ 0 := fun h => hw0 (hinj (h.trans (map_zero T).symm))
  obtain ⟨y0, hy0⟩ : ∃ y, T w0 y ≠ 0 := by
    by_contra h
    push Not at h
    exact hTw0 (ContinuousMultilinearMap.ext h)
  have hu0 : T w0 y0 ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w0, y0, rfl⟩)
  refine ⟨hsub, fun h => hy0 ((Submodule.mem_bot ℂ).1 (h ▸ hu0)), fun U' hU'le hU' => ?_⟩
  haveI : CompleteSpace U' := hU'.1.completeSpace_coe

  have hPc : ∀ g v, U'.starProjection (ρ g v) = ρ g (U'.starProjection v) := by
    intro g v
    have h1 : ρ g (U'.starProjection v) ∈ U' := hU'.2 g _ (U'.starProjection_apply_mem v)
    have h2 : ρ g (v - U'.starProjection v) ∈ U'ᗮ :=
      (hU'.orthogonal hρ).2 g _ (Submodule.sub_starProjection_mem_orthogonal (K := U') v)
    have e : ρ g v = ρ g (U'.starProjection v) + ρ g (v - U'.starProjection v) := by
      rw [← map_add (f := _), add_sub_cancel]
    rw [e, map_add (f := _), (Submodule.starProjection_eq_self_iff (K := U')).2 h1,
      (Submodule.starProjection_apply_eq_zero_iff U').2 h2, add_zero]

  obtain ⟨T', hT'a⟩ : ∃ T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H, ∀ w y, T' w y = U'.starProjection (T w y) :=
    ⟨(ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H U'.starProjection).toLinearMap ∘ₗ T,
      fun _ _ => rfl⟩
  have hΦ' : ∀ w, T' w ∈ homDS M ρ ⊤ := fun w => mem_homPi.2 ⟨fun _ => trivial, fun τ g y => by
    rw [hT'a, hT'a, (hT.1 w).2 τ g y, hPc]⟩

  let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  let C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T' v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
    bePi_self_pos hδ hρ (hT.1 x) ((map_ne_zero_iff T hinj).2 hx)
  have hBinv : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g v w => by
    change ⟪T (σ g w) _, T (σ g v) _⟫_ℂ = _
    rw [hTm.2.1, hTm.2.1, inner_map_map hρ]
    rfl
  have hCinv : ∀ g x y, C (σ g x) (σ g y) = C x y := fun g v w => by
    change ⟪T (σ g w) _, T' (σ g v) _⟫_ℂ = _
    rw [hT'a, hTm.2.1, hTm.2.1, hPc, inner_map_map hρ, ← hT'a]
    rfl
  obtain ⟨K, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨φ, hφ, hC⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K hKo hKc W W σ σ hadm hadm.1 B C hBpos hBinv hCinv
  obtain ⟨c, hc⟩ := GlobalTheory.SchurAdm.schur_admissible (GfC V) K hKo hKc W σ hirr hadm φ hφ
  have key : ∀ x y, bePi (T' x) (T y) = conj c * bePi (T x) (T y) := fun x y => by
    have := hC x y
    rw [hc, LinearMap.smul_apply, LinearMap.id_apply, map_smulₛₗ, smul_eq_mul] at this
    exact this
  have hgen2 : ∀ u ∈ {v | ∃ w y, v = T w y}, ∀ u' ∈ {v | ∃ w y, v = T w y},
      ⟪u', U'.starProjection u - conj c • u⟫_ℂ = 0 := by
    rintro _ ⟨w, z, rfl⟩ _ ⟨w', z', rfl⟩
    rw [inner_sub_right, inner_smul_right, ← hT'a, inner_eq_bePi hδ hρ (hΦ' w) (hT.1 w'),
      inner_eq_bePi hδ hρ (hT.1 w) (hT.1 w'), key, mul_assoc, sub_self]
  exact eq_bot_or_eq_of_starProjection_eq_smul hU'le (conj c)
    (eq_smul_on_closure_span _ U'.starProjection (conj c) (fun v _ => hU'le (U'.starProjection_apply_mem v)) hgen2)
    hu0 hy0

end GlobalTheory.TrCopy
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

theorem _root_.GlobalTheory.T.factorisable_restricted_tensor_level : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation σ J (fun v => (R v).π) ξ π B → ∀ (Kp : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GLoc σ J v)), (∀ᶠ v in cofinite, ∀ k ∈ Kp v, (R (.inr v)).π k (ξ (.inr v)) = ξ (.inr v)) → ∀ x : H, (∀ v, ∀ k ∈ Kp v, π (emb σ J v k) x = x) → x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, ∀ k ∈ Kp v, (R (.inr v)).π k (y (.inr v)) = y (.inr v)) ∧ z = B y}).topologicalClosure := by
  first | exact @GlobalTheory.FixedSpan.mem_closure_span_fixed | exact GlobalTheory.FixedSpan.mem_closure_span_fixed | (intros; apply GlobalTheory.FixedSpan.mem_closure_span_fixed <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  first | exact @GlobalTheory.TrAct.toInf_apply_homDS | exact GlobalTheory.TrAct.toInf_apply_homDS | (intros; apply GlobalTheory.TrAct.toInf_apply_homDS <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

theorem _root_.GlobalTheory.T.span_values_dense_finitePartSubrep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  first | exact @GlobalTheory.TrFinDense.span_values_dense | exact GlobalTheory.TrFinDense.span_values_dense | (intros; apply GlobalTheory.TrFinDense.span_values_dense <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.exists_irreducible_admissible_localComponent_finiteAdelic : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N), π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  first | exact @GlobalTheory.LocCompFin.exists_locComp | exact GlobalTheory.LocCompFin.exists_locComp | (intros; apply GlobalTheory.LocCompFin.exists_locComp <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

theorem _root_.GlobalTheory.T.finiteDimensional_homDS_closure_span_restricted : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ (R : ∀ v, IrrU (GPl D.sp.cm.sig V.gram v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation D.sp.cm.sig V.gram (fun v => (R v).π) ξ π B → ∀ (Q : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Submodule ℂ (R (.inr v)).H), (∀ v, FiniteDimensional ℂ (Q v)) → (∀ᶠ v in cofinite, Q v ≤ ℂ ∙ ξ (.inr v)) → FiniteDimensional ℂ (homDS M π (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, y (.inr v) ∈ Q v) ∧ z = B y}).topologicalClosure) := by
  first | exact @GlobalTheory.PureDS.finiteDimensional_homDS_closure_span | exact GlobalTheory.PureDS.finiteDimensional_homDS_closure_span | (intros; apply GlobalTheory.PureDS.finiteDimensional_homDS_closure_span <;> assumption)
end
