module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle080
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstVandermondeNodeLargeOfSmallThreshold
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle199
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle200
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
import Formalism.FormalDegreeBessel.StatementWR
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

noncomputable section

open Formalism.HermitianLatticeCounting.P

namespace GlobalTheory.DegCnt.WnLat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

def pr : V →ₗ[K] V := LinearMap.id - NFGeom.proj N

theorem pr_add (x : V) : pr N x + NFGeom.proj N x = x := by simp [pr]

theorem Wn_perp_Ist {y : V} (hy : y ∈ N.Wn) : ∀ u ∈ N.Ist, H.B y u = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).2

theorem Wn_perp_II {y : V} (hy : y ∈ N.Wn) {x : V} (hx : x ∈ II N.F N.F') : H.B y x = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).1 x (Submodule.mem_sup_left hx.1)

theorem pr_of_Wn {y : V} (hy : y ∈ N.Wn) : pr N y = y := by
  simp [pr, NFGeom.proj_zero N (Wn_perp_Ist N hy)]

theorem pr_II {x : V} (hx : x ∈ II N.F N.F') : pr N x = 0 := by
  simp [pr, NFGeom.proj_II N hx]

theorem pr_mem_Wn {x : V} (hx : x ∈ uPerp N.F N.F') : pr N x ∈ N.Wn :=
  (NFGeom.mem_perp_sup _ _ _).2
    ⟨Submodule.sub_mem _ hx (NFGeom.II_le_uPerp N (NFGeom.proj_mem N x)), NFGeom.sub_proj_perp N x⟩

theorem Wn_le_uPerp : N.Wn ≤ uPerp N.F N.F' := by
  rw [NFGeom.uPerp_eq N]; exact le_sup_left

theorem orthogonal_perp_z {w : V} (hw : w ∈ N.Wt) : H.B w N.F.z = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hw).1 _ (lastVector_mem_jointSpan_left N.F N.F')

theorem zz : H.B N.F.z N.F.z = -N.F.T := N.F.zz

theorem nondeg_Wn [FiniteDimensional K V] (x : V) (hx : x ∈ N.Wn) (h : ∀ y ∈ N.Wn, H.B x y = 0) :
    x = 0 := by
  have hx' := hx
  rw [NFGeom.Wn_eq N, Submodule.mem_sup] at hx'
  obtain ⟨w, hw, u, hu, rfl⟩ := hx'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
  have hz := h _ (NFGeom.z_mem_Wn N)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, orthogonal_perp_z N hw,
    zz] at hz
  have ht : t = 0 := by
    have := N.F.hT
    simp at hz
    exact hz.resolve_right this
  subst ht
  simp only [zero_smul, add_zero] at h ⊢
  by_contra h0
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hwW : w ∈ N.Wn := by rw [NFGeom.Wn_eq N]; exact Submodule.mem_sup_left hw
  have := NFGeom.Wt_pos N σ hw h0
  rw [h w hwW] at this
  simp at this

theorem z_ne : N.F.z ≠ 0 := fun h => N.F.hT (by
  have := zz N
  rw [h] at this
  simpa using this.symm)

theorem hermFramePair_middleSpace_inf_span_z_eq_bot : N.Wt ⊓ Submodule.span K {N.F.z} = ⊥ :=
  eq_bot_iff.2 fun x hx => (Submodule.mem_bot K).2 <| by
    obtain ⟨hw, hz⟩ := hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h := orthogonal_perp_z N hw
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, zz] at h
    have := N.F.hT
    rcases mul_eq_zero.1 h with h1 | h1
    · simp [h1]
    · exact absurd (neg_eq_zero.1 h1) this

theorem finrank_Wn [FiniteDimensional K V] : Module.finrank K N.Wn + 2 * r = Module.finrank K V := by
  have h1 := NFGeom.finrank_Wt N
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq N.Wt (Submodule.span K {N.F.z})
  rw [hermFramePair_middleSpace_inf_span_z_eq_bot, finrank_bot, finrank_span_singleton (z_ne N), ← NFGeom.Wn_eq N] at h2
  omega

def hW [FiniteDimensional K V] : HermSpace K N.Wn where
  B := H.B.domRestrict₁₂ N.Wn N.Wn
  herm x y := H.herm x y
  nondeg x hx := Submodule.coe_eq_zero.1 (nondeg_Wn N x x.2 fun y hy => hx ⟨y, hy⟩)

theorem hW_B [FiniteDimensional K V] (x y : N.Wn) : (hW N).B x y = H.B x y := rfl

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt.WnLat

open Formalism.HermitianLatticeCounting.P

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem unimod (L : Submodule (𝓞 K) V) (hL : IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F')) :
    GlobalTheory.HermLat.IsUnimod (hW N) (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  obtain ⟨⟨⟨N0, hN0, hLeq⟩, hspanL⟩, hdL⟩ := hL
  set M := L.comap (N.Wn.subtype.restrictScalars (𝓞 K)) with hM
  have hIL : ∀ x ∈ II N.F N.F', x ∈ L := fun x hx => by
    rw [hLeq]; exact Submodule.mem_sup_right hx
  have hprL : ∀ x ∈ L, pr N x ∈ L := fun x hx => by
    have : pr N x = x - NFGeom.proj N x := by simp [pr]
    rw [this]; exact L.sub_mem hx (hIL _ (NFGeom.proj_mem N x))
  have hprW : ∀ x ∈ L, pr N x ∈ N.Wn := fun x hx => by
    refine pr_mem_Wn N ?_
    rw [← hspanL]; exact Submodule.subset_span hx
  have hS : L ⊓ rs (𝓞 K) N.Wn = N0.map ((pr N).restrictScalars (𝓞 K)) := by
    apply le_antisymm
    · rintro x ⟨hxL, hxW⟩
      have hxL' := hxL
      rw [hLeq] at hxL'
      obtain ⟨n, hn, i, hi, rfl⟩ := Submodule.mem_sup.1 hxL'
      refine ⟨n, hn, ?_⟩
      show pr N n = n + i
      have h1 : pr N (n + i) = n + i := pr_of_Wn N hxW
      rwa [map_add, pr_II N hi, add_zero] at h1
    · rintro _ ⟨n, hn, rfl⟩
      have hnL : n ∈ L := by rw [hLeq]; exact Submodule.mem_sup_left hn
      exact ⟨hprL n hnL, hprW n hnL⟩
  have hmap : M.map (N.Wn.subtype.restrictScalars (𝓞 K)) = L ⊓ rs (𝓞 K) N.Wn := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
    · rintro ⟨hxL, hxW⟩; exact ⟨⟨x, hxW⟩, hxL, rfl⟩
  have hfg : M.FG := by
    refine Submodule.fg_of_fg_map_injective (N.Wn.subtype.restrictScalars (𝓞 K)) Subtype.val_injective ?_
    rw [hmap, hS]; exact hN0.map _
  have hspan : Submodule.span K (M : Set N.Wn) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := N.Wn.subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_subtype_top]
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨y, _, rfl⟩; exact y.2
    · intro w hw
      have h1 : w ∈ Submodule.span K (L : Set V) := by rw [hspanL]; exact Wn_le_uPerp N hw
      have h2 : pr N w ∈ (Submodule.span K (L : Set V)).map (pr N) := Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, pr_of_Wn N hw] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨pr N x, hprW x hx⟩, hprL x hx, rfl⟩
  have hdual : dual (hW N) M = M := by
    ext y
    rw [mem_dual_iff, hspan]
    simp only [Submodule.mem_top, true_and]
    constructor
    · intro h
      show (y : V) ∈ L
      rw [← hdL, mem_dual_iff, hspanL]
      refine ⟨Wn_le_uPerp N y.2, fun x hx => ?_⟩
      have h1 := h ⟨pr N x, hprW x hx⟩ (hprL x hx)
      rw [hW_B] at h1
      rw [← pr_add N x, map_add (f := _), Wn_perp_II N y.2 (NFGeom.proj_mem N x), add_zero]
      exact h1
    · intro hy x hx
      rw [hW_B]
      have : (y : V) ∈ dual H L := by rw [hdL]; exact hy
      exact ((mem_dual_iff H L y).1 this).2 x hx
  exact ⟨⟨⟨M, hfg, by simp [rs]⟩, hspan⟩, hdual⟩

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt

theorem NF.wnUnimod : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r) (L : Submodule (𝓞 K) V), IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → ∃ HW : HermSpace K N.Wn, (∀ x y : N.Wn, HW.B x y = H.B x y) ∧ Module.finrank K N.Wn + 2 * r = Module.finrank K V ∧ GlobalTheory.HermLat.IsUnimod HW (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N L hL
  exact ⟨WnLat.hW N, WnLat.hW_B N, WnLat.finrank_Wn N, WnLat.unimod N L hL⟩

end GlobalTheory.DegCnt
end
end

section

noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.FrameIntegral

theorem ef_one_of_split (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] (p : ℕ)
    (hall : ∀ W : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1)
    (Q : Ideal (𝓞 E)) (hQp : Q.IsPrime) (hQb : Q ≠ ⊥) (hpQ' : ((p : ℕ) : 𝓞 E) ∈ Q) :
    Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1 := by
  have hinjEL : Function.Injective (algebraMap (𝓞 E) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L)
  obtain ⟨W, -, hWp, hWQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) Q ⊥
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinjEL)]; exact bot_le)
  have hWb : W ≠ ⊥ := by
    intro h0; apply hQb; rw [← hWQ, h0]
    exact Ideal.comap_bot_of_injective _ hinjEL
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    have : algebraMap (𝓞 E) (𝓞 L) ((p : ℕ) : 𝓞 E) ∈ W := by
      change ((p : ℕ) : 𝓞 E) ∈ Ideal.under (𝓞 E) W
      rw [hWQ]; exact hpQ'
    simpa using this
  obtain ⟨h1, h2⟩ := hall ⟨W, hWp, hWb⟩ hpW
  have : W.LiesOver Q := ⟨hWQ.symm⟩
  have h1' : W.ramificationIdx ℤ = 1 := h1
  have h2' : W.inertiaDeg ℤ = 1 := h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) Q W] at h1'
  rw [Ideal.inertiaDeg_tower (R := ℤ) Q W] at h2'
  exact ⟨(mul_eq_one.mp h1').1, (mul_eq_one.mp h2').1⟩

theorem not_dvd_absNorm_different (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (hram : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1) :
    ¬ p ∣ Ideal.absNorm (differentIdeal ℤ (𝓞 K)) := by
  have key : ∀ I : Ideal (𝓞 K), I ∣ differentIdeal ℤ (𝓞 K) → ¬ p ∣ Ideal.absNorm I := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro h
      exact absurd (zero_dvd_iff.1 h) (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))
    | h₂ x hx =>
      intro _
      rw [Ideal.isUnit_iff.1 hx, Ideal.absNorm_top]
      exact hp.not_dvd_one
    | h₃ a P ha hP ih =>
      intro hdvd hpd
      rw [map_mul] at hpd
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
      · have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
        have hPb : P ≠ ⊥ := hP.ne_zero
        have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal hPp hPb
        have hfin : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPb
        have hcard : Ideal.absNorm P = Nat.card (𝓞 K ⧸ P) := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        rw [hcard] at h
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
        let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
        have hx0 : x ≠ 0 := by
          rintro rfl; rw [addOrderOf_zero] at hx; exact hp.one_lt.ne hx
        have hpx : (p : 𝓞 K ⧸ P) * x = 0 := by
          rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
        have hp0 : (p : 𝓞 K ⧸ P) = 0 := (mul_eq_zero.1 hpx).resolve_right hx0
        have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hp0
        have he := hram P hPp hPb hpP
        have hun : Algebra.IsUnramifiedAt ℤ P := Ideal.ramificationIdx_eq_one_iff.mp he
        exact (not_dvd_differentIdeal_iff.2 hun) (dvd_of_mul_right_dvd hdvd)
      · exact ih (dvd_of_mul_left_dvd hdvd) h
  exact key _ dvd_rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coprime_gi (i : Fin 2) : Nat.Coprime (Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))) (D.host.g i) := by
  have hall : ∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1 := fun W hW =>
    (GlobalTheory.unramified_degree_one_of_ncard_placesOver D.host.E _ (D.host.g_prime i) (D.nd.g_split i) W hW).2
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (D.host.g_prime i)).2 ?_)
  refine not_dvd_absNorm_different D.host.F _ (D.host.g_prime i) fun P hPp hPb hpP => ?_
  exact (ef_one_of_split D.host.F D.host.E _ hall P hPp hPb hpP).1

end GlobalTheory.FrameIntegral
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelUpper

theorem root_le (ka rd g Q b Cg m k : ℝ) (hb1 : 1 < b) (hm : 2 ≤ m) (hmk : 40 * m ^ 2 ≤ k)
    (hka0 : 0 < ka) (hki : ka⁻¹ ≤ b) (hrd1 : 1 ≤ rd) (hg0 : 0 ≤ g) (hgg : g ≤ b ^ (2 * Cg)) (hCg : 0 ≤ Cg)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ b ^ (10 * k * m)) :
    (ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q) ^
      ((1 : ℝ) / k) ≤ b ^ ((4 * Cg + 12) * m) := by
  have hb0 : 0 < b := by linarith
  have hk0 : 0 < k := by nlinarith
  have hkm : 0 ≤ k * m := by positivity
  have hE1a : 0 ≤ (m - 1) * k + m * (m - 1) / 2 := by nlinarith
  have hE1b : (m - 1) * k + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hE3a : 0 ≤ k * m + m * (m - 1) / 2 := by nlinarith
  have hE3b : k * m + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hP1 : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) ≤ b ^ (3 / 2 * (k * m)) := by
    rw [Real.rpow_neg hka0.le, ← Real.inv_rpow hka0.le]
    calc ka⁻¹ ^ ((m - 1) * k + m * (m - 1) / 2) ≤ b ^ ((m - 1) * k + m * (m - 1) / 2) :=
          Real.rpow_le_rpow (by positivity) hki hE1a
      _ ≤ b ^ (3 / 2 * (k * m)) := Real.rpow_le_rpow_of_exponent_le hb1.le hE1b
  have hP10 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) := Real.rpow_nonneg hka0.le _
  have hP2 : rd ^ (-((m - 1) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrd1 (by linarith)
  have hP20 : 0 ≤ rd ^ (-((m - 1) / 2)) := Real.rpow_nonneg (by linarith) _
  have hP3 : g ^ (k * m + m * (m - 1) / 2) ≤ b ^ (3 * Cg * (k * m)) := by
    calc g ^ (k * m + m * (m - 1) / 2) ≤ (b ^ (2 * Cg)) ^ (k * m + m * (m - 1) / 2) :=
          Real.rpow_le_rpow hg0 hgg hE3a
      _ = b ^ (2 * Cg * (k * m + m * (m - 1) / 2)) := (Real.rpow_mul hb0.le _ _).symm
      _ ≤ b ^ (3 * Cg * (k * m)) := by
        apply Real.rpow_le_rpow_of_exponent_le hb1.le
        nlinarith
  have hP30 : 0 ≤ g ^ (k * m + m * (m - 1) / 2) := Real.rpow_nonneg hg0 _
  have hX0 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q := by positivity
  have hXb : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
    calc ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q
        ≤ b ^ (3 / 2 * (k * m)) * 1 * b ^ (3 * Cg * (k * m)) * b ^ (10 * k * m) := by
          gcongr
      _ = b ^ (3 / 2 * (k * m) + 3 * Cg * (k * m) + 10 * k * m) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0]; ring
      _ ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1.le
          nlinarith
  calc _ ≤ (b ^ (k * ((4 * Cg + 12) * m))) ^ ((1 : ℝ) / k) :=
        Real.rpow_le_rpow hX0 hXb (by positivity)
    _ = b ^ ((4 * Cg + 12) * m) := by
        rw [← Real.rpow_mul hb0.le]
        congr 1
        field_simp

theorem tcrit_le_pow : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  intro hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 u τ
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hH := h.1
  obtain ⟨_, _, _, _, _, _, hm2L, _, _, _, hlogrd, hkg1, hg1, _, hg2, -⟩ := hH
  have hL : 1 ≤ large₂.sc.L := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hbexp : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hb1 : 1 < large₂.sc.b := by
    rw [hbexp]; exact lt_of_lt_of_le (by linarith) (Real.add_one_le_exp large₂.sc.L)
  have hb0 : 0 < large₂.sc.b := by linarith
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by have := D.R.two_le_m; exact_mod_cast this
  have hmk : 40 * (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ) := by
    have h1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right (by positivity) hL
    have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right h40 (by positivity)
    linarith
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by nlinarith

  have hCL : 1 ≤ Cl * large₂.sc.L := by nlinarith
  have hVV := Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT h.1 hCL τ
  have hlam0 : 0 < vand (lamSH D.R (D.hc τ)) :=
    Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb =>
      sub_pos.2 (Formalism.MainNotions.BridgeLemma.szh_anti h.1 τ (Finset.mem_filter.1 hb).2)
  have hvand : vand (lamSH D.R (D.hc τ)) ≤ Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) * vand (uS D u τ) :=
    GlobalTheory.RowVand.vand_lamSH_le D large₂ C' Cl Cg cb Cu cT CT C0 h h40 u τ
  have hexp : Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) = large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [hbexp, ← Real.exp_mul]; ring_nf
  rw [hexp] at hvand
  have hbp : 0 < large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := Real.rpow_pos_of_pos hb0 _
  have hu0 : 0 < vand (uS D u τ) := (pos_iff_pos_of_mul_pos (hlam0.trans_le hvand)).1 hbp
  have hQ0 : 0 ≤ VV D τ / vand (uS D u τ) := by rw [hVV]; positivity
  have hQ : VV D τ / vand (uS D u τ) ≤ large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [div_le_iff₀ hu0, hVV]; exact hvand

  have hrd1 : 1 ≤ D.host.rdE := by
    have h1 : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
    exact Real.one_le_rpow h1 (by positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    have hCl0 : 0 < Cl := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine hlogrd.trans ?_
      rw [div_le_iff₀ hCl0]; nlinarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd0).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr h1
      _ = large₂.sc.b := hbexp.symm

  have hka : D.host.ka = 2 * Real.pi / D.host.rdE := by
    show Real.pi / (D.host.rdE / 2) = 2 * Real.pi / D.host.rdE
    field_simp
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hki : D.host.ka⁻¹ ≤ large₂.sc.b := by
    rw [hka, inv_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]

  have hg1ge : 1 ≤ (D.host.g 0 : ℝ) :=
    le_trans (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hk1 hb1.le)) hkg1
  have hCg : 0 ≤ Cg := by
    by_contra hc
    push_neg at hc
    have := Real.rpow_lt_one_of_one_lt_of_neg hb1 hc
    linarith
  have hgg : gg D ≤ large₂.sc.b ^ (2 * Cg) := by
    rw [show 2 * Cg = Cg + Cg by ring, Real.rpow_add hb0]
    unfold gg
    exact mul_le_mul hg1 hg2 (by positivity) (by positivity)
  have hgg0 : 0 ≤ gg D := by unfold gg; positivity
  have key := root_le D.host.ka D.host.rdE (gg D) (VV D τ / vand (uS D u τ)) large₂.sc.b Cg D.R.m D.R.k
    hb1 hm hmk hka0 hki hrd1 hgg0 hgg hCg hQ0 hQ
  unfold Tcrit
  rw [mul_div_assoc]
  exact key

end GlobalTheory.CritLevelUpper
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.real_complex_span_orthonormal_skew_family : ∀ (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (s : Set (Fin d)), (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (B i)) → (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧ (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧ ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  first | exact @GlobalTheory.SkewSpan.real_span | exact GlobalTheory.SkewSpan.real_span | (intros; apply GlobalTheory.SkewSpan.real_span <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  first | exact @GlobalTheory.StabRing.exists_emb | exact GlobalTheory.StabRing.exists_emb | (intros; apply GlobalTheory.StabRing.exists_emb <;> assumption)
end
