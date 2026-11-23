module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle037
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle024
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PhiCountingHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitSk
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem gluing_vectors_exist : GlueVecsPre := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  have := h𝔭.isPrime
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  set W := orthK h U with hW
  set m := finrank K W with hm
  set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  have hPc : P.card < m := hc
  have hPm : ∀ i, (P.filter (· < i)).card < m := fun i =>
    lt_of_le_of_lt (Finset.card_filter_le _ _) hPc
  let τ : Fin (finrank K U) → Fin m := fun i => ⟨(P.filter (· < i)).card, hPm i⟩
  have hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k := by
    intro i k hi hk e
    exact card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)
  have hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m := by
    intro i hi
    have := card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    show (P.filter (· < i)).card + 1 < m
    omega
  choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))
  let t : Fin m → K := fun j =>
    if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1
  have hts : ∀ j, star (t j) = t j := by
    intro j; simp only [t]; split_ifs
    · exact star_fix hF _
    · exact star_one K
  have htp : ∀ j, TotPos (t j) := by
    intro j; simp only [t]; split_ifs
    · exact hnpos _
    · intro φ; rw [map_one]; simp
  have htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i) := by
    intro i hi
    have hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i := ⟨i, hi, rfl⟩
    simp only [t, dif_pos hj]
    rw [hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]
  have htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1 := by
    intro j hj
    have : ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j := fun ⟨i, hi, e⟩ => hj i hi e
    simp only [t, dif_neg this]
  let h' : W →ₗ⋆[K] W →ₗ[K] K := (LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)
  have h'a : ∀ x y : W, h' x y = h x y := fun x y => rfl
  have hsym' : ∀ x y : W, star (h' x y) = h' y x := by
    intro x y; rw [h'a, h'a, ← starRingEnd_apply]; exact hs.eq _ _
  have hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x) := by
    intro x hx φ; rw [h'a]; exact hpos x x.2 (fun e => hx (Subtype.ext e)) φ
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨v, ho, hv1, hvl⟩ := exists_presc_family hK h' hsym' hpos' (m - 1) (by omega)
    (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)
  let w : Fin m → V := fun j => (v (Fin.cast hm1.symm j) : V)
  have hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0 := by
    intro j k hjk
    exact ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))
  have hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j := by
    intro j hj
    have hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have := hv1 _ hne'
    simpa [w, h'a] using this
  have hwn0 : ∀ j, h (w j) (w j) ≠ 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < m
    · rw [hwn j hj]; exact TotPos.ne_zero' (htp j)
    · have hjl := j.isLt
      have hl : Fin.cast hm1.symm j = Fin.last (m - 1) := by
        ext; simp; omega
      have : v (Fin.cast hm1.symm j) ≠ 0 := by rw [hl]; exact hvl
      exact TotPos.ne_zero' (hpos' _ this)
  have hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x := fun j => by
    obtain ⟨x, hx⟩ := (hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))
    exact ⟨x, hx.symm⟩
  choose c hcw using hfix
  obtain ⟨π, s₀, hu⟩ := exists_isUnif0 h𝔭
  refine ⟨π, w, c, τ, fun j => (v _).2, hwo,
    fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩
  · intro i hi
    have e : algebraMap F K (c (τ i)) = algebraMap F K (nF i) := by
      rw [← hcw, hwn _ (hτl i hi), htpart i hi]
    rw [(algebraMap F K).injective e]
    exact hncong i
  · intro j hj hnp
    have e : c j = 1 := by
      apply (algebraMap F K).injective
      rw [← hcw, hwn j hj, htnp j hnp, map_one]
    rw [e, inv_one, map_one]
    exact ⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩

end Formalism.L2.SG.Pf.GluingBases
end
end

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.G5

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem alphaDisc_of (hP : PhiCount) (hKc : KerCount) (hD : DiscOnto) : AlphaDisc := by
  unfold AlphaDisc
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L hL hLi 𝔭 h𝔭 b a hJ
  have : Fact (IsFixF K F) := ⟨hF⟩
  have hk1 : 2 * vd h L 𝔭 + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk2 : 2 * vJof 𝔭 a + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk0 : 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have ha : ∀ i, a i ≠ 0 := hJ.2.2.2.2
  have hm : finrank K (⊤ : Submodule K V) = finrank K V := finrank_top K V
  have hlin : LinearIndependent K b :=
    Formalism.L2.SG.Pf.GluingBases.linearIndependent_orth h b hJ.2.2.1 (fun i => by
      rw [hJ.2.2.2.1 i]
      exact (map_ne_zero (algebraMap F K)).2 (by exact_mod_cast ha i))
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_span_eq_card hlin, Fintype.card_fin]
  have hfull : Submodule.IsFullLattice K L := by
    refine { toIsLattice := hL, span_eq_top := ?_ }
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Formalism.L2.SG.Pf.GluingBases.locF_subset_span h𝔭.isPrime L
    rw [← hJ.2.1]
    exact Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
  have hphi := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 0 (by simp) (fun i j => by simp)
  have hfib : ∀ T : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
      (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)))) →
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = T} =
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = 0} := by
    intro T hT hTm
    have h1 := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 T hT hTm
    exact_mod_cast h1.trans hphi.symm
  have hker := hKc K F hK 𝔭 h𝔭 _ a ha _ hk2 _ hfib
  have hdisc := hD K F V hK h hs hd L hL hLi 𝔭 h𝔭 b a hJ _ hk2
  have hpos : (0 : ℝ) < Ideal.absNorm 𝔭 := by exact_mod_cast Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.absNorm_pos h𝔭
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K (⊤ : Submodule K V) ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) := by
    have h1 := congrArg (fun m : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1))) hm
    rw [h1]
    ring
  have e2 : finrank K (⊤ : Submodule K V) - cJof 𝔭 a = finrank K V - cJof 𝔭 a :=
    congrArg (fun x => x - cJof 𝔭 a) hm
  rw [Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hfull hLi h𝔭 hk1, hdisc, hker, Nat.cast_mul, hphi, e1, e2]
  have hne : (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) ≠ 0 :=
    pow_ne_zero _ hpos.ne'
  field_simp

theorem alphaDisc_of_discOnto (hD : DiscOnto) : AlphaDisc :=
  alphaDisc_of Formalism.L2.SG.Pf.LocalizedFibreSets.phi_counting_holds
    (by
      unfold KerCount
      intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk N hN
      exact Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha hk N hN) hD

end Formalism.L2.SG.Pf.G5
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas.IntG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem base_lattice_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]
  exact le_sup_of_le_left le_sup_right

theorem Lb_le_aaLbS (b : Fin D.R.rS) : X.Lb ≤ aaLbS X b := fun l hl =>
  Submodule.subset_span ⟨1, one_mem_aaD b, l, hl, by rw [one_smul]⟩

theorem aaLbS_le_span (b : Fin D.R.rS) :
    aaLbS X b ≤ (Submodule.span D.host.E (X.Lb : Set (VS D).V)).restrictScalars (𝓞 D.host.E) := by
  unfold aaLbS
  rw [Submodule.span_le]
  rintro _ ⟨c, -, l, hl, rfl⟩
  exact Submodule.smul_mem _ c (Submodule.subset_span hl)

theorem span_aaLbS (b : Fin D.R.rS) :
    Submodule.span D.host.E (aaLbS X b : Set (VS D).V) = Submodule.span D.host.E (X.Lb : Set (VS D).V) :=
  le_antisymm (Submodule.span_le.2 (aaLbS_le_span X b)) (Submodule.span_mono (Lb_le_aaLbS X b))

theorem aaD_ne_zero' (b : Fin D.R.rS) : aaD D b ≠ 0 := by
  unfold aaD
  exact zpow_ne_zero _ ddS_ne_zero

theorem fg_aaLbS (b : Fin D.R.rS) : (aaLbS X b).FG := by
  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) ^ (D.R.rS - (b : ℕ)) with hNdef
  have hN : ((N : ℕ) : D.host.E) ∈ (aaD D b)⁻¹ := mem_aaD_inv b
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    refine pow_ne_zero _ ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  let f : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V := (N : 𝓞 D.host.E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((N : 𝓞 D.host.E) : D.host.E) • x = ((N : 𝓞 D.host.E) : D.host.E) • y := by
      rw [algebraMap_smul, algebraMap_smul]
      exact hxy
    have h2 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
      push_cast
      exact_mod_cast hN0
    exact smul_right_injective _ h2 h1
  have hle : (aaLbS X b).map f ≤ (VS D).L0 := by
    unfold aaLbS
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨c, hc, l, hl, rfl⟩, rfl⟩
    have hmul : ((N : ℕ) : D.host.E) * c ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E) := by
      have := FractionalIdeal.mul_mem_mul hN hc
      rwa [inv_mul_cancel₀ (aaD_ne_zero' b)] at this
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hmul
    have e : f (c • l) = o • l := by
      show (N : 𝓞 D.host.E) • (c • l) = o • l
      rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E), smul_smul, ← algebraMap_smul D.host.E o l, ho]
      push_cast
      rfl
    rw [e]
    exact base_lattice_le X (X.Lb.smul_mem o hl)
  haveI : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_fg_of_noetherian _ (VS D).standardTuple_isLattice.fg
  have hfg : ((aaLbS X b).map f).FG := (isNoetherian_submodule.1 inferInstance) _ hle
  exact Submodule.fg_of_fg_map_injective f hf hfg

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.FinVolSk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def KfOrb : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (X0 : Fin a → Fin n → E)
    (Λ : Set (Fin n → E)),
    IsCMExt F E σ → IsHermND σ J →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0} ∧
    ∀ x : Fin a → Fin n → Af F ⊗[F] E, (∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0) ↔
      ∀ v : HeightOneSpectrum (𝓞 F),
        projV v x ∈ {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) X0}

def LocSB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (X0 : Fin a → Fin n → E)
    (Λ : Set (Fin n → E)),
    IsCMExt F E σ → IsHermND σ J → (gramE σ J X0).det ≠ 0 →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∃ (d : ℕ) (b : Module.Basis (Fin d) F E)
      (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
      (∀ v, IsSB ((C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ))) ∧
      (∀ v, MeasurableSet (C v)) ∧
      (∀ v, C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))} =
        {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) X0}) ∧
      ∀ᶠ v in Filter.cofinite, C v = latV b v

def BoxVol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (a : ℕ)
    (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)),
    StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →
    Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → IsOmT F E σ n J ψ (gramE σ J X0) hT νX →
    ∀ (μinf : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)),
      SdW F E σ n J (Ainf F) (psiInf F ψ) a μinf → SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
      fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT) ≠ 0 →
      ∀ ωf : Measure (Fin a → Fin n → Af F ⊗[F] E),
        (∀ (A : (Fin a → Fin n → Ainf F ⊗[F] E) → ENNReal) (S : Set (Fin a → Fin n → Af F ⊗[F] E)),
          MeasurableSet S →
          ∫⁻ y, A (projInf y) * S.indicator 1 (projFin y) ∂νX =
            ωf S * ∫⁻ z, A z ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) →
        ωf {x | ¬ ∀ v : HeightOneSpectrum (𝓞 F),
          gramR (Fv F v) σ J (projV v x) = (gramE σ J X0).map (inclR (Fv F v))} = 0 ∧
        ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
          (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
          (∀ v, IsSB ((C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ))) →
          (∀ v, MeasurableSet (C v)) → (∀ᶠ v in Filter.cofinite, C v = latV b v) →
          ωf {x | ∀ v, projV v x ∈ C v} =
            ENNReal.ofReal (∏' v : HeightOneSpectrum (𝓞 F),
              (omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v)))
                (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal)

theorem omFinVol_of (h1 : KfOrb) (h2 : LocSB) (h3 : BoxVol) : Formalism.L2.SG.Pf.NcS.SplitSk.OmFinVol := by
  intro F E _ _ _ _ _ σ n J ψ a X0 hT νX Λ μf hStd hdet ha hn hSWa hSWc hLat hOm _ _ _
  obtain ⟨hKYm, hKYiff⟩ := h1 F E σ n J a X0 Λ hStd.1 hStd.2.1 hLat
  refine ⟨hKYm, ?_⟩
  intro μinf νinf fibInf hμ hν hfib hne ωf hdec
  obtain ⟨hsupp, hbox⟩ := h3 F E σ n J ψ a X0 hT νX hStd hdet ha hn hSWa hSWc hOm μinf νinf fibInf hμ hν hfib
    hne ωf hdec
  obtain ⟨d, b, C, hSB, hCm, hCeq, hCa⟩ := h2 F E σ n J a X0 Λ hStd.1 hStd.2.1 hdet hLat
  have hae : ∀ᵐ x ∂ωf, ∀ v : HeightOneSpectrum (𝓞 F),
      gramR (Fv F v) σ J (projV v x) = (gramE σ J X0).map (inclR (Fv F v)) := ae_iff.2 hsupp
  have hset : ωf {x | ∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0} = ωf {x | ∀ v, projV v x ∈ C v} := by
    apply measure_congr
    filter_upwards [hae] with x hx
    show (∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0) ↔ ∀ v, projV v x ∈ C v
    constructor
    · intro h v
      have h' := (hKYiff x).1 h v
      rw [← hCeq v] at h'
      exact h'.1
    · intro h
      refine (hKYiff x).2 fun v => ?_
      rw [← hCeq v]
      exact ⟨h v, hx v⟩
  rw [hset, hbox d b C hSB hCm hCa]
  congr 1
  exact tprod_congr fun v => by rw [hCeq v]

end Formalism.L2.SG.Pf.NcS.FinVolSk
end
end
