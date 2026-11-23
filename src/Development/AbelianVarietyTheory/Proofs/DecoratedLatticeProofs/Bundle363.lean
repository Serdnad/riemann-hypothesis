module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle005
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle107
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdBNonneg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle341
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinIntBridge

theorem comm_symm_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm a ∈ GlobalTheory.AdelicU.intLoc F E v := by
  have hle : Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ≤
      (GlobalTheory.AdelicU.intLoc F E v).comap
      ((Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F ⊗[F] E) := by
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩)
    · obtain ⟨x, rfl⟩ := RingHom.mem_range.1 (show e ∈ (algebraMap (𝓞 E) E).range from he)
      simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (one_mem _) x
    · simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (a := b) hb 1
  exact hle ha

theorem prV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (y : AF F ⊗[F] E) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm (Formalism.UG.prV (E := E) v
      (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y))) =
      Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin F v) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_intLoc_of_finM : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D)), GlobalTheory.AdForm.finM V hn κ = x.1 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 i j ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) → ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v κ)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D V n hn κ x hx v h i j
  have h1 := comm_symm_mem v (h (finCongr hn i) (finCongr hn j))
  have h2 : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 (finCongr hn i) (finCongr hn j) =
      Formalism.UG.prV (E := D.host.E) v (toEAf D (Formalism.L2.Theta.mt V κ i j)) := by
    change Formalism.UG.prV (E := D.host.E) v (x.1 (finCongr hn i) (finCongr hn j)) = _
    rw [← hx]
    simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  rw [h2] at h1
  have h3 := prV_gen (F := D.host.F) (E := D.host.E) v (Formalism.L2.Theta.mt V κ i j)
  exact (congrArg (· ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) h3).mp h1

end GlobalTheory.FinIntBridge
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LatFwd

theorem finM_inv_eq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D))
    (h : GlobalTheory.AdForm.finM V hn κ = x.1) : GlobalTheory.AdForm.finM V hn κ⁻¹ = (x⁻¹).1 := by
  subst hn
  have e : GlobalTheory.AdForm.finM V rfl κ * GlobalTheory.AdForm.finM V rfl κ⁻¹ = 1 := by
    have e1 : ∀ g, GlobalTheory.AdForm.finM V rfl g = (mt V g).map (toEAf D) := fun g => rfl
    have e2 : mt V κ * mt V κ⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [e1, e1, ← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h] at e
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem proj_mem_stabLoc_std {D : D7} (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hM : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g⁻¹)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.stdLattice D.host.E V.rank) v := by
  rw [map_inv, map_inv] at hM'
  set M := GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)
  have hint : ∀ (N : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)),
      (∀ i j, N i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ z : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ i, z i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ i, (N *ᵥ z) i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hz j)
  refine GlobalTheory.AdelicU.mem_stabLoc.2 fun z => ?_
  simp only [GlobalTheory.AdelicU.mem_latLoc_stdLattice]
  refine ⟨fun hz => hint _ hM z hz, fun hz => ?_⟩
  have e : (M⁻¹).1 *ᵥ (M.1 *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e]
  exact hint _ hM' _ hz

end GlobalTheory.FamTrace.LatFwd

namespace GlobalTheory.FamTrace.LatFwd


end GlobalTheory.FamTrace.LatFwd

end
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CentralUnitGen

theorem scalar_keeps {R : Type} [CommRing R] {S : Subring R} {n : ℕ} (Λ : Submodule S (Fin n → R)) (w : Fin n → R)
    (Mt Mt' Mk Mki : Matrix (Fin n) (Fin n) R) (c c' : R)
    (h1 : Mt = (c • (1 : Matrix (Fin n) (Fin n) R)) * Mt' * Mk) (h2 : (c' * c) • (1 : Matrix (Fin n) (Fin n) R) = 1)
    (hkk : Mk * Mki = 1)
    (hk : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mk y ∈ Λ) (hki : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mki y ∈ Λ)
    (hw : ∀ c0 : R, ((∃ x ∈ Λ, Matrix.mulVec Mt x = c0 • w) ↔ c0 ∈ S) ∧ ((∃ x ∈ Λ, Matrix.mulVec Mt' x = c0 • w) ↔ c0 ∈ S)) :
    ∀ y, y ∈ Λ ↔ Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y ∈ Λ := by
  have e2 : Mt' * Mk = (c' • (1 : Matrix (Fin n) (Fin n) R)) * Mt := by
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, Matrix.one_mul]
  have hcI : c ∈ S := by
    obtain ⟨x', hx', ex'⟩ := ((hw 1).2).2 (one_mem _)
    refine ((hw c).1).1 ⟨Matrix.mulVec Mki x', (hki x').1 hx', ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.mul_assoc, Matrix.mul_assoc, hkk, Matrix.mul_one, ← Matrix.mulVec_mulVec, ex', one_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc'I : c' ∈ S := by
    obtain ⟨x, hx, ex⟩ := ((hw 1).1).2 (one_mem _)
    refine ((hw c').2).1 ⟨Matrix.mulVec Mk x, (hk x).1 hx, ?_⟩
    rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec, ex, one_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro y
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro hy
    exact Λ.smul_mem ⟨c, hcI⟩ hy
  · intro hy
    have h3 := Λ.smul_mem ⟨c', hc'I⟩ hy
    have e3 : (c' * c) • y = y := by
      have := congrArg (fun A => Matrix.mulVec A y) h2
      simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using this
    rw [← e3, mul_smul]
    exact h3

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.CentralUnitGen

theorem proj_mem_center {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : GlobalTheory.AdelicU.GAd σ J}
    (hg : g ∈ Subgroup.center (GlobalTheory.AdelicU.GAd σ J)) : GlobalTheory.AdelicU.proj σ J v g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc σ J v) := by
  refine Subgroup.mem_center_iff.2 fun x => ?_
  have e := congrArg (GlobalTheory.AdelicU.proj σ J v) (Subgroup.mem_center_iff.1 hg (GlobalTheory.AdelicU.emb σ J v x))
  rwa [map_mul, map_mul, GlobalTheory.AdelicU.proj_emb_self] at e

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.MiTop


end GlobalTheory.MiTop

end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberData


open Formalism.MainNotions.S in
theorem dataNW_of_val {C : Formalism.MainNotions.Inhab.FC} {cD ch : ℝ} (hC : Std C) {D : D7} (L : SizeData₂ D)
    (hV : Val C cD ch L) (hS : SizesAt L) (hR : ∀ u, GlobalTheory.Core.Rk.RankMu D u) : GlobalTheory.Core.Deg.DataNW D := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hk0 : 0 < D.R.k := by omega
  have hSc := Sc_eq' L
  have e1 : ∀ u τ, uOne D u τ 1 = (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := fun u τ => by
    rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 hk0, D.hcW_first u τ hk0]
  have e2 : ∀ τ, vOne D τ 1 = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := fun τ => vOne_succ τ 0 (by omega)
  have hCc : L.Cc = 2 := hV.Cc_eq.trans hC.2.1
  have hdu : ∀ u, 0 < D.duS u := fun u => by
    have h := hR u
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
    have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
    have hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := sub_pos.2 (one_lt_pow₀ hT (by omega))
    have h0 : (0 : ℝ) < D.duS u := by rw [h]; positivity
    exact_mod_cast h0
  refine ⟨data1 L, data2, ?_, ?_, ?_, ?_, data7, data8,
    fun u => ⟨GlobalTheory.CollCompare.splits_level D u, T_mod D u⟩, hdu,
    Formalism.L2.SG.ResidEvFree.splitsE_g D 0, Formalism.L2.SG.ResidEvFree.splitsE_g D 1,
    discriminant_eq_base_sq D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D),
    fun u => ne_of_mod (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le (T_mod D u)⟩
  · intro u τ
    rw [e1, e2, ← hSc]
    by_cases ht : Formalism.MainNotions.S.IsTop D τ
    · obtain ⟨t, ht⟩ := ht
      have h1 := (L.top_u τ t hk0 ht).1
      have h2 := (L.cloud_v τ ⟨0, by omega⟩).2
      have h3 := (L.aT_win t).1
      have h4 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_Sc_le hS
      have h5 := L.Sc_pos
      have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      rw [h1]
      linarith
    · have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).1
      push_cast at this
      exact this
  · intro u τ ht
    have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).2
    push_cast at this
    rw [hCc] at this
    rw [e1, e2]
    linarith
  · intro u τ ht
    have hv := hV.hc.1 τ ⟨D.R.k - 2, by omega⟩
    have hu := (hV.hc.2.1 τ hk0 (fun h => ht ((isTop_iff τ).2 h))).2
    have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
    have hv' := vOne_succ τ (D.R.k - 2) (by omega)
    rw [← e] at hv'
    rw [uOne_last u τ, hv', hv, hu]
    norm_num
  · intro τ ht
    obtain ⟨t, ht⟩ := ht
    have hm0 : 0 < D.R.m := by omega
    have eb : bOne D τ 1 = (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, bOne_succ τ 0 hm0]
    have et : bTop D τ = (L.bT t : ℝ) + ((D.R.k : ℝ) - 1) / 2 := by
      unfold bTop
      rw [uOne_last D.u₀ τ, (L.top_u τ t hk0 ht).2]
      ring
    have h1 := L.top_b τ t hm0 ht
    obtain ⟨b1, hb, htop, -, -⟩ := hV.hc.2.2.1
    have hb0 := (hb τ ⟨0, hm0⟩).1
    have hbt := htop τ t ht
    have hbR : (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
      rw [hb0, hbt]
      push_cast
      ring
    have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _
    have hb'0 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_b'_nonneg (L := L)
    have hx1 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_x_ge (L := L)
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx1
    have hbT := L.bT_ge t
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    rw [eb, et]
    constructor <;> linarith

theorem val_congr {C C' : Formalism.MainNotions.Inhab.FC} {cD cD' ch ch' : ℝ} {D : D7} {L : SizeData₂ D} (h1 : C = C') (h2 : cD = cD')
    (h3 : ch = ch') (h : Val C cD ch L) : Val C' cD' ch' L := by
  subst h1 h2 h3
  exact h

end GlobalTheory.Fam.MemberData

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.GapAt

theorem poly_bound {M k m f r L T n t N : ℝ} (hM : 1 ≤ M) (hk1 : 1 ≤ k) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hf0 : 0 ≤ f) (hf : f ≤ M) (hr0 : 0 ≤ r) (hr : r ≤ M) (hL0 : 0 ≤ L) (hL : L ≤ M) (hT : T ≤ M) (hn0 : 0 ≤ n)
    (hn : n ≤ 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) + 8) (ht0 : 0 ≤ t) (ht : t ≤ 8 * f * r + 4 + T * n)
    (hN : N = k + m * (t + 1)) : 4 * N ^ 3 + 2 * t + 6 ≤ 300000 * M ^ 30 := by
  have hM0 : 0 ≤ M := by linarith
  have hk' : 0 ≤ k - 1 := by linarith
  have hk'' : k - 1 ≤ M := by linarith
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b h => pow_le_pow_right₀ hM h
  have h1 : f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ M ^ 7 := by
    calc f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 := div_le_self (by positivity) hm1
      _ ≤ M ^ 2 * M ^ 3 * M ^ 2 := by gcongr
      _ = M ^ 7 := by ring
  have h10 : 0 ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m := by
    have : 0 ≤ m := by linarith
    positivity
  have h2 : n ≤ 28 * M ^ 8 := by
    have a1 : f ≤ M ^ 7 := by have := pw 1 7 (by norm_num); rw [pow_one] at this; linarith
    have a2 : r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) ≤ M * (2 * M ^ 7) :=
      mul_le_mul hr (by linarith) (by linarith) hM0
    have a3 : M * (2 * M ^ 7) = 2 * M ^ 8 := by ring
    have a4 := pw 0 8 (by norm_num)
    rw [pow_zero] at a4
    rw [mul_assoc] at hn
    linarith
  have h3 : t ≤ 40 * M ^ 9 := by
    have a1 : f * r ≤ M * M := mul_le_mul hf hr hr0 hM0
    have a2 : T * n ≤ M * (28 * M ^ 8) := mul_le_mul hT h2 hn0 hM0
    have a3 : M * (28 * M ^ 8) = 28 * M ^ 9 := by ring
    have a4 := pw 0 9 (by norm_num)
    have a5 := pw 2 9 (by norm_num)
    rw [pow_zero] at a4
    rw [pow_two] at a5
    rw [mul_assoc] at ht
    linarith
  have h4 : N ≤ 42 * M ^ 10 := by
    have a4 := pw 0 9 (by norm_num)
    rw [pow_zero] at a4
    have a1 : m * (t + 1) ≤ M * (41 * M ^ 9) := mul_le_mul hm (by linarith) (by linarith) hM0
    have a3 : M * (41 * M ^ 9) = 41 * M ^ 10 := by ring
    have a5 := pw 1 10 (by norm_num)
    rw [pow_one] at a5
    linarith
  have hN0 : 0 ≤ N := by
    rw [hN]
    have : 0 ≤ m * (t + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h5 : N ^ 3 ≤ 74088 * M ^ 30 := by
    calc N ^ 3 ≤ (42 * M ^ 10) ^ 3 := pow_le_pow_left₀ hN0 h4 3
      _ = 74088 * M ^ 30 := by ring
  have a4 := pw 0 30 (by norm_num)
  have a5 := pw 9 30 (by norm_num)
  rw [pow_zero] at a4
  linarith

theorem rank_bound (s : Scale) (R : Ranks) (h : RankVal s R) :
    4 * ((R.N R.m : ℕ) : ℝ) ^ 3 + 2 * R.t + 6 ≤ 300000 * (4 * s.x ^ (377 : ℝ)) ^ 30 := by
  obtain ⟨-, -, ⟨-, hk⟩, ht⟩ := h
  have hx := s.one_lt_alt.le
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hY : 1 ≤ s.x ^ (377 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hk2 : (R.k : ℝ) ≤ 2 * s.x ^ (377 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx (show 9 / 2 + 10 * s.eps ≤ (377 : ℝ) by linarith)
    linarith
  have hL : s.L ≤ s.x ^ (377 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (show s.eps ≤ (377 : ℝ) by linarith)
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg (by linarith) _
  have n1 := R.two_le_m
  have n2 := R.m_add_three_le_k
  have hm1 : (1 : ℝ) ≤ R.m := by exact_mod_cast (show 1 ≤ R.m by omega)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (show 1 ≤ R.k by omega)
  have hmk : (R.m : ℝ) ≤ R.k := by exact_mod_cast (show R.m ≤ R.k by omega)
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast (show R.f ≤ R.k from R.f_le_k)
  have hrk : (R.r : ℝ) ≤ 2 * R.k := by
    exact_mod_cast (show R.r ≤ 2 * R.k by unfold Ranks.r; omega)
  have hT : (TOv s : ℝ) ≤ 4 * s.x ^ (377 : ℝ) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ (377 : ℝ) by linarith)
    unfold TOv
    linarith
  have hn : (nWv R s : ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) + 8 := by
    have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have := Nat.ceil_lt_add_one
      (show 0 ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 by positivity)
    unfold nWv
    push_cast
    linarith
  have ht' : (R.t : ℝ) ≤ 8 * (R.f : ℝ) * R.r + 4 + (TOv s : ℝ) * nWv R s := by
    exact_mod_cast (show R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s by omega)
  refine poly_bound (by linarith) hk1 (by linarith) hm1 (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _)
    (by linarith) hL0 (by linarith) hT (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) ht' ?_
  unfold Ranks.N
  push_cast
  rfl

theorem nodeGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) : D.NodeGap (h0v L.sc ch : ℝ) := by
  intro u τ j hj
  obtain ⟨b1, hb, -⟩ := h.hc.2.2.1
  rw [D.hcW_b u τ, (hb τ _).1, (hb τ _).1]
  push_cast
  exact le_of_eq (by ring)

theorem bigGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) (hch : 11311 ≤ ch)
    (hx : 300000 * 4 ^ 30 ≤ L.sc.x) : BigGap D := by
  refine (nodeGap_of_val h).mono ((rank_bound L.sc D.R h.ranks).trans ?_)
  have h1 := L.sc.one_lt_alt
  have h0 : 0 < L.sc.x := by linarith
  have e1 : (L.sc.x ^ (377 : ℝ)) ^ 30 = L.sc.x ^ (11310 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
  have e2 : L.sc.x * L.sc.x ^ (11310 : ℝ) ≤ L.sc.x ^ ch := by
    rw [mul_comm, ← Real.rpow_add_one h0.ne']
    exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
  have e3 : 0 ≤ L.sc.x ^ (11310 : ℝ) := Real.rpow_nonneg h0.le _
  have e4 := mul_le_mul_of_nonneg_right hx e3
  have e5 := Nat.le_ceil (L.sc.x ^ ch)
  have e6 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [mul_pow, e1, ← mul_assoc]
  unfold h0v
  push_cast
  linarith

end GlobalTheory.Core.Rk.GapAt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameImage_trivial_off_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (δ : TC.GA B (B.R.N j)), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ w : HeightOneSpectrum (𝓞 B.fields.E), (w ∈ (B.primes X).vGs ∨ w ∈ I.SQ ∨ (w ∈ (B.primes X).vT u ∧ w ≠ v.1)) →
      ∀ r r', adAt B.host.F w ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
  first | exact @GlobalTheory.AdForm.FrameTriv.frame_trivial_off | exact GlobalTheory.AdForm.FrameTriv.frame_trivial_off | (intros; apply GlobalTheory.AdForm.FrameTriv.frame_trivial_off <;> assumption)
end
