module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle109
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanTermANonneg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDimensionFormula
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle253
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.VacBox

variable {D : D7}

theorem gram_dbl_inv (A : HSp D) : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) :=
  Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram A).2.isUnit, blkMat_one])

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (resL A B x) (resL A B y) - hO A B (resR A B x) (resR A B y) := by
  simp only [hO]
  rw [gram_dbl_inv]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, resL, resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem hO_neg_neg (A B : HSp D) (x y : WO A B) : hO A B (-x) (-y) = hO A B x y := by
  simp only [hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y = symplOH A B (resL A B x) (resL A B y) - symplOH A B (resR A B x) (resR A B y) := by
  simp only [symplOH, symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_neg_neg (A B : HSp D) (x y : WO A B) : symplOH A B (-x) (-y) = symplOH A B x y := by
  simp only [symplOH, symplO, hO_neg_neg]

theorem resL_add (A B : HSp D) (x y : WO (dblSp A) B) : resL A B (x + y) = resL A B x + resL A B y :=
  Matrix.ext fun _ _ => rfl

theorem resR_add (A B : HSp D) (x y : WO (dblSp A) B) : resR A B (x + y) = resR A B x + resR A B y :=
  Matrix.ext fun _ _ => rfl

def resLHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resL_add A B

def resRHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resR A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resR_add A B

theorem conj_psi_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (z : AF D.host.F) :
    conj (ψ z) = ψ (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ, one_pow, inv_one, Complex.ofReal_one,
    mul_one]

theorem heisO_delta {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (A B : HSp D) (w₀ : WO (dblSp A) B)
    (f₁ f₂ : WO A B → ℂ) :
    heisO ψ (dblSp A) B w₀ (delta A B f₁ f₂) =
      delta A B (heisO ψ A B (resL A B w₀) f₁) (heisO ψ A B (-resR A B w₀) f₂) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, resL_add, resR_add, map_mul, conj_psi_eq hψ, symplOH_dbl, symplOH_neg_neg, neg_add]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem sum_dbl_gram_inl (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inl j)) =
      ∑ k, star ((fun k => s (finSumFinEquiv (Sum.inl k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem sum_dbl_gram_inr (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inr j)) =
      ∑ k, star ((-fun k => s (finSumFinEquiv (Sum.inr k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.neg_apply, Pi.neg_apply, star_neg, mul_neg, neg_mul]

theorem res_mem_latO {A B : HSp D} {LA : Lat A} {LB : Lat B} {P : FinPl D → Prop} {u : WO (dblSp A) B}
    (hu : u ∈ latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P) :
    resL A B u ∈ latO A B LA LB P ∧ resR A B u ∈ latO A B LA LB P := by
  have key : latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P ≤
      (latO A B LA LB P).comap (resLHom A B) ⊓ (latO A B LA LB P).comap (resRHom A B) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, fun k => s (finSumFinEquiv (Sum.inl k)), hs.1, t, ht, ?_⟩,
      AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, -fun k => s (finSumFinEquiv (Sum.inr k)), neg_mem hs.2, t, ht, ?_⟩⟩
    · ext i j
      simp only [resLHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resL, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inl A s j)
    · ext i j
      simp only [resRHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resR, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inr A s j)
  exact key hu

theorem latO_mono_at {A B : HSp D} (LA : Lat A) (LB : Lat B) {Sf : Finset (FinPl D)} {v : FinPl D} (hv : v ∉ Sf) :
    latO A B LA LB (fun u => u = v) ≤ latO A B LA LB (fun u => u ∉ Sf) := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hP, rest⟩
  refine ⟨α, hα, fun v' hv' => hP v' fun h => hv' (h ▸ hv), rest⟩

theorem pair_dbl (A : HSp D) (x y : Fin (dblSp A).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (dblSp A).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * A.gram i j * y (finSumFinEquiv (Sum.inl j))) -
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * A.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem selfDual_sumLat {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) :
    IsSelfDualC (dblSp A) (sumLat finSumFinEquiv L L) := by
  have hsum : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L) := by
    let φ : ((Fin A.rank → D.host.E) × (Fin A.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (A.rank + A.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L = (L.prod L).map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL.1.fg).map _)
  refine ⟨hsum, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ - b₂, ?_⟩
    rw [pair_dbl]
    push_cast
    linear_combination hb₁ - hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, sub_zero] at hb
      refine ⟨b, ?_⟩
      show (b : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inl j))
      exact hb
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hb
      refine ⟨-b, ?_⟩
      show ((-b : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inr j))
      push_cast
      linear_combination -hb

theorem doubling_isLatVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  intro D ψ A B LA LB hψ hLA
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨selfDual_sumLat hLA, ?_⟩
  intro Sf Φ₁ Φ₂ h₁ h₂ v hv
  have mono := latO_mono_at LA LB hv
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have eL : resL A B (2 • u) = 2 • resL A B u := by rw [two_nsmul, two_nsmul, resL_add]
    have eR : -resR A B (2 • u) = 2 • (-resR A B u) := by
      rw [two_nsmul, two_nsmul, resR_add, neg_add]
    rw [heisO_delta hn, eL, eR, h₁.1 _ (mono hL), h₂.1 _ (neg_mem (mono hR))]
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have hhL : IsHalf e (resL A B u) := fun i j => hh i (finSumFinEquiv (Sum.inl j))
    have hhR : IsHalf e (-resR A B u) := fun i j => by
      show e * -(u i (finSumFinEquiv (Sum.inr j))) = -(u i (finSumFinEquiv (Sum.inr j)))
      rw [mul_neg, hh]
    rw [heisO_delta hn, h₁.2 e he _ (mono hL) hhL, h₂.2 e he _ (neg_mem (mono hR)) hhR]

end GlobalTheory.Core.Rk.VacBox
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
namespace GlobalTheory.VacInertAt

variable {D : D7}

theorem half_eq_two_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) (S T : HSp D) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True)
    (hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) :
    ∃ u' ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      (fun x => x = v), u = 2 • u' := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have h2F : (2 : D.host.F) ≠ 0 := two_ne_zero
  set γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := α * algebraMap D.host.F _ ((2 : D.host.F)⁻¹) with hγdef
  have hγ : γ ∈ intAf D.host.F := fun w => by
    rw [hγdef, map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
        rw [← map_ofNat (algebraMap (𝓞 D.host.F) D.host.F) 2, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  have hγv : ∀ w, ¬ w = v → evalV D.host.F w γ = 0 := fun w hw => by
    rw [hγdef, map_mul, h0 w hw, zero_mul]
  have hαγ : α = γ + γ := by
    rw [← two_mul, hγdef, mul_comm α, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) 2,
      ← map_mul, mul_inv_cancel₀ h2F, map_one, one_mul]
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 γ) with ha₀
  let φ : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) a₀
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      (latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        (fun x => x = v)).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨γ * β, GlobalTheory.VacLat.intAf_mul hγ hβ,
      fun w hw => by rw [map_mul, hγv w hw, zero_mul], a, ha, s, by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact hs, t,
      by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact ht, ?_⟩
    ext i j
    simp only [φ, DistribSMul.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.VacLat.pairA_mul]
  refine ⟨a₀ • u, key hu, ?_⟩
  have he : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = a₀ + a₀ := by
    rw [ha₀, ← map_add (f := _), hαγ]
    congr 1
    exact Prod.ext (add_zero 0).symm rfl
  ext i j
  rw [two_nsmul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← add_mul, ← he]
  exact (hh i j).symm

theorem isVacAt_of_vacFin : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w = w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ),
    VacFin ψ S T v f → IsVacAt ψ S T w f := by
  intro D v w hv hw ψ S T f hf
  obtain ⟨ε, hε, -, hc, hpi⟩ := GlobalTheory.VacFixInert.inert_data hw
  have h2 := GlobalTheory.VacFixInert.two_not_mem hc
  rw [hv] at hε h2
  refine ⟨hf.1, fun e f' he u hu hhalf => ?_⟩
  have hee := (hpi e f' he).1
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h | h
    · rw [hee] at h; exact h
    · rw [hee, GlobalTheory.IdemSupport.cA_algebraMap] at h; exact h
  obtain ⟨u', hu', rfl⟩ := half_eq_two_smul hε h2 S T u hu hh
  exact hf.2.1 u' hu'

end GlobalTheory.VacInertAt
end

section

noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pairsDegOfType_holds : PairsDegOfType := by
  intro CH Ch Cp C hCH hCh hCp hC
  set Cc : ℝ := 21 + 4 * |CH| with hCcdef
  have hCc : 0 ≤ Cc := by positivity
  have hC0 : 0 ≤ C := by linarith
  refine ⟨max 1 (k2C0 (k2Cf C Ch Cc)), fun C' Cl Cg cb Cw cT CT C0 D large₂ X Y u h2 hH hTie tAt => ?_⟩
  have b1 : (1 : ℝ) ≤ Cl := le_trans (le_max_left _ _) h2
  have b5 : k2C0 (k2Cf C Ch Cc) ≤ Cl := le_trans (le_max_right _ _) h2
  have dAt : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    fun t ht => delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht
  have cAt := GlobalTheory.Core.Deg.sum_labels_one_record CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u b1 hH
  have pg := GlobalTheory.Core.Deg.pgC_le_two_at_record C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  obtain ⟨hΓ, hdim⟩ := kappa_off_diagonal_dim_form_C D X Y u hTie
  have hJ := JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hTie
  obtain ⟨hL, -, -, -, hWd, -⟩ := hTie
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u
  have hI := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd) hF
  have hIrr := IrrVecC_holds D X Y u hF hI
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hmass : 0 ≤ massC Y u := Finset.sum_nonneg fun Λ _ => by unfold wRow; positivity
  have hK : 0 ≤ dpiC X u * massC Y u := mul_nonneg hdpi hmass
  set B := dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 with hB
  set g : GTu Y u × GTu Y u → ℝ := ((Y.tO u u).allPairs (Y.tO u u).degSet).indicator
    (fun p => ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => Set.indicator_nonneg (fun p _ => by positivity) p
  have hfin : ∀ s : Finset (GTu Y u × GTu Y u), ∑ p ∈ s, g p ≤ B := by
    intro s
    have : ∑ p ∈ s, g p = ∑ p ∈ s.filter (fun p => p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet),
        ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ := by
      rw [Finset.sum_filter]
      rfl
    rw [this]
    exact fin_bound hC0 hCh (le_refl _) hK hIrr hJ tAt dAt cAt _ (fun p hp => (Finset.mem_filter.1 hp).2)
  have hsum : Summable g := summable_of_sum_le hg0 hfin
  have htsum : Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet) ≤ B :=
    tsum_le_of_sum_le' (mul_nonneg hK (sq_nonneg _)) hfin
  refine ⟨hsum, ?_⟩
  have hPg0 : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdu : 0 ≤ duC X Y u := Nat.cast_nonneg _
  have hCf : 1 ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k := by
    have hL0 : 0 ≤ large₂.sc.L := by
      rw [← log_scale_eq_L]; exact Real.log_nonneg (by linarith [two_le_scale_b large₂ (D := D)])
    have hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := mul_nonneg (by positivity) hL0
    have := hH.2.1
    calc k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L = k2C0 (k2Cf C Ch Cc) * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := by ring
      _ ≤ Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := mul_le_mul_of_nonneg_right b5 hm6
      _ = Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L := by ring
      _ ≤ _ := this
  have hA : (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 ≤ k2B D large₂ (k2Cf C Ch Cc) := by
    unfold k2B
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => kloostermanTermA_nonneg large₂ hC0 hCh hCc j)
      (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC0 j hj) 2
  have hclose := final_bound_closes D large₂ (k2Cf C Ch Cc) hCf _ hdu hk
  have hGB : (Y.tO u u).Gam1 * B ≤ duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
    have e : (Y.tO u u).Gam1 * B =
        ((Y.tO u u).Gam1 * massC Y u * dpiC X u) * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
      rw [hB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
  calc PgC Y * ((Y.tO u u).Gam1 *
        Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet))
      ≤ PgC Y * ((Y.tO u u).Gam1 * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htsum hΓ) hPg0
    _ ≤ PgC Y * (duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2) :=
        mul_le_mul_of_nonneg_left hGB hPg0
    _ ≤ 2 * (duC X Y u * k2B D large₂ (k2Cf C Ch Cc)) :=
        mul_le_mul pg (mul_le_mul_of_nonneg_left hA hdu) (mul_nonneg hdu (sq_nonneg _)) (by norm_num)
    _ = 2 * duC X Y u * k2B D large₂ (k2Cf C Ch Cc) := by ring
    _ ≤ _ := hclose

end GlobalTheory.Core.Deg
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicTranslate_one_eq_standardLattice : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := by
  first | exact @GlobalTheory.AdForm.MovesOne.moves_one | exact GlobalTheory.AdForm.MovesOne.moves_one | (intros; apply GlobalTheory.AdForm.MovesOne.moves_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bessel_column_function_continuousOn_bessel_group : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.Ginf), IsCharAF D.host.F ψ → ContinuousOn (fun g => Ph X u hK T (iotaX X h g * (y, X.xu u))) (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
  first | exact @GlobalTheory.Core.Mi.PhCont.ph_continuousOn | exact GlobalTheory.Core.Mi.PhCont.ph_continuousOn | (intros; apply GlobalTheory.Core.Mi.PhCont.ph_continuousOn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  first | exact @GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae | exact GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae | (intros; apply GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Mi

theorem exists_conjVec : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → ∃ v₀ : M.Vec, ConjVec X h θ M v₀ := by
  intro hcl D X h θ S M hS hθ _hgap hιE
  subst hS
  obtain ⟨-, -, hreal, -⟩ := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE
  obtain ⟨-, -, -, -, hmult, -, hstrict⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hcl
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_of_classification hcl
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.SeeInt.exists_conj_intertwiner hU hmult hstrict X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ
    X.B.w X.B.lam X.lam_eq X.ds X.low M
  refine ⟨fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hc2 τ⟩, c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x,
    fun τ => ?_⟩
  exact LinearIsometryEquiv.apply_symm_apply _ _

end GlobalTheory.Core.Mi

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateIntertwiner_values_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  first | exact @GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun | exact GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun | (intros; apply GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun <;> assumption)
end
