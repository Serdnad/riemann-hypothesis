module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFlatMapIndepUnfoldingStep
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle220
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle215
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle221
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselLinkKappa_adjoint_tau_factor : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  first | exact @GlobalTheory.kappa_adj | exact GlobalTheory.kappa_adj | (intros; apply GlobalTheory.kappa_adj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

theorem gram_of_lineMap {D : D7} {n m : ℕ} (hm : ∀ i j : Fin m, i = j) (τ : Matrix (Fin n) (Fin m) D.host.E)
    (G : Matrix (Fin n) (Fin n) D.host.E) (G' : Matrix (Fin m) (Fin m) D.host.E) (ζ : Fin n → D.host.E)
    (ζ' : Fin m → D.host.E) (c : D.host.E) (hmap : τ *ᵥ ζ' = -ζ)
    (hnorm : star ζ ⬝ᵥ G *ᵥ ζ = c * (star ζ' ⬝ᵥ G' *ᵥ ζ')) (hne : star ζ' ⬝ᵥ G' *ᵥ ζ' ≠ 0) :
    τᴴ * (G * τ) = c • G' := by
  haveI : Subsingleton (Fin m) := ⟨hm⟩
  have key : ∀ (M : Matrix (Fin m) (Fin m) D.host.E) (i : Fin m), star ζ' ⬝ᵥ M *ᵥ ζ' = star (ζ' i) * (M i i * ζ' i) := by
    intro M i
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_subsingleton _ i, Pi.star_apply]
  have hζ : ζ = -(τ *ᵥ ζ') := by rw [hmap, neg_neg]
  have h1 : star ζ ⬝ᵥ G *ᵥ ζ = star ζ' ⬝ᵥ (τᴴ * (G * τ)) *ᵥ ζ' := by
    rw [hζ, star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, Matrix.star_mulVec,
      Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  refine Matrix.ext fun i j => ?_
  obtain rfl := hm i j
  rw [h1, key _ i, key _ i] at hnorm
  rw [key _ i] at hne
  have hz : star (ζ' i) * ζ' i ≠ 0 := by
    intro h0; apply hne; rw [mul_left_comm, h0, mul_zero]
  have : star (ζ' i) * ζ' i * ((τᴴ * (G * τ)) i i - c * G' i i) = 0 := by
    rw [mul_sub]; rw [show star (ζ' i) * ζ' i * (τᴴ * (G * τ)) i i = star (ζ' i) * ((τᴴ * (G * τ)) i i * ζ' i) by ring, hnorm]; ring
  rw [Matrix.smul_apply, smul_eq_mul]
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hz)
  exact h3

end GlobalTheory.ContrComb
end

noncomputable section
namespace GlobalTheory.ContrComb

theorem link_gram {D : D7} {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) :
    l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • B'.L.gram := by
  rw [Int.cast_one, one_mul]
  refine gram_of_lineMap (fun i j => Fin.ext (by have := i.isLt; have := j.isLt; have := B'.line.1; omega))
    l.τ B.L.gram B'.L.gram B.ζ B'.ζ _ l.map l.norm B'.line.2

theorem integrand_cont_per : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → Continuous (fun p : Mx D B'.L.rank S.rank × (WO B.A S × WO S B'.A) => f₂ ((B'.o.resT S).symm (p.2.2, p.1)) * f₁ ((B.o.resS S).symm (p.2.1, l.κ S p.1))) ∧ ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ (w : Mx D B'.L.rank S.rank) (u : WO B.A S) (v : WO S B'.A), f₂ ((B'.o.resT S).symm (v, γ + w)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + w))) = f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w)) := by
  intro D ρ σ B B' l S ψ f₁ f₂ h₁ h₂
  obtain ⟨hadd, hcont, hrat, -, hsym, -⟩ :=
    GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 (link_gram l) (l.κ S) (fun _ => rfl)
  refine ⟨?_, ?_⟩
  · exact (h₂.cont.comp ((B'.o.continuous_resT_symm S).comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_fst))).mul
      (h₁.cont.comp ((B.o.continuous_resS_symm S).comp
        ((continuous_fst.comp continuous_snd).prodMk (hcont.comp continuous_fst))))
  · intro γ hγ w u v
    obtain ⟨c₀, hc₀⟩ := hrat γ hγ
    obtain ⟨γ₀, hγ₀⟩ := hγ
    have e₂ : (B'.o.resT S).symm (v, γ + w) = (B'.o.resT S).symm (0, γ) + (B'.o.resT S).symm (v, w) := by
      rw [← map_add (f := _)]; simp
    have q₂ : (B'.o.resT S).symm (0, γ) = ratW B'.V₀ S (B'.o.iB * γ₀) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, ← hγ₀]
      show _ = rat _
      rw [rat_mul]; rfl
    have e₁ : (B.o.resS S).symm (u, l.κ S (γ + w)) = (B.o.resS S).symm (0, l.κ S γ) + (B.o.resS S).symm (u, l.κ S w) := by
      rw [hadd, ← map_add (f := _)]; simp
    have q₁ : (B.o.resS S).symm (0, l.κ S γ) = ratW S B.V₀ (c₀ * B.o.qB) := by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, ← hc₀]
      show _ = rat _
      rw [rat_mul]; rfl
    have hph : symplOH B.L S (l.κ S γ) (l.κ S w) = -(symplOH S B'.L γ w) := by
      simp only [symplOH, hsym]
      push_cast
      ring
    rw [e₂, e₁, q₂, q₁, h₂.quasi, h₁.quasi, ← q₂, ← q₁, B'.o.symplOH_resT, B.o.symplOH_resS,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, symplOH_zero_left, zero_add, zero_add, hph, neg_neg]
    have hψ : ψ (-(symplOH S B'.L γ w)) * ψ (symplOH S B'.L γ w) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    linear_combination (f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) * hψ

end GlobalTheory.ContrComb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_flatMap_indep_unfoldingStep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s s' : StepBF ψ B J) f, IsThetaFunO ψ B.V J.W f → flatBF s f = flatBF s' f) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s s' : StepFB ψ J B) f, IsThetaFunO ψ J.W B.V f → flatFB s f = flatFB s' f := by
  first | exact @GlobalTheory.FlatIndep.flat_indep | exact GlobalTheory.FlatIndep.flat_indep | (intros; apply GlobalTheory.FlatIndep.flat_indep <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Unf.MajLoc

theorem exists_compact_sub {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (K Q : Set G)
    (hK : IsCompact K) (hQ : IsCompact Q) : ∃ K' : Set G, IsCompact K' ∧ ∀ k ∈ K, ∀ x ∈ Q, k - x ∈ K' :=
  ⟨_, (hK.prod hQ).image continuous_sub, fun k hk x hx => ⟨(k, x), ⟨hk, hx⟩, rfl⟩⟩

theorem summable_of_tsum_ne_top {α β : Type*} (f : β → ℝ) (hf : ∀ y, 0 ≤ f y) (h : (∑' y, ENNReal.ofReal (f y)) ≠ ⊤)
    (e : α → β) (he : Function.Injective e) : Summable fun a => f (e a) :=
  ((ENNReal.summable_toReal h).congr fun y => ENNReal.toReal_ofReal (hf y)).comp_injective he

theorem inv_pow_le {a c R : ℝ} (N : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hR : 0 ≤ R) (h : c ≤ a + R) :
    ((1 + a) ^ N)⁻¹ ≤ (1 + R) ^ N * ((1 + c) ^ N)⁻¹ := by
  have hle : 1 + c ≤ (1 + R) * (1 + a) := by nlinarith [mul_nonneg ha hR]
  have hA : 0 < (1 + a) ^ N := by positivity
  have hB : 0 < (1 + c) ^ N := by positivity
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle N

theorem realSize_neg {D : D7} (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : realSize θ (-x) = realSize θ x := by
  unfold realSize
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (-x) i j = -compAt θ τ x i j := by
    show θ τ (infPart D (-x i j)) = -θ τ (infPart D (x i j))
    rw [RingHom.map_neg (infPart D), RingHom.map_neg (θ τ)]
  rw [this, norm_neg]

theorem maj_add_le {D : D7} (θ : InfFam D) {m n : ℕ} (K K' : Set (Mx D m n)) (N : ℕ) (x y : Mx D m n) (R : ℝ)
    (hR : 0 ≤ R) (hx : realSize θ x ≤ R) (hK : ∀ k ∈ K, k - x ∈ K') :
    maj θ K N (x + y) ≤ (1 + R) ^ N * maj θ K' N y := by
  by_cases hb : InBox K (x + y)
  · have hb' : InBox K' y := by
      obtain ⟨k, hk, hkx⟩ := hb
      refine ⟨k - x, hK k hk, ?_⟩
      have : y - (k - x) = x + y - k := by abel
      rw [this]; exact hkx
    unfold maj
    rw [if_pos hb, if_pos hb']
    have hadd := GlobalTheory.MajSum.realSize_add_le θ (x + y) (-x)
    have e2 : x + y + -x = y := by abel
    rw [e2, realSize_neg] at hadd
    exact inv_pow_le N (realSize_nonneg θ _) (realSize_nonneg θ _) hR (by linarith)
  · have e0 : maj θ K N (x + y) = 0 := by
      unfold maj
      rw [if_neg hb]
    rw [e0]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N _)

theorem summable_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K Q : Set (Mx D m n),
    IsCompact K → IsCompact Q → ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧
      ∀ x ∈ Q, ∀ ξ, GlobalTheory.Unf.maj θ K N (x + rat ξ) ≤ b ξ := by
  intro D θ hθ m n
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ m n
  refine ⟨N, fun K Q hK hQ => ?_⟩
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) := GlobalTheory.Unf.MajMeas.continuous_realSize hθ
  obtain ⟨K', hK', hKK⟩ := @exists_compact_sub (Mx D m n) _ _ (lattice_Mx D m n).1 K Q hK hQ
  obtain ⟨R, hR⟩ := (hQ.image hcont).bddAbove
  have hs : Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => maj θ K' N (rat ξ) :=
    summable_of_tsum_ne_top (fun y : ratMx D m n => maj θ K' N y) (fun y => maj_nonneg θ K' N y) (hN K' hK')
      (fun ξ => ⟨rat ξ, rat_mem ξ⟩) fun a b h => rat_injective (congrArg Subtype.val h)
  exact ⟨fun ξ => (1 + max R 0) ^ N * maj θ K' N (rat ξ), hs.mul_left _, fun x hx ξ =>
    maj_add_le θ K K' N x (rat ξ) (max R 0) (le_max_right _ _) ((hR ⟨x, hx, rfl⟩).trans (le_max_left _ _))
      fun k hk => hKK k hk x hx⟩

end GlobalTheory.Unf.MajLoc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.satake_string_gives_simple_pole_hypotheses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t s, HasString R i t s → ∃ B c : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧ GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))) D.R.r D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
  first | exact @GlobalTheory.Core.Rk.StringPole.string_pole_hyp | exact GlobalTheory.Core.Rk.StringPole.string_pole_hyp | (intros; apply GlobalTheory.Core.Rk.StringPole.string_pole_hyp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isThetaFunO_source_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO S T → ℂ) (y : WO L T), IsThetaFunO ψ S T f → IsThetaFunO ψ A T (fun w => f ((o.resS T).symm (w, y))) := by
  first | exact @GlobalTheory.MixModel.OrthDec.isThetaFunO_slice | exact GlobalTheory.MixModel.OrthDec.isThetaFunO_slice | (intros; apply GlobalTheory.MixModel.OrthDec.isThetaFunO_slice <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverConj

theorem isConjugatePlace_conjugateIdealPlace (D : D7) (P : Pl D.host.E) : Formalism.L2.DIV.IsConjPl P (Formalism.DivisionValues.conjPl P) := by
  intro a b hab
  have hb : b = Formalism.DivisionValues.cO D.host.E a := RingOfIntegers.ext (by rw [hab]; rfl)
  subst hb
  show a ∈ P.asIdeal ↔ Formalism.DivisionValues.cO D.host.E a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    rw [Ideal.mem_map_of_equiv] at h
    obtain ⟨x, hx, hxa⟩ := h
    rwa [← (Formalism.DivisionValues.cO D.host.E).injective hxa]

theorem cover : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  intro D Pg hPg Q hQ
  have hv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]
    exact hQ
  obtain ⟨PP, ⟨hPP, hunder⟩, -⟩ := hPg.2 _ hv
  refine ⟨PP, hPP, ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hunder.symm with h | h
  · exact Or.inl h
  · right
    intro s
    have hc : Formalism.L2.DIV.IsConjPl PP Q := h ▸ isConjugatePlace_conjugateIdealPlace D PP
    exact (Formalism.L2.DIV.resS_sigS_eq_zero_iff (instOf D).cm hc.symm s).symm

end GlobalTheory.CoverConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mem_flagUnipotentRadical_iff_secondModel : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → _root_.GlobalTheory.Core.Mi.IdE X → ∀ (V₀ : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS), d.e = GlobalTheory.Core.SBesEx.eM X h t lam → ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u := by
  first | exact @GlobalTheory.Core.SBesFlagTie.mem_flagN_iff | exact GlobalTheory.Core.SBesFlagTie.mem_flagN_iff | (intros; apply GlobalTheory.Core.SBesFlagTie.mem_flagN_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.selfDualLatticeAtPlace_basis_gram_integral_invertible : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D)), ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → (∀ i j, β i j ∈ idAt D (· = v)) → (∀ i j, β' i j ∈ idAt D (· = v)) → β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) → (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.GramBasis.gram_basis | exact GlobalTheory.IwaPlace.GramBasis.gram_basis | (intros; apply GlobalTheory.IwaPlace.GramBasis.gram_basis <;> assumption)
end

end

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff


theorem _root_.GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K Q : Set (Mx D m n), IsCompact K → IsCompact Q → ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, GlobalTheory.Unf.maj θ K N (x + rat ξ) ≤ b ξ := by
  first | exact @GlobalTheory.Unf.MajLoc.summable_bound | exact GlobalTheory.Unf.MajLoc.summable_bound | (intros; apply GlobalTheory.Unf.MajLoc.summable_bound <;> assumption)

end
end
