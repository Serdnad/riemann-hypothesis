module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace UpperTheory.ConvolutionTheory.Sph

private theorem zpow_inj_of_absNorm {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : ℤ}
    (h : (Ideal.absNorm v.asIdeal : ℝ) ^ a = (Ideal.absNorm v.asIdeal : ℝ) ^ b) : a = b := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun e => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 e)
  have h2 : 1 < Ideal.absNorm v.asIdeal := by omega
  have h3 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast h2
  exact zpow_right_injective₀ (by linarith) h3.ne' h

theorem unrNorm : UnrNorm := by
  intro F E _ _ _ _ _ v w σw l N hN hq a
  refine MonoidHom.ext fun x => ?_
  have h := hN.abs x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.T.residue_card_eq_abs_norm F v, GlobalTheory.T.residue_card_eq_abs_norm E w.1, hq] at h
  have h' := zpow_inj_of_absNorm v h
  have h'' := neg_injective h'
  simp only [MonoidHom.comp_apply, GlobalTheory.SmGL.unrChar_apply, h'']

end UpperTheory.ConvolutionTheory.Sph
end

section

noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory.C GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

private theorem hasSat_iff {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (π : CuspSub K n)
    (v : HeightOneSpectrum (𝓞 K)) (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (hτ : π.IsLocComp v τ)
    (B : Multiset ℂˣ) : (Cusp.cx π).sat v B ↔ GlobalTheory.LFun.HasSatGL v τ.ρ B := by
  refine ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  have hB' : GlobalTheory.LFun.HasSatGL v (π.locRep v) B := hB
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep K n).comp (locGL K n v)) τ.ρ τ.irred
    (fun f : LocSph.Maps π v τ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL v (n := n) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v τ hτ]; exact x.2)
  obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred
    ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ hB'').unique hB' ▸ hB''

private theorem isSpherical_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) :
    IsSpherical τ.ρ ↔ GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.LFun.KGL v (n := n)) ≠ ⊥ := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := K) v n
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.satDict :
    UpperTheory.ConvolutionTheory.Sph.SatDict := by
  refine ⟨1, Or.inl rfl, ?_⟩
  intro K _ _ _ n π v τ hτ
  have hτ' : π.IsLocComp v τ := hτ
  refine ⟨?_, fun hs => ?_, fun α hs hα => ?_⟩
  · rintro ⟨B, hB⟩
    exact (isSpherical_iff v τ).2 ((hasSat_iff π v τ hτ' B).1 hB).1
  · refine GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries
      ((GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness _).1 (Fin n) τ.V τ.ρ τ.smooth τ.irred) τ.irred ?_
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
    exact (Submodule.ne_bot_iff _).2 ⟨x, fun h => hx ⟨h.1, iwahori_le_KO _ _ h.2⟩, hx0⟩
  · have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K v n τ.V τ.ρ α ⟨τ.irred, hs, hα⟩
    have e : (Finset.univ.val.map fun i => α i ^ (1 : ℤ)) = Finset.univ.val.map α := by simp
    rw [e]
    exact (hasSat_iff π v τ hτ' _).2 h
end
end
