module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle361
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle137
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle431
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
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
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeriesPair_of_pullbackKernelFunction : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ), PairOK X fd B χ SS cl Ξ₀ muT ρ → j < X.mm → (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → ∀ (s : ℂ) (Θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ), s ≠ 0 → (∀ z, kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z = s * TaylorLogMetric.pull D B.tor (e j La) (e (j + 1) La') Θ z) → FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' = linSub (fun x y => c * subBG E pos (reframe fd ρ e) j La La' x y) ((pPow X j La La' * ι (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ * s)) • MvPowerSeries.map ι (tay Θ)) := by
  first | exact @GlobalTheory.TwV.DelB.frecG_pull | exact GlobalTheory.TwV.DelB.frecG_pull | (intros; apply GlobalTheory.TwV.DelB.frecG_pull <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.RealGal.ConjUnr

theorem unr_of_conj_res : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (r : _root_.Formalism.ConjugateSelfDual.G ↥Q.K Ω →* GL (Fin a) (Qbar l)), UpperTheory.V.Af.RepIso r (ρ.comp (UpperTheory.V.Af.Bc.res E Ω ↥Q.K)) → (∀ᶠ w : HeightOneSpectrum (𝓞 ↥Q.K) in Filter.cofinite, ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ s ∈ Ine (F := ↥Q.K) A, r s = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1 := by
  intro E Ω _ _ _ _ _ Q l _ a ρ r hiso hr
  haveI : FiniteDimensional E Q.K := Module.finite_of_finrank_eq_succ Q.two
  have hS1 := GlobalTheory.InertiaAlmostAll.finite_ramified E Ω Q.K
  have hbad := Filter.eventually_cofinite.mp hr
  have hS2 := hbad.image (fun u : HeightOneSpectrum (𝓞 ↥Q.K) => u.under (𝓞 E))
  refine Filter.eventually_cofinite.mpr ((hS1.union hS2).subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨A, hA, s, hs, hρ⟩ := hw
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_image, not_or, not_exists, not_and] at hn
  obtain ⟨h1, h2⟩ := hn
  have hfix : s ∈ Q.K.fixingSubgroup := by
    by_contra hns
    exact h1 A hA (fun hle => hns (hle hs))
  obtain ⟨u, hu⟩ := GlobalTheory.LocLanglands.EpsUnique.exists_place hA ↥Q.K
  have hwu : u.under (𝓞 E) = w := ReciprocityTheory.Gal.eq_of_isPlaceOver (GlobalTheory.DelGlob.placeUnder_isPlaceOver ↥Q.K hu) hA
  have hgood : ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A u → ∀ t ∈ Ine (F := ↥Q.K) A, r t = 1 := by
    by_contra hb
    exact h2 u hb hwu
  let t : _root_.Formalism.ConjugateSelfDual.G ↥Q.K Ω := IntermediateField.fixingSubgroupEquiv Q.K ⟨s, hfix⟩
  have hts : UpperTheory.V.Af.Bc.res E Ω ↥Q.K t = s := AlgEquiv.ext fun _ => rfl
  have ht : t ∈ Ine (F := ↥Q.K) A := ⟨hs.1, hs.2⟩
  obtain ⟨g, hg⟩ := hiso
  apply hρ
  have := hg t
  rw [MonoidHom.comp_apply, hts, hgood A hu t ht] at this
  rw [this]; simp

end GlobalTheory.RealGal.ConjUnr
end
