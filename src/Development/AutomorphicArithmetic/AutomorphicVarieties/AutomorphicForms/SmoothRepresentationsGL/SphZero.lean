module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import GroundTheory.AutomorphicForms.HaarCosets
public import GroundTheory.AutomorphicForms.MacdonaldHecke
public import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Separation.Connected
public import GroundTheory.AutomorphicForms.MacdonaldAlternant

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section General

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra
open scoped ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem esymm_eq (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r := by
  rw [evalAt_esymmL, Multiset.map_map, Finset.esymm_map_val]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialChar_apply]
  simp only [lamS, Function.comp_apply]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

private theorem lamS_univ : lamS (Finset.univ : Finset (Fin n)) = fun _ => 1 := by
  funext i
  simp [lamS]

private theorem gMat_univ (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    gMat Finset.univ c = torusPow F n (fun _ => 1) := by
  have h : unipC (F := F) Finset.univ c = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_unipC, Matrix.add_apply, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
    rfl
  rw [gMat, h, one_mul, lamS_univ]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

private theorem central_of_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : minusculeHecke μ n ∈ eigenSubalgebra μ z f hf) : centralHecke μ ∈ eigenSubalgebra μ z f hf := by
  apply _root_.GlobalTheory.HenQ.ShellOp.central_mem_of_top <;> assumption

private theorem minuscule_mem (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {r : ℕ} (hr : r ≤ n)
    (h : ∀ g, ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out * f (g * c.out) =
        sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f g) :
    minusculeHecke μ r ∈ eigenSubalgebra μ z f hf :=
  _root_.GlobalTheory.HenQ.ShellOp.minuscule_mem_of z hf hr h

end General

theorem UpperTheory.V.Af.Smo.sphZero :
    UpperTheory.V.Af.Smo.SphDict → UpperTheory.V.Af.Smo.TjSet → UpperTheory.V.Af.Smo.CentLoc → UpperTheory.V.Af.Smo.SphZero := by
  intro hD hTj _ E _ _ n w ψ hψ B W hW hE h1
  obtain ⟨hK, hu, hq, hN⟩ := hD E n w
  obtain ⟨z, rfl⟩ : ∃ z : Fin n → ℂˣ, Finset.univ.val.map z = B := by
    obtain ⟨l, rfl⟩ := Quotient.exists_rep B
    have hl : l.length = n := hE.card
    subst hl
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  borelize (GL (Fin n) (w.adicCompletion E))
  let μ : Measure (GL (Fin n) (w.adicCompletion E)) := Measure.haar
  have hf : ∀ g, ∀ k ∈ GLnLocal.integralGL (w.adicCompletion E) n, W (g * k) = W g := by
    rw [hK]
    exact hE.inv
  have hT : ∀ r ≤ n, Spherical.minusculeHecke μ r ∈ Spherical.eigenSubalgebra μ z W hf := by
    intro r hr
    refine minuscule_mem z hf hr fun g => ?_
    rw [hK, ← hTj E n w r hr, hE.eig _ hu r hr g, hq r hr, esymm_eq, GlobalTheory.LFun.satEig]
  have htop := Spherical.eigenSubalgebra_eq_top z hf hT (central_of_top z hf (hT n le_rfl))
  funext g
  have := Spherical.eq_smul_sphericalWhittaker (μ := μ) (ψ₀ := ψ)
    (fun x hx => hψ.1 x ((GroundTheory.Global.mem_valuationInteger_iff w x).1 hx))
    (by
      obtain ⟨x, hx, hx'⟩ := hψ.2 _ hu
      exact ⟨x, (GroundTheory.Global.mem_valuationInteger_iff w _).2 hx, hx'⟩) z
    (fun u hu g => by rw [(hN u hu).2 ψ, hW u (hN u hu).1 g]) hf
    (fun h => show h ∈ Spherical.eigenSubalgebra μ z W hf from htop ▸ Algebra.mem_top) g
  rw [this, h1, zero_mul]
  rfl
