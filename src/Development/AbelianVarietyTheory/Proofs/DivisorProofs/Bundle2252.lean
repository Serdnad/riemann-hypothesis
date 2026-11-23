module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.discrete_series_model_trace_terms : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  first | exact @GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS | exact GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS | (intros; apply GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS <;> assumption)
end

section

theorem GlobalTheory.JoinFun.joinOut_of_five : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.Mem.LiteralAutomorphy.JoinOut :=
  fun hEM hHJ hSK hPZ hHT => GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity hEM hHJ hSK hPZ hHT (GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM hSK hPZ hHJ hEM)
    (GlobalTheory.T.latticeValueIsAlgebraic_of_ellipticCM_theorems hSK hPZ hHJ hEM) (GlobalTheory.T.latticeValueConjugation_of_ellipticCM_theorems hSK hPZ hHJ hEM)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolForm

theorem wedge_two_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (z : ⋀[K]^2 V)
    (h : ∀ f : Fin 2 → Module.Dual K V,
      exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) z = 0) : z = 0 := by
  by_contra hz
  obtain ⟨J, hJ⟩ := GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero
    (⇑(Module.finBasis K V).dualBasis) (Module.finBasis K V).dualBasis.span_eq z hz
  exact hJ (h _)

theorem pairingDual_ιMulti_two {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Fin 2 → Module.Dual K V) (u v : V) :
    exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) (exteriorPower.ιMulti K 2 ![u, v]) =
      f 0 u * f 1 v - f 0 v * f 1 u := by
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp
  ring

theorem ιMulti_two_swap {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] (u v : V) :
    exteriorPower.ιMulti K 2 ![u, v] = -exteriorPower.ιMulti K 2 ![v, u] := by
  have e : (![v, u] ∘ Equiv.swap (0 : Fin 2) 1) = ![u, v] := by
    ext i; fin_cases i <;> rfl
  rw [← e, AlternatingMap.map_swap _ _ (by decide)]



theorem chern_eq_sum_cup_form : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ → ∃ (I : Type) (_ : Fintype I) (c : I → primDR A) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))) (hω : ∀ k, Form.cl _ (ω k) ∈ primDR A), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (c k).1 (Form.cl _ (ω k))) ∧ ∀ f ∈ Fil A, ∀ x : HdR A, ψ f x = ∑ k, f (c k) * x ⟨_, hω k⟩ := by
  intro H K _ A _ g hA hg L hL ψ hψ
  obtain ⟨hFree, hHodge, -, -, hDual⟩ := H
  obtain ⟨-, hfin, -, -, e, he⟩ := hFree K A g hA hg
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hHodge K A g hA hg
  have hiso := (hDual K A g hA hg L hL ψ hψ).1
  obtain ⟨n, a, b, hch, rfl⟩ := hψ
  let pF := Submodule.projectionOnto (PrimitiveSubmodule A) N hN
  let pN := Submodule.projectionOnto N (PrimitiveSubmodule A) hN.symm
  have hsplit : ∀ c : primDR A, ((pF c : primDR A)) + (pN c : primDR A) = c :=
    Submodule.projection_add_projection_eq_self hN
  have hpN : ∀ c ∈ PrimitiveSubmodule A, pN c = 0 := fun c hc ↦
    (Submodule.projectionOnto_apply_eq_zero_iff hN.symm).2 hc

  have hvan : ∀ x y : Module.Dual K (primDR A),
      ∑ k, (x (pN (a k)) * y (pN (b k)) - x (pN (b k)) * y (pN (a k))) = 0 := by
    intro x y
    have hmem : ∀ z : Module.Dual K (primDR A), z ∘ₗ N.subtype ∘ₗ pN ∈ Fil A := fun z ↦
      (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by simp [hpN c hc]
    have := hiso _ (hmem x) _ (hmem y)
    rw [wedgeForm_apply] at this
    simpa using this
  have h0 : ∑ k, exteriorPower.ιMulti K 2
      ![((pN (a k) : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))), ((pN (b k) : primDR A) : FirstDeRham _)] = 0 := by
    haveI : FiniteDimensional K (FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := hfin
    apply wedge_two_eq_zero
    intro f

    rw [map_sum]
    simp only [pairingDual_ιMulti_two]
    exact hvan (f 0 ∘ₗ (primDR A).subtype) (f 1 ∘ₗ (primDR A).subtype)

  have hform : ∀ c : PrimitiveSubmodule A, ∃ w : Form (A.hom ≫ 𝟙 (Sp K)),
      Form.cl _ w = ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := fun c ↦ by
    have hc := c.2
    change ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    exact hc
  choose form hform using hform
  have hanti : ∀ u v : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) u v = -cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) v u := fun u v ↦ by
    rw [← he, ← he, ← map_neg, ιMulti_two_swap]
  have key : ∀ a₁ a₂ b₁ b₂ : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) (b₁ + b₂) =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) b₁ +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-b₂) a₁ + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) a₂ b₂ := by
    intro a₁ a₂ b₁ b₂
    simp only [map_add (f := _), LinearMap.add_apply, map_neg, LinearMap.neg_apply]
    rw [hanti a₁ b₂]
    abel
  have hZ : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 = 0 := by

    rw [← map_zero e, ← h0, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (he _ _).symm
  obtain ⟨ω, hωdef⟩ : ∃ ω : Fin n ⊕ Fin n → Form (A.hom ≫ 𝟙 (Sp K)),
      ω = Sum.elim (fun k ↦ form (pF (b k))) (fun k ↦ form (pF (a k))) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : Fin n ⊕ Fin n → primDR A,
      c = Sum.elim a (fun k ↦ -(pN (b k) : primDR A)) := ⟨_, rfl⟩
  have hωl : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inl k)) = (pF (b k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inl, hform]
  have hωr : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inr k)) = (pF (a k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inr, hform]
  have hcl : ∀ k, c (Sum.inl k) = a k := fun k ↦ by rw [hcdef, Sum.elim_inl]
  have hcr : ∀ k, c (Sum.inr k) = -(pN (b k) : primDR A) := fun k ↦ by rw [hcdef, Sum.elim_inr]
  have hω : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω k) ∈ primDR A := fun k ↦ by
    rcases k with k | k
    · rw [hωl]; exact Subtype.property _
    · rw [hωr]; exact Subtype.property _
  have hsum : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (c k).1 (Form.cl _ (ω k)) =
      ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 := by
    have e3 : ∀ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (pF (b k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-(pN (b k) : primDR A).1) (pF (a k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 :=
      fun k ↦ by
      have ha := congrArg Subtype.val (hsplit (a k))
      have hb := congrArg Subtype.val (hsplit (b k))
      rw [Submodule.coe_add] at ha hb
      rw [← ha, ← hb]
      exact key _ _ _ _
    rw [Fintype.sum_sum_type]
    simp only [hcl, hcr, hωl, hωr, Submodule.coe_neg]
    rw [Finset.sum_congr rfl fun k _ ↦ e3 k, Finset.sum_add_distrib, Finset.sum_add_distrib, hZ,
      add_zero]
  refine ⟨Fin n ⊕ Fin n, inferInstance, c, ω, hω, by rw [hsum]; exact hch, ?_⟩
  intro f hf x
  rw [Fil, Submodule.mem_dualAnnihilator] at hf
  have hfF : ∀ c : PrimitiveSubmodule A, f c = 0 := fun c ↦ hf _ c.2
  have hfa : ∀ k, f (a k) = f (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add (f := _), hfF, zero_add]
  have hfb : ∀ k, f (b k) = f (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add (f := _), hfF, zero_add]
  have hxa : ∀ k, x (a k) = x (pF (a k)) + x (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add (f := _)]
  have hxb : ∀ k, x (b k) = x (pF (b k)) + x (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add (f := _)]
  have hxl : ∀ k, x ⟨_, hω (Sum.inl k)⟩ = x (pF (b k)) := fun k ↦
    congrArg x (Subtype.ext (hωl k))
  have hxr : ∀ k, x ⟨_, hω (Sum.inr k)⟩ = x (pF (a k)) := fun k ↦
    congrArg x (Subtype.ext (hωr k))
  have hv := hvan f x
  rw [wedgeForm_apply, Fintype.sum_sum_type]
  simp only [hxl, hxr, hcl, hcr, map_neg]
  simp only [hfa, hfb, hxa, hxb]
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hv]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.PolForm
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Published.AbelianDeRham

theorem rigid_of_free_of_crystallineDeRham : GlobalTheory.Published.AbelianDeRham.Free →
    GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro H H' R _ A _ g hA hg I κ hκ R₀ _ π hπ hI A₀ _ i h
  have := hA.smooth
  have := hA.proper
  obtain ⟨h₁, -⟩ := H' R I κ hκ R₀ π hπ hI _ _ (A.hom ≫ 𝟙 _) A₀.hom i inferInstance inferInstance
    inferInstance (by rw [Category.comp_id]; exact h.1) (liftMor κ h).isMor
  have hP := (H R A g hA hg).1
  refine ⟨fun c d e ↦ Subtype.ext (h₁.1 ?_), fun c ↦ ?_⟩
  · have := congrArg Subtype.val e
    simpa only [GrpMor.coe_pull] using this
  · obtain ⟨c', hc'⟩ := h₁.2 c.1
    have hm : c' ∈ prim (dp0 R) (𝟙 _) A := by
      rw [show prim (dp0 R) (𝟙 _) A = ⊤ from hP]; trivial
    exact ⟨⟨c', hm⟩, Subtype.ext (by rw [GrpMor.coe_pull]; exact hc')⟩

end GlobalTheory.Published.AbelianDeRham
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectDual

theorem mono_of_isPerfect {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    [IsMonHom x] (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem isIso_of_isEmpty {S : Scheme.{0}} (hS : IsEmpty S) {X Y : Over S} (f : X ⟶ Y) : IsIso f := by
  haveI : IsEmpty X.left := ⟨fun p ↦ hS.false (X.hom p)⟩
  haveI : IsEmpty Y.left := ⟨fun p ↦ hS.false (Y.hom p)⟩
  haveI : IsIso f.left := ⟨⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩⟩
  haveI : IsIso ((Over.forget S).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget S)

theorem isDual_of_isPerfect_of_additive (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) (haddA : IsAdditive P) (haddB : IsAdditive (swap P)) :
    IsDual A B P := by
  obtain ⟨B', _, P', hB', hd', h1, h2⟩ := hD S A hA
  obtain ⟨A'', _, Q, hA'', hdQ, k1, k2⟩ := hD S B hB
  obtain ⟨x, hx, -⟩ := h1.univ B P hP.isLB haddA
  have hs : (swap P).IsLB := pull_isLB hP.isLB _
  obtain ⟨y, hy, -⟩ := k1.univ A (swap P) hs haddB
  have hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying S A B B' P P' h1 h2.additive hP.isLB haddB x hx
  have hss : (swap (swap P)).IsLB := pull_isLB hs _
  have haddSS : IsAdditive (swap (swap P)) := (isAdditive_iff hss).2 fun Y a a' t ↦ by
    rw [evc_swap hs hss, evc_swap hs hss, evc_swap hs hss, evc_swap hP.isLB hs, evc_swap hP.isLB hs,
      evc_swap hP.isLB hs]
    exact (isAdditive_iff hP.isLB).1 haddA Y a a' t
  have hmy : IsMonHom y := GlobalTheory.AbDual.isMonHom_of_classifying S B A A'' (swap P) Q k1 k2.additive hs haddSS y hy
  have mx : Mono x := mono_of_isPerfect h1 hP x hx
  have my : Mono y := mono_of_isPerfect k1 hP.swap y hy
  have ix : IsIso x := by
    rcases le_or_gt g g' with hle | hlt
    · exact GlobalTheory.AbMonoIso.isIso_of_mono S B B' hB hB' g' g hg' (hd' g hg) hle x hmx mx
    · by_cases hS : Nonempty S
      · exfalso
        have iy := GlobalTheory.AbMonoIso.isIso_of_mono S A A'' hA hA'' g g' hg (hdQ g' hg') hlt.le y hmy my
        exact absurd (GlobalTheory.relDim_unique_of_iso_grp S hS A A'' y iy g g' hg (hdQ g' hg')) hlt.ne'
      · exact isIso_of_isEmpty (not_nonempty_iff.1 hS) x
  exact GlobalTheory.AbDual.transport S A B B' P P' h1 hP.isLB x ix hmx hx

theorem isDual_of_isPerfect (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) : IsDual A B P :=
  isDual_of_isPerfect_of_additive hD A B hA hB hg hg' hP
    (CubeNoeth.isAdditive_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)
    (CubeNoeth.isAdditive_swap_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)

end GlobalTheory.PerfectDual
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeDual

theorem lam_mul_left (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a a' t : T ⟶ A) :
    lam (cls L hL) (a * a') t = lam (cls L hL) a t + lam (cls L hL) a' t := by
  have h := hC S A hA L hL T a a' t
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![a * a' * t, a * a', a * t, a' * t, a, a', t, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  unfold lam
  rw [← sub_eq_zero, ← e]
  abel

theorem evc_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem isAdditive_lam (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) : IsAdditive (abelian₂ A L) ∧ IsAdditive (swap (abelian₂ A L)) := by
  haveI := hA.comm
  have hs : (swap (abelian₂ A L)).IsLB := pull_isLB hP _
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (isAdditive_iff hs).2 fun Y a a' t ↦ ?_⟩
  · rw [evc_lam hL, evc_lam hL, evc_lam hL]
    exact lam_mul_left hC hA hL a a' t
  · rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_lam hL, evc_lam hL, evc_lam hL, lam_comm, lam_comm _ t a,
      lam_comm _ t a']
    exact lam_mul_left hC hA hL a a' t

theorem mono_of_isPerfect' {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) [IsMonHom x] : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem abelianDeRham_duality : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  intro hC hD hPD hF R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨haddL, haddS⟩ := isAdditive_lam hC hA hL hP
  obtain ⟨B, _, P, hB, hdim, h1, h2⟩ := hD (Sp R) A hA
  have hgB := hdim g hg
  obtain ⟨x, hx, -⟩ := h1.univ A (abelian₂ A L) hP haddL
  haveI hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying (Sp R) A A B (abelian₂ A L) P h1 h2.additive hP haddS x hx
  have perf := h1.isPerfect h2
  obtain ⟨φ, hφ⟩ := exists_isCorrForm (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg hgB))
    perf.isLB perf.zero_left perf.zero_right
  have e : LBIso (P.pull (lift (fst A A) (snd A A ≫ x)).left) (abelian₂ A L) :=
    (cls_eq_iff (pull_isLB h1.isLB _) hP).1 ((cls_eq_iff hP (pull_isLB h1.isLB _)).2 hx).symm
  obtain ⟨φ', hφ', k⟩ := hφ.pull h1.isLB (homMor (dp0 R) (𝟙 _) (𝟙 A)) (homMor (dp0 R) (𝟙 _) x)
    (h := (lift (fst A A) (snd A A ≫ x)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id])
    (by simp only [← Over.comp_left, lift_snd])
    hP e
  have hψ' := isCorrForm_lam hψ
  obtain rfl := hφ'.unique (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)) hP hψ'
  have hform : ∀ a b, φ' a b = φ a (push (dp0 R) (𝟙 _) x b) := fun a b ↦ by
    have := k (push (dp0 R) (𝟙 _) (𝟙 A) a) a (push (dp0 R) (𝟙 _) x b) b (fun _ ↦ rfl) fun _ ↦ rfl
    rw [this, push_id]
    rfl
  obtain ⟨-, orth⟩ := hPD R A B g hA hB hg hgB P h1 φ hφ
  refine ⟨fun a ha b hb ↦ ?_, fun hK ↦ ?_⟩
  · rw [hform]
    exact orth a ha _ (push_mem_Fil x hb)
  · have mx : Mono x := mono_of_isPerfect' h1 (isPerfect_lam hL hK) x hx
    have ix : IsIso x := GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension (Sp R) A B hA hB g hg hgB x hmx mx
    have hd : IsDual A A (abelian₂ A L) := GlobalTheory.AbDual.transport (Sp R) A A B (abelian₂ A L) P h1 hP x ix hmx hx
    exact (hPD R A A g hA hA hg hg (abelian₂ A L) hd φ' hψ').1

end GlobalTheory.CubeDual
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_extension_killing_finite_tateModule_image : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], LocallyOfFiniteType A.hom → ∀ (l : ℕ) [Fact l.Prime] (I : Set (Ω ≃ₐ[K] Ω)), (galTate A l '' I).Finite → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ σ ∈ I, (∀ a ∈ L, σ a = a) → galTate A l σ = 1 := by
  first | exact @GlobalTheory.AbVarRedCut.exists_finiteDimensional_galTate_eq_one | exact GlobalTheory.AbVarRedCut.exists_finiteDimensional_galTate_eq_one | (intros; apply GlobalTheory.AbVarRedCut.exists_finiteDimensional_galTate_eq_one <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_galois_smul_eq_valuationSubring_over_dvr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω] (V V' : ValuationSubring Ω), IsAbove R K V.toSubring → IsAbove R K V'.toSubring → ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  first | exact @GlobalTheory.ValConj.exists_smul_eq_of_isAbove | exact GlobalTheory.ValConj.exists_smul_eq_of_isAbove | (intros; apply GlobalTheory.ValConj.exists_smul_eq_of_isAbove <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_image_tateModule_of_bounded_exponent_comm : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)), Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1} → (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) → (∃ E : ℕ, 0 < E ∧ ∀ σ ∈ I, galTate A l σ ^ E = 1) → (galTate A l '' (I : Set (Ω ≃ₐ[K] Ω))).Finite := by
  first | exact @GlobalTheory.Proof.FiniteInertiaImage.finite_image_galTate | exact GlobalTheory.Proof.FiniteInertiaImage.finite_image_galTate | (intros; apply GlobalTheory.Proof.FiniteInertiaImage.finite_image_galTate <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.infinite_torsionUnramified_of_tateModuleUnramified : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  first | exact @GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | exact GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | (intros; apply GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified <;> assumption)
end
