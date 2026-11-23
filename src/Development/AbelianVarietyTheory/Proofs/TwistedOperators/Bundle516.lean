module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle481
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle482
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle293
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle483
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open GlobalTheory.HolDict GlobalTheory.BackForm
open scoped Classical

namespace GlobalTheory.CuspRepr



theorem exists_allMaps : ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ), ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → (∀ k ∈ K, ∀ y, RG V μ (k : GA D V) (Φ y) = Φ y) → ∃ T ∈ GlobalTheory.CuspMult.allMaps θ M, ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  intro D θ hθ V S M μ _ _ Φ hΦ K hK hKfix
  obtain ⟨𝓕, ρ, e, hp, hρ, he, hrep⟩ := GlobalTheory.T.exists_L2AdelicQuotient_model_equivalence D V μ
  obtain ⟨hcusp, hequiv⟩ := (GlobalTheory.AutMult.mem_homDS hθ).1 hΦ
  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), ∀ y, Φ' y = e (Φ y) :=
    ⟨(e.toContinuousLinearEquiv : DividedPowerChartLift V μ →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕)).compContinuousMultilinearMap Φ, fun _ => rfl⟩
  have e2 : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ' (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ' y) := by
    intro τ g hg y
    rw [hΦ', hΦ', hequiv τ g hg y, he]
  obtain ⟨r1, r2, -, r4, -, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  let U : Subgroup (GA D V) := K.comap (GlobalTheory.AutMult.toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hK.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ' y) = Φ' y := by
    intro y k hk hk'
    have h1 : (⟨k, hk'⟩ : GfC V) ∈ K := by
      have h2 : GlobalTheory.AutMult.toFin V k ∈ K := hk
      rwa [show GlobalTheory.AutMult.toFin V k = ⟨k, hk'⟩ from GlobalTheory.AutMult.toFin_coe (⟨k, hk'⟩ : GfC V)] at h2
    rw [hΦ', ← he]
    exact congrArg e (hKfix _ h1 y)
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ' e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ' fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  have p1' : ∀ y : M.Vec, Repr V μ 𝓕 (e (Φ fun τ => (y τ : M.H τ))) (ψ y) := fun y => hΦ' _ ▸ p1 y
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ' fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ'.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ'.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU
  have hEq : GlobalTheory.RepSmooth.IsEquiv θ T := by
    intro τ g hg y z hz
    refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  have cont_value {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
      (Φ : ContinuousMultilinearMap ℂ M.H K) (T : MMap M)
      (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
      (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
        Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
      (L : List (List (D.what₂.Tau × Mt V.rank))) (hL : ∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) (x : GA D V) (C : ℝ)
      (hC : ∀ y : M.Vec, ‖T y x‖ ≤ C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ))‖).sum)
      (τ : D.what₂.Tau) (v : M.Vec) :
      ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := by
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ((LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ)
    have hℓ' : ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := fun w => LinearMap.congr_fun hℓ w
    refine ⟨ℓ, ?_, hℓ'⟩
    obtain ⟨C', hC', hb⟩ := sum_bound
      (fun l (w : M.sm τ) => ‖l.foldr (dL2 θ V ρ) (Φ fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖)
      (fun l (w : M.sm τ) => ‖(lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => norm_nonneg _) L (by
        intro l hl
        refine ⟨‖Φ.toContinuousLinearMap (fun σ => (lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ‖, fun w => ?_⟩
        refine le_trans (le_of_eq ?_) (ContinuousLinearMap.le_opNorm _ _)
        rw [word_map ρ Φ hsm hΦ l (hL l hl), ContinuousMultilinearMap.toContinuousLinearMap_apply]
        congr 2
        funext σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Function.update_of_ne h])
    refine ⟨L.map (lettersAt τ), |C| * C', ?_, fun w hw => ?_⟩
    · intro l hl
      obtain ⟨l', h', rfl⟩ := List.mem_map.1 hl
      exact lettersAt_mem (hL l' h')
    · have hw' : w ∈ M.sm τ := Submodule.subset_span hw
      have h1 := hℓ' ⟨w, hw'⟩
      have h2 := hb ⟨w, hw'⟩
      have h3 := hC (Function.update v τ ⟨w, hw'⟩)
      rw [List.map_map, mul_assoc]
      simp only at h1
      rw [h1]
      refine h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg ?_)).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
      intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have word_value (T : MMap M)
      (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
      (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
        Rder θ V τ X (T y) = T (Function.update y τ w))
      (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
      ∃ y', l.foldr (fun p f => Rder θ V p.1 p.2 f) (T y) = T y' := by
    induction l with
    | nil => exact ⟨y, rfl⟩
    | cons p l ih =>
      obtain ⟨y', h⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hp := hl p List.mem_cons_self
      exact ⟨_, by rw [List.foldr_cons, h]; exact hT y' p.1 p.2 hp ⟨_, hsm _ _ hp (y' p.1)⟩ rfl⟩
  have hSob : GlobalTheory.RepSmooth.IsSob T := by
    intro τ y x
    obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ' T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this
  have hmult : IsMultMap θ M ∅ (fun _ => 1) T := by
    refine ⟨fun y => ⟨p2 y, p3 y, GlobalTheory.RepSmooth.zfin hEq hSob y, N, fun l hl x => ?_⟩, fun y => ?_,
      fun y k hk => hk.elim, hEq, hSob⟩
    · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
      obtain ⟨C, hC⟩ := hgr x
      refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ' fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
      rw [hy', mul_right_comm]
      exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
    · exact GlobalTheory.T.cuspidal_of_continuous_representative D V μ _ (hcusp _) (ψ y) (p2 y).cont (p2 y).left ((hrep _ _).1 (p1' y))
  exact ⟨T, Submodule.subset_span hmult, fun v => (hrep _ _).1 (p1' v)⟩

end GlobalTheory.CuspRepr
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
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  first | exact @GlobalTheory.TrPtFrame.exists_splitFrame_levG | exact GlobalTheory.TrPtFrame.exists_splitFrame_levG | (intros; apply GlobalTheory.TrPtFrame.exists_splitFrame_levG <;> assumption)
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

theorem _root_.GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ hU : IsSubrep π ⊤, IsCopyFinDS (finPartDSSm M hU) M π ⊤ := by
  first | exact @GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm | exact GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm | (intros; apply GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.CoreOnto

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem coefPlus_is (G : GridData L sc) (θ : InfFam D) (hθ : IsInfFam θ) : (coefPlus G θ).Is := by
  obtain ⟨hc, hs⟩ := GlobalTheory.CoefModel.realGL_laws hθ (Xp G)
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Xp G).gram
  refine GlobalTheory.CoefModel.coefOf_is _ _ _ (fun h hh => ?_) (fun h τ => ?_) (fun τ => ?_) (fun g hg => ?_)
  · have : GlobalTheory.CoefModel.realGL θ (Xp G) h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom (Xp G) h) = 1
      rw [show infHom (Xp G) h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, this, map_one]
  · exact GlobalTheory.CoefModel.invTr_unitary (g := GlobalTheory.CoefModel.realGL θ (Xp G) h τ)
      (GlobalTheory.RecDictModel.archM_unitary _ (hθ τ) h)
  · refine ((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹ τ : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) ℂ) = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (invTrK g) fun τ => by
      have := GlobalTheory.CoefModel.invTr_unitary (hg τ)
      rwa [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (posDef_Xp G _).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, e]
    exact funext fun τ => GlobalTheory.CoefModel.invTr_invTr _

theorem eps_core_m (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m))) :
    ∀ τ a, M.ε τ a = true := by
  intro τ a
  obtain ⟨-, q, -, hS⟩ := M.enum τ
  have h : (q a, M.ε τ a) ∈ Node.par D sc.cGap (.core D.R.m) τ := hS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
  have e : Node.par D sc.cGap (.core D.R.m) τ = (num D sc.cGap τ).parX 0 := (num D sc.cGap τ).parPi_m
  rw [e] at h
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 h
  exact (congrArg Prod.snd hx).symm

theorem topCols : TopCols := by
  intro D _ T L μ0 _ sc G W Mv _ M y hy w
  obtain ⟨pr, hpr⟩ := GlobalTheory.T.exists_dualPair_positiveWeightCoefficientSpace G W.θ W.θ_is M
  obtain ⟨c, hc, e⟩ := GlobalTheory.T.exists_column_perfectPairing_definiteCoreNode G W.θ W.θ_is M (eps_core_m G M) (coefPlus_is G W.θ W.θ_is) pr hpr y hy
  refine ⟨c, hc, pr.flip w, ?_⟩
  subst e
  rfl

end GlobalTheory.CoreOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreVacRe

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem reLat_sigOK (G : GridData L sc) (i : ℕ) (h : i ≤ D.R.m) (r : ReLat (G.V (.core i))) : r.sp.SigOK :=
  (G.isV (X := .core i) (by simpa [Node.InRange] using h) (by simp)).sigOK

theorem frameLat_selfDual (V : HSp D) : IsSelfDualC V (GlobalTheory.AdelicU.frameLat V) := by
  have e : GlobalTheory.AdelicU.frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [GlobalTheory.AdelicU.mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [e]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem vacExists_reLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i)))
    (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'),
    ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _)
      (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  intro D _ _ _ _ _ _ G W _ _ i hi r r' S S' M M'
  exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is r.sp r'.sp (cart M) (cart M')
    (reLat_sigOK G i hi.le r) (reLat_sigOK G (i + 1) hi r')
    (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ) (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M' τ)
    _ _ (frameLat_selfDual r.sp) (frameLat_selfDual r'.sp)

end GlobalTheory.CoreVacRe

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefTensorProof

theorem coefTensor : CoefTensor := by
  intro D V θ c hθ hc
  classical
  haveI : Nontrivial c.W := hc.2.2.2.1
  haveI : Nontrivial (Module.Dual ℂ c.W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_pos
  let a : ∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.UH (gramAt D V τ) → Module.End ℂ (Module.Dual ℂ c.W) :=
    fun τ g => (c.ρ (atTau θ V τ g.1)⁻¹).dualMap
  have ha : ∀ τ (g : Formalism.QuantumDeterminants.UH (gramAt D V τ)) f, a τ g f = f ∘ₗ c.ρ (atTau θ V τ g.1)⁻¹ := fun _ _ _ => rfl
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g h, a τ g * a τ' h = a τ' h * a τ g := by
    intro τ τ' hne g h
    have hc' := GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne g.1 g.2 h.1 h.2
    ext f w
    simp only [Module.End.mul_apply, ha, LinearMap.comp_apply]
    rw [← Module.End.mul_apply (c.ρ _), ← map_mul, ← Module.End.mul_apply (c.ρ _), ← map_mul, ← mul_inv_rev,
      ← mul_inv_rev, hc']
  have hirrD : ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ g, ∀ x ∈ N, a τ g x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => GlobalTheory.T.dual_irreducible_coefficientSpace_realPlaces D V θ c hθ hc N fun τ g hg f hf => hN τ ⟨g, hg⟩ f hf
  obtain ⟨X, i1, i2, i3, b, m, e, hinj, hint, hirr, heq⟩ := GlobalTheory.T.exists_tensorDecomposition_commutingFamilies D.what₂.Tau (Module.Dual ℂ c.W) _ a hcomm hirrD
  have hone : ∀ τ, atTau θ V τ 1 = 1 := fun τ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
  let π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (X τ) := fun τ g =>
    if hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then b τ ⟨g, hg⟩ else 1
  have hπ : ∀ τ g (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), π τ g = b τ ⟨g, hg⟩ := fun τ g hg => dif_pos hg
  refine ⟨X, i1, i2, i3, π, e, fun τ => ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  ·
    rw [hπ τ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _)]
    ext x
    apply hinj τ
    rw [hint, ha]
    show m τ x ∘ₗ c.ρ (atTau θ V τ 1)⁻¹ = m τ x
    rw [hone, inv_one, map_one]
    rfl
  · intro g hg h hh
    rw [hπ τ _ (GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh), hπ τ g hg, hπ τ h hh]
    ext x
    apply hinj τ
    rw [Module.End.mul_apply, hint, hint, hint]
    ext w
    simp only [ha, LinearMap.comp_apply]
    rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hh, mul_inv_rev, map_mul, Module.End.mul_apply]
  · intro w l
    obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (m τ) (LinearMap.ker_eq_bot.2 (hinj τ))
    obtain ⟨v, hv⟩ : ∃ v : c.W, ∀ φ : Module.Dual ℂ c.W, (l ∘ₗ r) φ = φ v :=
      ⟨(Module.evalEquiv ℂ c.W).symm (l ∘ₗ r), fun φ => by
        conv_lhs => rw [← (Module.evalEquiv ℂ c.W).apply_symm_apply (l ∘ₗ r)]
        rfl⟩
    refine (GlobalTheory.T.contragredient_matrix_coefficient_continuousOn_unitary D V θ c hθ hc τ (m τ w) v).congr fun g hg => ?_
    show l (π τ g w) = _
    rw [hπ τ g hg]
    have : l (b τ ⟨g, hg⟩ w) = (l ∘ₗ r) (m τ (b τ ⟨g, hg⟩ w)) := by
      rw [LinearMap.comp_apply, ← LinearMap.comp_apply r, hr, LinearMap.id_apply]
    rw [this, hv, hint, ha, LinearMap.comp_apply]
  · intro U hU
    exact hirr τ U fun g x hx => by rw [← hπ τ g.1 g.2]; exact hU g.1 g.2 x hx
  · intro τ g hg x y hy hy'
    have : y = Function.update x τ (b τ ⟨g, hg⟩ (x τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h; rw [Function.update_self, hy, hπ _ g hg]
      · rw [Function.update_of_ne h, hy' τ' h]
    rw [this, heq]
    rfl

end GlobalTheory.CoefTensorProof
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem coreOnto_of_chain (hO : ∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) (hC : ComOK) (hS : StageOK) (hE : ChainEx) (hT : TopCols) :
    CoreOnto := by
  intro D hq hsz T L μ0 hL sc hgap G W M hM v MP _hcart y hy x hx
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D
  obtain ⟨⟨r₀, hr₀⟩, hst₀⟩ := hS D hq T L μ0 hL sc G W M hM 0 (Nat.zero_le _)
  obtain ⟨r, Mm, _hr, Θ, hR, hB⟩ := hE D hq hsz T L μ0 hL sc hgap G W M hM v r₀ MP hr₀ D.R.m le_rfl
  have hcom : (gridCom W).Is := hC D hq hsz T L μ0 hL sc hgap G W M hM
  have hs0 : (gridStage G v 0 r₀ MP).Is (gridCom W) 0 := hst₀ r₀ hr₀ v MP
  have hsurj := hO D (gridCom W) hcom (gridStage G v 0 r₀ MP) hs0 D.R.m le_rfl _ Θ hR
  have hyCC : y ∈ (gridStage G v 0 r₀ MP).CC (gridCom W) := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).1
    exact (SetLike.ext_iff.mp h y).mpr hy
  obtain ⟨y', hy'⟩ := hsurj ⟨y, hyCC⟩
  have hx' : x ∈ (gridStage G v 0 r₀ MP).KF := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).2.1
    rw [← h] at hx
    exact hx
  have key := hB y' x hx'
  rw [hy'] at key
  refine Submodule.span_mono ?_ key
  rintro F₀ ⟨w, Ψ, hrap, hstep, h0, hm⟩
  refine ⟨Ψ, ⟨hrap, hstep⟩, h0, ?_⟩
  have htop : y'.1 ∈ CoreForms G W.θ D.R.m Mm := by
    have h := (hRL.2.1 (G.V (.core D.R.m)) r W.θ _ Mm (lev G (.core D.R.m) : Set _)).1
    exact (SetLike.ext_iff.mp h y'.1).mp y'.2
  obtain ⟨c, hc, ξ, hξ⟩ := hT D hq T L μ0 hL sc G W M hM Mm _ htop w
  exact ⟨c, hc, ξ, hm.trans hξ⟩

end GlobalTheory.CoreOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodRows_principalLevel_are_rows : GoodRows := by
  first | exact @GlobalTheory.SepRows.goodRows | exact GlobalTheory.SepRows.goodRows | (intros; apply GlobalTheory.SepRows.goodRows <;> assumption)
end
