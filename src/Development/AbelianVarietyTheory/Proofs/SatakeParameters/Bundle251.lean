module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle151
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle101
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbExt

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

def scalarLift (φ : E →+* Om l) : ℚ_[l] ⊗[ℚ] E →ₐ[ℚ_[l]] Om l :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (Om l)) φ.toRatAlgHom (fun _ _ => Commute.all _ _)

theorem scalarLift_tmul (φ : E →+* Om l) (a : ℚ_[l]) (y : E) :
    scalarLift φ (a ⊗ₜ y) = algebraMap ℚ_[l] (Om l) a * φ y := by
  simp [scalarLift]

theorem exists_near (φ ψ : E →+* Om l) (t : ℚ_[l] ⊗[ℚ] E) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖scalarLift φ t - φ x‖ < ε ∧ ‖scalarLift ψ t - ψ x‖ < ε := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    intro ε hε
    have hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1 := by positivity
    obtain ⟨q, hq⟩ := Padic.rat_dense l a (div_pos hε hM)
    refine ⟨(q : E) * y, ?_, ?_⟩
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖φ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (ψ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖ψ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (φ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
  | add t₁ t₂ h₁ h₂ =>
    intro ε hε
    obtain ⟨x₁, a₁, b₁⟩ := h₁ (ε / 2) (half_pos hε)
    obtain ⟨x₂, a₂, b₂⟩ := h₂ (ε / 2) (half_pos hε)
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · have e : scalarLift φ (t₁ + t₂) - φ (x₁ + x₂) = (scalarLift φ t₁ - φ x₁) + (scalarLift φ t₂ - φ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (scalarLift φ t₁ - φ x₁) (scalarLift φ t₂ - φ x₂)]
    · have e : scalarLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (scalarLift ψ t₁ - ψ x₁) + (scalarLift ψ t₂ - ψ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (scalarLift ψ t₁ - ψ x₁) (scalarLift ψ t₂ - ψ x₂)]

theorem norm_scalarLift_le (φ ψ : E →+* Om l) (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (t : ℚ_[l] ⊗[ℚ] E) :
    ‖scalarLift ψ t‖ ≤ ‖scalarLift φ t‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, h₁, h₂⟩ := exists_near φ ψ t (ε / 2) (half_pos hε)
  have e1 : ‖scalarLift ψ t‖ ≤ ‖scalarLift ψ t - ψ x‖ + ‖ψ x‖ := by
    simpa using norm_add_le (scalarLift ψ t - ψ x) (ψ x)
  have e2 : ‖φ x‖ ≤ ‖φ x - scalarLift φ t‖ + ‖scalarLift φ t‖ := by
    simpa using norm_add_le (φ x - scalarLift φ t) (scalarLift φ t)
  rw [norm_sub_rev] at e2
  rw [← h x] at e1
  linarith

theorem norm_eq_of_same_place (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ = ‖φ x‖ := by
  apply _root_.GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace <;> assumption

theorem main : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := by
  intro D l _ w O _ _ _ Bw hj τ hτ LL' hLL
  let jE : D.host.E →+* Om l := Bw.j.comp (algebraMap D.host.E D.nd.Om)
  have hA := D.nd.plOm.2 w
  have hw := hj.mem_placesOver hA
  have hjE : ∀ x : 𝓞 D.host.E, ‖jE (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := norm_eq_of_same_place τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (scalarLift jE), scalarLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((norm_scalarLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (scalarLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change scalarLift jE (a ⊗ₜ y) ∈ _
      rw [scalarLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (scalarLift jE).range) := by
    have : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((scalarLift jE).range : Set (Om l)) :=
    Submodule.isClosed_of_finiteDimensional (Subalgebra.toSubmodule (scalarLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (scalarLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by change scalarLift jE (1 ⊗ₜ x) = jE x; rw [scalarLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (scalarLift jE)) (scalarLift τ) hker).comp
      (Ideal.quotientKerEquivRange (scalarLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict LL'.1.toSubalgebra (fun y => hLL (Bw.LL_split σ y)), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (scalarLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = scalarLift jE (1 ⊗ₜ x)
    rw [scalarLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (scalarLift τ) hker ((Ideal.quotientKerEquivRange (scalarLift jE)).symm
    (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = scalarLift τ (1 ⊗ₜ x)
  rw [scalarLift_tmul, map_one, one_mul]

end GlobalTheory.EmbExt
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SpanLoc

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → NG.isoTyp a.ρ S ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL
  obtain ⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩ := hloc

  have hci : c = i := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i := by
      refine hd.equalizer hc hi (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hcL, hiL]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → a.W), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hnt : Nontrivial σ.V := by
    haveI := σ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  unfold NG.isoTyp
  refine sSup_le ?_
  rintro S' ⟨hS'irr, Φ, hΦ⟩
  let Good : (σ.V →ₗ[ℂ] (GAf L n → a.W)) → Prop := fun T =>
    (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧
      ∀ u, T u ∈ S'
  let Wd : Submodule ℂ (GAf L n → a.W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS' : Wd ≤ S' := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
    refine iSup_le fun T => ?_
    exact le_iSup₂_of_le (f := fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T)
      T.1 ⟨fun u => hS'irr.1.le (T.2.2 u), T.2.1⟩ le_rfl

  have htr : ∀ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS'irr.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂

  let T1 : σ.V →ₗ[ℂ] (GAf L n → a.W) := S'.subtype ∘ₗ Φ.toLinearMap ∘ₗ LinearMap.codRestrict S T0 hT0S
  have hT1 : Good T1 := by
    refine ⟨fun x hx u => ?_, fun u => (Φ _).2⟩
    exact hΦ x ⟨T0 u, hT0S u⟩ ⟨T0 _, hT0S _⟩ (hT0eq x hx u)
  have hrc := hS'irr.2.2 Wd ⟨hWdS'.trans hS'irr.1.le, hstab⟩ hWdS'
  rcases hrc with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : σ.V)
    have hmem : T1 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T1, hT1⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    apply hu
    apply hT0inj
    have h2 : Φ (LinearMap.codRestrict S T0 hT0S u) = 0 := Subtype.ext hmem
    rw [map_zero]
    have h3 := Φ.injective (h2.trans Φ.map_zero.symm)
    exact congrArg Subtype.val h3
  · rw [← h0]; exact hWdle

end GlobalTheory.SpanLoc
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory

theorem germImage_smooth : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (U : Z.Opens), IsAffineOpen U → ∀ (h : genericPoint Z ∈ U) (B : Subalgebra ℂ Z.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) h).hom f = y) → Algebra.Smooth ℂ B := by
  intro Z _ p hp inst hinst U hU h B hB
  exact smooth_sections_in_functionField Z p hp hinst U hU h B hB

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EigenFactor

section Avg

variable {H W W' : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Avg

section Tensor

variable {β : Type} [Fintype β] [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)]

end Tensor

theorem exists_eig_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  first
  | exact @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | (apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector ..)

end GlobalTheory.EigenFactor
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HodgeCoh

section Alg
open GlobalTheory.CechDR

theorem mem_closure_smul_ιMulti_D (k B : Type) [CommRing k] [CommRing B] [Algebra k B] (z : DR k B) :
    z ∈ AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} := by
  set A := AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} with hA
  have hsmul : ∀ (b : B) (a : DR k B), a ∈ A → b • a ∈ A := by
    intro b a ha
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, c, v, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨q, b * c, v, by rw [smul_smul]⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have key : ∀ z : DR k B, ∀ a ∈ A, z * a ∈ A := by
    intro z
    induction z using indDR with
    | h b => intro a ha; rw [← Algebra.smul_def]; exact hsmul b a ha
    | hd b =>
      intro a ha
      induction ha using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨q, c, v, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨q + 1, c, Fin.cons b v, ?_⟩
        rw [mul_smul_comm, ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, Function.comp_def]
      | zero => rw [mul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
      | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | hm x y hx hy => intro a ha; rw [mul_assoc]; exact hx _ (hy a ha)
    | ha x y hx hy => intro a ha; rw [add_mul]; exact add_mem (hx a ha) (hy a ha)
  have h1 : (1 : DR k B) ∈ A :=
    AddSubgroup.subset_closure ⟨0, 1, Fin.elim0, by rw [ExteriorAlgebra.ιMulti_zero_apply, one_smul]⟩
  simpa using key z 1 h1

variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']

theorem SemiHom.mDR_ιMulti_D {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (q : ℕ) (v : Fin q → B) :
    h.mDR (ExteriorAlgebra.ιMulti B q fun i => D R B (v i)) =
      ExteriorAlgebra.ιMulti B' q fun i => D R' B' (α (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  exact (SemiHom.mDR_ι h _).trans (congrArg ι1 (SemiHom.m1_D h _))

theorem SemiHom.mDR_mDR {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''}
    {ρ : R →+* R''} {γ : B →+* B''} (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ)
    (e : ∀ b, β (α b) = γ b) (x : DR R B) : h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isDRMap_mDR {k K K' : Type} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra k B] {g : B →+* K} {γ : B →+* K'} (hg : SemiHom (RingHom.id k) g)
    (hγ : SemiHom (RingHom.id k) γ) {ψ : K →ₐ[k] K'} {φ : DR k K →ₗ[k] DR k K'}
    (hφ : IsDRMap k ψ φ) (e : ∀ b, ψ (g b) = γ b) (z : DR k B) : φ (hg.mDR z) = hγ.mDR z := by
  induction mem_closure_smul_ιMulti_D k B z using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨q, c, v, rfl⟩ := hw
    rw [SemiHom.mDR_smul, SemiHom.mDR_ιMulti_D, hφ q (g c) (fun i => g (v i)), SemiHom.mDR_smul,
      SemiHom.mDR_ιMulti_D]
    simp only [e]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  | neg x _ hx => rw [map_neg, map_neg, hx, map_neg]

end Alg

theorem formGermI_res_mapOver : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  intro Z Z' _ _ p p' inst inst' hinst hinst' f hf ψ φ hφ hψ j V V' hV hV' hη hη' h y
  subst hinst hinst'
  letI := algΓ p; letI := algΓ p'
  set x := (toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) with hx
  have hy : sectionsOn.toΓ _ _ y = toOm p j V x := by
    exact (LinearEquiv.apply_symm_apply (toOmEquiv p j hV) _).symm
  have hz : sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p' j) h
      (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
      toOm p' j V' (formRes p' h j (formPull hf V j x)) := by
    have h2 : (omegaPull hf j).app V (toOm p j V x) = toOm p' j (f ⁻¹ᵁ V) (formPull hf V j x) :=
      omegaPull_toOmega hf j V x
    rw [sectionsOn.toΓ_res, sectionsOn.toΓ_mapOver, hy, h2, res_toOm]
  letI := ffAlg p; letI := ffAlg p'
  rw [formGermI_ffAlg, formGermI_ffAlg]
  simp only [formGerm, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hz, ← toOmEquiv_apply p' j hV', LinearEquiv.symm_apply_apply, ← hx]
  have hγ : SemiHom (RingHom.id ℂ) ((germSec p' (h hη')).comp (appSec p p' f V)) :=
    fun r b ↦ (semiHom_appSec hf V).comp (semiHom_germSec p' (h hη')) r b
  rw [isDRMap_mDR (semiHom_germSec p hη) hγ hφ (fun b ↦ hψ V hη (h hη') b)]
  change (semiHom_germSec p' hη').mDR ((SemiHom.of_algHom (Sec.res p' h)).mDR
    ((semiHom_appSec hf V).mDR (x : DR ℂ (Sec p V)))) = _
  rw [SemiHom.mDR_mDR (semiHom_appSec hf V) (SemiHom.of_algHom (Sec.res p' h))
    ((semiHom_appSec hf V).comp (SemiHom.of_algHom (Sec.res p' h))) (fun _ ↦ rfl)]
  refine SemiHom.mDR_mDR _ (semiHom_germSec p' hη') hγ (fun b ↦ ?_) _
  change (Z'.presheaf.germ V' (genericPoint Z') hη').hom
      ((Z'.presheaf.map (homOfLE h).op).hom ((f.app V).hom b)) =
    (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') (h hη')).hom ((f.app V).hom b)
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

end GlobalTheory.HodgeCoh
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem normalisedFamily_standardBases_integrality : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hA hO hCS
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hCD, hH⟩ := hA
  obtain ⟨om, oms, ζ, hBD⟩ := GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData p g2 g3 s2 ε σ F hCD (nP D p) hO.even
  refine ⟨c, beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ, hc,
    ⟨σ, F, cob F (phFF p g2 g3 s2 ε), om, oms, ζ, hBD, rfl⟩, ?_⟩
  intro N N' L L' P P' hAdm hP hP' G hG R hR
  obtain ⟨r, b, hb, ho, hint⟩ := hH N N' L L' hAdm
  obtain ⟨f, f', hf, heq⟩ := GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst D p lam σ hCD.2.2.2.2.2.1 hO hCS om oms hBD.2.2.2.2.1 hBD.2.2.2.2.2.1
    R hR N N' L L' P P' hAdm hP hP' r b hb ho
  exact GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt D p g2 g3 s2 ε σ F hCD hO om oms ζ hBD R hR N N' r f f' hf (thOrth D lam c b G) (hint G hG) c
    (stdSer D lam (fun _ => 1) P P' G) (heq c G)

end GlobalTheory.KerStd
end
end
