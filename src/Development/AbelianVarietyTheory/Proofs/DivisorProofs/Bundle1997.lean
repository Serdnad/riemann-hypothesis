module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle213
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1959
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageFactor

open MeasureTheory

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_add_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (P Q : PolF D WW.rank A.rank) (c : ℂ) (h : GA D WW) :
    X.ker ψ θ t (P + c • Q) h = fun g => X.ker ψ θ t P h g + c * X.ker ψ θ t Q h g := by
  funext g
  simp [Tri.ker, thetaKO, map_add (f := _), map_smul]

def linI (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) : PolF D WW.rank A.rank →ₗ[ℂ] (GA D WW → ℂ) where
  toFun P := X.I ψ θ t P
  map_add' P Q := by
    funext h
    have e := ker_add_smul X ψ θ t P Q 1 h
    simp only [one_smul, one_mul] at e
    simp only [Tri.I, Pi.add_apply, e]
    exact integral_add (hint P h) (hint Q h)
  map_smul' c Q := by
    funext h
    have e := ker_add_smul X ψ θ t 0 Q c h
    simp only [zero_add] at e
    have e0 : X.ker ψ θ t 0 h = 0 := by funext g; simp [Tri.ker, thetaKO]
    simp only [Tri.I, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e, e0, Pi.zero_apply, zero_add]
    exact integral_const_mul c _

theorem linI_apply (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) (P : PolF D WW.rank A.rank) :
    linI X ψ θ t hint P = X.I ψ θ t P := rfl

theorem factor_of_parts (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (hint : ∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m)
    (hker : ∀ t t' P, X.I ψ θ t P = 0 → X.I ψ θ t' P = 0)
    (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank) (hlam : ∀ t, lam t ≠ 0)
    (hs : ∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I ψ θ t (s P') = lam t • X.I' ψ θ t P')
    (hconv : ∃ P', (∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' ψ θ t P' ≠ 0) :
    Factor X ψ θ lam := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · refine ⟨hlam, ModuleCat.of ℂ ℂ, MvPolynomial.lcoeff ℂ 0, MvPolynomial.lcoeff ℂ 0, fun _ => 0,
      fun z => ⟨MvPolynomial.C z, by simp⟩, fun t => hT.elim t, fun t => hT.elim t, fun t => hT.elim t,
      fun t => hT.elim t, 1, by simp, fun t => hT.elim t⟩
  · let K : Submodule ℂ (PolF D WW.rank A.rank) := LinearMap.ker (linI X ψ θ t₀ (hint t₀))
    have hK : ∀ t, LinearMap.ker (linI X ψ θ t (hint t)) = K := fun t => by
      ext P
      simp only [K, LinearMap.mem_ker, linI_apply]
      exact ⟨hker t t₀ P, hker t₀ t P⟩
    let Jb : T → ((PolF D WW.rank A.rank ⧸ K) →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
      K.liftQ (linI X ψ θ t (hint t)) (hK t).ge
    have hJb : ∀ t, Function.Injective (Jb t) := fun t => by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (hK t).le
    refine ⟨hlam, ModuleCat.of ℂ (PolF D WW.rank A.rank ⧸ K), K.mkQ, K.mkQ ∘ₗ s, fun t => (lam t)⁻¹ • Jb t,
      K.mkQ_surjective, fun t => ?_, hint, fun t P => ?_, fun t P' hP' => ?_, ?_⟩
    · intro x y hxy
      exact hJb t (smul_right_injective _ (inv_ne_zero (hlam t)) hxy)
    · show X.I ψ θ t P = lam t • ((lam t)⁻¹ • Jb t (K.mkQ P))
      rw [smul_smul, mul_inv_cancel₀ (hlam t), one_smul]
      rfl
    · show X.I' ψ θ t P' = (lam t)⁻¹ • Jb t (K.mkQ (s P'))
      have : Jb t (K.mkQ (s P')) = X.I ψ θ t (s P') := rfl
      rw [this, hs t P' hP', smul_smul, inv_mul_cancel₀ (hlam t), one_smul]
    · obtain ⟨P', hc, hne⟩ := hconv
      refine ⟨P', fun h0 => hne t₀ ?_, hc⟩
      have h1 : s P' ∈ K := (Submodule.Quotient.mk_eq_zero K).1 h0
      have h2 : X.I ψ θ t₀ (s P') = 0 := h1
      rw [hs t₀ P' (hc t₀)] at h2
      exact (smul_eq_zero.1 h2).resolve_left (hlam t₀)

end GlobalTheory.StageFactor

open GlobalTheory.StageFactor

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqTower.StageExists

theorem hasSignature_map_conj {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

def withIdx {D : D7} (V : HSp D) (p : ℕ) : HSp D := { V with sig := fun _ => (V.rank - p, p) }

theorem withIdx_sigOK {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) : (withIdx V p).SigOK := by
  intro σ
  show Formalism.UG.HasSignature (V.gram.map σ) (V.rank - p) p
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_conj (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1


open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem rig_exists {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  obtain ⟨r, e, hr⟩ := GlobalTheory.T.self_dual_lattice_has_rigidification D (withIdx V p) Λ (withIdx_sigOK h) hΛ
  exact ⟨⟨r.Λ, r.β, r.s, r.B⟩, e, hr⟩


open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem vac_exists {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S WW : HSp D} {p q : ℕ} (hS : NegIdx S p) (hW : NegIdx WW q) {r : Rig S} {rW : Rig WW} (h : r.Is) (h' : rW.Is) :
    (∃ f, IsVacO ψ θ (neg S) WW (fun τ => -r.s τ) rW.s r.Λ rW.Λ f) ∧ ∃ f, IsVacO ψ θ S WW r.s rW.s r.Λ rW.Λ f := by
  have hneg : IsSelfDualC (neg S) r.Λ := by
    refine ⟨h.1.1, fun y => (h.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  constructor
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (neg (withIdx S p)) (withIdx WW q) (fun τ => -r.s τ) rW.s
      (sigOK_sgn true (withIdx_sigOK hS)) (withIdx_sigOK hW) (fun τ => isCartanInv_sgn true S τ (h.2.2 τ).1)
      (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ hneg h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (withIdx S p) (withIdx WW q) r.s rW.s
      (withIdx_sigOK hS) (withIdx_sigOK hW) (fun τ => (h.2.2 τ).1) (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ h.1 h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩


end GlobalTheory.SqTower.StageExists

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BottomIsom

theorem hasSignature_map_star {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

theorem hasSignature_all {D : D7} {V : HSp D} (h : NegIdx V 0) (σ : D.host.E →+* ℂ) :
    Formalism.UG.HasSignature (V.gram.map σ) V.rank 0 := by
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_star (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1

def posResign {D : D7} (V : HSp D) : HSp D := { V with sig := fun _ => (V.rank, 0) }

theorem posResign_sigOK {D : D7} {V : HSp D} (h : NegIdx V 0) : (posResign V).SigOK := fun σ =>
  hasSignature_all h σ

theorem isoMat_of_posDef : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 →
    Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  intro D V V' hr h h'
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D (posResign V) (posResign V')
    (posResign_sigOK h) (posResign_sigOK h') hr (fun _ => by simp [posResign, hr])
  exact ⟨GlobalTheory.Mem.Isom.IsoMat.ofEquiv φ hφ⟩

end GlobalTheory.BottomIsom
end
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.LeviHC

section Alg

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def FinMod (K : Submodule ℂ M) (A : Subalgebra ℂ (Module.End ℂ M)) (v : M) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ A, y = K.mkQ (a v)})

def MonicFactorFinite : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (p q : ℂ → Module.End ℂ N),
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    ∀ v : N, FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range fun u => p u * q u), y = a v}) →
      FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range p), y = a v})

def MonicFactorFiniteMod : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K ∧ q u x ∈ K) →
    (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
    ∀ v ∈ M', FinMod K (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v

theorem coeff_mem_span {d : ℕ} {a : ℕ → M} {p : ℂ → M} (hp : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i)
    {i : ℕ} (hi : i < d + 1) : a i ∈ Submodule.span ℂ (Set.range p) := by
  set W := Submodule.span ℂ (Set.range p)
  have hdual : ∀ f : Module.Dual ℂ (M ⧸ W), f (W.mkQ (a i)) = 0 := by
    intro f
    let P : Polynomial ℂ :=
      ∑ j ∈ Finset.range (d + 1), Polynomial.C (f (W.mkQ (a j))) * Polynomial.X ^ j
    have hP : P = 0 := by
      apply Polynomial.funext
      intro u
      have h0 : W.mkQ (p u) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span ⟨u, rfl⟩)
      have h1 : f (W.mkQ (p u)) = ∑ j ∈ Finset.range (d + 1), u ^ j * f (W.mkQ (a j)) := by

        rw [hp u, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, smul_eq_mul]
      rw [h0, map_zero] at h1
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff i) hP
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_ite_eq] at hc
    simpa [Finset.mem_range.2 hi] using hc
  have hq : W.mkQ (a i) = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ _).1 hdual
  exact (Submodule.Quotient.mk_eq_zero W).1 hq

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}



variable (σ J) in
def IsLineOf {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z)


variable {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → GAd σ J}

theorem IsLineOf.skew (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 := by
  apply GlobalTheory.LineDerSum.skew_of_exp_unitary
  intro t
  obtain ⟨y, -, hy⟩ := hγ t
  rw [← hy, GlobalTheory.Orb.archMat_eq_archEquiv J h τ y]
  exact (archEquiv J h τ y).2

theorem IsLineOf.isRealLine (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : IsRealLine σ J γ := ⟨w, τ, Z, hγ.skew h, hγ⟩

private theorem conjTranspose_map_eq_of_isHermND (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← h.2.2.2 τ, hJ.1 i j]

private theorem isUnit_det_map_of_det_ne_zero {K : Type} [Field K] {m : ℕ} {M : Matrix (Fin m) (Fin m) K}
    (hM : M.det ≠ 0) (τ : K →+* ℂ) : IsUnit (M.map τ).det := by
  have hd : (M.map τ).det = τ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 hM

theorem conjTranspose_map (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := conjTranspose_map_eq_of_isHermND h hJ τ

omit [NumberField F] [NumberField E] in
theorem isUnit_det_map (hJ : IsHermND σ J) (τ : E →+* ℂ) : IsUnit (J.map τ).det := isUnit_det_map_of_det_ne_zero hJ.2 τ

variable {n₁ : ℕ}




end GlobalTheory.LeviHC

end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.formPart_eq_lintegral_image_injective_holomorphic : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (Ω : Set M) (Φ : M → V n) (γ : V n → Alt n), IsOpen Ω → Set.InjOn Φ Ω → (∀ x : A.Pt, x.pt ∈ Ω → DifferentiableAt ℂ (Φ ∘ x.ch.symm) x.crd ∧ β x = pull (fderiv ℂ (Φ ∘ x.ch.symm) x.crd) (γ (Φ x.pt))) → ∀ (s : ℤˣ) (T : Set M), MeasurableSet T → T ⊆ Ω → A.part β s T = ∫⁻ v in Φ '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
  first | exact @GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image | exact GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image | (intros; apply GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kernel_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H)
    (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧
    ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  intro R _ _ A _ hA L hL ha
  obtain ⟨Z, i, hci, hfin, hflat, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds R A hA L hL ha
  haveI : IsClosedImmersion i.left := hci
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hmem : ∀ (T : Over (Sp R)) (z : T ⟶ Z), GlobalTheory.MemKL A L (z ≫ i) := fun T z => (hZ T _).2 ⟨z, rfl⟩
  have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ A) = η[A] := by
    show toUnit _ ≫ η[A] = η[A]
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨o, ho⟩ := (hZ _ η[A]).1 (e1 ▸ memKL_one hL _)
  have e2 : (i ⊗ₘ i) ≫ μ[A] = (fst Z Z ≫ i) * (snd Z Z ≫ i) := by
    show (i ⊗ₘ i) ≫ μ[A] = lift (fst Z Z ≫ i) (snd Z Z ≫ i) ≫ μ[A]
    rw [lift_fst_comp_snd_comp]
  obtain ⟨m, hm⟩ := (hZ _ ((i ⊗ₘ i) ≫ μ[A])).1 (e2 ▸ GlobalTheory.UU.InK.mul hL (hmem _ _) (hmem _ _))
  have e3 : i ≫ GrpObj.inv = (𝟙 Z ≫ i)⁻¹ := by
    rw [Category.id_comp]; rfl
  obtain ⟨n, hn⟩ := (hZ _ (i ≫ GrpObj.inv)).1 (e3 ▸ GlobalTheory.UU.InK.inv hL (hmem _ _))
  obtain ⟨G, hG⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  exact ⟨Z, G, i, hG, hmono, hfin, hflat, hZ⟩

end GlobalTheory
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

theorem _root_.GlobalTheory.T.finsum_discreteSeriesCharacter_eq_weylCharacter : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℤ) (α : Fin n → ℂ) (ι : Type) [Finite ι]
    (y : ι → Equiv.Perm (Fin n)) (θ : ι → Fin n → ℝ), Odd n → Function.Injective α →
    Function.Bijective (fun p : compactWeyl ε × ι => (y p.2)⁻¹ * p.1.1) →
    (∀ q a, Complex.exp (θ q a * Complex.I) = α ((y q)⁻¹ a)) →
    ∑ᶠ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = glChar (hiWt lam) α := by
  first | exact @GlobalTheory.dsChar_finsum_eq_glChar | exact GlobalTheory.dsChar_finsum_eq_glChar | (intros; apply GlobalTheory.dsChar_finsum_eq_glChar <;> assumption)
end
