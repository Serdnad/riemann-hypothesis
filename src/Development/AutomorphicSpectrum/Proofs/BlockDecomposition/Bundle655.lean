module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle130
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import GroundTheory.GlobalFields.TateThesis.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle643
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SocleJm

section General

variable {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem jhMult_le_of_injective {σ : Representation ℂ G U} {ρ₁ : Representation ℂ G V}
    {ρ : Representation ℂ G W} (hσ : σ.IsIrreducible) (ι : ρ₁.IntertwiningMap ρ)
    (hι : Function.Injective ι) : jhMult σ ρ₁ ≤ jhMult σ ρ := by
  let R : Subrepresentation ρ := ι.range
  let p : ρ.IntertwiningMap (subQuot ⊤ R) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  rw [jhMult_exact ι p hσ hι (fun x => ?_) (fun u => (hp _).2 ⟨u, rfl⟩) (fun v hv => (hp v).1 hv)]
  · exact le_self_add
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W U X : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]

theorem jhMult_jac_exact (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) X}
    (hσ : σ.IsIrreducible) {π : Representation ℂ (GL n k) V} {π₁ : Representation ℂ (GL n k) W}
    {π₂ : Representation ℂ (GL n k) U} (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂)
    (hπ : IsSmooth π) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (he : Function.Exact ι p) :
    jhMult σ (_root_.GlobalTheory.SmGL.jac e π) = jhMult σ (_root_.GlobalTheory.SmGL.jac e π₁) + jhMult σ (_root_.GlobalTheory.SmGL.jac e π₂) := by
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacInj.jacMap_injective k _ _ _ e W V π₁ π ι hπ hι) (fun x => ?_) (fun x => ?_)
    (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem one_le_jhMult_jac (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {τ : Representation ℂ (GL n k) V} (f : τ.IntertwiningMap (parInd e ρ))
    (hf : ∃ v, f v ≠ 0) : 1 ≤ jhMult ρ (_root_.GlobalTheory.SmGL.jac e τ) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Subtype.ext (Subtype.ext (funext h)))
  let φ := GlobalTheory.SmGL.Model.evalOne e f
  have h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0 := by
    have : φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x := by
      show (f (τ x v)).1.1 1 = _
      rw [f.isIntertwining, parInd_apply, one_mul]
    rwa [this]
  have h2 : Function.Surjective φ := by
    intro w
    rcases eq_bot_or_eq_top φ.range with e' | e'
    · have h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range :=
        (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩
      rw [e'] at h3
      exact absurd h3 h1
    · have h3 : w ∈ φ.range := e' ▸ trivial
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).1 h3
  exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible (GL (Fin (x a).1) k) (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ (x a).rep (x a).2.rep.irr
      (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem exists_isSocle_of_forall_isAtom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) [Nontrivial V]
    (hfl : HasFiniteLength π)
    (hone : ∀ T : Subrepresentation π, IsAtom T → 1 ≤ jhMult ρ (_root_.GlobalTheory.SmGL.jac e T.toRepresentation))
    (hjm : jhMult ρ (_root_.GlobalTheory.SmGL.jac e π) ≤ 1) : ∃ τ : IrrRep (GL n k), IsSocle τ.ρ π := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have huniq : ∀ T : Subrepresentation π, IsAtom T → T = S := by
    intro T hT
    by_contra hne
    have hdis : T ⊓ S = ⊥ := (hT.disjoint_of_ne hS hne).eq_bot
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have hadd := jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      have h1 : (u : V) ∈ S.toSubmodule := (hp0 _).1 hu
      have h2 : (u : V) ∈ (T ⊓ S) := ⟨u.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h1 : 1 ≤ jhMult ρ (_root_.GlobalTheory.SmGL.jac e (subQuot ⊤ S)) :=
      (hone T hT).trans (jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have h2 : (2 : ℕ∞) ≤ jhMult ρ (_root_.GlobalTheory.SmGL.jac e π) := by
      rw [hadd]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add (hone S hS) h1)
    exact absurd (h2.trans hjm) (by norm_num)
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  refine ⟨⟨S.toSubmodule, S.toRepresentation,
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs, hirr⟩, hirr, ι,
    Subtype.val_injective, fun T hT => ?_⟩
  rw [huniq T hT]
  refine SetLike.ext fun v => ⟨fun hv => (Representation.IntertwiningMap.mem_range _ _ _ _).2
    ⟨⟨v, hv⟩, rfl⟩, fun hv => ?_⟩
  obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hv
  exact u.2

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ) : Nontrivial (IndSp e ρ) := by
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρ
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hsρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem one_le_jhMult_jac_atom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (T : Subrepresentation (parInd e ρ)) (hT : IsAtom T) :
    1 ≤ jhMult ρ (_root_.GlobalTheory.SmGL.jac e T.toRepresentation) := by
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  refine one_le_jhMult_jac e hρ ιT ?_
  by_contra hc
  push_neg at hc
  exact hT.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv =>
    (Submodule.mem_bot ℂ).2 (hc ⟨v, hv⟩)))

theorem exists_isSocle_of_jm_le_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 →
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  intro k _ _ _ _ hA h N x hd hjm
  have hρ := isIrreducible_piTensor hA x
  have hsρ : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor fun a => (x a).2.rep.smooth
  haveI := nontrivial_indSp (stdBlocks (fun a => (x a).1) hd) hρ hsρ
  exact exists_isSocle_of_forall_isAtom (stdBlocks (fun a => (x a).1) hd) hρ
    (isSmooth_parInd _ _)
    (GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))
    (one_le_jhMult_jac_atom _ hρ) hjm

end GlobalTheory.CompanionTheory.SocleJm

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

section Family

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
  [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)]
  [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_pi_subset
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    (U : Set (∀ a, Γ a)) (hU : U ∈ nhds (1 : ∀ a, Γ a)) :
    ∃ H : ∀ a, Subgroup (Γ a), (∀ a, IsOpen (H a : Set (Γ a))) ∧ (∀ a, IsCompact (H a : Set (Γ a))) ∧
      ((Subgroup.pi Set.univ H : Subgroup (∀ a, Γ a)) : Set (∀ a, Γ a)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose H hHo hHc hHs using fun a => hG a (t a) (ht a)
  refine ⟨H, hHo, hHc, fun x hx => hsub fun a _ => hHs a ?_⟩
  exact (Subgroup.mem_pi Set.univ).mp hx a (Set.mem_univ a)

theorem pi_compactOpen_basis
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U) :
    ∀ U ∈ nhds (1 : ∀ a, Γ a), ∃ K : Subgroup (∀ a, Γ a), IsOpen (K : Set (∀ a, Γ a)) ∧
      IsCompact (K : Set (∀ a, Γ a)) ∧ (K : Set (∀ a, Γ a)) ⊆ U := by
  intro U hU
  obtain ⟨H, hHo, hHc, hsub⟩ := exists_pi_subset hG U hU
  refine ⟨Subgroup.pi Set.univ H, ?_, ?_, hsub⟩
  · show IsOpen (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isOpen_set_pi Set.finite_univ fun a _ => hHo a
  · show IsCompact (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isCompact_univ_pi fun a => hHc a

theorem isAdmissible_piTensor [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K ho hc => ?_⟩
  obtain ⟨H, h1, h2, h3⟩ := exists_pi_subset hG _ (ho.mem_nhds (one_mem K))
  haveI : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (H a)) := fun a => (hρ a).2 _ (h1 a) (h2 a)
  let M : (⨂[ℂ] a, fixed (ρ a) (H a)) →ₗ[ℂ] ⨂[ℂ] a, X a :=
    PiTensorProduct.map fun a => (fixed (ρ a) (H a)).subtype
  have hle : fixed (piTensor ρ) K ≤ LinearMap.range M := by
    intro w hw
    have hs := GlobalTheory.SmGL.IndTensor.mem_span_of_fixed (fun a => (hρ a).1) h2 w fun h hh =>
      GlobalTheory.ContraRefl.mem_fix.1 hw h (h3 hh)
    refine Submodule.span_le.2 ?_ hs
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun a => ⟨v a, hv a⟩, by simp [M]⟩
  exact Submodule.finiteDimensional_of_le hle

def pairForm (ρ : ∀ a, Representation ℂ (Γ a) (X a)) :
    (⨂[ℂ] a, X a) →ₗ[ℂ] (⨂[ℂ] a, smoothPart (ρ a).dual) →ₗ[ℂ] ℂ :=
  ((PiTensorProduct.dualDistrib (R := ℂ) (M := X)) ∘ₗ
    PiTensorProduct.map fun a => (smoothPart (ρ a).dual).subtype).flip

theorem pairForm_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (v : ∀ a, X a)
    (l : ∀ a, smoothPart (ρ a).dual) :
    pairForm ρ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ l) =
      ∏ a, (l a : Module.Dual ℂ (X a)) (v a) := by
  simp only [pairForm, LinearMap.flip_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply, Submodule.subtype_apply]

theorem pairForm_invariant (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a)
    (s : ⨂[ℂ] a, X a) (t : ⨂[ℂ] a, smoothPart (ρ a).dual) :
    pairForm ρ (piTensor ρ g s) (piTensor (fun a => contra (ρ a)) g t) = pairForm ρ s t := by
  have hpt : ∀ v : ∀ a, X a, piTensor ρ g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun a => ρ a (g a) (v a)) := by
    intro v
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  have hpt' : ∀ l : ∀ a, smoothPart (ρ a).dual, piTensor (fun a => contra (ρ a)) g (PiTensorProduct.tprod ℂ l) =
      PiTensorProduct.tprod ℂ (fun a => contra (ρ a) (g a) (l a)) := by
    intro l
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (contra (ρ a)).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ l) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  refine PiTensorProduct.induction_on s (fun r v => ?_) (fun x y hx hy => ?_)
  · refine PiTensorProduct.induction_on t (fun r' l => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, LinearMap.smul_apply]
      rw [hpt, hpt', pairForm_tprod, pairForm_tprod]
      congr 2
      refine Finset.prod_congr rfl fun a _ => ?_
      show (l a : Module.Dual ℂ (X a)) (ρ a (g a)⁻¹ (ρ a (g a) (v a))) = (l a : Module.Dual ℂ (X a)) (v a)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · simp only [map_add (f := _), hx, hy]
  · simp only [map_add (f := _), LinearMap.add_apply, hx, hy]

theorem nonempty_equiv_piTensor_contra [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a))
    (hi : ∀ a, (ρ a).IsIrreducible) :
    Nonempty ((piTensor fun a => contra (ρ a)).Equiv (contra (piTensor ρ))) := by
  have hK : ∀ a, ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧ IsCompact (K : Set (Γ a)) := fun a => by
    obtain ⟨K, h1, h2, -⟩ := hG a Set.univ Filter.univ_mem
    exact ⟨K, h1, h2⟩
  choose K0 hK1 hK2 using hK
  have hschur : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) (X a) (ρ a) (hi a) (hρ a)
  have hci : ∀ a, (contra (ρ a)).IsIrreducible := fun a =>
    GlobalTheory.ContraRefl.contra_isIrreducible (hG a) (hρ a) (hi a)
  have hca : ∀ a, IsAdmissible (contra (ρ a)) := fun a =>
    GlobalTheory.SmGL.ContraTrace.isAdmissible_contra (hρ a)
  have hcschur : ∀ a, ∀ φ : smoothPart (ρ a).dual →ₗ[ℂ] smoothPart (ρ a).dual,
      (∀ g x, φ (contra (ρ a) g x) = contra (ρ a) g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) _ (contra (ρ a)) (hci a) (hca a)
  have hI : (piTensor ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur ρ hi hschur
  have hI' : (piTensor fun a => contra (ρ a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hci hcschur
  have hCI : (contra (piTensor ρ)).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (pi_compactOpen_basis hG) (isAdmissible_piTensor hG hρ) hI
  have hB0 : pairForm ρ ≠ 0 := by
    have hne : ∀ a, ∃ v : X a, v ≠ 0 := fun a => by
      by_contra h
      push_neg at h
      apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
      apply Subrepresentation.ext
      ext x
      rw [h x]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    choose v hv using hne
    choose l hl using fun a => GlobalTheory.ContraRefl.exists_smooth_form_ne (hρ a).1 (hG a) (hv a)
    intro h0
    have h1 := pairForm_tprod ρ v l
    rw [h0] at h1
    exact Finset.prod_ne_zero_iff.2 (fun a _ => hl a) (by simpa using h1.symm)
  exact ⟨(GlobalTheory.InvPairing.pairMap (piTensor ρ) (isSmooth_piTensor fun a => isSmooth_contra (ρ a))
    (pairForm ρ) (pairForm_invariant ρ)).ofBijective (GlobalTheory.InvPairing.pairMap_bijective _ _ _ _ hB0 hI' hCI)⟩

end Family

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem contra_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    (contra x.rep).IsIrreducible :=
  GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1)
    (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr

theorem contra_piTensor_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    Nonempty ((piTensor fun a => contra (x a).rep).Equiv (contra (piTensor fun a => (x a).rep))) := by
  haveI : ∀ a, T2Space (GL (Fin (x a).1) k) := fun a => GlobalTheory.SplitFlip.t2Space_general_linear_group
  exact nonempty_equiv_piTensor_contra (Γ := fun a => GL (Fin (x a).1) k)
    (fun a => GlobalTheory.SqIntUnit.compactOpen_basis k (x a).1)
    (fun a => hA k (x a).1 _ (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)
    fun a => (x a).2.rep.irr

theorem parInd_equiv_contra {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) V} {ρ : Representation ℂ (Levi k m) W}
    (hρ : IsSmooth ρ) (φ : Nonempty (σ.Equiv (contra ρ))) :
    Nonempty ((parInd e σ).Equiv (contra (parInd e ρ))) := by
  obtain ⟨φ⟩ := φ
  obtain ⟨ψ⟩ := InductionContragredient.nonempty_equiv (GlobalTheory.CompanionTheory.Glob.inductionContragredient k) e hρ
  exact ⟨(parIndEquiv e φ).trans ψ⟩

theorem contra_prodIrr_multiProd (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks (fun a => (x a).1) hd) fun a => contra (x a).rep).Equiv
      (contra (prodIrr x hd))) :=
  parInd_equiv_contra (stdBlocks (fun a => (x a).1) hd)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (contra_piTensor_rep hA x)

theorem contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N,
      Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  intro k _ _ _ _ hA h N x hd
  have hci := fun a => contra_rep_isIrreducible hA (x a)
  have hy : (fun a => dualCl (x a)) =
      fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a) :=
    funext fun a => dif_pos (hci a)
  have key : ∀ y : Fin h → IrrGL (k := k),
      y = (fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a)) →
      ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd')) := by
    rintro _ rfl
    exact ⟨hd, (contra_prodIrr_multiProd hA x hd).map fun ψ => ψ.symm.trans
      (prodIrrEquiv hd (fun a => contra (x a).rep) (fun a => isSmooth_smoothRep _) hci)⟩
  exact key _ hy

end GlobalTheory.CompanionTheory.ContraProd

end
end

section

noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuOpen

theorem isOpen_ker_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) (w : HeightOneSpectrum (𝓞 L)) :
    IsOpen ((χ.loc w).ker : Set (w.adicCompletion L)ˣ) :=
  GroundTheory.Global.isOpen_ker_of_continuous w GroundTheory.Global.Complex.units_noSmallSubgroups (χ.loc w)
    (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w))

theorem unrChar_apply_of_isUnitAt {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (α : ℂˣ)
    (x : (w.adicCompletion L)ˣ) (hx : IsUnitAt w x) : GlobalTheory.SmGL.unrChar (w.adicCompletion L) α x = 1 := by
  rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion]
  have hx' : Valued.v (x : w.adicCompletion L) = 1 := hx
  rw [hx']
  simp

end GlobalTheory.CompanionTheory.MuOpen


open GlobalTheory.CompanionTheory.MuOpen in
theorem GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  intro h E _ _ _ hU
  obtain ⟨μ, e, hμ⟩ := h E hU
  refine ⟨μ, e, hμ, fun w hw x hx => ?_, GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ |>.1, fun w => isOpen_ker_loc μ w⟩
  rw [hμ.2.2.1 w hw]
  exact unrChar_apply_of_isUnitAt w _ x hx

end
end

section


theorem _root_.GlobalTheory.T.local_comparison_split : PositivityTheory.Rg.BcB.G8.Fin.LocCompareSplit := by
  first | exact @GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | exact GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | (intros; apply GlobalTheory.CompanionTheory.LcSplit.locCompareSplit <;> assumption)
end
