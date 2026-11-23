module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle062
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
public import Mathlib.Analysis.Complex.Norm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply

@[expose] public section

section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.AdeleDen

private theorem natCast_mul_mem_intAd {F : Type} [Field F] [NumberField F] (m : ℕ)
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F} (ha : a ∈ PI.AdCpctDenWork.intAd F) :
    (m : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * a ∈ PI.AdCpctDenWork.intAd F := by
  rw [PI.AdCpctDenWork.mem_intAd] at ha ⊢
  intro v
  rw [PI.AdCpctDenWork.natCast_mul_apply]
  exact mul_mem (PI.AdCpctDenWork.natCast_mem_int v m) (ha v)

theorem exists_common_denominator :
    ∀ (E : Type) [Field E] [NumberField E] (Q : Set (Af E)), IsCompact Q →
    ∃ D : ℕ, D ≠ 0 ∧ ∀ x : E, algebraMap E (Af E) x ∈ Q → ∃ r : 𝓞 E, (r : E) = D * x := by
  intro E _ _ Q hQ
  let U : ℕ → Set (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) := fun N =>
    {a | ((N.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E}
  have hUo : ∀ N, IsOpen (U N) := fun N =>
    (continuous_const.mul continuous_id).isOpen_preimage _ PI.AdCpctDenWork.isOpen_intAd
  have hUc : Q ⊆ ⋃ N, U N := by
    intro a _
    obtain ⟨m, hm, hma⟩ := PI.AdCpctDenWork.exists_nat_adele a
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hm le_rfl
    show ((m.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E
    rw [hk, Nat.cast_mul, mul_comm (m : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E), mul_assoc]
    exact natCast_mul_mem_intAd k hma
  have hUd : Directed (· ⊆ ·) U := by
    refine Monotone.directed_le ?_
    intro N M hNM a ha
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hNM
    show ((M.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E
    rw [hk, Nat.cast_mul, mul_comm ((N.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E), mul_assoc]
    exact natCast_mul_mem_intAd k ha
  obtain ⟨N, hN⟩ := hQ.elim_directed_cover U hUo hUc hUd
  refine ⟨N.factorial, Nat.factorial_ne_zero N, fun x hx => ?_⟩
  have hmem := hN hx
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      IsDedekindDomain.HeightOneSpectrum.valuation E v ((N.factorial : E) * x) ≤ 1 := by
    intro v
    have h1 : algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) ((N.factorial : E) * x) ∈
        PI.AdCpctDenWork.intAd E := by
      rw [map_mul, map_natCast]
      exact hmem
    have h2 := (PI.AdCpctDenWork.mem_intAd _).1 h1 v
    rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
    exact h2
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hint
  exact ⟨r, by rw [NumberField.RingOfIntegers.coe_eq_algebraMap, hr]⟩

end GlobalTheory.CompanionTheory.AdeleDen
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDMap

variable {B : Type} [CommRing B] {J : Ideal B}

theorem fil_anti (δ : DividedPowers J) {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m := by
  refine Ideal.span_mono ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact ⟨l, h1, h.trans h2, rfl⟩

theorem fil_zero_top (δ : DividedPowers J) : fil δ 0 = ⊤ := by
  refine (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], ?_, ?_, ?_⟩) <;> simp

theorem dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n := by
  refine Ideal.subset_span ⟨[(n, x)], ?_, ?_, ?_⟩ <;> simp [hx]

theorem fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ⟨l, h1, h2, rfl⟩, b, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h1 p hp
    · exact h1' p hp
  · simpa using Nat.add_le_add h2 h2'
  · simp

theorem map_fil_le' {C : Type} [CommRing C] {J' : Ideal C} (δ : DividedPowers J) (δ' : DividedPowers J')
    (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) : (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

theorem fil_le_map {C : Type} [CommRing C] (δ : DividedPowers J) (f : B →+* C)
    (δ' : DividedPowers (J.map f)) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    fil δ' N ≤ (fil δ N).map f := by
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (fil_mul_le δ m n)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (dpow_mem_fil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (fil_anti δ h2) (hprod l h1)

theorem extended_dividedPowers : ∀ {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} (δ : DividedPowers J) (φ : B →+* B') (δ' : DividedPowers (J.map φ)), IsDPMorphism δ δ' φ → (∀ r, fil δ' r = (fil δ r).map φ) ∧ ∀ {B'' : Type} [CommRing B''] {J'' : Ideal B''} (δ'' : DividedPowers J'') (ψ : B' →+* B''), IsDPMorphism δ δ'' (ψ.comp φ) → IsDPMorphism δ' δ'' ψ := by
  intro B B' _ _ J δ φ δ' hφ
  refine ⟨fun r ↦ le_antisymm (fil_le_map δ φ δ' hφ r) (map_fil_le' δ δ' φ hφ r), ?_⟩
  intro B'' _ J'' δ'' ψ hψ
  refine IsDPMorphism.on_span δ' δ'' (S := φ '' (J : Set B)) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hψ.ideal_comp (Ideal.mem_map_of_mem (ψ.comp φ) ha)
  · rintro n _ ⟨a, ha, rfl⟩
    have h1 := hφ.dpow_comp (n := n) a ha
    have h2 := hψ.dpow_comp (n := n) a ha
    rw [h1]
    exact h2.symm

end GlobalTheory.CompanionTheory.PDMap
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

theorem _root_.GlobalTheory.T.schwartzBruhat_prod_span_tensors : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] (f : SB (A × B)), (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B, (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧ F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  first | exact @GlobalTheory.CompanionTheory.FrobProd.span_box | exact GlobalTheory.CompanionTheory.FrobProd.span_box | (intros; apply GlobalTheory.CompanionTheory.FrobProd.span_box <;> assumption)
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

theorem _root_.GlobalTheory.T.exists_schwartzBruhat_character_integral_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ), Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | exact GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | (intros; apply GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one <;> assumption)
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

theorem _root_.GlobalTheory.T.partial_integral_mem_schwartzBruhat : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B), (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  first | exact @GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | exact GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | (intros; apply GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SplitFrob

section Proj

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isCompl_toSubmodule {S S' : Subrepresentation π} (h : IsCompl S S') :
    IsCompl S.toSubmodule S'.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp h.1]
    try rfl
  · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp h.2]
    try rfl

def proj {S S' : Subrepresentation π} (h : IsCompl S S') : V →ₗ[ℂ] V :=
  S.toSubmodule.subtype ∘ₗ
    Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h)

theorem proj_left {S S' : Subrepresentation π} (h : IsCompl S S') {v : V} (hv : v ∈ S.toSubmodule) :
    proj h v = v := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = v
  simp only [Submodule.projectionOnto_apply_of_mem_left _ hv, Submodule.subtype_apply]

theorem proj_right {S S' : Subrepresentation π} (h : IsCompl S S') {v : V}
    (hv : v ∈ S'.toSubmodule) : proj h v = 0 := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = 0
  simp only [Submodule.projectionOnto_apply_of_mem_right _ hv, map_zero]

theorem proj_comm {S S' : Subrepresentation π} (h : IsCompl S S') (g : G) (v : V) :
    proj h (π g v) = π g (proj h v) := by
  have htop : S.toSubmodule ⊔ S'.toSubmodule = ⊤ := (isCompl_toSubmodule h).sup_eq_top
  have hv : v ∈ S.toSubmodule ⊔ S'.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add (f := _), proj_left h hx, proj_right h hy, proj_left h (S.apply_mem_toSubmodule g hx),
    proj_right h (S'.apply_mem_toSubmodule g hy), add_zero]

end Proj

section Induced

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {X : Type} [AddCommGroup X] [Module ℂ X]

def ev (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) : IndSp e ρ →ₗ[ℂ] X where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_unip (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {u : GL n k}
    (hu : u ∈ unipRad k e) (f : IndSp e ρ) : ev e ρ (parInd e ρ u f) = ev e ρ f := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu
  rw [MonoidHom.mem_ker] at hp
  have h := f.1.2 p 1
  rw [MonoidHom.comp_apply, hp, map_one, Module.End.one_apply, mul_one] at h
  show f.1.1 (1 * ((parab k e).subtype p)) = f.1.1 1
  rw [one_mul]
  exact h

theorem ev_levi (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) (g : Levi k m)
    (f : IndSp e ρ) :
    ev e ρ (parInd e ρ (leviEmb k e g) f) = (deltaHalf k m g : ℂ) • ρ g (ev e ρ f) := by
  have hmem := leviEmb_mem_parab k e g
  have h := f.1.2 ⟨leviEmb k e g, hmem⟩ 1
  rw [mul_one, MonoidHom.comp_apply, leviProj_leviEmb] at h
  show f.1.1 (1 * leviEmb k e g) = (deltaHalf k m g : ℂ) • ρ g (f.1.1 1)
  rw [one_mul]
  exact h

theorem exists_ev_ne (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {f : IndSp e ρ}
    (hf : f ≠ 0) : ∃ g, ev e ρ (parInd e ρ g f) ≠ 0 := by
  by_contra hcon
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext g
  by_contra hg
  exact hcon ⟨g, by
    change f.1.1 (1 * g) ≠ 0
    rw [one_mul]
    exact hg⟩

variable {e : (Σ a, m a) ≃ n} {ρ : Representation ℂ (Levi k m) X}

def lam {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') : IndSp e ρ →ₗ[ℂ] X :=
  ev e ρ ∘ₗ proj h

theorem lam_apply {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (f : IndSp e ρ) :
    lam h f = ev e ρ (proj h f) := rfl

theorem lam_twKer {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    twKer (parInd e ρ) (unipRad k e) 1 ≤ LinearMap.ker (lam h) := by
  unfold GlobalTheory.PRep.twKer
  refine Submodule.span_le.mpr ?_
  rintro w ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul,
    lam_apply, lam_apply, proj_comm, ev_unip e ρ u.2, sub_self]

def frob {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    (jac e (parInd e ρ)).IntertwiningMap ρ where
  toLinearMap := (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
  isIntertwining' g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
        (jac e (parInd e ρ) g (Submodule.Quotient.mk v)) = ρ g (lam h v)
    rw [jac_mk, ← Submodule.Quotient.mk_smul, Submodule.liftQ_apply, map_smul, lam_apply, proj_comm,
      ev_levi, lam_apply, smul_smul]
    simp

theorem frob_mk {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (v : IndSp e ρ) :
    (frob h).toLinearMap (Submodule.Quotient.mk v) = lam h v := rfl

theorem exists_lam_ne {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥) :
    ∃ v ∈ S.toSubmodule, lam h v ≠ 0 := by
  have hS0 : S.toSubmodule ≠ ⊥ := by
    intro h0
    apply hS
    apply Subrepresentation.ext
    rw [h0]
    try rfl
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨g, hg⟩ := exists_ev_ne e ρ hf0
  refine ⟨parInd e ρ g f, S.apply_mem_toSubmodule g hfS, ?_⟩
  rw [lam_apply, proj_left h (S.apply_mem_toSubmodule g hfS)]
  exact hg

theorem not_dichotomy {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥)
    (hS' : S' ≠ ⊥) :
    ¬ (∀ φ ψ : (jac e (parInd e ρ)).IntertwiningMap ρ,
      φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro hd
  obtain ⟨v, hvS, hv⟩ := exists_lam_ne h hS
  obtain ⟨w, hwS', hw⟩ := exists_lam_ne h.symm hS'
  rcases hd (frob h) (frob h.symm) with h0 | ⟨c, hc⟩
  · apply hv
    rw [← frob_mk h v, h0, LinearMap.zero_apply]
  · have e1 : lam h.symm v = c • lam h v := by
      rw [← frob_mk h.symm v, hc, LinearMap.smul_apply, frob_mk]
    rw [lam_apply, proj_right h.symm hvS, map_zero] at e1
    rcases smul_eq_zero.mp e1.symm with hc0 | hc0
    · apply hw
      rw [← frob_mk h.symm w, hc, hc0, zero_smul, LinearMap.zero_apply]
    · exact hv hc0

end Induced

theorem not_dichotomy_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ W W' h hW hW'
  exact not_dichotomy h hW hW'

end GlobalTheory.CompanionTheory.SplitFrob
end
end

section

open ValuativeRel Matrix Topology MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.IwContract

open PositivityTheory.Rg.Tf.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem mem_iwahori_iff {g : GL (Fin n) F} :
    g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ↔ g ∈ GlobalTheory.SmGL.iwahori F (Fin n) := by
  rw [GlobalTheory.SmGL.mem_iwahori]; rfl


end GlobalTheory.CompanionTheory.IwContract
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

theorem _root_.GlobalTheory.T.admissible_of_finite_length_subquotients : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  first | exact @GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | (intros; apply GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finiteDimensional_fixed_tensor : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (K₁ : Subgroup G) (K₂ : Subgroup H), FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K₁) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K₂) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed (GlobalTheory.SmGL.extTensor ρ σ) (K₁.prod K₂)) := by
  first | exact @GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor | exact GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor | (intros; apply GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.filtration_unique_subquotient : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ) (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ t₀ : Fin N, (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) → (∀ t : Fin N, t ≠ t₀ → ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) → ∀ φ ψ : π.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  first | exact @GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | exact GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | (intros; apply GlobalTheory.CompanionTheory.Filtration.intertwining_proportional <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.admissible_unitary_semisimple : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  first | exact @GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | exact GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | (intros; apply GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl <;> assumption)
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.monomial_coefficient_comparison : ∀ {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ) (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ), (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) → ∀ m : Fin n → ℤ, ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | exact GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | (intros; apply GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus <;> assumption)
end
