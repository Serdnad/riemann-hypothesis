module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle446
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle611
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle613
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle614
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmpIsoOfExpansions
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle596
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle615
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory


theorem _root_.GlobalTheory.T.galoisCharacter_eq_one_of_trivial_degreeOne_frobenius : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (φ : G E Ω →* (Qbar l)ˣ), Continuous φ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      ∀ (A : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) σ → φ σ = 1) →
    φ = 1 := by
  first | exact @GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial | exact GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial | (intros; apply GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial <;> assumption)
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundDel

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

lemma actVB_tmul' (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := rfl

lemma actVdR_tmul' (g : G) (v : V) (b : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actdR g b := rfl

lemma φVB_tmul' (v : V) (b : B) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.φ b := rfl

lemma ιV_tmul' (v : V) (b : B) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.ι b := rfl

lemma φVB_actVB' (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', φVB_tmul', φVB_tmul', actVB_tmul', PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma ιV_actVB' (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', ιV_tmul', ιV_tmul', actVdR_tmul', PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b =>
    rw [actVB_tmul', actVB_tmul', actVB_tmul', map_mul, map_mul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma actVdR_mem_FilV' (g : G) (a : ℤ) (y : V ⊗[Qp] BdR)
    (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    actVdR PD ρ g y ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | tmul v b =>
    exact ⟨ρ g v ⊗ₜ[Qp] ⟨PD.actdR g b.1, PD.Fil_G g a _ b.2⟩, rfl⟩
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ hx hy

include PD in
lemma nontrivial_B' : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
lemma tmul_one_injective' {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  haveI := nontrivial_B' PD
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one Qp (one_ne_zero : (1 : B) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V f z)) h
  simpa [hf] using this

lemma sub_fixed_mem (d₁ : V ⊗[Qp] B) (h₁ : d₁ ∈ Dcris PD ρ) (d₂ : V ⊗[Qp] BdR) (h₂ : d₂ ∈ DdR PD ρ)
    (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (hy : y ∈ FilV PD (LL := LL) (V := V) 0)
    (hx : x - φVB PD (LL := LL) (V := V) x = d₁) (hxy : ιV PD (LL := LL) (V := V) x - y = d₂)
    (g : G) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVB PD ρ g x - x ∧
      ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have e₁ : actVB PD ρ g d₁ - d₁ = 0 := (Submodule.mem_iInf _).1 h₁ g
  have e₂ : actVdR PD ρ g d₂ - d₂ = 0 := (Submodule.mem_iInf _).1 h₂ g
  rw [← hx, map_sub] at e₁
  rw [← hxy, map_sub] at e₂
  constructor
  · rw [map_sub, φVB_actVB', ← sub_eq_zero, ← neg_eq_zero, ← e₁]
    abel
  · have : ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVdR PD ρ g y - y := by
      rw [map_sub, ιV_actVB', ← sub_eq_zero, ← e₂]
      abel
    rw [this]
    exact Submodule.sub_mem _ (actVdR_mem_FilV' PD ρ g 0 y hy) hy

lemma cocycle_of_tmul_one (x : V ⊗[Qp] B) (c : G → V)
    (hc : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g h : G) :
    c (g * h) = c g + ρ g (c h) := by
  apply tmul_one_injective' PD
  have e : ρ g (c h) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g (c h ⊗ₜ[Qp] (1 : B)) := by
    rw [actVB_tmul', map_one]
  rw [add_tmul, e, hc, hc, hc, map_sub, actVB_mul']
  abel

end General

theorem connecting_cocycle : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, ∀ d₁ ∈ Dcris (P.PD K) A.ρ, ∀ d₂ ∈ DdR (P.PD K) A.ρ, ∃ (x : A.V ⊗[ℚ_[l]] P.R.B) (y : A.V ⊗[ℚ_[l]] P.R.BdR) (c : ↥(GK K) → A.V), y ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := A.V) x = d₁ ∧ ιV (P.PD K) (LL := LL) (V := A.V) x - y = d₂ ∧ c ∈ finiteCocycles (P.PD K) A.ρ ∧ ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A d₁ h₁ d₂ h₂
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K LL A.V
  obtain ⟨x, y, hy, hx, hxy⟩ := hsurj d₁ d₂
  have key : ∀ g, ∃ v : A.V, actVB (P.PD K) A.ρ g x - x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun g =>
    hker _ (sub_fixed_mem (P.PD K) A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).1
      (sub_fixed_mem (P.PD K) A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).2
  choose c hc using key
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := fun g => (hc g).symm
  have hcont : Continuous c :=
    GlobalTheory.FundCont.contCore_tied l P AI T K LL O hO A 0 Fin.elim0 Fin.elim0 (fun i => i.elim0) x c
      (fun g => by rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]; exact hc' g)
  exact ⟨x, y, c, hy, hx, hxy,
    ⟨⟨hcont, cocycle_of_tmul_one (P.PD K) A.ρ x c hc'⟩, x, hc'⟩, hc'⟩

end GlobalTheory.FundDel
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.JumpsSES

section Trivial

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  induction b, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

theorem one_not_mem_fil_one : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h
  rw [mul_one] at this
  exact PD.not_mem_filtration_two this

theorem ddR_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K BdR).toLinearMap) ∧
    (∀ a ≤ 0, x ∈ FilV PD (LL := LL) (V := V) a) ∧
    (∀ a, 1 ≤ a → x ∈ FilV PD (LL := LL) (V := V) a → x = 0) := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  let e := Module.finBasis Qp V
  let c : Fin (finrank Qp V) → V ⊗[Qp] BdR →ₗ[Qp] BdR := fun i =>
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (LinearMap.rTensor BdR (e.coord i))
  have hsum : ∀ y : V ⊗[Qp] BdR, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c, TensorProduct.smul_tmul]
    | add a b ha hb =>
      simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
  have hc : ∀ i g y, c i (actVdR PD ρ g y) = PD.actdR g (c i y) := by
    intro i g y
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      have := ((PD.actdR g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
      have h2 : PD.actdR g (e.coord i v • b) = e.coord i v • PD.actdR g b := this
      simp only [c, actVdR, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2, hρ]
      simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hk : ∀ i, ∃ k : K, algebraMap K BdR k = c i x := fun i =>
    PD.invdR (c i x) fun g => by rw [← hc, hx]
  refine ⟨?_, fun a ha => ?_, fun a ha hF => ?_⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    have : c i x ∈ PD.Fil a := by
      rw [← hk, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (fil_anti PD ha PD.one_mem)
    exact ⟨e i ⊗ₜ ⟨c i x, this⟩, by simp⟩
  · have hF' : ∀ i, ∀ y ∈ FilV PD (LL := LL) (V := V) a, c i y ∈ PD.Fil a := by
      rintro i _ ⟨y, rfl⟩
      induction y using TensorProduct.inductionOn with
      | tmul v b =>
        have : (e.coord i v) • (b : BdR) ∈ (PD.Fil a).restrictScalars Qp := Submodule.smul_mem _ _ b.2
        simpa [c] using this
      | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz
    rw [hsum x]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    by_cases h0 : k = 0
    · rw [← hk, h0]; simp
    · exfalso
      apply one_not_mem_fil_one PD
      have h1 := Submodule.smul_mem _ k⁻¹ (fil_anti PD ha (hF' i x hF))
      rwa [← hk, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h0, one_smul] at h1

theorem jumps_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ) (ha : IsJumpV PD ρ τ a) : a = 0 := by
  by_contra h0
  apply ha
  ext x
  simp only [FildR, Submodule.mem_inf]
  refine and_congr_right fun hx => ?_
  obtain ⟨-, h1, h2⟩ := ddR_of_trivial PD ρ hρ x hx.1
  rcases lt_or_gt_of_ne h0 with h | h
  · exact ⟨fun _ => h1 a (by omega), fun _ => h1 (a + 1) (by omega)⟩
  · constructor
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _

end Trivial

theorem jumps_ses_and_one : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsSESLat (Qp := ℚ_[l]) ι π → (∀ τ a, IsJumpV ((D.loc l).PD K) T₁.ρ τ a ↔ IsJumpV ((D.loc l).PD K) T₀.ρ τ a ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) ∧ ∀ τ a, IsJumpV ((D.loc l).PD K) W.one.ρ τ a → a = 0 := by
  intro D HW l _ K s LL h W T₀ T₁ T₂ ι π hc hS
  refine ⟨fun τ a => ?_, fun τ a ha => ?_⟩
  · have h0 : IsCrys ((D.loc l).PD K) T₀.ρ :=
      (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hS.1 hc
    have h2 : IsCrys ((D.loc l).PD K) T₂.ρ :=
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2
        hS.2.1 hc).1
    exact GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l _ _ (D.locT l) K LL T₀ T₁ T₂ ι π hS h0 hc h2 τ a
  · haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] W.one.V := Module.Finite.trans ↥LL.1 W.one.V
    exact jumps_of_trivial _ W.one.ρ W.one_triv τ a ha

end GlobalTheory.NL.JumpsSES
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjHalfDual

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

variable {D : D7}

theorem cA_cA_self (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig x) = a ⊗ₜ[D.host.F] x
    congr 1
    exact star_star x
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infPart_cA_of_zero {z : AE D} (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  have key : ∀ w : AE D, infPart D (cA D w) =
      Algebra.TensorProduct.map (AlgHom.id D.host.F (Ainf D.host.F)) D.sp.cm.sig (infPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  rw [key, h, map_zero]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO; rw [hO_add_right, mul_add, map_add (f := _)]

theorem hO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    hO S T x (g • y') = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, ← hx d a, map_mul]
  calc incA D (S.gram⁻¹ a b) * (cA D g * cA D (y' c b)) * incA D (T.gram c d) * (f * x d a)
      = (cA D g * f) * (incA D (S.gram⁻¹ a b) * cA D (y' c b) * incA D (T.gram c d) * x d a) := by ring
    _ = 0 := by rw [hfg, zero_mul]

theorem symplO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    symplO S T x (g • y') = 0 := by
  unfold symplO; rw [hO_eq_zero_of hfg hx, mul_zero, map_zero]

theorem mem_latO_iff_of_conjHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  intro D ψ S T ΛS ΛT hψ hS hT e he hec hinf hfin u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hcc : cA D (cA D e) = e := cA_cA_self e
  have hcidem : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hcinf : infPart D (cA D e) = 0 := infPart_cA_of_zero hinf
  constructor
  · intro hmem l hl _
    have hl0 : l.map (infPart D) = 0 := by
      ext i j; exact latAll_infPart hl i j
    exact (key l hl0).1 hl u hmem
  · intro h
    have hu0 : u.map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, hcinf, zero_mul]
    refine (key u hu0).2 fun u' hu' => ?_
    have hdec : u' = e • u' + (cA D e • u' + (1 - e - cA D e) • u') := by
      ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    have m1 : e • u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
      smul_mem_latAll hfin hu'
    have hh1 : IsHalf e (e • u') := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
    have t1 : ψ (symplO S T u (e • u')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew, AddChar.map_neg_eq_inv, h _ m1 hh1, inv_one]
    have t2 : symplO S T u (cA D e • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by rw [hcc]; exact hec) hu
    have t3 : symplO S T u ((1 - e - cA D e) • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by
        rw [map_sub, map_sub, map_one, hcc]
        linear_combination (-1 : AE D) * hcidem - hec) hu
    rw [hdec, symplO_add_right', symplO_add_right', t2, t3, add_zero, add_zero, t1]

end GlobalTheory.ConjHalfDual

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory


theorem _root_.GlobalTheory.T.degreeOne_prime_CMField_over_split_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) ∧
    (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))).card = 2 ∧
    ∀ w' ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E))),
      Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal ∧ w'.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
  first | exact @GlobalTheory.SplitDegOne.main | exact GlobalTheory.SplitDegOne.main | (intros; apply GlobalTheory.SplitDegOne.main <;> assumption)
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.CmpCris

theorem wachLattice_comparison_dcris (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : P3 D HW F Cm := by
  intro l _ K s LL h T hT
  obtain ⟨h1, h2, -, h4⟩ := cmp_iso D HW F Cm l K s LL h T hT
  refine ⟨fun x hx => ?_, h2, fun x k hk => h4 x k hk⟩
  obtain ⟨y, rfl⟩ := (h1 x).1 hx
  exact ⟨y, y.2, rfl⟩

end GlobalTheory.NL.CmpCris
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmHerrLocal

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F :=
  fun D HW F => Formalism.MainNotions.HerrComplexNaturality.herr_class_maps_of_naturality D HW F
    (Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_a_and_natural D HW F))
    (GlobalTheory.HerrExtUnit.main D HW F)

end GlobalTheory.AdmHerrLocal
end
