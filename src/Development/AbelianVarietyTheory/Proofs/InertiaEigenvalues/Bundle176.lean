module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle008
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle007
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle114
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChange
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle157
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
public import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem finrank_le_of_span_subspace {K F M : Type} [Field K] [CommRing F] [Nontrivial F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M] (D : Submodule K M)
    [FiniteDimensional K D] (h : Submodule.span F (D : Set M) = ⊤) :
    finrank F M ≤ finrank K D := by
  classical
  let bD := Module.finBasis K D
  let s : Finset M := Finset.univ.image fun i => ((bD i : D) : M)
  have hs : Submodule.span F (s : Set M) = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    intro x hx
    have hx' := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    rw [← hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul F]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))
  calc finrank F M = finrank F (⊤ : Submodule F M) := (finrank_top F M).symm
    _ = finrank F (Submodule.span F (s : Set M)) := by rw [hs]
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ (Finset.univ : Finset (Fin (finrank K D))).card := Finset.card_image_le
    _ = finrank K D := by simp

theorem finrank_mul_le_finrank_DdR_of_spans {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F]
    [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (hs : Spans PD ρ) :
    Module.finrank Qp K * Module.finrank LL V ≤ Module.finrank LL ↥(DdR PD ρ) := by
  classical
  haveI : Nontrivial F := by
    refine nontrivial_of_ne (PD.ι PD.t) 0 fun h0 => PD.not_mem_filtration_two ?_
    rw [h0]
    exact (PD.Fil 2).zero_mem
  unfold Spans mulR at hs
  set W := DdR PD ρ with hW
  let e : V ⊗[Qp] F ≃ₗ[Qp] F ⊗[Qp] V := TensorProduct.comm Qp V F

  have he : ∀ (b : F) (x : V ⊗[Qp] F),
      e (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) x) = b • e x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

  have hK : ∀ (c : K) (x : V ⊗[Qp] F), x ∈ W →
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) x ∈ W := by
    intro c x hx
    simp only [hW, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    have hcomm : ∀ y : V ⊗[Qp] F, actVdR PD ρ g
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) y) =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c))
          (actVdR PD ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v z => simp [actVdR]
      | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    rw [hcomm, hx g]

  let D' : Submodule K (F ⊗[Qp] V) :=
    { carrier := e '' (W : Set (V ⊗[Qp] F))
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, W.add_mem hx hy, map_add e x y⟩
      zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨_, hK c x hx, ?_⟩
        rw [he, algebraMap_smul] }
  have hspan : Submodule.span F (D' : Set (F ⊗[Qp] V)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, b, d, hd, hy⟩ := hs (e.symm y)
    have hy' : y = ∑ i, b i • e (d i) := by

      rw [← e.apply_symm_apply y, hy, map_sum]
      simp only [he]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (show e (d i) ∈ (D' : Set (F ⊗[Qp] V)) from ⟨d i, hd i, rfl⟩))
  haveI : FiniteDimensional LL W := hfin
  haveI : FiniteDimensional Qp W := Module.Finite.trans LL W
  let φ : W ≃ₗ[Qp] D' :=
    LinearEquiv.ofBijective
      ({ toFun := fun w => ⟨e (w : V ⊗[Qp] F), (w : V ⊗[Qp] F), w.2, rfl⟩
         map_add' := fun x y => Subtype.ext (map_add e (x : V ⊗[Qp] F) y)
         map_smul' := fun a x => Subtype.ext (map_smul e a (x : V ⊗[Qp] F)) } : W →ₗ[Qp] D')
      ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)),
        by rintro ⟨_, w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩⟩
  haveI : FiniteDimensional Qp D' := Module.Finite.equiv φ
  haveI : FiniteDimensional K D' := Module.Finite.of_restrictScalars_finite Qp K D'
  have h1 := finrank_le_of_span_subspace D' hspan
  rw [Module.finrank_baseChange] at h1
  have h2 : finrank Qp K * finrank K D' = finrank Qp LL * finrank LL W := by
    rw [Module.finrank_mul_finrank, ← φ.finrank_eq, Module.finrank_mul_finrank]
  have h3 : finrank Qp LL * finrank LL V = finrank Qp V := Module.finrank_mul_finrank _ _ _
  have hpos : 0 < finrank Qp LL := Module.finrank_pos
  have key : finrank Qp LL * (finrank Qp K * finrank LL V) ≤ finrank Qp LL * finrank LL W :=
    calc finrank Qp LL * (finrank Qp K * finrank LL V)
        = finrank Qp K * finrank Qp V := by rw [← h3]; ring
      _ ≤ finrank Qp K * finrank K D' := Nat.mul_le_mul_left _ h1
      _ = finrank Qp LL * finrank LL W := h2
  exact Nat.le_of_mul_le_mul_left key hpos

end GlobalTheory.DRFil
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.DZero

theorem exists_irrRep_quotient_of_finite_gen : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), GlobalTheory.PRep.IsSmooth π → Nontrivial V → ∀ s : Finset V, Submodule.span ℂ (Set.range fun p : G × s => π p.1 (p.2 : V)) = ⊤ → ∃ (σ : IrrRep G) (p : V →ₗ[ℂ] σ.V), Function.Surjective p ∧ ∀ g v, p (π g v) = σ.ρ g (p v) := by
  intro G V _ _ _ _ _ π hπ hV s hs
  classical

  have htop : ∀ N : Submodule ℂ V, (∀ (g : G), ∀ v ∈ N, π g v ∈ N) →
      Submodule.span ℂ ((s : Set V)) ≤ N → N = ⊤ := by
    intro N hN hsN
    rw [eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact hN g _ (hsN (Submodule.subset_span v.2))
  let S : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, π g v ∈ N) ∧ N ≠ ⊤}
  have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], bot_ne_top⟩
  have hcomp := Submodule.finset_span_isCompactElement (R := ℂ) s
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun htop' => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
      exact le_sSup hM ((hcS hM).1 g v hvM)
    · obtain ⟨M, hM, hsM⟩ := (isCompactElement_iff_le_of_directed_sSup_le _).1 hcomp c hne hd
        (by rw [htop']; exact le_top)
      exact (hcS hM).2 (htop M (hcS hM).1 hsM)) ⊥ hbot
  obtain ⟨hNst, hNtop⟩ := hmax.prop
  let T : Subrepresentation π := ⟨N, fun g v hv => hNst g v hv⟩
  have hT : IsCoatom T := by
    refine ⟨fun h => hNtop (congrArg Subrepresentation.toSubmodule h), fun T' hT' => ?_⟩
    by_contra hne
    have hmem : T'.toSubmodule ∈ S := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv,
      fun h => hne (Subrepresentation.toSubmodule_injective h)⟩
    have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hT'.le) hT'.le
    exact hT'.ne (Subrepresentation.toSubmodule_injective heq.symm)
  have hi := isIrreducible_subQuot hT.covBy_top
  let q : (⊤ : Subrepresentation π).toRepresentation.IntertwiningMap (subQuot ⊤ T) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsm : IsSmooth (subQuot ⊤ T) :=
    IsSubquotient.isSmooth ⟨⊤, q, Submodule.Quotient.mk_surjective _⟩ hπ
  let σ : IrrRep G := ⟨_, subQuot ⊤ T, hsm, hi⟩
  let p : V →ₗ[ℂ] σ.V := (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
    LinearMap.id (fun _ => trivial)
  refine ⟨σ, p, fun w => ?_, fun g v => rfl⟩
  obtain ⟨⟨v, -⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨v, rfl⟩

end GlobalTheory.DZero
end

section

open Formalism.IrreducibleCountingLemmas.TYPES (zIdem)
open Formalism.L2.NT
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

theorem zIdem_eq_charIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

theorem zIdem_centralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ →
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  intro Γ _ _ τ hτ
  have h := orthogonalCentral Γ τ τ hτ hτ
  rw [zIdem_eq_charIdem]
  exact ⟨h.2.2.1, h.2.2.2.1⟩

end GlobalTheory.SerOSys
end

section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem nontrivial_of_simpleRep {Γ : Type} [Group Γ] [Fintype Γ] (V : FDRep ℂ Γ) (h : Simple V) :
    Nontrivial V := by
  rw [FDRep.simple_iff_char_is_norm_one] at h
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h0 : ∀ g, V.character g = 0 := fun g => by
    rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
  simp only [h0, mul_zero, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card Γ : ℂ) ≠ 0) h.symm

theorem invariant_eq_bot_or_top_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ)
    [Simple τ] (U : Submodule ℂ τ) (hU : ∀ g, ∀ x ∈ U, τ.ρ g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let A : Subrepresentation τ.ρ := ⟨U, fun g v hv => hU g v hv⟩
  let X : FDRep ℂ Γ := FDRep.of A.toRepresentation
  let i : X ⟶ τ := ⟨InducedCategory.homMk (ModuleCat.ofHom U.subtype), fun g => by
    ext1; ext x; rfl⟩
  have hinj : Function.Injective ⇑(ConcreteCategory.hom i) := by
    intro x y h; exact Subtype.ext h
  have : Mono i := ConcreteCategory.mono_of_injective i hinj
  by_cases h0 : i = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := congrArg (fun f : X ⟶ τ => ConcreteCategory.hom f ⟨x, hx⟩) h0
    have h1 : ConcreteCategory.hom i ⟨x, hx⟩ = x := rfl
    have h2 : ConcreteCategory.hom (0 : X ⟶ τ) ⟨x, hx⟩ = 0 := rfl
    simp only [h1, h2] at this
    exact this
  · right
    have : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 h0
    apply Submodule.eq_top_of_finrank_eq
    exact (FDRep.isoToLinearEquiv (asIso i)).finrank_eq

theorem zIdem_eq_of_linearEquiv {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) : zIdem τ = zIdem τ' := by
  apply MonoidAlgebra.ext
  ext γ
  rw [zIdem_coeff, zIdem_coeff, φ.finrank_eq]
  have h : τ'.ρ γ⁻¹ = φ.conj (τ.ρ γ⁻¹) := by
    ext x
    rw [LinearEquiv.conj_apply]
    simp [hφ]
  rw [h, LinearMap.trace_conj']

theorem zIdem_eq_centralIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ),
    Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  intro Γ _ _ τ τ' hτ hτ' hne
  haveI := nontrivial_of_simpleRep τ hτ
  haveI := nontrivial_of_simpleRep τ' hτ'
  rw [zIdem_eq_centralIdem, zIdem_eq_centralIdem]
  exact Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_orthogonal Γ τ τ' τ.ρ τ'.ρ
    (invariant_eq_bot_or_top_of_simple τ) (invariant_eq_bot_or_top_of_simple τ')
    (by rintro ⟨φ, hφ⟩; exact hne (zIdem_eq_of_linearEquiv τ τ' φ hφ))

end GlobalTheory.SerOSys
end
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LatticeQuotBound

theorem exists_pow_smul_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (v : V) : ∃ m : ℕ, ϖ ^ m • v ∈ T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem ..)

theorem pow_smul_eq_zero_of_compact : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  intro O _ _ _ V _ _ _ _ _ _ X _ _ T hT hTo ϖ hϖ c hc
  have hopen : ∀ m : ℕ, IsOpen {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro m
    have h : IsOpen ((Submodule.Quotient.mk : V → V ⧸ T) ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
      rw [isOpen_iff_forall_mem_open]
      intro v hv
      refine ⟨(fun t => v + t) '' (T : Set V), ?_, isOpenMap_add_left v _ hTo,
        ⟨0, T.zero_mem, add_zero v⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
      rw [Submodule.Quotient.mk_add, smul_add, hv, zero_add,
        (Submodule.Quotient.mk_eq_zero T).2 ht, smul_zero]
    exact isOpen_coinduced.mpr h
  have hcover : ∀ x, ∃ m : ℕ, x ∈ c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro x
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective T (c x)
    obtain ⟨m, hm⟩ := exists_pow_smul_mem T hT ϖ hϖ v
    refine ⟨m, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hv, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero T).2 hm]
  have hmono : Monotone (fun m : ℕ => c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
    intro a b hab x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    rw [← Nat.add_sub_cancel' hab, pow_add, mul_comm, mul_smul, hx, smul_zero]
  obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover _ (fun m => (hopen m).preimage hc)
    (fun x _ => Set.mem_iUnion.2 (hcover x)) hmono.directed_le
  exact ⟨m, fun x => hm (Set.mem_univ x)⟩

end GlobalTheory.LatticeQuotBound
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LatTorsFinite

theorem finite_quot_of_isOpen {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (hI : IsOpen (I : Set O)) : Finite (O ⧸ I) := by
  have hU : ∀ x : O, IsOpen ((fun y => y - x) ⁻¹' (I : Set O)) := fun x =>
    hI.preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : O => (fun y => y - x) ⁻¹' (I : Set O))
    hU (fun y _ => Set.mem_iUnion.2 ⟨y, by simp [I.zero_mem]⟩)
  refine Finite.of_surjective (fun x : t => Ideal.Quotient.mk I (x : O)) ?_
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (Ideal.Quotient.eq.2 hyx).symm

theorem finite_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (hO : IsTopologicalRing O) (hc : CompactSpace O)
    (hA : IsAdic (IsLocalRing.maximalIdeal O)) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hopen : IsOpen (((IsLocalRing.maximalIdeal O) ^ n : Ideal O) : Set O) :=
    (isAdic_iff.1 hA).1 n
  rw [hm, Ideal.span_singleton_pow] at hopen
  exact finite_quot_of_isOpen _ hopen

theorem finite_ker_pow_smul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hO : IsTopologicalRing O)
    (hc : CompactSpace O) (hA : IsAdic (IsLocalRing.maximalIdeal O)) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  haveI := finite_quot_pow hO hc hA hϖ n
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
      (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})

  let rep : V ⧸ T → V := fun q => Classical.choose (Submodule.Quotient.mk_surjective T q)
  have hrep : ∀ q, Submodule.Quotient.mk (p := T) (rep q) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective T q)
  have hmem : ∀ x : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)),
      ϖ ^ n • rep (x : V ⧸ T) ∈ T := by
    intro x
    have hx : (ϖ ^ n) • (x : V ⧸ T) = 0 := x.2
    rw [← hrep (x : V ⧸ T), ← Submodule.Quotient.mk_smul] at hx
    exact (Submodule.Quotient.mk_eq_zero T).1 hx

  have hinj : ∀ v w : V, ϖ ^ n • v = ϖ ^ n • w → v = w := by
    intro v w h
    have h0 : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) v,
      ← algebraMap_smul (FractionRing O) (ϖ ^ n) w] at h
    exact smul_right_injective V h0 h
  let f : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)) →
      T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T) :=
    fun x => Submodule.Quotient.mk ⟨ϖ ^ n • rep (x : V ⧸ T), hmem x⟩
  refine Finite.of_injective f ?_
  intro x y hxy
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hxy
  obtain ⟨t, -, ht⟩ := hxy
  have ht' : ϖ ^ n • (t : V) = ϖ ^ n • (rep (x : V ⧸ T) - rep (y : V ⧸ T)) := by
    rw [smul_sub]
    exact congrArg Subtype.val ht
  have hd := hinj _ _ ht'
  apply Subtype.ext
  rw [← hrep (x : V ⧸ T), ← hrep (y : V ⧸ T), Submodule.Quotient.eq, ← hd]
  exact t.2

end GlobalTheory.LatTorsFinite
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_periodFunctor_coeff_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  first | exact @GlobalTheory.CoeffBC.finrank_baseChange | exact GlobalTheory.CoeffBC.finrank_baseChange | (intros; apply GlobalTheory.CoeffBC.finrank_baseChange <;> assumption)
end

section

open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.hasSum_inner_eulerProduct_quotient_injective : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) [DecidableEq ι] (c : ι → Γ →* Γ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (s : ι → ℝ) (e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}), (∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) → (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ g, a g = ∏ᶠ v, a (c v g)) → (∀ g, ‖B g‖ ≤ 1) → B 1 = 1 → (∀ g k, k ∈ K → B (g * k) = B g) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset Γ), (∀ g ∈ C, c v g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ s v) → (∀ v γ, HasSum (fun x : Γ ⧸ K.comap (c v) => a (c v (Quotient.out x)) • B (γ * c v (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap (c v), a (c v (Quotient.out x)) • B (c v (Quotient.out x)))) → ∃ W : H →L[ℂ] H, Function.Injective W ∧ ∀ x y, HasSum (fun q : Γ ⧸ K => a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ) ⟪x, W y⟫_ℂ := by
  first | exact @GlobalTheory.hasSum_inner_quotient_eulerProduct_injective | exact GlobalTheory.hasSum_inner_quotient_eulerProduct_injective | (intros; apply GlobalTheory.hasSum_inner_quotient_eulerProduct_injective <;> assumption)
end
