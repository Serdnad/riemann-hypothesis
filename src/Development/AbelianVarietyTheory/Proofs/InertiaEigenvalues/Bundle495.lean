module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle356
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle493
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle388
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle486
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrthV

theorem exists_unitLattice {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
      L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  apply GlobalTheory.CycIntegral.cyc_lattice <;> assumption

theorem cocycle_mem_coboundaries_of_tate_orthogonal' : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL (P.PD K) (cupL A'.ρ m a b)) → b ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm b hb horth
  obtain ⟨⟨hDom, hDVR, hFrac⟩, hfd, hmt, htr, hopen⟩ := id hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := htr
  haveI : IsTopologicalAddGroup A'.V := IsModuleTopology.topologicalAddGroup LL A'.V
  obtain ⟨L1, hL1⟩ := exists_unitLattice P K LL O hO
  obtain ⟨LA, LA', hLL', -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hT'open : IsOpen (LA'.T : Set A'.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA'.T LA'.fg LA'.span
  have hL1open : IsOpen (L1.T : Set LL) := by
    rw [hL1]
    have e : ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) =
        Set.range (algebraMap O LL) := by
      ext y; simp [Algebra.linearMap_apply]
    rw [e]; exact hopen
  have hp : ((l : ℕ) : LL) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

  have hcobZ : ∀ x : A'.V, (fun g => A'.ρ g x - x) ∈ continuousCocycles A'.ρ := by
    intro x
    refine ⟨(A'.cont x).sub continuous_const, fun g h => ?_⟩
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel

  have key : ∀ n : ℕ, ∃ β ∈ latticeCocycles LA', b - ((l : LL) ^ n) • β ∈ B1 A'.ρ := by
    intro n
    set s : LL := (((l : ℕ) : LL) ^ n)⁻¹ with hs
    let c : ↥(GK K) → A'.V ⧸ LA'.T := fun g => Submodule.Quotient.mk (s • b g)
    have hcZ : c ∈ divisibleCocycles LA' := by
      refine ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA'.T hT'open _ (hb.1.const_smul s), fun g h => ?_⟩
      show Submodule.Quotient.mk (s • b (g * h)) = Submodule.Quotient.mk (s • b g) +
        actD LA' g (Submodule.Quotient.mk (s • b h))
      rw [hb.2 g h, smul_add, Submodule.Quotient.mk_add]
      congr 1
      show _ = Submodule.Quotient.mk (A'.ρ g (s • b h))
      rw [map_smul]
    have hcorth : ∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c) := by
      intro d hd
      obtain ⟨f, hfc, hf⟩ := horth d hd.1
      refine ⟨fun g => (Submodule.Quotient.mk (s • f g) : LL ⧸ L1.T),
        ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hL1open _ (hfc.const_smul s), fun _ => Submodule.mem_top⟩, ?_⟩
      funext x
      obtain ⟨g, h⟩ := x
      have hf' : ((cycLL (P.PD K) LL g : LLˣ) : LL) • f h - f (g * h) + f g =
          m (d g) (A'.ρ g (b h)) := congrFun hf (g, h)
      have hlift : liftD LA' (c h) - s • b h ∈ LA'.T :=
        (Submodule.Quotient.eq _).1 (Submodule.Quotient.mk_surjective LA'.T (c h)).choose_spec
      obtain ⟨e, he⟩ := (hLL'.2 _).1 (LA'.stable g _ hlift) (d g) (hd.2 g (Set.mem_univ g))
      show (Submodule.Quotient.mk (((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h)) : LL ⧸ L1.T) -
          Submodule.Quotient.mk (s • f (g * h)) + Submodule.Quotient.mk (s • f g) =
          Submodule.Quotient.mk (m (d g) (A'.ρ g (liftD LA' (c h))))
      rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, hL1]
      have e1 : ((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h) - s • f (g * h) + s • f g =
          s • m (d g) (A'.ρ g (b h)) := by
        rw [← hf']; simp only [smul_eq_mul]; ring
      have e2 : m (d g) (A'.ρ g (liftD LA' (c h))) =
          s • m (d g) (A'.ρ g (b h)) + m (d g) (A'.ρ g (liftD LA' (c h) - s • b h)) := by
        simp only [map_sub, map_smul, add_sub_cancel]
      rw [e1, e2]
      refine ⟨-e, ?_⟩
      show algebraMap O LL (-e) = _
      rw [map_neg, ← he]
      abel
    obtain ⟨xbar, hx⟩ := GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m
      hLL' c hcZ hcorth
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective LA'.T xbar
    refine ⟨fun g => s • b g - (A'.ρ g x - x), ⟨(continuousCocycles A'.ρ).sub_mem ((continuousCocycles A'.ρ).smul_mem s hb) (hcobZ x),
      fun g _ => ?_⟩, ?_⟩
    · have hg : Submodule.Quotient.mk (A'.ρ g x) - Submodule.Quotient.mk x =
          (Submodule.Quotient.mk (s • b g) : A'.V ⧸ LA'.T) := congrFun hx g
      rw [← Submodule.Quotient.mk_sub] at hg
      exact (Submodule.Quotient.eq _).1 hg.symm
    · refine ⟨(((l : ℕ) : LL) ^ n) • x, ?_⟩
      funext g
      have hps : (((l : ℕ) : LL) ^ n) * s = 1 := mul_inv_cancel₀ (pow_ne_zero n hp)
      simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul,
        Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul, hps, one_smul]
      abel

  have hl : ((l : ℕ) : O) ∉ nonunits O → False := by
    intro hu
    have hu' : IsUnit ((l : ℕ) : O) := by simpa [mem_nonunits_iff] using hu
    have hc := (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO).2.2.2
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu'
    have h10 : (1 : O) = 0 := by
      apply hc.toIsHausdorff.haus 1
      intro n
      rw [htop, Ideal.top_pow, Submodule.top_smul]
      exact SModEq.top
    exact one_ne_zero h10
  have hne : Ideal.span {((l : ℕ) : O)} ≠ ⊤ := by
    intro htop
    apply hl
    intro hmem
    exact hmem (Ideal.span_singleton_eq_top.1 htop)
  haveI hfinH : Module.Finite O (LatticeCohomology LA') :=
    GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  let S : Submodule O ↥(latticeCocycles LA') := ((B1 A'.ρ).restrictScalars O).comap (latticeCocycles LA').subtype
  have hBS : (latticeCoboundaries LA').comap (latticeCocycles LA').subtype ≤ S := by
    rintro z ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  haveI : Module.Finite O (↥(latticeCocycles LA') ⧸ S) := by
    refine Module.Finite.of_surjective (Submodule.factor hBS) ?_
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥(latticeCocycles LA') ⧸ S) _ hne
  obtain ⟨β0, hβ0, hbβ0⟩ := key 0
  rw [pow_zero, one_smul] at hbβ0
  have hq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) = 0 := by
    rw [← Submodule.mem_bot O, ← hK, Submodule.mem_iInf]
    intro i
    obtain ⟨β, hβ, hbβ⟩ := key i
    have heq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) =
        (((l : ℕ) : O) ^ i) • Submodule.Quotient.mk ⟨β, hβ⟩ := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show β0 - (((l : ℕ) : O) ^ i) • β ∈ B1 A'.ρ
      have h1 : β0 - (((l : ℕ) : O) ^ i) • β = (b - ((l : LL) ^ i) • β) - (b - β0) := by
        rw [← algebraMap_smul LL (((l : ℕ) : O) ^ i) β, map_pow, map_natCast]
        abel
      rw [h1]
      exact (B1 A'.ρ).sub_mem hbβ hbβ0
    rw [heq, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hβ0B : β0 ∈ B1 A'.ρ := (Submodule.Quotient.mk_eq_zero S).1 hq
  have : b = (b - β0) + β0 := by abel
  rw [this]
  exact (B1 A'.ρ).add_mem hbβ0 hβ0B

end GlobalTheory.TateOrthV
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

open scoped TensorProduct

namespace GlobalTheory.StabFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem norm_entry_le_one {g : GL (Fin n) L} (hg : g ∈ GQ0 L n) (φ : L →+* ℂ) (i j : Fin n) :
    ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ≤ 1 := by
  apply GlobalTheory.InvFormBdd.norm_emb_le_one <;> assumption

theorem exists_common_denom {ι : Type} [Fintype ι] (x : ι → AL L) :
    ∃ D : ℕ, 0 < D ∧ ∀ a, (D : AL L) * x a ∈ ALint L := by
  classical
  choose d hd0 hd using fun a => Formalism.IndefR.principalLevelFrame.cong_nat_denom (x a)
  refine ⟨∏ a, d a, Finset.prod_pos fun a _ => hd0 a, fun a => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Nat.cast_mul, mul_comm ((d a : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (hd a)

theorem exists_rat (γ : GQ L n) : ∃ g : GL (Fin n) L, g ∈ GQ0 L n ∧
    ∀ i j, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      ((g : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) := by
  have h : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.1 h
  refine ⟨g, hg, fun i j => ?_⟩
  rw [← he]
  rfl

theorem isIntegral_of_mem (z : L) (hz : z ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) ∈ ALint L) :
    IsIntegral ℤ z := by
  have hle : ALint L ≤ Formalism.MainNotions.S.IntAf (NumberField.maximalRealSubfield L) L := by
    rw [ReciprocityTheory.Aut.ALint, Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact Formalism.UG.P.csGlob_int (F := NumberField.maximalRealSubfield L) z (hle hz)

end GlobalTheory.StabFin

open scoped TensorProduct

namespace GlobalTheory.StabFin

theorem finite_conj_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  intro L _ _ _ n J hJ t
  classical
  obtain ⟨F, hF⟩ := hJ
  let M : GAf L n → Matrix (Fin n) (Fin n) (AL L) := fun a => ((a : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  obtain ⟨D, hD0, hD⟩ := exists_common_denom (L := L) (ι := (F × Fin n × Fin n) ⊕ (Fin n × Fin n))
    (fun a => match a with
      | .inl ⟨f, i, k⟩ => M (t * f) i k
      | .inr ⟨l, j⟩ => M t⁻¹ l j)
  have key : ∀ γ : GQ L n, t⁻¹ * (γ : GAf L n) * t ∈ J → ∀ i j, ((D : AL L) * D) * M γ i j ∈ ALint L := by
    intro γ hγ i j
    obtain ⟨f, hf, hu⟩ := hF _ hγ
    have hu' : ∀ a b, M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) a b ∈ ALint L := hu
    have e : (γ : GAf L n) = (t * f) * (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * t⁻¹ := by group
    have eM : M γ = M (t * f) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * M t⁻¹ := by
      conv_lhs => rw [e]
      simp only [M, Subgroup.coe_mul, Units.val_mul]
    rw [eM, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have e2 : ((D : AL L) * D) * (M (t * f) i k * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * M t⁻¹ l j) =
        ((D : AL L) * M (t * f) i k) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * ((D : AL L) * M t⁻¹ l j) := by ring
    rw [e2]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hD (.inl ⟨⟨f, hf⟩, i, k⟩)) (hu' k l)) (hD (.inr ⟨l, j⟩))
  set T : Set L := {z : L | IsIntegral ℤ z ∧ ∀ φ : L →+* ℂ, ‖φ z‖ ≤ ((D * D : ℕ) : ℝ)} with hT
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le L ℂ _
  have : Finite T := hTfin.to_subtype
  choose gs hgs0 hgs using exists_rat (L := L) (n := n)
  have hmem : ∀ x : {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J}, ∀ i j,
      ((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j ∈ T := by
    intro x i j
    refine ⟨isIntegral_of_mem _ ?_, fun φ => ?_⟩
    · have e : (((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) =
          ((D : AL L) * D) * M x.1 i j := by
        simp only [M]
        rw [hgs, ← Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.includeLeftRingHom_apply,
          map_mul, map_natCast]
        push_cast; ring
      rw [e]
      exact key x.1 x.2 i j
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (norm_entry_le_one (hgs0 x.1) φ i j)
  refine Finite.of_injective (fun x => fun i j => (⟨_, hmem x i j⟩ : T)) ?_
  intro x y hxy
  have hD' : ((D * D : ℕ) : L) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD0 hD0).ne'
  have hg : ∀ i j, (gs x.1 : Matrix (Fin n) (Fin n) L) i j = (gs y.1 : Matrix (Fin n) (Fin n) L) i j := by
    intro i j
    have := congrArg Subtype.val (congrFun (congrFun hxy i) j)
    exact mul_left_cancel₀ hD' this
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [hgs x.1 i j, hgs y.1 i j, hg i j]

end GlobalTheory.StabFin
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitCount in

theorem _root_.GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  let C := columns (N := D.nd) D.nbr i s
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun _ ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  rw [Nat.mul_add] at h
  change locDeg D.host.E w * C.ncard = D.R.f
  omega
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep

namespace GlobalTheory.CellDec

variable (E : Type) [Field E] [NumberField E] (n : ℕ)

abbrev NA : Subgroup (GA E n) := GlobalTheory.SmGL.unipB (Ad E) (Fin n)

def NE : Subgroup (GA E n) := (GlobalTheory.SmGL.unipB E (Fin n)).map (ratGL E n)

def compV (v : HeightOneSpectrum (𝓞 E)) : GA E n →* GL (Fin n) (v.adicCompletion E) :=
  GeneralLinearGroup.map ((pLoc E v).comp (pFin E))

def US (S : Finset (HeightOneSpectrum (𝓞 E))) : Subgroup (GA E n) :=
  ⨅ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), (GlobalTheory.LFun.KGL v (n := n)).comap (compV E n v)

def C0 (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (GA E n) :=
  {g | ∃ u ∈ NA E n, ∃ k ∈ US E n S, g = u * k}

abbrev abelian₂ (S : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  {l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0}

variable {E}

def adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ) : (Af E)ˣ where
  val := ⟨fun v => ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
    filter_upwards [m.support.finite_toSet.compl_mem_cofinite] with v hv
    have hv : m v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hv, zpow_zero, Units.val_one]
    exact one_mem _⟩
  inv := ⟨fun v => ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
    filter_upwards [m.support.finite_toSet.compl_mem_cofinite] with v hv
    have hv : m v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hv, neg_zero, zpow_zero, Units.val_one]
    exact one_mem _⟩
  val_inv := FiniteAdeleRing.ext E fun v => by
    change ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : _) = 1
    rw [← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  inv_val := FiniteAdeleRing.ext E fun v => by
    change ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : _) = 1
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]

def tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : GA E n :=
  finGL E n (GlobalTheory.SmGL.diagT (Af E) (Fin n) fun i => adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))

def wtS (a : Fin n → ℤ) : ℤ := ∑ i : Fin n, ∑ j : Fin n, if i < j then a i - a j else 0

def dinv (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : ℝ :=
  ∏ v ∈ l.support, (qV E v : ℝ) ^ wtS n (l v)

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem diagT_conj_mem {R : Type} [CommRing R] (w : Fin n → Rˣ) {u : GL (Fin n) R}
    (hu : u ∈ GlobalTheory.SmGL.unipB R (Fin n)) :
    GlobalTheory.SmGL.diagT R (Fin n) w * u * (GlobalTheory.SmGL.diagT R (Fin n) w)⁻¹ ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
  rw [← map_inv]
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
  refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, Matrix.mul_diagonal, h1 i j hij]
    simp
  · simp only [Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, Matrix.mul_diagonal, h2 i]
    simp

theorem countable_places (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have : Countable (Ideal (𝓞 F)) := by
    have hs : Function.Surjective (fun t : Finset (𝓞 F) => Ideal.span (t : Set (𝓞 F))) := fun I => by
      obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
      exact ⟨t, ht⟩
    exact hs.countable
  have hi : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) := fun v w h => HeightOneSpectrum.ext h
  exact hi.countable

instance countable_Lam (S : Finset (HeightOneSpectrum (𝓞 E))) : Countable (abelian₂ E n S) := by
  have := countable_places E
  exact Subtype.countable

theorem tl_eq_diagT (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    tl n ϖ l = GlobalTheory.SmGL.diagT (Ad E) (Fin n) fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) := by
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h; simp [finId, GlobalTheory.CuspRep.corner]
  · simp [h]

theorem tl_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    {u : GA E n} (hu : u ∈ NA E n) : tl n ϖ l * u * (tl n ϖ l)⁻¹ ∈ NA E n := by
  rw [tl_eq_diagT]; exact diagT_conj_mem _ hu

theorem adelicUnitriangular_mul_mem_unipotentTimesIntegral {S : Finset (HeightOneSpectrum (𝓞 E))} {u g : GA E n} (hu : u ∈ NA E n) (hg : g ∈ C0 E n S) :
    u * g ∈ C0 E n S := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  exact ⟨u * v, mul_mem hu hv, k, hk, (mul_assoc _ _ _).symm⟩

end GlobalTheory.CellDec
end
end
