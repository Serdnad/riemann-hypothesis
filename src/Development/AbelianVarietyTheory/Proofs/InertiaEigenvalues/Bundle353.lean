module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle078
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle331
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle101
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section PotTransport

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem linearMap_tensorOne_comm_diagonalAction {H : Type} [Group H] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    [Algebra Qp K₁] [Algebra Qp K₂] [Algebra K₁ K₂] [IsScalarTower Qp K₁ K₂]
    [Algebra K₁ B] [IsScalarTower Qp K₁ B]
    [Algebra K₁ BdR] [Algebra K₂ BdR] [IsScalarTower Qp K₂ BdR]
    [IsScalarTower K₁ K₂ BdR] [IsScalarTower Qp K₁ BdR]
    (PD : PeriodData H Qp K₁ K₂ B BdR) {σ : Representation LL H V} {σ' : Representation LL H V'}
    (f : V →ₗ[LL] V') (hf : ∀ g v, f (σ g v) = σ' g (f v)) (g : H) (x : V ⊗[Qp] B) :
    SumJumps.ext1 Qp B f (actVB PD σ g x) = actVB PD σ' g (SumJumps.ext1 Qp B f x) := by
  unfold actVB
  rw [SumJumps.ext1_comm f (σ g) (σ' g) (hf g)]

theorem eq_map_of_equiv_tensor (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] B)) (S' : Submodule LL (V' ⊗[Qp] B))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp B e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp B e.symm.toLinearMap x ∈ S) :
    S = S'.map (SumJumps.ext1 Qp B e.symm.toLinearMap) := by
  apply le_antisymm
  · intro x hx
    refine ⟨_, a x hx, ?_⟩
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  · rintro _ ⟨y, hy, rfl⟩
    exact b y hy

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem dpcris_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ PC.Dpcris ρ, SumJumps.ext1 Qp B f x ∈ PC.Dpcris ρ' :=
  SumJumps.dcris_map PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') f (fun h v => hf (h : G) v)

theorem eig_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (I : Subgroup G)
    (a : I →* LLˣ) : ∀ x ∈ PC.Eig ρ I a, SumJumps.ext1 Qp B f x ∈ PC.Eig ρ' I a := by
  intro x hx
  simp only [PotCrysData.Eig, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  refine ⟨dpcris_map PC f hf x hx.1, fun g => ?_⟩
  rw [← linearMap_tensorOne_comm_diagonalAction PC.PD f hf, hx.2 g, map_smul]

theorem potCrys_inertiaThrough_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧
      ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S := by
  have he' : ∀ g v, e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) :=
    symm_equivariant e he
  refine ⟨fun h => isCrys_of_equiv PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') e (fun h v => he (h : G) v) h, fun S hS => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨h1, h2, ?_⟩
  have hD : PC.Dpcris ρ = (PC.Dpcris ρ').map (SumJumps.ext1 Qp B e.symm.toLinearMap) :=
    eq_map_of_equiv_tensor e _ _ (dpcris_map PC e.toLinearMap he)
      (dpcris_map PC e.symm.toLinearMap he')
  have hE : ∀ a, PC.Eig ρ PC.Iner a =
      (PC.Eig ρ' PC.Iner a).map (SumJumps.ext1 Qp B e.symm.toLinearMap) := fun a =>
    eq_map_of_equiv_tensor e _ _ (eig_map PC e.toLinearMap he _ a)
      (eig_map PC e.symm.toLinearMap he' _ a)
  rw [hD, h3, Submodule.map_iSup]
  congr 1; ext a
  rw [Submodule.map_iSup, hE]

end PotTransport

end GlobalTheory.HTW.Rec

theorem GlobalTheory.HTW.Rec.potCrysData_transport : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (e : V ≃ₗ[LL] V'),
    (∀ g v, e (ρ g v) = ρ' g (e v)) →
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧ ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S :=
  by
  intros
  exact GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ ‹_› ‹_›
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLatDescent

theorem dualLat_resQ : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  intro l _ P K LL _ _ O _ _ V _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ _ _ lam n e f h1 h2 h3 ρ ρ' L L' LZ LZ' hT hT' Pr PQ hPQ hP
  obtain ⟨⟨hg, hl, hr, hrk⟩, hlat⟩ := hP

  have key : ∀ z : LL, (∀ a : LL, lam (a * z) = 0) → z = 0 := by
    intro z hz
    rw [h3 z]
    simp [hz]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g x y
    rw [hPQ, GlobalTheory.PstCoeff.resQ_apply, GlobalTheory.PstCoeff.resQ_apply, hg, hPQ]
    have : ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      simp [cycLL]
    rw [this, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro x hx
    apply hl
    intro y
    apply key
    intro a
    rw [← smul_eq_mul, ← map_smul, ← hPQ]
    exact hx _
  · intro y hy
    apply hr
    intro x
    apply key
    intro a
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, ← hPQ]
    exact hy _
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', hrk]
  · intro y
    rw [hT', hlat]
    constructor
    · intro H x hx
      obtain ⟨a, ha⟩ := H x ((hT x).1 hx)
      obtain ⟨z, hz⟩ := h2 a
      exact ⟨z, by rw [hPQ, ha, hz]; rfl⟩
    · intro H x hx
      have hi : ∀ i, ∃ z : ℤ_[l], lam (algebraMap O LL (f i) * Pr x y) = (z : ℚ_[l]) := by
        intro i
        have hm : f i • x ∈ L.T := L.T.smul_mem _ hx
        obtain ⟨z, hz⟩ := H _ ((hT _).2 hm)
        refine ⟨z, ?_⟩
        rw [hPQ, ← algebraMap_smul LL (f i) x, map_smul, LinearMap.smul_apply, smul_eq_mul] at hz
        rw [hz]; rfl
      choose z hz using hi
      have ho : ∀ i, ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z i : ℚ_[l]) := fun i => h1 (z i)
      choose o ho using ho
      refine ⟨∑ i, o i * e i, ?_⟩

      rw [h3 (Pr x y), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i, map_mul, ho i, Algebra.smul_def]

end GlobalTheory.DualLatDescent
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory

theorem latticeZl_of_latticeO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (L : Lattice (O := O) ρ),
    ∃ LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ), ∀ v, v ∈ LZ.T ↔ v ∈ L.T := by
  intro l _ K LL _ _ O _ _ V _ _ _ _ _ _ _ _ lam n e f h1 h2 h3 ρ L

  have hz : ∀ (z : ℤ_[l]) (v : V), z • v = ((z : ℚ_[l]) : ℚ_[l]) • v := fun z v => by
    rw [← algebraMap_smul ℚ_[l] z v]; rfl

  have hdec : ∀ (a : LL) (t : V), a • t = ∑ i, lam (algebraMap O LL (f i) * a) • (e i • t) := by
    intro a t
    conv_lhs => rw [h3 a]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_assoc, algebraMap_smul]
  let TZ : Submodule ℤ_[l] V :=
    { carrier := (L.T : Set V)
      add_mem' := fun ha hb => L.T.add_mem ha hb
      zero_mem' := L.T.zero_mem
      smul_mem' := by
        intro z v hv
        obtain ⟨o, ho⟩ := h1 z
        show z • v ∈ L.T
        rw [hz, ← algebraMap_smul LL (z : ℚ_[l]) v, ← ho, algebraMap_smul]
        exact L.T.smul_mem o hv }
  have hmem : ∀ v, v ∈ TZ ↔ v ∈ L.T := fun v => Iff.rfl

  have hfg : TZ.FG := by
    obtain ⟨S, hS⟩ := L.fg
    classical
    refine ⟨Finset.image (fun p : Fin n × V => e p.1 • p.2) (Finset.univ ×ˢ S), ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_product, Set.mem_prod, Finset.coe_univ,
        Set.mem_univ, true_and, Finset.mem_coe] at hx
      obtain ⟨⟨i, t⟩, ht, rfl⟩ := hx
      have : t ∈ L.T := hS ▸ Submodule.subset_span ht
      exact L.T.smul_mem (e i) this
    · intro x hx
      have hx' : x ∈ Submodule.span O (S : Set V) := by rw [hS]; exact hx
      obtain ⟨c, -, rfl⟩ := (Submodule.mem_span_finset).1 hx'
      refine Submodule.sum_mem _ fun t ht => ?_
      rw [← algebraMap_smul LL (c t) t, hdec]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨z, hz'⟩ := h2 (f i * c t)
      rw [← map_mul, hz', ← hz]
      refine Submodule.smul_mem _ z (Submodule.subset_span ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_product, Set.mem_prod, Finset.coe_univ,
        Set.mem_univ, true_and, Finset.mem_coe]
      exact ⟨(i, t), ht, rfl⟩
  have hfin : Module.Finite ℤ_[l] TZ := Module.Finite.iff_fg.mpr hfg
  have htf : Module.IsTorsionFree ℤ_[l] TZ := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro z x h
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    right
    have h' : ((z : ℚ_[l]) : ℚ_[l]) • (x : V) = 0 := by
      rw [← hz]; exact congrArg Subtype.val h
    have hq : (z : ℚ_[l]) ≠ 0 := fun h0 => hz0 (PadicInt.coe_eq_zero.1 h0)
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left hq)
  refine ⟨{ T := TZ, stable := ?_, fg := hfg, free := ?_, span := ?_ }, hmem⟩
  · intro g x hx
    exact L.stable g x hx
  · exact Module.free_of_finite_type_torsion_free'
  · let W : Submodule LL V :=
      { carrier := (Submodule.span ℚ_[l] (TZ : Set V) : Set V)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := by
          intro a x hx
          induction hx using Submodule.span_induction with
          | mem t ht =>
            show a • t ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [hdec]
            refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
            exact L.T.smul_mem (e i) ht
          | zero => simp
          | add x y _ _ hx hy =>
            show a • (x + y) ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [smul_add]; exact Submodule.add_mem _ hx hy
          | smul q x _ hx =>
            show a • (q • x) ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [← algebraMap_smul LL q x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
            exact Submodule.smul_mem _ q hx }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← L.span, Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ht
    rw [eq_top_iff]
    intro v _
    have : v ∈ W := hW ▸ Submodule.mem_top
    exact this
end GlobalTheory
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.nonempty_closure_hom_tilt_field : ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  first | exact @GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | exact GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | (intros; apply GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem ph_c_cob : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∃ b : ℝ, 0 < b ∧ ∀ (H : Subgroup ↥(GK K)) (t : ℝ), 0 < t → (∀ g ∈ H, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t) → ∀ i j, ∃ y : ℂ_[l], ∀ g ∈ H, ‖Formalism.Per.σC (g : GQ l) y - y - algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j)‖ ≤ b * t ^ 2 := by
  intro l _ n _ _ K ρ M hM
  set Mi : Matrix n n ℂ_[l] := ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) with hMi
  set a : ℝ := 1 + ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) with ha
  have hterm : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) := by
    intro i j
    calc ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ j', (‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖)
            (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖))
            (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ i)
  have hMa : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg (Mi i j); rw [ha]; linarith
  have hMia : ∀ i j, ‖Mi i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg ((M : Matrix n n ℂ_[l]) i j); rw [ha]; linarith
  have ha0 : 0 < a := by
    rw [ha]; have : 0 ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    linarith
  obtain ⟨c, hc, hAx⟩ := GlobalTheory.T.axLemma_padicComplexMatrix_galoisSubgroup_approximation l
  refine ⟨c * a ^ 2, by positivity, ?_⟩
  intro H t ht hρ i j
  set rC : ↥(GK K) → Matrix n n ℂ_[l] := fun g => (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) with hrCdef
  have hrent : ∀ g : ↥(GK K), ∀ i j, (rC g - 1) i j = algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j) := by
    intro g i j
    have e : rC g - 1 = (algebraMap ℚ_[l] ℂ_[l]).mapMatrix ((ρ g : Matrix n n ℚ_[l]) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]; rfl
  have hrow : ∀ g ∈ H, ∀ i j, ‖(rC g - 1) i j‖ ≤ t := by
    intro g hg i j; rw [hrent, norm_algebraMap']; exact hρ g hg i j
  have hY : ∀ g ∈ H, ∀ i j, ‖(Mi.map (Formalism.Per.σC (g : GQ l)) - Mi) i j‖ ≤ a * t := by
    intro g hg i j
    have hs := GlobalTheory.T.galois_inv_complexPadic_periodMatrix l n K ρ M hM g
    have e : Mi.map (Formalism.Per.σC (g : GQ l)) - Mi = Mi * (rC g - 1) := by
      rw [hMi, hs, mul_sub, mul_one]
    rw [e]
    exact GlobalTheory.T.norm_mul_apply_le_of_ultrametric ℂ_[l] n Mi (rC g - 1) a t ha0.le ht.le hMia (hrow g hg) i j
  obtain ⟨Z, hZ, hZb⟩ := hAx n K H Mi (a * t) (by positivity) hY
  refine ⟨-((M : Matrix n n ℂ_[l]) * Z) i j, fun g hg => ?_⟩
  have hcore := GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul ℂ_[l] n (Formalism.Per.σC (g : GQ l)) (rC g) (M : Matrix n n ℂ_[l]) Mi Z a (c * (a * t)) t
    ha0.le (by positivity) ht.le (GlobalTheory.RingBasics.norm_σC _) (by rw [hMi]; exact M.mul_inv) (hM g) (hZ g hg) hMa hZb (hrow g hg) i j
  rw [hrent] at hcore
  calc _ ≤ t * (a * (c * (a * t))) := hcore
    _ = c * a ^ 2 * t ^ 2 := by ring

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.RegularDense

theorem fixed_of_inertia_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l),
    (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) →
    ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y →
      ∀ g : GQ l, Per.σC g y = y := by
  intro l hl F hF y hI hFy g
  let H : Subgroup (GQ l) :=
    { carrier := {h | Per.σC h y = y}
      mul_mem' := fun {a b} ha hb => by
        show Per.σC (a * b) y = y
        have ha' : Per.σC a y = y := ha
        have hb' : Per.σC b y = y := hb
        rw [GlobalTheory.RingBasics.σC_mul, hb', ha']
      one_mem' := by
        show Per.σC 1 y = y
        rw [GlobalTheory.RingBasics.σC_one]
      inv_mem' := fun {a} ha => by
        show Per.σC a⁻¹ y = y
        have ha' : Per.σC a y = y := ha
        conv_lhs => rw [← ha']
        rw [← GlobalTheory.RingBasics.σC_mul, inv_mul_cancel, GlobalTheory.RingBasics.σC_one] }
  have hy := ax_sen_tate l H y (fun h hh => hh)
  have hcont : Continuous (fun z : ℂ_[l] => Per.σC g z) := by
    refine Isometry.continuous (Isometry.of_dist_eq fun a b => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, GlobalTheory.RingBasics.norm_σC]
  have hcl : IsClosed {z : ℂ_[l] | Per.σC g z = z} := isClosed_eq hcont continuous_id
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨z, hz, rfl⟩
  show Per.σC g (z : ℂ_[l]) = z
  rw [GlobalTheory.RingBasics.σC_coe]
  congr 1
  have hzK : z ∈ MaximalUnramifiedExtension l := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
    intro h hh
    exact hz h (hI h hh)
  have hFz : F z = z := hz F hFy
  have hpow : ∀ n : ℕ, (F ^ n) z = z := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hFz, ih]
  obtain ⟨m, hm, hlm, hH⟩ := FrobLaws.exists_level hzK
  have hr : ∀ (n : ℕ) (ζ : Om l), ζ ^ m = 1 → (F ^ n) ζ = ζ ^ (l ^ n) := fun n ζ hζ => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF ζ m hm hlm hζ, ← pow_mul, pow_succ']
  obtain ⟨n, hn⟩ := FrobLaws.gal_root g hm hlm
  rw [hH g (F ^ n) fun ζ hζ => by rw [hn ζ hζ, hr n ζ hζ], hpow]

end GlobalTheory.RegularDense
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  first | exact @GlobalTheory.UnitLine.sigma_unit_eigen | exact GlobalTheory.UnitLine.sigma_unit_eigen | (intros; apply GlobalTheory.UnitLine.sigma_unit_eigen <;> assumption)
end
