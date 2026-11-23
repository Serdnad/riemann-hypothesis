module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Mathlib.Algebra.AlgebraicCard
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle135
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle381
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CompactRepField

open Polynomial IntermediateField

theorem exists_mem_adjoin_simple (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (j : Ω →+* PadicAlgCl l) (x : PadicAlgCl l) : ∃ y : Ω, x ∈ ℚ_[l]⟮j y⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hfin : ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint x)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖x - y‖ < ‖x - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  obtain ⟨y, hy⟩ := (GlobalTheory.denseRange_of_isAlgClosed_padicAlgCl l Ω j).exists_mem_open hop
    ⟨x, by
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
      exact fun x' h => h.2⟩
  refine ⟨y, IsKrasner.krasner (minpoly.irreducible (hint x)).separable (IsAlgClosed.splits _)
    (hint _) fun x' h1 h2 => ?_⟩
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy
  exact hy x' ⟨h1, h2⟩

theorem exists_countable_family (l : ℕ) [Fact l.Prime] :
    ∃ (ι : Type) (_ : Countable ι) (K : ι → IntermediateField ℚ_[l] (PadicAlgCl l)),
      (∀ i, FiniteDimensional ℚ_[l] (K i)) ∧
      ∀ s : Set (PadicAlgCl l), s.Finite → ∃ i, s ⊆ K i := by
  classical
  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Countable (AlgebraicClosure ℚ) := by
    have h : {x : AlgebraicClosure ℚ | IsAlgebraic ℚ x}.Countable := Algebraic.countable ℚ _
    exact Set.countable_univ_iff.1 (h.mono fun x _ => halg.isAlgebraic x)
  let j : AlgebraicClosure ℚ →+* PadicAlgCl l :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := PadicAlgCl l)).toRingHom
  refine ⟨Finset (AlgebraicClosure ℚ), inferInstance,
    fun S => IntermediateField.adjoin ℚ_[l] (j '' (S : Set _)), fun S => ?_, fun s hs => ?_⟩
  · haveI : Finite (j '' (S : Set (AlgebraicClosure ℚ))) := (S.finite_toSet.image j).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  · choose y hy using exists_mem_adjoin_simple l (AlgebraicClosure ℚ) j
    refine ⟨(hs.image y).toFinset, fun x hx => ?_⟩
    refine IntermediateField.adjoin.mono _ _ _ ?_ (hy x)
    rw [Set.singleton_subset_iff]
    exact ⟨y x, by simpa using ⟨x, hx, rfl⟩, rfl⟩

def entrySubgroup {F E G : Type} [Field F] [Field E] [Algebra F E] [Group G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) E) (K : IntermediateField F E) : Subgroup G where
  carrier := {g | ∀ i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K ∧
    (r g⁻¹ : Matrix (Fin a) (Fin a) E) i j ∈ K}
  one_mem' := fun i j => by
    have : (r 1 : Matrix (Fin a) (Fin a) E) i j ∈ K := by
      rw [map_one, Units.val_one, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    exact ⟨this, by rwa [inv_one]⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨sum_mem fun k _ => mul_mem (hg i k).1 (hh k j).1,
      sum_mem fun k _ => mul_mem (hh i k).2 (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem exists_finiteDimensional_entries_mem (l : ℕ) [Fact l.Prime] (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (n : ℕ)
    (r : G →* Matrix.GeneralLinearGroup (Fin n) (PadicAlgCl l))
    (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧
      ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K := by
  obtain ⟨ι, _, K, hK, hcov⟩ := exists_countable_family l
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (entrySubgroup r (K m) : Set G) := fun m => by
    have : (entrySubgroup r (K m) : Set G) = ⋂ i, ⋂ j,
        ((fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m) ∩
         (fun g => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      ((hKcl m).preimage (hr i j)).inter ((hKcl m).preimage ((hr i j).comp continuous_inv))
  have hun : ⋃ m, (entrySubgroup r (K m) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov
      (Set.range (fun p : Fin n × Fin n => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2) ∪
       Set.range (fun p : Fin n × Fin n => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2))
      ((Set.finite_range _).union (Set.finite_range _))
    exact Set.mem_iUnion.2 ⟨m, fun i j =>
      ⟨hm (Or.inl ⟨(i, j), rfl⟩), hm (Or.inr ⟨(i, j), rfl⟩)⟩⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (entrySubgroup r (K m) : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (G ⧸ entrySubgroup r (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  let s : Set (PadicAlgCl l) := Set.range fun p : (G ⧸ entrySubgroup r (K m)) × Fin n × Fin n =>
    (r p.1.out : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hK m
  refine ⟨IntermediateField.adjoin ℚ_[l] s ⊔ K m, inferInstance, fun g i j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (entrySubgroup r (K m)) g
  have hg : g = (g : G ⧸ entrySubgroup r (K m)).out * (h : G)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, map_mul, Units.val_mul, Matrix.mul_apply]
  refine sum_mem fun k _ => mul_mem ?_ ?_
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g, i, k), rfl⟩)
  · exact (le_sup_right : K m ≤ _) (h.2 k j).2

theorem exists_finExt_entries_mem :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  intro l _ G _ _ _ _ _ a r hr L₀
  obtain ⟨K, hK, h⟩ := exists_finiteDimensional_entries_mem l G a r
    fun i j => hr.matrix_elem i j
  haveI := L₀.2
  exact ⟨⟨L₀.1 ⊔ K, inferInstance⟩, le_sup_left, fun g i j =>
    (le_sup_right : K ≤ L₀.1 ⊔ K) (h g i j)⟩

end GlobalTheory.CompactRepField
end

section

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory

section InertialCharacters

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
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem inertialEig_mem_iff (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ)
    (w : V ⊗[Qp] B) :
    w ∈ PC.Eig ρ I a ↔ w ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ (g : G) w = ((a g : LLˣ) : LL) • w := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem actVB_one_apply (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem inertialEig_inf_iSup_eq_bot (ρ : Representation LL G V) (I : Subgroup G) (b : I →* LLˣ)
    (T : Finset (I →* LLˣ)) (hb : b ∉ T) :
    PC.Eig ρ I b ⊓ (⨆ a ∈ T, PC.Eig ρ I a) = ⊥ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a0 T' ha0 ih =>
    have hba0 : b ≠ a0 := fun h => hb (h ▸ Finset.mem_insert_self _ _)
    have hbT : b ∉ T' := fun h => hb (Finset.mem_insert_of_mem h)
    have ih' := ih hbT
    obtain ⟨g, hg⟩ : ∃ g : I, b g ≠ a0 g := by
      by_contra h
      push_neg at h
      exact hba0 (MonoidHom.ext h)
    have hne : ((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL) ≠ 0 := by
      intro h
      exact hg (Units.ext (sub_eq_zero.mp h))
    set f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
      actVB PC.PD ρ (g : G) - ((a0 g : LLˣ) : LL) • LinearMap.id with hf
    have hfE : ∀ (a : I →* LLˣ) w, w ∈ PC.Eig ρ I a →
        f w = (((a g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • w := by
      intro a w hw
      rw [inertialEig_mem_iff] at hw
      simp [hf, hw.2 g, sub_smul]
    have hmapT : ∀ z ∈ (⨆ a ∈ T', PC.Eig ρ I a), f z ∈ (⨆ a ∈ T', PC.Eig ρ I a) := by
      intro z hz
      have : (⨆ a ∈ T', PC.Eig ρ I a) ≤ (⨆ a ∈ T', PC.Eig ρ I a).comap f := by
        refine iSup₂_le fun a ha w hw => ?_
        rw [Submodule.mem_comap, hfE a w hw]
        exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun a (_ : a ∈ T') => PC.Eig ρ I a) a ha) hw)
      exact this hz
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxb, hxs⟩ := hx
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, rfl⟩ := hxs
    have hfx : f (y + z) = (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) := hfE b _ hxb
    have hfy : f y = 0 := by rw [hfE a0 y hy, sub_self, zero_smul]
    have hmem : (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) ∈
        PC.Eig ρ I b ⊓ (⨆ a ∈ T', PC.Eig ρ I a) := by
      refine ⟨Submodule.smul_mem _ _ hxb, ?_⟩
      rw [← hfx, map_add (f := _), hfy, zero_add]
      exact hmapT z hz
    rw [ih'] at hmem
    rw [Submodule.mem_bot] at hmem ⊢
    exact (smul_eq_zero.mp hmem).resolve_left hne

theorem conj_mem_Iner (F : G) (g : G) (hg : g ∈ PC.Iner) : F⁻¹ * g * F ∈ PC.Iner := by
  intro c
  obtain ⟨c', hc'⟩ := PC.stableK₀' F c
  have hg' := hg c'
  have hFinv : PC.PD.actB F⁻¹ (algebraMap K₀' B c') = algebraMap K₀' B c := by
    rw [← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
  rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc', hg', hFinv]

def inerConj (F : G) : PC.Iner →* PC.Iner where
  toFun g := ⟨F⁻¹ * (g : G) * F, conj_mem_Iner PC F g g.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

theorem exists_frobStable_inertiaThrough {ι : Type} (ρ : ι → Representation LL G V) (F : G)
    (S : Finset (PC.Iner →* LLˣ)) (h1 : 1 ∈ S) (hS : ∀ x, PC.InertiaThrough (ρ x) S) :
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  classical
  let Sig : Finset (PC.Iner →* LLˣ) :=
    insert 1 (S.filter (fun a => ∃ x, PC.Eig (ρ x) PC.Iner a ≠ ⊥))
  have hSigS : Sig ⊆ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact h1
    · exact (Finset.mem_filter.mp ha).1
  refine ⟨Sig, hSigS, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨1, Finset.mem_insert_self _ _, fun g h _ => by simp⟩
    obtain ⟨haS, x, hx⟩ := Finset.mem_filter.mp ha
    let b : PC.Iner →* LLˣ := a.comp (inerConj PC F)
    refine ⟨b, ?_, ?_⟩
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      rw [inertialEig_mem_iff] at hv
      set u := actVB PC.PD (ρ x) F v with hu
      have huD : u ∈ PC.Dpcris (ρ x) := pc_Dpcris_stable PC (ρ x) F hv.1
      have hu0 : u ≠ 0 := by
        intro h
        apply hv0
        have : actVB PC.PD (ρ x) F⁻¹ u = v := by
          rw [hu, ← pc_actVB_mul, inv_mul_cancel, actVB_one_apply]
        rw [← this, h, map_zero]
      have huE : u ∈ PC.Eig (ρ x) PC.Iner b := by
        rw [inertialEig_mem_iff]
        refine ⟨huD, fun g => ?_⟩
        have e : (g : G) * F = F * (F⁻¹ * (g : G) * F) := by group
        have hc := hv.2 (inerConj PC F g)
        rw [hu, ← pc_actVB_mul, e, pc_actVB_mul]
        change actVB PC.PD (ρ x) F (actVB PC.PD (ρ x) ((inerConj PC F g : PC.Iner) : G) v) = _
        rw [hc, map_smul]
        rfl
      have hbS : b ∈ S := by
        by_contra hbS
        have hbot := inertialEig_inf_iSup_eq_bot PC (ρ x) PC.Iner b S hbS
        apply hu0
        have : u ∈ PC.Eig (ρ x) PC.Iner b ⊓ (⨆ a ∈ S, PC.Eig (ρ x) PC.Iner a) := by
          refine ⟨huE, ?_⟩
          rw [← (hS x).2.2]
          exact huD
        rw [hbot] at this
        exact (Submodule.mem_bot LL).mp this
      apply Finset.mem_insert_of_mem
      refine Finset.mem_filter.mpr ⟨hbS, x, ?_⟩
      intro h
      apply hu0
      have := huE
      rw [h] at this
      exact (Submodule.mem_bot LL).mp this
    · intro g h hh
      change a (inerConj PC F g) = a h
      congr 1
      ext
      exact hh.symm
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · intro a ha g hg
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rfl
      · exact (hS x).1 a (Finset.mem_filter.mp ha).1 g hg
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp
      · exact (hS x).2.1 a (Finset.mem_filter.mp ha).1
    · apply le_antisymm
      · rw [(hS x).2.2]
        refine iSup₂_le fun a ha => ?_
        by_cases h0 : PC.Eig (ρ x) PC.Iner a = ⊥
        · rw [h0]; exact bot_le
        · have haSig : a ∈ Sig := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, x, h0⟩)
          exact le_iSup₂ (f := fun a (_ : a ∈ Sig) => PC.Eig (ρ x) PC.Iner a) a haSig
      · exact iSup₂_le fun a _ => inf_le_left

end InertialCharacters

theorem frobStable_inertial_subset : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
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
    {ι : Type} (ρ : ι → Representation LL G V) (F : G) (S : Finset (PC.Iner →* LLˣ)),
    1 ∈ S → (∀ x, PC.InertiaThrough (ρ x) S) →
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  intros
  apply exists_frobStable_inertiaThrough <;> assumption

end GlobalTheory
end
end

section

open scoped NNReal

namespace GlobalTheory

theorem perfectRing_valuationSubring_of_isAlgClosed (l : ℕ) [Fact l.Prime] {L : Type} [Field L]
    [IsAlgClosed L] (V : ValuationSubring L) [CharP V l] : PerfectRing V l := by
  haveI : ExpChar V l := ExpChar.prime Fact.out
  refine PerfectRing.ofSurjective V l ?_
  intro v
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (v : L) (Nat.pos_of_ne_zero hl0)
  have hyV : y ∈ V := by
    rw [← V.valuation_le_one_iff]
    have hv : V.valuation (v : L) ≤ 1 := (V.valuation_le_one_iff _).2 v.2
    rw [← hy, map_pow] at hv
    exact (pow_le_one_iff_of_nonneg (zero_le') hl0).1 hv
  refine ⟨⟨y, hyV⟩, ?_⟩
  apply Subtype.ext
  simp [frobenius_def, hy]

theorem s_points_kpt : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 →
    u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) →
    (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) →
    ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  intro l _ R _ u x hl hu hrad H M
  rcases GlobalTheory.T.pow_dvd_bound_or_exists_valuationSubring_dvd R u x M hu hrad with h | ⟨L, _, _, V, f, hfu, hfnu, hdvd⟩
  · exact h
  exfalso
  haveI : CharP V l := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast f, hl, map_zero])
  haveI : PerfectRing V l := perfectRing_valuationSubring_of_isAlgClosed l V
  obtain ⟨hdom, hpre, hne, hnu, hcomp⟩ := GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain V (f u) hfu hfnu
  obtain ⟨hl', hbij⟩ := GlobalTheory.T.adicCompletion_principal_perfect l V (f u)
  set O := AdicCompletion (Ideal.span {f u}) V
  haveI : IsDomain O := hdom
  haveI : ValuationRing O := { toPreValuationRing := hpre }
  haveI : CharP O l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl'
  haveI : PerfectRing O l := ⟨hbij⟩
  let g : R →+* O := (algebraMap V O).comp f
  have hgx : g x = 0 := H O g hne hnu hcomp
  have hd : g x ∣ g u ^ M := by
    simpa [g, map_pow] using map_dvd (algebraMap V O) hdvd
  rw [hgx, zero_dvd_iff] at hd
  exact hne (by_contra fun h => pow_ne_zero M h hd)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellCompare

theorem isFundamentalDomain_of_map {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G)
    (H : Subgroup G) (Γ : Subgroup H) (𝓕 : Set G)
    (h : IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ) : IsFundamentalDomain Γ 𝓕 μ := by
  let E := Subgroup.equivMapOfInjective Γ H.subtype H.subtype_injective
  refine h.preimage_of_equiv (f := id) (e := E.symm) (Measure.QuasiMeasurePreserving.id μ)
    E.symm.bijective (fun g x => ?_)
  show (((E.symm g : Γ) : H) : G) * x = (g : G) * x
  congr 1
  have h1 : ((E (E.symm g) : Γ.map H.subtype) : G) = (g : G) := by rw [E.apply_symm_apply]
  rw [← h1, Subgroup.coe_equivMapOfInjective_apply]
  rfl

end GlobalTheory.CellCompare

theorem GlobalTheory.CellCompare.lintegral_comparison : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ Γ' : Subgroup H) [Countable Γ] [Countable Γ'] (D D' : Set H), IsFundamentalDomain Γ D ν →
    IsFundamentalDomain Γ' D' ν → ∀ (𝓕 𝓕' : Set G), IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ →
    IsFundamentalDomain (Γ'.map H.subtype) 𝓕' μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ h : H, ∀ g, f (h * g) = f g) →
    ν D' * ∫⁻ g in 𝓕, f g ∂μ = ν D * ∫⁻ g in 𝓕', f g ∂μ := by
  intro G _ _ _ _ μ _ _ H ν _ _ _ Γ Γ' _ _ D D' hD hD' 𝓕 𝓕' h𝓕 h𝓕' f hf hinv
  haveI : MeasurableSMul₂ H G := ⟨(measurable_subtype_coe.comp measurable_fst).mul measurable_snd⟩
  haveI : SMulInvariantMeasure H G μ := inferInstance
  haveI : MeasurableInv H := ⟨by
    have : Measurable fun x : H => (((x : G)⁻¹ : G)) := measurable_subtype_coe.inv
    exact Measurable.subtype_mk (f := fun x : H => ((x : G))⁻¹) (h := fun x => H.inv_mem x.2) this⟩
  haveI : MeasurableMul₂ H := ⟨by
    have : Measurable fun p : H × H => ((p.1 : G) * (p.2 : G)) :=
      (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
    exact Measurable.subtype_mk (f := fun p : H × H => ((p.1 : G) * (p.2 : G)))
      (h := fun p => H.mul_mem p.1.2 p.2.2) this⟩
  exact GlobalTheory.CovolIndep.lintegral_mul_eq ν μ Γ Γ' 𝓕 𝓕' D D'
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ 𝓕 h𝓕)
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ' 𝓕' h𝓕') hD hD' f hf (fun s x => hinv s x)
end
