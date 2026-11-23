module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.Algebra.Module.Torsion.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem deRham_invariants_coord_finrank :
    ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV hL hfin hrk Φ hΦ
  haveI := PD.finK
  let D : Submodule K (Fin d → BdR) :=
    { carrier := {y | ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec
          (fun i => PD.actdR g (y i)) = y}
      add_mem' := by
        intro a b ha hb g
        have : (fun i => PD.actdR g ((a + b) i)) =
            (fun i => PD.actdR g (a i)) + (fun i => PD.actdR g (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, ha g, hb g]
      zero_mem' := by
        intro g
        have : (fun i => PD.actdR g ((0 : Fin d → BdR) i)) = 0 := by
          funext i; simp
        rw [this, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha g
        have : (fun i => PD.actdR g ((c • a) i)) = c • (fun i => PD.actdR g (a i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_smul, ha g] }
  have hmem : ∀ z, z ∈ DdR PD ρ ↔ Φ z ∈ D := by
    intro z
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← hΦ g z]
    exact Φ.injective.eq_iff.symm
  let e : ↥(DdR PD ρ) ≃ₗ[Qp] ↥D :=
    { toFun := fun z => ⟨Φ z.1, (hmem _).1 z.2⟩
      invFun := fun y => ⟨Φ.symm y.1, (hmem _).2 (by simpa using y.2)⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp)
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  haveI : Module.Finite Qp ↥(DdR PD ρ) := Module.Finite.trans LL _
  haveI : Module.Finite Qp ↥D := Module.Finite.equiv e
  refine ⟨D, fun y => Iff.rfl, Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K ↥D
  have h2 := Module.finrank_mul_finrank Qp LL ↥(DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  have h4 : Module.finrank Qp V = d := by simpa using Module.finrank_eq_card_basis bV
  have h5 := e.finrank_eq
  have hpos : 0 < Module.finrank Qp K := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h5, ← h2, hrk, ← h4, ← h3]
  ring

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_tensor_coord_of_basis {k V M : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] {d : ℕ} (bV : Module.Basis (Fin d) k V) :
    ∃ Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M), (∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b) ∧
      ∀ z, z = ∑ i, bV i ⊗ₜ[k] Φ z i := by
  classical
  let Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M) :=
    (TensorProduct.congr bV.equivFun (LinearEquiv.refl k M)).trans
      ((TensorProduct.comm k _ _).trans (TensorProduct.piScalarRight k k M (Fin d)))
  have h : ∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b := by
    intro v b i
    simp [Φ]
  refine ⟨Φ, h, fun z => ?_⟩
  apply Φ.injective
  funext j

  rw [map_sum, Finset.sum_apply]
  simp only [h, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Finsupp.single_apply, hij]
  · simp

theorem exists_coord_tensor_dR : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV
  obtain ⟨Φ, h, hz⟩ := exists_tensor_coord_of_basis (M := BdR) bV
  refine ⟨Φ, fun a z => ⟨?_, fun H => ?_⟩, fun g z => ?_⟩
  · rintro ⟨w, rfl⟩ i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [AlgebraTensorModule.map_tmul, h]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ b.2
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply]
      exact add_mem hx hy
  · rw [hz z]
    refine Submodule.sum_mem _ fun i _ => ⟨bV i ⊗ₜ ⟨Φ z i, H i⟩, ?_⟩
    rw [AlgebraTensorModule.map_tmul]
    rfl
  · have hact : ∀ (v : V) (b : BdR), actVdR PD ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ PD.actdR g b := by
      intro v b
      unfold actVdR
      rw [AlgebraTensorModule.map_tmul]
      rfl
    funext i
    conv_lhs => rw [hz z]

    rw [map_sum, map_sum, Finset.sum_apply]
    simp only [hact, h, Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.smul_def]

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem equivFinsuppOfBasisLeft_lTensor_apply {F : Type} [Field F] {V M N : Type}
    [AddCommGroup V] [Module F V] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι F V) (f : M →ₗ[F] N) (x : V ⊗[F] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem algebraTensorModule_map_id_apply {F L : Type} [Field F] [Field L] [Algebra F L]
    {V M N : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (x : V ⊗[F] M) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) f x = f.lTensor V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_tmul_one_of_frob_fixed_of_mem_fil_zero :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (x : V ⊗[Qp] B), φVB PD (LL := LL) (V := V) x = x → ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ x hφ hF
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  have key : ∀ i, ∃ c : Qp, algebraMap Qp B c = equivFinsuppOfBasisLeft b x i := by
    intro i
    apply PD.fund
    · have h := equivFinsuppOfBasisLeft_lTensor_apply b PD.φ.toLinearMap x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h2 : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) PD.φ.toLinearMap x = x := hφ
      rw [h2] at h
      exact h.symm
    · obtain ⟨y, hy⟩ := hF
      have h := equivFinsuppOfBasisLeft_lTensor_apply b
        (PD.ι.toLinearMap.restrictScalars Qp) x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h' := equivFinsuppOfBasisLeft_lTensor_apply b
        ((PD.Fil 0).restrictScalars Qp).subtype y i
      rw [← algebraTensorModule_map_id_apply (L := LL), hy] at h'
      have h3 : PD.ι (equivFinsuppOfBasisLeft b x i)
          = ((PD.Fil 0).restrictScalars Qp).subtype (equivFinsuppOfBasisLeft b y i) :=
        h.symm.trans h'
      rw [h3]
      exact (equivFinsuppOfBasisLeft b y i).2
  choose c hc using key
  refine ⟨∑ i ∈ (equivFinsuppOfBasisLeft b x).support, c i • b i, ?_⟩
  have hx : x = (equivFinsuppOfBasisLeft b).symm (equivFinsuppOfBasisLeft b x) := by simp
  rw [equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] at hx
  rw [TensorProduct.sum_tmul]
  refine hx.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hc i, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LineLattice

theorem exists_generator {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V) [Module.Free O T]
    (hsp : Submodule.span LL (T : Set V) = ⊤) (h1 : Module.finrank LL V = 1) :
    ∃ v : V, v ≠ 0 ∧ T = Submodule.span O {v} := by
  classical
  have hfin : Module.Finite LL V := Module.finite_of_finrank_eq_succ h1
  let b := Module.Free.chooseBasis O T
  have hli : LinearIndependent O (fun i => (b i : V)) :=
    b.linearIndependent.map' T.subtype T.ker_subtype
  have hli' : LinearIndependent LL (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing O LL).1 hli
  have hT : T = Submodule.span O (Set.range fun i => (b i : V)) := by
    have h := congrArg (Submodule.map T.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h.symm
  have hfi : Finite (Module.Free.ChooseBasisIndex O T) := hli'.finite
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex O T)
  have hc := hli'.fintype_card_le_finrank
  rw [h1] at hc
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) :=
    Fintype.card_le_one_iff_subsingleton.1 hc
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex O T) with he | ⟨⟨i⟩⟩
  · exfalso
    rw [Set.range_eq_empty, Submodule.span_empty] at hT
    have hb : Submodule.span LL (T : Set V) = ⊥ := by
      rw [hT]; simp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
    exact bot_ne_top (hb.symm.trans hsp)
  · refine ⟨b i, hli.ne_zero i, ?_⟩
    refine hT.trans ?_
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      rw [Subsingleton.elim j i]; rfl
    · rintro rfl
      exact ⟨i, rfl⟩

theorem lattice_rank_one {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [IsDomain O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (h1 : Module.finrank LL V = 1) :
    (∃ e : LL ≃ₗ[LL] V, ∀ x : LL, e x ∈ L.T ↔ x ∈ Set.range (algebraMap O LL)) ∧
    ∀ a : O, a ≠ 0 →
      Nonempty (↥(Submodule.torsionBy O (V ⧸ L.T) a) ≃ₗ[O] (O ⧸ Ideal.span {a})) := by
  haveI := L.free
  obtain ⟨v, hv, hT⟩ := exists_generator L.T L.span h1
  have hsurj : ∀ w : V, ∃ c : LL, c • v = w := (finrank_eq_one_iff_of_nonzero' v hv).1 h1
  have hmem : ∀ x : LL, x • v ∈ L.T ↔ x ∈ Set.range (algebraMap O LL) := by
    intro x
    rw [hT, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← algebraMap_smul LL c v] at hc
      exact smul_left_injective LL hv hc
    · rintro ⟨c, rfl⟩
      exact ⟨c, (algebraMap_smul LL c v).symm⟩
  refine ⟨⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton LL V v)
    ⟨smul_left_injective LL hv, hsurj⟩, hmem⟩, ?_⟩
  intro a ha
  have ha' : algebraMap O LL a ≠ 0 := by
    simpa using ha
  have hx : L.T.mkQ ((algebraMap O LL a)⁻¹ • v) ∈ Submodule.torsionBy O (V ⧸ L.T) a := by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem,
      mul_inv_cancel₀ ha']
    exact ⟨1, map_one _⟩
  let f : O →ₗ[O] Submodule.torsionBy O (V ⧸ L.T) a :=
    LinearMap.toSpanSingleton O _ ⟨_, hx⟩
  have hf : ∀ c : O, (f c : V ⧸ L.T) =
      L.T.mkQ ((algebraMap O LL c * (algebraMap O LL a)⁻¹) • v) := by
    intro c
    rw [← smul_smul, algebraMap_smul, map_smul]
    rfl
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := L.T.mkQ_surjective y
    obtain ⟨x, rfl⟩ := hsurj w
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, Subtype.ext ?_⟩
    rw [hf, hc, mul_comm (algebraMap O LL a) x, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  have hk : LinearMap.ker f = Ideal.span {a} := by
    ext c
    rw [LinearMap.mem_ker, Subtype.ext_iff, hf, Ideal.mem_span_singleton']
    rw [Submodule.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, IsFractionRing.injective O LL ?_⟩
      rw [map_mul, hd, mul_assoc, inv_mul_cancel₀ ha', mul_one]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      rw [map_mul, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  exact ⟨(f.quotKerEquivOfSurjective hfs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

end GlobalTheory.LineLattice
end
