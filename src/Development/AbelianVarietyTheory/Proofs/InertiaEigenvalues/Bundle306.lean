module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle040
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle280
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.ConjugateSelfDual.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem tmul_gen_cancel (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    (e : T.V) (he : e ≠ 0) (heT : e ∈ T.L.T) (e₀ : ↥T.L.T) (h₀ : Submodule.span O {e₀} = ⊤)
    {R : Type} [CommRing R] [Algebra O R] (r r' : R)
    (h : (r ⊗ₜ[O] e₀ : TW R T) = r' ⊗ₜ[O] e₀) : r = r' := by
  have hne : (e₀ : T.V) ≠ 0 := by
    intro h0
    have hm : (⟨e, heT⟩ : ↥T.L.T) ∈ Submodule.span O {e₀} := by rw [h₀]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    apply he
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      have h1 : c • (e₀ : T.V) = 0 := congrArg Subtype.val hc
      rw [← algebraMap_smul LL c, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact hO (by rw [h1, map_zero])
      · exact absurd h1 hne
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h₀]
  let φ := LinearEquiv.ofBijective _ hb
  have hφ : φ.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [φ]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R φ.symm.toLinearMap z)) h
  simpa [hφ] using this

theorem etTie_io_act (hO : Function.Injective (algebraMap O LL)) {W : LocWach PD LL O v n}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {incl : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW incl φR gR πA) (g : G) (a : LetA O n) :
    incl (E.io (W.γA (W.resΓ g) a)) = gR g (incl (E.io a)) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (algebraMap (LetA O n) W.EE a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, TWact_smul, h1, W.γE_ext, E.ioE_ext,
    E.ioE_ext, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

end Generic



theorem io_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  intro l _ P AI K s LL h W E g a
  exact etTie_io_act Subtype.val_injective E.tie g a

end GlobalTheory.Cyc.Decomp
end
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LatBasis

variable {l : ℕ} [Fact l.Prime]

theorem exists_basis_of_submodule {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] (S : Submodule ℤ_[l] V) [Module.Free ℤ_[l] S]
    [Module.Finite ℤ_[l] S] (hS : ∀ x : V, ∃ y : ℤ_[l], y ≠ 0 ∧ y • x ∈ S) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ x : V, x ∈ S ↔ ∀ i, ‖w.repr x i‖ ≤ 1 := by
  let b := Module.finBasis ℤ_[l] S
  have hli : LinearIndependent ℤ_[l] (fun i => (b i : V)) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hli' : LinearIndependent ℚ_[l] (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hli
  have hsum : ∀ t : S, (t : V) = ∑ i, ((b.repr t i : ℤ_[l]) : ℚ_[l]) • (b i : V) := by
    intro t
    conv_lhs => rw [← b.sum_repr t]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul ℚ_[l]]
    rfl
  have hsp : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
    intro x _
    obtain ⟨y, hy, hx⟩ := hS x
    have hy' : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := by
      simpa using hy
    have h1 : y • x ∈ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
      have := hsum ⟨_, hx⟩
      change y • x = _ at this
      rw [this]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← algebraMap_smul ℚ_[l]] at h1
    exact (Submodule.smul_mem_iff _ hy').1 h1
  let w := Module.Basis.mk hli' hsp
  have hw : ∀ i, w i = (b i : V) := fun i => Module.Basis.mk_apply _ _ i
  refine ⟨_, w, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have := hsum ⟨x, hx⟩
    change x = _ at this
    simp only [← hw] at this
    have h2 : w.repr x i = ((b.repr ⟨x, hx⟩ i : ℤ_[l]) : ℚ_[l]) := by
      conv_lhs => rw [this]
      exact congrFun (w.repr_sum_self _) i
    rw [h2]
    exact PadicInt.norm_le_one _
  · rw [← w.sum_repr x]
    refine S.sum_mem fun i _ => ?_
    obtain ⟨z, h3⟩ : ∃ z : ℤ_[l], w.repr x i = algebraMap ℤ_[l] ℚ_[l] z := ⟨⟨_, hx i⟩, rfl⟩
    rw [h3, algebraMap_smul, hw]
    exact S.smul_mem _ (b i).2

theorem continuous_coord {L V : Type} [Field L] [Algebra ℚ_[l] L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] (hc : Continuous (algebraMap ℚ_[l] L))
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] [TopologicalSpace V]
    [IsModuleTopology L V] [FiniteDimensional L V] {n : ℕ} (w : Module.Basis (Fin n) ℚ_[l] V) :
    Continuous w.equivFun ∧ Continuous w.equivFun.symm := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup L V
  haveI : ContinuousSMul L V := IsModuleTopology.toContinuousSMul L V
  haveI : T2Space V := by
    let c := Module.finBasis L V
    have h1 : Continuous c.equivFun :=
      IsModuleTopology.continuous_of_linearMap c.equivFun.toLinearMap
    exact T2Space.of_injective_continuous c.equivFun.injective h1
  haveI : ContinuousSMul ℚ_[l] V := ⟨by
    have h : (fun p : ℚ_[l] × V => p.1 • p.2) = fun p => algebraMap ℚ_[l] L p.1 • p.2 := by
      funext p; rw [algebraMap_smul]
    rw [h]
    exact (hc.comp continuous_fst).smul continuous_snd⟩
  exact ⟨w.equivFunL.continuous, w.equivFunL.symm.continuous⟩

theorem exists_basis_lattice {L O V : Type} [Field L] [Algebra ℚ_[l] L] [CommRing O] [Algebra O L]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hcomp : ∀ a : ℤ_[l], algebraMap O L (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] L (a : ℚ_[l]))
    (hL : ∀ a : L, ∃ y : ℤ_[l], y ≠ 0 ∧ ∃ o : O, algebraMap O L o = algebraMap ℚ_[l] L y * a)
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] [Module O V]
    [IsScalarTower O L V] (S : Submodule O V) (hfg : S.FG) (hfree : Module.Free O S)
    (hspan : Submodule.span L (S : Set V) = ⊤) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ x : V, x ∈ S ↔ ∀ i, ‖w.repr x i‖ ≤ 1 := by
  first
  | (rename_i h_1 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15 h_16 h_17 h_18 h_19; revert l h_1 L O V h_5 h_6 h_7 h_8 h_9 h_10 h_11 hcomp hL h_14 h_15 h_16 h_17 h_18 h_19 S hfg hfree hspan; exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one)
  | exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
  | exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
  | (apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one ..)

theorem exists_mul_mem (LL : FinExt l) (a : ↥LL.1) :
    ∃ y : ℤ_[l], y ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℚ_[l] ↥LL.1 y * a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y, hy, ⟨_, hi⟩, ?_⟩
  change y • a = _
  rw [Algebra.smul_def]
  rfl

theorem continuous_algebraMap_ext (LL : FinExt l) : Continuous (algebraMap ℚ_[l] ↥LL.1) :=
  continuous_induced_rng.2 (continuous_algebraMap ℚ_[l] (Om l))



theorem exists_basis (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G]
    (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] T.V),
      (∀ x : T.V, x ∈ T.L.T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) ∧
        Continuous w.equivFun ∧ Continuous w.equivFun.symm := by
  haveI := Decomp.freeOL LL
  haveI := Decomp.finiteOL LL
  obtain ⟨n, w, hw⟩ := exists_basis_lattice (l := l) (L := ↥LL.1) (O := ↥(OL LL)) (fun _ => rfl)
    (exists_mul_mem LL) T.L.T T.L.fg T.L.free T.L.span
  exact ⟨n, w, hw, continuous_coord (continuous_algebraMap_ext LL) w⟩

end GlobalTheory.Cyc.LatBasis
end
end

section

namespace GlobalTheory.TiltComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

section General

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

theorem coeff_sum_stable (t : Perfection R p) (a : ℕ → Perfection R p) (n M N : ℕ)
    (hM : Perfection.coeff R p n t ^ M = 0) (h : M ≤ N) :
    Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) =
      Perfection.coeff R p n (∑ i ∈ Finset.range M, t ^ i * a i) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih =>
    rw [Finset.sum_range_succ, map_add (f := _), ih, map_mul, map_pow, pow_eq_zero_of_le h hM, zero_mul,
      add_zero]

theorem exists_limit (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) (a : ℕ → Perfection R p) :
    ∃ x : Perfection R p, ∀ n N, M n ≤ N →
      Perfection.coeff R p n x = Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) := by
  refine ⟨⟨fun n => Perfection.coeff R p n (∑ i ∈ Finset.range (M n), t ^ i * a i), fun n => ?_⟩,
    fun n N h => ?_⟩
  · beta_reduce
    rw [← coeff_sum_stable t a (n + 1) _ _ (hM _) (le_max_left (M (n + 1)) (M n)),
      ← coeff_sum_stable t a n _ _ (hM _) (le_max_right (M (n + 1)) (M n)),
      Perfection.coeff_pow_p']
  · rw [Perfection.coeff_mk, coeff_sum_stable t a n _ _ (hM _) h]

theorem separated_complete (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) :
    (∀ x : Perfection R p, (∀ m : ℕ, t ^ m ∣ x) → x = 0) ∧
      ∀ a : ℕ → Perfection R p, ∃ x : Perfection R p, ∀ m : ℕ,
        t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i := by
  refine ⟨fun x hx => Perfection.ext fun n => ?_, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hx (M n)
    rw [map_mul, map_pow, hM, zero_mul, map_zero]
  · obtain ⟨x, hx⟩ := exists_limit t M hM a
    refine ⟨x, fun m => ?_⟩
    obtain ⟨y, hy⟩ := exists_limit t M hM fun i => a (m + i)
    refine ⟨y, Perfection.ext fun n => ?_⟩
    rw [map_sub, map_mul, hx n (m + M n) (Nat.le_add_left _ _), hy n (M n) le_rfl, ← map_mul,
      ← map_sub, Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_assoc]

end General

theorem tilt_separated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), (∀ x : OCb l, (∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x) → x = 0) ∧ ∀ a : ℕ → OCb l, ∃ x : OCb l, ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x - ∑ i ∈ Finset.range m, (AI.εroot s - 1) ^ i * a i := by
  intro l _ P AI s
  refine separated_complete (R := ModP (OC l) l) (p := l) (AI.εroot s - 1 : OCb l)
    (fun n => l ^ (s + n)) fun n => ?_
  change PreTilt.coeff n (AI.εroot s - 1) ^ l ^ (s + n) = 0
  have h := ζ_add_pow AI 0 (s + n)
  rw [zero_add, AI.ζ_zero] at h
  rw [map_sub, map_one, sub_pow_char_pow, coeff_εroot, ← map_pow, h, map_one, one_pow, sub_self]

end GlobalTheory.TiltComplete
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Conv

section General

variable {A : Type*} [CommRing A]

theorem step_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A} (hc : c ∈ I) (n : ℕ)
    {y : A} (hy : y ∈ I ^ n) : c * φ y ∈ I ^ (n + 1) := by
  rw [pow_succ']
  refine Ideal.mul_mem_mul hc ?_
  have h : φ y ∈ (I ^ n).map φ := Ideal.mem_map_of_mem φ hy
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono hφ n h

theorem solve (I : Ideal A) [hI : IsAdicComplete I A] (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A}
    (hc : c ∈ I) (q : A) : ∃ y, y - c * φ y = q := by
  let f : ℕ → A := fun n => (fun z => q + c * φ z)^[n] 0
  have hf : ∀ n, f (n + 1) = q + c * φ (f n) := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n, f n - f (n + 1) ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := step_mem I φ hφ hc n ih
      rw [hf (n + 1)]
      nth_rewrite 1 [hf n]
      convert this using 1
      rw [map_sub]; ring
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right hmn (h1 n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' f (by
    intro m n hmn
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact h2 m n hmn)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hL
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine hI.toIsHausdorff.haus' _ fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have := sub_mem (step_mem I φ hφ hc n (hL n)) (hL (n + 1))
  convert this using 1
  rw [hf, map_sub]; ring

theorem geom_mem (p : ℕ) (e : A) :
    ∑ i ∈ Finset.range p, e ^ i ∈ Ideal.span {(p : A), e - 1} := by
  have h : ∑ i ∈ Finset.range p, e ^ i = (p : A) + ∑ i ∈ Finset.range p, (e ^ i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h]
  refine add_mem (Ideal.subset_span (by simp)) (Ideal.sum_mem _ fun i _ => ?_)
  obtain ⟨d, hd⟩ : e - 1 ∣ e ^ i - 1 := by simpa using sub_dvd_pow_sub_pow e 1 i
  rw [hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem map_le (p : ℕ) (φ : A →+* A) {m c : A} (h : φ m = c * m) :
    (Ideal.span {(p : A), m}).map φ ≤ Ideal.span {(p : A), m} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨x, rfl | rfl, rfl⟩
  · rw [map_natCast]; exact Ideal.subset_span (by simp)
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem iterate_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {m c : A} (hc : c ∈ I)
    (h : φ m = c * m) (k : ℕ) : ∃ d ∈ I ^ k, φ^[k] m = d * m := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, e⟩ := ih
    refine ⟨c * φ d, step_mem I φ hφ hc k hd, ?_⟩
    rw [Function.iterate_succ_apply', e, map_mul, h]; ring

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_mu : WittVector.frobenius AI.μ =
    (∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i) * AI.μ := by
  have h : WittVector.frobenius (WittVector.teichmuller l AI.ε) =
      WittVector.teichmuller l AI.ε ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [LocAinf.μ, map_sub, map_one, h, geom_sum_mul]

theorem mu_not_isUnit : ¬ IsUnit AI.μ := by
  intro h
  obtain ⟨θ, hθ⟩ := exists_isTheta l P AI
  have h0 : θ AI.μ = 0 := (hθ.2.2.2.1 _).2 ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := h.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  intro l _ P AI
  have hc : ∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i ∈
      Ideal.span {((l : ℕ) : Ainf l), AI.μ} := geom_mem l _
  have hφ := map_le l _ (frob_mu AI)
  refine ⟨fun q => ?_, fun M n => ⟨n + M, fun k hk => ?_⟩⟩
  · haveI := (GlobalTheory.Per.AinfComplete.main l AI.μ (mu_not_isUnit AI)).1
    obtain ⟨y, hy⟩ := solve _ _ hφ hc q
    refine ⟨y, ?_⟩
    rw [map_mul, frob_mu, ← hy]; ring
  · obtain ⟨d, hd, e⟩ := iterate_mem _ _ hφ hc (frob_mu AI) k
    rw [e]
    refine Ideal.mul_mem_right _ _ ?_
    have h1 : Ideal.span {((l : ℕ) : Ainf l), AI.μ} ≤ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [AI.μ_eq]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have h2 := Ideal.pow_le_pow_right hk (Ideal.pow_right_mono h1 k hd)
    rw [Ideal.span_insert] at h2
    rw [Ideal.span_insert, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.sup_pow_add_le_pow_sup_pow h2

end GlobalTheory.ExpImage.Conv
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.LocalIntegers.goodO_integers | exact GlobalTheory.LocalIntegers.goodO_integers | (intros; apply GlobalTheory.LocalIntegers.goodO_integers <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem sqrt_neg_l_not_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  intro l _ y hy hK
  have hl1 : (1 : ℝ) < (l : ℝ) := Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hy, norm_neg]
    exact Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hn
    have : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hl0.ne'
    exact this (by rw [← hn]; norm_num)
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hK hy0
  rw [hk, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one] at hn
  have h := zpow_right_injective₀ hl0 hl1.ne' hn
  omega

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.completion_comparison_admissible_every_place_over : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i := by
  first | exact @GlobalTheory.BridgeTie.localCoefficientCompatibility | exact GlobalTheory.BridgeTie.localCoefficientCompatibility | (intros; apply GlobalTheory.BridgeTie.localCoefficientCompatibility <;> assumption)
end
