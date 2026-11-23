module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle134
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle139
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle137
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.TorsCoc

theorem exists_pow_smul_mem {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O LL] [IsFractionRing O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (hT : Submodule.span LL (T : Set V) = ⊤) (ϖ : O) (hϖ : Irreducible ϖ)
    (v : V) : ∃ k : ℕ, ∀ j, k ≤ j → (algebraMap O LL ϖ) ^ j • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := hT ▸ Submodule.mem_top

  have up : ∀ (x : V) (k j : ℕ), k ≤ j → (algebraMap O LL ϖ) ^ k • x ∈ T →
      (algebraMap O LL ϖ) ^ j • x ∈ T := by
    intro x k j hkj hx
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    rw [pow_add, mul_comm, mul_smul, ← map_pow, algebraMap_smul]
    exact T.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, fun j _ => by rw [← map_pow, algebraMap_smul]; exact T.smul_mem _ hx⟩
  | zero => exact ⟨0, fun j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun j hj => by
      rw [smul_add]
      exact T.add_mem (ha j (le_trans (le_max_left _ _) hj)) (hb j (le_trans (le_max_right _ _) hj))⟩
  | smul a x _ hx =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) a
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
    refine ⟨n + k, fun j hj => up _ (n + k) j hj ?_⟩
    have key : (algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s) =
        algebraMap O LL (b * ((u⁻¹ : Oˣ) : O)) := by
      have hsne : algebraMap O LL s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [mul_div_assoc', div_eq_iff hsne, hu]
      simp only [map_mul, map_pow]
      have hu1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(algebraMap O LL b * algebraMap O LL ϖ ^ n)) * hu1
    have e : (algebraMap O LL ϖ) ^ (n + k) • ((algebraMap O LL b / algebraMap O LL s) • x) =
        ((algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s)) •
          ((algebraMap O LL ϖ) ^ k • x) := by
      rw [pow_add, mul_smul, mul_smul, smul_comm (algebraMap O LL b / algebraMap O LL s)]
    rw [e, key, algebraMap_smul]
    exact T.smul_mem _ (hk k le_rfl)

theorem cocycle_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ)
    (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', ∃ r : ℕ, ∀ g,
    (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T := by
  intro l _ K LL _ _ _ O _ _ hO A' LA' ϖ hϖ c hc
  obtain ⟨⟨hD, hDVR, hFR⟩, -⟩ := hO
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  have hfin : (Set.range c).Finite := hc.1.range_finite
  choose f hf using fun y : A'.V ⧸ LA'.T =>
    exists_pow_smul_mem LA'.T LA'.span ϖ hϖ (liftD LA' y)
  refine ⟨hfin.toFinset.sup f, fun g => hf (c g) _ ?_⟩
  exact Finset.le_sup (f := f) (hfin.mem_toFinset.2 ⟨g, rfl⟩)

end GlobalTheory.TorsCoc
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLat

variable {LL O V W : Type} [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W] [FiniteDimensional LL W]

theorem exists_dual (m : V →ₗ[LL] W →ₗ[LL] LL)
    (h3 : ∀ y : W, (∀ x : V, m x y = 0) → y = 0)
    (h4 : finrank LL V = finrank LL W)
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) :
    ∃ T' : Submodule O W, T'.FG ∧ Module.Free O T' ∧ Submodule.span LL (T' : Set W) = ⊤ ∧
      (∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ a, m x y = algebraMap O LL a) ∧
      (∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ a, m x y = algebraMap O LL a) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let b := Module.Free.chooseBasis O T
  let bV0 : Module.Free.ChooseBasisIndex O T → V := fun i => (b i : V)
  have hTspan : Submodule.span O (Set.range bV0) = T := by
    rw [show bV0 = T.subtype ∘ b from rfl, Set.range_comp, Submodule.span_image, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hliO : LinearIndependent O bV0 := b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hliL : LinearIndependent LL bV0 := (LinearIndependent.iff_fractionRing O LL).mp hliO
  have hspL : ⊤ ≤ Submodule.span LL (Set.range bV0) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← hTspan] at hx
    exact Submodule.span_le_restrictScalars O LL _ hx
  let bV := Basis.mk hliL hspL
  have hbV : ∀ i, bV i = bV0 i := fun i => Basis.mk_apply hliL hspL i
  let φ : W →ₗ[LL] Module.Dual LL V := m.flip
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact h3 y (fun x => by simpa [φ] using LinearMap.congr_fun hy x)
  have hdim : finrank LL W = finrank LL (Module.Dual LL V) := by
    rw [Subspace.dual_finrank_eq, h4]
  let e : W ≃ₗ[LL] Module.Dual LL V := LinearMap.linearEquivOfInjective φ hφ hdim
  let f' := bV.dualBasis.map e.symm
  have key1 : ∀ x j, m x (f' j) = bV.repr x j := by
    intro x j
    have h : φ (f' j) = bV.dualBasis j := by
      show e (e.symm (bV.dualBasis j)) = bV.dualBasis j
      exact e.apply_symm_apply _
    calc m x (f' j) = φ (f' j) x := rfl
      _ = bV.dualBasis j x := by rw [h]
      _ = bV.repr x j := Basis.dualBasis_apply _ _ _
  have key2 : ∀ i y, m (bV i) y = f'.repr y i := by
    intro i y
    have : m (bV i) = f'.coord i := f'.ext (fun j => by
      rw [key1, Basis.coord_apply, Basis.repr_self, Basis.repr_self, Finsupp.single_apply,
        Finsupp.single_apply]
      simp only [eq_comm])
    rw [this, Basis.coord_apply]
  haveI : IsTorsionFree O LL := inferInstance
  refine ⟨Submodule.span O (Set.range f'), Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_, ?_⟩
  · exact Module.Free.of_basis (Basis.span ((LinearIndependent.iff_fractionRing O LL).mpr f'.linearIndependent))
  · rw [Submodule.span_span_of_tower, f'.span_eq]
  · intro y
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hy x hx
      rw [← hTspan] at hx
      have hle : Submodule.span O (Set.range bV0) ≤
          Submodule.comap ((m.flip y).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        obtain ⟨a, ha⟩ := hy i
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key2, hbV]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hx)
      exact ⟨a, ha.symm⟩
    · intro hy i
      obtain ⟨a, ha⟩ := hy (bV i) (by rw [hbV, ← hTspan]; exact Submodule.subset_span ⟨i, rfl⟩)
      exact ⟨a, by rw [← key2, ha]⟩
  · intro x
    have hTeq : T = Submodule.span O (Set.range bV) := by
      rw [show (bV : _ → V) = bV0 from funext hbV, hTspan]
    refine (SetLike.ext_iff.mp hTeq x).trans ?_
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hx y hy
      have hle : Submodule.span O (Set.range f') ≤
          Submodule.comap ((m x).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        obtain ⟨a, ha⟩ := hx j
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key1]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hy)
      exact ⟨a, ha.symm⟩
    · intro hx j
      obtain ⟨a, ha⟩ := hx (f' j) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨a, by rw [← key1, ha]⟩

end GlobalTheory.DualLat

namespace GlobalTheory.DualLat

theorem dualLattice_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (LA : Lattice (O := O) A.ρ), IsDual1 (P.PD K) A.ρ A'.ρ m → (∀ g, ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a) → ∃ LA' : Lattice (O := O) A'.ρ, IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m LA hD hc
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hO
  obtain ⟨h1, h2, h3, h4⟩ := hD
  obtain ⟨T', hfg, hfree, hspan, hmem1, hmem2⟩ := exists_dual (O := O) m h3 h4 LA.T LA.fg LA.free LA.span
  have hstab : ∀ g, ∀ y ∈ T', (A'.ρ g) y ∈ T' := by
    intro g y hy
    rw [hmem1] at hy ⊢
    intro x hx
    obtain ⟨c, hcg⟩ := hc g
    obtain ⟨a, ha⟩ := hy (A.ρ g⁻¹ x) (LA.stable g⁻¹ x hx)
    refine ⟨c * a, ?_⟩
    have hx' : x = A.ρ g (A.ρ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx', h1, ha, hcg, map_mul]
  let LA' : WeaklyAdmissibleFiltrations.Lattice (O := O) A'.ρ :=
    { T := T', stable := hstab, fg := hfg, free := hfree, span := hspan }
  refine ⟨LA', ⟨⟨h1, h2, h3, h4⟩, hmem1⟩, ⟨⟨?_, ?_, ?_, h4.symm⟩, ?_⟩⟩
  · intro g y x
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  · intro y hy
    exact h3 y (fun x => by simpa only [LinearMap.flip_apply] using hy x)
  · intro x hx
    exact h2 x (fun y => by simpa only [LinearMap.flip_apply] using hx y)
  · intro y
    simpa only [LinearMap.flip_apply] using hmem2 y

end GlobalTheory.DualLat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem span_cocycles_ext {G F E : Type} [Group G] [TopologicalSpace G] [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] [Field E] [Algebra F E] [TopologicalSpace E]
    [FiniteDimensional F E] [IsModuleTopology F E] [IsTopologicalRing E] (χ : G → F)
    (H : ∃ z0 : G × G → F, (Continuous z0 ∧ ∀ g h k,
        χ g * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → F, Continuous z →
        (∀ g h k, χ g * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : F, ∃ f : G → F, Continuous f ∧
          ∀ g h, χ g * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h)) :
    ∃ z0 : G × G → E, (Continuous z0 ∧ ∀ g h k,
        algebraMap F E (χ g) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → E, Continuous z →
        (∀ g h k, algebraMap F E (χ g) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : E, ∃ f : G → E, Continuous f ∧
          ∀ g h, algebraMap F E (χ g) * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h) := by
  obtain ⟨z0, ⟨hc0, hz0⟩, H⟩ := H
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  have hA : Continuous (algebraMap F E) := by
    have : (algebraMap F E : F → E) = fun a => a • (1 : E) := by
      funext a; rw [Algebra.algebraMap_eq_smul_one]
    rw [this]; fun_prop
  refine ⟨fun p => algebraMap F E (z0 p), ⟨hA.comp hc0, fun g h k => ?_⟩, fun z hc hz => ?_⟩
  · have := congrArg (algebraMap F E) (hz0 g h k)
    simpa using this
  · let b := Module.finBasis F E
    have hb : ∀ i, Continuous (b.coord i) := fun i =>
      IsModuleTopology.continuous_of_linearMap (b.coord i)
    have key : ∀ i, ∃ x : F, ∃ f : G → F, Continuous f ∧
        ∀ g h, χ g * f h - f (g * h) + f g = b.coord i (z (g, h)) - x * z0 (g, h) := by
      intro i
      refine H (fun p => b.coord i (z p)) ((hb i).comp hc) (fun g h k => ?_)
      have := congrArg (b.coord i) (hz g h k)
      rw [← Algebra.smul_def, map_sub, map_add (f := _), map_sub, map_smul, map_zero, smul_eq_mul] at this
      exact this
    choose x f hf hxf using key
    refine ⟨∑ i, x i • b i, fun g => ∑ i, f i g • b i, ?_, fun g h => ?_⟩
    · exact continuous_finsetSum _ (fun i _ => (hf i).smul continuous_const)
    · have hs : z (g, h) = ∑ i, b.coord i (z (g, h)) • b i := by
        simp [b.sum_repr]
      rw [hs, ← Algebra.smul_def, mul_comm, ← Algebra.smul_def, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, smul_smul, ← sub_smul, ← add_smul, ← sub_smul, hxf i g h, mul_comm (x i)]

theorem span_cocycles_cyc_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  intro l _ P K LL _ _ _ O _ _ hO H
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  obtain ⟨z0, hz0, H⟩ := H
  have := span_cocycles_ext (F := ℚ_[l]) (E := LL)
    (fun g : ↥(GK K) => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) ⟨z0, hz0, fun z hc hz => by
      obtain ⟨x, f, hf, hd⟩ := H z hc hz
      refine ⟨x, f, hf, fun g h => ?_⟩
      have := congrFun hd (g, h)
      simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using this⟩
  have e : ∀ g : ↥(GK K), algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])
      = ((cycLL (P.PD K) LL g : LLˣ) : LL) := fun g => by simp [cycLL]
  simp only [e] at this
  obtain ⟨w0, hw0, H'⟩ := this
  refine ⟨w0, hw0, fun z hc hz => ?_⟩
  obtain ⟨x, f, hf, hd⟩ := H' z hc hz
  refine ⟨x, f, hf, ?_⟩
  funext ⟨g, h⟩
  simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using hd g h

end GlobalTheory
end

section

open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem hasSum_inner_quotient_eulerProduct_injective : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) [DecidableEq ι] (c : ι → Γ →* Γ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (s : ι → ℝ) (e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}), (∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) → (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ g, a g = ∏ᶠ v, a (c v g)) → (∀ g, ‖B g‖ ≤ 1) → B 1 = 1 → (∀ g k, k ∈ K → B (g * k) = B g) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset Γ), (∀ g ∈ C, c v g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ s v) → (∀ v γ, HasSum (fun x : Γ ⧸ K.comap (c v) => a (c v (Quotient.out x)) • B (γ * c v (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap (c v), a (c v (Quotient.out x)) • B (c v (Quotient.out x)))) → ∃ W : H →L[ℂ] H, Function.Injective W ∧ ∀ x y, HasSum (fun q : Γ ⧸ K => a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ) ⟪x, W y⟫_ℂ := by
  intro Γ _ K ι _ c H _ _ _ a B s e he hK hidem horth haK ha1 hfac hB hB1 hBK hs hs1 hloc hstep
  classical
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H

  have aK : ∀ g : Γ, a ((QuotientGroup.mk g : Γ ⧸ K).out) = a g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk]; exact haK g k k.2
  have BK : ∀ g : Γ, B ((QuotientGroup.mk g : Γ ⧸ K).out) = B g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk]; exact hBK g k k.2
  have acv : ∀ v (g : Γ), a (c v ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)).out)) = a (c v g) := by
    intro v g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.comap (c v)) g
    rw [hk, map_mul]; exact haK _ _ k.2
  have cv1 : ∀ v, c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out) ∈ K := by
    intro v
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.comap (c v)) (1 : Γ)
    rw [hk, one_mul]; exact k.2
  let x0 : ∀ v, Γ ⧸ K.comap (c v) := fun v => QuotientGroup.mk 1
  let a' : ∀ v, Γ ⧸ K.comap (c v) → ℂ := fun v x => a (c v x.out)
  let Z : ι → (H →L[ℂ] H) := fun v => ∑' x : Γ ⧸ K.comap (c v), a (c v x.out) • B (c v x.out)
  let B' : (∀ v, Γ ⧸ K.comap (c v)) → (H →L[ℂ] H) := fun f =>
    if h : {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite then B ((e.symm ⟨f, h⟩).out) else B 1
  have B'eval : ∀ (f : ∀ v, Γ ⧸ K.comap (c v)) (g : Γ),
      (∀ w, f w = (QuotientGroup.mk g : Γ ⧸ K.comap (c w))) → B' f = B g := by
    intro f g hf
    have hfeq : f = (e (QuotientGroup.mk g)).1 := funext fun w => (hf w).trans (he g w).symm
    subst hfeq
    simp only [B', dif_pos (e (QuotientGroup.mk g)).2, Subtype.coe_eta, Equiv.symm_apply_apply]
    exact BK g
  have h1 : ∀ v, a' v (x0 v) = 1 := by
    intro v
    show a (c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out)) = 1
    rw [acv, map_one, ha1]
  have hfin : ∀ v (C : Finset (Γ ⧸ K.comap (c v))), x0 v ∉ C → ∑ x ∈ C, ‖a' v x‖ ≤ s v := by
    intro v C hC
    have eqcl : ∀ x y : Γ ⧸ K.comap (c v), (c v x.out)⁻¹ * c v y.out ∈ K → x = y := by
      intro x y hxy
      have hm : x.out⁻¹ * y.out ∈ K.comap (c v) := by
        rw [Subgroup.mem_comap, map_mul, map_inv]; exact hxy
      have := (QuotientGroup.eq (s := K.comap (c v))).mpr hm
      simpa only [QuotientGroup.out_eq'] using this
    calc ∑ x ∈ C, ‖a' v x‖ = ∑ g ∈ C.image (fun x => c v x.out), ‖a g‖ := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          apply eqcl
          have hxy' : c v x.out = c v y.out := hxy
          rw [hxy', inv_mul_cancel]; exact K.one_mem
      _ ≤ s v := by
          apply hloc
          · intro g hg
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
            refine ⟨hidem v _, fun hmem => hC ?_⟩
            have : x = x0 v := by
              apply eqcl
              exact K.mul_mem (K.inv_mem hmem) (cv1 v)
            rw [← this]; exact hx
          · intro g hg g' hg' hgg
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
            rw [eqcl x y hgg]
  have hnorm : ∀ f, ‖B' f‖ ≤ 1 := by
    intro f
    simp only [B']
    split_ifs
    · exact hB _
    · exact hB 1
  have hx0 : B' x0 = 1 := by
    rw [B'eval x0 1 (fun w => rfl), hB1]
  have hrec : ∀ v (f : ∀ v, Γ ⧸ K.comap (c v)), {w | f w ≠ x0 w}.Finite → f v = x0 v →
      HasSum (fun x => a' v x • B' (Function.update f v x)) (B' f * Z v) := by
    intro v f hf hv
    set γ' : Γ := (e.symm ⟨f, hf⟩).out with hγ'
    have hfγ' : ∀ w, f w = (QuotientGroup.mk γ' : Γ ⧸ K.comap (c w)) := by
      intro w
      have h2 : e (QuotientGroup.mk γ') = ⟨f, hf⟩ := by
        rw [hγ', QuotientGroup.out_eq', Equiv.apply_symm_apply]
      have h3 := congrArg (fun p => p.1 w) h2
      simp only at h3
      rw [← h3, he]
    set γ : Γ := γ' * (c v γ')⁻¹ with hγ
    have hcγ : c v γ = 1 := by
      rw [hγ, map_mul, map_inv, hidem, mul_inv_cancel]
    have key : ∀ x : Γ ⧸ K.comap (c v), B' (Function.update f v x) = B (γ * c v x.out) := by
      intro x
      apply B'eval
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [Function.update_self]
        refine ((QuotientGroup.eq (s := K.comap (c w))).mpr ?_).trans (QuotientGroup.out_eq' x) |>.symm
        rw [Subgroup.mem_comap]
        simp only [mul_inv_rev, map_mul, map_inv, hidem, hcγ, inv_one, mul_one, inv_mul_cancel]
        exact K.one_mem
      · rw [Function.update_of_ne hw, hfγ' w, QuotientGroup.eq, Subgroup.mem_comap]
        simp only [hγ, mul_inv_rev, inv_inv, map_mul, map_inv, horth v w _ hw.symm, inv_one, mul_one,
          one_mul, inv_mul_cancel]
        exact K.one_mem
    have hupd : Function.update f v (x0 v) = f := by
      rw [← hv]; exact Function.update_eq_self v f
    have hBf : B' f = B γ := by
      rw [← hupd, key, hBK _ _ (cv1 v)]
    rw [hBf]
    have := hstep v γ
    convert this using 1
    funext x
    rw [key]
  obtain ⟨W, hW, hinj, -⟩ := GlobalTheory.T.eulerOperator_injective_eigenvector ι (fun v => Γ ⧸ K.comap (c v)) x0 H a' s B' Z h1 hs hs1 hfin
    hnorm hx0 hrec
  refine ⟨W, hinj, fun x y => ?_⟩
  have hW' := (Equiv.hasSum_iff e).mpr hW
  have hfun : ((fun f : {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ x0 w}.Finite} =>
      (∏ᶠ v, a' v (f.1 v)) • B' f.1) ∘ e) = fun q => a q.out • B q.out := by
    funext q
    have hq : ∀ v, (e q).1 v = (QuotientGroup.mk q.out : Γ ⧸ K.comap (c v)) := by
      intro v
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      exact he _ v
    simp only [Function.comp]
    rw [B'eval _ q.out hq]
    congr 1
    rw [hfac q.out]
    exact finprod_congr fun v => by simp only [a']; rw [hq v]; exact acv v q.out
  rw [hfun] at hW'
  have := hW'.mapL ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y))
  simpa [inner_smul_right] using this

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.integralClosure_fg_finiteEtale_dvr : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A], (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntegralClosureFG.integralClosure_fg | exact GlobalTheory.IntegralClosureFG.integralClosure_fg | (intros; apply GlobalTheory.IntegralClosureFG.integralClosure_fg <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem _root_.GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L], {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  first | exact @GlobalTheory.InertiaAlmostAll.finite_ramified | exact GlobalTheory.InertiaAlmostAll.finite_ramified | (intros; apply GlobalTheory.InertiaAlmostAll.finite_ramified <;> assumption)
end
