module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle001
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle002

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open ReciprocityTheory.Coh CategoryTheory

noncomputable section

universe u

variable {R : Type u} [CommRing R]

section Discrete

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

def pairRepHom {M : TRep R G} {M' : TRep R G'} (P : Pair M M') :
    Rep.res P.φ (Rep.of M.rho) ⟶ Rep.of M'.rho :=
  Rep.ofHom ⟨P.u, fun g => LinearMap.ext fun m => P.equiv g m⟩

open groupCohomology

def zIncl (M : TRep R G) (n : ℕ) : M.coch.Z n →ₗ[R] ((Fin n → G) → M.V) where
  toFun z := z.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zIncl_d (M : TRep R G) (n : ℕ) :
    ModuleCat.ofHom (zIncl M n) ≫ (inhomogeneousCochains (Rep.of M.rho)).d n (n + 1) = 0 := by
  rw [inhomogeneousCochains.d_def]
  ext z g
  exact congrFun (congrArg Subtype.val z.2) g

def toCyc (M : TRep R G) (n : ℕ) : ModuleCat.of R (M.coch.Z n) ⟶ cocycles (Rep.of M.rho) n :=
  (inhomogeneousCochains (Rep.of M.rho)).liftCycles (ModuleCat.ofHom (zIncl M n)) (n + 1) (by simp)
    (zIncl_d M n)

theorem i_toCyc (M : TRep R G) (n : ℕ) (z : M.coch.Z n) :
    iCocycles (Rep.of M.rho) n (toCyc M n z) = z.1.1 :=
  congrArg (fun φ => φ.hom z)
    ((inhomogeneousCochains (Rep.of M.rho)).liftCycles_i (ModuleCat.ofHom (zIncl M n)) (n + 1) (by simp)
      (zIncl_d M n))

theorem iCocycles_injective (A : Rep R G) (n : ℕ) : Function.Injective (iCocycles A n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem d_iCocycles (A : Rep R G) (n : ℕ) (c : cocycles A n) :
    inhomogeneousCochains.d A n (iCocycles A n c) = 0 := by
  have h := (inhomogeneousCochains A).iCycles_d n (n + 1)
  rw [inhomogeneousCochains.d_def] at h
  exact congrArg (fun φ => φ.hom c) h

theorem π_eq_zero_iff (A : Rep R G) (i n : ℕ) (hi : (ComplexShape.up ℕ).prev n = i) (c : cocycles A n) :
    π A n c = 0 ↔ ∃ y, toCocycles A i n y = c := by
  have ex : (ShortComplex.mk (toCocycles A i n) (π A n)
      ((inhomogeneousCochains A).toCycles_comp_homologyπ i n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ ((inhomogeneousCochains A).homologyIsCokernel i n hi)
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).1 ex c
  · rintro ⟨y, rfl⟩
    exact congrArg (fun φ => φ.hom y) ((inhomogeneousCochains A).toCycles_comp_homologyπ i n)

theorem i_toCocycles (A : Rep R G) (i n : ℕ) (y) :
    iCocycles A n (toCocycles A i n y) = (inhomogeneousCochains A).d i n y :=
  congrArg (fun φ => φ.hom y) ((inhomogeneousCochains A).toCycles_i i n)

variable [DiscreteTopology G] [DiscreteTopology G']

theorem toCyc_surjective (M : TRep R G) (n : ℕ) : Function.Surjective (toCyc M n) := by
  intro c
  refine ⟨⟨⟨iCocycles _ n c, continuous_of_discreteTopology⟩, Subtype.ext (d_iCocycles _ n c)⟩, ?_⟩
  exact iCocycles_injective _ n (i_toCyc M n _)

def toH (M : TRep R G) (n : ℕ) : M.coch.Z n →ₗ[R] groupCohomology (Rep.of M.rho) n :=
  (toCyc M n ≫ π (Rep.of M.rho) n).hom

theorem toH_surjective (M : TRep R G) (n : ℕ) : Function.Surjective (toH M n) := by
  intro x
  induction x using groupCohomology_induction_on with
  | h c =>
    obtain ⟨z, rfl⟩ := toCyc_surjective M n c
    exact ⟨z, rfl⟩

theorem ker_toH (M : TRep R G) (n : ℕ) :
    (M.coch.B n).comap (M.coch.Z n).subtype = LinearMap.ker (toH M n) := by
  ext z
  rw [LinearMap.mem_ker]
  show z.1 ∈ M.coch.B n ↔ π _ n (toCyc M n z) = 0
  cases n with
  | zero =>
    rw [π_eq_zero_iff _ 0 0 (by simp)]
    constructor
    · intro hz
      have hz' : z.1 = 0 := hz
      have : z = 0 := Subtype.ext hz'
      subst this
      exact ⟨0, by simp⟩
    · rintro ⟨y, hy⟩
      have h := i_toCocycles (Rep.of M.rho) 0 0 y
      rw [hy, i_toCyc, (inhomogeneousCochains (Rep.of M.rho)).shape 0 0 (by simp)] at h
      show z.1 = 0
      exact Subtype.ext h
  | succ n =>
    rw [π_eq_zero_iff _ n (n + 1) (by simp)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y.1, iCocycles_injective _ _ ?_⟩
      rw [i_toCocycles, i_toCyc, inhomogeneousCochains.d_def, ← hy]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨⟨y, continuous_of_discreteTopology⟩, Subtype.ext ?_⟩
      have h := i_toCocycles (Rep.of M.rho) n (n + 1) y
      rw [hy, i_toCyc, inhomogeneousCochains.d_def] at h
      exact h.symm

def finEquiv (M : TRep R G) (n : ℕ) : M.H n ≃ₗ[R] groupCohomology (Rep.of M.rho) n :=
  (Submodule.quotEquivOfEq _ _ (ker_toH M n)).trans ((toH M n).quotKerEquivOfSurjective (toH_surjective M n))

end Discrete

section Cyclic

def kerQuotEquiv {V : Type u} [AddCommGroup V] [Module R V] (p q : V →ₗ[R] V)
    (h : ∀ x, p x ∈ LinearMap.ker q) (W : Submodule R V) (hW : LinearMap.ker q = W) :
    (LinearMap.ker q ⧸ LinearMap.range (p.codRestrict (LinearMap.ker q) h)) ≃ₗ[R]
      (W ⧸ (LinearMap.range p).comap W.subtype) := by
  subst hW
  exact Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)

def scEquiv {V : Type u} [AddCommGroup V] [Module R V] (p q : V →ₗ[R] V)
    (h : ModuleCat.ofHom p ≫ ModuleCat.ofHom q = 0) (W : Submodule R V) (hW : LinearMap.ker q = W) :
    (ShortComplex.mk (ModuleCat.ofHom p) (ModuleCat.ofHom q) h).homology ≃ₗ[R]
      (W ⧸ (LinearMap.range p).comap W.subtype) :=
  (ShortComplex.moduleCatHomologyIso _).toLinearEquiv ≪≫ₗ
    kerQuotEquiv p q (fun x => LinearMap.mem_ker.2
      (congrArg (fun φ : ModuleCat.of R V ⟶ ModuleCat.of R V => φ.hom x) h)) W hW

variable {C : Type u} [CommGroup C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C]
  [DiscreteTopology C]

theorem sub_toLinearMap (M : TRep R C) (g : C) :
    (Rep.applyAsHom (Rep.of M.rho) g - 𝟙 (Rep.of M.rho)).hom.toLinearMap = M.rho g - LinearMap.id := rfl

theorem nonempty_cyclic_even (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (h0 : i ≠ 0)
    (hi : Even i) :
    Nonempty (M.H i ≃ₗ[R] (M.rho.invariants ⧸
      (LinearMap.range M.rho.norm).comap M.rho.invariants.subtype)) := by
  have : NeZero i := ⟨h0⟩
  have hW : LinearMap.ker (M.rho g - LinearMap.id) = M.rho.invariants := by
    ext x
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers M.rho g hg, LinearMap.mem_ker]
    simp [sub_eq_zero]
  rw [← sub_toLinearMap] at hW
  have e := scEquiv _ _ (Rep.FiniteCyclicGroup.normHomCompSub (Rep.of M.rho) g).zero _ hW
  exact ⟨finEquiv M i ≪≫ₗ
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven (Rep.of M.rho) g hg i hi).toLinearEquiv ≪≫ₗ e⟩

theorem nonempty_cyclic_odd (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃ₗ[R] (LinearMap.ker M.rho.norm ⧸
      (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype)) := by
  have e := scEquiv _ _ (Rep.FiniteCyclicGroup.subCompNormHom (Rep.of M.rho) g).zero _ rfl
  exact ⟨finEquiv M i ≪≫ₗ
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd (Rep.of M.rho) g hg i hi).toLinearEquiv ≪≫ₗ e⟩

end Cyclic

section Low

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

end Low

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem rad_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : 0 ≤ ρ * (1 / 2 : ℝ) ^ n := by positivity

theorem filt_ball {A C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hA1 : ∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) (hA : 0 ≤ A)
    (hC1 : ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖)
    (hAρ : A * ρ < 1) (hCρ : C * ρ ≤ 1 / 2) :
    Filt (L ≃ₐ[K] L) (fun n => ball (K := K) (L := L) (ρ * (1 / 2 : ℝ) ^ n) (rad_nonneg hρ n)) (proj1 (K := K) (L := L)) := by
  refine {
    anti := ?_
    mul := ?_
    smul := ?_
    comp := ?_
    sep := ?_
    inv := ?_
    e_mem := ?_
    e_sum := ?_ }
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1) at hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    refine hx.trans ?_
    rw [pow_succ]
    nlinarith [rad_nonneg hρ n]
  · intro n x y hx hy
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L y‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 at hy
    change ‖Phi K L (x * y)‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1)
    rw [pow_zero, mul_one] at hy
    calc ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖ := hC1 x y
      _ ≤ C * (ρ * (1 / 2 : ℝ) ^ n) * ρ := by gcongr
      _ = (C * ρ) * (ρ * (1 / 2 : ℝ) ^ n) := by ring
      _ ≤ (1 / 2) * (ρ * (1 / 2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_right hCρ (rad_nonneg hρ n)
      _ = ρ * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  · intro n g x hx
    exact (norm_Phi_map g x).trans hx
  · intro x hx
    have hx' : ∀ k, ‖Phi K L (x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ k := fun k => by
      exact hx k
    have hsum : Summable fun k => Phi K L (x k) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ρ) hx'
    refine ⟨(Phi K L).symm (∑' k, Phi K L (x k)), fun n => ?_⟩
    change ‖Phi K L ((Phi K L).symm (∑' k, Phi K L (x k)) - ∑ k ∈ range n, x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ n

    rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, map_sum,
    ← hsum.sum_add_tsum_nat_add n, add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (rad_nonneg hρ n) fun k => ?_
    refine (hx' (k + n)).trans ?_
    gcongr ρ * ?_
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left n k)
  · intro x hx
    have hx' : ∀ n, ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n := hx
    have hlim : Filter.Tendsto (fun n : ℕ => ρ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (ρ * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul ρ
    have h0 : ‖Phi K L x‖ ≤ ρ * 0 := ge_of_tendsto' hlim hx'
    rw [mul_zero] at h0
    have := norm_le_zero_iff.1 h0
    simpa using this
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L ((1 + x)⁻¹ - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    have hr : ρ * (1 / 2 : ℝ) ^ n ≤ ρ := by
      have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hxlt : ‖x‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 x).trans ?_) hAρ
      gcongr
      exact hx.trans hr
    have hne : 1 + x ≠ 0 := by
      intro h0
      have : x = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one] at hxlt
      exact lt_irrefl _ hxlt
    set y : L := (1 + x)⁻¹ - 1 with hy
    have hy1 : y = -x + -(x * y) := by
      rw [hy]; field_simp; ring
    have h1 : ‖Phi K L y‖ ≤ max ‖Phi K L x‖ ‖Phi K L (x * y)‖ := by
      conv_lhs => rw [hy1, map_add (f := _), map_neg, map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_neg]
    have h2 : ‖Phi K L (x * y)‖ ≤ (1 / 2) * ‖Phi K L y‖ := by
      refine (hC1 x y).trans ?_
      gcongr
      refine le_trans ?_ hCρ
      gcongr
      exact hx.trans hr
    rcases le_max_iff.1 h1 with h3 | h3
    · exact h3.trans hx
    · have : ‖Phi K L y‖ ≤ 0 := by linarith
      exact this.trans (rad_nonneg hρ n)
  · intro n x hx
    classical
    have hbound : ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1)‖ ≤ ‖Phi K L x‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro τ
      show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
      rw [map_smul, Pi.smul_apply]
      have h : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
        Module.Basis.equivFun_self _ _ _
      rw [h, smul_eq_mul]
      split_ifs
      · rw [mul_one]
        exact norm_le_pi_norm _ _
      · rw [mul_zero, norm_zero]
        exact norm_nonneg _
    exact hbound.trans (by change ‖Phi K L x‖ ≤ _; exact hx)
  · intro x
    calc ∑ σ : L ≃ₐ[K] L, σ • proj1 (K := K) (L := L) (σ⁻¹ • x)
        = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          show σ (Phi K L (σ⁻¹ • x) 1 • IsGalois.normalBasis K L 1) = _
          rw [map_smul]
          congr 1
          have h := Phi_map (σ⁻¹) x (1 : L ≃ₐ[K] L)
          simpa [inv_inv] using h
      _ = x := by
        rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem exists_units_subgroup [IsUltrametricDist L] : ∃ S : Subgroup Lˣ,
    (∀ (σ : L ≃ₐ[K] L) (u v : Lˣ), u ∈ S → (v : L) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖(u : L)‖ = 1) ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ u : Lˣ, ‖(u : L) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : L ≃ₐ[K] L, σ (u : L) = u) → ∃ v ∈ S, ∏ σ : L ≃ₐ[K] L, σ (v : L) = u) ∧
    ∀ σ₀ : L ≃ₐ[K] L, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : L ≃ₐ[K] L, σ (u : L) = 1 →
      ∃ v ∈ S, σ₀ (v : L) = u * v := by
  obtain ⟨A, B, C, hA, hB, hC, hA1, hB1, hC1⟩ := exists_consts (K := K) (L := L)
  set ρ : ℝ := (2 * (C + A + 1))⁻¹ with hρdef
  have hpos : 0 < 2 * (C + A + 1) := by positivity
  have hρ : 0 < ρ := inv_pos.2 hpos
  have hρ1 : ρ * (2 * (C + A + 1)) = 1 := inv_mul_cancel₀ hpos.ne'
  have hAρ : A * ρ < 1 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have hCρ : C * ρ ≤ 1 / 2 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have F := filt_ball hC hρ.le hA1 hA hC1 hAρ hCρ
  refine ⟨F.V 0, fun σ u v hu hv => ?_, fun u hu => ?_, ⟨ρ / (B + 1), by positivity, fun u hu => ?_⟩,
    fun u hu hfix => F.norm_surj u hu hfix, fun σ₀ hσ₀ u hu hN => F.hilbert90_matrix_subalgebra_norm_one σ₀ hσ₀ u hu hN⟩
  · have : v = act σ u := Units.ext hv
    rw [this]
    exact F.act_mem σ hu
  · have hu' : ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 := hu
    rw [pow_zero, mul_one] at hu'
    have hlt : ‖(u : L) - 1‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 _).trans ?_) hAρ
      gcongr
    have h1 : (u : L) = 1 + ((u : L) - 1) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'), norm_one]
    exact max_eq_left hlt.le
  · show ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0
    rw [pow_zero, mul_one]
    refine (hB1 _).trans ?_
    have h2 : B * ‖(u : L) - 1‖ ≤ (B + 1) * (ρ / (B + 1)) := by
      gcongr
      · linarith
    refine h2.trans (le_of_eq ?_)
    field_simp

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

namespace RationalModIntegerChains

open scoped Nat

variable {A : Type} [AddCommGroup A]

section Chain

variable {C : Type} [AddCommGroup C]

end Chain

theorem qz_torsion (x : QZ) : ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨q.num, by
    show (q.num : ℚ) = _
    rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]⟩

end RationalModIntegerChains

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel

structure Model (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (p : ℕ) [Fact p.Prime] where
  K' : IntermediateField ℚ_[p] (PadicAlgCl p)
  fin : FiniteDimensional ℚ_[p] K'
  e : K ≃+* K'
  E : AlgebraicClosure K ≃+* PadicAlgCl p
  comm : ∀ x, E (algebraMap K (AlgebraicClosure K) x) = (e x : PadicAlgCl p)
  homeo : IsHomeomorph e
  int : ∀ x, x ∈ 𝒪[K] ↔ ‖(e x : PadicAlgCl p)‖ ≤ 1

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime]

def Model.IsGalIso (m : Model K p) (φ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃* GK p m.K') : Prop :=
  ∀ σ x, φ σ (m.E x) = m.E (σ x)

def Model.Corr (m : Model K p) (L : IntermediateField K (AlgebraicClosure K))
    (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop := ∀ x, m.E x ∈ L' ↔ x ∈ L

noncomputable def Model.eU (m : Model K p) : Kˣ ≃* (m.K')ˣ := Units.mapEquiv m.e.toMulEquiv

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

def trivRep (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] : TRep ℤ G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  { V := A
    rho := 1
    cont := continuous_snd }

scoped instance (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] :
    DiscreteTopology (trivRep G A).V := ⟨rfl⟩

def trivMap (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) : Pair (trivRep G A) (trivRep G B) :=
  Pair.ofMap (M := trivRep G A) (M' := trivRep G B) f.toIntLinearMap continuous_of_discreteTopology
    fun _ _ => rfl

def charGrp (G : Type) [Group G] [TopologicalSpace G] : AddSubgroup (Additive G →+ QZ) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' := fun ha hb => IsLocallyConstant.add ha hb
  neg_mem' := fun ha => IsLocallyConstant.neg ha

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
