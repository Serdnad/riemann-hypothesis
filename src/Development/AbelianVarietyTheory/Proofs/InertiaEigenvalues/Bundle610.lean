module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CovRep

variable {l : ℕ} [Fact l.Prime]

theorem zOm_smul_eq {m a : ℕ} (c : ℤ_[l]) (x : Fin m → Matrix (Fin a) (Fin a) (Om l)) :
    zOm l c • x = ((c : ℚ_[l])) • x := by
  rw [← algebraMap_smul (Om l) (c : ℚ_[l]) x]
  rfl

theorem isInducing_coe : Topology.IsInducing (fun x : ℤ_[l] => (x : ℚ_[l])) := { eq_induced := rfl }

theorem coord_unique {m a d' : ℕ} {bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)}
    (hli : LinearIndependent ℚ_[l] bb) {z z' : Fin d' → ℤ_[l]}
    (h : ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s) : z = z' := by
  simp only [zOm_smul_eq] at h
  have h0 : ∑ s, (((z s : ℚ_[l])) - (z' s : ℚ_[l])) • bb s = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := (Fintype.linearIndependent_iff.mp hli) _ h0
  funext s
  have hs := this s
  rw [sub_eq_zero] at hs
  exact Subtype.ext hs

theorem tup_mul {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs (g * h) = GlobalTheory.TraceConjugationCover.tup ρs g * GlobalTheory.TraceConjugationCover.tup ρs h := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_one {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) :
    GlobalTheory.TraceConjugationCover.tup ρs 1 = 1 := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_inv {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ = fun k => (((ρs k g)⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

end GlobalTheory.CovRep

open GlobalTheory.CovRep in
theorem GlobalTheory.CovRep.rep_of_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (T : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l))) (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), (∀ k, Continuous (ρs k)) → LinearIndependent ℚ_[l] bb → (∀ s, bb s ∈ T) → (∀ x ∈ T, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) → (∀ g, ∀ x ∈ T, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ T) → ∃ ρ' : Γ →* GL (Fin d') ℤ_[l], Continuous ρ' ∧ ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) • bb s := by
  intro l _ Γ _ _ a m ρs T d' bb hc hli hbbT hcoord hstab
  classical
  let crd : (Fin m → Matrix (Fin a) (Fin a) (Om l)) → Fin d' → ℤ_[l] := fun x =>
    if h : ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s then h.choose else 0
  have hcrd : ∀ x ∈ T, x = ∑ s, zOm l (crd x s) • bb s := by
    intro x hx
    have h := hcoord x hx
    simp only [crd, dif_pos h]
    exact h.choose_spec
  have hcrd_eq : ∀ z : Fin d' → ℤ_[l], crd (∑ s, zOm l (z s) • bb s) = z := by
    intro z
    have h : ∃ z' : Fin d' → ℤ_[l], ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s := ⟨z, rfl⟩
    simp only [crd, dif_pos h]
    exact (coord_unique hli h.choose_spec).symm
  let Mf : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun s j => crd (GlobalTheory.TraceConjugationCover.tup ρs g * bb j) s
  have hMf : ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (Mf g s j) • bb s :=
    fun g j => hcrd _ (hstab g _ (hbbT j))
  have key : ∀ g (z : Fin d' → ℤ_[l]),
      GlobalTheory.TraceConjugationCover.tup ρs g * ∑ s, zOm l (z s) • bb s = ∑ t, zOm l ((Mf g *ᵥ z) t) • bb t := by
    intro g z
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hMf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_smul]
    congr 1

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hmul : ∀ g h, Mf (g * h) = Mf g * Mf h := by
    intro g h
    apply Matrix.ext
    intro s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j = ∑ t, zOm l ((Mf g *ᵥ fun s => Mf h s j) t) • bb t := by
      rw [tup_mul, mul_assoc, hMf h j, key]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j) s = _
    rw [e, hcrd_eq]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hone : Mf 1 = 1 := by
    apply Matrix.ext
    intro s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j = ∑ t, zOm l ((1 : Matrix (Fin d') (Fin d') ℤ_[l]) t j) • bb t := by
      rw [tup_one, one_mul]
      simp [Matrix.one_apply]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j) s = _
    rw [e, hcrd_eq]
  let ρM : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] :=
    { toFun := Mf, map_one' := hone, map_mul' := hmul }
  let ρ' : Γ →* GL (Fin d') ℤ_[l] := ρM.toHomUnits
  have hval : ∀ g, ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) = Mf g := fun g => rfl

  let W := Submodule.span ℚ_[l] (Set.range bb)
  let B : Module.Basis (Fin d') ℚ_[l] W := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] W := Module.Finite.of_basis B
  have hW : ∀ x ∈ T, x ∈ W := by
    intro x hx
    rw [hcrd x hx]
    simp only [zOm_smul_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  have hrepr : ∀ x (hx : x ∈ T) s, ((crd x s : ℚ_[l])) = B.repr ⟨x, hW x hx⟩ s := by
    intro x hx s
    have e : (⟨x, hW x hx⟩ : W) = ∑ t, ((crd x t : ℚ_[l])) • B t := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      have hB : ∀ t, ((B t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t := fun t => by
        show ((Module.Basis.span hli t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t
        rw [Module.Basis.span_apply]
      simp only [Submodule.coe_smul, hB]
      show x = _
      conv_lhs => rw [hcrd x hx]
      exact Finset.sum_congr rfl fun t _ => zOm_smul_eq _ _
    rw [e, B.repr_sum_self]
  have hcont : ∀ F : Γ → (Fin m → Matrix (Fin a) (Fin a) (Om l)), Continuous F → (∀ g, F g ∈ T) →
      ∀ s, Continuous fun g => crd (F g) s := by
    intro F hF hT s
    rw [isInducing_coe.continuous_iff]
    have e : (fun x : ℤ_[l] => (x : ℚ_[l])) ∘ (fun g => crd (F g) s) =
        fun g => B.coord s ⟨F g, hW _ (hT g)⟩ := by
      funext g
      simp only [Function.comp_apply, Module.Basis.coord_apply]
      exact hrepr _ (hT g) s
    rw [e]
    exact (LinearMap.continuous_of_finiteDimensional (B.coord s)).comp (hF.subtype_mk _)
  have htup : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g :=
    continuous_pi fun k => Units.continuous_val.comp (hc k)
  have htupi : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ := by
    simp_rw [tup_inv]
    exact continuous_pi fun k => Units.continuous_coe_inv.comp (hc k)
  have hMc : Continuous Mf := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htup).matrix_mul continuous_const))
      (fun g => hstab g _ (hbbT j)) s
  have hMci : Continuous fun g => Mf g⁻¹ := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htupi).matrix_mul continuous_const))
      (fun g => hstab g⁻¹ _ (hbbT j)) s
  refine ⟨ρ', ?_, fun g j => by rw [hval]; exact hMf g j⟩
  rw [Units.continuous_iff]
  refine ⟨hMc, ?_⟩
  have e : (fun g => (((ρ' g)⁻¹ : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) = fun g => Mf g⁻¹ := by
    funext g
    rw [← map_inv]
    exact hval _
  rw [e]
  exact hMci

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.TraceConjugationCover

theorem latT_entries_and_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∀ k i j, x k i j ∈ (L k).1) ∧ ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (GlobalTheory.TraceConjugationCover.latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
  intro l _ Γ _ a m ρs L t M hρ ht hspan

  have hsm : ∀ k (c : ℤ_[l]) (y : Om l), y ∈ (L k).1 → c • y ∈ (L k).1 := by
    intro k c y hy
    rw [← IsScalarTower.algebraMap_smul ℚ_[l] c y]
    exact (L k).1.smul_mem hy
  let S : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
    { carrier := {x | ∀ k i j, x k i j ∈ (L k).1}
      add_mem' := fun {x y} hx hy k i j => by
        simpa using (L k).1.add_mem (hx k i j) (hy k i j)
      zero_mem' := fun k i j => by simpa using (L k).1.zero_mem
      smul_mem' := fun c x hx k i j => by
        simpa using hsm k c _ (hx k i j) }
  have hlM : ∀ k, ((l : Om l) ^ M) ∈ (L k).1 := fun k =>
    pow_mem (by simpa using (L k).1.natCast_mem l) M
  have hsingle : ∀ k (y : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, y i j ∈ (L k).1) →
      Pi.single k y ∈ S := by
    intro k y hy k' i j
    by_cases h : k' = k
    · subst h; simpa using hy i j
    · simp [Pi.single_apply, h, (L k').1.zero_mem]
  have hle : latT ρs t M ≤ S := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩ k i j
      exact hρ k g i j
    · rw [latL, Submodule.span_le]
      intro z hz
      simp only [Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨k, y, hy, rfl⟩ := hz
      refine hsingle k _ fun i j => ?_
      simpa using (L k).1.mul_mem (hlM k) (ht k y hy i j)
  refine ⟨fun x hx => hle hx, ?_⟩
  intro x hx
  have hsing : ∀ k, ∀ y ∈ t k, Pi.single k y ∈
      Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
    intro k y hy
    have hne : ((l : ℚ_[l]) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hmem : Pi.single k ((l : Om l) ^ M • y) ∈ latT ρs t M :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_iUnion.2 ⟨k, y, hy, rfl⟩))
    have heq : (l : Om l) ^ M • y = ((l : ℚ_[l]) ^ M) • y := by
      rw [← algebraMap_smul (Om l) ((l : ℚ_[l]) ^ M) y]
      simp
    have : (Pi.single k y : Fin m → Matrix (Fin a) (Fin a) (Om l)) = ((l : ℚ_[l]) ^ M)⁻¹ • (Pi.single k ((l : Om l) ^ M • y) : Fin m → Matrix (Fin a) (Fin a) (Om l)) := by
      rw [heq, Pi.single_smul', inv_smul_smul₀ hne]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hk : ∀ k, Pi.single k (x k) ∈
      Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
    intro k
    have h1 := hspan k (x k) (hx k)
    have h2 : LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k (x k) ∈
        Submodule.map (LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k)
          (Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) :=
      Submodule.mem_map_of_mem h1
    rw [Submodule.map_span] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨y, hy, rfl⟩
    exact hsing k y hy
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem _ fun k _ => hk k

end GlobalTheory.TraceConjugationCover
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.TraceConjugationCover

theorem latT_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] bb ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s := by
  intro l _ Γ _ a m ρs t M h1 h2

  set Λ : Fin m → Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    fun k => Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) with hΛ
  have hsum : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]), ∑ y ∈ t k, zOm l (c y) • y ∈ Λ k := by
    intro k c
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [zOm_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  have hone : ∀ k, (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ Λ k := by
    intro k
    obtain ⟨c, hc⟩ := h1 k
    rw [← hc]; exact hsum k c
  have hstab : ∀ k g, ∀ x ∈ Λ k, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k := by
    intro k g x hx
    refine Submodule.span_induction (p := fun x _ => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨c, hc⟩ := h2 k g y hy
      rw [hc]; exact hsum k c
    · simp
    · intro x y _ _ hx hy
      rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [← zOm_smul, Matrix.mul_smul, zOm_smul]
      exact Submodule.smul_mem _ _ hx

  have hsingle : ∀ k, ∀ x ∈ Λ k, Pi.single k x ∈ latL t 0 := by
    intro k x hx
    have : (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) x ∈ latL t 0 := by
      have hle : (Λ k).map (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) ≤ latL t 0 := by
        rw [hΛ, Submodule.map_span, latL]
        refine Submodule.span_mono ?_
        rintro _ ⟨y, hy, rfl⟩
        refine Set.mem_iUnion.2 ⟨k, y, hy, ?_⟩
        simp
      exact hle (Submodule.mem_map_of_mem hx)
    simpa using this
  have hT : latT ρs t M ≤ latL t 0 := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [show tup ρs g = ∑ k, Pi.single k (tup ρs g k) from (Finset.univ_sum_single _).symm]
      refine Submodule.sum_mem _ fun k _ => hsingle k _ ?_
      have := hstab k g 1 (hone k)
      simpa [tup] using this
    · rw [latL, Submodule.span_le]
      intro z hz
      obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.1 hz
      refine hsingle k _ ?_
      have : ((l : ℤ_[l]) ^ M) • y ∈ Λ k := Submodule.smul_mem _ _ (Submodule.subset_span hy)
      rw [← zOm_smul, map_pow, map_natCast] at this
      exact this
  have hfg0 : (latL t (0 : ℕ)).FG := by
    rw [latL]
    refine Submodule.fg_span ?_
    exact Set.finite_iUnion fun k => (t k).finite_toSet.image _
  have hfg : (latT ρs t M).FG := hfg0.of_le hT
  haveI : Module.Finite ℤ_[l] (latT ρs t M) := Module.Finite.iff_fg.2 hfg
  have hinj : Function.Injective (zOm l) :=
    (algebraMap ℚ_[l] (Om l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI tf0 : Module.IsTorsionFree ℤ_[l] (Om l) := .of_smul_eq_zero fun c x h => by
    rw [← zOm_smul, smul_eq_mul, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hinj (by simpa using h)
    · right; exact h
  haveI tf1 : Module.IsTorsionFree ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    inferInstanceAs (Module.IsTorsionFree ℤ_[l] (Fin a → Fin a → Om l))
  haveI : Module.IsTorsionFree ℤ_[l] (latT ρs t M) := inferInstance
  haveI : Module.Free ℤ_[l] (latT ρs t M) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] (latT ρs t M)
  refine ⟨_, fun s => (b s : Fin m → Matrix (Fin a) (Fin a) (Om l)), ?_, fun s => (b s).2, ?_⟩
  · rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
    exact b.linearIndependent.map' (latT ρs t M).subtype (Submodule.ker_subtype _)
  · intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [zOm_smul]
    exact this.symm

end GlobalTheory.TraceConjugationCover
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l)

theorem phiS_map_emb (u : ↥L.1 ⊗[ℚ_[l]] ↥L.1) :
    phiS P σ L (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) u) =
      emb P σ L (Algebra.TensorProduct.lift (AlgHom.id ℚ_[l] ↥L.1) (AlgHom.id ℚ_[l] ↥L.1)
        (fun _ _ => Commute.all _ _) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c d => simp [phiS, map_mul]

theorem key_emb (t : ↥L.1 ⊗[ℚ_[l]] ↥L.1)
    (ht : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] c) * t = (AlgHom.id ℚ_[l] ↥L.1) c • t) (c : ↥L.1) :
    ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t =
      (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L)) (ht c)
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
  rw [h, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  simp

theorem mul_eq_mul_phiS (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hkey : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e = (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e)
    (s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) : e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), TensorProduct.tmul_add, mul_add]
  | tmul c b =>
    calc e * (c ⊗ₜ[ℚ_[l]] b) = ((c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by
          rw [mul_comm (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
      _ = (((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by rw [hkey]
      _ = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L (c ⊗ₜ[ℚ_[l]] b)) := by
          rw [mul_comm ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, phiS_tmul, emb_apply]

theorem sm_eq_zero_of_PhiS (a : ℕ) (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hmul : ∀ s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s))
    (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) (hx : PhiS P σ L a x = 0) :
    GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  have hc : ∀ i, phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥L.1 (Fin a)).coord i) x) = 0 := by
    intro i
    have : (Pi.basisFun ↥L.1 (Fin a)).coord i = (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) := by
      ext v; simp
    rw [this]
    exact congrFun hx i
  have hsum := GlobalTheory.DRFil.eq_sum_basis (Qp := ℚ_[l]) (F := P.R.BdR) (Pi.basisFun ↥L.1 (Fin a)) x

  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← GlobalTheory.DRFil.sm_mul, hmul, hc i, TensorProduct.tmul_zero, mul_zero]
  simp

end GlobalTheory.HodgeAt

theorem GlobalTheory.HodgeAt.exists_idem_phiS_ker : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  intro l _ P σ L _ a
  obtain ⟨t, ht1, ht2⟩ := GlobalTheory.DRFil.exists_idem (Qp := ℚ_[l]) (AlgHom.id ℚ_[l] ↥L.1)
  refine ⟨Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t, ?_, ?_⟩
  · rw [phiS_map_emb, ht1, map_one]
  · exact sm_eq_zero_of_PhiS P σ L a _ (mul_eq_mul_phiS P σ L _ (key_emb P σ L t ht2))
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

theorem PhiS_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  intro l _ P K L σ a r R hR g hg x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, PhiS_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add x y hx hy =>
    rw [map_add (f := _), PhiS_add, hx, hy, PhiS_add]
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, hR, PhiS_tmul, PhiS_tmul]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]

    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, Finset.sum_mul,
    P.actQdR_Om, hg, mul_assoc]

end GlobalTheory.HodgeAt
end
end
