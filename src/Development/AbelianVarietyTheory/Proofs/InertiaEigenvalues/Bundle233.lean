module

public import GroundTheory.LocalFields.Different
public import GroundTheory.LocalFields.IntermediateField
public import GroundTheory.LocalFields.Bundle004
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle219
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle025
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle220
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle040
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Formalism.CoboundaryTransfers.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.LocalFields.Interface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | exact GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | (intros; apply GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.galoisGroup_fixedField_baseChange_localField : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  first | exact @GlobalTheory.PMon.Ram.baseChange_fixedField | exact GlobalTheory.PMon.Ram.baseChange_fixedField | (intros; apply GlobalTheory.PMon.Ram.baseChange_fixedField <;> assumption)
end

section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.BurnsideIff

theorem eq_bot_or_top_of_span_eq_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (h : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, ((M g).map (algebraMap k K)).mulVec x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5; revert Γ k K h_3 h_4 h_5 r M h W hW; exact @_root_.GlobalTheory.InvariantBotOrTop.main)
  | exact @_root_.GlobalTheory.InvariantBotOrTop.main
  | exact _root_.GlobalTheory.InvariantBotOrTop.main
  | (apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantBotOrTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantBotOrTop.main ..)

end GlobalTheory.BurnsideIff
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_initialSegment_not_inf_le_filtration : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R → (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | exact GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | (intros; apply GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem _root_.GlobalTheory.T.block_mulVec_decomposition_map_of_decomposition : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))), ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)), ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K), (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) → ∀ u, e' ((M.map φ).mulVec u) = ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  first | exact @GlobalTheory.blockDecomposition_baseChange | exact GlobalTheory.blockDecomposition_baseChange | (intros; apply GlobalTheory.blockDecomposition_baseChange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.character_mod_prime_pow_kernel_generator : ∀ (G : Type) [Group G] (p r : ℕ) (a : G → ℤ), p.Prime → (∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  first | exact @GlobalTheory.PMon.Ram.character_kernel_generator | exact GlobalTheory.PMon.Ram.character_kernel_generator | (intros; apply GlobalTheory.PMon.Ram.character_kernel_generator <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory

theorem padicInt_exists_pow_sub_norm_le_of_exact_level (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ)
    (hm : 1 ≤ m) (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m)
    (hv : ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m) :
    ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  have key : ∀ (x : ℤ_[l]) (n : ℕ), ‖x‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ n ↔ ((l : ℕ) : ℤ_[l]) ^ n ∣ x := by
    intro x n
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_p,
      zpow_neg, zpow_natCast, inv_pow]
  have hl0 : ‖((l : ℕ) : ℤ_[l])‖ ^ m ≠ 0 := by
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨a, ha⟩ := (key _ _).1 hu.le
  obtain ⟨b, hb⟩ := (key _ _).1 hv
  have ha1 : ‖a‖ = 1 := by
    rw [ha, norm_mul, norm_pow] at hu
    exact mul_left_cancel₀ hl0 (by rw [hu, mul_one])
  obtain ⟨a', ha'⟩ := (PadicInt.isUnit_iff.2 ha1).exists_right_inv
  refine ⟨(a' * b).appr 1, (key _ _).2 ?_⟩
  set i := (a' * b).appr 1 with hi
  have hc := PadicInt.appr_spec 1 (a' * b)
  rw [Ideal.mem_span_singleton, pow_one, ← hi] at hc
  obtain ⟨c, hc⟩ := hc
  have hu' : u = 1 + ((l : ℕ) : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  have hv' : v = 1 + ((l : ℕ) : ℤ_[l]) ^ m * b := by rw [← hb]; ring
  have hpow : ∀ (x : ℤ_[l]) (n : ℕ), ∃ d, (1 + x) ^ n = 1 + n * x + x ^ 2 * d := by
    intro x n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d + n + x * d, by rw [pow_succ, hd]; push_cast; ring⟩
  obtain ⟨d, hd⟩ := hpow (((l : ℕ) : ℤ_[l]) ^ m * a) i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ⟨-(a * c) + ((l : ℕ) : ℤ_[l]) ^ k * a ^ 2 * d, ?_⟩
  have hi' : (i : ℤ_[l]) = a' * b - ((l : ℕ) : ℤ_[l]) * c := by rw [← hc]; ring
  rw [hu', hd, hv', hi']
  linear_combination (((l : ℕ) : ℤ_[l]) ^ (1 + k) * b) * ha'

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ), 2 ≤ k → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∀ n : ℕ, ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  first | exact @GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one | exact GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one | (intros; apply GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.TransportH2

variable {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ]
  [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem apply_symm' (i : G ≃ₜ* Γ) (y : Γ) : i (i.symm y) = y := i.apply_symm_apply y

theorem symm_apply' (i : G ≃ₜ* Γ) (x : G) : i.symm (i x) = x := i.symm_apply_apply x

noncomputable def cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Z2 rho ≃ₗ[R] Z2 (rho.comp i.toMulEquiv.toMonoidHom) :=
  { restrictCocycles2 rho i.toMulEquiv.toMonoidHom i.continuous with
    invFun := fun f => ⟨fun p => f.1 (i.symm p.1, i.symm p.2),
      f.2.1.comp (i.symm.continuous.prodMap i.symm.continuous), fun g h k => by
        have e := f.2.2 (i.symm g) (i.symm h) (i.symm k)
        have e' : (rho.comp i.toMulEquiv.toMonoidHom) (i.symm g) = rho g := by
          show rho (i (i.symm g)) = rho g
          rw [apply_symm']
        rw [e'] at e
        show rho g (f.1 (i.symm h, i.symm k)) - f.1 (i.symm (g * h), i.symm k) +
          f.1 (i.symm g, i.symm (h * k)) - f.1 (i.symm g, i.symm h) = 0
        rw [map_mul, map_mul]
        exact e⟩
    left_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i (i.symm p.1), i (i.symm p.2)) = f.1 p
      rw [apply_symm', apply_symm']
    right_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i.symm (i p.1), i.symm (i p.2)) = f.1 p
      rw [symm_apply', symm_apply'] }

theorem map_cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    ((B2 rho).comap (Z2 rho).subtype).map (cocycleEquiv i rho : Z2 rho →ₗ[R] _) =
      (B2 (rho.comp i.toMulEquiv.toMonoidHom)).comap
        (Z2 (rho.comp i.toMulEquiv.toMonoidHom)).subtype := by
  ext f
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨f', hf', rfl⟩
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf'
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ i, hc.comp i.continuous, ?_⟩
    funext p
    have e := congrFun hcf (i p.1, i p.2)
    change _ = f'.1 (i p.1, i p.2)
    rw [← e]
    simp [d1]
    rfl
  · intro hf
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hf
    refine ⟨(cocycleEquiv i rho).symm f, (separated_dvr_second_cohomology_mem rho _).2
      ⟨c ∘ i.symm, hc.comp i.symm.continuous, ?_⟩, (cocycleEquiv i rho).apply_symm_apply f⟩
    funext p
    have e := congrFun hcf (i.symm p.1, i.symm p.2)
    change _ = f.1 (i.symm p.1, i.symm p.2)
    rw [← e]
    simp [d1, symm_apply']
    exact congrArg (fun g => rho g (c (i.symm p.2))) (apply_symm' i p.1).symm

theorem natCard_H2_comp (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) :=
  (Nat.card_congr (Submodule.Quotient.equiv _ _ (cocycleEquiv i rho)
    (map_cocycleEquiv i rho)).toEquiv).symm

end GlobalTheory.TransportH2
end

section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory


open Filter Topology in
open scoped TensorProduct in
theorem _root_.GlobalTheory.lattice_multiples_nhds_basis :
    ∀ (LL O V : Type) [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V] (T : Submodule O V) (lam : O), T.FG → Submodule.span LL (T : Set V) = ⊤ → IsOpen (Set.range (algebraMap O LL)) → algebraMap O LL lam ≠ 0 → (∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (lam ^ a * x) ∈ U) → (∀ a : ℕ, {v : V | ∃ t ∈ T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ T, lam ^ a • t ∈ U := by
  intro LL O V _ _ _ _ _ _ _ _ _ _ _ T lam hT hspan hopen hlam hsmall
  obtain ⟨n, s, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hT
  set φ : (Fin n → LL) →ₗ[LL] V := Fintype.linearCombination LL s with hφ
  have key : ∀ (a : ℕ) (c : Fin n → O),
      φ (fun i => algebraMap O LL (lam ^ a * c i)) = lam ^ a • ∑ i, c i • s i := by
    intro a c
    simp only [hφ, Fintype.linearCombination_apply, Finset.smul_sum, map_mul, mul_smul,
      algebraMap_smul]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp ht
    exact ⟨_, by rw [key 0 c, pow_zero, one_smul]⟩
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hsurj
  refine ⟨fun a => ?_, fun U hU => ?_⟩
  · have hc : algebraMap O LL (lam ^ a) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hlam
    set W : Set LL := Set.range fun x : O => algebraMap O LL (lam ^ a * x) with hW
    have hWeq : W = (Homeomorph.mulLeft₀ _ hc) '' Set.range (algebraMap O LL) := by
      ext y; simp [hW, map_mul]
    have hWo : IsOpen W := hWeq ▸ (Homeomorph.mulLeft₀ _ hc).isOpenMap _ hopen
    have hPo : IsOpen (φ '' Set.univ.pi fun _ => W) :=
      hq.isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hWo)
    refine mem_of_superset (hPo.mem_nhds ⟨0, fun i _ => ⟨0, by simp⟩, map_zero φ⟩) ?_
    rintro v ⟨y, hy, rfl⟩
    choose c hc' using fun i => hy i (Set.mem_univ i)
    have : y = fun i => algebraMap O LL (lam ^ a * c i) := funext fun i => (hc' i).symm
    subst this
    exact ⟨_, (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c, rfl⟩, key a c⟩
  · have h0 : φ ⁻¹' U ∈ 𝓝 (0 : Fin n → LL) :=
      hq.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, hsub⟩ := h0
    obtain ⟨a, ha⟩ := hsmall (⋂ i, t i) (Filter.iInter_mem.mpr ht)
    refine ⟨a, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hv
    rw [← key a c]
    exact hsub fun i _ => Set.mem_iInter.mp (ha (c i)) i

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.H2CardScalars

theorem card_H2_eq_of_same_action {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G]
    [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M]
    (rho : Representation R G M) (rho' : Representation S G M)
    (h : ∀ g m, rho g m = rho' g m) : Nat.card (H2 rho) = Nat.card (H2 rho') := by
  have hZ : ∀ f : G × G → M, f ∈ Z2 rho ↔ f ∈ Z2 rho' := by
    intro f; rw [mem_cocycles2, mem_cocycles2]; simp only [h]
  have hd : ∀ c : G → M, d1 rho c = d1 rho' c := fun c => funext fun p => by
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, h]
  have hB : ∀ f : G × G → M, f ∈ B2 rho ↔ f ∈ B2 rho' := by
    intro f; rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]; simp only [hd]
  let e : Z2 rho ≃ Z2 rho' := Equiv.subtypeEquiv (Equiv.refl _) hZ
  apply Nat.card_congr
  refine Quotient.congr e ?_
  intro a b
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]
  exact hB _

end GlobalTheory.H2CardScalars
end
