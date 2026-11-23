module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePointCountScaling
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle121
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import GroundTheory.LocalFields.Interface

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lastCol {n : ℕ} (u : MirUin k n) : Fin n → k :=
  fun i => (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

theorem continuous_lastCol (n : ℕ) : Continuous (lastCol k (n := n)) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun u : MirUin k n =>
      (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact h.matrix_elem _ _

theorem thetaA_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (u : MirUin k n) :
    thetaA k ψ a u = Circle.toUnits (ψ (a ⬝ᵥ lastCol k u)) := by
  obtain ⟨w, hw⟩ : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n := Subgroup.mem_subgroupOf.1 u.2
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hw.symm
  have hcol : lastCol k u = w.toAdd := by
    funext i
    simp only [lastCol, ← hw]
    exact unip_apply_castSucc_last k n w i
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)).toAdd)) = _
  rw [key, hcol]

theorem isOpen_addChar_eq_one (ψ : AddChar k Circle) (hψ : Continuous ψ) : IsOpen {x : k | ψ x = 1} := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ψ x = 1 := hx
  have ht : Filter.Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  filter_upwards [ht (cball_mem_nhds s)] with y hy
  have h1 : ψ (y - x) = 1 := hs _ hy
  have h2 : ψ y = ψ (y - x) * ψ x := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  show ψ y = 1
  rw [h2, h1, hx', one_mul]

theorem thetaOpen : ThetaOpen k := by
  intro ψ hψ n a
  have hc : Continuous fun u : MirUin k n => a ⬝ᵥ lastCol k u := by
    have h := continuous_lastCol k n
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp h)
  have he : ((thetaA k ψ a).ker : Set (MirUin k n)) =
      (fun u : MirUin k n => a ⬝ᵥ lastCol k u) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, thetaA_apply, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (isOpen_addChar_eq_one k ψ hψ).preimage hc

end GlobalTheory.CompanionTheory.BZFun

end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem rhoVec_sub {i j : Fin n} (h : (j : ℕ) = i + 1) : rhoVec n i - rhoVec n j = 1 := by
  have : (j : ℂ) = (i : ℂ) + 1 := by exact_mod_cast h
  simp only [rhoVec, this]; ring

def sqSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (i j : Fin n), (j : ℕ) = i + 1 ∧ u * e (j, i) ^ 2 = x}

def Jp (n : ℕ) : Submodule ℂ (U n) := vermaIdeal (rhoVec n) ⊔ sqSpan n

theorem vermaIdeal_le_Jp : vermaIdeal (rhoVec n) ≤ Jp n := le_sup_left

theorem sqSpan_le_Jp : sqSpan n ≤ Jp n := le_sup_right

theorem mul_mem_sqSpan (v : U n) {x : U n} (hx : x ∈ sqSpan n) : v * x ∈ sqSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    exact Submodule.subset_span ⟨v * u, i, j, hij, mul_assoc _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mul_mem_Jp (v : U n) {x : U n} (hx : x ∈ Jp n) : v * x ∈ Jp n := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  rw [mul_add]
  exact Submodule.add_mem _ (vermaIdeal_le_Jp (mul_mem_vermaIdeal _ v hy))
    (sqSpan_le_Jp (mul_mem_sqSpan v hw))

theorem mul_sq_mem_Jp (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ Jp n :=
  sqSpan_le_Jp (Submodule.subset_span ⟨u, i, j, hij, rfl⟩)

def IsAdW (μ : Fin n → ℤ) (x : U n) : Prop :=
  ∀ k, e (k, k) * x - x * e (k, k) = (μ k : ℂ) • x

def LowExp (m : Fin n × Fin n →₀ ℕ) : Prop := ∀ a ∈ m.support, IsLower a

def lowSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ canon m = x}

def lowSpanW (μ : Fin n → ℤ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ ∧ canon m = x}

def casC (τ : Fin n → ℂ) : ℂ :=
  ∑ a, τ a ^ 2 + ∑ a, ∑ b, if a < b then τ a - τ b else 0

def ht (μ : Fin n → ℤ) : ℤ := ∑ k : Fin n, ((n : ℤ) - 1 - 2 * (k : ℕ)) * μ k

theorem exists_act {A : Type} [AddCommGroup A] [Module ℂ A] (G : Fin n → Fin n → Module.End ℂ A)
    (h : Formalism.REAL.GlRel G) : ∃ φ : U n →ₐ[ℂ] Module.End ℂ A, ∀ i j, φ (e (i, j)) = G i j := by
  let L : gl n →ₗ[ℂ] Module.End ℂ A :=
    { toFun := fun X => ∑ a : Fin n × Fin n, X a.1 a.2 • G a.1 a.2
      map_add' := fun X Y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r X => by simp [Finset.smul_sum, smul_smul] }
  have hL : ∀ a : Fin n × Fin n, L (E a) = G a.1 a.2 := by
    intro a
    show ∑ b : Fin n × Fin n, (E a) b.1 b.2 • G b.1 b.2 = _
    rw [Finset.sum_eq_single a]
    · simp [E]
    · intro b _ hb
      have : ¬ (a.1 = b.1 ∧ a.2 = b.2) := fun h => hb (Prod.ext h.1 h.2).symm
      simp [E, Matrix.single_apply, this]
    · simp
  have hE : ∀ a b : Fin n × Fin n, L ⁅E a, E b⁆ = ⁅L (E a), L (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul,
      hL, hL, h, map_sub, apply_ite L, apply_ite L, hL, hL, map_zero]
  let ρ : gl n →ₗ⁅ℂ⁆ Module.End ℂ A :=
    { L with
      map_lie' := fun {X Y} => by
        show L ⁅X, Y⁆ = ⁅L X, L Y⁆
        rw [eq_sum_E X, eq_sum_E Y]

        simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ ρ, fun i j => ?_⟩
  rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact hL (i, j)

theorem act_word {A : Type} [AddCommGroup A] [Module ℂ A] {G : Fin n → Fin n → Module.End ℂ A}
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (hφ : ∀ i j, φ (e (i, j)) = G i j)
    (l : List (Fin n × Fin n)) : φ (word l) = (l.map fun p => G p.1 p.2).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [word_cons, map_mul, ih, List.map_cons, List.prod_cons, hφ]

theorem glRel_e (n : ℕ) : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) :=
  fun a b c d => e_mul_sub_mul (a, b) (c, d)

theorem IsAdW.e_mul {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) (a : Fin n × Fin n) :
    IsAdW (fun k => μ k + rootAt a k) (e a * x) := by
  intro k
  have h1 := e_diag_mul_sub k a
  have h2 := hx k
  have : e (k, k) * (e a * x) - e a * x * e (k, k) =
      (e (k, k) * e a - e a * e (k, k)) * x + e a * (e (k, k) * x - x * e (k, k)) := by
    noncomm_ring
  rw [this, h1, h2, smul_mul_assoc, mul_smul_comm, ← add_smul]
  push_cast; ring_nf

theorem ht_rootAt (a : Fin n × Fin n) :
    ht (rootAt a) = 2 * ((a.2 : ℕ) : ℤ) - 2 * ((a.1 : ℕ) : ℤ) := by
  simp only [ht, rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem ht_add_rootAt (μ : Fin n → ℤ) (a : Fin n × Fin n) :
    ht (fun k => μ k + rootAt a k) = ht μ + ht (rootAt a) := by
  simp only [ht, mul_add, Finset.sum_add_distrib]

theorem ht_wt (m : Fin n × Fin n →₀ ℕ) :
    ht (wt m) = m.sum fun a c => (c : ℤ) * ht (rootAt a) := by
  simp only [ht, wt, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ht_wt_nonpos {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ht (wt m) ≤ 0 := by
  rw [ht_wt]
  refine Finset.sum_nonpos fun a ha => ?_
  have h : (a.2 : ℕ) < a.1 := hm a ha
  show (m a : ℤ) * ht (rootAt a) ≤ 0
  rw [ht_rootAt]
  have : (0 : ℤ) ≤ (m a : ℤ) := by positivity
  nlinarith

theorem act_eq_zero_of_mem {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) {x : U n}
    (hx : x ∈ vermaIdeal (rhoVec n)) : φ x t = 0 := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  have h1 : φ y t = 0 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, a, ha, rfl⟩ := hx
      simp [hu a ha]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have h2 : φ w t = 0 := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, k, rfl⟩ := hx
      simp [hd k, Algebra.algebraMap_eq_smul_one]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  simp [h1, h2]

end GlobalTheory.CompanionTheory.PresRho
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.finite_product_difference_bound : ∀ (V : Type) (a : V → ℝ) (A U : Finset V), A ⊆ U → |∏ v ∈ U, a v - ∏ v ∈ A, a v| ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset | exact GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset <;> assumption)
end

section

open Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.CharPerp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def perp {n : ℕ} (ψ : AddChar k Circle) (A : AddSubgroup (Fin n → k)) :
    AddSubgroup (Fin n → k) where
  carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
  zero_mem' := fun a _ => by simp
  add_mem' := fun {x y} hx hy a ha => by
    rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  neg_mem' := fun {x} hx a ha => by
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one]

theorem isOpen_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k))) :
    IsOpen (perp ψ A : Set (Fin n → k)) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have hN : IsOpen ((fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s) :=
    (isOpen_cball s).preimage continuous_dot
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      (fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    obtain rfl : x = 0 := hx
    simp [cball]
  obtain ⟨u, v, hu, -, h0u, hAv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hAc hN hsub
  refine AddSubgroup.isOpen_of_mem_nhds (perp ψ A) (g := 0) ?_
  refine Filter.mem_of_superset (hu.mem_nhds (h0u rfl)) fun ξ hξ a ha => ?_
  exact hs _ (huv (Set.mk_mem_prod hξ (hAv ha)))

theorem isClosed_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) : IsClosed (perp ψ A : Set (Fin n → k)) := by
  have : (perp ψ A : Set (Fin n → k)) =
      ⋂ a ∈ A, (fun ξ : Fin n → k => ψ (ξ ⬝ᵥ a)) ⁻¹' {1} := by
    ext ξ
    simp [perp]
  rw [this]
  refine isClosed_biInter fun a _ => isClosed_singleton.preimage ?_
  exact hψ.comp (continuous_id.dotProduct continuous_const)

theorem isCompact_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (A : AddSubgroup (Fin n → k)) (hAo : IsOpen (A : Set (Fin n → k))) :
    IsCompact (perp ψ A : Set (Fin n → k)) := by
  classical
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  obtain ⟨s, hs⟩ := exists_box_subset (n := Fin n) (hAo.mem_nhds A.zero_mem)
  refine (isCompact_box (n := Fin n) (c * s⁻¹)).of_isClosed_subset (isClosed_perp ψ hψ A) ?_
  intro ξ hξ i _
  by_contra hi
  obtain ⟨t, ht, hne⟩ := hc.exists_ne_one s hi
  have hmem : Pi.single i t ∈ box (Fin n) s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  apply hne
  have := hξ _ (hs hmem)
  rwa [dotProduct_single, mul_comm] at this

theorem perp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) →
    IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧
      IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo
  exact ⟨isOpen_perp ψ hψ A hAc, isCompact_perp ψ hψ h1 A hAo⟩

end GlobalTheory.CompanionTheory.CharPerp
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.lattice_point_count_scaling : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (Λ : AddSubgroup G) [Countable Λ] (D K₀ : Set G) (R : Finset G) (T : ℝ → G →+ G) (M : ℕ), MeasurableSet D → IsCompact K₀ → D ⊆ K₀ → μ D = 1 → (∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) → (∀ ε : ℝ, 0 < ε → Continuous (T ε)) → (∀ ε : ℝ, 0 < ε → ∀ y, T ε⁻¹ (T ε y) = y ∧ T ε (T ε⁻¹ y) = y) → (∀ ε : ℝ, 0 < ε → Measure.map (T ε) μ = ENNReal.ofReal ((ε ^ M)⁻¹) • μ) → (∀ B : Set G, IsCompact B → ∀ U ∈ 𝓝 (0 : G), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, T ε b ∈ U) → ∀ (x0 : G) (φ : G → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l))) ∧ Tendsto (fun ε : ℝ => ε ^ M * ∑' l : Λ, φ (T ε (x0 + l))) (𝓝[>] 0) (𝓝 ((R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.RiemannCore.main | exact GlobalTheory.CompanionTheory.RiemannCore.main | (intros; apply GlobalTheory.CompanionTheory.RiemannCore.main <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.tail_sum_over_places_small : ∀ (F : Type) [Field F] [NumberField F] (C : ℝ), 0 ≤ C → ∀ η : ℝ, 0 < η → ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, T₀ ⊆ T → ∀ U : Finset (HeightOneSpectrum (𝓞 F)), ∑ D ∈ U.powerset with ¬ D ⊆ T, ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq | exact GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

private theorem det_updateRow_one' {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (r : n) (b : n → R) : (updateRow (1 : Matrix n n R) r b).det = b r := by
  rw [← det_transpose, ← updateCol_transpose, transpose_one, ← cramer_apply, cramer_one]
  rfl

theorem exists_GL_lastRow_eq (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hN : (updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_updateRow_one']
    simpa using hi
  have hM : ((updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).submatrix id (Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_permute']
    refine mul_ne_zero ?_ hN
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i (Fin.last m))) with h | h <;> simp [h]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩
  show updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m)) (Fin.last m) (Equiv.swap i (Fin.last m) j) = a j
  rw [updateRow_self, Function.comp_apply, Equiv.swap_apply_self]

end GlobalTheory.CompanionTheory.MirFourier
end
