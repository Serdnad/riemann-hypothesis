module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.FiniteLength
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.DFinsupp.WellFounded
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Automorphic.CompactSelfAdjoint

open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem finite_setOf_mem_of_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W] : {i | v i ∈ W}.Finite := by
  let f : {i | v i ∈ W} → W := fun i => ⟨v i, i.2⟩
  have hf : LinearIndependent 𝕜 f := by
    apply LinearIndependent.of_comp W.subtype
    exact hv.linearIndependent.comp _ Subtype.val_injective
  exact Set.finite_coe_iff.1 hf.finite_of_isNoetherian

theorem isClosed_eigenspace (T : E →L[𝕜] E) (μ : 𝕜) :
    IsClosed (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) := by
  have : (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) =
      (T - μ • ContinuousLinearMap.id 𝕜 E) ⁻¹' {0} := by
    ext x
    simp [sub_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage (map_continuous _)

section HilbertBasis

variable [CompleteSpace E]

theorem exists_hilbertBasis_subset_iUnion {α : Type*} (W : α → Submodule 𝕜 E)
    (hW : OrthogonalFamily 𝕜 (fun a => W a) fun a => (W a).subtypeₗᵢ)
    (hc : ∀ a, IsClosed (W a : Set E)) (hbot : (⨆ a, W a)ᗮ = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧ s ⊆ ⋃ a, (W a : Set E) := by
  classical
  have : ∀ a, CompleteSpace (W a) := fun a =>
    completeSpace_coe_iff_isComplete.2 (hc a).isComplete
  choose w b hb using fun a => exists_hilbertBasis 𝕜 (W a)
  let v : (Σ a, w a) → E := fun p => ((p.2 : W p.1) : E)
  have hv : Orthonormal 𝕜 v :=
    hW.orthonormal_sigma_orthonormal (v_family := fun a => ((↑) : w a → W a))
      (fun a => by rw [← hb a]; exact (b a).orthonormal)
  have hkey : ∀ a, (W a : Set E) ⊆ closure (span 𝕜 (Set.range v) : Set E) := by
    intro a y hy
    let y' : W a := ⟨y, hy⟩
    have h := (W a).subtypeL.hasSum ((b a).hasSum_repr y')
    refine mem_closure_of_tendsto h (Eventually.of_forall fun t => ?_)
    refine Submodule.sum_mem _ fun i _ => ?_
    simp only [map_smul]
    refine Submodule.smul_mem _ _ (subset_span ⟨⟨a, i⟩, ?_⟩)
    simp [v, hb a]
  have hle : (⨆ a, W a) ≤ (span 𝕜 (Set.range v))ᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, iSup_le_iff]
    intro a y hy
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact hkey a hy
  have hspan : (span 𝕜 (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff, ← hbot, ← Submodule.triorthogonal_eq_orthogonal]
    exact Submodule.orthogonal_le hle
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hv' : Orthonormal 𝕜 ((↑) : Set.range v → E) := (orthonormal_subtype_range hinj).2 hv
  have hspan' : (span 𝕜 (Set.range ((↑) : Set.range v → E)))ᗮ = ⊥ := by
    rwa [Subtype.range_coe]
  refine ⟨Set.range v, HilbertBasis.mkOfOrthogonalEqBot hv' hspan',
    HilbertBasis.coe_mkOfOrthogonalEqBot hv' hspan', ?_⟩
  rintro _ ⟨p, rfl⟩
  exact Set.mem_iUnion.2 ⟨p.1, (p.2 : W p.1).2⟩

end HilbertBasis

section Spectrum

variable {T : E →L[𝕜] E}

variable [CompleteSpace E]

theorem exists_real_of_hasEigenvalue (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : HasEigenvalue (T : E →ₗ[𝕜] E) μ) : ∃ r : ℝ, μ = r :=
  RCLike.conj_eq_iff_real.1
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT').conj_eigenvalue_eq_self hμ)

theorem finite_eigenvalues_norm_ge (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {ε : ℝ}
    (hε : 0 < ε) : {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  by_contra hinf
  set S := {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  let f : ℕ ↪ S := Infinite.natEmbedding S
  have hv : ∀ n, ∃ v : E, T v = ((f n : 𝕜)) • v ∧ ‖v‖ = 1 := by
    intro n
    obtain ⟨v, hv1, hv2⟩ := (f n).2.1.exists_hasEigenvector
    refine ⟨((‖v‖⁻¹ : ℝ) : 𝕜) • v, ?_, ?_⟩
    · rw [map_smul, show T v = (f n : 𝕜) • v from mem_eigenspace_iff.1 hv1, smul_comm]
    · rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hv2)]
  choose v hvT hvn using hv
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, -, ψ, hψ, hψy⟩ :=
    hK.tendsto_subseq (fun n => hK' ⟨v n, by simp [hvn], rfl⟩)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hψy.cauchySeq ε hε
  have h1 : dist (T (v (ψ (N + 1)))) (T (v (ψ N))) < ε := hN (N + 1) (Nat.le_succ N)
  set a := ψ (N + 1)
  set b := ψ N
  have hne : (f a : 𝕜) ≠ f b := by
    intro h
    have := f.injective (Subtype.ext h)
    exact (hψ (Nat.lt_succ_self N)).ne this.symm
  have horth : ⟪v a, v b⟫_𝕜 = 0 := by
    have := hS.orthogonalFamily_eigenspaces hne ⟨v a, mem_eigenspace_iff.2 (hvT a)⟩
      ⟨v b, mem_eigenspace_iff.2 (hvT b)⟩
    simpa using this
  have hx : ⟪T (v a), T (v b)⟫_𝕜 = 0 := by
    rw [hvT, hvT, inner_smul_left, inner_smul_right, horth, mul_zero, mul_zero]
  have hnx : ε ≤ ‖T (v a)‖ := by
    rw [hvT, norm_smul, hvn, mul_one]
    exact (f a).2.2
  have hsq := norm_sub_sq (𝕜 := 𝕜) (T (v a)) (T (v b))
  rw [hx, map_zero, mul_zero, sub_zero] at hsq
  rw [dist_eq_norm] at h1
  have h2 : 0 ≤ ‖T (v a) - T (v b)‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖T (v b)‖]

end Spectrum

section Eigenbasis

variable [CompleteSpace E]

theorem exists_hilbertBasis_eigenvectors {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧
      ∀ v ∈ s, ∃ μ : ℝ, T v = (μ : 𝕜) • v := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_subset_iUnion
    (fun μ => eigenspace (T : E →ₗ[𝕜] E) μ) hS.orthogonalFamily_eigenspaces
    (isClosed_eigenspace T) (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hS)
  refine ⟨s, b, hb, fun v hv => ?_⟩
  obtain ⟨μ, hμ⟩ := Set.mem_iUnion.1 (hs hv)
  have hv0 : v ≠ 0 := by
    have h := b.orthonormal.1 ⟨v, hv⟩
    rw [hb] at h
    intro h0
    simp [h0] at h
  have hE : HasEigenvalue (T : E →ₗ[𝕜] E) μ := hasEigenvalue_of_hasEigenvector ⟨hμ, hv0⟩
  obtain ⟨r, hr⟩ := exists_real_of_hasEigenvalue hT' hE
  exact ⟨r, by rw [← hr]; exact mem_eigenspace_iff.1 hμ⟩

theorem exists_hilbertBasis_eigenvectors_hasSum {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (l : s → ℝ), ⇑b = ((↑) : s → E) ∧
      (∀ i, T (b i) = (l i : 𝕜) • b i) ∧
      (∀ x, HasSum (fun i => ((l i : 𝕜) * ⟪b i, x⟫_𝕜) • b i) (T x)) ∧
      ∀ ε > 0, {i | ε ≤ |l i|}.Finite := by
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_eigenvectors hT hT'
  choose l hl using fun i : s => hs i i.2
  have hTb : ∀ i, T (b i) = (l i : 𝕜) • b i := fun i => by rw [hb]; exact hl i
  refine ⟨s, b, l, hb, hTb, fun x => ?_, fun ε hε => ?_⟩
  · simpa only [map_smul, hTb, smul_smul, b.repr_apply_apply, mul_comm] using
      T.hasSum (b.hasSum_repr x)
  · have hF := finite_eigenvalues_norm_ge hT hT' hε
    have hsub : {i | ε ≤ |l i|} ⊆ ⋃ μ ∈ {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖},
        {i | b i ∈ eigenspace (T : E →ₗ[𝕜] E) μ} := by
      intro i hi
      have hmem : b i ∈ eigenspace (T : E →ₗ[𝕜] E) (l i : 𝕜) := mem_eigenspace_iff.2 (hTb i)
      have hne : b i ≠ 0 := fun h => by simpa [h] using b.orthonormal.1 i
      refine Set.mem_biUnion (x := (l i : 𝕜))
        ⟨hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩, ?_⟩ hmem
      simpa [RCLike.norm_ofReal] using hi
    refine (hF.biUnion fun μ hμ => ?_).subset hsub
    have hμ0 : μ ≠ 0 := norm_pos_iff.1 (hε.trans_le hμ.2)
    have := ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ0
    exact finite_setOf_mem_of_orthonormal b.orthonormal _

end Eigenbasis

end GroundTheory.Automorphic.CompactSelfAdjoint
end

section

namespace GroundTheory.Automorphic

open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section FinProj

variable {ι : Type*} [Fintype ι]

def finProj (u : ι → H) : H →L[ℂ] H := ∑ i, rankOne ℂ (u i) (u i)

variable {u : ι → H}

end FinProj

section Limits

variable [CompleteSpace H]

end Limits

end

end GroundTheory.Automorphic
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

def HasFiniteLength (ρ : Representation ℂ G V) : Prop :=
  IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule

variable {ρ : Representation ℂ G V}

theorem hasFiniteLength_iff :
    HasFiniteLength ρ ↔
      WellFoundedLT (Subrepresentation ρ) ∧ WellFoundedGT (Subrepresentation ρ) := by
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff, IsArtinian]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨e.strictMono.wellFoundedLT, e.strictMono.wellFoundedGT⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.symm.strictMono.wellFoundedGT, e.symm.strictMono.wellFoundedLT⟩

theorem HasFiniteLength.wellFoundedLT (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).1

theorem HasFiniteLength.wellFoundedGT (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).2

theorem hasFiniteLength_of_strictMono {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PartialOrder (α i)] [∀ i, WellFoundedLT (α i)] [∀ i, WellFoundedGT (α i)]
    (Λ : Subrepresentation ρ → ∀ i, α i) (hΛ : StrictMono Λ) : HasFiniteLength ρ := by
  rw [hasFiniteLength_iff]
  refine ⟨hΛ.wellFoundedLT, ?_⟩
  have h1 : WellFoundedLT (∀ i, (α i)ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i, α i) := h1
  exact hΛ.wellFoundedGT

theorem hasFiniteLength_of_subsingleton [Subsingleton V] : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  exact IsFiniteLength.of_subsingleton

theorem hasFiniteLength_of_isIrreducible [ρ.IsIrreducible] : HasFiniteLength ρ := by
  classical
  have : Finite (Subrepresentation ρ) := Finite.of_equiv _ IsSimpleOrder.equivBool.symm
  rw [hasFiniteLength_iff]
  exact ⟨Finite.to_wellFoundedLT, Finite.to_wellFoundedGT⟩

section MapComap

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}

def subrepMap (f : Representation.IntertwiningMap ρ σ) (A : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := A.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, A.apply_mem_toSubmodule g hx, Representation.IntertwiningMap.isIntertwining _ _ f g x⟩

def subrepComap (f : Representation.IntertwiningMap ρ σ) (B : Subrepresentation σ) :
    Subrepresentation ρ where
  toSubmodule := B.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g x hx := by
    show f (ρ g x) ∈ B.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact B.apply_mem_toSubmodule g hx

theorem subrepMap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepMap f) :=
  fun _ _ h _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

theorem subrepComap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepComap f) :=
  fun _ _ h _ hx => h hx

theorem hasFiniteLength_of_injective (f : Representation.IntertwiningMap ρ σ)
    (hf : Injective f) (hσ : HasFiniteLength σ) : HasFiniteLength ρ := by
  have := hσ.wellFoundedLT
  have := hσ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation σ)
    (fun A _ => subrepMap f A) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepMap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ : f x ∈ subrepMap f A := by
    show f x ∈ subrepMap f A
    rw [show subrepMap f A = subrepMap f B from h1]
    exact ⟨x, hx, rfl⟩
  rw [← hf hyx]
  exact hy

theorem hasFiniteLength_of_surjective (f : Representation.IntertwiningMap ρ σ)
    (hf : Surjective f) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  have := hρ.wellFoundedLT
  have := hρ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation ρ)
    (fun B _ => subrepComap f B) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepComap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun y hy => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ subrepComap f B := hy
  rw [← show subrepComap f A = subrepComap f B from h1] at hx
  exact hx

end MapComap

section Filtration

theorem hasFiniteLength_of_filtration {k : ℕ} (Vf : ℕ → Submodule ℂ V)
    (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ g)) (h0 : Vf 0 = ⊥) (hk : Vf k = ⊤)
    {W : Fin k → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (σ : ∀ j, Representation ℂ G (W j))
    (Ψ : ∀ j : Fin k, Representation.IntertwiningMap (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1)))
      (σ j))
    (hΨ : ∀ (j : Fin k) x, Ψ j x = 0 ↔ (x : V) ∈ Vf j) (hσ : ∀ j, HasFiniteLength (σ j)) :
    HasFiniteLength ρ := by
  classical
  have := fun j => (hσ j).wellFoundedLT
  have := fun j => (hσ j).wellFoundedGT

  let cut : ∀ j : Fin k, Subrepresentation ρ →
      Subrepresentation (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) := fun j A =>
    ⟨A.toSubmodule.comap (Vf (j + 1)).subtype, fun g x hx => A.apply_mem_toSubmodule g hx⟩
  refine hasFiniteLength_of_strictMono (α := fun j => Subrepresentation (σ j))
    (fun A j => subrepMap (Ψ j) (cut j A)) fun A B hAB => ?_
  have hmono' : ∀ j, subrepMap (Ψ j) (cut j A) ≤ subrepMap (Ψ j) (cut j B) := fun j =>
    subrepMap_mono _ (fun x hx => hAB.le hx)
  rw [Pi.lt_def]
  refine ⟨hmono', ?_⟩

  have hex : ∃ j, j < k ∧ ∃ x ∈ B, x ∈ Vf (j + 1) ∧ x ∉ A := by
    obtain ⟨x, hxB, hxA⟩ := IsConcreteLE.exists_of_lt hAB
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [h0] at hk
      exact hxA (by
        have : x ∈ (⊤ : Submodule ℂ V) := trivial
        rw [← hk] at this
        rw [(Submodule.mem_bot ℂ).1 this]
        exact A.toSubmodule.zero_mem)
    refine ⟨k - 1, by omega, x, hxB, ?_, hxA⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk]
    trivial
  let j₀ := Nat.find hex
  obtain ⟨hj₀k, x, hxB, hxV, hxA⟩ := Nat.find_spec hex
  have hbelow : ∀ y ∈ B, y ∈ Vf j₀ → y ∈ A := by
    intro y hyB hyV
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, h0] at hyV
      rw [(Submodule.mem_bot ℂ).1 hyV]
      exact A.toSubmodule.zero_mem
    · by_contra hyA
      obtain ⟨m, hm⟩ : ∃ m, j₀ = m + 1 := ⟨j₀ - 1, by omega⟩
      have := Nat.find_min hex (m := m) (by omega)
      exact this ⟨by omega, y, hyB, by rw [← hm]; exact hyV, hyA⟩
  refine ⟨⟨j₀, hj₀k⟩, lt_of_le_of_ne (hmono' _) fun heq => hxA ?_⟩
  have hmem : Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ ∈ subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) :=
    ⟨⟨x, hxV⟩, hxB, rfl⟩
  have heq' : subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ A) =
      subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) := heq
  rw [← heq'] at hmem
  obtain ⟨y, hyA, hyx⟩ := hmem
  have hyx' : Ψ ⟨j₀, hj₀k⟩ y = Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ := hyx
  have hd : Ψ ⟨j₀, hj₀k⟩ (⟨x, hxV⟩ - y) = 0 := by rw [map_sub, hyx', sub_self]
  rw [hΨ] at hd
  have hyA' : (y : V) ∈ A := hyA
  have hdB : ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) ∈ B :=
    B.toSubmodule.sub_mem hxB (hAB.le hyA')
  have := hbelow _ hdB hd
  have hx' : x = ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) + y := by simp
  rw [hx']
  exact A.toSubmodule.add_mem this hyA'

end Filtration

end GroundTheory.Automorphic
end
end
