module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle065
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalEqHaarMultiple
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle069
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizable
public import Mathlib.RepresentationTheory.Character
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle071
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032

@[expose] public section

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Avg

open Classical in
theorem sum_eq_zero_of_translates {G : Type} [Group G] [Fintype G] (N A : Set G) (h1 : (1 : G) ∈ A)
    (hN : ∀ v ∈ A, ∀ u, u * v ∈ N ↔ u ∈ N) (L χ : G → ℂ)
    (hL : ∀ u ∈ N, ∀ v ∈ A, L (u * v) = L u)
    (hs : ∀ u, (∑ v : G, if v ∈ A then χ (u * v) else 0) = 0) :
    (∑ u : G, if u ∈ N then L u * χ u else 0) = 0 := by
  set S : ℂ := ∑ u : G, if u ∈ N then L u * χ u else 0 with hS
  have hv : ∀ v ∈ A, (∑ u : G, if u ∈ N then L u * χ (u * v) else 0) = S := by
    intro v hvA
    rw [hS, ← Equiv.sum_comp (Equiv.mulRight v) (fun u => if u ∈ N then L u * χ u else 0)]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Equiv.coe_mulRight, hN v hvA u]
    split_ifs with hu
    · rw [hL u hu v hvA]
    · rfl
  have h2 : (∑ v : G, if v ∈ A then S else 0) = 0 := by
    calc (∑ v : G, if v ∈ A then S else 0)
        = ∑ v : G, ∑ u : G, if v ∈ A then (if u ∈ N then L u * χ (u * v) else 0) else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          split_ifs with hvA
          · exact (hv v hvA).symm
          · simp
      _ = ∑ u : G, ∑ v : G, if v ∈ A then (if u ∈ N then L u * χ (u * v) else 0) else 0 :=
          Finset.sum_comm
      _ = ∑ u : G, if u ∈ N then L u * ∑ v : G, (if v ∈ A then χ (u * v) else 0) else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          split_ifs with hu
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => ?_
            split_ifs <;> simp
          · simp
      _ = 0 := by
          refine Finset.sum_eq_zero fun u _ => ?_
          rw [hs u]
          simp
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h2
  have hc : (((Finset.univ.filter fun v => v ∈ A).card : ℕ) : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.2
    exact (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
  exact (mul_eq_zero.1 h2).resolve_left hc

theorem colGeR_zero (K : Type) [Field K] (d j : ℕ) : colGeR K d j 0 = colGeE K d (j + 1) := by
  funext i l
  simp [colGeR]

theorem isPat_colGe (d j : ℕ) : IsPat (colGe d j) :=
  ⟨fun i h => lt_irrefl _ h.1, fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2⟩⟩

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}

theorem unip_entry {v : GL (Fin d) K} (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j))
    {k l : Fin d} (hk : j ≤ (k : ℕ)) (hl : j ≤ (l : ℕ)) :
    (v : Matrix (Fin d) (Fin d) K) k l = if k = l then 1 else 0 := by
  refine hv.2 k l ?_
  simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, not_lt.2 hk, not_lt.2 hl]

theorem unip_subset_patSet {v : GL (Fin d) K}
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    v ∈ patSet (K := K) (colGe d j) := by
  intro i l
  constructor
  · rintro rfl
    have := hv.2 i i rfl
    simpa using this
  · intro e hn
    by_cases hi : (i : ℕ) < j
    · by_cases hl : (l : ℕ) < j
      · have := hv.2 i l (by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl])
        simpa [e] using this
      · exact absurd ⟨Fin.lt_def.2 (by
          have := not_lt.1 hl
          omega), not_lt.1 hl⟩ hn
    · by_cases hl : (l : ℕ) < j
      · refine hv.1.1 i l ?_
        simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl]
      · have := unip_entry hv (not_lt.1 hi) (not_lt.1 hl)
        simpa [e] using this

theorem mul_entry {u v : GL (Fin d) K} (hu : u ∈ patSet (K := K) (colGe d j))
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) {i l : Fin d}
    (hi : j ≤ (i : ℕ)) (hl : j ≤ (l : ℕ)) :
    ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i l = (u : Matrix (Fin d) (Fin d) K) i l := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single l]
  · rw [unip_entry hv hl hl]
    simp
  · intro k _ hk
    by_cases hik : (u : Matrix (Fin d) (Fin d) K) i k = 0
    · simp [hik]
    · have hjk : j ≤ (k : ℕ) := by
        by_cases e : i = k
        · exact e ▸ hi
        · by_contra hn
          exact hik ((hu i k).2 e fun h => hn h.2)
      rw [unip_entry hv hjk hl, if_neg hk, mul_zero]
  · simp

theorem patChar_mul_unip (ψ₀ : AddChar K ℂ) {u v : GL (Fin d) K} (hu : u ∈ patSet (K := K) (colGe d j))
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    patChar (colGeE K d (j + 1)) ψ₀ (u * v) = patChar (colGeE K d (j + 1)) ψ₀ u := by
  unfold patChar
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h : (l : ℕ) = i + 1 ∧ j + 1 ≤ (l : ℕ)
  · rw [mul_entry hu hv (by omega) (by omega)]
  · have hz : colGeE K d (j + 1) i l = 0 := if_neg h
    rw [hz, zero_mul, zero_mul]

theorem wh_zero_row (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ)
    (hs : ∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) :
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  classical
  rw [colGeR_zero]
  unfold wh
  have h1 : (1 : GL (Fin d) K) ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by
    refine ⟨one_mem _, fun i l _ => ?_⟩
    simp [Matrix.one_apply]
  have hP := isPat_colGe d j
  have hN : ∀ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j), ∀ u : GL (Fin d) K,
      u * v ∈ patSet (K := K) (colGe d j) ↔ u ∈ patSet (K := K) (colGe d j) := by
    intro v hv u
    have hv' : v ∈ GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K := K) hP := unip_subset_patSet hv
    exact (GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K := K) hP).mul_mem_cancel_right hv'
  have key := sum_eq_zero_of_translates (patSet (K := K) (colGe d j))
    (Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) h1 hN
    (fun u => (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹) χ
    (fun u hu v hv => by simp only [patChar_mul_unip ψ₀ hu hv]) (by simpa using hs)
  rw [key, mul_zero]

theorem wh_zero_row' : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  intro K _ _ _ d j ψ₀ χ hs
  exact wh_zero_row K d j ψ₀ χ hs

end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_extend {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K))
    (hs : Submodule.span K (L : Set (Fin m → K)) = ⊤) (φ : L →ₗ[𝓞 K] 𝓞 K) :
    ∃ G : (Fin m → K) →ₗ[K] K, ∀ x : L, G x = algebraMap (𝓞 K) K (φ x) := by
  classical
  have hs' : ⊤ ≤ Submodule.span K (L : Set (Fin m → K)) := hs.ge
  obtain ⟨ι, b, hb⟩ : ∃ (ι : Type) (b : Module.Basis ι K (Fin m → K)), ∀ i, b i ∈ L :=
    ⟨_, Module.Basis.ofSpan hs', fun i => Module.Basis.ofSpan_subset hs' ⟨i, rfl⟩⟩
  haveI := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite ι
  let G : (Fin m → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩))
  have hGb : ∀ i, G (b i) = algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩) := fun i => b.constr_basis _ _ _
  refine ⟨G, fun x => ?_⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun i => b.repr (x : Fin m → K) i) (S := K)
  choose e he using hd
  have hx : ((d : 𝓞 K) • (x : Fin m → K)) = ∑ i, e i • b i := by
    conv_lhs => rw [← b.sum_repr (x : Fin m → K)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), he i, smul_assoc]
  have hxL : (d : 𝓞 K) • x = ∑ i, e i • (⟨b i, hb i⟩ : L) := by
    apply Subtype.ext
    simpa using hx
  have h1 : (d : 𝓞 K) * φ x = ∑ i, e i * φ ⟨b i, hb i⟩ := by
    have h := congrArg φ hxL

    rw [map_smul, map_sum, smul_eq_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have h2 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = algebraMap (𝓞 K) K ((d : 𝓞 K) * φ x) := by
    have h3 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = G ((d : 𝓞 K) • (x : Fin m → K)) := by
      rw [← algebraMap_smul K (d : 𝓞 K) (x : Fin m → K), map_smul, smul_eq_mul]

    rw [h3, hx, h1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), map_smul, hGb, smul_eq_mul, map_mul]
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero d.2
    simpa using this
  rw [map_mul] at h2
  exact mul_left_cancel₀ hd0 h2

theorem mem_of_dot_integral : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K,
    (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  intro K _ _ m L hL v hv
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree (𝓞 K) L := inferInstance
  haveI : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let φ : Fin n → L →ₗ[𝓞 K] 𝓞 K := fun i => (LinearMap.proj i).comp s
  let l : Fin n → L := fun i => f (fun j => if i = j then 1 else 0)
  have hdual : ∀ x : L, x = ∑ i, φ i x • l i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    have h2 := LinearMap.pi_apply_eq_sum_univ f (s x)
    rw [h1] at h2
    exact h2
  choose G hG using fun i => exists_extend L hspan (φ i)
  let a : Fin n → Fin m → K := fun i j => G i (fun k => if j = k then 1 else 0)
  have ha : ∀ i w, a i ⬝ᵥ w = G i w := by
    intro i w
    rw [LinearMap.pi_apply_eq_sum_univ (G i) w]
    simp [dotProduct, a, mul_comm]
  have hid : ∀ w : Fin m → K, w = ∑ i, G i w • (l i : Fin m → K) := by
    let T : (Fin m → K) →ₗ[K] (Fin m → K) := ∑ i, (G i).smulRight (l i : Fin m → K)
    have hT : T = LinearMap.id := by
      refine LinearMap.ext_on hspan ?_
      intro x hx
      have h1 := congrArg (Subtype.val) (hdual ⟨x, hx⟩)
      simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have h2 : ∀ i, G i x • (l i : Fin m → K) = φ i ⟨x, hx⟩ • (l i : Fin m → K) := by
        intro i
        rw [show G i x = algebraMap (𝓞 K) K (φ i ⟨x, hx⟩) from hG i ⟨x, hx⟩, algebraMap_smul]
      simp only [h2]
      simpa using h1.symm
    intro w
    have h := LinearMap.congr_fun hT w
    simpa [T, LinearMap.sum_apply] using h.symm
  have hint : ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = a i ⬝ᵥ v := by
    intro i
    have h := hv (a i) (fun x hx => by
      rw [(ha i x).trans (hG i ⟨x, hx⟩)]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩)
    exact Submodule.mem_one.mp h
  choose o ho using hint
  rw [hid v]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h3 : G i v • (l i : Fin m → K) = o i • (l i : Fin m → K) := by
    rw [← ha, ← ho, algebraMap_smul]
  rw [h3]
  exact L.smul_mem _ (l i).2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix nonZeroDivisors

theorem mem_den_iff {K : Type} [Field K] [NumberField K] (x : K) (a : 𝓞 K) :
    a ∈ HS.den K x ↔ ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * x := by
  rw [HS.den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  show (∀ i : Fin 1, ∃ o, algebraMap (𝓞 K) K o = (a • fun _ : Fin 1 => x) i) ↔ _
  simp only [Pi.smul_apply, Algebra.smul_def]
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem exists_bezout {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ a ∈ HS.den K x, ∃ c ∈ HS.den K x,
      algebraMap (𝓞 K) K a + algebraMap (𝓞 K) K c * x = 1 := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : FractionalIdeal (𝓞 K)⁰ K,
      S = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ x :=
    ⟨_, rfl⟩
  have h1S : (1 : K) ∈ S := by
    rw [hSdef]; exact (le_sup_left : FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hxS : x ∈ S := by
    rw [hSdef]; exact (le_sup_right : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hS : S ≠ 0 := by
    intro h
    rw [h] at h1S
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).1 h1S)
  have hden : ∀ t ∈ S⁻¹, ∃ a ∈ HS.den K x, algebraMap (𝓞 K) K a = t := by
    intro t ht
    rw [FractionalIdeal.mem_inv_iff hS] at ht
    have ht1 : t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      have := ht 1 h1S
      rwa [mul_one] at this
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 ht1
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 (ht x hxS)
    exact ⟨a, (mem_den_iff x a).2 ⟨o, by rw [ho, ha]⟩, ha⟩
  have hsplit : ∀ T : FractionalIdeal (𝓞 K)⁰ K, S * T = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) * T ⊔
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * T := by
    intro T
    rw [hSdef, FractionalIdeal.sup_eq_add, FractionalIdeal.sup_eq_add, add_mul]
  have h1 : (1 : K) ∈ S * S⁻¹ := by
    rw [mul_inv_cancel₀ hS]; exact FractionalIdeal.one_mem_one _
  rw [hsplit S⁻¹, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
  obtain ⟨u, hu, v, hv, huv⟩ := h1
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨a, ha, ha'⟩ := hden u' hu'
  obtain ⟨c, hc, hc'⟩ := hden v' hv'
  refine ⟨a, ha, c, hc, ?_⟩
  rw [ha', hc', ← huv]
  ring

theorem den_algebraMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : F) :
    HS.den E (algebraMap F E x) = Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (HS.den F x) := by
  have tower : ∀ o : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) o) =
      algebraMap F E (algebraMap (𝓞 F) F o) := by
    intro o
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  apply le_antisymm
  · intro b hb
    obtain ⟨a, ha, c, hc, hac⟩ := exists_bezout x
    obtain ⟨o, ho⟩ := (mem_den_iff _ b).1 hb
    have key : b = algebraMap (𝓞 F) (𝓞 E) a * b + algebraMap (𝓞 F) (𝓞 E) c * o := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      have hac' := congrArg (algebraMap F E) hac
      simp only [map_add (f := _), map_mul, map_one] at hac'
      simp only [map_add (f := _), map_mul, tower, ho]
      linear_combination (-(algebraMap (𝓞 E) E b)) * hac'
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha))
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc))
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_den_iff]
    obtain ⟨o, ho⟩ := (mem_den_iff x a).1 ha
    exact ⟨algebraMap (𝓞 F) (𝓞 E) o, by rw [tower, tower, ho, map_mul]⟩

theorem absNorm_den_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ x : F,
      Ideal.absNorm (HS.den E (algebraMap F E x)) = Ideal.absNorm (HS.den F x) ^ 2 := by
  intro F E _ _ _ _ _ h2 x
  rw [den_algebraMap, Ideal.absNorm_algebraMap]
  congr 1
  rw [← h2]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap
end
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isLat_lam_of_matrix (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K) : IsLat (lam c) := by
  have hL : IsLat (intVec K m) := isLat_intVec m
  refine ⟨Submodule.FG.sup hL.1 (Submodule.FG.map _ hL.1), ?_⟩
  rw [eq_top_iff, ← hL.2]
  exact Submodule.span_mono (fun v hv => (le_sup_left : intVec K m ≤ lam c) hv)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

theorem _root_.GlobalTheory.T.unimodular_haar_right_invariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | exact GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | (intros; apply GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod <;> assumption)
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

theorem _root_.GlobalTheory.T.invariant_functional_eq_haar_multiple : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ), (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) → ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral | exact GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral | (intros; apply GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.multiplicity_reduction_diagonal_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | exact GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.hermitian_matrix_diagonalizable : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), cT σ h = h → ∃ (g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧ (∀ i, σ (d i) = d i) ∧ cT σ g * h * g = Matrix.diagonal d := by
  first | exact @GlobalTheory.CompanionTheory.HermDiag.herm_diag | exact GlobalTheory.CompanionTheory.HermDiag.herm_diag | (intros; apply GlobalTheory.CompanionTheory.HermDiag.herm_diag <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.cuspidal_of_unipotent_sums_vanish : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | exact GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char <;> assumption)
end
