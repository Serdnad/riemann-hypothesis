module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle034
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.normDom :
    UpperTheory.Gal.Join.NormDom := by
  intro k k' _ _ _ _ _ _ _ _ ι σ l N hN
  refine ⟨fun x => ?_, fun n t => ⟨fun ht i j hij => ?_, ?_, fun s ht hs i j hij => ?_⟩⟩
  · apply Units.ext
    apply ι.injective
    rw [hN.prod, hN.prod]
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by have := hN.cyc.pos; omega⟩
    subst hm
    have hord : σ^[m + 1] (x : k') = x := hN.cyc.ord x
    have hl : ∀ i, σ^[i] ((Units.map (σ : k' →* k') x : k'ˣ) : k') = σ^[i + 1] (x : k') := fun i => by
      rw [Function.iterate_succ_apply]
      rfl
    simp only [hl]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => σ^[i] (x : k')), hord]
    rfl
  · refine lt_of_not_ge fun h => ?_
    have h1 := (GlobalTheory.SplitWeil.nabs_le_iff (N (t j)) (N (t i))).2 h
    rw [hN.abs, hN.abs] at h1
    exact absurd h1 (not_le.2 (GlobalTheory.SplitWeil.nabs_lt_of_valuation_lt (ht i j hij)))
  · unfold deltaB
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    have e : nT n N t i / nT n N t j = N (t i / t j) := by
      rw [map_div]
      rfl
    rw [e, hN.abs]
  · have hj : valuation k' (s j : k') ≠ 0 := by simp
    have e : ∀ a, valuation k' (((t * s) a : k'ˣ) : k') = valuation k' (t a : k') * valuation k' (s a : k') := fun a => by
      simp
    rw [e, e]
    calc valuation k' (t i : k') * valuation k' (s i : k')
        ≤ valuation k' (t i : k') * valuation k' (s j : k') := mul_le_mul' le_rfl (hs i j hij)
      _ < valuation k' (t j : k') * valuation k' (s j : k') :=
        mul_lt_mul_of_pos_right (ht i j hij) (zero_lt_iff.2 hj)
end

section

noncomputable section

open ValuativeRel
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem indep {T : Type} [CommGroup T] (M : Submonoid T) (hM : ∀ t : T, ∃ s ∈ M, s * t ∈ M) (t₀ : T)
    (E E' : Multiset (T →* ℂˣ)) (c c' : ℂ) (hc : c ≠ 0)
    (h : ∀ t ∈ M, c * (E.map fun μ => (μ (t₀ * t) : ℂ)).sum = c' * (E'.map fun μ => (μ (t₀ * t) : ℂ)).sum) :
    ∀ μ ∈ E, μ ∈ E' := by
  classical
  let ρ : (T →* ℂˣ) → (M →* ℂ) := fun μ => (Units.coeHom ℂ).comp (μ.comp M.subtype)
  have hρm : ∀ μ (m : M), ρ μ m = (μ m : ℂ) := fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    intro μ ν hμν
    have hM' : ∀ m ∈ M, μ m = ν m := by
      intro m hm
      apply Units.ext
      have := DFunLike.congr_fun hμν ⟨m, hm⟩
      rw [hρm, hρm] at this
      exact this
    refine MonoidHom.ext fun t => ?_
    obtain ⟨s, hs, hst⟩ := hM t
    have e : t = s⁻¹ * (s * t) := by rw [inv_mul_cancel_left]
    rw [e, map_mul μ, map_mul ν, map_inv μ, map_inv ν, hM' s hs, hM' _ hst]
  have hli : LinearIndependent ℂ (fun μ : T →* ℂˣ => ((ρ μ : M →* ℂ) : M → ℂ)) :=
    (linearIndependent_monoidHom M ℂ).comp ρ hρinj
  intro μ hμ
  by_contra hμ'
  let S := (E + E').toFinset
  let g : (T →* ℂˣ) → ℂ := fun ν => (c * E.count ν - c' * E'.count ν) * (ν t₀ : ℂ)
  have conv : ∀ F : Multiset (T →* ℂˣ), F.toFinset ⊆ S → ∀ t : T,
      (F.map fun ν => (ν (t₀ * t) : ℂ)).sum = ∑ ν ∈ S, (F.count ν : ℂ) * ((ν t₀ : ℂ) * (ν t : ℂ)) := by
    intro F hF t
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hF]
    · apply Finset.sum_congr rfl
      intro ν _
      rw [nsmul_eq_mul, map_mul, Units.val_mul]
    · intro ν _ hν
      rw [Multiset.count_eq_zero.mpr (by simpa using hν)]
      simp
  have hsum : ∑ ν ∈ S, g ν • ((ρ ν : M →* ℂ) : M → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h1 := h m m.2
    rw [conv E (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inl (Multiset.mem_toFinset.mp hx)))) m,
      conv E' (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_toFinset.mp hx)))) m,
      Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    apply Finset.sum_congr rfl
    intro ν _
    rw [hρm]
    simp only [g]
    ring
  have h0 := linearIndependent_iff'.mp hli S g hsum μ
    (Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl hμ)))
  simp only [g, Multiset.count_eq_zero.mpr hμ', Nat.cast_zero, mul_zero, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc h3
    · exact (Multiset.count_pos.mpr hμ).ne' (by exact_mod_cast h3)
  · exact (μ t₀).ne_zero h2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private def domM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    Submonoid (Fin n → kˣ) where
  carrier := {t | Dom t}
  mul_mem' := by
    intro a b ha hb i j hij
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    exact mul_le_mul' (ha i j hij) (hb i j hij)
  one_mem' := by
    intro i j _
    simp

private theorem dom_translate (t : Fin n → kˣ) : ∃ s ∈ domM k n, s * t ∈ domM k n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, (domM k 0).one_mem, ?_⟩
    show Dom _
    intro i
    exact i.elim0
  · obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
      (fun p => valuation k ((t p.1 / t p.2 : kˣ) : k)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
    have hx1 : 1 ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) := by
      have := hp (⟨0, hn⟩, ⟨0, hn⟩) (Finset.mem_univ _)
      simpa using this
    have hxt : ∀ i j, valuation k (t i : k) ≤
        valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k) := by
      intro i j
      have := hp (i, j) (Finset.mem_univ _)
      have e : (t i : k) = ((t i / t j : kˣ) : k) * (t j : k) := by simp
      rw [e, map_mul]
      gcongr
    refine ⟨fun i => (t p.1 / t p.2) ^ (i : ℕ), ?_, ?_⟩
    · show Dom _
      intro i j hij
      simp only [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_pow_right₀ hx1 (le_of_lt hij)
    · show Dom _
      intro i j hij
      simp only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
      have hij' : (i : ℕ) + 1 ≤ j := hij
      have hpw := pow_le_pow_right₀ hx1 hij'
      calc valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) * valuation k (t i : k)
          ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) *
            (valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k)) := by
            gcongr
            exact hxt i j
        _ = valuation k ((t p.1 / t p.2 : kˣ) : k) ^ ((i : ℕ) + 1) * valuation k (t j : k) := by
            rw [pow_succ, mul_assoc]
        _ ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (j : ℕ) * valuation k (t j : k) := by
            gcongr

theorem charDom : CharDom := by
  intro k _ _ _ _ n t₀ E E' c c' hc h
  have hind := indep (domM k n) (fun t => dom_translate t) t₀ E E' c c' hc h
  refine ⟨hind, fun hE => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hE
  have := indep (domM k n) (fun t => dom_translate t) t₀ E 0 1 0 one_ne_zero
    (fun t ht => by rw [one_mul, hne t ht]; simp) μ hμ
  simp at this

end UpperTheory.Gal.Join
end
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join.KernelKilling

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem conj_entry (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹ := by
  have hinv : (((diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun i => ((t i : k))⁻¹ := by
    rw [← map_inv, val_diagT]
    congr 1
    funext i
    simp
  rw [Units.val_mul, Units.val_mul, hinv, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_close {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    {c B : ValueGroupWithZero k} (hc : c ≤ 1) (hB0 : B ≠ 0)
    (hB : ∀ i j, valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B)
    (t : Fin n → kˣ)
    (ht : ∀ i j, i < j → valuation k (t i : k) ≤ c * B⁻¹ * valuation k (t j : k)) (i j : Fin n) :
    valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ c ∧
      valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  rw [conj_entry]
  rw [mem_unipB] at hu
  obtain ⟨hlow, hdiag⟩ := hu
  have hc1 : c ≤ 1 := hc
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hne : i ≠ j := ne_of_lt hij
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne hne
    have hvj : valuation k (t j : k) ≠ 0 := by simp
    have key : valuation k ((t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹) ≤ c := by
      rw [map_mul, map_mul, map_inv₀]
      calc valuation k (t i : k) * valuation k ((u : Matrix (Fin n) (Fin n) k) i j) *
            (valuation k (t j : k))⁻¹
          ≤ c * B⁻¹ * valuation k (t j : k) * B * (valuation k (t j : k))⁻¹ := by
            gcongr
            · exact ht i j hij
            · exact hB i j
        _ = c * (B⁻¹ * B) * (valuation k (t j : k) * (valuation k (t j : k))⁻¹) := by
            simp only [mul_comm, mul_assoc, mul_left_comm]
        _ = c := by rw [inv_mul_cancel₀ hB0, mul_inv_cancel₀ hvj, mul_one, mul_one]
    rw [h1, sub_zero]
    exact ⟨key, le_trans key hc1⟩
  · rw [hdiag i, Matrix.one_apply_eq]
    have : (t i : k) * 1 * (t i : k)⁻¹ = 1 := by simp
    rw [this, sub_self, map_zero, map_one]
    exact ⟨zero_le', le_refl _⟩
  · have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
    rw [hlow i j hij, h1]
    simp

private theorem exists_bound (u : GL (Fin n) k) : ∃ B : ValueGroupWithZero k, B ≠ 0 ∧ ∀ i j,
    valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B ∧
      valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ B := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun p : Fin n × Fin n =>
    max (valuation k ((u : Matrix (Fin n) (Fin n) k) p.1 p.2))
      (valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2)))
  refine ⟨max M 1, ?_, fun i j => ⟨?_, ?_⟩⟩
  · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  · exact le_trans (le_trans (le_max_left _ _) (hM (i, j))) (le_max_left _ _)
  · exact le_trans (le_trans (le_max_right _ _) (hM (i, j))) (le_max_left _ _)

private theorem conj_mem {K : Subgroup (GL (Fin n) k)} (hK : IsOpen (K : Set (GL (Fin n) k)))
    {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) :
    ∃ r : ValueGroupWithZero k, r ≠ 0 ∧ ∀ t : Fin n → kˣ,
      (∀ i j, i < j → valuation k (t i : k) ≤ r * valuation k (t j : k)) →
        diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ K := by
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1
    (hK.mem_nhds K.one_mem)
  obtain ⟨B, hB0, hB⟩ := exists_bound u
  set c : ValueGroupWithZero k :=
    valuation k ((GroundTheory.Automorphic.GLnLocal.uniformizer k : k)) ^ m with hcdef
  have hc : c ≤ 1 := pow_le_one₀ zero_le'
    (le_of_lt (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k))
  have hc0 : c ≠ 0 := pow_ne_zero _ (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero k)
  have hui : u⁻¹ ∈ unipB k (Fin n) := inv_mem hu
  refine ⟨c * B⁻¹, mul_ne_zero hc0 (inv_ne_zero hB0), fun t ht => hm ?_⟩
  have hA := conj_close hu hc hB0 (fun i j => (hB i j).1) t ht
  have hI := conj_close hui hc hB0 (fun i j => (hB i j).2) t ht
  have hinv : (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹)⁻¹ =
      diagT k (Fin n) t * u⁻¹ * (diagT k (Fin n) t)⁻¹ := by group
  rw [SetLike.mem_coe, GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff,
    GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff, hinv]
  refine ⟨⟨fun i j => (Valuation.mem_integer_iff _ _).2 (hA i j).2,
    fun i j => (Valuation.mem_integer_iff _ _).2 (hI i j).2⟩, fun i j => (hA i j).1⟩

end UpperTheory.Gal.Join.KernelKilling

theorem UpperTheory.Gal.Join.kerKill :
    UpperTheory.Gal.Join.KerKill := by
  intro k _ _ _ _ n V _ _ π K hK e he v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, x, rfl⟩ := hw
    obtain ⟨r, hr, h⟩ := UpperTheory.Gal.Join.KernelKilling.conj_mem hK.co.2 u.2
    refine ⟨r, hr, fun t ht => ?_⟩
    have hk := he.inv _ (h t ht) (π (diagT k (Fin n) t) x)
    have hc : π (diagT k (Fin n) t * (u : GL (Fin n) k) * (diagT k (Fin n) t)⁻¹)
        (π (diagT k (Fin n) t) x) = π (diagT k (Fin n) t) (π (u : GL (Fin n) k) x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [hc] at hk
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hk, sub_self]
  | zero => exact ⟨1, one_ne_zero, fun t _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r₁, h₁, ha⟩ := ha
    obtain ⟨r₂, h₂, hb⟩ := hb
    refine ⟨min r₁ r₂, ?_, fun t ht => ?_⟩
    · rcases min_choice r₁ r₂ with h | h <;> rw [h] <;> assumption
    · rw [map_add (f := _), map_add (f := _),
        ha t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_left _ _) le_rfl),
        hb t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_right _ _) le_rfl), add_zero]
  | smul c a _ ha =>
    obtain ⟨r, hr, ha⟩ := ha
    exact ⟨r, hr, fun t ht => by rw [map_smul, map_smul, ha t ht, smul_zero]⟩
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.expLev :
    UpperTheory.Gal.Join.ExpLev := by
  intro k _ _ _ _ n V _ _ π hs y
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  let U : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  refine ⟨U, hs v, fun K hK => ?_⟩
  refine Submodule.mem_map_of_mem (p := fixed π K) ?_
  intro h
  have hv : π (h : GL (Fin n) k) v = v := hK h.2
  simpa using hv
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem lift_eigen {T V : Type} [CommGroup T] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V} (hψ : ∀ t, ρ t v = (ψ t : ℂ) • v)
    (hne : μ ≠ ψ) (hy : y ∉ Submodule.span ℂ {v})
    (hq : ∀ t, ρ t y - (μ t : ℂ) • y ∈ Submodule.span ℂ {v}) (hv : v ≠ 0) :
    ∃ z, z ≠ 0 ∧ ∀ t, ρ t z = (μ t : ℂ) • z :=
  _root_.UpperTheory.Reformulated.B.R4.lift_eigen ρ hψ hne hy hq hv

private theorem exists_eigenchars {T : Type} [CommGroup T] (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ T V), Module.finrank ℂ V = d →
    ∃ E : Multiset (T →* ℂˣ), (∀ t, LinearMap.trace ℂ V (ρ t) = (E.map fun χ => (χ t : ℂ)).sum) ∧
      ∀ μ, μ ∈ E ↔ ∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y := by
  induction d with
  | zero =>
    intro V _ _ _ ρ h
    haveI : Subsingleton V := Module.finrank_zero_iff.1 h
    refine ⟨0, fun t => ?_, fun μ => ?_⟩
    · simp [Subsingleton.elim (ρ t) 0]
    · simp [Subsingleton.elim _ (0 : V)]
  | succ d ih =>
    intro V _ _ _ ρ h
    haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [h]; exact d.succ_pos)
    obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ T V ρ fun a b => by
      rw [← map_mul, mul_comm, map_mul]
    have hst : ∀ g, Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap (ρ g) := fun g => by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hψ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hd : Module.finrank ℂ (V ⧸ Submodule.span ℂ {v}) = d := by
      have := (Submodule.span ℂ {v}).finrank_quotient_add_finrank
      rw [finrank_span_singleton hv, h] at this
      omega
    obtain ⟨E, h1, h2⟩ := ih _ (ρ.quotient _ hst) hd
    refine ⟨ψ ::ₘ E, fun t => ?_, fun μ => ⟨fun hμ => ?_, ?_⟩⟩
    · rw [GlobalTheory.IwahoriTraceProof.trace_eq_add_quot (ρ t) hv (hψ t) (ρ.quotient _ hst t) fun _ => rfl, h1,
        Multiset.map_cons, Multiset.sum_cons]
    · by_cases hne : μ = ψ
      · exact ⟨v, hv, hne ▸ hψ⟩
      obtain ⟨q, hq0, hq⟩ := (h2 μ).1 ((Multiset.mem_cons.1 hμ).resolve_left hne)
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine lift_eigen ρ hψ hne (fun hy => hq0 ((Submodule.Quotient.mk_eq_zero _).2 hy)) (fun t => ?_) hv
      refine (Submodule.Quotient.eq _).1 ?_
      exact hq t
    · rintro ⟨y, hy, hμ⟩
      by_cases hne : μ = ψ
      · exact hne ▸ Multiset.mem_cons_self _ _
      refine Multiset.mem_cons_of_mem ((h2 μ).2 ⟨Submodule.Quotient.mk y, fun h0 => hne ?_, fun t => ?_⟩)
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
        refine MonoidHom.ext fun t => Units.ext ?_
        have h3 := hμ t
        rw [map_smul, hψ, smul_comm, ← sub_eq_zero, ← sub_smul] at h3
        rcases smul_eq_zero.1 h3 with h3 | h3
        · exact (sub_eq_zero.1 h3).symm
        · exact absurd h3 hy
      · exact congrArg (Submodule.Quotient.mk (p := Submodule.span ℂ {v})) (hμ t)

theorem UpperTheory.Gal.Join.traceExp :
    UpperTheory.Gal.Join.TraceExp := by
  intro T X _ _ _ ρ P _ hP
  let R : Representation ℂ T P :=
    { toFun := fun t => (ρ t).restrict (hP t)
      map_one' := by
        ext y
        simp
      map_mul' := fun a b => by
        ext y
        simp }
  obtain ⟨E, h1, h2⟩ := exists_eigenchars (T := T) _ P R rfl
  refine ⟨E, fun t => ?_, fun μ => ?_⟩
  · rw [trIn, dite_eq_left (hP t)]
    exact h1 t
  · rw [h2]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0), fun t => congrArg Subtype.val (h t)⟩
    · rintro ⟨y, hyP, hy, h⟩
      exact ⟨⟨y, hyP⟩, fun h0 => hy (congrArg Subtype.val h0), fun t => Subtype.ext (h t)⟩
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.quotEmb :
    UpperTheory.Gal.Join.QuotEmb := by
  intro k _ _ _ _ n V _ _ π hπ hirr ω l hl0 hl
  exact GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr (torusChar ω) l hl0 hl
end
