module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.Bundle002
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.PolynomialDimension.MultinomialDepth.MonoCount
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Bundle001
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M

namespace LatticeBasis

variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem mem_intPol_iff (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  constructor
  · rintro ⟨f0, rfl⟩ m
    simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
    exact PadicInt.norm_le_one (AddMonoidAlgebra.coeff f0 m)
  · intro h
    have : (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
      intro a ha
      rw [Finset.mem_coe, mem_coeffs_iff] at ha
      obtain ⟨m, _, rfl⟩ := ha
      exact ⟨⟨x.coeff m, h m⟩, rfl⟩
    rw [← mem_range_map_iff_coeffs_subset] at this
    simpa [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range] using this

theorem exists_unit_coeff (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (hU : U ≠ ⊥) :
    ∃ x₀ ∈ U, ∃ m, x₀.coeff m = 1 ∧ x₀ ∈ IntPol p σ := by
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU
  have hne : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hx0 (support_eq_empty.mp h)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image x.support (fun m => ‖x.coeff m‖) hne
  have ha : x.coeff m ≠ 0 := mem_support_iff.mp hm
  refine ⟨(x.coeff m)⁻¹ • x, U.smul_mem _ hxU, m, ?_, ?_⟩
  · rw [MvPolynomial.coeff_smul, smul_eq_mul, inv_mul_cancel₀ ha]
  · rw [mem_intPol_iff]
    intro n
    rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, norm_inv]
    have hpos : 0 < ‖x.coeff m‖ := norm_pos_iff.mpr ha
    rw [inv_mul_le_iff₀ hpos, mul_one]
    by_cases hn : n ∈ x.support
    · exact hmax n hn
    · rw [notMem_support_iff.mp hn, norm_zero]
      exact hpos.le

theorem exists_family (d : ℕ) : ∀ (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])), FiniteDimensional ℚ_[p] U →
    Module.finrank ℚ_[p] U = d →
    ∃ (k : ℕ) (b : Fin k → MvPolynomial σ ℚ_[p]), LinearIndependent ℚ_[p] b ∧
      Submodule.span ℚ_[p] (Set.range b) = U ∧ (∀ i, b i ∈ IntPol p σ) ∧
      ∀ x ∈ U, x ∈ IntPol p σ → ∃ c : Fin k → ℚ_[p], (∀ i, ‖c i‖ ≤ 1) ∧ x = ∑ i, c i • b i := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hfd hd
    by_cases hU : U = ⊥
    · subst hU
      refine ⟨0, Fin.elim0, linearIndependent_empty_type, by simp, fun i => i.elim0, ?_⟩
      intro x hx _
      exact ⟨Fin.elim0, fun i => i.elim0, by simpa using hx⟩
    · obtain ⟨x₀, hx₀U, m, hm1, hx₀I⟩ := exists_unit_coeff U hU
      set U' : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) := U ⊓ LinearMap.ker (lcoeff ℚ_[p] m) with hU'
      have hle : U' ≤ U := inf_le_left
      have hx₀U' : x₀ ∉ U' := by
        intro h
        have : x₀.coeff m = 0 := by simpa using (Submodule.mem_inf.mp h).2
        rw [hm1] at this
        exact one_ne_zero this
      have hlt : U' < U := lt_of_le_of_ne hle (fun h => hx₀U' (h ▸ hx₀U))
      have hfd' : FiniteDimensional ℚ_[p] U' := Submodule.finiteDimensional_of_le hle
      have hrk : Module.finrank ℚ_[p] U' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨k, b, hli, hsp, hbI, hco⟩ := ih _ hrk U' hfd' rfl
      have hsplit : ∀ x ∈ U, x - x.coeff m • x₀ ∈ U' := by
        intro x hx
        refine Submodule.mem_inf.mpr ⟨U.sub_mem hx (U.smul_mem _ hx₀U), ?_⟩
        simp [hm1]
      refine ⟨k + 1, Fin.cons x₀ b, ?_, ?_, ?_, ?_⟩
      · rw [linearIndependent_finCons]
        exact ⟨hli, by rw [hsp]; exact hx₀U'⟩
      · rw [Fin.range_cons, Submodule.span_insert, hsp]
        apply le_antisymm
        · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₀U) hle
        · intro x hx
          have : x = x.coeff m • x₀ + (x - x.coeff m • x₀) := by abel
          rw [this]
          exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) (hsplit x hx)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx₀I
        · simpa using hbI j
      · intro x hx hxI
        have hc : ‖x.coeff m‖ ≤ 1 := (mem_intPol_iff x).mp hxI m
        have hI' : x - x.coeff m • x₀ ∈ IntPol p σ := by
          rw [mem_intPol_iff]
          intro n
          rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul, sub_eq_add_neg]
          refine (Padic.nonarchimedean _ _).trans (max_le ((mem_intPol_iff x).mp hxI n) ?_)
          rw [norm_neg, norm_mul]
          exact mul_le_one₀ hc (norm_nonneg _) ((mem_intPol_iff x₀).mp hx₀I n)
        obtain ⟨c, hc1, hxc⟩ := hco _ (hsplit x hx) hI'
        refine ⟨Fin.cons (x.coeff m) c, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hc
          · simpa using hc1 j
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hxc]
          abel

end LatticeBasis

theorem lattice_basis_polynomial : LatBasisPol := by
  intro p _ σ U hfd
  obtain ⟨k, b, hli, hsp, hbI, hco⟩ := LatticeBasis.exists_family (p := p) (σ := σ) _ U hfd rfl
  subst hsp
  refine ⟨k, Module.Basis.span hli, ?_, ?_⟩
  · intro i
    rw [Module.Basis.span_apply]
    exact hbI i
  · intro x hx i
    obtain ⟨c, hc1, hxc⟩ := hco x.1 x.2 hx
    have hx' : x = ∑ j, c j • Module.Basis.span hli j := by
      apply Subtype.ext
      rw [hxc]
      simp [Module.Basis.span_apply]
    rw [hx', Module.Basis.repr_sum_self]
    exact hc1 i

end Formalism.InvariantFactorPaths.PW
end

section

namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity

section gen

variable {K V V₁ V₂ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] {n : ℕ}

theorem glRel_of (G : GlW K V n) : GlRel G.E := by
  intro a b c d
  ext x
  have h := G.comm a b c d x
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [h]
  split_ifs <;> simp

def mapsInto (V₁ : Type) [AddCommGroup V₁] [Module K V₁] (W : Submodule K V₂) : Submodule K (V₁ →ₗ[K] V₂) where
  carrier := {φ | ∀ x, φ x ∈ W}
  add_mem' := fun {φ ψ} hφ hψ x => by rw [LinearMap.add_apply]; exact W.add_mem (hφ x) (hψ x)
  zero_mem' := fun x => by rw [LinearMap.zero_apply]; exact W.zero_mem
  smul_mem' := fun c φ hφ x => by rw [LinearMap.smul_apply]; exact W.smul_mem c (hφ x)

theorem hom_eig_zero [CharZero K] (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ)
    (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l) (z : Fin n) (k : ℤ) (φ : V₁ →ₗ[K] V₂) (hφ : ∀ x, φ x ∈ W)
    (he : homAct G₁.E G₂.E z z φ = (k : K) • φ) (hk : (l : ℤ) < |k|) : φ = 0 := by
  have key : ∀ μ x, φ (G₁.comp μ x) = 0 := by
    intro μ x
    by_contra hy
    have hx' : G₁.comp μ x ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hE : G₂.E z z (φ (G₁.comp μ x)) = ((k + μ z : ℤ) : K) • φ (G₁.comp μ x) := by
      have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ (G₁.comp μ x)) he
      simp only [homAct_apply, LinearMap.smul_apply] at h
      rw [G₁.diag, map_smul] at h
      rw [Int.cast_add, add_smul, ← h]
      abel
    have hc : ∀ ν, G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
      intro ν
      by_contra hν
      have e1 := G₂.comp_Ecc ν z (φ (G₁.comp μ x))
      rw [hE, map_smul] at e1
      have e2 : (((k + μ z : ℤ) : K) - ((ν z : ℤ) : K)) • G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
        rw [sub_smul, e1, sub_self]
      rcases smul_eq_zero.mp e2 with h | h
      · have h3 : k + μ z = ν z := by exact_mod_cast sub_eq_zero.mp h
        have h4 := hb μ ν (G₁.comp μ x) _ hx' hν (G₂.graded_of hW ν _ (hφ _)) (G₁.isWt_comp μ x)
          (G₂.isWt_comp ν _) z
        rw [← h3, add_sub_cancel_right] at h4
        omega
      · exact hν h
    apply hy
    have h := G₂.sum_comp (φ (G₁.comp μ x)) ∅ (fun ν _ => hc ν)
    simpa using h.symm
  ext x
  obtain ⟨S, hS⟩ := G₁.dec x

  rw [← G₁.sum_comp x S hS, map_sum, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun μ _ => key μ x

end gen

theorem homInv_of (h1 : InvInv) : HomInv := by
  intro K V₁ V₂ _ _ _ _ _ _ n G₁ G₂ W l hW hb φ hφ h0
  have hrel : GlRel (homAct G₁.E G₂.E) := hom_relation_holds K V₁ V₂ (Fin n) G₁.E G₂.E (glRel_of G₁) (glRel_of G₂)
  obtain ⟨c1, c2, c3⟩ := h1 K (V₁ →ₗ[K] V₂) (Fin n) (homAct G₁.E G₂.E) hrel l (mapsInto V₁ W)
    (fun a b ψ hψ x => by
      rw [homAct_apply]
      exact W.sub_mem (hW a b _ (hψ x)) (hψ _))
    (fun z k ψ hψ he hk => hom_eig_zero G₁ G₂ W l hW hb z k ψ hψ he hk)
    (List.finRange n) (List.nodup_finRange n) φ hφ (fun a _ => h0 a)
  refine ⟨fun a b x => ?_, c2, c3⟩
  have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ x) (c1 a (List.mem_finRange a) b (List.mem_finRange b))
  simp only [homAct_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.mp h).symm

theorem schurTrace_of_homInv (h2 : HomInv) : SchurTrace := by
  intro K V _ _ _ _ n G W l hW hfd hfW hb la h hh hhW hh0 φ h0
  have hUW : G.gS {h} ≤ W := G.gS_le (by simpa using hhW) hW
  have : FiniteDimensional K (G.gS {h}) := Submodule.finiteDimensional_of_le hUW
  obtain ⟨c1, -, c3⟩ := h2 K (G.gS {h}) (G.gS {h}) n (res G _ (G.gS_stable {h})) (res G _ (G.gS_stable {h})) ⊤ l
    (fun _ _ _ _ => Submodule.mem_top)
    (fun μ ν x y hx hy _ hwx hwy c => hb μ ν x y (fun e => hx (Subtype.ext e)) (fun e => hy (Subtype.ext e))
      (hUW x.2) (hUW y.2) (congrArg Subtype.val hwx) (congrArg Subtype.val hwy) c)
    φ (fun _ => Submodule.mem_top) h0
  generalize InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ = ψ
    at c1 c3 ⊢
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have hwt : (res G _ (G.gS_stable {h})).IsWt la ⟨h, hmem⟩ := Subtype.ext hh.1
  have hwψ : (res G _ (G.gS_stable {h})).IsWt la (ψ ⟨h, hmem⟩) :=
    Formalism.CountingSumsFrames.GlX.isWt_of_eig _ (fun c => by
      rw [← c1, (res G _ (G.gS_stable {h})).E_diag_of_isWt hwt c, map_smul])
  obtain ⟨c, hc⟩ := G.comp_top_of_mem hh (ψ ⟨h, hmem⟩).2
  have hc' : ((ψ ⟨h, hmem⟩ : G.gS {h}) : V) = c • h := by
    rw [← hc]; exact (congrArg Subtype.val hwψ).symm
  have hle : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker (ψ - c • LinearMap.id)) := by
    apply G.gS_le
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨⟨y, hmem⟩, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [sub_eq_zero]
      exact Subtype.ext hc'
    · rintro a b _ ⟨y, hy, rfl⟩
      refine ⟨(res G _ (G.gS_stable {h})).E a b y, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hy ⊢
      rw [c1, ← map_smul, ← map_sub, hy, map_zero]
  have hψ : ψ = c • LinearMap.id := by
    ext x
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hy
    rw [sub_eq_zero.mp hy]
    rfl
  have htr : LinearMap.trace K _ (ψ - φ) = 0 := hom_trace_holds K (G.gS {h}) (Fin n) _ _ c3
  have : Nontrivial (G.gS {h}) := ⟨⟨⟨h, hmem⟩, 0, fun e => hh0 (congrArg Subtype.val e)⟩⟩
  have hfr : (Module.finrank K (G.gS {h}) : K) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := G.gS {h})).ne'
  rw [map_sub, sub_eq_zero, hψ, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hψ, ← htr, mul_div_assoc, div_self hfr, mul_one]

theorem schurTrace_of (h1 : InvInv) : SchurTrace := schurTrace_of_homInv (homInv_of h1)

end Formalism.InvariantFactorPaths.PW
end
