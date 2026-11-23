module

public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaGen

variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

def fIwasawaH (x y : Fin n → L) : L := ∑ j, σ (x (Fin.rev j)) * y j

def fIwasawaUn (M : Matrix (Fin n) (Fin n) L) : Prop := cT σ M * antiJ L n * M = antiJ L n

theorem fIwasawa_antiJ (i j : Fin n) : antiJ L n i j = if j = Fin.rev i then 1 else 0 := by
  unfold antiJ
  try simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ (j = Fin.rev i) := by
    rw [Fin.ext_iff, Fin.val_rev]; omega
  by_cases h : j = Fin.rev i
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

private theorem cT_apply' (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ M i j = σ (M j i) := by
  first | rfl | simp [cT] | (unfold cT; simp)

private theorem cT_mul_adelic_iwasawa_hecke (A B : Matrix (Fin n) (Fin n) L) : cT σ (A * B) = cT σ B * cT σ A := by
  ext i j

  simp only [cT_apply', Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem fIwasawa_gram (M : Matrix (Fin n) (Fin n) L) (a b : Fin n) :
    (cT σ M * antiJ L n * M) a b = fIwasawaH σ (fun i => M i a) (fun i => M i b) := by
  unfold fIwasawaH
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev k)]
  · simp [fIwasawa_antiJ, cT_apply']
  · intro l _ hl
    have : k ≠ Fin.rev l := fun h => hl (by rw [h, Fin.rev_rev])
    simp [fIwasawa_antiJ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem fIwasawa_H_single_left (p : Fin n) (w : Fin n → L) :
    fIwasawaH σ (Pi.single p 1) w = w (Fin.rev p) := by
  unfold fIwasawaH
  rw [Finset.sum_eq_single (Fin.rev p)]
  · simp
  · intro j _ hj
    have : Fin.rev j ≠ p := fun h => hj (by rw [← h, Fin.rev_rev])
    simp [Pi.single_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem fIwasawa_un_of_isometry (M : Matrix (Fin n) (Fin n) L)
    (h : ∀ x y, fIwasawaH σ (M *ᵥ x) (M *ᵥ y) = fIwasawaH σ x y) : fIwasawaUn σ M := by
  have hc : ∀ a : Fin n, (fun i => M i a) = M *ᵥ Pi.single a 1 := by
    intro a; ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold fIwasawaUn
  ext a b
  rw [fIwasawa_gram, hc a, hc b, h, fIwasawa_H_single_left, fIwasawa_antiJ]
  by_cases hb : b = Fin.rev a
  · subst hb; simp
  · simp [Pi.single_apply, hb, Ne.symm hb]

theorem fIwasawa_un_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaUn σ A) (hB : fIwasawaUn σ B) :
    fIwasawaUn σ (A * B) := by
  unfold fIwasawaUn at *
  rw [cT_mul_adelic_iwasawa_hecke, show cT σ B * cT σ A * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B by
    simp only [Matrix.mul_assoc], hA, hB]

theorem fIwasawa_antiJ_mul_antiJ : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [fIwasawa_antiJ, fIwasawa_antiJ, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  · intro k _ hk
    simp [fIwasawa_antiJ, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

def fIwasawaInv (M : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  antiJ L n * cT σ M * antiJ L n

theorem fIwasawa_inv_mul (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    fIwasawaInv σ M * M = 1 := by
  unfold fIwasawaInv
  unfold fIwasawaUn at hM
  rw [show antiJ L n * cT σ M * antiJ L n * M = antiJ L n * (cT σ M * antiJ L n * M) by
    simp only [Matrix.mul_assoc], hM, fIwasawa_antiJ_mul_antiJ]

theorem fIwasawa_mul_inv (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    M * fIwasawaInv σ M = 1 := by
  have h := fIwasawa_inv_mul σ M hM
  first
  | exact mul_eq_one_comm.mp h
  | (rw [← Matrix.inv_eq_left_inv h]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h))

def fIwasawaMk (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) : GU σ n :=
  ⟨⟨M, fIwasawaInv σ M, fIwasawa_mul_inv σ M hM, fIwasawa_inv_mul σ M hM⟩, hM⟩

theorem fIwasawa_mk_val (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    (((fIwasawaMk σ M hM : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = M := rfl

theorem fIwasawa_mem_un (g : GU σ n) :
    fIwasawaUn σ (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := g.2

end FIwasawaGen

end Formalism.UG.P
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Lattice

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem easyc_inclE_mem (e : E) (he : e ∈ intOE E) :
    inclE (F := F) R e ∈ tensInt (F := F) R (intOE E) S₂ := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, he⟩, rfl⟩

theorem easyc_single_mem (i : n) :
    (Pi.single i (1 : E) : n → E) ∈ stdLat (n := n) (A := E) (𝓞 E) := by
  rw [mem_stdLat_iff']
  intro k
  by_cases hk : k = i
  · subst hk; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hk]⟩

theorem easyc_latS_std :
    latS (F := F) R (tensInt (F := F) R (intOE E) S₂) (stdLat (n := n) (A := E) (𝓞 E)) =
      stdLat (n := n) (A := E ⊗[F] R) ↥(tensInt (F := F) R (intOE E) S₂) := by
  apply le_antisymm
  · rw [latS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_stdLat_iff']
    intro i
    have hxi := (mem_stdLat_iff' (R := 𝓞 E) x).1 hx i
    have hm : x i ∈ intOE E := by
      obtain ⟨y, hy⟩ := hxi
      exact ⟨y, hy⟩
    exact ⟨⟨_, easyc_inclE_mem R S₂ (x i) hm⟩, rfl⟩
  · intro x hx
    rw [mem_stdLat_iff'] at hx
    choose s hs using hx
    have hx : x = ∑ i, s i • (fun j => inclE (F := F) R ((Pi.single i (1 : E) : n → E) j)) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · simp [← hs j, Algebra.smul_def]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨_, easyc_single_mem i, rfl⟩

end Lattice

theorem level_subgroup_finite_adelic_standard : Formalism.UG.LevelAfLStd := by
  intro F E _ _ _ _ _ n _ _ σ J
  unfold levelAfL levelAf
  rw [easyc_latS_std]

end Formalism.UG.P
end
end

section

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem conv_mul_right {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₂ : IsBiInv K f₂) (g : G) (b : K) : conv K f₁ f₂ (g * b) = conv K f₁ f₂ g := by
  unfold conv
  congr 1
  funext x
  have h := hf₂ 1 b (x.out⁻¹ * g)
  simp only [OneMemClass.coe_one, one_mul] at h
  rw [← mul_assoc, h]

theorem conv_mul_left {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) (a : K) (g : G) :
    conv K f₁ f₂ ((a : G) * g) = conv K f₁ f₂ g := by
  have key : ∀ y : G ⧸ K, ∃ c : K, ((a : G) • y).out = (a : G) * y.out * c := by
    intro y
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * y.out)
    refine ⟨c, ?_⟩
    have e : (a : G) • y = (QuotientGroup.mk ((a : G) * y.out) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [e, hc]
  unfold conv
  refine (finsum_comp_equiv (MulAction.toPerm (a : G) : Equiv.Perm (G ⧸ K))).symm.trans ?_
  congr 1
  funext y
  obtain ⟨c, hc⟩ := key y
  simp only [MulAction.toPerm_apply]
  rw [hc, hf₁ a c y.out]
  have e2 : ((a : G) * y.out * c)⁻¹ * ((a : G) * g) = ((c⁻¹ : K) : G) * (y.out⁻¹ * g) * ((1 : K) : G) := by
    simp only [InvMemClass.coe_inv, OneMemClass.coe_one, mul_one]
    group
  rw [e2, hf₂]

theorem conv_biInv {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : IsBiInv K (conv K f₁ f₂) := by
  intro a b g
  rw [conv_mul_right K f₁ f₂ hf₂ ((a : G) * g) b, conv_mul_left K f₁ f₂ hf₁ hf₂ a g]

theorem conv_finDosetSupp {k : Type} [CommRing k] {K : Subgroup G} (hK : IsCommensurated K)
    (f₁ f₂ : G → k) (hs₁ : FinDosetSupp K f₁) (hs₂ : FinDosetSupp K f₂) :
    FinDosetSupp K (conv K f₁ f₂) := by
  classical
  have hX := finite_support_cosets hK hs₁
  obtain ⟨S₂, hS₂⟩ := hs₂
  set T : Set G := ⋃ t ∈ (S₂ : Set G), ⋃ x ∈ {x : G ⧸ K | f₁ x.out ≠ 0},
    ⋃ y ∈ {y : G ⧸ K | ∃ a b : K, y.out = (a : G) * t * b}, {x.out * y.out} with hTdef
  have hT : T.Finite :=
    S₂.finite_toSet.biUnion fun t _ => hX.biUnion fun x _ =>
      (finite_cosets_in_doset hK t).biUnion fun y _ => Set.finite_singleton _
  refine ⟨hT.toFinset, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (finsum_eq_zero_of_forall_eq_zero h)
  have h1 : f₁ x.out ≠ 0 := left_ne_zero_of_mul hx
  have h2 : f₂ (x.out⁻¹ * g) ≠ 0 := right_ne_zero_of_mul hx
  obtain ⟨t, ht, a, b, hab⟩ := hS₂ _ h2
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * t)
  refine ⟨x.out * (QuotientGroup.mk ((a : G) * t) : G ⧸ K).out, ?_, 1, c⁻¹ * b, ?_⟩
  · rw [Set.Finite.mem_toFinset, hTdef]
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨t, ht, x, h1, _, ⟨a, c, hc⟩, rfl⟩
  · rw [hc]
    have e : g = x.out * (x.out⁻¹ * g) := by group
    rw [e, hab]
    simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    group

theorem hecke_convolution_mem_holds : Formalism.UG.HeckeConvMem := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂
  have h1 : IsBiInv K f₁ ∧ FinDosetSupp K f₁ := hf₁
  have h2 : IsBiInv K f₂ ∧ FinDosetSupp K f₂ := hf₂
  show IsBiInv K (conv K f₁ f₂) ∧ FinDosetSupp K (conv K f₁ f₂)
  exact ⟨conv_biInv K f₁ f₂ h1.1 h2.1, conv_finDosetSupp hK f₁ f₂ h1.2 h2.2⟩

theorem convolution_count_holds : Formalism.UG.ConvCount := by
  classical
  intro G _ K k _ hK a b g
  set S : Set (G ⧸ K) := {x : G ⧸ K | x.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ∧
    x.out⁻¹ * g ∈ DoubleCoset.doubleCoset b (K : Set G) K} with hSdef
  have hfin : S.Finite := by
    refine (finite_cosets_in_doset hK a).subset fun x hx => ?_
    obtain ⟨h, hh, c, hc, e⟩ := DoubleCoset.mem_doubleCoset.1 hx.1
    exact ⟨⟨h, hh⟩, ⟨c, hc⟩, e⟩
  have hterm : ∀ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) =
      if x ∈ S then 1 else 0 := by
    intro x
    simp only [dosetInd, Set.indicator_apply, Pi.one_apply, hSdef, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  show ∑ᶠ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = _
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [Finset.sum_congr rfl (fun x hx => if_pos (hfin.mem_toFinset.1 hx))]
    simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hx (if_neg h)

end Formalism.UG.P
end
end
