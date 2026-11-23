module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.QuadT

section Abstract

variable {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (u l : ι → κ → A)

theorem core_term (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (a b : ι) (i j k : κ) :
    u a k * l a i * (u b j * l b k) =
      u a k * l b k * (l a i * u b j) - if k = j then u a k * l a i else 0 := by
  have e1 : u b j * l b k = l b k * u b j - if k = j then 1 else 0 := by
    rw [h b k j]; abel
  have e2 : u a k * l a i * (l b k * u b j) = u a k * l b k * (l a i * u b j) := by
    calc _ = u a k * (l a i * l b k) * u b j := by simp only [mul_assoc]
      _ = u a k * (l b k * l a i) * u b j := by rw [hll]
      _ = _ := by simp only [mul_assoc]
  rw [e1, mul_sub, e2]
  split_ifs <;> simp

theorem core1 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (i j : κ) :
    ∑ k, (∑ a, u a k * l a i) * (∑ b, u b j * l b k) =
      (∑ a, ∑ b, (∑ k, u a k * l b k) * (l a i * u b j)) -
        (Fintype.card ι : ℂ) • ∑ a, u a j * l a i := by
  simp only [Finset.sum_mul, Finset.mul_sum, core_term u l h hll, Finset.sum_sub_distrib]
  congr 1
  · calc (∑ k, ∑ b, ∑ a, u a k * l b k * (l a i * u b j))
          = ∑ b, ∑ k, ∑ a, u a k * l b k * (l a i * u b j) := Finset.sum_comm
        _ = ∑ b, ∑ a, ∑ k, u a k * l b k * (l a i * u b j) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]

theorem core2 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0) (i j : κ) :
    ∑ a, l a i * u a j = ∑ a, u a j * l a i + if i = j then (Fintype.card ι : ℂ) • (1 : A) else 0 := by
  simp only [h, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

end Abstract

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

section Main

variable {V ι κ : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (u l : ι → κ → Module.End ℂ V) (E : ι → ι → Module.End ℂ V) (G : κ → κ → Module.End ℂ V)

theorem quad_main (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c)
    (hE : ∀ a b, E a b = ∑ c, u a c * l b c + (if a = b then (Fintype.card κ : ℂ) / 2 else 0) • 1)
    (hG : ∀ c d, G c d = ∑ a, u a c * l a d + (if c = d then (Fintype.card ι : ℂ) / 2 else 0) • 1)
    (x : ℂ) (i j : κ) :
    qop (fun c d => -G d c) ((Fintype.card κ : ℂ) / 2 - x)
        ((Fintype.card ι : ℂ) ^ 2 / 4 + (x - (Fintype.card κ : ℂ) / 2) * (Fintype.card ι : ℂ) / 2) i j =
      ∑ a, ∑ b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) := by
  have hR : ∀ a b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) =
      (∑ c, u a c * l b c) * (l a i * u b j) +
        (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) := by
    intro a b
    rw [hE]
    split_ifs <;> simp [add_mul, sub_mul, sub_smul, smul_mul_assoc, add_sub_assoc]
  simp only [hR, Finset.sum_add_distrib]
  have hD : ∑ a, ∑ b, (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) =
      ((Fintype.card κ : ℂ) / 2 - x) • ∑ a, l a i * u a j := by
    simp [ite_smul, Finset.sum_ite_eq, Finset.smul_sum]
  have h1 := core1 u l h hll i j
  rw [eq_sub_iff_add_eq] at h1
  rw [hD, core2 u l h, ← h1]
  simp only [qop, hG]
  simp only [neg_mul_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, Finset.sum_add_distrib, ite_smul, zero_smul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    module
  · simp only [hij, Ne.symm hij, if_false]
    module

end Main

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

theorem fockAct1_Eab_eq {P Q R S : ℕ} (a b : Ix P Q) :
    fockAct1 P Q R S (Eab a b) =
      ∑ c, raiB (a, c) * lowB (b, c) + (if a = b then (Fintype.card (Ix R S) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct1_Eab]
  simp only [omE, Prod.mk.injEq, and_true, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem fockAct2_Eab_eq {P Q R S : ℕ} (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) =
      ∑ a, raiB (a, c) * lowB (a, d) + (if c = d then (Fintype.card (Ix P Q) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct2_Eab]
  simp only [omE, Prod.mk.injEq, true_and, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem negT_fockAct2_quad : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f,
    qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  intro P Q R S x
  refine ⟨(Fintype.card (Ix R S) : ℂ) / 2 - x,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 + (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2,
    fun i j f => ?_⟩
  have key : qop (negT (units (fockAct2 P Q R S))) ((Fintype.card (Ix R S) : ℂ) / 2 - x)
      ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 +
        (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2) i j =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab a b) - (if a = b then x else 0) • 1) *
        (lowB (a, i) * raiB (b, j)) :=
    quad_main (fun (a : Ix P Q) (c : Ix R S) => raiB (a, c)) (fun a c => lowB (a, c))
      (fun a b => fockAct1 P Q R S (Eab a b)) (fun c d => fockAct2 P Q R S (Eab c d))
      (fun b c e => by simp [GlobalTheory.FockCasimir.lowB_mul_raiB])
      (fun a c b e => GlobalTheory.FockCasimir.lowB_comm _ _) fockAct1_Eab_eq fockAct2_Eab_eq x i j
  rw [key, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [Module.End.mul_apply]
  apply Submodule.subset_span
  refine ⟨Eab a b, (lowB (a, i) * raiB (b, j)) f, ?_⟩
  by_cases hab : a = b
  · subst hab
    simp [Eab, Matrix.trace_single_eq_same]
  · simp [hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab]

end GlobalTheory.HoweR.QuadT
end
end

section

noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.HoweR.MultOne

variable {P Q R S : ℕ}

theorem coinv_stable2 (x : ℂ) (Y : Mat R S) {v : Pol P Q R S} (hv : v ∈ coinv P Q R S x) :
    fockAct2 P Q R S Y v ∈ coinv P Q R S x := by
  induction hv using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Y f, ?_⟩
    rw [map_sub, map_smul, GlobalTheory.FockAlg.MinFirst.fockAct1_fockAct2_commute]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem fockHarmonicsSecondMember_of_jointShape_highestWeight {x : ℚ} {μ' : Ix R S → ℚ} (hJ : JointShape P Q R S (fun _ => x) μ') {f : Pol P Q R S}
    (h2 : f ∈ harm2 P Q R S) (hc : f ∈ GlobalTheory.FockScalarType.charSub P Q R S x)
    (hw : f ∈ hwSub (fockAct2 P Q R S) μ') : f ∈ harm1 P Q R S := by
  by_cases h0 : f = 0
  · subst h0; intro Z _; simp [minusPart]
  obtain ⟨d, hd, hdf⟩ := isSide_two.homog_of_hw Prod.swap_bijective ⟨h0, hw⟩ ((mem_harm2 f).1 h2)
  have hdeg := (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hJ hJ).2
  intro Z hZ
  rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) f).2]
  by_cases hd2 : d < 2
  · exact dnOp_low _ d hd2 f hdf
  by_contra hne
  have h1 := isSide_one.degW_le Function.bijective_id (dnOp_homog _ d f hdf)
    (GlobalTheory.FockScalarType.isHW_of_mem hne (GlobalTheory.FockScalarType.dnOp_mem_charSub hZ hdf hc))
  rw [hdeg, ← hd] at h1
  have e : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ d)]; ring
  rw [e] at h1
  linarith

end GlobalTheory.HoweR.MultOne

namespace GlobalTheory.HoweR


open GlobalTheory.HoweR.MultOne in
theorem hw_le_span_sup_coinv : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' →
    ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  intro P Q R S x μ' hJ
  set L := hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
    Submodule.span ℂ (jointHarm P Q R S) with hL
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 (GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hJ)
  refine ⟨v.1, fun g hg => ?_⟩
  set C := coinv P Q R S (x : ℂ) with hC
  let pr := C.mkQ
  have hker : ∀ w, pr w = 0 ↔ w ∈ C := fun w => by rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hpr1 : ∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f := by
    intro X f
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact (hker _).2 (Submodule.subset_span ⟨X, f, rfl⟩)
  have hpr2 : ∀ Y w w', pr w = pr w' → pr (fockAct2 P Q R S Y w) = pr (fockAct2 P Q R S Y w') := by
    intro Y w w' h
    rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact (hker _).2 (coinv_stable2 _ Y ((hker _).1 h))
  have hPC : ∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0 := by
    intro Z hZ f; rw [hpr1, GlobalTheory.HarmLift.trace_PC hZ, mul_zero, zero_smul]
  obtain ⟨h, hh, hprh⟩ := GlobalTheory.HarmLift.lemA P Q R S _ pr hPC g
  obtain ⟨H0, hfin, hH0, hharm, hs1, hs2⟩ := GlobalTheory.HarmLift.lemB P Q R S h hh
  obtain ⟨ι, hιIP, hιinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  let A : Set (Module.End ℂ (Pol P Q R S)) :=
    {a | (∃ X, IsKC X ∧ a = fockAct1 P Q R S X) ∨ ∃ Y, IsKC Y ∧ a = fockAct2 P Q R S Y}
  have hadj := GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hιIP
  obtain ⟨c, hc, hcpr, hceig⟩ := GlobalTheory.HarmLift.lemC (Pol P Q R S) (Pol P Q R S ⧸ C) _ ι hιinj pr H0 hfin A
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w hw
      exacts [hs1 X hX w hw, hs2 Y hY w hw])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w _ hw
      · rw [hpr1, hw, smul_zero]
      · rw [hpr2 Y w 0 (by rw [hw, map_zero]), map_zero, map_zero])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, GlobalTheory.HarmLift.isKC_adjZ hX, rfl⟩, hadj.2.1 X⟩
      · exact ⟨_, Or.inr ⟨_, GlobalTheory.HarmLift.isKC_adjZ hY, rfl⟩, hadj.2.2 Y⟩)
    h hH0
  rw [hprh] at hcpr
  have hcc : c ∈ GlobalTheory.FockScalarType.charSub P Q R S x := fun X hX =>
    hceig _ (Or.inl ⟨X, hX, rfl⟩) _ (by rw [hpr1])
  have hcw : c ∈ hwSub (fockAct2 P Q R S) μ' := by
    have hg2 := hg
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hg2 ⊢
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]
      refine hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) _ ?_
      rw [hpr2 (Eab a a) c g hcpr, hg2.1 a, map_smul, hcpr]
    · have hs : sameBlock a b := by
        revert hab; rcases a with a | a <;> rcases b with b | b <;> simp [posC, sameBlock]
      rw [hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) 0
        (by rw [hpr2 (Eab a b) c g hcpr, hg2.2 a b hab, map_zero, zero_smul]), zero_smul]
  have hcJ : c ∈ jointHarm P Q R S := ⟨hharm c hc, fockHarmonicsSecondMember_of_jointShape_highestWeight hJ (hharm c hc) hcc hcw⟩
  have hcL : c ∈ L := by
    by_cases h0 : c = 0
    · rw [h0]; exact L.zero_mem
    exact ⟨⟨(GlobalTheory.FockScalarType.isHW_of_mem h0 hcc).2, hcw⟩, Submodule.subset_span hcJ⟩
  obtain ⟨t, ht⟩ := hv ⟨c, hcL⟩
  have hct : c = t • v.1 := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  have hgc : g - c ∈ C := (hker _).1 (by rw [map_sub, hcpr, sub_self])
  rw [← sub_add_cancel g c, add_comm]
  exact Submodule.add_mem_sup (hct ▸ Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)) hgc

end GlobalTheory.HoweR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem pol_comp_equiv {ι : Type} [Fintype ι] (τ : ι ≃ ι) (φ : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => φ (n ∘ τ.symm)) = FibreProj.pol φ := by
  classical
  unfold FibreProj.pol
  refine Fintype.sum_equiv (Equiv.finsetCongr τ) _ _ fun S => ?_
  simp only [Equiv.finsetCongr_apply, Finset.card_map]
  congr 2
  funext i
  simp

theorem mixArch_iso_symm_congr : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → mixArch L M hr = mixArch L' M hr) ∧ (∀ τ : Equiv.Perm (Fin e), mixArch (fun a => L (τ a)) M hr = mixArch L M hr) ∧ ∀ (M' : HermLB q) (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), M'.div hr' = M.div hr → (∀ σ, Set.EqOn (logNorm (M'.φ σ) r') (logNorm (M.φ σ) r) (offSupp q σ (M.div hr))) → mixArch L M' hr' = mixArch L M hr := by
  intro k _ Y _ q e L M r hr
  refine ⟨fun L' hL => ?_, fun τ => ?_, fun M' r' hr' hd hn => ?_⟩
  · have h : ∀ n, (comb L n).archInt M e hr = (comb L' n).archInt M e hr := fun n =>
      by simp only [HermLB.archInt, (isometric_comb_congr hL n).chernInt_eq]
    simp only [mixArch, h]
  · have h : ∀ n, (comb (fun a => L (τ a)) (n ∘ τ)).archInt M e hr = (comb L n).archInt M e hr := fun n => by
      have iso : (comb (fun a => L (τ a)) (n ∘ τ)).Isometric (comb L n) := by
        refine HermLB.icls_eq_iff.1 ?_
        rw [icls_comb, icls_comb]
        exact Fintype.sum_equiv τ _ _ fun a => by simp
      simp only [HermLB.archInt, iso.chernInt_eq]
    simp only [mixArch]
    rw [← pol_comp_equiv τ.symm (fun n => (comb (fun a => L (τ a)) n).archInt M e hr)]
    simp only [Equiv.symm_symm, h]
  · have h : ∀ n, (comb L n).archInt M' e hr' = (comb L n).archInt M e hr := fun n => by
      simp only [HermLB.archInt, hd]
      exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (hn σ)
    simp only [mixArch, h]

end GlobalTheory.MixHt
end
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.JointKer

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem dual_contr (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (ν : Module.Dual ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    ν (GlobalTheory.TensorFactorUnique.contr f w y) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update f w ν)) y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.TensorFactorUnique.contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem contr_atPl (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (L : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    GlobalTheory.TensorFactorUnique.contr f w (atPl w L y) = L (GlobalTheory.TensorFactorUnique.contr f w y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, atPl_tprod, GlobalTheory.TensorFactorUnique.contr_tprod, GlobalTheory.TensorFactorUnique.contr_tprod,
      map_smul, Function.update_self, LinearMap.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem atPl_eq_zero_of_common (w : T) (F : Set (Module.End ℂ (V w))) (g : Module.End ℂ (V w))
    (hg : ∀ v, (∀ L ∈ F, L v = 0) → g v = 0) (y : ⨂[ℂ] i, V i) (hy : ∀ L ∈ F, atPl w L y = 0) :
    atPl w g y = 0 := by
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib
  intro f
  have hv : g (GlobalTheory.TensorFactorUnique.contr f w y) = 0 := hg _ fun L hL => by rw [← contr_atPl, hy L hL, map_zero]
  have h := dual_contr f w (f w) (atPl w g y)
  rw [contr_atPl, hv, map_zero, Function.update_eq_self] at h
  exact h.symm

theorem atPl_sub_one (w : T) (p : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    atPl w (p - 1) y = atPl w p y - y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, LinearMap.sub_apply, Module.End.one_apply,
      MultilinearMap.map_update_sub, Function.update_eq_self, smul_sub]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]; abel

theorem exists_proj {M : Type} [AddCommGroup M] [Module ℂ M] (A : Submodule ℂ M) :
    ∃ π : Module.End ℂ M, (∀ v, π v ∈ A) ∧ ∀ v ∈ A, π v = v := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype _)
  refine ⟨A.subtype ∘ₗ g, fun v => (g v).2, fun v hv => ?_⟩
  have := congrArg (fun h => ((h ⟨v, hv⟩ : A) : M)) hg
  simpa using this

end GlobalTheory.HoweR.JointKer

namespace GlobalTheory.HoweR

open JointKer

theorem mem_tensAll_of_killed : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)),
    (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) →
    y ∈ tensAll H := by
  intro T _ _ V _ _ L H hH y hy
  choose p hpK hpid using fun w => exists_proj (H w)
  have hfix : ∀ w, atPl w (p w) y = y := by
    intro w
    have h0 := atPl_eq_zero_of_common w (L w) (p w - 1) (fun v hv => by
        rw [LinearMap.sub_apply, Module.End.one_apply, hpid w v (hH w v hv), sub_self]) y (hy w)
    rw [atPl_sub_one] at h0
    exact sub_eq_zero.1 h0
  have hmap : ∀ s : Finset T,
      PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a s ha ih =>
      have e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) =
          fun w => (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) a (p a) w) ∘ₗ
            (if w ∈ s then p w else LinearMap.id) := by
        funext w
        by_cases hw : w = a
        · subst hw
          simp [ha]
        · simp [hw, Function.update_of_ne hw]
      rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
      exact hfix a
  have hy' : PiTensorProduct.map p y = y := by
    have := hmap Finset.univ
    simpa using this
  rw [← hy']
  clear hy' hmap hfix hy
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _, rfl⟩)
  | add x z hx hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hz

end GlobalTheory.HoweR

end
end
