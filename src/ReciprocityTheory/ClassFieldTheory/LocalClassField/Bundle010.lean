module

public import Mathlib.GroupTheory.PGroup
public import ReciprocityTheory.GroupCohomology.Bundle002
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle004
public import Lemmata.GeneralBFactUpperTerForm.Imports
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle008
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle006
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle009
public import ReciprocityTheory.GroupCohomology.Bundle001
public import ReciprocityTheory.GroupCohomology.Bundle008

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open ReciprocityTheory.Coh Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

abbrev resP (M : TRep R G) (U : Subgroup G) : Pair M (M.resSub U) :=
  Pair.res M U.subtype continuous_subtype_val

theorem pair_H_bijective {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : IsHomeomorph P.φ)
    (hu : IsHomeomorph P.u) (n : ℕ) : Bijective (P.hom.H n) :=
  Deg2.pair_bij P hφ hu n

theorem infRes2_exact (M : TRep R G) (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (Q : TRep R (G ⧸ N)) (P : Pair Q M) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((resP M N).hom.H 2) :=
  Deg2.exact2 M N Q P hN hP h1

theorem exists_normal_index_eq_prime {H : Type*} [Group H] [Finite H] [Nontrivial H] (l : ℕ) [Fact l.Prime]
    (hH : IsPGroup l H) : ∃ N : Subgroup H, N.Normal ∧ N.index = l :=
  Deg2.exists_normal_index l hH

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

namespace UnramifiedExtensions

variable {p}

theorem norm_sum_le_of_le {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  first | exact Bl.general_b_fact_upper_ter_form.goal1 .. | (apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption)

theorem norm_sum_eq_one {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (b : ι → Obar p)
    (hb : ∀ j, (b j : PadicAlgCl p) ∈ K) (i : ι) (hi : b i = 1) :
    ‖∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ = 1 := by
  have hs : ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) = ((∑ j, b j * ω j : Obar p) : PadicAlgCl p) := by
    push_cast; rfl
  rw [hs]
  refine le_antisymm (norm_le_one _) (not_lt.1 fun hlt => ?_)
  have h0 := (res_eq_zero_iff _).2 hlt

  rw [map_sum] at h0
  let c : ι → resK p K := fun j => ⟨res (b j), (mem_resK_iff K _).2 ⟨b j, hb j, rfl⟩⟩
  have h1 : ∑ j, c j • IsLocalRing.residue (Obar p) (ω j) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, map_mul]
  have h2 := Fintype.linearIndependent_iff.1 hω c h1 i
  have h3 : res (b i) = 0 := congrArg Subtype.val h2
  rw [hi, map_one] at h3
  exact one_ne_zero h3

end UnramifiedExtensions

theorem norm_le_norm_sum {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (a : ι → K) (i : ι) :
    ‖(a i : PadicAlgCl p)‖ ≤ ‖∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖) ⟨i, Finset.mem_univ i⟩
  refine (hm i (Finset.mem_univ i)).trans ?_
  by_cases h0 : (a m : PadicAlgCl p) = 0
  · rw [h0, norm_zero]; exact norm_nonneg _
  have hpos : 0 < ‖(a m : PadicAlgCl p)‖ := norm_pos_iff.2 h0
  have hle : ∀ j, ‖(a j : PadicAlgCl p) / (a m : PadicAlgCl p)‖ ≤ 1 := by
    intro j
    rw [norm_div, div_le_one hpos]
    exact hm j (Finset.mem_univ j)
  let b : ι → Obar p := fun j => ⟨(a j : PadicAlgCl p) / (a m : PadicAlgCl p), mem_Obar_iff.2 (hle j)⟩
  have h1 := UnramifiedExtensions.norm_sum_eq_one (K := K) ω hω b (fun j => K.div_mem (a j).2 (a m).2) m
    (Subtype.ext (div_self h0))
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)
      = (a m : PadicAlgCl p) * ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = (a m : PadicAlgCl p) * ((a j : PadicAlgCl p) / (a m : PadicAlgCl p) * (ω j : PadicAlgCl p))
    field_simp
  rw [h2, norm_mul, h1, mul_one]

namespace UnramifiedExtensions

variable {p} {K}

noncomputable def comb {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L) : (ι → K) →ₗ[ℚ_[p]] L where
  toFun a := ⟨∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p),
    L.sum_mem fun j _ => L.mul_mem (hKL (a j).2) (hL j)⟩
  map_add' a b := by
    apply Subtype.ext
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc, Finset.mul_sum]

theorem comb_injective {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) :
    Function.Injective (comb hKL ω hL) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  have h1 := norm_le_norm_sum p K ω hω a i
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) = 0 := congrArg Subtype.val ha
  rw [h2, norm_zero] at h1
  exact Subtype.ext (norm_le_zero_iff.1 h1)

noncomputable def resMod {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Submodule (resK p K) (kbar p) where
  carrier := (resK p L : Set (kbar p))
  add_mem' := fun ha hb => (resK p L).add_mem ha hb
  zero_mem' := (resK p L).zero_mem
  smul_mem' := fun c x hx => by
    rw [Subfield.smul_def, smul_eq_mul]
    exact (resK p L).mul_mem (resK_mono hKL c.2) hx

set_option synthInstance.maxHeartbeats 100000 in
theorem exists_lifts {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ ∃ ω : Fin f → Obar p, (∀ j, (ω j : PadicAlgCl p) ∈ L) ∧
      LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i)) := by
  have hfL : Finite (resK p L) := finite_resK L hL
  have hfW : Finite (resMod hKL) := hfL
  letI : Module.Finite (resK p K) (resMod hKL) := Module.Finite.of_finite
  have hcard : Nat.card (resMod hKL) = Nat.card (resK p K) ^ Module.finrank (resK p K) (resMod hKL) :=
    Module.natCard_eq_pow_finrank
  have hnt : Nontrivial (resMod hKL) :=
    ⟨⟨⟨1, (resK p L).one_mem⟩, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  refine ⟨Module.finrank (resK p K) (resMod hKL), Module.finrank_pos, hcard, ?_⟩
  let B := Module.finBasis (resK p K) (resMod hKL)
  have hex : ∀ i, ∃ x : Obar p, (x : PadicAlgCl p) ∈ L ∧ res x = (B i : kbar p) :=
    fun i => (mem_resK_iff L _).1 (B i).2
  choose ω h1 h2 using hex
  refine ⟨ω, h1, ?_⟩
  have h3 : (fun i => IsLocalRing.residue (Obar p) (ω i)) = (resMod hKL).subtype ∘ B := by
    funext i; exact h2 i
  rw [h3]
  exact B.linearIndependent.map' _ (Submodule.ker_subtype _)

theorem finrank_fun (hK : FiniteDimensional ℚ_[p] K) (f : ℕ) : Module.finrank ℚ_[p] (Fin f → K) = f * Module.finrank ℚ_[p] K := by
  rw [Module.finrank_pi_fintype]
  simp

end UnramifiedExtensions

theorem qK_le_pow_finrank (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ f * Module.finrank ℚ_[p] K ≤ Module.finrank ℚ_[p] L := by
  obtain ⟨f, hf, hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  refine ⟨f, hf, hq, ?_⟩
  rw [← UnramifiedExtensions.finrank_fun hK]
  exact LinearMap.finrank_le_finrank_of_injective (UnramifiedExtensions.comb_injective hKL ω h1 h2)

theorem exists_norm_eq_of_qK (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {f : ℕ} (hf : 0 < f) (hdeg : Module.finrank ℚ_[p] L = f * Module.finrank ℚ_[p] K)
    (h : qK p L = qK p K ^ f) {x : PadicAlgCl p} (hx : x ∈ L) : ∃ y ∈ K, ‖x‖ = ‖y‖ := by
  classical
  have hL : FiniteDimensional ℚ_[p] L := by
    apply Module.finite_of_finrank_pos
    rw [hdeg]
    exact Nat.mul_pos hf Module.finrank_pos
  obtain ⟨f', hf', hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  have hff : f' = f := Nat.pow_right_injective (one_lt_qK p K hK) (hq.symm.trans h)
  subst hff
  have hsurj : Function.Surjective (UnramifiedExtensions.comb hKL ω h1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((UnramifiedExtensions.finrank_fun hK f').trans hdeg.symm)).1 (UnramifiedExtensions.comb_injective hKL ω h1 h2)
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  have hxa : x = ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) := (congrArg Subtype.val ha).symm
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖)
    ⟨⟨0, hf⟩, Finset.mem_univ _⟩
  refine ⟨a m, (a m).2, le_antisymm ?_ ?_⟩
  · rw [hxa]
    refine UnramifiedExtensions.norm_sum_le_of_le _ _ (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖(a j : PadicAlgCl p)‖ * ‖(ω j : PadicAlgCl p)‖ ≤ ‖(a j : PadicAlgCl p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (UnramifiedExtensions.norm_le_one _) (norm_nonneg _)
      _ ≤ ‖(a m : PadicAlgCl p)‖ := by rw [mul_one]; exact hm j (Finset.mem_univ j)
  · rw [hxa]
    exact norm_le_norm_sum p K ω h2 a m

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

noncomputable section

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation R G M)

def qRho (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : Representation R (G ⧸ N) M :=
  QuotientGroup.lift N rho (fun σ hσ => LinearMap.ext (hN σ hσ))

abbrev qT (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : TRep R (G ⧸ N) where
  V := M
  rho := qRho N rho hN
  cont := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact hrho.comp (continuous_id.prodMk continuous_const)

variable {N rho}

theorem exists_desc1 (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : G → M) (hc : c ∈ Z1 rho) (h0 : ∀ σ ∈ N, c σ = 0) :
    ∃ c' : G ⧸ N → M, c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN) ∧ ∀ g, c' (QuotientGroup.mk g) = c g := by
  have hw : ∀ a b : G, QuotientGroup.leftRel N a b → c a = c b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h2 := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h0 _ h1, map_zero, add_zero] at h2
    exact h2.symm
  refine ⟨fun q => Quotient.liftOn' q c hw, ⟨?_, ?_⟩, fun g => rfl⟩
  · exact hc.1.quotient_liftOn' hw
  · intro a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    exact hc.2 g h

theorem inflation_mem_one_cocycles (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c' : G ⧸ N → M) (hc : c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN)) :
    (fun g : G => c' (QuotientGroup.mk g)) ∈ Z1 rho :=
  ⟨hc.1.comp QuotientGroup.continuous_mk, fun g h => hc.2 (QuotientGroup.mk g) (QuotientGroup.mk h)⟩

theorem apply_eq_zero_of_mem_H1ur (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : Z1 rho)
    (hc : (Submodule.Quotient.mk c : H1 rho) ∈ H1ur rho N) (σ : G) (hσ : σ ∈ N) : c.1 σ = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val c) : H1 (rho.comp N.subtype)) = 0 := hc
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 h1
  have h3 : c.1 σ = rho σ m - m := hm ⟨σ, hσ⟩
  rw [h3, hN σ hσ, sub_self]

theorem torsion_of_finite [Finite M] (m : M) : ∃ k : ℕ, 0 < k ∧ k • m = 0 :=
  ⟨Nat.card M, Nat.card_pos, card_nsmul_eq_zero'⟩

variable [CompactSpace (G ⧸ N)] [T2Space (G ⧸ N)] [TotallyDisconnectedSpace (G ⧸ N)] [Finite M]

theorem ker_frobenius_sub_id_eq_invariants (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : LinearMap.ker (rho s - LinearMap.id) = H0 rho := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, mem_riemannRochSpace_iff_regularAt_everywhere]
  refine ⟨fun h g => ?_, fun h => h s⟩
  set W := ProcyclicCohomology.stab (qT N rho hrho hN) m with hW
  have hWo : IsOpen (W : Set (G ⧸ N)) := ProcyclicCohomology.stab_isOpen (qT N rho hrho hN) m
  have hWc : IsClosed (W : Set (G ⧸ N)) := W.isClosed_of_isOpen hWo
  have hsW : (QuotientGroup.mk s : G ⧸ N) ∈ W := h
  have hz : (Subgroup.zpowers (QuotientGroup.mk s : G ⧸ N) : Set (G ⧸ N)) ⊆ W :=
    (Subgroup.zpowers_le.2 hsW)
  have htop : (W : Set (G ⧸ N)) = Set.univ := by
    rw [← hWc.closure_eq, ← Set.univ_subset_iff, ← hs.1.closure_eq]
    exact closure_mono hz
  have : (QuotientGroup.mk g : G ⧸ N) ∈ (W : Set (G ⧸ N)) := by rw [htop]; trivial
  exact this

theorem card_quot_range (u : M →ₗ[R] M) : Nat.card (M ⧸ LinearMap.range u) = Nat.card (LinearMap.ker u) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range u)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker u)
  rw [Nat.card_congr u.quotKerEquivRange.toEquiv] at h2
  have h3 : 0 < Nat.card (LinearMap.range u) := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left h3 h1).symm

theorem card_H1ur (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : Nat.card (H1ur rho N) = Nat.card (H0 rho) := by
  set P : Submodule R M := LinearMap.range (rho s - LinearMap.id) with hP
  let f : Z1 rho →ₗ[R] M ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 rho).subtype)
  have hker : (Bd1 rho).comap (Z1 rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker]
    change (Submodule.Quotient.mk (c.1 s) : M ⧸ P) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ : H1 rho →ₗ[R] M ⧸ P := ((Bd1 rho).comap (Z1 rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hinj0 : ∀ z ∈ H1ur rho N, φ z = 0 → z = 0 := by
    intro z hz hz0
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨c', hc', hcc⟩ := exists_desc1 hN c.1 c.2 (apply_eq_zero_of_mem_H1ur hN c hz)
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hz0
    obtain ⟨m, hm⟩ := hz0
    have h1 : c' (QuotientGroup.mk s) = rho s m - m := by rw [hcc, ← hm]; rfl
    have h2 := ProcyclicCohomology.cocycle_eq_of_apply (qT N rho hrho hN) hs.1 c' hc' m h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_contCoboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    change c.1 g = _
    rw [← hcc]
    exact h2 (QuotientGroup.mk g)
  have hbij : Bijective (fun x : H1ur rho N => φ x.1) := by
    constructor
    · intro x y hxy
      have h1 : φ (x.1 - y.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hxy
      exact Subtype.ext (sub_eq_zero.1 (hinj0 _ ((H1ur rho N).sub_mem x.2 y.2) h1))
    · intro y
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨c', hc', hcs⟩ := ProcyclicCohomology.exists_cocycle (qT N rho hrho hN) (ProcyclicCohomology.comm_of_dense hs.1) hs.1 hs.2 m
        (torsion_of_finite (M := M) m)
      have hZ := inflation_mem_one_cocycles hN c' hc'
      refine ⟨⟨Submodule.Quotient.mk ⟨_, hZ⟩, ?_⟩, ?_⟩
      · change (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val ⟨_, hZ⟩) :
          H1 (rho.comp N.subtype)) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        refine (mem_contCoboundaries1 _ _).2 ⟨0, fun σ => ?_⟩
        change c' (QuotientGroup.mk σ.1) = _
        rw [(QuotientGroup.eq_one_iff σ.1).2 σ.2, map_zero, sub_zero]
        have h1 : c' (1 * 1) = c' 1 + qRho N rho hN 1 (c' 1) := hc'.2 1 1
        rw [mul_one, map_one, Module.End.one_apply] at h1
        exact left_eq_add.1 h1
      · change φ (Submodule.Quotient.mk _) = _
        rw [hφ]
        exact congrArg _ hcs
  rw [Nat.card_eq_of_bijective _ hbij, hP, card_quot_range, ker_frobenius_sub_id_eq_invariants hrho hN hs]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles
end
