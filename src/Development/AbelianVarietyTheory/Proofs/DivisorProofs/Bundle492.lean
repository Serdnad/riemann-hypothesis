module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle248
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005

@[expose] public section

section

noncomputable section

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta CategoryTheory

namespace GlobalTheory.DlogSpan

theorem ker_finite_free {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {h : ℕ}
    (b : (Fin h → O) →ₗ[O] (Fin h → O)) :
    Module.Finite O (LinearMap.ker b) ∧ Module.Free O (LinearMap.ker b) := by
  have flat : ∀ S : Submodule O (Fin h → O), Module.Flat O S := fun S => by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have h1 : (a : O) • (x : Fin h → O) = 0 := congrArg Subtype.val ha
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero a.2)
  haveI := flat (LinearMap.range b)
  haveI : Module.Free O (LinearMap.range b) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property b.rangeRestrict LinearMap.id
    b.surjective_rangeRestrict
  have hs' : ∀ y, b (s y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let π : (Fin h → O) →ₗ[O] LinearMap.ker b :=
    (LinearMap.id - s ∘ₗ b.rangeRestrict).codRestrict _ fun x => by
      simp [LinearMap.mem_ker, hs']
  have hπ : Function.Surjective π := fun x => ⟨x, by
    apply Subtype.ext
    have h0 : b.rangeRestrict x = 0 := Subtype.ext x.2
    simp [π, h0]⟩
  haveI hfin : Module.Finite O (LinearMap.ker b) := Module.Finite.of_surjective π hπ
  haveI := flat (LinearMap.ker b)
  exact ⟨hfin, Module.free_of_flat_of_isLocalRing⟩

theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) : ζ - 1 ∣ (k : O) := by
  have h0 := hζ.geom_sum_eq_zero hk
  have h1 : (k : O) = -∑ i ∈ Finset.range k, (ζ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, h0]; simp
  rw [h1, dvd_neg]
  exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one ζ i

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

def pDivGroupOmegaBidualEquiv (G : PDivGroup p O) : G.omega ≃ₗ[O] G.dual.dual.omega :=
  LinearEquiv.ofLinear (omegaMap _ _ G.bidual.inv) (omegaMap _ _ G.bidual.hom)
    (by rw [← omegaMap_comp, Iso.inv_hom_id, omegaMap_id])
    (by rw [← omegaMap_comp, Iso.hom_inv_id, omegaMap_id])

theorem pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate (G : PDivGroup p O) (χ : G.dual.Tate) :
    pDivGroupOmegaBidualEquiv G (dlog G χ) = hodgeTate G.dual χ := by
  rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap]
  rfl

theorem finite_free_and_sq_smul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  intro p hp C _ _ _ v O _ _ _ _ _ ε hε hv hS G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨u₁, u₂, hS⟩ := hS
  obtain ⟨D, e, fil, lie, hR⟩ := hS G.dual ℤ_[p] (padicAction _)
  let Ψ : G.omega ≃ₗ[O] D.Fil := pDivGroupOmegaBidualEquiv G ≪≫ₗ fil
  obtain ⟨hfin, hfree⟩ := ker_finite_free D.bb
  haveI : Module.Finite O D.Fil := hfin
  haveI : Module.Free O D.Fil := hfree
  refine ⟨Module.Finite.equiv Ψ.symm, Module.Free.of_equiv Ψ.symm, fun w => ?_⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by
    have h := hε 1
    rw [pow_one] at h
    exact h
  obtain ⟨-, -, -, hb, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have hθ : WittVector.fontaineTheta O p (nu ε) = (root ε).untilt - 1 := by
    rw [nu, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
  have hal : ∀ χ : G.dual.Tate, D.al (toO e χ) = (Ψ ((u₁ : O) • dlog G χ) : Fin _ → O) := by
    intro χ
    rw [hR.al_eq, ← hodgeTate_eq_omegaMap, ← pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate, map_smul]
    rfl
  have key : ∀ y, ∃ s ∈ Submodule.span O (Set.range (dlog G)),
      D.al y = (Ψ s : Fin _ → O) := by
    intro y
    refine ⟨∑ i, y i • (u₁ : O) • dlog G (e.symm (Pi.single i 1)), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hy : y = ∑ i, y i • toO e (e.symm (Pi.single i 1)) := by
        ext j
        simp [toO, Finset.sum_apply, Pi.single_apply, apply_ite]
      conv_lhs => rw [hy]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hal, map_smul Ψ (y i), Submodule.coe_smul]
  obtain ⟨y, hy⟩ := hb (Ψ w) (Ψ w).2
  obtain ⟨s, hs, hys⟩ := key y
  have h1 : WittVector.fontaineTheta O p (nu ε) • w = s := by
    apply Ψ.injective
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, ← hy, hys]
  obtain ⟨c, hc⟩ := sub_one_dvd hζ hp.out.one_lt
  have h2 : (p : O) ^ 2 • w = ((p : O) * c) • s := by
    rw [← h1, hθ, smul_smul, pow_two]
    congr 1
    rw [mul_assoc, mul_comm c, ← hc]
  rw [h2]
  exact Submodule.smul_mem _ _ hs

end GlobalTheory.DlogSpan
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.EsymmVirt

theorem esymm_zero' (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + C a * X : ℂ[X])).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul]
    cases n with
    | zero => simp [ih, esymm_zero']
    | succ n => rw [coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ)
    (h : ∀ j : ℕ, 0 < j → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) (n : ℕ) :
    s.esymm n = t.esymm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [esymm_zero', esymm_zero']
    have h1 := GlobalTheory.multiset_newton_psum s n hn
    have h2 := GlobalTheory.multiset_newton_psum t n hn
    have h3 : ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * s.esymm i * (s.map (· ^ (n - i))).sum
        = ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * t.esymm i * (t.map (· ^ (n - i))).sum := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ioo] at hi
      rw [ih i hi.2, h (n - i) (by omega)]
    have h4 : ((-1) ^ (n + 1) * (n : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hn.ne')
    apply mul_left_cancel₀ h4
    linear_combination h2 - h1 + h n hn + h3

variable {G : Type} [Group G] [Finite G]

theorem one_mem_virt : (fun _ : G => (1 : ℂ)) ∈ Virt ℂ ℂ G := by
  simpa using (virt_mul_comap_conj_ind_linear G).2.2.2.2 1

theorem esymm_add_mem_virt {A B : G → Multiset ℂ}
    (hA : ∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G)
    (hB : ∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) (s : ℕ) :
    (fun g => (A g + B g).esymm s) ∈ Virt ℂ ℂ G := by
  have : (fun g => (A g + B g).esymm s) = ∑ i ∈ Finset.range (s + 1),
      (fun g => (A g).esymm i) * (fun g => (B g).esymm (s - i)) := by
    funext g
    simp [esymm_add, Finset.sum_apply]
  rw [this]
  exact sum_mem fun i _ => (virt_mul_comap_conj_ind_linear G).1 _ (hA _) _ (hB _)

theorem exists_multisets {φ : G → ℂ} (hφ : φ ∈ Virt ℂ ℂ G) :
    ∃ A B : G → Multiset ℂ, (∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G) ∧
      (∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) ∧
      ∀ g j, 0 < j → φ (g ^ j) + ((B g).map (· ^ j)).sum = ((A g).map (· ^ j)).sum := by
  have h0 : ∀ s, (fun _ : G => (0 : Multiset ℂ).esymm s) ∈ Virt ℂ ℂ G := by
    intro s
    cases s with
    | zero => simpa only [esymm_zero'] using one_mem_virt
    | succ s =>
      have : (fun _ : G => (0 : Multiset ℂ).esymm (s + 1)) = 0 := by
        funext g
        simp [Multiset.esymm, Multiset.powersetCard_zero_right]
      rw [this]
      exact zero_mem _
  induction hφ using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨n, ρ, hρ⟩ := (matrixChar_iff_isChar G a).2 ha
    refine ⟨fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots, fun _ => 0,
      fun s => isChar_mem_virt_complex (isChar_esymm_roots_charpoly G n s ρ), h0, fun g j _ => ?_⟩
    rw [hρ, map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly,
      GlobalTheory.CharpolyPow.roots_charpoly_pow]
    simp
  | zero => exact ⟨fun _ => 0, fun _ => 0, h0, h0, fun g j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    obtain ⟨A', B', hA', hB', h'⟩ := hy
    refine ⟨fun g => A g + A' g, fun g => B g + B' g, esymm_add_mem_virt hA hA',
      esymm_add_mem_virt hB hB', fun g j hj => ?_⟩
    simp only [Pi.add_apply, Multiset.map_add (f := _), Multiset.sum_add]
    linear_combination h g j hj + h' g j hj
  | neg x _ hx =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    refine ⟨B, A, hB, hA, fun g j hj => ?_⟩
    simp only [Pi.neg_apply]
    linear_combination - h g j hj

theorem esymm_mem_virt : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ),
    φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) →
    ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  intro G _ _ φ x hφ hx s
  obtain ⟨A, B, hA, hB, h⟩ := exists_multisets hφ
  have he : ∀ g n, (x g + B g).esymm n = (A g).esymm n := fun g n =>
    esymm_eq_of_psum_eq _ _ (fun j hj => by
      rw [Multiset.map_add (f := _), Multiset.sum_add, ← hx g j hj, h g j hj]) n
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have : (fun g => (x g).esymm s) = (fun g => (A g).esymm s) - ∑ i ∈ Finset.range s,
        (fun g => (x g).esymm i) * (fun g => (B g).esymm (s - i)) := by
      funext g
      have := he g s
      rw [esymm_add, Finset.sum_range_succ, Nat.sub_self, esymm_zero', mul_one] at this
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply]
      linear_combination this
    rw [this]
    exact sub_mem (hA s) (sum_mem fun i hi =>
      (virt_mul_comap_conj_ind_linear G).1 _ (ih i (Finset.mem_range.1 hi)) _ (hB _))

end GlobalTheory.EsymmVirt
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem esymm_pow_twelve_div_mem : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f →
    (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ,
    (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  intro ι _ act w N f R τ₀ hN hact hf hq hj k
  have hF : IsFam act ((12 : ℕ) * (w : ℤ)) fun i τ => f i τ ^ 12 :=
    (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.2.2.1 w f 12 hf
  obtain ⟨-, -, -, -, hpow, hsp⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hqS : QAll (· ∈ R) N fun τ =>
      ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ ^ 12 :=
    (hsp (Finset ι) (Finset.powersetCard k Finset.univ) (fun t τ => ∏ i ∈ t, f i τ ^ 12)
      fun t _ => (hsp ι t (fun i τ => f i τ ^ 12) fun i _ => hpow (f i) 12 (hq i)).2).1
  have hw : ((k : ℤ) * (((12 : ℕ) : ℤ) * (w : ℤ))) = 12 * ((k * w : ℕ) : ℤ) := by
    push_cast; ring
  obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant R N (k * w) _ hN (fun γ => by
    have h := (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hF γ).2 k
    rw [hw] at h
    exact h) hqS
  have hD : DD τ₀ ^ (k * w) ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ₀)
  have hsum : (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) =
      (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12) / DD τ₀ ^ (k * w) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2, ← pow_mul,
      mul_comm w k]
  have h0 := hPe τ₀
  rw [hsum, h0, mul_div_cancel_left₀ _ hD, Polynomial.eval_eq_sum_range]
  exact R.sum_mem fun i _ => R.mul_mem (hP i) (R.pow_mem hj i)

end GlobalTheory.QFam
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem hc_one_orth_hfree : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b →
    ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  intro F _ _ a b n hn hb α Y hY hF
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  have hn0 : 0 < n := by omega
  have hcl : ∀ g x : GL (Fin n) F, Y (x⁻¹ * g * x) = Y g :=
    (virt_mul_comap_conj_ind_linear (GL (Fin n) F)).2.2.1 Y (isChar_mem_virt_complex hY)
  let Pm : GL (Fin n) F → Prop := fun x => ∀ i j : Fin n, (j : ℕ) + 1 < n →
    (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j
  have hR : ∀ (M : Matrix (Fin n) (Fin n) F) (x : GL (Fin n) F), Pm x → ∀ i j : Fin n, (j : ℕ) + 1 < n →
      (M * (x : Matrix (Fin n) (Fin n) F)) i j = M i j := by
    intro M x hx i j hj
    rw [Matrix.mul_apply]
    simp only [hx _ j hj]
    rw [← Matrix.mul_apply, Matrix.mul_one]
  let H : Subgroup (GL (Fin n) F) :=
    { carrier := {x | Pm x}
      one_mem' := fun i j _ => by simp
      mul_mem' := fun {x y : GL (Fin n) F} hx hy i j hj => by
        show ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _
        rw [Units.val_mul, hR _ y hy i j hj]; exact hx i j hj
      inv_mem' := fun {x : GL (Fin n) F} hx i j hj => by
        have h1 : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have := hR ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) x hx i j hj
        rw [h1] at this
        exact this.symm }
  have hH : ∑ᶠ u : H, Y u = 0 := by
    have := hF hn0
    rw [← finsum_set_coe_eq_finsum_mem] at this
    exact this
  have hcos := char_coset_sum_eq_zero (GL (Fin n) F) Y hY H hH
  haveI : Fintype H := Fintype.ofFinite _
  let f : GL (Fin n) F → ℂ := fun x => if InPar a x then α (tlG a x) else 0
  have hent : ∀ x : GL (Fin n) F, ∀ h ∈ H, ∀ i j : Fin n, (j : ℕ) < a →
      ((x * h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = (x : Matrix (Fin n) (Fin n) F) i j := by
    intro x h hh i j hj
    rw [Units.val_mul]
    exact hR _ h hh i j (by omega)
  have hinv : ∀ x : GL (Fin n) F, ∀ h ∈ H, f (x * h) = f x := by
    intro x h hh
    have h1 : InPar a (x * h) ↔ InPar a x := by
      unfold InPar
      constructor
      · intro H' i j hj hi; rw [← hent x h hh i j hj]; exact H' i j hj hi
      · intro H' i j hj hi; rw [hent x h hh i j hj]; exact H' i j hj hi
    have h2 : tlG a (x * h) = tlG a x := by
      unfold tlG
      congr 1
      funext i j
      unfold tl ent
      split_ifs with hij
      · exact hent x h hh _ _ j.2
      · rfl
    simp only [f, h1, h2]
  have hS : ∑ x, f x * star (Y x) = 0 := by
    have hh : ∀ h : H, ∑ x, f x * star (Y x) = ∑ x, f x * star (Y (x * h)) := by
      intro h
      refine Fintype.sum_equiv (Equiv.mulRight (h : GL (Fin n) F)).symm _ _ ?_
      intro x
      simp only [Equiv.coe_mulRight, Equiv.mulRight_symm]
      rw [inv_mul_cancel_right, hinv x _ (H.inv_mem h.2)]
    have hsum : (Fintype.card H : ℂ) * ∑ x, f x * star (Y x) = 0 := by
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      rw [Finset.sum_congr rfl fun h _ => hh h, Finset.sum_comm]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← Finset.mul_sum, ← star_sum]
      have := hcos x
      rw [finsum_eq_sum_of_fintype] at this
      rw [this, star_zero, mul_zero]
    have hc0 : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp hsum).resolve_left hc0
  have hmain : ∀ y : GL (Fin n) F, ∑ x, f (y⁻¹ * x * y) * star (Y x) = 0 := by
    intro y
    rw [← hS]
    refine Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _ _ ?_
    intro x
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, hcl]
  have hg : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := fun y => by
    ext i j; simp [gal]
  rw [finsum_eq_sum_of_fintype]
  unfold hc hcTw
  simp only [hg, mul_one, finsum_eq_sum_of_fintype]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [← Finset.mul_sum]
  have := hmain y
  simp only [f, mul_assoc] at this
  rw [this, mul_zero]

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HCChar

theorem gal_id_apply {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem hc_isChar : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  intro F _ _ a b n hn α β hα hβ
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  haveI : Finite (GL (Fin n) F) := inferInstance
  have h1 : IsChar ℂ ℂ (fun p : H => α (π p).1) := by
    obtain ⟨m, ρ, hρ⟩ := hα
    exact ⟨m, ρ.comp ((MonoidHom.fst _ _).comp π), fun p => hρ _⟩
  have h2 : IsChar ℂ ℂ (fun p : H => β (π p).2) := by
    obtain ⟨m, ρ, hρ⟩ := hβ
    exact ⟨m, ρ.comp ((MonoidHom.snd _ _).comp π), fun p => hρ _⟩
  have hψ : IsChar ℂ ℂ ((fun p : H => α (π p).1) * (fun p : H => β (π p).2)) := isChar_mul_complex h1 h2
  have hind := isChar_ind ℂ ℂ (GL (Fin n) F) H _ hψ
  convert hind using 1
  funext x
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hH x).symm))
  unfold hc hcTw ind
  rw [hcard]
  congr 1
  apply finsum_congr
  intro y
  rw [gal_id_apply]
  unfold ext0
  by_cases hy : y⁻¹ * x * y ∈ H
  · rw [dite_eq_left hy, if_pos ((hH _).1 hy), Pi.mul_apply, hπ]
  · rw [dite_eq_right hy, if_neg (fun e => hy ((hH _).2 e))]

end GlobalTheory.Shin.HCChar
end
