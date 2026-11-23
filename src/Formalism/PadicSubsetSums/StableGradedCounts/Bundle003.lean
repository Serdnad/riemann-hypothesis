module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Mathlib.RingTheory.Finiteness.Prod
public import Lemmata.GeneralBFactSecondVersion.Imports
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

@[expose] public section

section

namespace Formalism.IrreducibleCountingLemmas.TOP

private theorem tsum_mul_inv_pow_succ_eq_div_sub_one (ℓ : ℕ) (H : ℝ) (hℓ : (2 : ℝ) ≤ ℓ) :
    ∑' j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = H / ((ℓ : ℝ) - 1) := by
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hl0 : (ℓ : ℝ) ≠ 0 := by positivity
  have hl1 : (ℓ : ℝ) - 1 ≠ 0 := by intro h; linarith
  have e : ∀ j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = (H * (ℓ : ℝ)⁻¹) * ((ℓ : ℝ)⁻¹) ^ j := by
    intro j; ring
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e2 : (1 : ℝ) - (ℓ : ℝ)⁻¹ = ((ℓ : ℝ) - 1) / ℓ := by field_simp
  rw [e2]
  field_simp

theorem carryFloorLeGeom : SgLe := by
  intro f _ ℓ h H hℓ hH i
  unfold sg
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeom : Summable (fun j : ℕ => (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left ((H : ℝ) * (ℓ : ℝ)⁻¹)
    refine this.congr ?_
    intro j; ring
  have hle : ∀ j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) ≤
      (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1) := by
    intro j
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hH _) (by positivity)
  have hnn : ∀ j : ℕ, 0 ≤ (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) :=
    fun j => by positivity
  have hs : Summable (fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)) :=
    hgeom.of_nonneg_of_le hnn hle
  have h1 := hs.tsum_le_tsum hle hgeom
  rw [tsum_mul_inv_pow_succ_eq_div_sub_one ℓ H hℓ'] at h1
  exact (Int.floor_le _).trans h1

end Formalism.IrreducibleCountingLemmas.TOP
end

section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

section
variable {G R : Type} [TopologicalSpace G] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private def CoeffCont (P : G → R[X]) : Prop := ∀ j, Continuous fun g => (P g).coeff j

private theorem CoeffCont.const (p : R[X]) : CoeffCont (fun _ : G => p) := by
  intro j
  exact continuous_const

private theorem CoeffCont.mul {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g * Q g := by
  intro j
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hP x.1).mul (hQ x.2)

private theorem CoeffCont.sub {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g - Q g := by
  intro j
  simp only [Polynomial.coeff_sub]
  exact (hP j).sub (hQ j)

private theorem CoeffCont.sum {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∑ i ∈ s, P i g := by
  intro j
  simp only [Polynomial.finsetSum_coeff]
  exact continuous_finsetSum _ fun i hi => hP i hi j

private theorem CoeffCont.prod {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∏ i ∈ s, P i g := by
  classical
  revert hP
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using CoeffCont.const (G := G) (1 : R[X])
  · intro a s ha ih hP
    have h1 := hP a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    have h3 := CoeffCont.mul h1 h2
    simpa only [Finset.prod_insert ha] using h3

private theorem CoeffCont.C {f : G → R} (hf : Continuous f) :
    CoeffCont fun g => Polynomial.C (f g) := by
  intro j
  by_cases h : j = 0
  · subst h
    simpa using hf
  · simpa [Polynomial.coeff_C, h] using (continuous_const : Continuous fun _ : G => (0 : R))

theorem continuous_coeff_charpolyRev {n : ℕ} {r : G → Matrix (Fin n) (Fin n) R}
    (hr : Continuous r) (j : ℕ) : Continuous fun g => (Matrix.charpolyRev (r g)).coeff j := by
  have hsmul : ∀ (u : ℤˣ) {Q : G → R[X]}, CoeffCont Q → CoeffCont fun g => u • Q g := by
    intro u Q hQ j
    simp only [Units.smul_def, Polynomial.coeff_smul]
    exact (hQ j).const_smul (u : ℤ)
  have h : CoeffCont fun g => Matrix.charpolyRev (r g) := by
    simp only [Matrix.charpolyRev, Matrix.det_apply]
    refine CoeffCont.sum _ fun σ _ => ?_
    refine hsmul _ (CoeffCont.prod _ fun i _ => ?_)
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact CoeffCont.sub (CoeffCont.const _) (CoeffCont.mul (CoeffCont.const _) (CoeffCont.C (hr.matrix_elem _ _)))
  exact h j

end

theorem charpolyCoeffClosure : CharpolyCoeffClosure := by
  intro G _ R _ _ _ X _ n r T D hr hT hD hDT g j
  have hc : Continuous fun g => (fun x => (Matrix.charpolyRev (r x g)).coeff j) :=
    continuous_pi fun x => continuous_coeff_charpolyRev (hr x) j
  have hcl : IsClosed {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := hT.preimage hc
  have hsub : D ⊆ {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := fun g hg => hDT g hg j
  have hcs := hcl.closure_subset_iff.mpr hsub
  exact hcs (by rw [hD.closure_eq]; exact Set.mem_univ g)

end Formalism.IrreducibleCountingLemmas.Z
end

section

namespace Formalism.IrreducibleCountingLemmas.TOP

theorem geomRatioBound : SgRange := by
  intro ℓ s b H hH h1 h2 h3
  have hs0 : (0 : ℝ) < s - 1 := by linarith
  have hlt : s - 1 < (ℓ : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hspos : (0 : ℝ) < s := by linarith
  have step1 : H / ((ℓ : ℝ) - 1) ≤ H / (s - 1) := by
    rw [div_le_div_iff₀ hl0 hs0]
    nlinarith [mul_le_mul_of_nonneg_left hlt.le hH]
  have step2 : H / (s - 1) ≤ 2 * b / s := by
    rw [div_le_div_iff₀ hs0 hspos]
    linarith
  exact step1.trans step2

end Formalism.IrreducibleCountingLemmas.TOP
end

section

open scoped NumberField

namespace Formalism.IrreducibleCountingLemmas.Z

theorem degree_one_split : DegreeOneSplit := by
  intro F E _ _ _ _ _ h2 P _ hP hf he
  classical
  set p : Ideal (𝓞 F) := P.under (𝓞 F) with hp
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : P.inertiaDeg (𝓞 F) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨inferInstance, ⟨rfl⟩⟩
  have hpos : ∀ q : p.primesOver (𝓞 E), 1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := by
    intro q
    have : q.1.IsPrime := q.2.1
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := 𝓞 F) q.1) (Ideal.inertiaDeg_pos q.1 (𝓞 F))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨P, hPmem⟩ : p.primesOver (𝓞 E)))] at hsum
  simp only [he, hf1, mul_one] at hsum
  have hrest : ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)),
      q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = 1 := by omega
  have hle : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≤ 1 := by
    calc _ = ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => hpos q
      _ = 1 := hrest
  have hge : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hrest
    simp at hrest
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hle hge
  have key : Fintype.card { x // x ∈ p.primesOver (𝓞 E) } = 2 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact key

end Formalism.IrreducibleCountingLemmas.Z
end

section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

theorem padicValNat_finset_prod {ι : Type} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i ≠ 0) : padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp [Nat.padicValNat_def]) ?_
  intro a t ha ih h
  have hrest : ∀ i ∈ t, f i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
  rw [Finset.prod_insert ha, Finset.sum_insert ha,
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (h a (Finset.mem_insert_self a t)) (Finset.prod_ne_zero_iff.mpr hrest),
    ih hrest]

private theorem pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt (q r i : ℕ) (hq : 0 < q) (hi : i < r) :
    q ^ r - q ^ i = q ^ i * (q ^ (r - i) - 1) := by
  have h1 : q ^ r = q ^ i * q ^ (r - i) := by rw [← pow_add, Nat.add_sub_cancel' hi.le]
  have h2 : 1 ≤ q ^ (r - i) := Nat.one_le_pow _ _ hq
  obtain ⟨k, hk⟩ : ∃ k, q ^ (r - i) = k + 1 := ⟨q ^ (r - i) - 1, (Nat.sub_add_cancel h2).symm⟩
  rw [h1, hk]
  simp [mul_add]

theorem padicValNat_prod_pow_sub (g q r : ℕ) [Fact g.Prime] (hq : 2 ≤ q) :
    padicValNat g (∏ i ∈ Finset.range r, (q ^ r - q ^ i)) =
      (∑ i ∈ Finset.range r, i) * padicValNat g q +
        ∑ a ∈ Finset.Icc 1 r, padicValNat g (q ^ a - 1) := by
  have hq0 : 0 < q := by omega
  have hbig : ∀ i ∈ Finset.range r, q ^ (r - i) - 1 ≠ 0 := by
    intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have h3 : q ≤ q ^ (r - i) := by
      simpa using Nat.pow_le_pow_right hq0 (show 1 ≤ r - i by omega)
    omega
  have hne : ∀ i ∈ Finset.range r, q ^ r - q ^ i ≠ 0 := by
    intro i hi
    rw [pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi)]
    exact Nat.mul_ne_zero (pow_ne_zero _ hq0.ne') (hbig i hi)
  have term : ∀ i ∈ Finset.range r, padicValNat g (q ^ r - q ^ i) =
      i * padicValNat g q + padicValNat g (q ^ (r - i) - 1) := by
    intro i hi
    rw [pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hq0.ne') (hbig i hi), Nat.padicValNat_def, Nat.multiplicity_pow, ← Nat.padicValNat_def]
  rw [padicValNat_finset_prod g _ _ hne, Finset.sum_congr rfl term, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  congr 1
  apply Finset.sum_nbij' (fun i => r - i) (fun a => r - a)
  all_goals intro a ha
  all_goals (try simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢)
  all_goals (first | rfl | omega)

theorem card_GL_zmod (q r : ℕ) [Fact q.Prime] :
    Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) =
      ∏ i ∈ Finset.range r, (q ^ r - q ^ i) := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [Matrix.card_GL_field, ZMod.card]
  exact Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i) r

theorem padicValCardGeneralLinear : GLCardVal := by
  unfold GLCardVal
  intro g g' r instg instg' hne
  have hg : g.Prime := instg.out
  have hg' : g'.Prime := instg'.out
  constructor
  · rw [card_GL_zmod, padicValNat_prod_pow_sub g g r hg.two_le, Nat.padicValNat_def, Nat.Prime.multiplicity_self,
      mul_one, Finset.sum_range_id, Finset.sum_eq_zero, add_zero]
    intro a ha
    rw [Nat.padicValNat_def]
    apply multiplicity_eq_zero_of_not_dvd
    intro hd
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have h1 : g ∣ g ^ a := dvd_pow_self g (by omega)
    have h2 : 1 ≤ g ^ a := Nat.one_le_pow _ _ hg.pos
    have h3 : g ∣ g ^ a - (g ^ a - 1) := by
      first
        | exact Nat.dvd_sub' h1 hd
        | exact Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self h2] at h3
    exact hg.one_lt.ne' (Nat.dvd_one.mp h3)
  · rw [card_GL_zmod, padicValNat_prod_pow_sub g g' r hg'.two_le]
    have h0 : padicValNat g g' = 0 :=
      by
        rw [Nat.padicValNat_def]
        exact multiplicity_eq_zero_of_not_dvd fun hd => hne ((Nat.prime_dvd_prime_iff_eq hg hg').mp hd)
    rw [h0, mul_zero, zero_add]

end Formalism.IrreducibleCountingLemmas.WindowSums
end

section

noncomputable section
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.Z.BN

def cp (k : Type) {A : Type} (V : Type) [Field k] [Ring A] [Algebra k A] [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] (a : A) : k[X] :=
  (Algebra.lsmul k k V a).charpoly

section
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W S : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup S] [Module A S]

theorem cp_congr [FiniteDimensional k V] [FiniteDimensional k W] (e : V ≃ₗ[A] W) (a : A) :
    cp k V a = cp k W a := by
  unfold cp
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k) (Algebra.lsmul k k V a)]
  congr 1
  ext w
  simp [LinearEquiv.conj_apply]

theorem cp_prod [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    cp k (V × W) a = cp k V a * cp k W a := by
  unfold cp
  rw [← LinearMap.charpoly_prodMap]
  congr 1

theorem exists_ne_zero_hom [FiniteDimensional k W] [IsSemisimpleModule A W] [IsSimpleModule A S]
    (h : ∀ a : A, (∀ w : W, a • w = 0) → ∀ s : S, a • s = 0) : ∃ f : W →ₗ[A] S, f ≠ 0 := by
  exact Bl.general_b_fact_second_version.goal1 (k := k) h

instance (N : Submodule A V) [FiniteDimensional k V] : FiniteDimensional k N :=
  Module.Finite.of_injective (N.subtype.restrictScalars k) N.subtype_injective

instance (N : Submodule A V) [FiniteDimensional k V] : FiniteDimensional k (V ⧸ N) :=
  Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective

end

theorem mul_eq_one_of_covolume_identity {k A : Type} [Field k] [Ring A] [Algebra k A] : ∀ (n : ℕ) (V W : Type)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W], Module.finrank k V = n →
    IsSemisimpleModule A V → IsSemisimpleModule A W →
    (∀ a : A, cp k V a = cp k W a) → Nonempty (V ≃ₗ[A] W) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ _ _ _ _ hn hV hW h
  have hdim : Module.finrank k V = Module.finrank k W := by
    have := congrArg natDegree (h 0)
    simpa [cp, LinearMap.charpoly_natDegree] using this
  by_cases hV0 : Subsingleton V
  · have hW0 : Subsingleton W := by
      rw [← Module.finrank_zero_iff (R := k)] at hV0 ⊢
      omega
    exact ⟨0⟩
  · rw [not_subsingleton_iff_nontrivial] at hV0
    obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A V
    have key : ∀ a : A, (∀ w : W, a • w = 0) → ∀ s : S, a • s = 0 := by
      intro a ha s
      by_contra hne
      obtain ⟨u, hu⟩ := IsSimpleModule.toSpanSingleton_surjective A hne s
      have hu' : (u * a) • s = s := by simpa [mul_smul] using hu
      have hcW : Algebra.lsmul k k W (u * a) = 0 := by
        ext w
        simp [ha]
      have hnil : IsNilpotent (Algebra.lsmul k k V (u * a)) := by
        rw [LinearMap.isNilpotent_iff_charpoly]
        have h1 := h (u * a)
        unfold cp at h1
        rw [h1, hcW, hdim]
        exact (LinearMap.isNilpotent_iff_charpoly (0 : Module.End k W)).mp IsNilpotent.zero
      obtain ⟨m, hm⟩ := hnil
      have hfix : ∀ j : ℕ, ((Algebra.lsmul k k V (u * a)) ^ j) (s : V) = s := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ, Module.End.mul_apply]
          have : (Algebra.lsmul k k V (u * a)) (s : V) = s := by
            have := congrArg (Subtype.val) hu'
            simpa [mul_smul] using this
          rw [this, ihj]
      have hs0 : (s : V) = 0 := by
        rw [← hfix m, hm]
        simp
      apply hne
      have : s = 0 := by exact_mod_cast hs0
      rw [this, smul_zero]
    obtain ⟨f, hf⟩ := exists_ne_zero_hom (k := k) key
    have hsurj : Function.Surjective f := LinearMap.surjective_of_ne_zero hf
    obtain ⟨V', hV'⟩ := exists_isCompl S
    obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
    let eV : (S × V') ≃ₗ[A] V := Submodule.prodEquivOfIsCompl S V' hV'
    let eC : C ≃ₗ[A] S :=
      (Submodule.quotientEquivOfIsCompl (LinearMap.ker f) C hC).symm ≪≫ₗ
        f.quotKerEquivOfSurjective hsurj
    let eW : (S × LinearMap.ker f) ≃ₗ[A] W :=
      (LinearEquiv.prodCongr eC.symm (LinearEquiv.refl A _)) ≪≫ₗ
        (LinearEquiv.prodComm A _ _) ≪≫ₗ Submodule.prodEquivOfIsCompl (LinearMap.ker f) C hC
    have h' : ∀ a : A, cp k V' a = cp k (LinearMap.ker f) a := by
      intro a
      have h1 : cp k S a * cp k V' a = cp k S a * cp k (LinearMap.ker f) a := by
        rw [← cp_prod, ← cp_prod, cp_congr eV, cp_congr eW, h a]
      exact mul_left_cancel₀ (LinearMap.charpoly_monic _).ne_zero h1
    have hlt : Module.finrank k V' < n := by
      have h1 : Module.finrank k (S × V') = Module.finrank k V :=
        LinearEquiv.finrank_eq (eV.restrictScalars k)
      rw [Module.finrank_prod] at h1
      have : Nontrivial S := IsSimpleModule.nontrivial A S
      have h2 : 0 < Module.finrank k S := Module.finrank_pos
      omega
    obtain ⟨e'⟩ := ih _ hlt V' (LinearMap.ker f) rfl inferInstance inferInstance h'
    exact ⟨eV.symm ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl A _) e') ≪≫ₗ eW⟩

end Formalism.IrreducibleCountingLemmas.Z.BN

namespace Formalism.IrreducibleCountingLemmas.Z

theorem brauer_nesbitt_algebra : BrauerNesbittAlg := by
  intro k A V W _ _ _ _ _ _ _ _ _ _ _ _ _ hV hW h
  exact BN.mul_eq_one_of_covolume_identity _ V W rfl hV hW h

end Formalism.IrreducibleCountingLemmas.Z
end
end
