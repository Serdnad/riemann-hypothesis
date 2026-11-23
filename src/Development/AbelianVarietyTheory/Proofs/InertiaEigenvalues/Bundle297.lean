module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem exists_greatest_of_sup_closed {S V ι : Type} [CommRing S] [IsNoetherianRing S] [AddCommGroup V]
    [Module S V] [Finite ι] (C : (ι → Submodule S V) → Prop) (P N₀ : ι → Submodule S V) (h₀ : C N₀)
    (hP : ∀ i, (P i).FG) (hle : ∀ N, C N → ∀ i, N i ≤ P i)
    (hsup : ∀ N N', C N → C N' → C (fun i => N i ⊔ N' i)) :
    ∃ N, C N ∧ ∀ N', C N' → ∀ i, N' i ≤ N i := by
  classical
  have one : ∀ i, ∃ N, C N ∧ ∀ N', C N' → N' i ≤ N i := by
    intro i
    haveI : IsNoetherian S (P i) := isNoetherian_of_fg_of_noetherian _ (hP i)
    obtain ⟨_, ⟨N, hN, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 this
      {Q : Submodule S (P i) | ∃ N, C N ∧ (N i).comap (P i).subtype = Q} ⟨_, N₀, h₀, rfl⟩
    refine ⟨N, hN, fun N' hN' x hx => ?_⟩
    have h1 := hmax _ ⟨_, hsup N N' hN hN', rfl⟩
    have h2 : (N i).comap (P i).subtype = (N i ⊔ N' i).comap (P i).subtype :=
      (Submodule.comap_mono le_sup_left).eq_of_not_lt h1
    have h3 : (⟨x, hle N' hN' i hx⟩ : P i) ∈ (N i ⊔ N' i).comap (P i).subtype :=
      Submodule.mem_sup_right hx
    rw [← h2] at h3
    exact h3
  have all : ∀ s : Finset ι, ∃ N, C N ∧ ∀ N', C N' → ∀ i ∈ s, N' i ≤ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨N₀, h₀, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨N, hN, h⟩ := ih
      obtain ⟨N₁, hN₁, h₁⟩ := one a
      refine ⟨_, hsup N N₁ hN hN₁, fun N' hN' i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_sup_of_le_right (h₁ N' hN')
      · exact le_sup_of_le_left (h N' hN' i hi)
  haveI := Fintype.ofFinite ι
  obtain ⟨N, hN, h⟩ := all Finset.univ
  exact ⟨N, hN, fun N' hN' i => h N' hN' i (Finset.mem_univ i)⟩

theorem exists_largest_model : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N₀ : Lats k n A.m), M.Model A N₀ → ∃ N, M.Model A N ∧ ∀ N', M.Model A N' → ∀ i, N' i ≤ N i := by
  intro k G _ _ l n _ _ _ R F r Dt M A N₀ h₀
  obtain ⟨-, hl₀, hab₀, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N₀ h₀
  refine exists_greatest_of_sup_closed (fun N => M.Model A N)
    (fun i => sh (-(sg l Dt.h i : ℤ)) (N₀ i)) N₀ h₀ (fun i => ((hl₀ i).shift _).1) (fun N hN i => ?_)
    (fun N N' => GlobalTheory.T.model_sup_alt F M A N N')
  obtain ⟨-, hl, hab, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N hN
  have h := sh_le_sh (-(sg l Dt.h i : ℤ)) (GlobalTheory.T.phiGamma_lattice_families_shift_inclusion (F.D A) Dt.h Dt.w N N₀ hl hl₀ hab hab₀ i)
  rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h

end GlobalTheory.Models
end

section

noncomputable section
namespace GlobalTheory.Models.CharSign
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem exists_unit_zpow {c : k⸨X⸩} (hc : c ≠ 0) :
    ∃ (a : ℤ) (u : (k⟦X⟧)ˣ), c = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a := by
  obtain ⟨a, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := k⟦X⟧) (K := k⸨X⸩) PowerSeries.X_irreducible hc
  refine ⟨a, u, ?_⟩
  rw [h, Units.smul_def, Algebra.smul_def, vv_eq_coe_X]
  rfl

theorem coe_smul (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := algebraMap_smul k⸨X⸩ a x

theorem le_of_sh_le_sh {N : Submodule k⟦X⟧ V} (hN : N.FG) (h0 : N ≠ ⊥) {a b : ℤ} (h : sh a N ≤ sh b N) :
    b ≤ a := by
  by_contra hab
  have h1 : N ≤ sh 1 N := by
    have h2 := sh_le_sh (-a) h
    rw [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq] at h2
    exact h2.trans (sh_le_sh_of_le (by omega) N)
  apply h0
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {(PowerSeries.X : k⟦X⟧)}) N hN ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 (h1 hx)
    rw [zpow_one, vv_eq_coe_X, coe_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PowerSeries.maximalIdeal_eq_span_X]

theorem span_unit_zpow (a : ℤ) (u : (k⟦X⟧)ˣ) (y : V) :
    Submodule.span k⟦X⟧ {(((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a) • y} = sh a (Submodule.span k⟦X⟧ {y}) := by
  rw [sh, Submodule.map_span, Set.image_singleton, mul_smul, coe_smul,
    Submodule.span_singleton_smul_eq u.isUnit]
  rfl

theorem φ_zpow {l : ℕ} (R : RingPG k l) (a : ℤ) :
    ∃ u : (k⟦X⟧)ˣ, R.φ (vv k ^ a) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l * a) := by
  obtain ⟨u, hu⟩ := R.φ_v
  refine ⟨u ^ a, ?_⟩
  rw [map_zpow₀, hu, mul_zpow, zpow_mul, zpow_natCast]
  congr 1
  have := map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k : k⟦X⟧ →+* k⸨X⸩).toMonoidHom) u a
  have h2 := congrArg Units.val this
  rw [Units.val_zpow_eq_zpow_val] at h2
  exact h2.symm

variable [Module k V]

theorem pull_sh_le {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) ≤ sh (l * a) (pull f N) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := φ_zpow R a
  rw [hf, hu, mul_smul, coe_smul]
  exact Submodule.smul_mem _ _ (mem_sh_iff_exists.2 ⟨f y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩)

theorem pull_sh {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) = sh (l * a) (pull f N) := by
  refine le_antisymm (pull_sh_le R hf a N) ?_
  have h := sh_le_sh (l * a) (pull_sh_le R hf (-a) (sh a N))
  rwa [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq, mul_neg, add_neg_cancel, sh_zero_eq] at h

end

section
variable {k : Type} [Field k]

theorem exists_smul_eq {y : Vc k 1} (hy : y ≠ 0) (x : Vc k 1) : ∃ c : k⸨X⸩, x = c • y := by
  have h0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0]; exact h)
  refine ⟨x 0 / y 0, funext fun j => ?_⟩
  rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]

theorem span_eq_sh {x y : Vc k 1} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a : ℤ, Submodule.span k⟦X⟧ {x} = sh a (Submodule.span k⟦X⟧ {y}) := by
  obtain ⟨c, rfl⟩ := exists_smul_eq hy x
  obtain ⟨a, u, rfl⟩ := exists_unit_zpow (c := c) (by rintro rfl; exact hx (zero_smul _ _))
  exact ⟨a, span_unit_zpow a u y⟩

theorem span_total (x y : Vc k 1) : Submodule.span k⟦X⟧ {x} ≤ Submodule.span k⟦X⟧ {y} ∨
    Submodule.span k⟦X⟧ {y} ≤ Submodule.span k⟦X⟧ {x} := by
  by_cases hx : x = 0
  · left; simp [hx]
  by_cases hy : y = 0
  · right; simp [hy]
  obtain ⟨a, h⟩ := span_eq_sh hx hy
  rw [h]
  rcases le_total 0 a with ha | ha
  · left; exact (sh_le_sh_of_le ha _).trans (sh_zero_eq _).le
  · right; exact (sh_zero_eq _).ge.trans (sh_le_sh_of_le ha _)

theorem exists_gen {N : Submodule k⟦X⟧ (Vc k 1)} (hN : N.FG) : ∃ x, N = Submodule.span k⟦X⟧ {x} := by
  classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨x, hx⟩ := ih
    rw [Finset.coe_insert, Submodule.span_insert, hx]
    rcases span_total a x with h | h
    · exact ⟨x, sup_eq_right.2 h⟩
    · exact ⟨a, sup_eq_left.2 h⟩

theorem ne_bot_of_isLat {N : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) : N ≠ ⊥ := by
  rintro rfl
  have h := hN.2
  simp at h

theorem exists_eq_sh {N N' : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) (hN' : IsLat N') : ∃ a : ℤ, N = sh a N' := by
  obtain ⟨x, rfl⟩ := exists_gen hN.1
  obtain ⟨y, rfl⟩ := exists_gen hN'.1
  refine span_eq_sh ?_ ?_
  · rintro rfl; exact ne_bot_of_isLat hN (by simp)
  · rintro rfl; exact ne_bot_of_isLat hN' (by simp)

end

theorem model_char_sign : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → ∃ κ : ZMod n → ℤ, ∀ i, N i = sh (κ i) (M.Nχ e i) ∧ |κ i| ≤ Dt.sg l i ∧ (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧ ∀ x, sen ((F.D (chr (M.ω ^ (-e)))).γ i) (N i) x = resCount {e - κ i} 0 x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 _ _ e he0 het N hN
  obtain ⟨-, hL, hAB, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) N hN
  obtain ⟨-, hL0, hAB0, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) (M.Nχ e) (M.χ_model e he0 het)
  have hχ := M.χ_lat e (by omega) het
  choose κ hκ using fun i => exists_eq_sh (hL i) (hL0 i)
  have key : ∀ i {a b : ℤ}, sh a (M.Nχ e i) ≤ sh b (M.Nχ e i) → b ≤ a :=
    fun i a b h => le_of_sh_le_sh (hL0 i).1 (ne_bot_of_isLat (hL0 i)) h
  have habs : ∀ i, |κ i| ≤ Dt.sg l i := by
    intro i
    have a1 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w N (M.Nχ e) hL hL0 hAB hAB0 i
    have a2 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w (M.Nχ e) N hL0 hL hAB0 hAB i
    rw [hκ i, sh_sh_eq] at a1
    rw [hκ i] at a2
    have b1 := key i (a1.trans (sh_zero_eq _).ge)
    have b2 := key i a2
    unfold TopData.sg
    rw [abs_le]
    constructor <;> omega
  have hJ : ∀ i, -Dt.w i + κ i ≤ l * κ (i - 1) + e ∧ l * κ (i - 1) + e ≤ Dt.wst i + κ i := by
    intro i
    obtain ⟨a1, a2⟩ := hAB i
    have hp : pull ((F.D (chr (M.ω ^ (-e)))).φ i) (N (i - 1)) = sh (l * κ (i - 1) + e) (M.Nχ e i) := by
      rw [hκ (i - 1), pull_sh R ((F.D (chr (M.ω ^ (-e)))).φ_semi i), (hχ i).2.2.1, sh_sh_eq]
    rw [hp, hκ i, sh_sh_eq] at a1 a2
    exact ⟨key i a1, key i a2⟩
  refine ⟨κ, fun i => ⟨hκ i, habs i, fun hi => ?_, fun hi => ?_, fun x => ?_⟩⟩
  · by_contra hneg
    have c1 := (Dt.lowG i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).2
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).1
    have c5 : (l : ℤ) * κ (i - 1) ≤ l * (-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · by_contra hneg
    have c1 := (Dt.lowBd i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).1
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).2
    unfold TopData.wst at c4
    have c5 : (l : ℤ) * 1 ≤ l * κ (i - 1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · rw [hκ i, GlobalTheory.PhiGam.SenShift.sen_sh R _ ((F.D (chr (M.ω ^ (-e)))).γ_semi i) _ (hχ i).1 (hχ i).2.1,
      (hχ i).2.2.2]
    unfold resCount
    have : (((e - 0 : ℤ) : k) = x + (κ i : k)) ↔ (((e - κ i - 0 : ℤ) : k) = x) := by
      push_cast
      rw [sub_zero, sub_zero, sub_eq_iff_eq_add]
    classical
    simp only [Multiset.filter_singleton, this]
    split_ifs <;> simp

end GlobalTheory.Models.CharSign
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.AntiRamConj
open scoped TensorProduct Pointwise

namespace GlobalTheory.TwistDet

section Places

variable {D : Formalism.BasicNotions.D7}

def conjInt (D : Formalism.BasicNotions.D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

theorem conjInt_coe (x : 𝓞 D.host.E) : ((conjInt D x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem conjInt_conjInt (x : 𝓞 D.host.E) : conjInt D (conjInt D x) = x := by
  apply RingOfIntegers.ext
  rw [conjInt_coe, conjInt_coe, host_conj_conj]

theorem isConjPl_iff {P P' : PlE D.host} :
    IsConjPl D.host P P' ↔ ∀ x, x ∈ P.asIdeal ↔ conjInt D x ∈ P'.asIdeal := by
  constructor
  · intro h x
    exact h x _ rfl
  · intro h x y hxy
    have e : y = conjInt D x := RingOfIntegers.ext hxy
    rw [e, h]

theorem isConjPl_symm {P P' : PlE D.host} (h : IsConjPl D.host P P') : IsConjPl D.host P' P := by
  rw [isConjPl_iff] at h ⊢
  intro x
  rw [h, conjInt_conjInt]

theorem isConjPl_unique {P P' P'' : PlE D.host} (h : IsConjPl D.host P P') (h' : IsConjPl D.host P P'') : P' = P'' := by
  have a := isConjPl_iff.1 (isConjPl_symm h)
  have b := isConjPl_iff.1 (isConjPl_symm h')
  ext x
  rw [a, b]

theorem exists_isConjPl (P : PlE D.host) : ∃ P', IsConjPl D.host P P' := by
  refine ⟨P.comap (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E) (conjInt D).surjective, isConjPl_iff.2 fun x => ?_⟩
  change x ∈ P.asIdeal ↔ conjInt D (conjInt D x) ∈ P.asIdeal
  rw [conjInt_conjInt]

theorem ne_of_isSplitPl {P P' : PlE D.host} (hs : IsSplitPl D.host P) (h : IsConjPl D.host P P') : P ≠ P' := by
  rintro rfl
  obtain ⟨x, hx, hy⟩ := hs
  exact hy (conjInt D x) rfl ((isConjPl_iff.1 h x).1 hx)

theorem normV_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') : normV P' = normV P := by
  have e : P'.asIdeal = P.asIdeal.map (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    ext y
    obtain ⟨x, rfl⟩ := (conjInt D).surjective y
    rw [← isConjPl_iff.1 h]
    exact (Ideal.apply_mem_of_equiv_iff (f := conjInt D)).symm
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (conjInt D) e).toEquiv).symm

theorem mem_placesOver_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') {p : ℕ}
    (hp : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have := (isConjPl_iff.1 h (p : 𝓞 D.host.E)).1 hp
  rwa [map_natCast] at this

theorem over_refl (P : PlE D.host) : Over P P := Or.inl rfl

theorem over_symm {P v : PlE D.host} (h : Over P v) : Over v P :=
  h.elim (fun e => Or.inl e.symm) fun c => Or.inr (isConjPl_symm c)

theorem over_trans {P v w : PlE D.host} (h : Over P v) (h' : Over v w) : Over P w := by
  rcases h with rfl | h
  · exact h'
  · rcases h' with rfl | h'
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique h' (isConjPl_symm h))

end Places

section Galois

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem cc_algebraMap (x : D.host.E) :
    X.cc (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := X.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply (j.comp (algebraMap D.host.E N.Om)) x).symm

theorem cc_cc (x : N.Om) : X.cc (X.cc x) = x := by
  obtain ⟨j, hj⟩ := X.cc_cm.1
  apply j.injective
  rw [hj, hj, Complex.conj_conj]

theorem cc_symm (x : N.Om) : X.cc.symm x = X.cc x := by
  rw [RingEquiv.symm_apply_eq, cc_cc]

theorem cc_symm_mem (x : D.host.E) : ∃ y : D.host.E,
    X.cc.symm (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om y :=
  ⟨_, by rw [cc_symm, cc_algebraMap]⟩

def cConj : GE N →* GE N where
  toFun := conjAut X.cc (cc_symm_mem X)
  map_one' := by
    ext x
    exact X.cc.apply_symm_apply x
  map_mul' g h := by
    ext x
    change X.cc (g (h (X.cc.symm x))) = X.cc (g (X.cc.symm (X.cc (h (X.cc.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem cConj_apply (g : GE N) (x : N.Om) : cConj X g x = X.cc (g (X.cc.symm x)) := rfl

theorem cConj_cConj (g : GE N) : cConj X (cConj X g) = g := by
  ext x
  rw [cConj_apply, cConj_apply, cc_cc, cc_symm, cc_symm, cc_cc]

theorem antiHom_cConj {A : Type} [CommGroup A] {φ : GE N →* A} (h : AntiHom X.cc φ) (g : GE N) :
    φ (cConj X g) = (φ g)⁻¹ := h g _ (cConj_apply X g)

theorem isPlaceOver_moveVal_cc {P P' : PlE D.host} (h : IsConjPl D.host P P') {B : ValuationSubring N.Om}
    (hB : IsPlaceOver B P) : IsPlaceOver (moveVal X.cc B) P' := by
  intro y
  rw [moveVal_lt_one, cc_symm, cc_algebraMap, ← conjInt_coe, hB]
  exact (isConjPl_iff.1 (isConjPl_symm h) y).symm

theorem cConj_mem_ine {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) B) :
    cConj X σ ∈ Ine (F := D.host.E) (moveVal X.cc B) := conjAut_mem_ine X.cc (cc_symm_mem X) hσ

theorem isFrob_cConj {B : ValuationSubring N.Om} {q : ℕ} {σ : GE N} (hσ : IsFrob B q σ) :
    IsFrob (moveVal X.cc B) q (cConj X σ) := by
  have hd : σ ∈ Dec (F := D.host.E) B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show cConj X σ ∈ Dec (F := D.host.E) (moveVal X.cc B)
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (cConj X σ).surjective x
    have h1 : ((cConj X σ)⁻¹ : GE N) (cConj X σ z) = z := (cConj X σ).symm_apply_apply z
    rw [h1, mem_moveVal, mem_moveVal, cConj_apply, RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hd]
  · rw [moveVal_lt_one, map_sub, cConj_apply, RingEquiv.symm_apply_apply, map_pow]
    apply hσ.2
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact hx

theorem isFrob_smul {B : ValuationSubring N.Om} {q : ℕ} {σ : GE N} (hσ : IsFrob B q σ) (g : GE N) :
    IsFrob (g • B) q (g * σ * g⁻¹) := by
  have hd : σ • B = B := hσ.1
  have hm : ∀ y : N.Om, y ∈ g • B ↔ (g⁻¹ : GE N) y ∈ B := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • g • B = g • B
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, hd]
  · rw [ValuationSubring.valuation_le_one_iff, hm] at hx
    have h2 := hσ.2 _ ((B.valuation_le_one_iff _).2 hx)
    have e : (g⁻¹ : GE N) ((g * σ * g⁻¹) x - x ^ q) = σ ((g⁻¹ : GE N) x) - ((g⁻¹ : GE N) x) ^ q := by
      rw [map_sub, map_pow, ← AlgEquiv.mul_apply, mul_assoc, inv_mul_cancel_left, AlgEquiv.mul_apply]
    rw [valuation_lt_one_iff'] at h2 ⊢
    rw [hm, hm, map_inv₀, ← map_eq_zero_iff (g⁻¹ : GE N) (g⁻¹ : GE N).injective, e]
    exact h2

theorem exists_frob_of_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') {σ : GE N}
    (hσ : IsFrob (N.plOm.1 P') (normV P') σ) :
    ∃ σ₀ g : GE N, IsFrob (N.plOm.1 P) (normV P) σ₀ ∧ σ = g * cConj X σ₀ * g⁻¹ := by
  have h1 := isFrob_cConj X hσ
  have h2 := isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)
  have h3 := isFrob_smul h1 g
  rw [hg, normV_conj h] at h3
  refine ⟨_, (cConj X g)⁻¹, h3, ?_⟩
  rw [map_mul, map_mul, map_inv, cConj_cConj]
  group

theorem isOpen_comap_cConj {H : Subgroup (GE N)} (hH : IsOpen (H : Set (GE N))) :
    IsOpen ((H.comap (cConj X) : Subgroup (GE N)) : Set (GE N)) := by
  obtain ⟨L, hL, hLH⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om (H : Set (GE N))).1 (hH.mem_nhds H.one_mem)
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin D.host.E ((S.image X.cc.symm : Finset N.Om) : Set N.Om)
  have hL' : FiniteDimensional D.host.E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := L'.fixingSubgroup) (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen L')
  apply hLH
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg
  have : L ≤ IntermediateField.fixedField (Subgroup.zpowers (cConj X g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : cConj X g x = x := by
      rw [cConj_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (GE N) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) _ (Subgroup.mem_zpowers _)

end Galois

end GlobalTheory.TwistDet

end
end
