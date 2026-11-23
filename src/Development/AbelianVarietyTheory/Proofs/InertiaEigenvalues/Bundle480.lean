module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle322
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle117
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfIsUniUp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle326
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle369
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.AdmBound

theorem inZZ_mono {k : Type} [Field k] {l n m r : ℕ} {R : RingPG k l} (D : ModPG R n (Vc k m)) (Dt : TopData n r)
    {N N' : Lats k n m} (h : ∀ i, N i ≤ N' i) {b g : ZMod n → Vc k m} (hz : InZZ D Dt N b g) :
    InZZ D Dt N' b g := by
  intro i
  obtain ⟨h0, h1, h2, h3⟩ := hz i
  refine ⟨h0, sh_le_sh 1 (h i) h1, fun hG => sh_le_sh _ (h i) (h2 hG), fun hB => ?_⟩
  obtain ⟨hb, x, hx, hx'⟩ := h3 hB
  exact ⟨sh_le_sh _ (pull_le_pull _ (h (i - 1))) hb, x, h i hx, sh_le_sh _ (h i) hx'⟩

theorem repr_sum {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {ι : Type} (z : ι → G → Fin A.m → k)
    (b g : ι → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a)) (a₀ : ι) (c : ι → k) (t : Finset ι) :
    Repr F A (∑ a ∈ t, c a • z a) (∑ a ∈ t, c a • b a) (∑ a ∈ t, c a • g a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 := GlobalTheory.T.repr_smul_add F A (-1) (z a₀) (z a₀) (b a₀) (g a₀) (b a₀) (g a₀) (h a₀) (h a₀)
    simpa only [neg_one_smul, neg_add_cancel, Finset.sum_empty] using h0
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.repr_smul_add F A (c a) (z a) _ (b a) (g a) _ _ (h a) ih

theorem indep_pairs {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {s : ℕ} (z : Fin s → G → Fin A.m → k)
    (b g : Fin s → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a))
    (hz : LinearIndependent k (fun a => (cob A).mkQ (z a))) :
    LinearIndependent k (fun a => (herrB (F.D A)).mkQ (b a, g a)) := by
  classical
  rw [linearIndependent_iff'] at hz ⊢
  intro t c hc a ha
  have e1 : ∑ a ∈ t, c a • (herrB (F.D A)).mkQ (b a, g a) =
      (herrB (F.D A)).mkQ (∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) := by
    rw [show ((∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) : (ZMod n → Vc k A.m) × (ZMod n → Vc k A.m)) =
        ∑ a ∈ t, c a • (b a, g a) by ext <;> simp [Prod.fst_sum, Prod.snd_sum]]

    simp only [map_sum, map_smul]
  rw [e1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
  have hcob := GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F A _ _ _ (repr_sum F A z b g h a c t) hc
  refine hz t c ?_ a ha
  have e2 : ∑ a ∈ t, c a • (cob A).mkQ (z a) = (cob A).mkQ (∑ a ∈ t, c a • z a) := by

    simp only [map_sum, map_smul]
  rw [e2, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hcob

private theorem exists_ne_zero_smul_mem_of_mem_span' (hψ : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi) {k : Type} [Field k] {l n m r : ℕ} [Fact l.Prime]
    [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n r)
    (N : Lats k n m) (hr : m = r) (hc : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (habc : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧
      (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧
      (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = r ∧
        EPoly (D.γ i) (N i) (Dt.wst i + 1)))
    (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : ∀ a, InZZ D Dt N (z a).1 (z a).2)
    (hind : LinearIndependent k (fun a => (herrB D).mkQ (z a))) : s ≤ Dt.dsum := by
  subst hr
  exact GlobalTheory.T.card_cocycles_independent_mod_coboundaries_le hψ D ι Dt N hc h1 h2 h3 habc hsen s z hz hind

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (s : ℕ) (z : Fin s → G → Fin M.T.m → k), (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) → LinearIndependent k (fun a => (cob M.T).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hψ k G _ _ l n _ _ _ R F r Dt M ι hc h1 h2 h3 s z hz hind
  choose N b g hN hR hZ using fun a => GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 M.T (z a) (hz a)
  obtain ⟨Nm, hNm, hmax⟩ := GlobalTheory.T.exists_largest_model' F M M.T M.Nstd M.std_model
  have hS := GlobalTheory.T.twistedPhiGammaModel_sen_weight_count F M h1 h2 h3 Nm hNm (hmax _ M.std_model)
  refine exists_ne_zero_smul_mem_of_mem_span' hψ (F.D M.T) ι Dt Nm M.T_m hc h1 h2 h3 (GlobalTheory.T.obj_and_abc_of_model F M M.T Nm hNm).2
    (fun i => ⟨(hS i).1, (hS i).2.1, fun hB => ⟨(hS i).2.2 hB,
      GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 M.T Nm hNm i hB⟩⟩)
    s (fun a => (b a, g a)) (fun a => inZZ_mono _ _ (hmax _ (hN a)) (hZ a)) (indep_pairs F M.T z b g hR hind)

end GlobalTheory.Models.AdmBound
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ExactMult

variable {g : ℕ} [Fact g.Prime]

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun h => ∑ i ∈ s, f i h) = ∑ i ∈ s, wh ψ (f i) := by
  unfold wh tr
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun h => c * f h) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem wh_gg_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (gg ψ 0) = 1 := by
  have hU : ∀ M : Mt g 0, IsUniUp M := fun M a => a.elim0
  have hgg : ∀ x : Gn g 0, gg ψ 0 x = 1 := by
    intro x
    unfold gg
    simp [hU]
  unfold wh eU
  rw [GlobalTheory.GLm.TraceTail.tr_eDat]
  simp [hU, hgg]

theorem isClass_der (ψ : AddChar (ZMod g) ℂ) {N : ℕ} (i : ℕ) (hi : i ≤ N) (χ : Gn g N → ℂ)
    (hχ : IsClass χ) : IsClass (der ψ i χ) := by
  intro x y
  have h := ((GlobalTheory.GLq.HcClass.hc_class g i (N - i) N (by omega)).2 χ hχ).2
  unfold der
  congr 1
  funext z
  exact h z x y

theorem wh_hc (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ)
    (hα : IsClass α) (hβ : IsClass β) : wh ψ (hc a b α β (a + b)) = wh ψ α * wh ψ β := by
  unfold hc
  rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ a b (a + b) rfl _ (fun y x z => by simp only [hα x z])
    (fun x y z => by simp only [hβ y z])]
  simp only [wh_const_mul]
  rw [show (fun x => α x * wh ψ β) = (fun x => wh ψ β * α x) from funext fun _ => mul_comm _ _,
    wh_const_mul, mul_comm]

end GlobalTheory.GLq.ExactMult

namespace GlobalTheory.GLq.ExactMult

open GlobalTheory.GLm

theorem tr_eJ'_eq_sum_wh_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k : ℕ), 1 ≤ k →
    k < N → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ' g N k ψ) χ =
      (∑ i ∈ Finset.range k, wh ψ (der ψ i χ) * ((g : ℂ) ^ (k - i) - (g : ℂ) ^ (k - i - 1))) +
        wh ψ (der ψ k χ) := by
  intro g _ ψ hψ N k _ hk χ hχ
  rw [tr_eJ'_eq_wh_tail g ψ N k χ hk]
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have hF := GlobalTheory.GLm.TailClass.isMirClass_tail g ψ (k + 1) N χ (by omega) (by omega) hM
  rw [show (fun h => tail ψ (k + 1) χ (diag1 h (k + 1))) = fun h =>
      ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k h from
    funext (mirClass_diag1_eq_sum g ψ hψ k _ hF)]
  rw [wh_sum, Finset.sum_range_succ]
  have key : ∀ i, i < k + 1 → wh ψ (hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k) =
      wh ψ (der ψ i χ) * wh ψ (gg ψ (k - i)) := by
    intro i hi
    rw [GlobalTheory.GLm.DerTail.der_tail g ψ i (k + 1) N χ hi (by omega)]
    have := wh_hc ψ hψ i (k - i) (der ψ i χ) (gg ψ (k - i)) (isClass_der ψ i (by omega) χ hχ)
      (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ (k - i)).2
    rwa [show i + (k - i) = k by omega] at this
  rw [key k (by omega), Nat.sub_self, wh_gg_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [key i (by omega), (GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity g ψ hψ (k - i) (by omega)).1]

end GlobalTheory.GLq.ExactMult
end
end

section

noncomputable section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.SuppCusp

section general
variable {G : Type} [Group G] [Fintype G]

theorem ip_add_left (u v w : G → ℂ) : ip (fun x => u x + v x) w = ip u w + ip v w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; ring

theorem ip_add_right (u v w : G → ℂ) : ip u (v + w) = ip u v + ip u w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; simp only [Pi.add_apply]; ring

theorem irr_char {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h; exact ⟨V, hV⟩

theorem char_class {χ : G → ℂ} (h : IsChar χ) : IsClass χ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G χ).2.2.1 h

theorem ip_irr_char_nat {α A : G → ℂ} (hα : IsIrr α) (hA : IsChar A) : ∃ c : ℕ, ip α A = c := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA
  clear hA
  induction L with
  | nil => exact ⟨0, by simp [ip]⟩
  | cons ρ L ih =>
    obtain ⟨c, hc⟩ := ih (fun r hr => hL r (List.mem_cons_of_mem _ hr))
    have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G α ρ hα (hL ρ (by simp))).2.2
    refine ⟨(if α = ρ then 1 else 0) + c, ?_⟩
    rw [List.sum_cons, ip_add_right, hc, h1]; split_ifs <;> simp

end general

section prod
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

theorem ip_prod_single (α A : G → ℂ) (β B : H → ℂ) :
    ip (fun p : G × H => α p.1 * β p.2) (fun p => A p.1 * B p.2) = ip α A * ip β B := by
  unfold ip
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp only [Prod.fst_inv, Prod.snd_inv]
  have e : ∀ x y, α x * β y * (A x⁻¹ * B y⁻¹) = (α x * A x⁻¹) * (β y * B y⁻¹) := by intros; ring
  simp only [e]
  rw [show ((Fintype.card G : ℂ))⁻¹ * (∑ x, α x * A x⁻¹) * (((Fintype.card H : ℂ))⁻¹ * ∑ y, β y * B y⁻¹) =
    ((Fintype.card G : ℂ))⁻¹ * ((Fintype.card H : ℂ))⁻¹ * ((∑ x, α x * A x⁻¹) * ∑ y, β y * B y⁻¹) by ring,
    Finset.sum_mul_sum, Nat.cast_mul, mul_inv]

theorem ip_prod_list (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ) :
    ip (fun p : G × H => (R.map fun k => k.1 p.1 * k.2 p.2).sum) (fun p => A p.1 * B p.2) =
      (R.map fun k => ip k.1 A * ip k.2 B).sum := by
  induction R with
  | nil => simp [ip]
  | cons k R ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ip_add_left (fun p : G × H => k.1 p.1 * k.2 p.2), ih, ip_prod_single]

theorem sum_nat_ne_zero (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ)
    (hR : ∀ k ∈ R, IsIrr k.1 ∧ IsIrr k.2) (hA : IsChar A) (hB : IsChar B) :
    ∃ N : ℕ, (R.map fun k => ip k.1 A * ip k.2 B).sum = N ∧
      ((∃ k ∈ R, ip k.1 A ≠ 0 ∧ ip k.2 B ≠ 0) → N ≠ 0) := by
  induction R with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons k R ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun r hr => hR r (List.mem_cons_of_mem _ hr))
    obtain ⟨c, hc⟩ := ip_irr_char_nat (hR k (by simp)).1 hA
    obtain ⟨d, hd⟩ := ip_irr_char_nat (hR k (by simp)).2 hB
    refine ⟨c * d + N, by simp [List.sum_cons, hN, hc, hd], ?_⟩
    rintro ⟨k', hk', h1, h2⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · rw [hc] at h1; rw [hd] at h2
      have hc0 : c ≠ 0 := by rintro rfl; simp at h1
      have hd0 : d ≠ 0 := by rintro rfl; simp at h2
      have := Nat.mul_ne_zero hc0 hd0; omega
    · have := hN0 ⟨k', hk', h1, h2⟩; omega

end prod

section lists
variable {g : ℕ} [Fact g.Prime]

theorem degL_append (L₁ L₂ : List (Pc g)) : degL (L₁ ++ L₂) = degL L₁ + degL L₂ := by
  simp [degL, List.map_append, List.sum_append]

theorem class_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsClass (hcL L (degL L)) :=
  char_class (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1

theorem char_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) :=
  (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1

theorem hcL_append (L₁ L₂ : List (Pc g)) (h : ∀ p ∈ L₁ ++ L₂, IsChar p.2) (n : ℕ)
    (hn : n = degL L₁ + degL L₂) :
    hcL (L₁ ++ L₂) n = hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n := by
  induction L₁ generalizing n with
  | nil =>
    have h2 : ∀ p ∈ L₂, IsChar p.2 := fun p hp => h p (by simpa using hp)
    change n = 0 + degL L₂ at hn
    rw [Nat.zero_add] at hn; subst hn
    exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g (degL L₂) 0 0 (degL L₂) (hcL L₂ (degL L₂)) (fun _ => 1) (fun _ => 1)
      (class_hcL L₂ h2) (fun _ _ => rfl) (fun _ _ => rfl)).2.2.1).symm
  | cons p L₁ ih =>
    have hp : IsChar p.2 := h p (by simp)
    have h1 : ∀ q ∈ L₁, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h2 : ∀ q ∈ L₂, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h12 : ∀ q ∈ L₁ ++ L₂, IsChar q.2 := fun q hq => h q (by simp at hq ⊢; tauto)
    have e1 := degL_append L₁ L₂
    have e2 : degL (p :: L₁) = p.1 + degL L₁ := by simp [degL]
    rw [List.cons_append, hcL_cons, hcL_cons, ih h12 (degL (L₁ ++ L₂)) e1, e1, e2]
    exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g p.1 (degL L₁) (degL L₂) n p.2 (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂))
      (char_class hp) (class_hcL L₁ h1) (class_hcL L₂ h2)).1 (by omega)).symm

end lists

theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsIrr χ) :
    ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hcls : IsClass χ := char_class (irr_char hχ)
  have hself : ip χ χ = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.2
  by_cases hn : n = 0
  · subst hn
    have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Matrix.ext fun i _ => i.elim0)
    have hu : (Finset.univ : Finset (Gn g 0)) = {1} := by ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact hsub x
    have hcard : Fintype.card (Gn g 0) = 1 := by rw [← Finset.card_univ, hu]; simp
    have hc1 : ∀ f : Gn g 0 → ℂ, ip χ f = χ 1 * f 1 := by
      intro f; unfold ip; rw [hcard, hu]; simp
    refine ⟨[], by simp, rfl, ?_⟩
    rw [hcL_nil, hc1]; rw [hc1] at hself
    simp only [mul_one]; intro h0; rw [h0] at hself; simp at hself
  · by_cases hcu : IsCusp χ
    · refine ⟨[⟨n, χ⟩], by simpa using hcu, by simp [degL], ?_⟩
      have e : hcL [(⟨n, χ⟩ : Pc g)] n = χ := by
        rw [hcL_cons]
        exact (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g n 0 0 n χ (fun _ => 1) (fun _ => 1) hcls (fun _ _ => rfl)
          (fun _ _ => rfl)).2.2.2
      rw [e, hself]; exact one_ne_zero
    · have hne : ∃ a, 0 < a ∧ a < n ∧ res a (n - a) χ 1 1 ≠ 0 := by
        by_contra hc; push_neg at hc
        exact hcu ⟨Nat.pos_of_ne_zero hn, hχ, fun a h1 h2 => hc a h1 h2⟩
      obtain ⟨a, ha0, han, hres⟩ := hne
      generalize hb : n - a = b at hres
      have hnab : n = a + b := by omega
      obtain ⟨R, hR, hRes⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a b n hnab).2 χ (irr_char hχ)
      obtain ⟨k, hk⟩ : ∃ k, k ∈ R := by
        rcases R with _ | ⟨k, R⟩
        · exact absurd (by simpa using hRes 1 1) hres
        · exact ⟨k, by simp⟩
      obtain ⟨L₁, hL₁c, hL₁d, hL₁⟩ := ih a han k.1 (hR k hk).1
      obtain ⟨L₂, hL₂c, hL₂d, hL₂⟩ := ih b (by omega) k.2 (hR k hk).2
      have hch : ∀ p ∈ L₁ ++ L₂, IsChar p.2 := by
        intro p hp
        rcases List.mem_append.1 hp with h | h
        exacts [irr_char (hL₁c p h).2.1, irr_char (hL₂c p h).2.1]
      refine ⟨L₁ ++ L₂, fun p hp => ?_, ?_, ?_⟩
      · rcases List.mem_append.1 hp with h | h
        exacts [hL₁c p h, hL₂c p h]
      · rw [degL_append]; omega
      · subst hL₁d; subst hL₂d
        have hc1 : IsChar (hcL L₁ (degL L₁)) := char_hcL L₁ fun p hp => hch p (by simp [hp])
        have hc2 : IsChar (hcL L₂ (degL L₂)) := char_hcL L₂ fun p hp => hch p (by simp [hp])
        rw [hcL_append L₁ L₂ hch n hnab]
        have e : ip χ (hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n) =
            ip (fun p : Gn g (degL L₁) × Gn g (degL L₂) => (R.map fun k => k.1 p.1 * k.2 p.2).sum)
              (fun p => hcL L₁ (degL L₁) p.1 * hcL L₂ (degL L₂) p.2) := by
          rw [← funext fun p : Gn g (degL L₁) × Gn g (degL L₂) => hRes p.1 p.2]
          exact GlobalTheory.T.harishChandra_frobenius_reciprocity g _ _ n hnab χ (fun x y => hcL L₁ (degL L₁) x * hcL L₂ (degL L₂) y) hcls
        rw [e, ip_prod_list]
        obtain ⟨N, hN, hN0⟩ := sum_nat_ne_zero R _ _ hR hc1 hc2
        rw [hN]; exact_mod_cast hN0 ⟨k, hk, hL₁, hL₂⟩

end GlobalTheory.GLq.SuppCusp
end
end

section

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Generic

variable {g : ℕ} [Fact g.Prime]

theorem br_zero_self {d : ℕ} (M : Mt g d) : br 0 d M = M := by
  funext i j
  simp [br, entN, i.isLt, j.isLt]

theorem res_zero_self {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g d) : res 0 d χ 1 h = χ h := by
  unfold res
  have hI : ∀ x : Gn g d, InPar 0 (x : Mt g d) := fun x i j hj _ => absurd hj (Nat.not_lt_zero _)
  have hT : ∀ x : Gn g d, tl 0 (x : Mt g d) = ((1 : Gn g 0) : Mt g 0) := fun x => by
    funext i; exact i.elim0
  simp only [hI, hT, br_zero_self, true_and, zero_mul, pow_zero, inv_one, one_mul, Units.val_inj]
  rw [Finset.sum_ite_eq']
  simp

theorem wh_zero_fun (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : wh ψ (fun _ : Gn g n => (0 : ℂ)) = 0 := by
  simp [wh, tr]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

end GlobalTheory.GLq.Generic

theorem GlobalTheory.GLq.wh_cusp_pos : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  intro g _ ψ hψ d χ hc
  have hc' := hc
  obtain ⟨hd, hirr, _⟩ := hc'
  have hder := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (GlobalTheory.GLq.Generic.isClass_of_isIrr hirr)
  rw [Finset.sum_eq_single 0] at hder
  rotate_left
  · intro m hm hm0
    have hmd : m < d := Finset.mem_range.mp hm
    have hz : res m (d - m) χ 1 = fun _ => 0 := by
      funext y
      exact GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g d m χ hc (Nat.pos_of_ne_zero hm0) hmd 1 y
    have : der ψ m χ 1 = 0 := by
      show wh ψ (res m (d - m) χ 1) = 0
      rw [hz]
      exact GlobalTheory.GLq.Generic.wh_zero_fun ψ _
    rw [this, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr hd) h0
  have h0 : der ψ 0 χ 1 = wh ψ χ := by
    change wh ψ (n := d) (res 0 d χ 1) = wh ψ χ
    congr 1
    funext h
    exact GlobalTheory.GLq.Generic.res_zero_self χ h
  rw [h0] at hder
  obtain ⟨V, _, hV⟩ := hirr
  have hchar : IsChar χ := ⟨V, hV⟩
  obtain ⟨d', hd'pos, hd'⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).2.1 ⟨V, ‹_›, hV⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g d 0 0 ψ).1 hchar
  have hwh : wh ψ χ = n := hn
  refine ⟨n, Nat.pos_of_ne_zero ?_, hwh⟩
  rintro rfl
  rw [hwh, Nat.cast_zero, zero_mul, hd'] at hder
  exact absurd hder (by exact_mod_cast hd'pos.ne')
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.rankin_selberg_epsilon_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle), (∀ x, ψ' (i x) = ψ x) → ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) k)) (π' : IrrRep (GL (Fin (m + 1)) k')) (τ : IrrRep (GL (Fin m) k)) (τ' : IrrRep (GL (Fin m) k')) (c : ℂ), RepRel i (cls π) (cls π') → RepRel i (cls τ) (cls τ') → HasPairEps ψ π.ρ τ.ρ c → HasPairEps ψ' π'.ρ τ'.ρ c := by
  first | exact @GlobalTheory.LocLanglands.hasPairEps_transport | exact GlobalTheory.LocLanglands.hasPairEps_transport | (intros; apply GlobalTheory.LocLanglands.hasPairEps_transport <;> assumption)
end
