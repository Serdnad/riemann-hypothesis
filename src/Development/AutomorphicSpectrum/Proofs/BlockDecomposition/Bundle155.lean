module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle136
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle134
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045

@[expose] public section

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

section Tuples
variable {ι : Type}

theorem cons_comp_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Fin.succAbove_zero]

theorem cons_comp_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons a (i ∘ k.succAbove) := by
  funext t
  cases t using Fin.cases with
  | zero => simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.cons_zero]
  | succ t => simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]

theorem mem_ent_cons [DecidableEq ι] {n : ℕ} {a x : ι} {i : Fin n → ι}
    (h : x ∈ ent (Fin.cons a i : Fin (n + 1) → ι)) : x = a ∨ x ∈ ent i := by
  simp only [ent, Finset.mem_image, Finset.mem_univ, true_and] at h ⊢
  obtain ⟨k, rfl⟩ := h
  cases k using Fin.cases with
  | zero =>
    left
    simp only [Fin.cons_zero]
  | succ k =>
    right
    exact ⟨k, by simp only [Fin.cons_succ]⟩

end Tuples

section Coordinates
variable {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W] [Module K W] {Λ : Type}
  (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι)

def Sup (S : Finset ι) (w : W) : Prop := ∀ l, b.repr w l ≠ 0 → good' l ∧ T l ⊆ S

theorem mem_span_iff (S : Finset ι) (w : W) :
    w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S}) ↔ Sup b good' T S w := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h l hl
    exact h (Finsupp.mem_support_iff.2 hl)
  · intro h l hl
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hl
    exact h l hl

theorem coord_sum {n : ℕ} (D : Fin n → W) (l : Λ) :
    b.repr (∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • D k) l = ∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • b.repr (D k) l := by

  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Finsupp.smul_apply]


open Classical in
def contr {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) : W :=
  b.repr.symm (Finsupp.onFinset (Finset.univ.biUnion fun a' : ι => (b.repr (C (Fin.cons a' i))).support)
    (fun l => if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0) (by
      intro l hl
      by_cases h : good' l
      · rw [dif_pos h] at hl
        exact Finset.mem_biUnion.2 ⟨a l h, Finset.mem_univ _, Finsupp.mem_support_iff.2 hl⟩
      · rw [dif_neg h] at hl
        exact absurd rfl hl))

open Classical in
theorem contr_apply {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) (l : Λ) :
    b.repr (contr b good' C a i) l = if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0 := by
  unfold contr
  rw [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]

theorem contr_sup {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (a : ∀ l, good' l → ι) (ha : ∀ l h, a l h ∉ T l) (i : Fin n → ι) :
    Sup b good' T (ent i) (contr b good' C a i) := by
  intro l hl
  rw [contr_apply] at hl
  by_cases h : good' l
  · rw [dif_pos h] at hl
    obtain ⟨-, hT⟩ := hC _ l hl
    refine ⟨h, fun x hx => ?_⟩
    rcases mem_ent_cons (hT hx) with rfl | hx'
    · exact absurd hx (ha l h)
    · exact hx'
  · rw [dif_neg h] at hl
    exact absurd rfl hl

theorem homotopy {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (hZ : ∀ i : Fin (n + 2) → ι, ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • C (i ∘ k.succAbove) = 0)
    (a : ∀ l, good' l → ι) (i : Fin (n + 1) → ι) :
    ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • contr b good' C a (i ∘ k.succAbove) = C i := by
  apply b.repr.injective
  ext l
  rw [coord_sum]
  simp only [contr_apply]
  by_cases h : good' l
  · simp only [dif_pos h]
    have hz := congrArg (fun w => b.repr w l) (hZ (Fin.cons (a l h) i))
    rw [Fin.sum_univ_succ] at hz

    simp only [Fin.val_zero, pow_zero, one_smul, cons_comp_zero, Fin.val_succ, cons_comp_succ,
    map_add, map_sum, map_zsmul, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, pow_succ, mul_neg, mul_one,
    neg_smul, Finset.sum_neg_distrib, map_neg, Finsupp.coe_neg, Pi.neg_apply] at hz
    rw [← sub_eq_add_neg, sub_eq_zero] at hz
    exact hz.symm
  · simp only [dif_neg h, smul_zero, Finset.sum_const_zero]
    by_contra hne
    exact h (hC i l (Ne.symm hne)).1

end Coordinates

section Main

theorem j_dZ {ι : Type} [DecidableEq ι] {W : Type} [AddCommGroup W] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W)
    (hr : ∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    j (ent i) (dZ M r m c i) = ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) := by

  simp only [dZ, map_sum, map_zsmul, hr]

theorem exP_of_basis : ∀ {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W]
    [Module K W] {Λ : Type} (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι),
    (∀ l, good' l → T l ≠ Finset.univ) → ∀ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W), (∀ S, Function.Injective (j S)) →
    (∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) →
    (∀ S w, (∃ x, j S x = w) ↔ w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S})) → ExP M r := by
  intro K _ ι _ _ W _ _ Λ b good' T hT M _ r j hj hr hspan
  have hout : ∀ l, good' l → ∃ y, y ∉ T l := by
    intro l hl
    by_contra hc
    push Not at hc
    exact hT l hl (Finset.eq_univ_iff_forall.2 hc)
  choose a ha using hout
  have hsup : ∀ S (x : M S), Sup b good' T S (j S x) := fun S x =>
    (mem_span_iff b good' T S _).1 ((hspan S _).1 ⟨x, rfl⟩)
  have hlift : ∀ S w, Sup b good' T S w → ∃ x, j S x = w := fun S w h =>
    (hspan S w).2 ((mem_span_iff b good' T S w).2 h)
  refine ⟨fun x hx => ?_, fun c hc => ?_, fun m c hc => ?_⟩
  · have hw : j ∅ x = 0 := by
      apply b.repr.injective
      ext l
      rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_contra hne
      obtain ⟨hg, -⟩ := hsup ∅ x l hne
      have h0 := hr (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x
      have hx0 : r (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x = 0 := hx _
      rw [hx0, map_zero] at h0
      rw [← h0] at hne
      exact hne (by rw [map_zero, Finsupp.coe_zero, Pi.zero_apply])
    exact hj ∅ (hw.trans (map_zero (j ∅)).symm)
  · have hZ : ∀ i : Fin (0 + 2) → ι,
        ∑ k : Fin (0 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr 0 c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (0 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) := fun i => hsup _ (c i)
    have hw := contr_sup b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs a ha Fin.elim0
    have he : ent (Fin.elim0 : Fin 0 → ι) = ∅ := by simp [ent]
    rw [he] at hw
    obtain ⟨x, hx⟩ := hlift ∅ _ hw
    refine ⟨x, fun i => hj _ ?_⟩
    rw [hr, hx]
    have hh := homotopy b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs hZ a i
    rw [Fin.sum_univ_succ] at hh
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero,
      one_smul] at hh
    convert hh using 2
  · have hZ : ∀ i : Fin (m + 1 + 2) → ι,
        ∑ k : Fin (m + 1 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr (m + 1) c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (m + 1 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) :=
      fun i => hsup _ (c i)
    have hb : ∀ i' : Fin (m + 1) → ι, ∃ x : M (ent i'),
        j (ent i') x = contr b good' (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) a i' :=
      fun i' => hlift _ _ (contr_sup b good' T _ hCs a ha i')
    choose b' hb' using hb
    refine ⟨b', funext fun i => hj _ ?_⟩
    rw [j_dZ M r j hr m b' i]
    simp only [hb']
    exact homotopy b good' T (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) hCs hZ a i

end Main

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
end
end

section

set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD

variable {K : Type} [Field K] {n d : ℕ}

theorem monL_zero' : monL K (0 : Gam n d) = 1 := rfl

theorem monL_add' (g g' : Gam n d) : monL K (g + g') = monL K g * monL K g' := by
  unfold monL
  rw [mon_mul]

theorem monL_neg_mul (g : Gam n d) : monL K (-g) * monL K g = 1 := by
  rw [← monL_add', neg_add_cancel, monL_zero']

def lam (K : Type) [Field K] {n d : ℕ} (g : Gam n d) : Ω[Lr K n d⁄K] :=
  monL K (-g) • KaehlerDifferential.D K (Lr K n d) (monL K g)

theorem lam_add (g g' : Gam n d) : lam K (g + g') = lam K g + lam K g' := by
  unfold lam
  have h1 : monL K (-(g + g')) = monL K (-g) * monL K (-g') := by
    rw [neg_add, monL_add']
  have e1 : monL K (-g) * monL K (-g') * monL K g = monL K (-g') := by
    rw [mul_comm (monL K (-g)), mul_assoc, monL_neg_mul, mul_one]
  have e2 : monL K (-g) * monL K (-g') * monL K g' = monL K (-g) := by
    rw [mul_assoc, monL_neg_mul, mul_one]
  rw [monL_add', Derivation.leibniz, smul_add, smul_smul, smul_smul, h1, e1, e2]
  exact add_comm _ _

def lamHom (K : Type) [Field K] (n d : ℕ) : Gam n d →+ Ω[Lr K n d⁄K] :=
  AddMonoidHom.mk' (lam K) lam_add

theorem exp_eq_sum (g : Gam n d) : g = ∑ e, g e • (oneE e : Gam n d) := by
  funext x
  simp [oneE, Finset.sum_apply, Pi.single_apply]

theorem lam_eq_sum (g : Gam n d) : lam K g = ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  have h : lam K g = lamHom K n d g := rfl
  rw [h]
  conv_lhs => rw [exp_eq_sum g]

  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_zsmul]
  rfl

theorem D_monL (g : Gam n d) :
    KaehlerDifferential.D K (Lr K n d) (monL K g) = monL K g • ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  rw [← lam_eq_sum]
  unfold lam
  rw [smul_smul, mul_comm, monL_neg_mul, one_smul]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD
end
end

section

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem dZ_addEquiv_apply {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    e _ (dZ M r m c i) = dZ N r' m (fun i => e _ (c i)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dZ, map_sum, map_zsmul, hn]

theorem dZ_eq_zero_of_addEquiv {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, N (ent i)) (hc : dZ N r' m c = 0) :
    dZ M r m (fun i => (e _).symm (c i)) = 0 := by
  funext i
  apply (e _).injective
  rw [dZ_addEquiv_apply M N r r' e hn m, Pi.zero_apply, map_zero]
  simp only [AddEquiv.apply_symm_apply]
  exact congrFun hc i

theorem exP_of_addEquiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  intro ι _ M N _ _ r r' e hn hM
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : (e ∅).symm x = 0 := by
      apply h0
      intro i
      have h7 := hn (Finset.empty_subset (ent i)) ((e ∅).symm x)
      rw [AddEquiv.apply_symm_apply] at h7
      have h8 : r' (Finset.empty_subset (ent i)) x = 0 := hx i
      rw [h8] at h7
      exact (e _).injective (h7.trans (map_zero _).symm)
    simpa using congrArg (e ∅) hx'
  · intro c hc
    obtain ⟨x, hx⟩ := h1 (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn 0 c hc)
    refine ⟨e ∅ x, fun i => ?_⟩
    have h5 : r (Finset.empty_subset (ent i)) x = (e _).symm (c i) := hx i
    have h6 := hn (Finset.empty_subset (ent i)) x
    rw [h5, AddEquiv.apply_symm_apply] at h6
    exact h6.symm
  · intro m c hc
    obtain ⟨b, hb⟩ := h2 m (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn (m + 1) c hc)
    refine ⟨fun i => e _ (b i), ?_⟩
    funext i
    have h3 := dZ_addEquiv_apply M N r r' e hn m b i
    have h4 : dZ M r m b i = (e _).symm (c i) := congrFun hb i
    rw [h4, AddEquiv.apply_symm_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end

section

set_option autoImplicit false

noncomputable section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

theorem cech_d_eq_dZ (P : PM.{0} R ι) (n : ℕ) (c : P.cech.X n) :
    P.cech.d n c = dZ P.M (fun h x => P.res h x) n c := by
  funext i
  simp only [CrystallineSemistableComparison.Cos.d, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, dZ]
  rfl

theorem cech_d_aug (P : PM.{0} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  rw [cech_d_eq_dZ]
  funext i
  have key : ∀ (k : Fin 2), P.res (ent_comp i k.succAbove) (P.aug x (i ∘ k.succAbove)) =
      P.res (Finset.empty_subset (ent i)) x := fun k => P.res_comp _ _ x
  simp only [dZ, Fin.sum_univ_two, key]
  simp
  rfl

theorem ex_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι),
    ExP P.M (fun h x => P.res h x) → P.Ex := by
  intro R _ ι _ P h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨cech_d_aug P, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [one_smul]
    exact h0 x fun i => congrFun hx i
  · obtain ⟨x, hx⟩ := h1 y ((cech_d_eq_dZ P 0 y).symm.trans hy)
    exact ⟨x, (funext hx).trans (one_smul _ _).symm⟩
  · obtain ⟨b, hb⟩ := h2 n y ((cech_d_eq_dZ P (n + 1) y).symm.trans hy)
    exact ⟨b, ((cech_d_eq_dZ P n b).trans hb).trans (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.cech_structure_sheaf_comparison : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) :=
  @cech_OSys_homology_equiv
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.card_orthonormal_frames_hermitian_space : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | exact GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.tube_transform_independent_of_base : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω → ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | exact GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.lattice_coset_scaled_riemann_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), IsStdInf li → ∀ (ι : Type) [Fintype ι] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun x : latCoset I x0 => φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) ∧ Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : latCoset I x0, φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ * ∫ y, φ y ∂(Measure.pi fun _ => li))) := by
  first | exact @GlobalTheory.CompanionTheory.Equi.lat_sum | exact GlobalTheory.CompanionTheory.Equi.lat_sum | (intros; apply GlobalTheory.CompanionTheory.Equi.lat_sum <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi

theorem _root_.GlobalTheory.T.locally_constant_finite_ball_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : (Fin n → k) → E) (s S : kˣ), (∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v) → (∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) → ∃ R : Finset (Fin n → k), ∀ v : Fin n → k, φ v = ∑ x ∈ R, @ite _ (Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s) (Classical.propDecidable _) (φ x) 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates | exact GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.twisted_invariant_small_boxes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V), v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype) → ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | exact GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

theorem _root_.GlobalTheory.T.fibre_representation_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | exact GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

theorem _root_.GlobalTheory.T.omega_equiv_induced_fibre : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.fibStr | exact GlobalTheory.CompanionTheory.ThetaGLLen.fibStr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.fibStr <;> assumption)
end
