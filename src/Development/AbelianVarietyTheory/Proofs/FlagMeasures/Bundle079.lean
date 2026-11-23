module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle073
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PhaseProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem coef_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) (a : Fin r) :
    (G.S p).coef sf se m a = algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) *
      (A.loc p).ιE (∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) := by
  have hexp : r - (a : ℕ) = (r - ((a.succ : Fin (r + 1)) : ℕ)) + 1 := by
    have := a.isLt
    simp only [Fin.val_succ]
    omega
  set t := algebraMap (A.loc p).Fp (A.loc p).Ep
    ((G.c p : (A.loc p).Fp) ^ (r - ((a.succ : Fin (r + 1)) : ℕ))) with ht
  set u := algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) with hu
  have key : ∀ i, t * m (sf a.succ) i = (A.loc p).ιE (n (f a.succ) i) := by
    intro i
    have h1 := congrArg m (hsf a.succ)
    rw [map_smul, hx] at h1
    exact congrFun h1 i
  have hcj : ∀ j, (A.L p).cj (se a j) = t * u * (A.loc p).ιE (sig (es a j)) := by
    intro j
    rw [A.L_cj p, hse a]
    change (A.loc p).cj (algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) * (A.loc p).ιE (es a j)) = _
    rw [map_mul, AlgEquiv.commutes, (A.loc p).cj_ιE, hexp, pow_succ, map_mul]

  simp only [Frames.coef, Frames.h, hf, map_sum, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hcj j, (G.Hm_eq p), Matrix.map_apply]
  linear_combination (u * (A.loc p).ιE (G.Hm i j) * (A.loc p).ιE (sig (es a j))) * key i

theorem psiOf_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (δ : ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹)))
    (h2 : (G.c p : (A.loc p).Fp) * g = δ * (G.S p).th)
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) :
    (G.S p).psiOf sf se m = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) / g))) := by
  have hth : (G.S p).th ≠ 0 := by
    unfold Frames.th
    split_ifs
    · exact fun h => (G.S p).ϖ_irr.ne_zero (Subtype.ext h)
    · exact one_ne_zero
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  set X : E := ∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j) with hX
  have hXg : (A.loc p).ιE X = (A.loc p).ιE (X / g) * algebraMap (A.loc p).Fp (A.loc p).Ep (g : (A.loc p).Fp) := by
    rw [map_natCast, ← map_natCast (A.loc p).ιE g, ← map_mul, div_mul_cancel₀ _ hgE]
  have hsc : (G.S p).th⁻¹ * ((G.c p : (A.loc p).Fp) * g) * (δ : (A.loc p).Fp)⁻¹ = 1 := by
    rw [h2]
    field_simp
  have hsum : ∑ j, (G.S p).coef sf se m j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X := by

    rw [hX, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => coef_eq A G p n m hx sf se f es hsf hse a
  have harg : algebraMap (A.loc p).Fp (A.loc p).Ep (G.S p).th⁻¹ *
      (algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X) *
      algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹ = (A.loc p).ιE (X / g) := by
    have h3 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) hsc
    simp only [map_mul, map_one] at h3
    rw [hXg]
    linear_combination ((A.loc p).ιE (X / g)) * h3
  unfold Frames.psiOf
  rw [hsum, h1, harg, map_neg (A.loc p).ιE]

theorem main {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) [StarRing E] (hCM : Formalism.BasicNotions.CMData F E)
    (hsig : ∀ x, sig x = star x) (δ : ∀ p, ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ p y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ p : (A.loc p).Fp))⁻¹)))
    (h2 : ∀ p, (G.c p : (A.loc p).Fp) * g = δ p * (G.S p).th)
    (n : G.GLV) (m : ∀ p, (G.S p).GLV) (hx : ∀ p, A.Ext p n (m p)) :
    (∏ᶠ p, (G.S p).psi (m p) = Complex.exp (-(2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ E ((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g) : ℚ) : ℂ)))) ∧
    (∏ᶠ p, (G.S p).psi' (m p) = Complex.exp (-(2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ E ((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g) : ℚ) : ℂ)))) ∧
    {p | (G.S p).psi (m p) ≠ 1 ∨ (G.S p).psi' (m p) ≠ 1}.Finite := by
  have hp : ∀ p, (G.S p).psi (m p) = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g))) := fun p =>
    psiOf_eq A G p (δ p) g hg (h1 p) (h2 p) n (m p) (hx p) (G.S p).f (G.S p).es G.f G.es
      (G.f_eq p) (G.es_eq p)
  have hp' : ∀ p, (G.S p).psi' (m p) = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g))) := fun p =>
    psiOf_eq A G p (δ p) g hg (h1 p) (h2 p) n (m p) (hx p) (G.S p).f' (G.S p).es' G.f' G.es'
      (G.f'_eq p) (G.es'_eq p)
  obtain ⟨s1, e1⟩ := GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace hCM sig hsig A.loc
    (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g))
  obtain ⟨s2, e2⟩ := GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace hCM sig hsig A.loc
    (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g))
  refine ⟨?_, ?_, ?_⟩
  · simp only [hp]
    rw [e1, map_neg, Rat.cast_neg, mul_neg]
  · simp only [hp']
    rw [e2, map_neg, Rat.cast_neg, mul_neg]
  · refine (s1.union s2).subset ?_
    intro p hq
    rcases hq with hq | hq
    · left
      simpa [Function.mem_mulSupport, hp p] using hq
    · right
      simpa [Function.mem_mulSupport, hp' p] using hq

end GlobalTheory.HL.PhaseProduct
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_integers_localisation_iff_sum_cmData : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by
  first | exact @GlobalTheory.LocSpan.mem_O_iff | exact GlobalTheory.LocSpan.mem_O_iff | (intros; apply GlobalTheory.LocSpan.mem_O_iff <;> assumption)
end

section

open NumberField
open scoped TensorProduct

noncomputable section
open Classical

namespace GlobalTheory.VectorInclusion

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def vecIncl (x : Fin n → E) : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F :=
  fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)

theorem inclE_int_mem (c : 𝓞 E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E) ∈ Formalism.MainNotions.S.IntAf F E := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(c : E), ⟨c, rfl⟩⟩, ?_⟩
  rfl

theorem vecIncl_add (x y : Fin n → E) :
    vecIncl (F := F) (x + y) = vecIncl (F := F) x + vecIncl (F := F) y := by
  funext i; simp [vecIncl, map_add (f := _)]

theorem vecIncl_zero : vecIncl (F := F) (0 : Fin n → E) = 0 := by
  funext i; simp [vecIncl]

theorem vecIncl_smul (c : 𝓞 E) (x : Fin n → E) :
    vecIncl (F := F) (c • x) =
      (⟨Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E), inclE_int_mem c⟩ : Formalism.MainNotions.S.IntAf F E) •
        vecIncl (F := F) x := by
  funext i
  simp only [vecIncl, Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

theorem lamAf_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) := by
  obtain ⟨s, hs⟩ := hL
  refine ⟨s.image (vecIncl (F := F)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    have hxL : x ∈ L := hs ▸ Submodule.subset_span hx
    exact ⟨⟨x, hxL⟩, rfl⟩
  · unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro y ⟨⟨x, hx⟩, rfl⟩
    have key : ∀ z ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)),
        vecIncl (F := F) z ∈ Submodule.span (Formalism.MainNotions.S.IntAf F E)
          ((s.image (vecIncl (F := F)) : Finset _) : Set (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        apply Submodule.subset_span
        simp only [Finset.coe_image]
        exact ⟨z, hz, rfl⟩
      | zero => rw [vecIncl_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [vecIncl_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [vecIncl_smul]; exact Submodule.smul_mem _ _ ha
    rw [← hs] at hx
    exact key x hx

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) :=
  fun L hL => lamAf_fg L hL

end GlobalTheory.VectorInclusion

end
end

section

open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace GlobalTheory

theorem exists_gram_factor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {k : ℕ}
    (x : Fin k → E) : ∃ C : Fin k → Fin k → ℂ, ∀ l l',
      ⟪x l, x l'⟫_ℂ = ∑ r, (starRingEnd ℂ) (C r l) * C r l' := by
  have h := (Matrix.posSemidef_gram ℂ x).nonneg
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  refine ⟨fun r l => C r l, fun l l' => ?_⟩
  have := congrFun (congrFun hC l) l'
  simpa [Matrix.gram_apply, Matrix.mul_apply, Matrix.star_apply] using this

theorem exists_normSq_tens_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (tens : (∀ v, H v) → Hs)
    (ht : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (v₀ : ι) {k : ℕ}
    (u : Fin k → ∀ v, H v) :
    ∃ C : ({v // v ≠ v₀} → Fin k) → Fin k → ℂ, ∀ a : Fin k → H v₀,
      ‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 = ∑ r, ‖∑ l, C r l • a l‖ ^ 2 := by
  choose D hD using fun v : {v // v ≠ v₀} => exists_gram_factor (fun l => u l v.1)
  refine ⟨fun r l => ∏ v, D v (r v) l, fun a => ?_⟩
  have key : ∀ l l', ⟪tens (Function.update (u l) v₀ (a l)),
      tens (Function.update (u l') v₀ (a l'))⟫_ℂ =
      ∑ r : {v // v ≠ v₀} → Fin k,
        ⟪(∏ v, D v (r v) l) • a l, (∏ v, D v (r v) l') • a l'⟫_ℂ := by
    intro l l'
    rw [ht, Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [Function.update_self]
    have h1 : ∏ v : {v // v ≠ v₀}, ⟪Function.update (u l) v₀ (a l) v.1,
        Function.update (u l') v₀ (a l') v.1⟫_ℂ =
        ∏ v : {v // v ≠ v₀}, ∑ r, (starRingEnd ℂ) (D v r l) * D v r l' := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Function.update_of_ne v.2, Function.update_of_ne v.2, hD]
    rw [h1, Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [inner_smul_left, inner_smul_right, Finset.prod_mul_distrib, map_prod]
    ring
  have hc : ((‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 : ℝ) : ℂ) =
      ((∑ r : {v // v ≠ v₀} → Fin k, ‖∑ l, (∏ v, D v (r v) l) • a l‖ ^ 2 : ℝ) : ℂ) := by
    have hn : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E),
        ((‖z‖ ^ 2 : ℝ) : ℂ) = ⟪z, z⟫_ℂ := by
      intro E _ _ z
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [Complex.ofReal_sum, hn]
    simp only [hn, sum_inner, inner_sum, key]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  exact_mod_cast hc

theorem sum_normSq_tens_update_le :
    ∀ (B : RowsAut) (v₀ : InfinitePlace B.I.F) (S : ∀ v, Submodule ℂ (B.H v)) (m : ℕ) (L : Fin m → (S v₀ →ₗ[ℂ] B.H v₀)) (β : ℝ), (∀ y : S v₀, ∑ i, ‖L i y‖ ^ 2 ≤ β * ‖y‖ ^ 2) → ∀ (k : ℕ) (u : Fin k → ∀ v, S v), open Classical in ∑ i, ‖∑ l, B.tens (Function.update (fun v => (u l v : B.H v)) v₀ (L i (u l v₀)))‖ ^ 2 ≤ β * ‖∑ l, B.tens (fun v => (u l v : B.H v))‖ ^ 2 := by
  classical
  intro B v₀ S m L β hL k u
  obtain ⟨C, hC⟩ := exists_normSq_tens_update B.tens B.tens_spec.1 v₀
    (fun l v => (u l v : B.H v))
  have h0 := hC (fun l => (u l v₀ : B.H v₀))
  have hu : ∀ l, Function.update (fun v => (u l v : B.H v)) v₀ (u l v₀ : B.H v₀) =
      fun v => (u l v : B.H v) := fun l => Function.update_eq_self v₀ _
  simp only [hu] at h0
  rw [h0, Finset.mul_sum]
  have h1 : ∀ i, _ := fun i => hC (fun l => L i (u l v₀))
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r _ => ?_
  have := hL (∑ l, C r l • u l v₀)

  simp only [map_sum, map_smul] at this
  refine this.trans_eq ?_
  rw [← Submodule.norm_coe]
  simp

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalUnitaryTop

theorem linearIndependent_iff_smul_basis {K S V ι α : Type} [Field K] [CommRing S] [Algebra K S]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower K S V] [Fintype ι] [Fintype α]
    (b : Module.Basis ι K S) (X : α → V) :
    LinearIndependent S X ↔ LinearIndependent K fun p : ι × α => b p.1 • X p.2 := by
  refine ⟨fun h => linearIndependent_smul b.linearIndependent h, fun h => ?_⟩
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 := h (fun p => b.repr (g p.2) p.1) (by
    rw [← hg, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr (g j), Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => (smul_assoc _ _ _).symm)
  exact b.ext_elem fun k => by simpa using h0 (k, i)

theorem isOpen_linearIndependent {K S ι α β : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [CommRing S] [Algebra K S] [TopologicalSpace S] [IsModuleTopology K S] [IsTopologicalRing S]
    [Fintype ι] [Fintype α] [Fintype β] (b : Module.Basis ι K S) :
    IsOpen {X : α → β → S | LinearIndependent S X} := by
  let e : (β → S) ≃ₗ[K] (β → ι → K) := LinearEquiv.piCongrRight fun _ => b.equivFun
  have hb : Continuous b.equivFun :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc : Continuous fun (X : α → β → S) (p : ι × α) => e (b p.1 • X p.2) := by
    refine continuous_pi fun p => continuous_pi fun j => ?_
    have : Continuous fun X : α → β → S => b p.1 * X p.2 j := by fun_prop
    exact hb.comp this
  have ho := (isOpen_setOfPred_linearIndependent (𝕜 := K) (E := β → ι → K) (ι := ι × α)).preimage hc
  convert ho using 1
  ext X
  rw [Set.mem_ofPred_eq, linearIndependent_iff_smul_basis b]
  exact (e.toLinearMap.linearIndependent_iff e.ker).symm

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  intro F E _ _ _ _ _ σ _ n J _ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hr : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Fv F v) σ n J
  refine ⟨hr, e.isClosedEmbedding.locallyCompactSpace, e.isEmbedding.t2Space,
    e.secondCountableTopology, inferInstanceAs (IsTopologicalGroup (HR (Fv F v) σ J)), h1, h3, h2,
    fun a => ⟨?_, ?_⟩⟩
  · letI : NontriviallyNormedField (Fv F v) :=
      Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
    exact isOpen_linearIndependent (K := Fv F v)
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))
  · have hm : Continuous fun g : HA (Fv F v) σ J => HA.mat (Fv F v) σ J g :=
      continuous_subtype_val
    have hv : Continuous fun g : HA (Fv F v) σ J =>
        ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := Units.continuous_val.comp hm
    refine continuous_pi fun b => ?_
    exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.LocalUnitaryTop
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal

namespace GlobalTheory.ArchUnitaryTop

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n a : ℕ) (J : Matrix (Fin n) (Fin n) E), ContinuousSMul (HA (Ainf F) σ J) (Fin a → Fin n → Ainf F ⊗[F] E) ∧ BorelSpace (Fin a → Fin n → Ainf F ⊗[F] E) ∧ SecondCountableTopology (Fin a → Fin n → Ainf F ⊗[F] E) ∧ T2Space (Fin a → Fin n → Ainf F ⊗[F] E) ∧ IsTopologicalGroup (HA (Ainf F) σ J) ∧ LocallyCompactSpace (HA (Ainf F) σ J) ∧ SecondCountableTopology (HA (Ainf F) σ J) ∧ T2Space (HA (Ainf F) σ J) := by
  intro F E _ _ _ _ _ σ n a J
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (Ainf F ⊗[F] E) := e.isEmbedding.t2Space
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ n J
  refine ⟨⟨?_⟩, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsTopologicalGroup (HR (Ainf F) σ J)), h1, h2, h3⟩
  have hm : Continuous fun g : HA (Ainf F) σ J => HA.mat (Ainf F) σ J g :=
    continuous_subtype_val
  have hv : Continuous fun g : HA (Ainf F) σ J =>
      ((HA.mat (Ainf F) σ J g : GL (Fin n) (Ainf F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := Units.continuous_val.comp hm
  refine continuous_pi fun b => ?_
  exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.ArchUnitaryTop
end
