module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
public import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle116
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section
namespace GlobalTheory.UnitLemma.Desc

theorem norm_prod_one {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₁) :
    Algebra.norm F ((x, 1) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (x, 1) = (Algebra.lmul F R₁ x).prodMap (Algebra.lmul F R₂ 1) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₂), map_one LinearMap.det, mul_one]

theorem norm_one_prod {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₂) :
    Algebra.norm F ((1, x) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (1, x) = (Algebra.lmul F R₁ 1).prodMap (Algebra.lmul F R₂ x) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₁), map_one LinearMap.det, one_mul]

theorem coi_prod {R₁ R₂ : Type} [Ring R₁] [Ring R₂] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {e₁ : ι₁ → R₁} {e₂ : ι₂ → R₂} (h₁ : CompleteOrthogonalIdempotents e₁)
    (h₂ : CompleteOrthogonalIdempotents e₂) :
    CompleteOrthogonalIdempotents (Sum.elim (fun i => ((e₁ i, 0) : R₁ × R₂)) (fun j => ((0, e₂ j) : R₁ × R₂))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact Prod.ext (h₁.idem i).eq (mul_zero 0)
    · exact Prod.ext (mul_zero 0) (h₂.idem j).eq
  · rintro (i | j) (i' | j') hne
    · have hii : i ≠ i' := fun h => hne (congrArg Sum.inl h)
      exact Prod.ext (h₁.ortho hii) (mul_zero 0)
    · exact Prod.ext (mul_zero _) (zero_mul _)
    · exact Prod.ext (zero_mul _) (mul_zero _)
    · have hjj : j ≠ j' := fun h => hne (congrArg Sum.inr h)
      exact Prod.ext (mul_zero 0) (h₂.ortho hjj)
  · rw [Fintype.sum_sum_type]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, h₁.complete]
    · simp [Prod.snd_sum, h₂.complete]

theorem factor_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₁) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₁, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₁ f = f) ∧ (¬Q → f * σ₁ f = 0 ∧ e = f + σ₁ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (e, 0) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (e, 0) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(f, 0), Prod.ext hf.eq (mul_zero 0), fun h0 => hf0 (congrArg Prod.fst h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₁ : f * y₁ ≠ 0 := fun h0 => hy (Prod.ext h0 (zero_mul y₂))
    obtain ⟨z, hz⟩ := hfy y₁ hy₁
    exact ⟨(z, 0), Prod.ext hz (mul_zero _)⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ f, σ₂ 0) = (f, 0)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((f, 0) * (σ₁ f, σ₂ 0) : R₁ × R₂) = 0 ∧ (e, 0) = (f, 0) + (σ₁ f, σ₂ 0)
    rw [map_zero]
    exact ⟨Prod.ext h1 (mul_zero 0), Prod.ext h2 (add_zero 0).symm⟩

theorem factor_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₂) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₂ f = f) ∧ (¬Q → f * σ₂ f = 0 ∧ e = f + σ₂ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (0, e) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (0, e) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(0, f), Prod.ext (mul_zero 0) hf.eq, fun h0 => hf0 (congrArg Prod.snd h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₂ : f * y₂ ≠ 0 := fun h0 => hy (Prod.ext (zero_mul y₁) h0)
    obtain ⟨z, hz⟩ := hfy y₂ hy₂
    exact ⟨(0, z), Prod.ext (mul_zero _) hz⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ 0, σ₂ f) = (0, f)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((0, f) * (σ₁ 0, σ₂ f) : R₁ × R₂) = 0 ∧ (0, e) = (0, f) + (σ₁ 0, σ₂ f)
    rw [map_zero]
    exact ⟨Prod.ext (mul_zero 0) h1, Prod.ext (add_zero 0).symm h2⟩

theorem unit_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₁) (hu : IsUnit x) (hσ : σ₁ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((x, 1) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (x, 1) = (x, 1)) ∧
      ((x, 1) : R₁ × R₂) * (1 - (e, 0)) = 1 - (e, 0) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨hu, isUnit_one⟩, ?_⟩, ?_⟩
  · show (σ₁ x, σ₂ 1) = (x, 1)
    rw [hσ, map_one]
  · exact Prod.ext (by simpa using h1) (by simp)

theorem unit_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₂) (hu : IsUnit x) (hσ : σ₂ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((1, x) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (1, x) = (1, x)) ∧
      ((1, x) : R₁ × R₂) * (1 - (0, e)) = 1 - (0, e) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨isUnit_one, hu⟩, ?_⟩, ?_⟩
  · show (σ₁ 1, σ₂ x) = (1, x)
    rw [hσ, map_one]
  · exact Prod.ext (by simp) (by simpa using h1)

theorem isFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  intro K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ h₁ h₂
  obtain ⟨⟨hc₁, hf₁⟩, hπ₁⟩ := h₁
  obtain ⟨⟨hc₂, hf₂⟩, hπ₂⟩ := h₂
  refine ⟨⟨coi_prod hc₁ hc₂, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact factor_inl B₁.σ B₂.σ (e₁ i) _ _ Finset.inl_mem_disjSum (hf₁ i)
    · exact factor_inr B₁.σ B₂.σ (e₂ j) _ _ Finset.inr_mem_disjSum (hf₂ j)
  · rintro (i | j) hi
    · rw [Finset.inl_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₁ i hi
      obtain ⟨hA, hB⟩ := unit_inl B₁.σ B₂.σ (π₁ i) (e₁ i) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((π₁ i, 1) : B₁.A × B₂.A)) = -1
      rw [norm_prod_one]
      exact hη
    · rw [Finset.inr_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₂ j hi
      obtain ⟨hA, hB⟩ := unit_inr B₁.σ B₂.σ (π₂ j) (e₂ j) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((1, π₂ j) : B₁.A × B₂.A)) = -1
      rw [norm_one_prod]
      exact hη

end GlobalTheory.UnitLemma.Desc
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology

variable {K : UQ} (B : InvAlg K)

theorem eta_c (x : K.E) : K.eta (K.c x) = K.eta x := by
  unfold UQ.eta; rw [UnramNorm.val_c]

theorem norm_sigma (u : B.A) : Algebra.norm K.E (B.σ u) = K.c (Algebra.norm K.E u) := by
  have h := Algebra.norm_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) u
  rw [h, RingEquiv.apply_symm_apply]

theorem norm_ne_zero_of_isUnit {u : B.A} (hu : IsUnit u) : Algebra.norm K.E u ≠ 0 :=
  (hu.map (Algebra.norm K.E)).ne_zero

theorem eta_norm_mul_sigma {v : B.A} (hv : IsUnit v) : K.eta (Algebra.norm K.E (v * B.σ v)) = 1 := by
  rw [map_mul, norm_sigma, eta_mul (norm_ne_zero_of_isUnit B hv)
    ((map_ne_zero K.c).2 (norm_ne_zero_of_isUnit B hv)), eta_c, eta_sq]

theorem twist_mul {E : B.A} (hE : E * E = E) (x y : B.A) :
    (x * E + (1 - E)) * (y * E + (1 - E)) = x * y * E + (1 - E) := by
  linear_combination (x * y - x - y + 1) * hE

theorem twist_isUnit {E : B.A} (hE : E * E = E) {x : B.A} (hx : IsUnit x) : IsUnit (x * E + (1 - E)) := by
  obtain ⟨u, rfl⟩ := hx
  refine isUnit_iff_exists_inv.2 ⟨((u⁻¹ : B.Aˣ) : B.A) * E + (1 - E), ?_⟩
  rw [twist_mul B hE, Units.mul_inv, one_mul]; ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem e_mul_eS {e : ι → B.A} (he : OrthogonalIdempotents e) (i : ι) (I : Finset ι) :
    e i * eS B e I = if i ∈ I then e i else 0 := by
  unfold eS; rw [Finset.mul_sum]; split_ifs with h
  · rw [Finset.sum_eq_single i (fun j _ hji => he.ortho (Ne.symm hji)) (fun h' => absurd h h'), (he.idem i).eq]
  · exact Finset.sum_eq_zero fun j hj => he.ortho (fun hij => h (hij ▸ hj))

theorem eS_idem {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  show (∑ i ∈ I, e i) * eS B e I = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [e_mul_eS B he, if_pos hi]

theorem sigma_e {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : B.σ (e i) = e i := by
  obtain ⟨f, -, -, -, h1, h2⟩ := h.2 i
  by_cases hi : i ∈ S
  · rw [(h1 hi).1, (h1 hi).2]
  · rw [(h2 hi).2, map_add (f := _), B.σ_σ, add_comm]

theorem sigma_eS {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) : B.σ (eS B e I) = eS B e I := by
  unfold eS; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => sigma_e B h i

theorem chi_mul {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) {x y : B.A} (hx : IsUnit x)
    (hy : IsUnit y) : chi B e I (x * y) = chi B e I x * chi B e I y := by
  unfold chi
  have hE := eS_idem B he I
  rw [← twist_mul B hE, map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hx))
    (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy))]

theorem chi_norm {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) {w : B.A} (hw : IsUnit w) :
    chi B e I (w * B.σ w) = 1 := by
  unfold chi
  have hE := eS_idem B h.1.toOrthogonalIdempotents I
  have hσ : B.σ (w * eS B e I + (1 - eS B e I)) = B.σ w * eS B e I + (1 - eS B e I) := by
    rw [map_add (f := _), map_mul, map_sub, map_one, sigma_eS B h]
  rw [← twist_mul B hE, ← hσ]
  exact eta_norm_mul_sigma B (twist_isUnit B hE hw)

theorem eta_prod {s : Finset ι} (x : ι → K.E) (hx : ∀ i ∈ s, x i ≠ 0) :
    K.eta (∏ i ∈ s, x i) = ∏ i ∈ s, K.eta (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [UQ.eta, val]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      eta_mul (hx a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

theorem chi_prod {e π : ι → B.A} {S : Finset ι} (h : IsFrame B e π S) (I J : Finset ι) (hJ : J ⊆ S) :
    chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card := by
  have he := h.1.1.toOrthogonalIdempotents
  set E := eS B e I with hEdef
  have hE := eS_idem B he I

  have h1 : (∏ j ∈ J.filter (· ∉ I), π j) * E = E := by
    refine Finset.prod_induction _ (fun t => t * E = E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : E = (1 - e j) * E := by
      rw [sub_mul, one_mul, mul_comm (e j) E, hEdef, mul_comm, e_mul_eS B he, if_neg hjI, sub_zero]
    show π j * E = E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have h2 : (∏ j ∈ J.filter (· ∈ I), π j) * (1 - E) = 1 - E := by
    refine Finset.prod_induction _ (fun t => t * (1 - E) = 1 - E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : 1 - E = (1 - e j) * (1 - E) := by
      have := e_mul_eS B he j I
      rw [if_pos hjI] at this
      rw [← hEdef] at this
      linear_combination -this
    show π j * (1 - E) = 1 - E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have hprod : (∏ j ∈ J, π j) * E + (1 - E) = ∏ j ∈ J.filter (· ∈ I), π j := by
    rw [← Finset.prod_filter_mul_prod_filter_not J (· ∈ I), mul_assoc]
    rw [h1]
    linear_combination -h2
  unfold chi
  rw [← hEdef, hprod, map_prod, eta_prod]
  · rw [Finset.filter_mem_eq_inter]
    rw [Finset.prod_congr rfl fun j hj => (h.2 j (hJ (Finset.mem_inter.1 hj).1)).2.2, Finset.prod_const]
  · intro j hj
    exact norm_ne_zero_of_isUnit B (h.2 j (hJ (Finset.mem_filter.1 hj).1)).1.1

theorem mul_eq_zero_of_idem {e : ι → B.A} (he : OrthogonalIdempotents e) {i j : ι} (hij : i ≠ j) {a b : B.A}
    (ha : a * e i = a) (hb : b * e j = b) : a * b = 0 := by
  rw [← ha, ← hb, show a * e i * (b * e j) = a * b * (e i * e j) by ring, he.ortho hij, mul_zero]

theorem sum_mul_sum_diag {e : ι → B.A} (he : OrthogonalIdempotents e) (s : Finset ι) (a b : ι → B.A)
    (ha : ∀ i ∈ s, a i * e i = a i) (hb : ∀ i ∈ s, b i * e i = b i) :
    (∑ i ∈ s, a i) * (∑ j ∈ s, b j) = ∑ i ∈ s, a i * b i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact Finset.sum_eq_single i (fun j hj hji => mul_eq_zero_of_idem B he (Ne.symm hji) (ha i hi) (hb j hj))
    (fun h => absurd hi h)

theorem chi_plus {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) {y : B.A} (hy : B.Plus y) :
    chi B e S y = K.eta (Algebra.norm K.E y) := by
  have he := h.1.toOrthogonalIdempotents
  have hcomp := h.1.complete
  choose f hf using h.2
  set E := eS B e S with hEdef
  have hE : E * E = E := eS_idem B he S
  have hσE : B.σ E = E := sigma_eS B h S
  have hfe : ∀ i ∈ Sᶜ, f i * e i = f i := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, hid.eq, (h2 hiS).1, add_zero]
  have hge : ∀ i ∈ Sᶜ, B.σ (f i) * e i = B.σ (f i) := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, mul_comm (B.σ (f i)) (f i), (h2 hiS).1, zero_add, ← map_mul, hid.eq]
  set F := ∑ i ∈ Sᶜ, f i with hFdef
  set G := ∑ i ∈ Sᶜ, B.σ (f i) with hGdef
  have hGσ : G = B.σ F := by rw [hGdef, hFdef, map_sum]
  have hFF : F * F = F := by
    rw [hFdef, sum_mul_sum_diag B he _ f f hfe hfe]; exact Finset.sum_congr rfl fun i _ => (hf i).1.eq
  have hFG : F * G = 0 := by
    rw [hFdef, hGdef, sum_mul_sum_diag B he _ f _ hfe hge]
    exact Finset.sum_eq_zero fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).1
  have hGG : G * G = G := by rw [hGσ, ← map_mul, hFF]
  have hFE : F * E = 0 := by
    rw [hFdef, hEdef, eS, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
      mul_eq_zero_of_idem B he (fun hij => Finset.mem_compl.1 hi (by rw [hij]; exact hj)) (hfe i hi) (he.idem j).eq
  have hGE : G * E = 0 := by rw [hGσ, ← hσE, ← map_mul, hFE, map_zero]
  have hFGsum : F + G = 1 - E := by
    have h1 : F + G = ∑ i ∈ Sᶜ, e i := by
      rw [hFdef, hGdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).2.symm
    rw [h1, ← hcomp, ← Finset.sum_add_sum_compl S e, hEdef, eS]; ring
  set w := y * F + G + E with hwdef
  have hσw : B.σ w = y * G + F + E := by
    rw [hwdef, map_add (f := _), map_add (f := _), map_mul, hy.2, hσE, hGσ, B.σ_σ]
  have hw : w * B.σ w = y * (1 - E) + E := by
    rw [hσw, ← hFGsum]
    linear_combination (y ^ 2 + 1) * hFG + y * hFF + (y + 1) * hFE + y * hGG + (y + 1) * hGE + hE
  have hE' : (1 - E) * (1 - E) = 1 - E := by linear_combination hE
  have hwwU : IsUnit (w * B.σ w) := by
    have := twist_isUnit B hE' hy.1
    rwa [sub_sub_cancel, ← hw] at this
  have hwU : IsUnit w := isUnit_of_mul_isUnit_left hwwU
  have hsplit : y = (y * E + (1 - E)) * (w * B.σ w) := by
    rw [hw]; linear_combination (y ^ 2 - 2 * y + 1) * hE
  unfold chi
  rw [← hEdef]
  conv_rhs => rw [hsplit]
  rw [map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy.1)) (norm_ne_zero_of_isUnit B hwwU),
    eta_norm_mul_sigma B hwU, mul_one]

theorem chi_frame_props : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S →
    (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧
    (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧
    (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧
    (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  intro K B ι _ _ e π S h
  exact ⟨fun I x y hx hy => chi_mul B h.1.1.toOrthogonalIdempotents I hx hy, fun I w hw => chi_norm B h.1 I hw,
    fun I J _ hJ => chi_prod B h I J hJ, fun y hy => chi_plus B h.1 hy⟩

end GlobalTheory.UnitLemma.Desc
end
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem cyclotomic_isLocallyConstant_mod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ) (hε : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) (N : ℕ) :
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  have hp : p.Prime := Fact.out
  have hne : ((p ^ N : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast pow_ne_zero N hp.ne_zero
  haveI : NeZero ((p ^ N : ℕ) : PadicAlgCl p) := ⟨hne⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ N)
  have hint : IsIntegral K ζ := (hζ.isIntegral (pow_pos hp.pos N)).tower_top
  haveI : FiniteDimensional K (IntermediateField.adjoin K {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hU : IsOpen ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have key : ∀ σ τ : Formalism.GaloisCohomology.GK p K, σ ζ = τ ζ →
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O) =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε τ : Oˣ) : O) := by
    intro σ τ h
    obtain ⟨a, ha, ha'⟩ := hε σ N ζ hζ.pow_eq_one
    obtain ⟨b, hb, hb'⟩ := hε τ N ζ hζ.pow_eq_one
    have hab : ζ ^ a = ζ ^ b := by rw [← ha, ← hb, h]
    have hmod : a ≡ b [MOD p ^ N] := by
      rw [hζ.eq_orderOf]
      exact (hζ.isOfFinOrder (pow_ne_zero N hp.ne_zero)).pow_eq_pow_iff_modEq.1 hab
    obtain ⟨c, hc⟩ := hmod.dvd
    have hc' : (b : O) - (a : O) = (p : O) ^ N * (c : O) := by
      have := congrArg (Int.cast : ℤ → O) hc
      push_cast at this
      exact this
    rw [Ideal.Quotient.eq]
    have e : ((ε σ : Oˣ) : O) - ((ε τ : Oˣ) : O) =
        (((ε σ : Oˣ) : O) - a) - (((ε τ : Oˣ) : O) - b) - ((b : O) - a) := by ring
    rw [e, hc']
    exact Ideal.sub_mem _ (Ideal.sub_mem _ ha' hb')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [IsLocallyConstant.iff_exists_open]
  intro σ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)),
    hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro τ hτ
    apply key
    have h1 : (σ⁻¹ * τ) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (IntermediateField.mem_adjoin_simple_self K ζ)
    have h2 := congrArg σ h1
    simpa using h2

end GlobalTheory.ShapeNeg
end

section

open scoped PowerSeries Pointwise

theorem _root_.GlobalTheory.T.X_pow_mem_map_sup_span_pow_of_frobenius_bound : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ (a e h b : ℕ) [NeZero a] (I : ZMod a → Ideal O⟦X⟧), 1 ≤ b → h + b ≤ l → (∀ τ, ∃ s : ℕ, PowerSeries.X ^ s ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) → (∀ τ, ∀ x ∈ I τ, (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x ∈ (I (τ - 1)).map φ) → ∀ τ, (PowerSeries.X : O⟦X⟧) ^ (e * (h + b)) ∈ (I τ).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  first | exact @GlobalTheory.frobenius_ideal_degree_bound | exact GlobalTheory.frobenius_ideal_degree_bound | (intros; apply GlobalTheory.frobenius_ideal_degree_bound <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.pow_dvd_bound_or_exists_valuationSubring_dvd : ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) → (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨ ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by
  first | exact @GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd | exact GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd | (intros; apply GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd <;> assumption)
end

section

open scoped BigOperators

namespace GlobalTheory.GaussSubspace

theorem sum_card_subspaces :
    ∀ (k : Type) [Field k] [Finite k] (m : ℕ) (A : Type) [CommRing A] (Y : A), ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ j * (Nat.card k : A) ^ (j * (j - 1) / 2) * (Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W = j} : A) * Y ^ j = ∏ i ∈ Finset.range m, (1 - (Nat.card k : A) ^ i * Y) := by
  intro k _ _ m A _ Y
  rw [← GlobalTheory.GaussCount.gauss_formula (Nat.card k) A Y m]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := GlobalTheory.GaussCount.subspaceCount k (Fin m → k) j
  rw [Module.finrank_fin_fun] at h
  rw [h]

end GlobalTheory.GaussSubspace
end
