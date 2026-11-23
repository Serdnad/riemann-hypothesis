module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle276
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent

section Algebra

variable {F : Type} [Field F] {n : ℕ}

theorem cM_eq_zero_of_ne {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n}
    (h : ¬ ((j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1)) : cM n k x i j = 0 := by
  simp only [cM, Matrix.of_apply]
  rw [dite_eq_right h]

theorem cM_eq_of {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n} (hj : (j : ℕ) = k + 1)
    (hi : (i : ℕ) < k + 1) : cM n k x i j = x ⟨i, hi⟩ := by
  simp only [cM, Matrix.of_apply]
  rw [dite_eq_left ⟨hj, hi⟩]

theorem col_val (k : ℕ) (x : Fin (k + 1) → F) :
    ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + cM n k x := rfl

theorem col_inv_val (k : ℕ) (x : Fin (k + 1) → F) :
    (((col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 - cM n k x := rfl

theorem col_mem (k : ℕ) (x : Fin (k + 1) → F) : col n k x ∈ unipotent F n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (j : ℕ) < i := hij
    rw [col_val, Matrix.add_apply, Matrix.one_apply_ne (by intro e; subst e; omega),
      cM_eq_zero_of_ne x (by omega), add_zero]
  · rw [col_val, Matrix.add_apply, Matrix.one_apply_eq, cM_eq_zero_of_ne x (by omega), add_zero]

theorem superdiagSum_cM {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.superdiagSum (cM n k x) = x (Fin.last k) := by
  unfold Whittaker.superdiagSum
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin n), Finset.sum_eq_single (⟨k + 1, hk⟩ : Fin n)]
  · rw [if_pos rfl, cM_eq_of x rfl (by simp)]
    rfl
  · intro j _ hj
    rw [if_neg]
    intro e
    exact hj (Fin.ext (by simpa using e))
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · refine cM_eq_zero_of_ne x fun h' => hi (Fin.ext ?_)
      simp only
      omega
    · rfl
  · simp

theorem psiN_col (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.psiN ψ (col n k x) = ψ (x (Fin.last k)) := by
  rw [Whittaker.psiN, col_val, Whittaker.superdiagSum_add, Whittaker.superdiagSum_one, zero_add,
    superdiagSum_cM hk]

theorem mul_cM {k : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j : Fin n, (j : ℕ) ≤ k → M i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (x : Fin (k + 1) → F) : M * cM n k x = cM n k x := by
  have h : M * cM n k x = 1 * cM n k x := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ k
    · rw [hM i l hl]
    · rw [cM_eq_zero_of_ne x (i := l) (j := j) (by omega), mul_zero, mul_zero]
  rw [h, one_mul]

theorem conj_expand {M C : Matrix (Fin n) (Fin n) F} (hMC : M * C = C) (hCC : C * C = 0) :
    (1 + C) * M * (1 - C) = M + C * M - C := by
  calc (1 + C) * M * (1 - C) = M + C * M - M * C - C * (M * C) := by noncomm_ring
    _ = M + C * M - C := by rw [hMC, hCC, sub_zero]

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem inU_split (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (g : GL (Fin n) F) (hg : inU k g) :
    ∃ (g' : GL (Fin n) F) (x : Fin (k + 1) → F), inU (k + 1) g' ∧ g = g' * col n k x ∧
      Whittaker.psiN ψ g = Whittaker.psiN ψ g' * ψ (x (Fin.last k)) := by
  obtain ⟨hu, hc⟩ := hg
  let x : Fin (k + 1) → F := fun i => (g : Matrix (Fin n) (Fin n) F) ⟨i, by omega⟩ ⟨k + 1, hk⟩
  have hv : ((g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, col_inv_val, mul_sub, mul_one, mul_cM hc]
  have hm : g * (col n k x)⁻¹ ∈ unipotent F n :=
    (unipotent F n).mul_mem hu ((unipotent F n).inv_mem (col_mem k x))
  refine ⟨g * (col n k x)⁻¹, x, ⟨hm, fun i j hj => ?_⟩, (inv_mul_cancel_right _ _).symm, ?_⟩
  · rw [hv, Matrix.sub_apply]
    by_cases hjk : (j : ℕ) ≤ k
    · rw [cM_eq_zero_of_ne x (by omega), sub_zero, hc i j hjk]
    · have hj' : (j : ℕ) = k + 1 := by omega
      by_cases hi : (i : ℕ) < k + 1
      · have hx : x ⟨i, hi⟩ = (g : Matrix (Fin n) (Fin n) F) i j := by
          have e : j = ⟨k + 1, hk⟩ := Fin.ext hj'
          subst e
          rfl
        rw [cM_eq_of x hj' hi, hx, sub_self, Matrix.one_apply_ne (by intro e; subst e; omega)]
      · rw [cM_eq_zero_of_ne x (by omega), sub_zero]
        by_cases e : i = j
        · subst e
          rw [hu.2, Matrix.one_apply_eq]
        · have hlt : id j < id i := by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
              omega
            exact this
          rw [hu.1 hlt, Matrix.one_apply_ne e]
  · have h : Whittaker.psiN ψ g = Whittaker.psiN ψ (g * (col n k x)⁻¹ * col n k x) := by
      rw [inv_mul_cancel_right]
    rw [h, Whittaker.psiN_mul ψ hm (col_mem k x), psiN_col ψ hk]

theorem inU_conj (ψ : AddChar F ℂ) {k : ℕ} (g : GL (Fin n) F) (hg : inU (k + 1) g)
    (x : Fin (k + 1) → F) :
    ∃ g' : GL (Fin n) F, inU (k + 1) g' ∧ col n k x * g = g' * col n k x ∧
      Whittaker.psiN ψ g' = Whittaker.psiN ψ g := by
  obtain ⟨hu, hc⟩ := hg
  have hcol : col n k x ∈ unipotent F n := col_mem k x
  have hcg := (unipotent F n).mul_mem hcol hu
  have hinv := (unipotent F n).inv_mem hcol
  have hv : ((col n k x * g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) + cM n k x * (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, Units.val_mul, col_val, col_inv_val]
    exact conj_expand (mul_cM (fun i j hj => hc i j (by omega)) x) (cM_mul k x x)
  refine ⟨col n k x * g * (col n k x)⁻¹, ⟨(unipotent F n).mul_mem hcg hinv, fun i j hj => ?_⟩,
    (inv_mul_cancel_right _ _).symm, ?_⟩
  · have hC : (cM n k x * (g : Matrix (Fin n) (Fin n) F)) i j = cM n k x i j := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => by rw [hc l j hj], ← Matrix.mul_apply,
        mul_one]
    rw [hv, Matrix.sub_apply, Matrix.add_apply, hC, hc i j hj, add_sub_cancel_right]
  · have h0 := Whittaker.psiN_ne_zero ψ (col n k x)
    rw [Whittaker.psiN_mul ψ hcg hinv, Whittaker.psiN_mul ψ hcol hu, Whittaker.psiN_inv ψ hcol]
    field_simp

end Local

theorem main : ColumnsUnipotent := by
  intro F _ _ _ _ _ _ μ _ ψ _ n k hk
  exact ⟨fun g hg => inU_split ψ hk g hg, fun g hg x => inU_conj ψ g hg x⟩

end GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent
end

section

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound
open PositivityTheory.JacquetShalikaLocal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem div_mono {ι : Type} {c c' : ℕ} (h : c ≤ c') {A : Matrix ι ι F} (hA : Div c' A) : Div c A := by
  intro i j
  obtain ⟨y, hy, e⟩ := hA i j
  refine ⟨(uniformizer F : F) ^ (c' - c) * y,
    Subring.mul_mem _ (Subring.pow_mem _ (uniformizer F).2 _) hy, ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem modulus_eq_one_of_integral {a : F} (ha : a ≠ 0) (h₁ : a ∈ 𝒪[F]) (h₂ : a⁻¹ ∈ 𝒪[F]) :
    Measures.modulus a = 1 := by
  let u : Fˣ := Units.mk0 a ha
  let g : GL (Fin 1) F := Units.map (Matrix.scalar (Fin 1) : F →+* Matrix (Fin 1) (Fin 1) F).toMonoidHom u
  have hg : ∀ i j, (g : Matrix (Fin 1) (Fin 1) F) i j = a := by
    intro i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    simp [g, u]
  have hgi : ∀ i j, ((g⁻¹ : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) i j = a⁻¹ := by
    intro i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    simp [g, u]
  have key := Measures.distribHaarChar_glEquiv g
  rw [Measures.distribHaarChar_glEquiv_eq_one (fun i j => by rw [hg]; exact h₁)
    (fun i j => by rw [hgi]; exact h₂)] at key
  have hdet : Matrix.GeneralLinearGroup.det g = u := by
    ext
    simp [g, u]
  rw [hdet] at key
  rw [show a = (u : F) from rfl, Measures.modulus_units, ← key]

theorem modulus_det_eq_one {m c : ℕ} (h : GL (Fin m) F)
    (hD : Div (c + 1) ((h : Matrix (Fin m) (Fin m) F) - 1)) :
    Measures.modulus (h : Matrix (Fin m) (Fin m) F).det = 1 := by
  classical
  choose y hy hA using hD
  let A : Matrix (Fin m) (Fin m) 𝒪[F] := Matrix.of fun i j => ⟨y i j, hy i j⟩
  let M : Matrix (Fin m) (Fin m) 𝒪[F] := 1 + (uniformizer F ^ (c + 1)) • A
  have hM : (𝒪[F]).subtype.mapMatrix M = (h : Matrix (Fin m) (Fin m) F) := by
    ext i j
    have := hA i j
    rw [Matrix.sub_apply, sub_eq_iff_eq_add] at this
    rw [this]
    simp [M, A, Matrix.one_apply, add_comm]
    split_ifs <;> simp
  have hdet : ((M.det : 𝒪[F]) : F) = (h : Matrix (Fin m) (Fin m) F).det := by
    rw [← hM]
    exact RingHom.map_det (𝒪[F]).subtype M
  let I : Ideal 𝒪[F] := Ideal.span {uniformizer F}
  have hq : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    have h0 : Ideal.Quotient.mk I (uniformizer F) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    ext i j
    simp [M, h0, Matrix.one_apply]
  have hone : Ideal.Quotient.mk I M.det = 1 := by
    rw [RingHom.map_det, hq, Matrix.det_one]
  have hmem : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hone, map_one, sub_self]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  have hv : ValuativeRel.valuation F ((M.det : 𝒪[F]) : F) = 1 := by
    have e : ((M.det : 𝒪[F]) : F) = 1 + (z : F) * (uniformizer F : F) := by
      have := congrArg (fun w : 𝒪[F] => (w : F)) hz
      simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one] at this
      rw [this]; ring
    rw [e]
    refine Valuation.map_one_add_of_lt _ ?_
    rw [map_mul]
    have hz1 : ValuativeRel.valuation F (z : F) ≤ 1 := z.2
    calc ValuativeRel.valuation F (z : F) * ValuativeRel.valuation F (uniformizer F : F)
        ≤ 1 * ValuativeRel.valuation F (uniformizer F : F) := mul_le_mul_left hz1 _
      _ < 1 := by rw [one_mul]; exact valuation_uniformizer_lt_one F
  rw [← hdet]
  have hne : ((M.det : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  refine modulus_eq_one_of_integral hne ?_ ?_
  · exact (Valuation.mem_integer_iff _ _).2 hv.le
  · refine (Valuation.mem_integer_iff _ _).2 ?_
    rw [map_inv₀, hv, inv_one]

theorem div_col {n k c : ℕ} {y : Fin (k + 1) → F}
    (hy : ∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c * t) :
    Div c ((col n k y : Matrix (Fin n) (Fin n) F) - 1) := by
  intro i j
  have e : ((col n k y : Matrix (Fin n) (Fin n) F) - 1) i j = cM n k y i j := by
    show ((1 + cM n k y) - 1) i j = _
    rw [add_sub_cancel_left]
  rw [e]
  by_cases h : (j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1
  · obtain ⟨t, ht, e'⟩ := hy ⟨i, h.2⟩
    refine ⟨t, ht, ?_⟩
    simp only [cM, Matrix.of_apply, dif_pos h]
    exact e'
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    simp only [cM, Matrix.of_apply, dif_neg h, mul_zero]

theorem stability_coefficients : L0 → L2 → ColumnsMirabolic → FormCoefficientStability := by
  intro h0 h2 h3 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hI u u'
  obtain ⟨cu, hcu⟩ := hρ u
  obtain ⟨cv, hcv⟩ := hρ u'
  obtain ⟨hadd, -, -, -, -, hext⟩ := h3 F μ ψ hψ n k hk
  have hfix : ∀ g : GL (Fin n) F, Div (max cu cv + 1) ((g : Matrix (Fin n) (Fin n) F) - 1) →
      ρ g u = u ∧ ρ g u' = u' := fun g hg =>
    ⟨hcu g (div_mono (by omega) hg), hcv g (div_mono (by omega) hg)⟩
  have hf1 : ∀ x y : Fin (k + 1) → F,
      (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (max cu cv + 1) * t) →
      B u' (ρ (col n k (x + y)) u) = B u' (ρ (col n k x) u) := by
    intro x y hy
    rw [hadd, map_mul, Module.End.mul_apply, (hfix _ (div_col hy)).1]
  have hf2 : ∀ h : GL (Fin (k + 1)) F,
      Div (max cu cv + 1) ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) →
      ∀ x, B u' (ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u) =
        B u' (ρ (col n k x) u) := by
    intro h hh x
    obtain ⟨g, hgP, hdet, hcomm, hdiv⟩ := hext h
    obtain ⟨gu, gu'⟩ := hfix g (hdiv _ hh)
    have hmod : Measures.modulus (g : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← hdet]
      exact modulus_det_eq_one h hh
    have e : ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u =
        ρ g (ρ (col n k x) u) := by
      have := congrArg (fun a => ρ a u) (hcomm x)
      simp only [map_mul, Module.End.mul_apply, gu] at this
      exact this.symm
    have q := hI.quasi g hgP u' (ρ (col n k x) u)
    rw [gu', hmod] at q
    rw [e, q]
    simp
  have hcont : Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u)) := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
    have hϖ : ((uniformizer F : F) ^ (max cu cv + 1)) ≠ 0 := by
      refine pow_ne_zero _ fun h => ?_
      exact valuation_uniformizer_ne_zero F (by rw [h, map_zero])
    refine ⟨(fun z : Fin (k + 1) → F => ((uniformizer F : F) ^ (max cu cv + 1))⁻¹ • (z - x)) ⁻¹'
      (Measures.box F (Fin (k + 1))), Measures.isOpen_box.preimage (by fun_prop), ?_, ?_⟩
    · simpa using Measures.zero_mem_box
    · intro x' hx'
      have := hf1 x (x' - x) fun i => ⟨_, Measures.mem_box.1 hx' i, by
        simp [hϖ]⟩
      simpa using this
  exact ⟨hcont, max cu cv, fun g hg => h2 F μ ψ hψ k (max cu cv) (max cu cv + 1) _ hf1 hf2 g hg⟩

end GlobalTheory.CompanionTheory.JSBound
end
end

section

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inv_top {n : ℕ} (hn : 1 < n) {ρ : Representation ℂ (GL (Fin n) F) V} {ψ : AddChar F ℂ}
    {l : V →ₗ[ℂ] ℂ} {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) : Inv ρ ψ l (n - 1) B := by
  obtain ⟨hh, hp, hi⟩ := hU
  refine ⟨hh, fun u => ?_, fun u hu => ?_, fun g _ u u' => ?_, fun g hg u u' => ?_⟩
  · by_cases h : u = 0
    · simp [h]
    · exact (hp u h).le
  · by_cases h : u = 0
    · simp [h]
    · have := hp u h
      rw [hu] at this
      simp at this
  · rw [hi, Nat.sub_self, pow_zero, one_mul]
  · have h1 : g = 1 := by
      apply Units.ext
      ext i j
      exact hg.2 i j (by omega)
    subst h1
    rw [Whittaker.psiN_one]
    simp

theorem inv_step [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ}
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {k : ℕ} (hk : k + 1 < n) {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : Inv ρ ψ l (k + 1) B) :
    ∃ B', Char μ ρ ψ k B B' ∧ Inv ρ ψ l k B' := by
  obtain ⟨B', hC⟩ := h4a F μ ψ hψ n V ρ hρ l k B hk hB
  obtain ⟨hh, hp, hz⟩ := h4b F μ ψ hψ n V ρ hρ l k B B' hk hW hB hC
  exact ⟨B', hC, hh, hp, hz, h4c F μ ψ hψ n V ρ hρ l k B B' hk hB hC,
    h4d F μ ψ hψ n V ρ hρ l k B B' hk hB hC⟩

theorem inv_down [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ} (hn : 1 < n)
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) (d : ℕ) (hd : d ≤ n - 2) :
    ∃ B₁, Inv ρ ψ l (n - 1 - d) B₁ := by
  induction d with
  | zero => exact ⟨B, inv_top hn hU⟩
  | succ d ih =>
    obtain ⟨B₁, h₁⟩ := ih (by omega)
    have e : n - 1 - d = n - 1 - (d + 1) + 1 := by omega
    rw [e] at h₁
    obtain ⟨B₂, -, h₂⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (by omega) h₁
    exact ⟨B₂, h₂⟩

theorem final_form_bessel_bound : StableAverageExists → FormHermitianPositive → FormQuasiInvariantMirabolic → FormEquivariantColumn → L5 → L6 := by
  intro h4a h4b h4c h4d h5 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l B hn hW hU
  obtain ⟨B₁, h₁⟩ := inv_down h4a h4b h4c h4d μ hψ hn hρ hW hU (n - 2) le_rfl
  have e : n - 1 - (n - 2) = 0 + 1 := by omega
  rw [e] at h₁
  obtain ⟨B', hC, h'⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (k := 0) (by omega) h₁
  exact ⟨B', h', h5 F μ ψ hψ n V ρ hρ l B₁ B' hn h₁ hC⟩

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

def stabSub {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ M W) (w : W) :
    Subgroup M where
  carrier := {m | σ m w = w}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem twAct_isSmooth {G M V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hsc : Continuous s)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    IsSmooth (twAct ρ N θ s hs) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hle : ((stabSub ρ v).comap s) ≤ stabSub (twAct ρ N θ s hs) (Submodule.Quotient.mk v) := by
    intro m hm
    change ρ (s m) v = v at hm
    change (twAct ρ N θ s hs) m (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    exact congrArg (Submodule.Quotient.mk (p := twKer ρ N θ)) hm
  have hop : IsOpen (((stabSub ρ v).comap s : Subgroup M) : Set M) :=
    (hρ v).preimage hsc
  exact Subgroup.isOpen_mono hle hop

end GlobalTheory.CompanionTheory.BZMir
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.sobolev_sequence_uniform_cauchy : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ) → (∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) → ∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.RwCauchy.uniformCauchy | exact GlobalTheory.CompanionTheory.PresSobA.RwCauchy.uniformCauchy | (intros; apply GlobalTheory.CompanionTheory.PresSobA.RwCauchy.uniformCauchy <;> assumption)
end
end
