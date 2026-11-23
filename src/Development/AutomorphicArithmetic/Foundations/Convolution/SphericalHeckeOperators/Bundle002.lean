module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.AutomorphicForms.IwahoriFactorization
import GroundTheory.LocalFields.LocalFourierHaar
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
import Mathlib.RingTheory.Henselian
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

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem mem_supp_monomial {n : ℕ} {a b : Fin n → ℤ}
    (h : a ∈ (monomial b : LaurentRing n).coeff.support) : a = b := by
  rw [AddMonoidAlgebra.coeff_single] at h
  simpa using Finsupp.support_single_subset h

private theorem card_touch_le {n : ℕ} (T : Finset (Fin n × Fin n)) (hT : T ⊆ pairs n) (j : Fin n) :
    (T.filter fun p => p.1 = j ∨ p.2 = j).card ≤ n := by
  have := Finset.card_le_card_of_injOn (s := T.filter fun p => p.1 = j ∨ p.2 = j) (t := Finset.univ)
    (fun p : Fin n × Fin n => if p.1 = j then p.2 else p.1) (fun _ _ => by simp) (by
      rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : a < b := by simpa [pairs] using hT hp.1
      have h2 : c < d := by simpa [pairs] using hT hq.1
      have h3 := hp.2
      have h4 := hq.2
      simp only at h h3 h4
      simp only [Prod.mk.injEq]
      split_ifs at h <;> omega)
  simpa using this

private def Bd {n : ℕ} (T : Finset (Fin n × Fin n)) (e : Fin n → ℤ) : Prop :=
  ∀ j, 0 ≤ e j ∧ e j ≤ ((T.filter fun p => p.1 = j ∨ p.2 = j).card : ℤ)

private theorem bd_insert {n : ℕ} {T : Finset (Fin n × Fin n)} {p : Fin n × Fin n} (hp : p ∉ T)
    {e : Fin n → ℤ} (he : Bd T e) {k : Fin n} (hk : k = p.1 ∨ k = p.2) :
    Bd (insert p T) (Pi.single k 1 + e) := by
  intro j
  obtain ⟨h0, h1⟩ := he j
  rw [Finset.filter_insert]
  by_cases hj : j = k
  · subst hj
    rw [if_pos (by tauto), Finset.card_insert_of_notMem (by simp [hp])]
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hj]
    split_ifs
    · rw [Finset.card_insert_of_notMem (by simp [hp])]
      push_cast
      omega
    · omega

private theorem bd_sum {n : ℕ} (f : Fin n × Fin n → Fin n) (hf : ∀ p, f p = p.1 ∨ f p = p.2)
    (T : Finset (Fin n × Fin n)) : Bd T (∑ p ∈ T, Pi.single (f p) 1) := by
  induction T using Finset.induction_on with
  | empty => intro j; simp
  | insert p T hp ih => rw [Finset.sum_insert hp]; exact bd_insert hp ih (hf p)

private theorem bd_prod {n : ℕ} (t : ℂ) (T : Finset (Fin n × Fin n)) :
    ∀ a ∈ (∏ p ∈ T, (varL p.1 - t • varL p.2) : LaurentRing n).coeff.support, Bd T a := by
  induction T using Finset.induction_on with
  | empty =>
    intro a ha
    rw [Finset.prod_empty] at ha
    have : a = 0 := mem_supp_monomial (b := 0) ha
    subst this
    intro j; simp
  | insert p T hp ih =>
    intro a ha
    rw [Finset.prod_insert hp] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul] at hb
    rcases Finset.mem_union.1 (Finsupp.support_sub hb) with hb | hb
    · rw [mem_supp_monomial hb]; exact bd_insert hp (ih c hc) (Or.inl rfl)
    · rw [mem_supp_monomial (Finsupp.support_smul hb)]; exact bd_insert hp (ih c hc) (Or.inr rfl)

private theorem anti_of_bd {n : ℕ} {ν e : Fin n → ℤ} (hν : Gap n ν) {T : Finset (Fin n × Fin n)}
    (hT : T ⊆ pairs n) (he : Bd T e) : Antitone (ν + e) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · have h1 := hν i j hij
    have h2 := (he i).1
    have h3 := (he j).2
    have h4 := card_touch_le T hT j
    simp only [Pi.add_apply]
    omega

theorem UpperTheory.ConvolutionTheory.H.gapDom :
    ∀ (n : ℕ) (ν : Fin n → ℤ), Gap n ν → (∀ S ∈ (pairs n).powerset, Antitone (ν + eL S) ∧ Antitone (ν + eR S)) ∧
      (∀ t : ℂ, Dom (monomial ν * dPol n t)) ∧ ∀ a, Antitone a → Gap n (a + ν) := by
  intro n ν hν
  refine ⟨fun S hS => ⟨?_, ?_⟩, fun t a ha => ?_, fun a ha i j hij => ?_⟩
  · exact anti_of_bd hν (Finset.mem_powerset.1 hS) (bd_sum Prod.fst (fun _ => Or.inl rfl) S)
  · exact anti_of_bd hν Finset.sdiff_subset (bd_sum Prod.snd (fun _ => Or.inr rfl) _)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [mem_supp_monomial hb]
    exact anti_of_bd hν subset_rfl (bd_prod t _ c hc)
  · have h1 := hν i j hij
    have h2 := ha hij.le
    simp only [Pi.add_apply]
    omega
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] {n : ℕ}

private theorem val_sig (σ : E ≃ₐ[k] E) (x : E) :
    ValuativeRel.valuation E (σ x) = ValuativeRel.valuation E x :=
  GroundTheory.LocalField.valuation_algEquiv_apply k E σ x

private theorem sig_apply (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) (i j : Fin n) :
    ((PositivityTheory.Rg.Tf.Loc.sigmaGL σ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      σ ((g : Matrix (Fin n) (Fin n) E) i j) := rfl

private theorem sig_symm (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ.symm (PositivityTheory.Rg.Tf.Loc.sigmaGL σ g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sig_apply, sig_apply, AlgEquiv.symm_apply_apply]

private theorem sig_mem_K (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ integralGL E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ integralGL E n := by
  rw [mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.1 i j
  · rw [← map_inv, sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.2 i j

private theorem sig_mem_I (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ iwahori E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ iwahori E n := by
  rw [mem_iwahori_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [sig_apply, val_sig]
    exact hg.1 i j
  · rw [sig_apply, val_sig]
    exact hg.2.1 i j h
  · rw [sig_apply, val_sig]
    exact hg.2.2 i

private theorem diag_mem_I {d : Fin n → Eˣ} (hd : ∀ i, ValuativeRel.valuation E (d i : E) = 1) :
    diagGL E n d ∈ iwahori E n := by
  rw [mem_iwahori_iff]
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [coe_diagGL]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, hd]
    · rw [Matrix.diagonal_apply_ne _ e, map_zero]
      exact zero_le'
  · rw [coe_diagGL, Matrix.diagonal_apply_ne _ h.ne', map_zero]
    exact zero_lt_one
  · rw [coe_diagGL, Matrix.diagonal_apply_eq, hd]

private theorem sig_torusPow (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) :
    ∃ u ∈ iwahori E n, PositivityTheory.Rg.Tf.Loc.sigmaGL σ (torusPow E n a) = torusPow E n a * u := by
  have h0 : (GLnLocal.uniformizer E : E) ≠ 0 := (uniformizerUnit E).ne_zero
  have hs : σ (GLnLocal.uniformizer E : E) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff σ σ.injective]
  let v : Eˣ := Units.mk0 (σ (GLnLocal.uniformizer E : E) / (GLnLocal.uniformizer E : E)) (div_ne_zero hs h0)
  have hv : ValuativeRel.valuation E (v : E) = 1 := by
    rw [Units.val_mk0, map_div₀, val_sig, div_self]
    exact (Valuation.ne_zero_iff _).2 h0
  refine ⟨diagGL E n fun i => v ^ a i, diag_mem_I fun i => ?_, ?_⟩
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, one_zpow]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [sig_apply, Units.val_mul, coe_torusPow, coe_diagGL, Matrix.diagonal_mul_diagonal]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, Units.val_zpow_eq_zpow_val,
        Units.val_mk0, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
    · rw [Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ e, map_zero]

private theorem sig_mem_dco (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) {g : GL (Fin n) E} (h : g ∈ dco E a) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ dco E a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨u, hu, e⟩ := sig_torusPow σ a
  refine ⟨PositivityTheory.Rg.Tf.Loc.sigmaGL σ x, sig_mem_I σ hx, u * PositivityTheory.Rg.Tf.Loc.sigmaGL σ y,
    mul_mem hu (sig_mem_I σ hy), ?_⟩
  rw [map_mul, map_mul, e]
  simp only [mul_assoc]

end

theorem UpperTheory.ConvolutionTheory.H.sigInv :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (n : ℕ) (x : GL (Fin n) E),
      oneK E n (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = oneK E n x ∧ ∀ a : Fin n → ℤ, uFn E a (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = uFn E a x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n x
  have hK : PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ integralGL E n ↔ x ∈ integralGL E n :=
    ⟨fun h => by simpa only [sig_symm] using sig_mem_K σ.symm h, sig_mem_K σ⟩
  have hD : ∀ a : Fin n → ℤ, PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ dco E a ↔ x ∈ dco E a := fun a =>
    ⟨fun h => by simpa only [sig_symm] using sig_mem_dco σ.symm a h, sig_mem_dco σ a⟩
  refine ⟨?_, fun a => ?_⟩
  · unfold oneK
    by_cases h : x ∈ integralGL E n
    · rw [Set.indicator_of_mem (SetLike.mem_coe.2 (hK.2 h)), Set.indicator_of_mem (SetLike.mem_coe.2 h)]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hK.1 h')), Set.indicator_of_notMem h]
  · unfold uFn
    by_cases h : x ∈ dco E a
    · rw [Set.indicator_of_mem ((hD a).2 h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h ((hD a).1 h')), Set.indicator_of_notMem h]
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open ValuativeRel in
private theorem iw_eq (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) := by
  ext g
  constructor
  · rintro ⟨⟨u, rfl⟩, hl⟩
    refine ⟨u, ?_, rfl⟩
    change residueReduction F n u ∈ borel n _
    rw [mem_borel_iff]
    intro i j hij
    rw [residueReduction_apply]
    exact (residue_eq_zero_iff_valuation_lt_one F (u i j)).mpr (hl i j hij)
  · intro hg
    exact ⟨iwahori_le_integralGL F n hg, ((mem_iwahori_iff F n).1 hg).2.1⟩

open ValuativeRel in
private theorem unif (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    PositivityTheory.Rg.Tf.Loc.IsUniformiser ((uniformizerUnit F : Fˣ) : F) := by
  refine ⟨valuation_uniformizer_lt_one F, Units.ne_zero _, fun x hx => ?_⟩
  let y : 𝒪[F] := ⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (residue_eq_zero_iff_valuation_lt_one F y).mpr hx
  have h1 := (mem_maximalIdeal_pow_iff F (m := 1) (y := y)).1 (by rwa [pow_one])
  simpa using h1

open ValuativeRel in
private theorem diag_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    (t : Fin n → Fˣ) (ht : ∀ i, valuation F ((t i : Fˣ) : F) = 1) : diagGL F n t ∈ iwahori F n := by
  have he : ∀ i j, ((diagGL F n t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      Matrix.diagonal (fun i => ((t i : Fˣ) : F)) i j := fun i j => rfl
  refine (mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [he]
    by_cases h : i = j
    · subst h
      simp [ht]
    · simp [Matrix.diagonal_apply_ne _ h]
  · rw [he, Matrix.diagonal_apply_ne _ hij.ne']
    simp
  · rw [he]
    simp [ht]

theorem UpperTheory.ConvolutionTheory.H.defBridge :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ),
      PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) F = integralGL F n ∧
      PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) ∧
      (∃ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F)) ∧
      ∀ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F) → ∀ a : Fin n → ℤ,
        PositivityTheory.Rg.Tf.Loc.iwahoriFn F (PositivityTheory.Rg.Tf.Loc.diagPow ϖ a) = uFn F a := by
  intro F _ _ _ _ n
  have hI := iw_eq F n
  refine ⟨rfl, hI, ⟨uniformizerUnit F, unif F⟩, fun ϖ hϖ a => ?_⟩
  have h0 := unif F
  have hv : ValuativeRel.valuation F (ϖ : F) = ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) :=
    le_antisymm (h0.2.2 _ hϖ.1) (hϖ.2.2 _ h0.1)
  set u : Fˣ := ϖ * (uniformizerUnit F)⁻¹ with hu
  have hu1 : ValuativeRel.valuation F (u : F) = 1 := by
    have hne : ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
    rw [hu, Units.val_mul, map_mul, hv, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ hne]
  have hd : diagGL F n (fun i => u ^ a i) ∈ iwahori F n := by
    refine diag_mem F n _ fun i => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu1, one_zpow]
  have hfac : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = torusPow F n a * diagGL F n (fun i => u ^ a i) := by
    have : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = diagGL F n (fun i => ϖ ^ a i) := Units.ext rfl
    rw [this, torusPow, ← map_mul]
    apply congrArg (diagGL F n)
    funext i
    change ϖ ^ a i = uniformizerUnit F ^ a i * u ^ a i
    rw [← mul_zpow, hu, mul_left_comm, mul_inv_cancel, mul_one]
  unfold PositivityTheory.Rg.Tf.Loc.iwahoriFn uFn dco
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, hI, SetLike.mem_coe, hfac]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, _ * y, mul_mem hd hy, by simp only [mul_assoc]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, (diagGL F n (fun i => u ^ a i))⁻¹ * y, mul_mem (inv_mem hd) hy, by simp only [mul_assoc, mul_inv_cancel_left]⟩
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open scoped Pointwise

private theorem conj_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (a : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ iwahori F n)
    (h : ∀ i j, a i < a j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    torusPow F n a * g * (torusPow F n a)⁻¹ ∈ iwahori F n := by
  have he : ∀ i j, ((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) F) i j := by
    intro i j
    rw [← torusPow_neg, Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul, sub_eq_add_neg, zpow_add₀ (GLnLocal.uniformizer_ne_zero F), Pi.neg_apply]
    ring
  have hle : ∀ i j, ValuativeRel.valuation F
      (((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ≤
      ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j) := by
    intro i j
    rw [he]
    rcases lt_or_ge (a i) (a j) with hij | hij
    · rw [h i j hij, mul_zero]
    · obtain ⟨d, hd⟩ : ∃ d : ℕ, a i - a j = d := ⟨(a i - a j).toNat, by omega⟩
      rw [hd, zpow_natCast, map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' (valuation_uniformizer_lt_one F).le d)
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hg
  refine (mem_iwahori_iff F n).2 ⟨fun i j => (hle i j).trans (h1 i j),
    fun i j hij => (hle i j).trans_lt (h2 i j hij), fun i => ?_⟩
  rw [he, sub_self, zpow_zero, one_mul, h3]

private theorem fact {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    {k : GL (Fin n) F} (hk : k ∈ iwahori F n) :
    ∃ u ∈ unipotent F n, u ∈ iwahori F n ∧ ∃ w, k = u * w ∧
      ∀ b : Fin n → ℤ, Antitone b → (torusPow F n b)⁻¹ * w * torusPow F n b ∈ iwahori F n := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id k hk
  have hx' := Parabolic.mem_unipotentRadical.1 hx.2
  refine ⟨x, (mem_unipotent F n).2 ⟨hx'.1, fun i => by simpa using hx'.2 i i rfl⟩, hx.1, y * z, mul_assoc _ _ _,
    fun b hb => ?_⟩
  have h1 := conj_mem (-b) hz.1 fun i j hij =>
    (Parabolic.mem_oppositeUnipotentRadical.1 hz.2).1 i j
      (lt_of_not_ge fun h => (hb h).not_gt (neg_lt_neg_iff.1 hij))
  have h2 := conj_mem (-b) hy.1 fun i j hij =>
    Parabolic.mem_levi.1 hy.2 i j (fun h => by
      have h' : i = j := h
      subst h'; exact lt_irrefl _ hij)
  rw [torusPow_neg, inv_inv] at h1 h2
  have := mul_mem h2 h1
  simpa [mul_assoc] using this

theorem UpperTheory.ConvolutionTheory.H.dcoShape :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (a : Fin n → ℤ), Antitone a →
      (∀ g, g ∈ dco F a ↔ ∃ u ∈ unipotent F n ⊓ integralGL F n, ∃ y ∈ iwahori F n, g = u * torusPow F n a * y) ∧
      (∀ b, Antitone b → ∀ g ∈ dco F a, ∀ g' ∈ dco F b, g * g' ∈ dco F (a + b)) ∧
      uFn F a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ BiI F (uFn F a) := by
  intro F _ _ _ _ n a ha
  have hbi : ∀ g, ∀ y ∈ iwahori F n, (y * g ∈ dco F a ↔ g ∈ dco F a) ∧ (g * y ∈ dco F a ↔ g ∈ dco F a) := by
    have hl : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → y * g ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨y * x, mul_mem hy hx, x', hx', by group⟩
    have hr : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → g * y ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨x, hx, x' * y, mul_mem hx' hy, by group⟩
    intro g y hy
    exact ⟨⟨fun h => by simpa using hl _ _ (inv_mem hy) h, hl g y hy⟩,
      ⟨fun h => by simpa using hr _ _ (inv_mem hy) h, hr g y hy⟩⟩
  refine ⟨fun g => ⟨?_, ?_⟩, ?_, ?_, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk, y, hy, rfl⟩
    obtain ⟨u, hu, huI, w, rfl, hw⟩ := fact hk
    exact ⟨u, ⟨hu, iwahori_le_integralGL F n huI⟩, _, mul_mem (hw a ha) hy, by group⟩
  · rintro ⟨u, ⟨hu, hu'⟩, y, hy, rfl⟩
    refine ⟨u, ?_, y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_unipotent F n).1 hu
    refine (mem_iwahori_iff F n).2 ⟨fun i j => ((mem_integralGL_iff F n).1 hu').1 i j, fun i j hij => ?_, fun i => ?_⟩
    · rw [h1 hij, map_zero]; exact zero_lt_one
    · rw [h2, map_one]
  · rintro b hb g ⟨x, hx, y, hy, rfl⟩ g' ⟨x', hx', y', hy', rfl⟩
    obtain ⟨u, hu, huI, w, e, hw⟩ := fact (mul_mem hy hx')
    have h1 := conj_mem a huI fun i j hij =>
      ((mem_unipotent F n).1 hu).1 (lt_of_not_ge fun h => (ha h).not_gt hij)
    refine ⟨_, mul_mem hx h1, _, mul_mem (hw b hb) hy', ?_⟩
    rw [torusPow_add]
    calc x * torusPow F n a * y * (x' * torusPow F n b * y')
        = x * torusPow F n a * (y * x') * torusPow F n b * y' := by group
      _ = _ := by rw [e]; group
  · have e : dco F a = (iwahori F n : Set (GL (Fin n) F)) * {torusPow F n a} * (iwahori F n : Set (GL (Fin n) F)) := by
      ext g
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact Set.mul_mem_mul (Set.mul_mem_mul hx rfl) hy
      · rintro ⟨_, ⟨x, hx, _, rfl, rfl⟩, y, hy, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    refine indicator_mem_locallyConstantCompactSupport (R := ℂ) (U := dco F a) ?_ ?_ (1 : ℂ)
    · rw [e]; exact ((isCompact_iwahori F n).mul isCompact_singleton).mul (isCompact_iwahori F n)
    · rw [e]; exact (isOpen_iwahori F n).mul_left
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).1]
    · simp [uFn, h, (hbi g y hy).1]
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).2]
    · simp [uFn, h, (hbi g y hy).2]
end
