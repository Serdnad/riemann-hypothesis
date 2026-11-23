module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Topology

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_intAt (v : HeightOneSpectrum (𝓞 E)) :
    IsOpen (v.adicCompletionIntegers E : Set (v.adicCompletion E)) := by
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem tendsto_af {α : Type} {l : Filter α} (g : α → Af E) (c : Af E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v c ∈ v.adicCompletionIntegers E)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (g a) = pLoc E v c) :
    Tendsto g l (𝓝 c) := by
  let c' : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun v => ⟨pLoc E v c, hc v⟩
  have hcc : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite c' = c := by
    apply RestrictedProduct.ext
    intro v
    rfl
  let g' : α → Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun a =>
    if h : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E then fun v => ⟨pLoc E v (g a), h v⟩
    else c'
  have hg' : Tendsto g' l (𝓝 c') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [h2, h3 v] with a ha hav
    simp only [g', dif_pos ha]
    exact Subtype.ext hav.symm
  have hmap := (tendsto_map (f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite)).comp hg'
  rw [← RestrictedProduct.nhds_eq_map_structureMap (fun v => isOpen_intAt v), hcc] at hmap
  apply hmap.congr'
  filter_upwards [h2] with a ha
  simp only [Function.comp_apply, g', dif_pos ha]
  apply RestrictedProduct.ext
  intro v
  rfl

theorem tendsto_ad {α : Type} {l : Filter α} (g : α → Ad E) (c : Ad E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E c) ∈ v.adicCompletionIntegers E)
    (h1 : ∀ᶠ a in l, (g a).1 = c.1)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E (g a)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (pFin E (g a)) = pLoc E v (pFin E c)) :
    Tendsto g l (𝓝 c) := by
  have hA : Tendsto (fun a => (g a).1) l (𝓝 c.1) := tendsto_const_nhds.congr' (h1.mono fun a ha => ha.symm)
  have hB : Tendsto (fun a => (g a).2) l (𝓝 c.2) := tendsto_af (fun a => (g a).2) c.2 hc h2 h3
  exact hA.prodMk_nhds hB

end GlobalTheory.FixLevOpen

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tendsto_mat {α : Type} {l : Filter α} (f : α → Matrix (Fin n) (Fin n) (Ad E))
    (h1 : ∀ᶠ a in l, ∀ i j, (f a i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1)
    (h2 : ∀ᶠ a in l, ∀ (v : HeightOneSpectrum (𝓞 E)) i j, pLoc E v (pFin E (f a i j)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, ∀ i j,
      pLoc E v (pFin E (f a i j)) = pLoc E v (pFin E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j))) :
    Tendsto f l (𝓝 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  apply tendsto_ad
  · intro v
    rcases eq_or_ne i j with rfl | h
    · rw [Matrix.one_apply_eq, map_one, map_one]
      exact one_mem _
    · rw [Matrix.one_apply_ne h, map_zero, map_zero]
      exact zero_mem _
  · exact h1.mono fun a ha => ha i j
  · exact h2.mono fun a ha v => ha v i j
  · exact fun v => (h3 v).mono fun a ha => ha i j

theorem inf_entry (u : finU (E := E) (n := n)) (i j : Fin n) :
    ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := by
  have hu : cInf (u : UA E n) = 1 := u.2
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) hu
  have h' : pInf E ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
      pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
    refine h.trans ?_
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.one_apply_eq]
    · simp [Matrix.one_apply_ne hij]
  have h'' : (infEq E).symm ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 =
      (infEq E).symm ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := h'
  exact (infEq E).symm.injective h''

theorem mem_of_isOpen_of_eq_one_on_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Set (finU (E := E) (n := n))), IsOpen U →
    (1 : finU (E := E) (n := n)) ∈ U → ∃ T : Finset (Pl E), ∀ u : finU (E := E) (n := n), (∀ v ∈ T, cLoc v (u : UA E n) = 1) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E) → u ∈ U := by
  intro E _ _ _ n U hU h1
  let S : Finset (Pl E) → Set (finU (E := E) (n := n)) := fun T => {u | (∀ v ∈ T, cLoc v (u : UA E n) = 1) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E)}
  have hanti : ∀ T₁ T₂ : Finset (Pl E), T₁ ⊆ T₂ → S T₂ ⊆ S T₁ := fun T₁ T₂ h u hu =>
    ⟨fun v hv => hu.1 v (h hv), hu.2.1, hu.2.2⟩
  have hdir : Directed (fun x1 x2 => x1 ≥ x2) (fun T => 𝓟 (S T)) := by
    intro T₁ T₂
    refine ⟨T₁ ∪ T₂, ?_, ?_⟩
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_left)
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_right)
  let l : Filter (finU (E := E) (n := n)) := ⨅ T, 𝓟 (S T)
  have hmem : ∀ T, S T ∈ l := fun T => mem_iInf_of_mem T (mem_principal_self _)
  let ι : finU (E := E) (n := n) → GA E n := fun u => ((u : UA E n) : GA E n)
  have hι : Topology.IsInducing ι := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hl : Tendsto id l (𝓝 (1 : finU (E := E) (n := n))) := by
    rw [hι.tendsto_nhds_iff, Units.isEmbedding_embedProduct.isInducing.tendsto_nhds_iff]
    show Tendsto (fun u => (((ι u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)),
      MulOpposite.op (((ι u)⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)))) l
      (𝓝 ((1 : Matrix (Fin n) (Fin n) (Ad E)), MulOpposite.op (1 : Matrix (Fin n) (Fin n) (Ad E))))
    refine Tendsto.prodMk_nhds ?_ (MulOpposite.continuous_op.tendsto _ |>.comp ?_)
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u i j
      · filter_upwards [hmem ∅] with u hu
        exact fun v i j => hu.2.1 v i j
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (hu.1 v (Finset.mem_singleton_self v))
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u⁻¹ i j
      · filter_upwards [hmem ∅] with u hu
        intro v i j
        have := hu.2.2 v i j
        rwa [← map_inv] at this
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have hv : cLoc v ((u : UA E n)⁻¹) = 1 := by
          rw [map_inv, hu.1 v (Finset.mem_singleton_self v), inv_one]
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) hv
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
  have hU' : U ∈ l := hl (hU.mem_nhds h1)
  rw [mem_iInf_of_directed hdir] at hU'
  obtain ⟨T, hT⟩ := hU'
  exact ⟨T, fun u a b c => mem_principal.mp hT ⟨a, b, c⟩⟩

end GlobalTheory.FixLevOpen
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem twTr_conj_equiv : ∀ (G : Type) [Group G] (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (e : ρ.Equiv ρ') (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V), twTr ρ' K K' f (e.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ e.toLinearEquiv.symm.toLinearMap) = twTr ρ K K' f A := by
  intro G _ V V' _ _ _ _ ρ ρ' e K K' f A
  set φ := e.toLinearEquiv with hφ
  have hint : ∀ g v, φ (ρ g v) = ρ' g (φ v) := fun g v => by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    simpa [hφ] using h
  have hint' : ∀ g v', ρ' g v' = φ (ρ g (φ.symm v')) := fun g v' => by
    rw [hint, φ.apply_symm_apply]
  have hmem : ∀ v', v' ∈ fixed ρ' K' ↔ φ.symm v' ∈ fixed ρ K' := by
    intro v'
    show (∀ h : K', ρ' h v' = ((1 : K' →* ℂˣ) h : ℂ) • v') ↔
      (∀ h : K', ρ h (φ.symm v') = ((1 : K' →* ℂˣ) h : ℂ) • φ.symm v')
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    refine forall_congr' fun h => ?_
    rw [hint']
    constructor
    · intro H
      exact (φ.symm_apply_eq.2 H.symm).symm
    · intro H
      rw [H, φ.apply_symm_apply]
  have hlev : levOp ρ' K K' f (φ.conj A) = φ.conj (levOp ρ K K' f A) := by
    have hs := (φ.conj.toAddEquiv).map_finsum (fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A))
    unfold levOp
    rw [map_smul]
    congr 1
    refine Eq.trans ?_ hs.symm
    congr 1
    funext q
    ext v'
    simp [LinearEquiv.conj_apply, hint']
  have hA : φ.toLinearMap ∘ₗ A ∘ₗ φ.symm.toLinearMap = φ.conj A := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]
  rw [hA]
  have hmap : (fixed ρ K').map (φ : V →ₗ[ℂ] V') = fixed ρ' K' := by
    ext v'
    rw [Submodule.mem_map_equiv, hmem]
  set L := levOp ρ K K' f A with hL
  have hc : (∀ v ∈ fixed ρ' K', φ.conj L v ∈ fixed ρ' K') ↔ (∀ v ∈ fixed ρ K', L v ∈ fixed ρ K') := by
    constructor
    · intro H v hv
      have h1 : φ v ∈ fixed ρ' K' := (hmem _).2 (by simpa using hv)
      have h2 := (hmem _).1 (H _ h1)
      simpa [LinearEquiv.conj_apply] using h2
    · intro H v' hv'
      rw [hmem]
      simpa [LinearEquiv.conj_apply] using H _ ((hmem _).1 hv')
  unfold twTr
  simp only [hlev]
  by_cases h : ∀ v ∈ fixed ρ K', L v ∈ fixed ρ K'
  · rw [dite_eq_left (hc.2 h), dite_eq_left h]
    let ψ := φ.ofSubmodules _ _ hmap
    have hr : (φ.conj L).restrict (hc.2 h) = ψ.conj (L.restrict h) := by
      ext ⟨v', hv'⟩
      simp [ψ, LinearEquiv.conj_apply, LinearMap.restrict_apply]
    rw [hr, LinearMap.trace_conj']
  · rw [dite_eq_right (mt hc.1 h), dite_eq_right h]

end GlobalTheory.BCT
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResConj

theorem prod_product_mul (A B : Multiset ℂ) (f g : ℂ → ℂ) :
    ((A ×ˢ B).map fun ij => f ij.1 * g ij.2).prod =
      (A.map f).prod ^ Multiset.card B * (B.map g).prod ^ Multiset.card A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [Multiset.cons_product, Multiset.map_add (f := _), Multiset.prod_add, ih, Multiset.map_map]
    simp only [Function.comp_def, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, mul_pow, pow_succ]
    ring

theorem conj_prod_sub (A B : Multiset ℂ) (hA : ∀ x ∈ A, ‖x‖ = 1) (hB : ∀ y ∈ B, ‖y‖ = 1) :
    (starRingEnd ℂ) (((A ×ˢ B).map fun ij => ij.1 - ij.2).prod) *
        (A.prod ^ Multiset.card B * B.prod ^ Multiset.card A) =
      (-1) ^ (Multiset.card A * Multiset.card B) * ((A ×ˢ B).map fun ij => ij.1 - ij.2).prod := by
  have h := prod_product_mul A B id id
  simp only [Multiset.map_id, id, Multiset.map_id'] at h
  rw [← h, map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  have hc : ∀ ij ∈ A ×ˢ B, ((starRingEnd ℂ) ∘ fun ij : ℂ × ℂ => ij.1 - ij.2) ij * (ij.1 * ij.2) =
      (-1) * (ij.1 - ij.2) := by
    intro ij hij
    rw [Multiset.mem_product] at hij
    have h1 := hA _ hij.1
    have h2 := hB _ hij.2
    have n1 : ij.1 ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    have n2 : ij.2 ≠ 0 := by intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
    have c1 : (starRingEnd ℂ) ij.1 = ij.1⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
    have c2 : (starRingEnd ℂ) ij.2 = ij.2⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h2]; simp
    simp only [Function.comp_apply, map_sub, c1, c2]
    field_simp
    ring
  rw [Multiset.map_congr rfl hc, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    Multiset.card_product]

theorem conj_resultant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (P₁ P₂ : E[X]),
    P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCMField.complexConj E (resultant P₁ P₂) *
      (((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a) = (-1) ^ (a * b) * resultant P₁ P₂ := by
  intro E _ _ _ a b P₁ P₂ h₁ h₂
  obtain ⟨m₁, d₁, -, r₁⟩ := h₁
  obtain ⟨m₂, d₂, -, r₂⟩ := h₂
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  have sA : (P₁.map τ).Splits := IsAlgClosed.splits _
  have sB : (P₂.map τ).Splits := IsAlgClosed.splits _
  have cA : Multiset.card (P₁.map τ).roots = a := by rw [← sA.natDegree_eq_card_roots, natDegree_map, d₁]
  have cB : Multiset.card (P₂.map τ).roots = b := by rw [← sB.natDegree_eq_card_roots, natDegree_map, d₂]
  have hres : τ (resultant P₁ P₂) =
      (((P₁.map τ).roots ×ˢ (P₂.map τ).roots).map fun ij => ij.1 - ij.2).prod := by
    rw [← resultant_eq_prod_roots_sub _ _ (m₁.map τ) (m₂.map τ) sA sB,
      ← resultant_map_map P₁ P₂ P₁.natDegree P₂.natDegree τ, natDegree_map, natDegree_map]
  have e₁ : τ ((-1) ^ a * P₁.coeff 0) = (P₁.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sA.coeff_zero_eq_prod_roots_of_monic (m₁.map τ),
      natDegree_map, d₁, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have e₂ : τ ((-1) ^ b * P₂.coeff 0) = (P₂.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sB.coeff_zero_eq_prod_roots_of_monic (m₂.map τ),
      natDegree_map, d₂, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have key := conj_prod_sub _ _ (r₁ τ) (r₂ τ)
  rw [cA, cB] at key
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, e₁, e₂, IsCMField.complexEmbedding_complexConj, hres, key,
    map_pow, map_neg, map_one]

end GlobalTheory.ResConj
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_X_sub_C' (μ : ℂ) : (X - C μ : ℂ[X]).reverse = 1 - C μ * X := by
  have h1 : (1 : ℂ[X]).reverse = 1 := by simp only [reverse, natDegree_one, reflect_one, pow_zero]
  have hX : (X : ℂ[X]).reverse = 1 := by simpa [h1] using reverse_X_mul (1 : ℂ[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, neg_mul, ← sub_eq_add_neg]

theorem prod_conj_reverse (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    (((s.map fun z => X - C z).prod).map (starRingEnd ℂ)).reverse =
      C (conj (((s.map fun z => X - C z).prod).coeff 0)) * (s.map fun z => X - C z).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    have hs' : ∀ z ∈ s, ‖z‖ = 1 := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have ha : ‖a‖ = 1 := hs a (Multiset.mem_cons_self a s)
    have hca : conj a * a = 1 := by
      rw [Complex.conj_mul', ha]; simp
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, reverse_mul_of_domain, ih hs',
      mul_coeff_zero]
    have hlin : ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse = C (-conj a) * (X - C a) := by
      rw [Polynomial.map_sub, map_X, map_C, reverse_X_sub_C']
      have hw : C (conj a) * C a = (1 : ℂ[X]) := by rw [← C_mul, hca, C_1]
      rw [C_neg]
      linear_combination (-1 : ℂ[X]) * hw
    have hc0 : (X - C a : ℂ[X]).coeff 0 = -a := by simp
    rw [hlin, hc0, map_mul, C_mul]
    simp only [map_neg]
    ring

end GlobalTheory.ConjSelfRecip

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_map_inj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem ell_conj_selfRecip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ C (IsCMField.complexConj E (P.coeff 0)) * P =
      (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  intro E _ _ _ n P hP
  obtain ⟨hm, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := Classical.choice inferInstance
  have hQm : (P.map τ).Monic := hm.map τ
  have hQ : ((P.map τ).roots.map fun z => X - C z).prod = P.map τ :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm IsAlgClosed.card_roots_eq_natDegree
  have hr : ∀ z ∈ (P.map τ).roots, ‖z‖ = 1 := hroots τ
  have key := prod_conj_reverse (P.map τ).roots hr
  rw [hQ] at key
  constructor
  · intro h0
    have h0' : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots hQm.ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hr 0 h0'
    simp at this
  · apply Polynomial.map_injective τ τ.injective
    have hcomp : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ := by
      ext x
      simp [IsCMField.complexEmbedding_complexConj]
    rw [Polynomial.map_mul, map_C, ← reverse_map_inj τ τ.injective, Polynomial.map_map, hcomp,
      ← Polynomial.map_map, key, coeff_map]
    congr 2
    simp [IsCMField.complexEmbedding_complexConj]

end GlobalTheory.ConjSelfRecip
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CongConj

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {m : ℕ}

theorem v_le_one_of_mem_KGL {c : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w (n := m)) (i j : Fin m) :
    Valued.v (c.val i j) ≤ 1 := by
  obtain ⟨a, rfl⟩ := hc
  exact (a.val i j).2

theorem v_mul_left_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) ≤ γ) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hA i l) (hB l j)

theorem v_mul_right_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ γ) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_of_le_one (hA i l) (hB l j)

theorem conj_imp (k : ℕ) {c N : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w (n := m))
    (hN : N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) :
    c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j -
      (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  refine ⟨mul_mem (mul_mem (inv_mem hc) hN.1) hc, fun i j => ?_⟩
  have hid : (c⁻¹ * N * c).val - 1 = (c⁻¹).val * (N.val - 1) * c.val := by
    have h1 : (c⁻¹).val * c.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have := v_mul_right_le (v_mul_left_le (B := N.val - 1) (v_le_one_of_mem_KGL (inv_mem hc)) (fun a b => by
    rw [Matrix.sub_apply]; exact hN.2 a b)) (v_le_one_of_mem_KGL hc) i j
  rw [← hid, Matrix.sub_apply] at this
  exact this

end GlobalTheory.CongConj

theorem GlobalTheory.congConj_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w (n := m) → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  intro E _ _ w m k c N hc
  constructor
  · intro h
    have h2 := GlobalTheory.CongConj.conj_imp k (inv_mem hc) h
    simpa [mul_assoc] using h2
  · exact GlobalTheory.CongConj.conj_imp k hc
end
end
