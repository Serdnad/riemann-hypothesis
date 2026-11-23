module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.RealPlaceAnalysis.Bundle004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellScalarTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Cell

variable {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem cellFunctor_central (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m → ℂˣ) (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v)
    (x : Levi k m') (hx : x ∈ relParab k g) (hcomm : ∀ y, y * x = x * y) (w) :
    cellFunctor f g ρ x w =
      ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w := by
  apply Subtype.ext; apply Subtype.ext; funext y
  show w.1.1 (y * x) = _
  rw [hcomm y]
  have h2 : w.1.1 (x * y) = _ := w.1.2 ⟨x, hx⟩ y
  rw [h2]
  show _ = ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w.1.1 y
  generalize w.1.1 y = u
  induction u using Submodule.Quotient.induction_on with
  | H v =>
  rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, hρ]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, smul_smul, ← Submodule.Quotient.mk_smul]
  rw [mul_assoc]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] in
theorem scalar_comm (s : β → kˣ) (x : Levi k m') (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j))
    (y : Levi k m') : y * x = x * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, hx]
  ext1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in
theorem scalar_mem (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) : x ∈ relParab k g := by
  intro j _
  rw [hx]
  refine mem_parab.2 fun a b hab => ?_
  have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
  simp [Matrix.GeneralLinearGroup.scalar, hne]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in
theorem det_relProj (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) (h : x ∈ relParab k g) (j : β) (i : α) :
    GeneralLinearGroup.det (relProj k g ⟨x, h⟩ j i) = s j ^ Fintype.card (c i j) := by
  have e : relProj k g ⟨x, h⟩ j i = GeneralLinearGroup.scalar _ (s j) := by
    ext a a'
    refine (leviProj_apply k (g j) ⟨x j, h j trivial⟩ i a a').trans ?_
    show ((x j : GL (m' j) k) : Matrix (m' j) (m' j) k) _ _ = _
    rw [hx]
    by_cases h : a = a'
    · subst h; simp [Matrix.GeneralLinearGroup.scalar]
    · have h' : g j ⟨i, a⟩ ≠ g j ⟨i, a'⟩ := by simpa using h
      simp [Matrix.GeneralLinearGroup.scalar, h, h']
  rw [e]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end Cell

theorem modExp_false (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m false = Fintype.card (m true) := by
  simp [modExp, Finset.sum_filter]

theorem modExp_true (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m true = -(Fintype.card (m false) : ℤ) := by
  simp [modExp, Finset.sum_filter]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem extTensor_detRep_apply (χ₁ χ₂ : kˣ →* ℂˣ) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (y : Levi k (Two a b)) (t : TensorProduct ℂ ℂ ℂ) :
    ((extTensor (detRep a χ₁) (detRep b χ₂)).comp (leviTwo k a b).symm.toMonoidHom) y t =
      ((χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)) : ℂˣ) : ℂ) • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => rw [map_add (f := _), hs, ht, smul_add]
  | tmul s t =>
    refine (extTensor_tmul (detRep a χ₁) (detRep b χ₂) (y false, y true) s t).trans ?_
    rw [detRep, detRep, ofChar_apply, ofChar_apply, ← smul_eq_mul, ← smul_eq_mul,
      TensorProduct.smul_tmul_smul]
    rfl

theorem cellFunctor_scalar_action {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ)
    (x : Levi k (Two (Fin (u + v)) (Fin 1)))
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j)) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      x w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hm := scalar_mem (c := fun i j => Fin (b.1 i j)) g _ x hx
  have hd := det_relProj (c := fun i j => Fin (b.1 i j)) g _ x hx hm
  have h11 : b.1 true true = 0 := by
    have := b.2.2 true
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    omega
  have h00 : (b.1 false false : ℂ) = u - 1 := by
    have := b.2.1 false
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    have h3 : b.1 false false + 1 = u := by omega
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h3
  refine (cellFunctor_central (c := fun i j => Fin (b.1 i j)) f g _
    (fun y => χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)))
    (extTensor_detRep_apply χ₁ χ₂ (Fin u) (Fin (v + 1))) x hm (scalar_comm _ x hx) w).trans ?_
  refine congrArg (fun s : ℂˣ => (s : ℂ) • w) ?_
  have hd' : ∀ i j, GeneralLinearGroup.det
      (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨x, hm⟩) i j) = _ := fun i j => hd j i
  simp only [relDeltaHalf_apply, deltaHalf_apply, relEmb_apply, det_leviEmb, Fintype.prod_bool, hd, hd',
    modExp_false, modExp_true, Fintype.card_fin, hb, h11]
  have hz : absPow k (-(b.1 false false : ℂ) / 2) = (absPow k (((u : ℂ) - 1) / 2))⁻¹ := by
    rw [h00, neg_div, absPow_neg]
  simp [hz, mul_comm]

theorem cellFunctor_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      (leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hx : ∀ j, leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) j =
      GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j) := by
    intro j
    cases j
    · exact (map_one (GeneralLinearGroup.scalar (R := k) (Fin (u + v)))).symm
    · rfl
  exact cellFunctor_scalar_action χ₁ χ₂ u v b hb f g ϖ _ hx w

end GlobalTheory.CellScalarTwo
end
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
open scoped nonZeroDivisors

namespace GlobalTheory.LieDisc

theorem isIntegral_of_trace_integral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E,
      (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  intro E _ _ _ hu w hw
  set F := maximalRealSubfield E
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hu
    infer_instance
  have hd : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [hd, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  have hmem : w ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have ht := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (w * algebraMap (𝓞 E) E b)
    have hi : IsIntegral ℤ (Algebra.trace F E (w * algebraMap (𝓞 E) E b)) := by
      rw [← isIntegral_algebraMap_iff (B := E), ht]
      exact hw _ (RingOfIntegers.isIntegral_coe b)
    exact ⟨⟨_, hi⟩, rfl⟩
  rw [hdual] at hmem
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

end GlobalTheory.LieDisc
end

section

noncomputable section

open Polynomial CategoryTheory

namespace GlobalTheory.DualLabel

theorem roots_reverse_prod {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    have ha : a ≠ 0 := fun h => hs.1 h.symm
    have hX : (X : K[X]).reverse = 1 := by simp [reverse]
    have e : (X - C a : K[X]).reverse = C (-a) * (X - C a⁻¹) := by
      rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, hX, mul_sub, ← C_mul, neg_mul,
        mul_inv_cancel₀ ha]
      simp [add_comm]
    have hm : (s.map fun x => X - C x).prod ≠ 0 :=
      (monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x).ne_zero
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, e, roots_mul, roots_C_mul _ (neg_ne_zero.2 ha),
      roots_X_sub_C, ih hs.2, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 ha)) (X_sub_C_ne_zero _))
      (by rwa [Ne, reverse_eq_zero])

theorem monic_normRev {K : Type} [Field K] {f : K[X]} (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
    inv_mul_cancel₀ h0]

theorem rootsBar_normRev {K : Type} [Field K] {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K (C (f.coeff 0)⁻¹ * f.reverse) =
      (Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f).map (·⁻¹) := by
  have hz : (0 : AlgebraicClosure K) ∉ Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f := fun h => by
    rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, mem_roots (hm.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero,
      coeff_map] at h
    exact h0 ((map_eq_zero _).1 h)
  have e : f.reverse.map (algebraMap K (AlgebraicClosure K)) = (f.map (algebraMap K (AlgebraicClosure K))).reverse := by
    rw [reverse, reverse, reflect_map, natDegree_map]
  have hf := (IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hm.map _)
  rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
  exact roots_reverse_prod _ hz

theorem eq_of_rootsBar_eq {K : Type} [Field K] {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f = Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K g) : f = g := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K (AlgebraicClosure K)).injective
  rw [(IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (g.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hg.map _)]
  exact congrArg (fun s => (s.map fun a => X - C a).prod) h

theorem lab_dual : ∀ {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Simple τ' →
    Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ' →
    (∀ γ : GL (Fin d) K, LinearMap.trace ℂ τ'.V (τ'.ρ γ) = LinearMap.trace ℂ τ.V (τ.ρ γ⁻¹)) →
    O.lab d τ' = Polynomial.C ((O.lab d τ).coeff 0)⁻¹ * (O.lab d τ).reverse := by
  intro K _ _ _ C O hO d τ τ' hd hs hc hs' hc' htr
  have h := hO.2 d τ τ' hd hs hc hs' hc' htr
  obtain ⟨hm, hi, hX, -⟩ := O.lab_spec d τ hd hs hc
  have h0 := Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX
  refine eq_of_rootsBar_eq (O.lab_spec d τ' hd hs' hc').1 (monic_normRev h0) ?_
  rw [h, rootsBar_normRev hm h0]

end GlobalTheory.DualLabel
end
end

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagUnitary

def Pm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 1 else 0

def Qm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 0 else 1

lemma Pm_eq {n : ℕ} (ε : Fin n → Bool) : Pm ε = (1/2 : ℂ) • (1 + Jm ε) := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Jm, hε] <;> norm_num
  · simp [Pm, Jm, h, diagonal_apply_ne _ h, one_apply_ne h]

lemma Qm_eq {n : ℕ} (ε : Fin n → Bool) : Qm ε = 1 - Pm ε := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Qm, hε]
  · simp [Pm, Qm, h, diagonal_apply_ne _ h, one_apply_ne h]

lemma comm_Pm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Pm ε = Pm ε * a := by
  rw [Pm_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h,
    Matrix.mul_one, Matrix.one_mul]

lemma comm_Qm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Qm ε = Qm ε * a := by
  rw [Qm_eq, Matrix.mul_sub, Matrix.sub_mul, comm_Pm h, Matrix.mul_one, Matrix.one_mul]

lemma sum_sq_norm_eq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = trace (Mᴴ * M) := by
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma trace_unitary_conj {n : ℕ} (a b h : Matrix (Fin n) (Fin n) ℂ) (ha : aᴴ * a = 1)
    (hb : bᴴ * b = 1) : trace ((a * h * b)ᴴ * (a * h * b)) = trace (hᴴ * h) := by
  have hb' : b * bᴴ = 1 := mul_eq_one_comm.mp hb
  have e : (a * h * b)ᴴ * (a * h * b) = bᴴ * ((hᴴ * h) * b) := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (hᴴ * aᴴ) * (a * h * b) = bᴴ * (hᴴ * (aᴴ * a) * h * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, trace_mul_comm, Matrix.mul_assoc, hb', Matrix.mul_one]

lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2
      = ∑ i, ∑ j, ‖(Pm ε * M * Qm ε) i j‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
      (by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pm, Qm, diagonal_mul, mul_diagonal]
  cases ε i <;> cases ε j <;> simp

end GlobalTheory.OffDiagUnitary

open GlobalTheory.OffDiagUnitary in
theorem GlobalTheory.offDiag_sum_sq_norm_unitary_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (a b g : Matrix (Fin n) (Fin n) ℂ), aᴴ * a = 1 → a * Jm ε = Jm ε * a → bᴴ * b = 1 → b * Jm ε = Jm ε * b → ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(a * g * b) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε a b g ha haJ hb hbJ
  rw [off_sum_eq, off_sum_eq]
  have e : Pm ε * (a * g * b) * Qm ε = a * (Pm ε * g * Qm ε) * b := by
    calc Pm ε * (a * g * b) * Qm ε = (Pm ε * a) * g * (b * Qm ε) := by simp only [Matrix.mul_assoc]
      _ = (a * Pm ε) * g * (Qm ε * b) := by rw [comm_Pm haJ, comm_Qm hbJ]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  apply Complex.ofReal_injective
  rw [sum_sq_norm_eq_trace, sum_sq_norm_eq_trace, trace_unitary_conj _ _ _ ha hb]
end

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem pcLieEntry : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z ↔ ∀ a b, (starRingEnd ℂ) (Z a b) = -((if ε a then (1 : ℂ) else -1) * (if ε b then (1 : ℂ) else -1) * Z b a) := by
  intro n ε Z
  have key : ∀ a b, (Zᴴ * Jm ε + Jm ε * Z) a b = (starRingEnd ℂ) (Z b a) * (if ε b then (1 : ℂ) else -1) + (if ε a then (1 : ℂ) else -1) * Z a b := by
    intro a b
    simp [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  unfold inG
  constructor
  · intro h a b
    have hb := congrFun (congrFun h b) a
    rw [key] at hb
    simp only [Matrix.zero_apply] at hb
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb
  · intro h
    ext a b
    rw [key]
    simp only [Matrix.zero_apply]
    have hb := h b a
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb

end GlobalTheory
end

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem haar_UJ_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro n ε μ _
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by
    rw [Measure.map_smul, hR.map_mul_right_eq_self]
    exact (measurable_mul_const g).aemeasurable⟩

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.symmCocycle_apply_finset_sum : ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] (γ : A → A → B), (∀ x y, γ x y = γ y x) → (∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0) → γ 0 0 = 0 → ∀ (d : ℕ) (x y : Fin d → A), γ (∑ m, x m) (∑ m, y m) = ∑ m, γ (x m) (y m) + ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) - (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) - ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) := by
  first | exact @GlobalTheory.symmCocycle_sum | exact GlobalTheory.symmCocycle_sum | (intros; apply GlobalTheory.symmCocycle_sum <;> assumption)
end

section

open Matrix Topology

theorem _root_.GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ → ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  first | exact @GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | exact GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | (intros; apply GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact <;> assumption)
end
