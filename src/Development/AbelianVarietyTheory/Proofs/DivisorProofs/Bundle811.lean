module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle753
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle008
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalRingCardinality.Params

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.fibre_pullback_affineFunction_eq_quotientConst : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  first | exact @GlobalTheory.fibre_restrict_scalar_compat | exact GlobalTheory.fibre_restrict_scalar_compat | (intros; apply GlobalTheory.fibre_restrict_scalar_compat <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.riemannian_lie_volume_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → (∀ i, e i ∈ lieLat X.Gm Λ) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt r ^ fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ)) • formLie X.Ψ e := by
  first | exact @GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie | exact GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie | (intros; apply GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie <;> assumption)
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.metaplectic_euclidean_gaussian : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (Continuous fun x : G × Sch l => omS x.1 x.2) ∧ ∀ (g : G) (P Q : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) → ∃ c : ℂ, c ^ 2 * P.det = 1 ∧ ∀ x : EuclideanSpace ℝ l, omS g φ x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _
  obtain ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.T.metaplecticGaussianNormalisedAlt l
  refine ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7,
    GlobalTheory.T.continuous_metaplectic_schwartz_action_prod l G pr om omS h1.continuous h4 h5 h6, ?_⟩
  intro g P Q hP hQ
  refine ⟨omS g φ 0, h9 g P hP, ?_⟩
  obtain ⟨hdet, hS⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm l (pr g).1 P Q hP hQ (pr g).2
  have hann : ∀ j : l, dRho ((pr g).1 *ᵥ Pi.single (.inl j) 1) (omS g φ) =
      I • dRho ((pr g).1 *ᵥ Pi.single (.inr j) 1) (omS g φ) := fun j => by
    rw [← omS_dRho h5 h6, ← omS_dRho h5 h6, h8 j, map_smul]
  have hd := GlobalTheory.T.fderiv_eq_mulVec_of_schrodinger_annihilated l (pr g).1 P Q hP hQ hdet (omS g φ) hann
  rw [hS.eq] at hd
  exact GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm l (-(Q * P⁻¹)) (omS g φ) hS hd
end

section

open Formalism.BasicNotions.TH

namespace GlobalTheory.FockLie

theorem weyl_comm {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [DecidableEq ι] (a b : ι → A)
    (h : ∀ l m, (b l * a m - a m * b l = if l = m then (1 : A) else 0) ∧
      b l * b m = b m * b l ∧ a l * a m = a m * a l) (i j k l : ι) :
    (a i * b j) * (a k * b l) - (a k * b l) * (a i * b j) =
      (if j = k then a i * b l else 0) - (if l = i then a k * b j else 0) := by
  have h1 : b j * a k = a k * b j + if j = k then (1 : A) else 0 := by
    rw [← (h j k).1]; abel
  have h2 : b l * a i = a i * b l + if l = i then (1 : A) else 0 := by
    rw [← (h l i).1]; abel
  have e1 : (a i * b j) * (a k * b l) = a i * (b j * a k) * b l := by simp only [mul_assoc]
  have e2 : (a k * b l) * (a i * b j) = a k * (b l * a i) * b j := by simp only [mul_assoc]
  have e3 : a i * (a k * b j) * b l = a k * (a i * b l) * b j := by
    calc a i * (a k * b j) * b l = (a i * a k) * (b j * b l) := by simp only [mul_assoc]
      _ = (a k * a i) * (b l * b j) := by rw [(h i k).2.2, (h j l).2.1]
      _ = _ := by simp only [mul_assoc]
  rw [e1, e2, h1, h2, mul_add, mul_add, add_mul, add_mul, e3]
  split_ifs <;> simp

theorem omE_comm {p q r s : ℕ} (i j k l : Ln p q r s) :
    omE i j * omE k l - omE k l * omE i j =
      (if j = k then omE i l else 0) - (if l = i then omE k j else 0) := by
  have h := weyl_comm (raiB : Ln p q r s → _) lowB (GlobalTheory.fock_letters_ccr p q r s) i j k l
  have e : omE i j * omE k l - omE k l * omE i j =
      (raiB i * lowB j) * (raiB k * lowB l) - (raiB k * lowB l) * (raiB i * lowB j) := by
    simp only [omE]
    split_ifs <;>
      simp only [add_zero, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] <;>
      module
  rw [e, h]
  simp only [omE]
  by_cases h1 : j = k <;> by_cases h2 : l = i
  · subst h1; subst h2; simp
  · have h3 : ¬ i = l := fun h => h2 h.symm
    simp [h1, h2, h3]
  · have h3 : ¬ k = j := fun h => h1 h.symm
    simp [h1, h2, h3]
  · simp [h1, h2]

theorem omAct_single {p q r s : ℕ} (i j : Ln p q r s) (x : ℂ) :
    omAct p q r s (Matrix.single i j x) = x • omE i j := by
  rw [omAct_apply]
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_smul]

theorem omAct_single_mul {p q r s : ℕ} (i j k l : Ln p q r s) (x y : ℂ) :
    omAct p q r s (Matrix.single i j x * Matrix.single k l y) =
      (x * y) • (if j = k then omE i l else 0) := by
  by_cases h : j = k
  · subst h
    rw [Matrix.single_mul_single_same, omAct_single, if_pos rfl]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, if_neg h, map_zero, smul_zero]

theorem omAct_lie (p q r s : ℕ) (Y Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s (Y * Z - Z * Y) =
      omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y := by
  induction Y using Matrix.induction_on' with
  | h_zero => simp
  | h_add Y Y' hY hY' =>
    have : (Y + Y') * Z - Z * (Y + Y') = (Y * Z - Z * Y) + (Y' * Z - Z * Y') := by
      rw [add_mul, mul_add]; abel
    rw [this, map_add (f := _), hY, hY', map_add (f := _), add_mul, mul_add]; abel
  | h_std_basis i j x =>
    induction Z using Matrix.induction_on' with
    | h_zero => simp
    | h_add Z Z' hZ hZ' =>
      have : Matrix.single i j x * (Z + Z') - (Z + Z') * Matrix.single i j x =
          (Matrix.single i j x * Z - Z * Matrix.single i j x) +
            (Matrix.single i j x * Z' - Z' * Matrix.single i j x) := by
        rw [add_mul, mul_add]; abel
      rw [this, map_add (f := _), hZ, hZ', map_add (f := _), add_mul, mul_add]; abel
    | h_std_basis k l y =>
      rw [map_sub, omAct_single_mul, omAct_single_mul, omAct_single, omAct_single,
        smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub, ← smul_sub, omE_comm]

end GlobalTheory.FockLie
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.TypesMirror

theorem sameBlock_swap {p q : ℕ} (a b : Ix p q) :
    sameBlock (p := q) (q := p) a.swap b.swap ↔ sameBlock a b := by
  cases a <;> cases b <;> simp [sameBlock]

theorem card_filter_swap {p q : ℕ} (P : Ix p q → Prop) (Q : Ix q p → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P b ↔ Q b.swap) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_equiv (Equiv.sumComm (Fin p) (Fin q)) ?_
  intro b
  simpa using h b

theorem blattner_swap {p q : ℕ} (lam : Ix q p → ℚ) (a : Ix p q) :
    blattner (fun b : Ix p q => lam b.swap) a = blattner lam a.swap := by
  unfold blattner rhoNC
  rw [card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap])]

theorem shiftNu_swap {p q : ℕ} (r s : ℕ) (lam : Ix q p → ℚ) (a : Ix p q) :
    shiftNu (cPair r s) (blattner (fun b : Ix p q => lam b.swap)) a =
      shiftNu (cPair s r) (blattner lam) a.swap := by
  cases a <;> simp only [shiftNu, blattner_swap, Sum.swap_inl, Sum.swap_inr, cPair] <;> ring

theorem ofBlocks_swap {p q : ℕ} (l₁ l₂ : List ℚ) :
    (ofBlocks l₁ l₂ : Ix p q → ℚ) = fun b => (ofBlocks l₂ l₁ : Ix q p → ℚ) b.swap := by
  funext b; cases b <;> rfl

theorem isParam_swap {p q : ℕ} (lam : Ix q p → ℚ) (h : IsParam lam) :
    IsParam (fun b : Ix p q => lam b.swap) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.comp (Equiv.sumComm (Fin p) (Fin q)).injective, ?_, fun a => h3 _, fun a b => h4 _ _⟩
  intro a b hab
  apply h2
  cases a <;> cases b <;> simpa [posC] using hab

theorem jointShape_swap {p q r s : ℕ} (lam : Ix q p → ℚ) (lam' : Ix s r → ℚ)
    (h : JointShape q p s r (blattner lam) (blattner lam')) :
    JointShape p q r s (blattner fun b => lam b.swap) (blattner fun b => lam' b.swap) := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, pa, pb, pc, pd, l1, l2, l3, l4, e1, e2⟩ := h
  refine ⟨c, d, a, b, hc, ha, hd, hb, pc, pd, pa, pb, l2, l1, l4, l3, ?_, ?_⟩
  · funext x
    rw [shiftNu_swap, e1, ofBlocks_swap]
    simp
  · funext x
    rw [shiftNu_swap, e2, ofBlocks_swap]
    simp

theorem hypA_swap {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) :
    HypA t ga de al be := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hp : (ga ++ de ++ al ++ be).Perm (al ++ be ++ ga ++ de) := by
    rw [List.append_assoc (ga ++ de), List.append_assoc (al ++ be)]
    exact List.perm_append_comm
  refine ⟨h1, by omega, h5, h6, h3, h4, hp.nodup_iff.mpr h7,
    fun e he => h8 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h9 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h10 e (hp.mem_iff.mp he), fun e he => h11 e (hp.mem_iff.mp he)⟩

theorem types_mirror : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) ∧ IsParam (lamM' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamM' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c) ∧ (lamM' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c ≤ 0)) := by
  intro t al be ga de h
  obtain ⟨k1, -, k3, k4, k5⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t ga de al be (hypA_swap h)
  have e1 : lamA al be ga de = fun b => lamA ga de al be b.swap := ofBlocks_swap _ _
  have e2 : lamM' t al be ga de = fun b => lamA' t ga de al be b.swap := ofBlocks_swap _ _
  rw [e1, e2]
  refine ⟨jointShape_swap _ _ k1, isParam_swap _ k3, fun a => ?_, fun c => ?_⟩
  · rw [shiftNu_swap]; exact k4 a.swap
  · rw [shiftNu_swap]; exact k5 c.swap

end GlobalTheory.TypesMirror
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.exists_unitary_harishChandra_discreteSeries : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T), ∃ M : UGKMod p q, M.M = D.HK := by
  first | exact @GlobalTheory.DiscreteSeriesUnitary.exists_unitary | exact GlobalTheory.DiscreteSeriesUnitary.exists_unitary | (intros; apply GlobalTheory.DiscreteSeriesUnitary.exists_unitary <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.totalDegree_omAct_kron_blockDiagonal_le : ∀ (p q r s : ℕ) (E : Mat p q), IsKC E → ∀ (d : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → (omAct p q r s (Matrix.kroneckerMap (· * ·) E (Jm r s)) P).totalDegree ≤ d := by
  first | exact @GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le | exact GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le | (intros; apply GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le <;> assumption)
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.TensorNormCompare

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke

variable {ι : Type} [Fintype ι] {n n' : ℕ}

theorem fockS_re_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (fockS f f).re := by
  obtain ⟨r, hr, h⟩ := TensorPlaceNorm.fockS_self_nonneg f
  rw [h, Complex.ofReal_re]; exact hr

theorem fockS_re_pos' {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (fockS f f).re := by
  have : (fockS f f).re = ∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) := by
    have e : fockS f f = ((∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) : ℝ) : ℂ) := by
      unfold fockS
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Complex.conj_mul']
      rfl
    rw [e, Complex.ofReal_re]
  rw [this]
  refine Finset.sum_pos (fun m hm => mul_pos (pow_pos (norm_pos_iff.mpr (mem_support_iff.mp hm)) 2) ?_)
    (support_nonempty.mpr hf)
  exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _

theorem fockS_conj_symm {σ : Type} (f g : MvPolynomial σ ℂ) : (starRingEnd ℂ) (fockS g f) = fockS f g := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right,
    fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, Complex.star_def, Complex.conj_conj]
  ring

def fockCore (σ : Type) : InnerProductSpace.Core ℂ (MvPolynomial σ ℂ) where
  inner f g := fockS f g
  conj_inner_symm f g := fockS_conj_symm f g
  re_inner_nonneg f := fockS_re_nonneg f
  add_left f f' g := by
    change fockL (f + f') g = fockL f g + fockL f' g
    rw [map_add (f := _), LinearMap.add_apply]
  smul_left f g r := by
    change fockL (r • f) g = _ * fockL f g
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite f h := by
    by_contra hf
    have h' : fockS f f = 0 := h
    have := fockS_re_pos' hf
    rw [h'] at this
    simp at this

theorem exists_norm_bound {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (S : Submodule ℂ E) [FiniteDimensional ℂ S] (A : S →ₗ[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (inner ℂ (A f) (A f)).re ≤ C * (inner ℂ f.1 f.1).re := by
  let B := LinearMap.toContinuousLinearMap A
  refine ⟨‖B‖ ^ 2, by positivity, fun f => ?_⟩
  have h1 : (inner ℂ (A f) (A f)).re = ‖A f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (A f)
  have h2 : (inner ℂ f.1 f.1).re = ‖f.1‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f.1
  have h3 : ‖A f‖ ≤ ‖B‖ * ‖f.1‖ := B.le_opNorm f
  rw [h1, h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

theorem exists_fock_bound {σ σ' : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ S]
    (A : S →ₗ[ℂ] MvPolynomial σ' ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (fockS (A f) (A f)).re ≤ C * (fockS f.1 f.1).re := by
  exact @exists_norm_bound _ _ (fockCore σ).toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ).toCore)
    (fockCore σ').toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ').toCore) S ‹_› A

theorem finiteDimensional_nablaSq (lam : DomWeight n) : FiniteDimensional ℂ (nablaSq ℂ n lam) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ n n lam.natW
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  unfold nablaSq
  rw [← hb]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range b)

theorem extremal_fock_pos (lam : DomWeight n) : 0 < (fockS (extremal ℂ n lam) (extremal ℂ n lam)).re :=
  fockS_re_pos' (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW)

end GlobalTheory.TensorNormCompare
end
end

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

theorem _root_.GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : Module.End K (VV K lam)), (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∀ v : VV K lam, (∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by
  first | exact @GlobalTheory.CoefTorusWeight.weight_preserved | exact GlobalTheory.CoefTorusWeight.weight_preserved | (intros; apply GlobalTheory.CoefTorusWeight.weight_preserved <;> assumption)
end
end

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

theorem _root_.GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K)), (∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) → VV K lam ≤ Submodule.span K {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  first | exact @GlobalTheory.coefSpace_le_span_pure_tensors | exact GlobalTheory.coefSpace_le_span_pure_tensors | (intros; apply GlobalTheory.coefSpace_le_span_pure_tensors <;> assumption)
end
end

section

open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ → x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) → ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  first | exact @GlobalTheory.FrameCong.redFn_eq_one_of_congr | exact GlobalTheory.FrameCong.redFn_eq_one_of_congr | (intros; apply GlobalTheory.FrameCong.redFn_eq_one_of_congr <;> assumption)
end

section

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem expo_frob_indep : ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool), ({ W with fr := fr, cj := cj } : Wts ι).Ok P ∧
      ∀ l : ℕ, l.Prime → W.WRange P l → ({ W with fr := fr, cj := cj } : Wts ι).coarseWeightBound P l = W.coarseWeightBound P l := by
  intro P hH hL ι _ _ W hW fr cj
  have hW' : ({ W with fr := fr, cj := cj } : Wts ι).Ok P :=
    { anti := hW.anti, what₂ := hW.what₂, block := hW.block, centre := hW.centre, window := hW.window,
      cloud := hW.cloud, low := hW.low, thick := hW.thick, other := hW.other }
  refine ⟨hW', ?_⟩
  intro l hl hR
  have hN := (places_real_holds P hH hL ι W hW (fun _ => 0)).2
  have hN' := (places_real_holds P hH hL ι ({ W with fr := fr, cj := cj } : Wts ι) hW' (fun _ => 0)).2
  have hi : ({ W with fr := fr, cj := cj } : Wts ι).iW P l = W.iW P l := by
    funext τ
    unfold Wts.iW SizeData₂.depth
    obtain ⟨a1, a2⟩ := hN l hl hR.1 hR.2.2.1 τ
    obtain ⟨b1, b2⟩ := hN' l hl hR.1 hR.2.2.1 τ
    rw [a1, a2, b1, b2]
    rfl
  unfold Wts.coarseWeightBound
  rw [hi]
  rfl

end GlobalTheory
end
