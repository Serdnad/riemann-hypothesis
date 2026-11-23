module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def deg1 (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) : Submodule ℂ (Polynomial (HA M)) :=
  (W.comap (HA M).val.toLinearMap).map ((Polynomial.monomial 1).restrictScalars ℂ)

theorem mem_homogeneousExponentsOneBlock (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (p : Polynomial (HA M)) :
    p ∈ deg1 M W ↔ ∃ f : HA M, (f : C → M.dom → ℂ) ∈ W ∧ Polynomial.monomial 1 f = p := Iff.rfl

def deg1Equiv (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) :
    W ≃ₗ[ℂ] deg1 M W :=
  LinearEquiv.ofBijective
    ({ toFun := fun f => ⟨Polynomial.monomial 1 ⟨f, hW f f.2⟩, (mem_homogeneousExponentsOneBlock M W _).2 ⟨⟨f, hW f f.2⟩, f.2, rfl⟩⟩
       map_add' := fun f g => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((f + g : W) : C → M.dom → ℂ), hW _ (f + g).2⟩ : HA M) =
           Polynomial.monomial 1 ⟨f, hW _ f.2⟩ + Polynomial.monomial 1 ⟨g, hW _ g.2⟩
         rw [← map_add (f := _)]
         rfl)
       map_smul' := fun z f => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((z • f : W) : C → M.dom → ℂ), hW _ (z • f).2⟩ : HA M) =
           z • Polynomial.monomial 1 ⟨f, hW _ f.2⟩
         rw [Polynomial.smul_monomial]
         rfl) } :
      W →ₗ[ℂ] deg1 M W)
    ⟨fun f g hfg => by
      have := congrArg Subtype.val hfg
      have := Polynomial.monomial_injective 1 this
      exact Subtype.ext (congrArg (fun q : HA M => (q : C → M.dom → ℂ)) this),
     fun p => by
      obtain ⟨f, hf, hp⟩ := (mem_homogeneousExponentsOneBlock M W p.1).1 p.2
      exact ⟨⟨f, hf⟩, Subtype.ext hp⟩⟩

theorem deg1Equiv_coe (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) (f : W) :
    ((deg1Equiv M W hW f : deg1 M W) : Polynomial (HA M)) = Polynomial.monomial 1 ⟨f, hW f f.2⟩ := rfl

theorem mul_pb_mem_cusp (M : TwoLevels E r U C) (ka mu : Wt M.Ψ r) (u0 : C → Frame M.Ψ r → ℂ) (hu0 : u0 ∈ M.SS mu)
    (k h : U) {f : C → M.dom → ℂ} (hf : f ∈ M.cusp ka) :
    f * pb M k (M.res u0) * pb M h (M.res u0) ∈ M.cusp (ka + 2 • mu) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, rfl⟩ := hf
    have e : M.res F * pb M k (M.res u0) * pb M h (M.res u0) = M.res (F * M.pull k u0 * M.pull h u0) := rfl
    rw [e, two_smul, ← add_assoc]
    exact Submodule.subset_span ⟨_, GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ (GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ hF
      (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 k hu0)) (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 h hu0), rfl⟩
  | zero => simp
  | add f g _ _ hf hg => rw [add_mul, add_mul]; exact add_mem hf hg
  | smul z f _ hf => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ z hf

end GlobalTheory.CuspEmb


open GlobalTheory.CuspEmb in
theorem GlobalTheory.CuspEmb.cusp_embReg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) →
    ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ ep c0 hR H hL
  classical
  haveI : Fintype U := Fintype.ofFinite U
  obtain ⟨u0, hu0, hdet⟩ := GlobalTheory.T.exists_cuspForm_independent_translates E r H C (sub M H) hL (sOf M) (even_sOf M) (le_sOf M)
  have hu0' : u0 ∈ M.SS (deMul M.Ψ r M.p0 (sOf M)) := hu0
  have hVHA : ∀ f ∈ M.cusp ka, f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M ka F hF
  have h2HA : ∀ f ∈ M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)), f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ F hF
  obtain ⟨a, hcoc, hform⟩ := GlobalTheory.T.exists_cocycle_pullbackRepresentation E r U C M ka ρ hρ (fun f hf => (hVHA f hf).2)
  obtain ⟨h1, hlaw⟩ := GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle E r U C M a hcoc
  let act : U →* (Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M)) :=
    { toFun := fun k => tw M (fun c => (a k⁻¹ c : ℂ)) k⁻¹
      map_one' := by
        show tw M (fun c => (a 1⁻¹ c : ℂ)) 1⁻¹ = 1
        rw [inv_one]
        exact h1
      map_mul' := fun g h => by
        simp only [mul_inv_rev]
        rw [← hlaw]
        rfl }
  let ut : HA M := ⟨M.res u0, GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ u0 hu0'⟩
  have hact : ∀ k, act k (Polynomial.C ut) = Polynomial.C (pbA M k⁻¹ ut) := fun k => tw_C M _ _ _
  have hactm : ∀ k (f : HA M), act k (Polynomial.monomial 1 f) =
      Polynomial.monomial 1 (cst M (fun c => (a k⁻¹ c : ℂ)) * pbA M k⁻¹ f) := fun k f => tw_monomial_one M _ _ _

  have hnz : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)).det ∈ nonZeroDivisors (Polynomial (HA M)) := by
    have e : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)) =
        (Polynomial.C : HA M →+* Polynomial (HA M)).mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) := by
      refine Matrix.ext fun h g => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hact, mul_inv_rev]
    rw [e, ← RingHom.map_det]
    refine GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors E r U C M _ fun c => ?_
    obtain ⟨x, hx, hne⟩ := hdet c
    refine ⟨⟨x, hx⟩, ?_⟩
    let φ : HA M →+* ℂ := ((Pi.evalRingHom _ (⟨x, hx⟩ : M.dom)).comp (Pi.evalRingHom _ c)).comp (HA M).val.toRingHom
    have e2 : ((Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det : C → M.dom → ℂ) c ⟨x, hx⟩ =
        φ (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det := rfl
    rw [e2, RingHom.map_det]
    have e3 : φ.mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) =
        ((Matrix.of fun h h' : H => M.pull ((h : U) * h') u0 c x).submatrix (Equiv.inv H) (Equiv.inv H)).transpose := by
      ext h g
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
        Equiv.inv_apply, mul_inv_rev]
      rfl
    rw [e3, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hne

  let V := deg1 M (M.cusp ka)
  let V2 := deg1 M (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)))
  let V1 : Submodule ℂ (Polynomial (HA M)) :=
    Submodule.span ℂ {p | ∃ x ∈ V, ∃ h : H, p = x * act h (Polynomial.C ut)}
  let e := deg1Equiv M (M.cusp ka) hVHA
  let e2 := deg1Equiv M _ h2HA
  haveI : Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := hR.2.1
  haveI : FiniteDimensional ℂ V2 := LinearEquiv.finiteDimensional e2
  let ρ' : Representation ℂ U V :=
    { toFun := fun k => e.toLinearMap ∘ₗ ρ k ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }
  have hρ' : ∀ g x, ((ρ' g x : V) : Polynomial (HA M)) = act g x := by
    intro g x
    obtain ⟨f, rfl⟩ := e.surjective x
    have e1 : ρ' g (e f) = e (ρ g f) := by simp [ρ']
    rw [e1, deg1Equiv_coe, deg1Equiv_coe, hactm]
    congr 1
    apply Subtype.ext
    funext c x
    have := hform g⁻¹ f c x
    rw [inv_inv] at this
    exact this
  have hV1 : ∀ h : H, ∀ x ∈ V, x * act h (Polynomial.C ut) ∈ V1 := fun h x hx => Submodule.subset_span ⟨x, hx, h, rfl⟩
  have hactV : ∀ (k : U), ∀ x ∈ V, act k x ∈ V := fun k x hx => by
    have := hρ' k ⟨x, hx⟩
    rw [← this]
    exact (ρ' k ⟨x, hx⟩).2
  have hV1s : ∀ h : H, ∀ x ∈ V1, act h x ∈ V1 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      refine Submodule.subset_span ⟨act h y, hactV h y hy, h * k, ?_⟩
      rw [map_mul, Subgroup.coe_mul, map_mul act]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul z x _ hx => rw [map_smul]; exact Submodule.smul_mem _ z hx
  have hV2 : ∀ h : H, ∀ x ∈ V1, x * act h (Polynomial.C ut) ∈ V2 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      obtain ⟨f, hf, rfl⟩ := (mem_homogeneousExponentsOneBlock M _ y).1 hy
      rw [hact, hact, Polynomial.monomial_mul_C, Polynomial.monomial_mul_C]
      refine (mem_homogeneousExponentsOneBlock M _ _).2 ⟨_, ?_, rfl⟩
      exact mul_pb_mem_cusp M ka _ u0 hu0' _ _ hf
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul z x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ z hx
  obtain ⟨n, ⟨j, hj, hjeq⟩, hn⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant ℂ U (Polynomial (HA M)) act H (Polynomial.C ut) hnz V V1 V2 ρ' hρ' hV1
    hV1s hV2
  refine ⟨n, ⟨j ∘ₗ e.toLinearMap, hj.comp e.injective, fun h v i => ?_⟩, ?_⟩
  · have := hjeq h (e v) i
    have e1 : ρ' h (e v) = e (ρ h v) := by simp [ρ']
    rw [e1] at this
    exact this
  · rw [← e2.finrank_eq] at hn
    exact hn

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OscSplit

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumBig sumSmallSpread not_isBig_iff)

theorem ereal_coe_sum {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
theorem card_filter_inPsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← GlobalTheory.LamF.card_psiSet H, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
    rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)


open Classical in
theorem sumBig_le {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {F k : ℕ} {Mb : ℝ} {cx : Lt1 Dw → ℕ}
    (hF : Module.finrank ℚ E = 2 * F)
    (h : ∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) :
    (sumBig k cx : ℝ) ≤ F * Mb := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi, hF]; omega
  have e : sumBig k cx = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ),
      ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ), cx f := by
    unfold sumBig
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.filter_filter]
  rw [e, Nat.cast_sum]
  refine (Finset.sum_le_sum fun τ _ => h τ).trans ?_
  rw [Finset.sum_const, hc, nsmul_eq_mul]

theorem oscLe_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp h2 hd hs la
  classical
  obtain ⟨-, hqm, -, -, -, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hB
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  let B : Lt1 Dw → ℝ := fun f =>
    if _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f then (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) else boundAll p (rk f) (cx f)
  have hsum : ∑ f, B f ≤ (F * m * Mb + Sm) / ((p : ℝ) - 1) := by
    have e1 : ∑ f ∈ Finset.univ.filter (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) =
        (sumBig k cx : ℝ) * Dw.q / ((p : ℝ) - 1) := by
      rw [← Finset.sum_mul, mul_div_assoc, sumBig, Nat.cast_sum]
    have e2 : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), boundAll p (rk f) (cx f) =
        (sumSmallSpread k cx : ℝ) / ((p : ℝ) - 1) := by
      rw [sumSmallSpread, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr (Finset.filter_congr fun f _ => not_isBig_iff k f) fun f _ => ?_
      rw [boundAll, Nat.cast_mul]
    have h1 := sumBig_le (k := k) (cx := cx) hF hbig
    have h3 : (Dw.q : ℝ) ≤ m := by exact_mod_cast hqm
    have h4 : (sumBig k cx : ℝ) * Dw.q ≤ F * Mb * m :=
      mul_le_mul h1 h3 (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hMb)
    rw [Finset.sum_ite, e1, e2, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hp1.le
  refine ⟨0, fun T io e ho y => ?_⟩
  have hall := fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y
  constructor
  · rw [Nat.cast_zero, EReal.coe_zero]
    exact Finset.sum_nonneg fun f _ => (hall f).1
  · intro ha
    rw [Nat.cast_zero, zero_add]
    refine le_trans ?_ (EReal.coe_le_coe_iff.2 hsum)
    rw [ereal_coe_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    by_cases hf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f
    · simp only [B, if_pos hf]
      exact (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) ha h2 hd f (cx f) hf.1).1 hs
    · simp only [B, if_neg hf]
      exact (hall f).2 ha

end GlobalTheory.OscSplit

end
end

section



open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop.FlatDegProof

theorem flatDegAt_of_st {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hS : FlatDegreeSt) : FlatDegAt p i Y := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hL : Laws Y.U (xiR D) := GlobalTheory.LawsDeep.laws_deep D p.T _ Y _ _ p.fw.laws hj hY.1
  obtain ⟨hd, χ, hχ, h1, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q p.fw.laws.pins.1 p.Del p.h0
  have := hS D.host.E p.T.Q.H hH χ hχ (p.T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) hL
  unfold FlatDegAt
  rwa [← h1]

end GlobalTheory.CovTop.FlatDegProof
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CopEx

theorem exists_cop : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) →
    ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (F G : Thick D.κ D.t) (u : T ⟶ F) (q : F ⟶ G) (r : Λ.L.obj U ⟶ G),
      (KK D.κ D.t).QAt u ∧ IsLev F.δ (n + 1) ∧ Function.Surjective q.φ ∧ (∀ b, q.φ b ∈ G.J → b ∈ F.J) ∧
        IsCop (n + 1) (u ≫ q) r := by
  intro D Λ n U T hT hU
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.hom_spec_points_levels D Λ
  haveI : Algebra.Smooth D.R (Sec D.s U.unop.1) := (GlobalTheory.T.smooth_sections_mono_reduction_affine_inf D).1 U.unop
  obtain ⟨m, pres, hpres⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType D.R (Sec D.s U.unop.1))
  obtain ⟨g, hgx, hgR⟩ := h2 U T hU
  choose bl hbl using fun i : Fin m ↦ T.surj (g (pres (MvPolynomial.X i)))
  obtain ⟨F, u, τ, hfree, hQ⟩ := GlobalTheory.T.exists_freeThickening_level_finitelyMany_elements D.R D.I D.κ D.X₀ D.t n m T hT
  let ψ : MvPolynomial (Fin m) D.R →ₐ[D.R] F.B := MvPolynomial.aeval fun i ↦ u.φ (bl i) + τ i
  have hψX : ∀ i, ψ (MvPolynomial.X i) = u.φ (bl i) + τ i := fun i ↦ MvPolynomial.aeval_X _ _

  have hψπ : ∀ p, F.π (ψ p) = u.φ₀ (g (pres p)) := by
    have e : F.π.comp (ψ : MvPolynomial (Fin m) D.R →+* F.B) =
        u.φ₀.comp (g.comp (pres : MvPolynomial (Fin m) D.R →+* Sec D.s U.unop.1)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show F.π (ψ (MvPolynomial.C r)) = u.φ₀ (g (pres (MvPolynomial.C r)))
        have hC : MvPolynomial.C r = algebraMap D.R (MvPolynomial (Fin m) D.R) r := rfl
        rw [hC, AlgHom.commutes, AlgHom.commutes, hgR, u.comm, u.φ.commutes]
      · intro i
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hψX, map_add (f := _)]
        rw [(F.ker _).2 (hfree.2.1 i), add_zero, ← hbl i, u.comm]
    exact fun p ↦ RingHom.congr_fun e p
  have hker : ∀ k ∈ RingHom.ker pres, ψ k ∈ F.J := fun k hk ↦
    (F.ker _).1 (by rw [hψπ, (RingHom.mem_ker).1 hk, map_zero, map_zero])
  set 𝔟 : Ideal F.B := Ideal.span {y | ∃ j : ℕ, j ≠ 0 ∧ ∃ x ∈ ψ '' (RingHom.ker pres : Set _), y = F.δ.dpow j x}
    with h𝔟def
  have h𝔟 : F.δ.IsSubDPIdeal 𝔟 := (GlobalTheory.DPQuot.quotient_subDPIdeal F.B F.J F.δ).2 _ (by
    rintro _ ⟨k, hk, rfl⟩; exact hker k hk)
  obtain ⟨G, q, hqs, hq0, hGJ, hGlev, hquniv⟩ := GlobalTheory.T.exists_quotient_nilCrystallineThickening_of_subDPIdeal D.R D.I D.κ D.X₀ D.t F 𝔟 h𝔟
  have hψ𝔟 : ∀ k ∈ RingHom.ker pres, (q.φ.comp ψ) k = 0 := fun k hk ↦ (hq0 _).2
    (Ideal.subset_span ⟨1, one_ne_zero, ψ k, ⟨k, hk, rfl⟩, (F.δ.dpow_one (hker k hk)).symm⟩)

  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B :=
    (Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟).comp
      (Ideal.quotientKerAlgEquivOfSurjective hpres).symm.toAlgHom
  have hy : ∀ p, y (pres p) = q.φ (ψ p) := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p) = Ideal.Quotient.mk _ p :=
      (AlgEquiv.symm_apply_eq _).2 rfl
    change Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟
      ((Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p)) = _
    rw [this]
    rfl
  have hyπ : G.π.comp (y : Sec D.s U.unop.1 →+* G.B) = (u ≫ q).φ₀.comp g := by
    ext a
    obtain ⟨p, rfl⟩ := hpres a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hy]
    rw [← q.comm, hψπ]
    rfl
  obtain ⟨r, hr⟩ := (h1 U G y).1 (by
    rw [hyπ, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, (u ≫ q).pt])
  refine ⟨F, G, u, q, r, hQ, hfree.1, hqs, ?_, hGlev _ hfree.1, ?_⟩
  · intro b hb
    rw [hGJ] at hb
    obtain ⟨j, hj, hjb⟩ := (Ideal.mem_map_iff_of_surjective _ hqs).1 hb
    have : b - j ∈ 𝔟 := (hq0 _).1 (by rw [map_sub]; change q.φ b - q.φ j = 0; rw [← hjb]; exact sub_self _)
    have := F.J.add_mem hj (h𝔟.isSubideal this)
    rwa [add_sub_cancel] at this
  intro S hS a b

  have hsame : ∀ x, S.π (b.φ (Λ.e U x)) = a.φ₀ (g x) := by
    have e := h3 U S.B₀ (b.φ₀.comp ((Λ.L.obj U).π.comp (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B)))
      (a.φ₀.comp g) (by
        rw [Cris.spMap_comp, Category.assoc, Λ.pt U, ← Category.assoc, b.pt, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, a.pt])
    intro x
    rw [← b.comm]
    exact RingHom.congr_fun e x
  let c : Fin m → S.B := fun i ↦ b.φ (Λ.e U (pres (MvPolynomial.X i))) - a.φ (bl i)
  have hc : ∀ i, c i ∈ S.J := by
    intro i
    refine (S.ker _).1 ?_
    simp only [c, map_sub, hsame, ← a.comm, hbl i, sub_self]
  obtain ⟨g', ⟨hg'u, hg'τ⟩, hg'uniq⟩ := hfree.2.2 S hS a c hc
  have hg'ψ : ∀ p, g'.φ (ψ p) = b.φ (Λ.e U (pres p)) := by
    have e : g'.φ.comp ψ = b.φ.comp ((Λ.e U).toAlgHom.comp pres) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, hψX, map_add (f := _), AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
      rw [hg'τ i, ← Thick.comp_φ, hg'u]
      simp only [c]
      abel
    exact fun p ↦ AlgHom.congr_fun e p
  have hkill : ∀ z ∈ 𝔟, g'.φ z = 0 := by
    intro z hz
    refine (Ideal.span_le (I := RingHom.ker (g'.φ : F.B →+* S.B))).2 ?_ hz
    rintro _ ⟨j, hj, _, ⟨k, hk, rfl⟩, rfl⟩
    change g'.φ (F.δ.dpow j (ψ k)) = 0
    have hdp := g'.dp.dpow_comp (n := j) _ (hker k hk)
    change S.δ.dpow j (g'.φ (ψ k)) = g'.φ (F.δ.dpow j (ψ k)) at hdp
    rw [← hdp, hg'ψ, (RingHom.mem_ker).1 hk, map_zero, map_zero, dpow_eval_zero _ hj]
  obtain ⟨c0, hc0, hc0u⟩ := hquniv S g' hkill
  refine ⟨c0, ⟨by rw [Category.assoc, hc0, hg'u], ?_⟩, ?_⟩
  · apply Thick.Hom.ext'
    apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := (Λ.e U).surjective z
    obtain ⟨p, rfl⟩ := hpres x
    rw [Thick.comp_φ, hr, hy, ← Thick.comp_φ, hc0, hg'ψ]
  · rintro c1 ⟨hc1a, hc1b⟩
    refine hc0u c1 (hg'uniq (q ≫ c1) ⟨by rw [← Category.assoc, hc1a], fun i ↦ ?_⟩)
    have hτ : τ i = ψ (MvPolynomial.X i) - u.φ (bl i) := by rw [hψX]; abel
    rw [hτ, map_sub, Thick.comp_φ, Thick.comp_φ, ← hy, ← hr, ← Thick.comp_φ, hc1b, ← Thick.comp_φ q c1,
      ← Thick.comp_φ u, ← Category.assoc, hc1a]

end GlobalTheory.CopEx
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.vectorFormTensor_range_le_unitaryAutFormsWeightLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.range_Phi_le_forms | exact GlobalTheory.BCT.TrKer.range_Phi_le_forms | (intros; apply GlobalTheory.BCT.TrKer.range_Phi_le_forms <;> assumption)
end
