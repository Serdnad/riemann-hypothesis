module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory

theorem formCalculus : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    A.IsForm 1 ∧ (∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) ∧
      A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) ∧ A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α) ∧
    (∀ (w : A.Pt → Ev n) (β : A.Fld), A.IsForm (fld A w) → A.IsForm β →
      A.del (fld A w * β) = A.del (fld A w) * β + fld A w * A.del β ∧ A.dbar (fld A w * β) = A.dbar (fld A w) * β + fld A w * A.dbar β) ∧
    (∀ (ι : Type) (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ), (∀ i, A.IsForm (fld A (w i))) → A.IsForm (evalF A w P) ∧
      ((∀ i, A.del (fld A (w i)) = 0) → A.del (evalF A w P) = 0) ∧ ((∀ i, A.dbar (fld A (w i)) = 0) → A.dbar (evalF A w P) = 0)) ∧
    ∀ (M' : Type) [TopologicalSpace M'] (n' : ℕ) (A' : HolAtlas M' n') (f : M' → M), A.IsHolo A' f →
      A.pullback A' f 1 = 1 ∧ ∀ (c : ℂ) (α β : A.Fld), A.pullback A' f (α + β) = A.pullback A' f α + A.pullback A' f β ∧
        A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β ∧ A.pullback A' f (c • α) = c • A.pullback A' f α ∧
        (A.IsForm α → A'.IsForm (A.pullback A' f α) ∧ A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
          A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α)) := by
  intro M _ n A
  refine ⟨(GlobalTheory.T.isForm_one_add_mul_smul M n A).1, fun c α β hα hβ => ?_, fun w β hw hβ => GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A w β hw hβ, fun ι w P hw => ?_,
    fun M' _ n' A' f hf => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 c α β hα hβ
    obtain ⟨d1, d2⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A α hα
    obtain ⟨e1, e2, e3, e4⟩ := (GlobalTheory.T.del_dbar_additive_complexLinear_one M n A).2 c α β hα hβ
    exact ⟨h1, h2, h3, d1, d2, e1, e2, e3, e4⟩
  · induction P using MvPolynomial.induction_on with
    | C r =>
      have e : evalF A w (C r) = ((r : ℂ) • (1 : A.Fld)) := by
        funext x
        simp [evalF, fld, Algebra.algebraMap_eq_smul_one]
        first | rfl | exact Subalgebra.coe_smul _ _ _ | (rw [SetLike.val_smul]; simp) | simp [Subalgebra.coe_algebraMap]
      have h1 := (GlobalTheory.T.isForm_one_add_mul_smul M n A).1
      have hf := ((GlobalTheory.T.isForm_one_add_mul_smul M n A).2 (r : ℂ) 1 1 h1 h1).2.2
      obtain ⟨⟨z1, z2⟩, hl⟩ := GlobalTheory.T.del_dbar_additive_complexLinear_one M n A
      obtain ⟨-, -, s1, s2⟩ := hl (r : ℂ) 1 1 h1 h1
      rw [e]
      exact ⟨hf, fun _ => by rw [s1, z1, smul_zero], fun _ => by rw [s2, z2, smul_zero]⟩
    | add p q hp hq =>
      have e : evalF A w (p + q) = evalF A w p + evalF A w q := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a1, -, -⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 1 _ _ hp1 hq1
      obtain ⟨l1, l2, -, -⟩ := (GlobalTheory.T.del_dbar_additive_complexLinear_one M n A).2 1 _ _ hp1 hq1
      rw [e]
      exact ⟨a1, fun h => by rw [l1, hp2 h, hq2 h, add_zero], fun h => by rw [l2, hp3 h, hq3 h, add_zero]⟩
    | mul_X p i hp =>
      have e : evalF A w (p * X i) = evalF A w p * fld A (w i) := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨-, a2, -⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 1 _ _ hp1 (hw i)
      obtain ⟨b1, b2⟩ := GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A (fun x => aeval (fun i => w i x) (p.map (algebraMap ℝ ℂ))) (fld A (w i)) hp1 (hw i)
      rw [e]
      refine ⟨a2, fun h => ?_, fun h => ?_⟩
      · change A.del (fld A _ * fld A (w i)) = 0
        rw [b1]
        change A.del (evalF A w p) * _ + _ = 0
        rw [hp2 h, h i, zero_mul, mul_zero, add_zero]
      · change A.dbar (fld A _ * fld A (w i)) = 0
        rw [b2]
        change A.dbar (evalF A w p) * _ + _ = 0
        rw [hp3 h, h i, zero_mul, mul_zero, add_zero]
  · refine ⟨funext fun x => map_one _, fun c α β => ⟨funext fun x => map_add _ _ _, funext fun x => map_mul _ _ _,
      funext fun x => map_smul (pull _) c _, fun hα => ?_⟩⟩
    obtain ⟨d1, d2⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A α hα
    exact ⟨GlobalTheory.T.holAtlas_isForm_pullback_holomorphic M M' n n' A A' f α hf hα, GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar M M' n n' A A' f α hf hα d1 d2⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

section ArcQuot

variable {Y : Scheme.{0}} {W : Y.Opens}

theorem arcPt_mem_basicOpen (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) (q : Γ(Y, W)) (s : Sp ℂ) :
    (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ Y.basicOpen q ↔ φ q ≠ 0 := by
  change (spMap φ) s ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen q ↔ _
  rw [hW.fromSpec_preimage_basicOpen q]
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change q ∉ (Ideal.comap φ s.asIdeal) ↔ _
  rw [hs]
  simp [Ideal.mem_comap]

theorem evalPt_arcPt (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ)
    (h : ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W) :
    GlobalTheory.TangentOrigin.evalPt (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) W h = φ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hW _ h
  dsimp only [spMap] at this
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem arcPt_top_le (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) :
    ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  change ⊤ ≤ spMap φ ⁻¹ᵁ (hW.fromSpec ⁻¹ᵁ W)
  rw [hW.fromSpec_preimage_self]
  exact le_rfl

theorem exists_punctured_ne_zero {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    {u₀ : ℂ} (hu₀ : u₀ ∈ Metric.ball (0 : ℂ) r) (h₀ : f u₀ ≠ 0) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → f u ≠ 0 := by
  have ha := hf.analyticOnNhd Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  rcases (ha 0 h0).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact absurd (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected h0 hz hu₀) h₀
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hz
    obtain ⟨ε, hε, hz⟩ := hz
    refine ⟨min ε r, lt_min hε hr, min_le_right _ _, fun u hu hu0 => hz u ?_ hu0⟩
    exact Metric.ball_subset_ball (min_le_left _ _) hu

end ArcQuot

end GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

theorem exists_quot_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  intro k _ Y p B O m W hW i hWi ψ r hψ hout
  obtain ⟨hr, hhol⟩ := hψ
  have hu₀ : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  have hu₀0 : ((r / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (half_pos hr).ne'
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hyO : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ O :=
    hout _ hu₀ hu₀0 (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hyW : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ W :=
    arcPt_top_le hW (ψ (r / 2 : ℝ)) (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨q, hqle, hqy⟩ := hW.exists_basicOpen_le (V := O ⊓ B.U i) ⟨_, hyO, hWi hyW⟩ hyW
  have hq0 : ψ (r / 2 : ℝ) q ≠ 0 := (arcPt_mem_basicOpen hW _ q s).1 hqy
  haveI := hW.isLocalization_basicOpen q
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj q (resG Y hqle (m.loc i))
  obtain ⟨ρ, hρ, hρr, hne⟩ := exists_punctured_ne_zero (hhol q) hu₀ hq0 hr
  refine ⟨ρ, a, q ^ n, hρ, hρr, fun u hu hu0 => ?_⟩
  have hqu : ψ u q ≠ 0 := hne u hu hu0
  refine ⟨by rw [map_pow]; exact pow_ne_zero _ hqu, fun hO hi => ?_⟩
  have hD : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ Y.basicOpen q :=
    fun s _ => (arcPt_mem_basicOpen hW (ψ u) q s).2 hqu
  have hWx := arcPt_top_le hW (ψ u)
  have e := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hD) hna
  have hres (z : Γ(Y, W)) : GlobalTheory.TangentOrigin.evalPt _ _ hD (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen q) z) = ψ u z := by
    exact (GlobalTheory.TangentOrigin.evalPt_res _ (Y.basicOpen_le q) hWx hD z).trans
      (DFunLike.congr_fun (evalPt_arcPt hW (ψ u) hWx) z)
  rw [map_mul, map_pow, hres, hres] at e
  rw [H0.val_apply, ← GlobalTheory.TangentOrigin.evalPt_res _ hqle _ hD, map_pow, e]

end GlobalTheory.Vanishing
end
end

section

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem exists_ringEquiv {A : Type} [CommRing A] {Z : Scheme.{0}} (κ : Sp A ⟶ Z) [IsOpenImmersion κ] :
    ∃ θ : A ≃+* Γ(Z, κ.opensRange), spMap θ.toRingHom ≫ κ = (isAffineOpen_opensRange κ).fromSpec := by
  let e := IsOpenImmersion.isoOfRangeEq (isAffineOpen_opensRange κ).fromSpec κ
    (isAffineOpen_opensRange κ).range_fromSpec
  let e' : CommRingCat.of A ≅ Γ(Z, κ.opensRange) := (Scheme.Spec.preimageIso (X := .op _) (Y := .op _) e).unop
  refine ⟨e'.commRingCatIsoToRingEquiv, ?_⟩
  have : spMap e'.commRingCatIsoToRingEquiv.toRingHom = e.hom := Scheme.Spec.map_preimage e.hom
  rw [this]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure Atlas (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) where
  B : Type
  fin : Finite B
  k : B → ECh Y p
  aff : ∀ b, IsAffineOpen (k b).V
  cov : ∀ x : Y.X, ∃ b, x ∈ (k b).V
  N : ℕ
  A : ∀ b, Matrix (Fin (N + 1)) (Fin (k b).M.n) Γ(Y.X, (k b).V)
  C : ∀ b, Matrix (Fin (k b).M.n) (Fin (N + 1)) Γ(Y.X, (k b).V)
  CA : ∀ b, C b * A b = 1
  tw : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (b b' : B) (h : ⊤ ≤ x ⁻¹ᵁ (k b).V) (h' : ⊤ ≤ x ⁻¹ᵁ (k b').V)
    (hM : ⊤ ≤ x ⁻¹ᵁ ((k b').M.U ⊓ (k b).M.U)), ∃ a : Sˣ, (A b).map (ev x _ h) =
      (a : S) • ((A b').map (ev x _ h') * (chg (k b').M.toMChart (k b).M.toMChart).map (ev x _ hM))

variable {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} (A : Atlas Y p)

namespace Atlas

abbrev V (b : A.B) : Y.X.affineOpens := ⟨(A.k b).V, A.aff b⟩

def alpha (b : A.B) : c.F →+* Γ(Y.X, (A.V b).1) := str (tau (A.aff b))

def cv (b : A.B) : Let Dw.mult → Fin (A.N + 1) → Γ(Y.X, (A.V b).1) :=
  fun z r => (A.A b * (A.k b).u z.1) r z.2

def Dv (b : A.B) : Let Dw.mult → Fin (A.N + 1) → Γ(Y.X, (A.V b).1) :=
  fun z r => ((A.k b).w z.1 * A.C b) z.2 r

end Atlas

variable {A}

structure Cells (A : Atlas Y p) {Z : Scheme.{0}} (π : Z ⟶ Y.X)
    (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1))
    (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) : Prop where
  proper : IsProper π
  normal : Geo.Tor.IsNormalScheme Z
  plk : HasPlk (RingHom.id c.F) A.V A.alpha A.cv π g κ
  cover : ∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)
  ext : ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a'

def cellMat (U : Y.X.affineOpens) (σ : E →+* ℂ) : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (CR Dw.mult U) :=
  Matrix.of (cell MvPolynomial.X σ)

theorem det_cellMat (U : Y.X.affineOpens) (σ : E →+* ℂ) : (cellMat (Dw := Dw) U σ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [cellMat, cell]
  · intro i j hij
    have h1 : ¬ j < i := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_lt hij
    simp [cellMat, cell, h1, h2]


variable (A) in
abbrev cC (b : A.B) : Γ(Y.X, (A.k b).V) →+* CR Dw.mult (A.V b) := MvPolynomial.C


variable (A) in
def uC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) :
    Matrix (Fin (A.k b).M.n) (Fin (Dw.mult σ)) (CR Dw.mult (A.V b)) :=
  (((A.k b).u σ).map (cC A b)).submatrix id (w σ) * cellMat (A.V b) σ


variable (A) in
def wC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (A.k b).M.n) (CR Dw.mult (A.V b)) :=
  (cellMat (A.V b) σ)⁻¹ * (((A.k b).w σ).map (cC A b)).submatrix (w σ) id

theorem wC_mul_uC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) : wC A b w σ * uC A b w σ = 1 := by
  have h1 : (((A.k b).w σ).map (cC A b)).submatrix (w σ) id * (((A.k b).u σ).map (cC A b)).submatrix id (w σ) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.map_mul, (A.k b).wu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]
  have h2 : IsUnit (cellMat (Dw := Dw) (A.V b) σ).det := by rw [det_cellMat]; exact isUnit_one
  calc wC A b w σ * uC A b w σ
      = (cellMat (A.V b) σ)⁻¹ * ((((A.k b).w σ).map (cC A b)).submatrix (w σ) id *
          (((A.k b).u σ).map (cC A b)).submatrix id (w σ)) * cellMat (A.V b) σ := by
        simp only [wC, uC, Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ h2]

variable {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)


variable (κ) in
def cellθ (k : A.B × Pm Dw.mult) : CR Dw.mult (A.V k.1) ≃+* Γ(Z, (κ k.1 k.2).opensRange) :=
  (exists_ringEquiv (κ k.1 k.2)).choose

theorem spMap_cellθ (k : A.B × Pm Dw.mult) :
    spMap (cellθ κ k).toRingHom ≫ κ k.1 k.2 = (isAffineOpen_opensRange (κ k.1 k.2)).fromSpec :=
  (exists_ringEquiv (κ k.1 k.2)).choose_spec

include hZ in
theorem cell_le (k : A.B × Pm Dw.mult) : (κ k.1 k.2).opensRange ≤ π ⁻¹ᵁ (A.k k.1).M.U := by
  rintro _ ⟨y, rfl⟩
  have e : κ k.1 k.2 ≫ π = cbase Dw.mult (A.V k.1) := hZ.plk.base _ _
  have h : (κ k.1 k.2 ≫ π) y ∈ ((A.V k.1).1 : Set Y.X) := by
    rw [e, cbase, Scheme.Hom.comp_apply]
    exact (A.V k.1).2.range_fromSpec.le ⟨_, rfl⟩
  exact (A.k k.1).le (by rw [Scheme.Hom.comp_apply] at h; exact h)

def FlagCellFrameChangeTriangular : Prop :=
  ∀ (k k' : A.B × Pm Dw.mult) (σ : E →+* ℂ), ∃ B : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ))
      Γ(Z, (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange), B.BlockTriangular id ∧
    (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map
        (π.appLE ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange)
          (inf_le_inf (cell_le hZ k) (cell_le hZ k'))).hom *
      ((uC A k'.1 k'.2 σ).map (cellθ κ k')).map (resG Z inf_le_right) =
      ((uC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z inf_le_left) * B

def cellFrames (ht : FlagCellFrameChangeTriangular hZ) : Frames Y π where
  J := A.B × Pm Dw.mult
  U k := (κ k.1 k.2).opensRange
  cover := eq_top_iff.2 fun z _ => by
    obtain ⟨b, w, h⟩ := hZ.cover z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, w), h⟩
  M k := (A.k k.1).M
  le := cell_le hZ
  u k σ := (uC A k.1 k.2 σ).map (cellθ κ k)
  split k σ := ⟨(wC A k.1 k.2 σ).map (cellθ κ k), by
    rw [← Matrix.map_mul, wC_mul_uC, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  tri := ht

end GlobalTheory.FlagMod.FieldFlag
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.BoundProof

section Gen

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem actV_mem_latT (a : Λ) {y : P.V} (hy : y ∈ P.latT) : P.actV a y ∈ P.latT :=
  (P.mem_latT_iff _).2 fun t => by
    obtain ⟨c, hc⟩ := (P.mem_latT_iff y).1 hy (P.actT (star a) t)
    exact ⟨c, by rw [hc, P.pairV_act]; rfl⟩

theorem pairV_inclT_mem {u : P.V} (hu : u ∈ P.latT) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV u (P.inclT y) ∈ (algebraMap O C).range := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]⟩
  | tmul c t =>
    obtain ⟨b, hb⟩ := (P.mem_latT_iff u).1 hu t
    refine ⟨c * b, ?_⟩
    have e : (algebraMap O C c ⊗ₜ[ℤ_[p]] t : P.V) = algebraMap O C c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [P.inclT_tmul, e, map_smul, smul_eq_mul, map_mul, hb]

end Gen

section Gen2

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem pairV_bLie_inclT (x : LieG P.Gt) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV (P.bLie x) (P.inclT y) = algebraMap O C ((P.al y).1 x) := by
  rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end Gen2

section Discr

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

end Discr

end GlobalTheory.FlatModel.BoundProof

namespace GlobalTheory.FlatModel

end GlobalTheory.FlatModel
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.traceLattice_le_span_thetaSeries_awayFromOwnPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  first | exact @GlobalTheory.CompareOff.compareOffOwn_run | exact GlobalTheory.CompareOff.compareOffOwn_run | (intros; apply GlobalTheory.CompareOff.compareOffOwn_run <;> assumption)
end
