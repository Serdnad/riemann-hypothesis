module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCusps
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlab
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConjKappa
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle032
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = _root_.Formalism.L2.PjFree.relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  first | exact @GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct | exact GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct | (intros; apply GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.decay_of_vanishing_at_cusps' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N R : ℕ) (δ s : ℝ), 0 < N → 0 < R → 0 < δ → 0 ≤ s → ∃ C : ℝ, ∀ (f : CM Ψ N N → ℂ) (B : ℝ), DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} → (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N, f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) → (∀ Z ∈ HnGe Ψ N (δ / 4), ‖f Z‖ ≤ B) → (∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0)) → ∀ Z ∈ HnGe Ψ N δ, ‖f Z‖ * detIm Z ^ s ≤ C * B := by
  first | exact @GlobalTheory.SW.decay_of_vanishing_at_cusps | exact GlobalTheory.SW.decay_of_vanishing_at_cusps | (intros; apply GlobalTheory.SW.decay_of_vanishing_at_cusps <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_splitIdempotents_of_relTraceOneModTwo : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∃ s : Finset (Formalism.L2.Theta.AE D), (∀ e ∈ s, IsSplitIdem D e ∧ ∀ e' ∈ s, e ≠ e' → e * e' = 0 ∧ e * cA D e' = 0) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] w - ∑ e ∈ s, e = 2 * a) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) - ∑ e ∈ s, (e + cA D e) = 2 * a) ∧ ∀ e, IsSplitIdem D e → e ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)} ∧ (e ∈ s ∨ cA D e ∈ s ∨ ∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, e = 2 * a) := by
  first | exact @GlobalTheory.IdemModTwo.exists_split_idempotents | exact GlobalTheory.IdemModTwo.exists_split_idempotents | (intros; apply GlobalTheory.IdemModTwo.exists_split_idempotents <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.dual_half_level_marking_exists_and_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ζ : ℂ), SelfD X L → IsMark l L mk → IsPrimitiveRoot ζ l.M → (∃ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ) ∧ (∀ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ → L ≤ LinearMap.range δ ⊔ Mfr l • L ∧ (∀ a, δ a ∈ Mfr l • L ↔ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ ga : GL (Fin r) E, IsUn X ga → IsMark l (mapL ga L) (mvMap ga mk) ∧ IsDual X l ζ (mapL ga L) (mvMap ga mk) (mvMap ga δ)) ∧ ∀ mk' δ' : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk' → IsDual X l ζ L mk' δ' → (∀ a, δ a - δ' a ∈ Mfr l • L) → ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) ∧ conjI (Mfr l) = l.Mb ∧ Mfr l * l.Mb = Ideal.span {(l.M : 𝓞 E)} ∧ ∀ n N : ℕ, 0 < N → ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y := by
  first | exact @GlobalTheory.Dict.DualMark.dual_marking | exact GlobalTheory.Dict.DualMark.dual_marking | (intros; apply GlobalTheory.Dict.DualMark.dual_marking <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.uniformisation_component_lattices_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp), (U.X k).κ0 = 2 * (U.X k).ξ0 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ r = (W.F.Di (W.ik k)).p + (W.F.Di (W.ik k)).q ∧ Function.Injective (W.emb k) ∧ Submodule.span E (Set.range (W.emb k)) = ⊤ ∧ ∀ a b, (((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (W.emb k a) (W.emb k b) := by
  first | exact @GlobalTheory.Dict.uw_lattice | exact GlobalTheory.Dict.uw_lattice | (intros; apply GlobalTheory.Dict.uw_lattice <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem form_eq_zero_of_im {V : Type} [AddCommGroup V] [Module ℂ V] (f : V → V → ℂ)
    (h1 : ∀ w, IsLinearMap ℂ (fun z => f z w)) (h2 : ∀ z, IsLinearMap ℝ (f z)) (S : Set V)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ u ∈ S, ∀ v ∈ S, (f u v).im = 0) (z w : V) : f z w = 0 := by
  have key : ∀ z w, (f z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem u hu =>
      induction hw using Submodule.span_induction with
      | mem v hv => exact h u hu v hv
      | zero => rw [(h2 u).map_zero, zero_im]
      | add a b _ _ ha hb => rw [(h2 u).map_add (f := _), add_im, ha, hb, add_zero]
      | smul t a _ ha => rw [(h2 u).map_smul, smul_im, ha, smul_zero]
    | zero => rw [(h1 w).map_zero, zero_im]
    | add a b _ _ ha hb => rw [(h1 w).map_add (f := _), add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [← Complex.coe_smul, (h1 w).map_smul, smul_eq_mul, im_ofReal_mul, ha, mul_zero]
  have h3 := key (I • z) w
  rw [(h1 w).map_smul, smul_eq_mul, I_mul_im] at h3
  exact Complex.ext h3 (key z w)

theorem hermForm_eq_of_im {g : ℕ} (M M' : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ u ∈ S, ∀ v ∈ S, (hermForm M (a * u) v).im = (hermForm M' u (b * v)).im) (z w : Fin g → ℂ) :
    hermForm M (a * z) w = hermForm M' z (b * w) := by
  refine sub_eq_zero.1 (form_eq_zero_of_im (fun z w => hermForm M (a * z) w - hermForm M' z (b * w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) S hS
    (fun u hu v hv => by rw [sub_im, h u hu v hv, sub_self]) z w)
  · simp only [hermForm, mul_add, add_dotProduct]; ring
  · simp only [hermForm, mul_smul_comm, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hermForm, mul_add, star_add, mulVec_add, dotProduct_add]; ring
  · simp only [hermForm, mul_smul_comm, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_eq_hermForm (x : Frame X.Ψ r) (z w : Fin g → ℂ) :
    hx X bas idx x z w = hermForm (ThFr.Hm X bas idx x) z w := (hermForm_Hm bas idx x z w).symm

theorem span_range_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range (pv X idx x)) = ⊤ := by
  have col (s : Fin g → Fin g ⊕ Fin g) (t : Fin g → ℝ) :
      perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) ∈ Submodule.span ℝ (Set.range (pv X idx x)) := by
    have : perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) =
        ∑ k, t k • pv X idx x (bas (Pi.single (s k) 1)) := by
      funext i
      simp [mulVec, dotProduct, pv, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine eq_top_iff.2 fun z _ => ?_
  have hu := isUnit_det_perMat idx hs hx
  have hY := (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit
  set τ := tauMat X bas idx x with hτ
  set y := hMat X bas idx x *ᵥ z with hy
  obtain ⟨t, ht⟩ : ∃ t : Fin g → ℝ, τ.map Complex.im *ᵥ t = fun k => (y k).im :=
    ⟨(τ.map Complex.im)⁻¹ *ᵥ _, by rw [mulVec_mulVec, mul_nonsing_inv _ hY, one_mulVec]⟩
  have h1 : y = (fun k => (((y - τ *ᵥ fun k => (t k : ℂ)) k).re : ℂ)) + τ *ᵥ fun k => (t k : ℂ) := by
    funext k
    apply Complex.ext
    · simp
    · have := congrFun ht k
      simp only [mulVec, dotProduct, map_apply] at this
      simp [mulVec, dotProduct, this]
  have hAB : perMat X bas idx Sum.inl x * τ = perMat X bas idx Sum.inr x :=
    mul_nonsing_inv_cancel_left _ _ hu
  have h2 : z = perMat X bas idx Sum.inl x *ᵥ y := by
    rw [hy, mulVec_mulVec, hMat, mul_nonsing_inv _ hu, one_mulVec]
  rw [h2, h1, mulVec_add, mulVec_mulVec, hAB]
  exact add_mem (col _ _) (col _ _)

theorem span_image_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (L : Lt E r)
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ := by
  rw [eq_top_iff, ← span_range_pv idx hs hx, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem L hL v
  have : pv X idx x v = (k : ℝ)⁻¹ • pv X idx x (k • v) := by
    funext i
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [pv, pv, per_zsmul]
    simp only [Function.comp_apply, Pi.smul_apply, zsmul_eq_mul, real_smul, ofReal_inv, Pi.mul_apply, Pi.intCast_apply,
      ofReal_intCast]
    rw [inv_mul_cancel_left₀ hk']
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hv, rfl⟩)

theorem pv_smul (x : Frame X.Ψ r) (a : E) (v : Fin r → E) :
    pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
  funext fun _ => per_smul X x a v _

theorem EF_smul_left (a : E) (u v : Fin r → E) : EF X (a • u) v = EF X u (cc a • v) := by
  have h (b : E) : IsCMField.complexConj E (IsCMField.complexConj E a * b) = a * IsCMField.complexConj E b := by
    rw [map_mul, IsCMField.complexConj_apply_apply]
  simp only [EF_def, herm, cc, Pi.smul_apply, smul_eq_mul, h]
  congr 2
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hx_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  intro E _ _ _ r X g bas idx n hs _ x hx
  have him {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v) :
      (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) :=
    im_hermForm_Hm idx hs hx u v
  simp only [hx_eq_hermForm]
  refine ⟨fun z w => ?_, fun z hz => hermForm_Hm_pos idx hs hx hz, him hx, fun a z w => ?_,
    pv_smul idx x, fun u v h => ?_, fun L hL => ⟨span_image_pv idx hs hx L hL, fun M _ h z w => ?_⟩,
    fun ga hga => ⟨hga.lact_mem hx, fun v => ?_, fun h τ i => ?_, fun z w => ?_⟩⟩
  · have hH := Hm_isHermitian idx hs hx
    rw [hermForm, hermForm, ← RCLike.star_def, ← star_dotProduct_star, star_mulVec, star_star, hH.eq,
      dotProduct_mulVec]
  · refine hermForm_eq_of_im _ _ (fun j => rowType X (idx j) a) (fun j => rowType X (idx j) (cc a)) _
      (span_range_pv idx hs hx) ?_ z w
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have h1 := him hx (a • u) v
    have h2 := him hx u (cc a • v)
    rw [pv_smul] at h1 h2
    rw [EF_smul_left] at h1
    exact h1.trans h2.symm
  · obtain ⟨m, rfl⟩ := vecQ_surjective X bas u
    obtain ⟨m', rfl⟩ := vecQ_surjective X bas v
    have h' (t) : EF X (vecQ X bas m) (vecQ X bas t) = EF X (vecQ X bas m') (vecQ X bas t) := by
      have := (him hx (vecQ X bas m) (vecQ X bas t)).symm.trans (h ▸ him hx (vecQ X bas m') (vecQ X bas t))
      exact_mod_cast this
    simp only [EF_vecQ hs] at h'
    congr 1
    funext j
    rcases j with j | j
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)
  · have := hermForm_eq_of_im M (ThFr.Hm X bas idx x) 1 1 _ (span_image_pv idx hs hx L hL) (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [_root_.one_mul, _root_.one_mul, h u hu v hv, him hx]) z w
    rwa [_root_.one_mul, _root_.one_mul] at this
  · rw [pv, per_lact x hga, pv]
  · have e1 : mat (lact ga x) τ = (ga : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have e2 : FD.gram τ.1 X.Gm (mat (lact ga x) τ) = FD.gram τ.1 X.Gm (mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hga]
    have h' := h τ i
    unfold dmin at h' ⊢
    rwa [e2]
  · have := hermForm_eq_of_im (ThFr.Hm X bas idx (lact ga x)) (ThFr.Hm X bas idx x) 1 1 _
      (span_range_pv idx hs hx) (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      have h1 := him (hga.lact_mem hx) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v)
      rw [pv, pv, per_lact x hga, per_lact x hga, EF_def, hga, ← EF_def] at h1
      rw [_root_.one_mul, _root_.one_mul, him hx]
      exact h1) z w
    rwa [_root_.one_mul, _root_.one_mul] at this

end GlobalTheory.Dict
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.gaussianKernel_integrableOn_thin_slab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → 2 * r ≤ n → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ x₁ ∈ X.dom, IntegrableOn (fun x₂ => kern X hr idx P x₁ x₂) (slab X δ) volume ∧ ∃ C : ℝ, ∀ x₂ ∈ slab X δ, ‖kern X hr idx P x₁ x₂‖ ≤ C := by
  first | exact @GlobalTheory.SW.kern_integrableOn_slab | exact GlobalTheory.SW.kern_integrableOn_slab | (intros; apply GlobalTheory.SW.kern_integrableOn_slab <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.maximalIsotropic_doubled_graph_or_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ γ' : GL (Fin r) E, IsUn X γ → IsUn X γ' → botSpan (iota X 1 γ) = botSpan (iota X 1 γ') → γ = γ') ∧ ∀ U : Lag E r, (∃ γ : GL (Fin r) E, IsUn X γ ∧ botSpan (iota X 1 γ) = U.1) ∨ ∃ ξ : Fin r → E, ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0 ∧ Sum.elim ξ 0 ᵥ* dblT X ∈ U.1 := by
  first | exact @GlobalTheory.SW.lag_graph_or_isotropic | exact GlobalTheory.SW.lag_graph_or_isotropic | (intros; apply GlobalTheory.SW.lag_graph_or_isotropic <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.tensorLattice_vacua_exist_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (∃ v, IsVac X bas w (tens Λ L) v) ∧ (∀ v v', IsVac X bas w (tens Λ L) v → IsSB v' → (∀ y ∈ tens Λ L, epsW X w y • heisG X bas y v' = v') → v' = ip v' v • v) ∧ (∀ φ : TF n g, IsSB φ → ∀ v, IsVac X bas w (tens Λ L) v → projA X bas w (tens Λ L) φ = ip φ v • v) ∧ ∀ L', SelfD X L' → ∀ Λ' ∈ Vset E n M, ∀ v v', IsVac X bas w (tens Λ L) v → IsVac X bas w (tens Λ' L') v' → ((tens Λ' L').relIndex (tens Λ L) : ℝ) * ‖ip v v'‖ ^ 2 = 1 := by
  first | exact @GlobalTheory.SW.TensVac.vacua | exact GlobalTheory.SW.TensVac.vacua | (intros; apply GlobalTheory.SW.TensVac.vacua <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem cc_cc (a : E) : cc (cc a) = a := by
  unfold cc
  exact IsCMField.complexConj_apply_apply E a

theorem cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a := by
  unfold cc
  exact Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem sum_trace {ι : Type} [Fintype ι] (B : Module.Basis ι ℚ E) (b d : E) :
    ∑ j, Algebra.trace ℚ E (b * cc (B j)) * B.repr d j = Algebra.trace ℚ E (b * cc d) := by

  have hd : cc d = ∑ j, B.repr d j • cc (B j) := by
    conv_lhs => rw [← B.sum_repr d]
    unfold cc

    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_rat_smul _ _ _

  rw [hd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

theorem vec_inl (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = y₁ a - y₂ a := by
  simp [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

theorem vec_inr (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) = X.κ0 / 4 * ∑ c, (y₁ c + y₂ c) * X.Gm c a := by
  simp only [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem split_form (y₁ y₂ z₁ z₂ : Fin r → E) :
    ∑ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inl a)) -
      ∑ a, cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inr a)) * (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) =
      -(X.κ0 / 2) * herm X.Gm y₂ z₂ - -(X.κ0 / 2) * herm X.Gm y₁ z₁ := by

  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by unfold cc; exact map_add _ a b
  have hsub : ∀ a b : E, cc (a - b) = cc a - cc b := fun a b => by unfold cc; exact map_sub _ a b
  have hsum : ∀ f : Fin r → E, cc (∑ c, f c) = ∑ c, cc (f c) := fun f => by
    unfold cc; exact map_sum _ _ _
  have hk : cc (X.κ0 / 4) = -(X.κ0 / 4) := by
    have h4 : cc (4 : E) = 4 := by unfold cc; exact map_ofNat _ 4
    have hd : cc (X.κ0 / 4) = cc X.κ0 / cc 4 := by unfold cc; exact map_div₀ _ _ _
    rw [hd, h4, DblPer.cc_kappa X, neg_div]
  simp only [vec_inl, vec_inr, cc_mul, hadd, hsub, hsum, hk, X.Gm_herm, herm]
  simp only [Finset.mul_sum, Finset.sum_mul]

  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

noncomputable def dv (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) : Fin r ⊕ Fin r → E :=
  Sum.elim (vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)))
    (vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)))) ᵥ* dblT X

theorem dv_add (u v) : dv X bas (u + v) = dv X bas u + dv X bas v := by
  have h₁ : Sum.elim ((u + v).1 ∘ Sum.inl) ((u + v).2 ∘ Sum.inl) =
      Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) + Sum.elim (v.1 ∘ Sum.inl) (v.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((u + v).1 ∘ Sum.inr) (-((u + v).2 ∘ Sum.inr)) =
      Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) + Sum.elim (v.1 ∘ Sum.inr) (-(v.2 ∘ Sum.inr)) := by
    ext (i | i)
    · rfl
    · simp only [Sum.elim_inr, Pi.neg_apply, Function.comp_apply, Prod.snd_add, Pi.add_apply]
      ring
  unfold dv
  rw [h₁, h₂, vecQ_add, vecQ_add, ← Matrix.add_vecMul, Sum.elim_add_add]

theorem dv_smul (q : ℚ) (u) : dv X bas (q • u) = q • dv X bas u := by
  have h₁ : Sum.elim ((q • u).1 ∘ Sum.inl) ((q • u).2 ∘ Sum.inl) =
      q • Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((q • u).1 ∘ Sum.inr) (-((q • u).2 ∘ Sum.inr)) =
      q • Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) := by
    ext (i | i) <;> simp
  have h₃ : ∀ f g' : Fin r → E, Sum.elim (q • f) (q • g') = q • Sum.elim f g' := fun f g' => by
    ext (i | i) <;> rfl
  unfold dv
  rw [h₁, h₂, vecQ_smul, vecQ_smul, h₃, Matrix.smul_vecMul]

noncomputable def crdMap : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ]
    ((QI E r → ℚ) × (QI E r → ℚ)) where
  toFun u := (fun p => Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)),
    fun p => (Module.finBasis ℚ E).repr (dv X bas u (Sum.inl p.1)) p.2)
  map_add' u v := by
    ext p <;> simp [dv_add, add_mul]
  map_smul' q u := by
    ext p <;> simp [dv_smul]

theorem crdMap_pair (u v) : (crdMap X bas u).1 ⬝ᵥ (crdMap X bas v).2 =
    Algebra.trace ℚ E (∑ a, dv X bas u (Sum.inr a) * cc (dv X bas v (Sum.inl a))) := by
  have e₁ : ∀ p : QI E r, (crdMap X bas u).1 p =
      Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)) := fun p => rfl
  have e₂ : ∀ p : QI E r, (crdMap X bas v).2 p =
      (Module.finBasis ℚ E).repr (dv X bas v (Sum.inl p.1)) p.2 := fun p => rfl
  simp only [dotProduct, e₁, e₂]

  rw [Fintype.sum_prod_type, map_sum (Algebra.trace ℚ E)]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [sum_trace (Module.finBasis ℚ E) (dv X bas u (Sum.inr a)) (dv X bas v (Sum.inl a))]

theorem dbl_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ), IsSympl X bas → ∃ F : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ] ((QI E r → ℚ) × (QI E r → ℚ)), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) ∧ ∀ (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) (y₁ y₂ : Fin r → E), y₁ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) → y₂ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) → (∀ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = ∑ j, (F u).2 (a, j) • Module.finBasis ℚ E j) ∧ ∀ a j, (F u).1 (a, j) = Algebra.trace ℚ E ((Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc (Module.finBasis ℚ E j)) := by
  intro E _ _ _ r X g bas hs
  refine ⟨crdMap X bas, fun u v => ?_, fun u y₁ y₂ h₁ h₂ => ?_⟩
  ·
    have hsum : ∀ f : Fin r → E, cc (∑ a, f a) = ∑ a, cc (f a) := fun f => by
      unfold cc; exact map_sum _ _ _
    have hsw : (crdMap X bas u).2 ⬝ᵥ (crdMap X bas v).1 =
        Algebra.trace ℚ E (∑ a, cc (dv X bas v (Sum.inr a)) * dv X bas u (Sum.inl a)) := by
      rw [dotProduct_comm, crdMap_pair, ← trace_cc, hsum]
      simp only [cc_mul, cc_cc]
    rw [crdMap_pair, hsw, ← map_sub]
    unfold dv
    rw [split_form, map_sub, ← EF_def, ← EF_def, EF_vecQ hs, EF_vecQ hs]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Pi.neg_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_neg, neg_mul]
    ring
  · subst h₁ h₂
    exact ⟨fun a => ((Module.finBasis ℚ E).sum_repr _).symm, fun a j => rfl⟩

end GlobalTheory.SW.DblLat
end
