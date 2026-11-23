module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle418
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRep
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle387
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle419
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.heisenbergTranslate_fockVacuum_cauchyRiemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  first | exact @GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | exact GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | (intros; apply GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : UniformSpace E) (_ : IsUniformAddGroup E) (_ : CompleteSpace E) (_ : T2Space E) (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)), Function.Injective ι ∧ (∀ φ, φ ∈ Set.range ι ↔ Continuous φ ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤) ∧ (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) ∧ ∀ τ, ∃ π dπ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E), GlobalTheory.SmoothGlob.IsSmoothModRep (A.ε τ) p π dπ ∧ (∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), ∀ x, ι (π g x) = rTr V (A.elt θ τ g) (ι x)) ∧ ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (A.ε τ), ∀ x, ι (dπ X x) = Rder θ V τ ((A.fr τ)⁻¹ * X * A.fr τ) (ι x) := by
  first | exact @GlobalTheory.CuspFrechet.exists_frechet | exact GlobalTheory.CuspFrechet.exists_frechet | (intros; apply GlobalTheory.CuspFrechet.exists_frechet <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapVac

variable {D : D7}

theorem lnk_simil {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') :
    l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L.gram := by
  rw [Int.cast_one, one_mul]
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  exact mul_right_cancel₀ b c

theorem lnk_tau_ne {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') : l.τ ≠ 0 := by
  intro h0
  have e := l.map
  rw [h0, Matrix.zero_mulVec] at e
  have hz : ζ = 0 := neg_eq_zero.mp e.symm
  have n : D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L.gram *ᵥ ζ') = 0 := by
    rw [← l.norm, hz]; simp
  rcases mul_eq_zero.1 n with h1 | h1
  · rcases mul_eq_zero.1 h1 with h3 | h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D (star_eq_zero.1 h3)
  · exact h.2 h1

theorem kap_surj {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) :
    Function.Surjective (l.κ S) := by
  obtain ⟨σ, _, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  intro x
  refine ⟨(rat σ : Mx D L.rank L.rank) ⬝ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S x, ?_⟩
  rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

theorem kap_add {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : l.κ S (v + w) = l.κ S v + l.κ S w :=
  (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).1 v w

theorem kap_sympl {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : symplOH L S (l.κ S v) (l.κ S w) = -symplOH S L v w := by
  have e := (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).2.2.2.2.1 v w
  unfold symplOH
  rw [e, Int.cast_one, one_mul, mul_neg]

theorem kap_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E}
    (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) (Ξ : WO L S → ℂ) (w' : WO S L)
    (hw : heisO ψ S L w' (fun w => star (Ξ (l.κ S w))) = fun w => star (Ξ (l.κ S w))) :
    heisO ψ L S (l.κ S w') Ξ = Ξ := by
  funext x
  obtain ⟨v, rfl⟩ := kap_surj h l S x
  have e := congrFun hw v
  simp only [heisO] at e
  have e2 := congrArg (starRingEnd ℂ) e
  rw [map_mul, GlobalTheory.AdjLawPf.conj_psi ψ hψ] at e2
  simp only [starRingEnd_apply, star_star] at e2
  simp only [heisO]
  rw [kap_sympl h l, ← kap_add h l]
  exact e2

theorem half_mul_left {m n k : ℕ} {e : AE D} (M : Mx D m n) {x : Mx D n k} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem half_mul_right {m n k : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hx]

theorem half_smul {m n : ℕ} {e : AE D} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx]

theorem half_adj {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) := by
  intro i j
  show cA D e * cA D (x j i) = cA D (x j i)
  rw [← map_mul, hx]

theorem split_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hv,
    by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]⟩

theorem kap_half {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    {e : AE D} {w : WO S L} (hh : IsHalf e (l.κ S w)) : IsHalf (cA D e) w := by
  obtain ⟨σ, hστ, _⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  have h1 : IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S (l.κ S w)) :=
    half_smul _ (half_mul_left _ (half_mul_right (half_adj hh) _))
  rw [Lnk.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj] at h1
  have h2 := half_mul_left (rat σ : Mx D L.rank L.rank) h1
  rwa [← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul] at h2

theorem kappa_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  intro D ψ hψ L S ζ ζ' h l Λ Ξ hv w hw
  refine ⟨?_, fun e he hh => ?_⟩
  · have e2 : (2 • l.κ S w : WO L S) = l.κ S (2 • w) := by rw [two_nsmul, two_nsmul, kap_add h l]
    rw [e2]
    exact kap_heis ψ hψ h l S Ξ _ (hv.1 w hw)
  · exact kap_heis ψ hψ h l S Ξ w (hv.2 (cA D e) (split_conj he) w hw (kap_half h l S hh))

end GlobalTheory.KapVac
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def actUni (B : BesL D σ) : Subgroup (GA D B.V) where
  carrier := {g | ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt B.V a⁻¹ ⬝ (xLast B.d (vecB B.o B.ζ) ⬝ u.1) ⬝ (u⁻¹).1 = xLast B.d (vecB B.o B.ζ) ⬝ (u⁻¹).1 := by
      rw [← ha, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
    rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem mem_actUni_iff (B : BesL D σ) (g : GA D B.V) : g ∈ actUni B ↔ ∃ u ∈ UX D σ, ∃ v : Fin σ → AE D,
    mt B.V g ⬝ B.d.jX = B.d.jX ⬝ u.1 ∧
      mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) + B.d.jX *ᵥ v :=
  FB.snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V g)

theorem flagN_le_actUni (B : BesL D σ) : flagN B.d ≤ actUni B := by
  intro n hn
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn
  rw [mem_actUni_iff]
  have hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]
  refine ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem embA_mem_actUni (B : BesL D σ) (h : GA D B.A) : embA B.d B.o h ∈ actUni B := by
  rw [mem_actUni_iff]
  refine ⟨1, one_mem _, 0, ?_, ?_⟩
  · rw [embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]
  · rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec,
      vecB, FB.ratV_mulVec_rat]
    change B.d.j0 *ᵥ (mt B.V₀ (B.o.emb (h, 1)) *ᵥ (B.o.jB *ᵥ ratV B.ζ)) = B.d.j0 *ᵥ (B.o.jB *ᵥ ratV B.ζ)
    congr 1
    rw [Matrix.mulVec_mulVec, B.o.emb_jB, mt_one, Matrix.mul_one]

theorem besGrp_le_actUni (B : BesL D σ) : besGrp B.d B.o ≤ actUni B :=
  sup_le (flagN_le_actUni B) (by rintro _ ⟨h, rfl⟩; exact embA_mem_actUni B h)

theorem mem_besGrp_of_actUni (B : BesL D σ) (g : GA D B.V) (hg : g ∈ actUni B) : g ∈ besGrp B.d B.o := by
  obtain ⟨u, hu, v, hX, h0⟩ := (mem_actUni_iff B g).1 hg
  have hst : B.d.levi u⁻¹ * g ∈ stabX B.d := by
    show mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.jX = B.d.jX
    rw [mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, k, hk⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.2.1 _).1 hst
  obtain ⟨b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.1 n).1 hn
  have hp : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.j0 = mt B.V₀ k := by
    rw [hk, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_unipotentMixed, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_unipotentSkew,
      Matrix.mul_assoc _ B.d.pY, B.d.pY_nC, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc _ B.d.pY, B.d.wittDecomp_projY_anisotropicEmbedding,
      Matrix.sub_mul, Matrix.mul_assoc, B.d.p0_j0, Matrix.mul_one, Matrix.mul_assoc _ B.d.pY, B.d.pY_j0,
      Matrix.mul_zero, sub_zero]
  have hz : mt B.V₀ k *ᵥ ratV (B.o.iB *ᵥ B.ζ) = ratV (B.o.iB *ᵥ B.ζ) := by
    have e1 : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) = B.d.p0 ⬝ mt B.V g := by
      rw [mt_mul, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_levi]
    rw [← hp, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change B.d.p0 *ᵥ (mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) = _
    rw [h0, Matrix.mulVec_add, Matrix.mulVec_mulVec, B.d.p0_j0, Matrix.one_mulVec, Matrix.mulVec_mulVec, B.d.p0_jX,
      Matrix.zero_mulVec, add_zero]
    rfl
  obtain ⟨h, rfl⟩ := FB.fix_lineVec_emb D B.V₀ B.A B.L B.o B.ζ B.line k hz
  have hg' : g = (B.d.levi u * (B.d.nB b * B.d.nC c)) * embA B.d B.o h := by
    rw [embA_apply, mul_assoc, ← hk, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (((flag_jacobi_structure D B.V B.V₀ σ B.d).1 _).2 ⟨u, hu, b, c, rfl⟩))
    (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem besGrp_act_xLast : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), xLast B.d (vecB B.o B.ζ) ⬝ a = xLast B.d (vecB B.o B.ζ) ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  intro D σ B
  obtain ⟨⟨P, hP, hPx⟩, hx⟩ := xLast_rat_leftInv D σ B
  refine ⟨fun g => ⟨fun hg => besGrp_le_actUni B hg, fun hg => mem_besGrp_of_actUni B g hg⟩, ?_, ?_⟩
  · intro a a' h
    rw [← Matrix.one_mul a, ← Matrix.one_mul a', ← hPx, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro g hg u hgu
    have hinv : mt B.V g⁻¹ ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ (u.1⁻¹).1 := by
      have h1 : mt B.V g⁻¹ ⬝ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) ⬝ (u.1⁻¹).1 = xLast B.d (vecB B.o B.ζ) ⬝ (u.1⁻¹).1 := by
        rw [← hgu, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · have e : u.1.1 = P ⬝ mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) := by
        rw [Matrix.mul_assoc, hgu, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 hg)) hx
    · have e : (u.1⁻¹).1 = P ⬝ mt B.V g⁻¹ ⬝ xLast B.d (vecB B.o B.ζ) := by
        rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 (inv_mem hg))) hx

end GlobalTheory.Asc.FBL

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowEx



theorem exKey_of (h1 : GridEx) (h2 : IsEx) (h3 : NFAll) (cG : CarryG) (cW : CarryW) (cS : CarryS)
    (t1 : TrEasy) (t2 : TrPhase) (t3 : TrJet) (t4 : TrBot) : ExKey := by
  classical
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_right (le_of_max_le_right hC))
  refine ⟨max x1 (max x2 x3), fun s he hx P f κ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_right (le_of_max_le_right hx)
  by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
      (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
      (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks X.toD7.what₂.LL)
      (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ
  swap
  · exact ⟨∅, by simp, fun X f' a b large₂ c Γ _ _ Pl0 T A Ks _ _ _ R F d e g i _ =>
      absurd ⟨X, f', a, b, large₂, c, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, d, e, g, i⟩ H⟩
  obtain ⟨X0, f0, a0, b0, Lg0, rfl, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, d0, e0, g0, i0⟩ := H
  obtain ⟨G0, W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 g0
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G0 W0 hW0 S0
  obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
  refine ⟨Finset.univ.image fun i => ((b i : N) : ℂ), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
  intro X f' a b' large₂ hs Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i hz
  have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
  have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
  have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
    rintro P _ rfl k k' h x hx
    obtain rfl := eq_of_heq h
    exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
  have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
    obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
    exact ⟨t0, h⟩
  choose ι hι using hι
  have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
  have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
    rw [d0.core.lev.xi_base]
    have := (hι A.μ0).1
    rw [d.core.lev.xi_base] at this
    exact eq_of_heq (this.symm.trans (one _ _ hpre)))
  have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
    ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX, d.betaX⟩
  obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G0
  obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G0 G hG W0
  obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G0 G hG W0 W hWA S.toGridChoice
  have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
  have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
  rw [hs] at h2'
  obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
  refine ⟨_, hIs', rfl, ?_⟩
  obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
  have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root, t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase,
    t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios, t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
  subst hS2
  refine hAll'.numbersIn.mono ?_
  rintro _ ⟨y, rfl⟩

  rw [← b.sum_repr y, map_sum]
  refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hz _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

end GlobalTheory.RowEx
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem exField_of_keyFin_exKey : KeyFin → ExKey → ExField := by
  classical
  intro h2 h1
  obtain ⟨c, h1⟩ := h1
  refine ⟨c, fun ε CF hC => ?_⟩
  obtain ⟨x, h1⟩ := h1 ε CF hC
  refine ⟨x, fun s e hx P f Ξ hΞ => ?_⟩
  obtain ⟨𝒦, hK, H⟩ := h2 P Ξ hΞ
  choose S hS HS using h1 s e hx P f
  refine ⟨hK.toFinset.biUnion S, fun z hz => ?_, fun Y f' hP hf large₂ hs Γ _ _ Pl0 U A Ks _ _ _ R F st hC ho hc hz => ?_⟩
  · obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ z hz
  · obtain ⟨κ, hκ, hk⟩ := H Y U R.toLevCh A.μ0 hP st.core.lev hc
    exact HS κ Y f' hP hf large₂ hs Γ Pl0 U A Ks R F st hC ho hk fun z hz' =>
      hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, hz'⟩)

end GlobalTheory.RowEx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEx

theorem keyFin_holds : KeyFin := by
  classical
  intro P Ξ hΞ
  let U : Key P := {p | p.1 ∈ Ξ ∧ {w | ¬ p.1.UnrAt w}.Finite ∧ ∀ w ∈ p.2, ¬ p.1.UnrAt w}
  have hU : U.Finite := by
    refine (hΞ.biUnion (t := fun ξ => {p ∈ U | p.1 = ξ}) fun ξ _ => ?_).subset fun p hp => Set.mem_biUnion hp.1 ⟨hp, rfl⟩
    by_cases hf : {w | ¬ ξ.UnrAt w}.Finite
    · refine ((hf.toFinset.powerset.finite_toSet).image fun Q => (ξ, Q)).subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact ⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun w hw => hf.mem_toFinset.2 (h.2.2 w hw)), rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact hf h.2.1
  refine ⟨{κ | κ ⊆ U}, hU.finite_subsets, ?_⟩
  rintro X T L μ₀ rfl hL h
  refine ⟨keyOf L, ?_, HEq.rfl⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, h1, h2⟩ := h t
  refine ⟨by rw [← eq_of_heq h2] at h1; exact h1, ?_, fun w hw => (hL.Q_ram t w).2 (Or.inl hw)⟩
  refine ((L.Q t).finite_toSet.union ((L.Q t).finite_toSet.image Formalism.DivisionValues.conjPl)).subset fun w hw => ?_
  rcases (hL.Q_ram t w).1 hw with h | ⟨w', h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨w', h, (GlobalTheory.GoodPrimes.isConjPl_iff.1 h').symm⟩

end GlobalTheory.RowEx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc


theorem _root_.GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_orthogonal_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, thPair μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1 := by
  first | exact @GlobalTheory.MatCoefLevel.matCoef_level | exact GlobalTheory.MatCoefLevel.matCoef_level | (intros; apply GlobalTheory.MatCoefLevel.matCoef_level <;> assumption)
end
