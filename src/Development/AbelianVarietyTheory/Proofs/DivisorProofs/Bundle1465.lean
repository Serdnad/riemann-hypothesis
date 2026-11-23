module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle207
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle234
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaSatake

open GlobalTheory.ThetaPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev cw (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  conjSrc (IsCMField.complexConj E).toRingEquiv w

theorem theta_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (cFin E) (locGL E n (cw w) g) =
      locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cw v)) (locGL E n (cw w) g))) := fun v =>
    map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
      (Matrix.GeneralLinearGroup.map (cFin E) (locGL E n (cw w) g))
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v)
        (locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one, map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key2 v)

theorem conjLoc_surj (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem absNorm_cw (w : HeightOneSpectrum (𝓞 E)) : Ideal.absNorm (cw w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
  simp only [Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv

def cloc (w : HeightOneSpectrum (𝓞 E)) : (cw w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surj w⟩

theorem thetaGL_conj (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      PhiU n _ * GlobalTheory.LFun.ConjPlace.invT (cloc w) n g * (PhiU n _)⁻¹ := by
  have e1 : GlobalTheory.LFun.ConjPlace.invT (cloc w) n g =
      GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
  rw [e1]
  rfl

theorem phiU_mem {K : Type} [Field K] (O : Subring K) (n : ℕ) : PhiU n K ∈ Formalism.UG.GLint (Fin n) O := by
  have h : ∀ i j : Fin n, GlobalTheory.Tw.Phi n K i j ∈ O := fun i j => by
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    split_ifs
    · exact pow_mem (neg_mem (one_mem O)) _
    · exact zero_mem O
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, fun i j => h j i⟩

theorem hasSatGL_of_invT {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}
    (c : w.adicCompletion E ≃+* w'.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : Formalism.UG.qV E w' = Formalism.UG.qV E w)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w'.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (GlobalTheory.LFun.ConjPlace.invT c a g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w' ρ' (B.map (·⁻¹)) := by
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) c (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp (GlobalTheory.LFun.ConjPlace.invT c a).symm.toMonoidHom) g y) =
      ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ ((GlobalTheory.LFun.ConjPlace.invT c a).symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w' ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c hc hq hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

theorem hasSat_thetaSub {a : ℕ} (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (C : Multiset ℂˣ)
    (h : (CG.mk π).HasSat (cw w) C) : (CG.mk (thetaSub π)).HasSat w (C.map (·⁻¹)) := by
  rw [CG.hasSat_mk] at h ⊢
  let ρ' := (thetaSub π).locRep w
  let T₀ : π.V ≃ₗ[ℂ] (thetaSub π).V := (pull E a).submoduleMap π.V
  have h0 : ∀ g x, ρ' (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) (T₀ x) =
      T₀ (π.locRep (cw w) g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq, ← theta_locGL]
    exact Subtype.ext (pull_act (.fin (locGL E a (cw w) g)) x.1).symm
  let k := PhiU a (w.adicCompletion E)
  let S : (thetaSub π).V ≃ₗ[ℂ] (thetaSub π).V :=
    LinearEquiv.ofLinear (ρ' k⁻¹) (ρ' k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine hasSatGL_of_invT (cloc w) (conjLoc_spec _ w).2.2 (absNorm_cw w).symm (T₀.trans S) (fun g x => ?_) h
  change ρ' _ (ρ' k⁻¹ (T₀ x)) = ρ' k⁻¹ (T₀ _)
  rw [← h0, thetaGL_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  dsimp only [k]
  group

end GlobalTheory.ThetaSatake
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ), L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) = (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  first | exact @GlobalTheory.FlagPush.alternating_of_adjacent_swap | exact GlobalTheory.FlagPush.alternating_of_adjacent_swap | (intros; apply GlobalTheory.FlagPush.alternating_of_adjacent_swap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.parabolicMatrixFamily_diag_isUnit : ∀ (ι : Type) (m : ι → ℕ) (K : Type) [Field K] (O : Subring K) (S : Mat m K), Par m O S → ∀ x : Root m, S x.1 x.2 x.2 ≠ 0 ∧ (S x.1 x.2 x.2)⁻¹ ∈ O ∧ S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ ∧ ∀ T : Mat m K, Par m ⊤ T → (S * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * T x.1 x.2 x.2 := by
  first | exact @GlobalTheory.FlagPush.diag_of_par | exact GlobalTheory.FlagPush.diag_of_par | (intros; apply GlobalTheory.FlagPush.diag_of_par <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  first | exact @GlobalTheory.GoodTop.contDiffAt_holoChart | exact GlobalTheory.GoodTop.contDiffAt_holoChart | (intros; apply GlobalTheory.GoodTop.contDiffAt_holoChart <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodTop

theorem gram_smooth_isUnit_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  intro F _ σ X m E O H hH e he y hyO hye A hA
  refine ⟨fun a b => ?_, ?_⟩
  · obtain ⟨hre, him⟩ := hH.smooth y hyO A hA () a b
    have h1 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).re) (e y) := contDiffAt_holoChart he hye hre
    have h2 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).im) (e y) := contDiffAt_holoChart he hye him
    have h3 : ContDiffAt ℝ ∞ (fun v => ((H A (e.symm v) () a b).re : ℂ) + ((H A (e.symm v) () a b).im : ℂ) * Complex.I)
        (e y) :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h2).mul contDiffAt_const)
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => (Complex.re_add_im _).symm)
  · rw [e.left_inv hye]
    exact isUnit_iff_ne_zero.mpr (hH.posDef y hyO A hA ()).det_pos.ne'

end GlobalTheory.GoodTop
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  first | exact @GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos | exact GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos | (intros; apply GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem l2ExtensionLogCanonical' : GlobalTheory.Published.L2ExtensionLogCanonical := by
  intro n hn Y _ _ _ _ _ _ ι La _ A hH E L s hs hS hjac hle δ hδ hcurv f
  obtain ⟨Λ, τ, z, β, hdata⟩ := GlobalTheory.T.exists_etale_frame_off_finite_zeroSet n Y ι La A hn hH E L s hs hS
  exact GlobalTheory.T.l2_extension_etale_coordinates_finite_zeros n Y ι La A hn E L s hs hS hjac hle δ hδ hcurv Λ τ z β hdata f

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ChernDegreeBaseChange

theorem exists_baseChange {F E : Type} [Field F] [Field E] (ρ : F →+* E) (Y : Var F) :
    ∃ (Y' : Var E) (r : Y'.X ⟶ Y.X), Y'.dim = Y.dim ∧ IsPullback r Y'.str Y.str (spMap ρ) := by
  have H := IsPullback.of_hasPullback Y.str (spMap ρ)
  generalize Limits.pullback.fst Y.str (spMap ρ) = r at H
  generalize Limits.pullback.snd Y.str (spMap ρ) = q at H
  have hs : SmoothOfRelativeDimension Y.dim q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange Y.dim
    MorphismProperty.of_isPullback H Y.smooth_str
  have hg : GeometricallyIntegral q :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H Y.geometricallyIntegral_str
  have hc : GeometricallyConnected q :=
    ⟨fun _ _ y _ fst snd h =>
      have := GeometricallyIntegral.geometrically_isIntegral (f := q) y fst snd h
      inferInstance⟩
  obtain ⟨Y', e, hd, he⟩ := Var.exists_iso q Y.dim (ProjSpace.isProjOver_of_isPullback_spMap ρ H Y.isProjOver)
  refine ⟨Y', e.inv ≫ r, hd, ?_⟩
  refine H.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simpa using he.symm
  · simp
  · simp

theorem chernDegree_of_complex (h : GlobalTheory.Published.ChernDegreeComplex) : GlobalTheory.Published.ChernDegree := by
  intro F _ Y σ Δ L r hr φ hφ
  obtain ⟨Y', π, hd, H⟩ := exists_baseChange σ Y
  have := CxPts.compactSpace (RingHom.id ℂ) Y'.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (RingHom.id ℂ) Y'.isProjOver
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts Y'.str (RingHom.id ℂ) → CxPts Y.str σ, (∀ z, (m z).1 = z.1 ≫ π) ∧
      Function.Bijective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, bijective_bcMap H _⟩
  let Φ : CxPts Y'.str (RingHom.id ℂ) ≃ₜ CxPts Y.str σ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hb) (continuous_of_comp hm)
  have hΦ : ∀ z, (Φ z).1 = z.1 ≫ π := hm
  have hL' := LB.isLB_pull hr.isLB π
  obtain ⟨s, hs⟩ := exists_isRatSec hL'
  have hp := presents_divOfRatSec hL' hs
  obtain ⟨h₁, h₂⟩ := h Y' _ _ s hp (ChernTransfer.pullW hΦ φ) (ChernTransfer.isCInf_pullW hΦ hφ)
  have hi : Y'.inter (fun _ => divOfRatSec hL' hs) = Y.inter fun _ => Δ := by
    letI := σ.toAlgebra
    rw [Var.inter_eq_of_toPic_eq (fun _ => hL') (fun _ => hp.toPic_eq),
      Var.inter_eq_of_toPic_eq (fun _ => hr.isLB) (fun _ => hr.toPic_eq), hd]
    exact FieldChangeInter.interNum_pull (f := Y.str) (f' := Y'.str) H (L := fun _ => L) fun _ => hr.isLB
  have hsm : SmoothOfRelativeDimension Y.dim Y'.str := hd ▸ Y'.smooth_str
  have e (ε) := ChernTransfer.chernPart_pullW hΦ (AnRead.all _ _ Y.dim) (AnRead.all _ _ Y.dim) hφ ε
  rw [hi] at h₂
  rw [hd] at h₁ h₂
  simp only [Weight.ChernIntegrableOn, Weight.chernInt, integrableOn_univ, Measure.restrict_univ, e,
    integral_map_equiv, integrable_map_equiv] at h₁ h₂ ⊢
  exact ⟨h₁, h₂⟩

end GlobalTheory.ChernDegreeBaseChange
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nsq_pow_addFn_const {σ : k →+* ℂ} {B : LB X} (φ : Weight p σ B) (c : ℝ) (m : ℕ)
    (s : (lbPow B m).ι → CxPts p σ → ℂ) (y : CxPts p σ) :
    ((φ.addFn fun _ => c).pow m).nsq s y = (φ.pow m).nsq s y * Real.exp (-(m * c)) := by
  simp only [Weight.nsq]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Weight.addFn]
  push_cast
  ring

theorem isometric_pull_id (L : HermLB p) : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
    (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
  · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
      (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
    rw [Category.comp_id]
  · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))

theorem recursion_pull_id [IsLocallyNoetherian X] {D : ℕ} (hX : IsArithVar p D) (hD : 1 ≤ D) {L : HermLB p} {h : X → ℝ}
    (H : L.IsArithHeight h) (m : ℕ) {q : X ⟶ Sp k} (hq : 𝟙 X ≫ p = q)
    (r : ((L.pull (𝟙 X) hq).pow m).B.ι → X.functionFieldˣ) (hr : IsRatSec ((L.pull (𝟙 X) hq).pow m).B r) :
    (L.pull (𝟙 X) hq).ArchIntegrable ((L.pull (𝟙 X) hq).pow m) D hr ∧
      (m : ℝ) * h (genericPoint X) = ∑ᶠ z, ((((L.pull (𝟙 X) hq).pow m).div hr).mult z : ℝ) * h z -
        (L.pull (𝟙 X) hq).archInt ((L.pull (𝟙 X) hq).pow m) D hr := by
  subst hq
  have e := H.recursion X (𝟙 X) hX.charZero D hD hX.dim_eq m r hr
  simpa using e

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem height_add_mul_gdeg_nonneg_of_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (m : ℕ) (u : ℝ), 0 < m → 0 ≤ u → (∃ s ∈ ((C.shift (fun _ => u) fun _ => rfl).pow m).smallSec, s ≠ 0) → 0 ≤ h (genericPoint X) + u * gdeg C D := by
  intro HC k _ X _ p D hX hD C h hSP H hnn m u hm hu hex
  obtain ⟨s, hs, hs0⟩ := hex
  have := hX.isLocallyNoetherian
  have := hX.finite_emb
  have hiso := isometric_pull_id C
  set C' := C.pull (𝟙 X) (Category.id_comp p) with hC'
  let s' : (C.pow m).B.Sec := s
  have hg : genericPoint X ∈ nonzeroLocus s' := (sec_ne_zero_iff s').1 hs0
  obtain ⟨r', hr', hdiv, hlog⟩ := (hiso.pow m).exists_isRatSec (isRatSec_ratOfSec s' hg)
  obtain ⟨hI, hrec⟩ := recursion_pull_id hX hD H m (Category.id_comp p) r' hr'

  have hsum : 0 ≤ ∑ᶠ z, (((C'.pow m).div hr').mult z : ℝ) * h z := by
    refine finsum_nonneg fun z => ?_
    rw [hdiv]
    by_cases hz : ((C.pow m).div (isRatSec_ratOfSec s' hg)).mult z = 0
    · simp [hz]
    · exact mul_nonneg (by exact_mod_cast mult_divOfSec_nonneg z)
        (hnn z fun e => CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hz))

  have hneg (σ : k →+* ℂ) : (C.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (C.cInf σ) (hSP σ)
  have hfin (σ : k →+* ℂ) : IsFiniteMeasure ((C.φ σ).chernPart D 1) := by
    have hu1 : ∀ σ (y : CxPts p σ), CInfAt (fun _ : CxPts p σ => (1 : ℝ)) y := fun σ y => cInfAt_const 1 y
    have hc1 : ∀ σ σ' : k →+* ℂ, (Weight.ofFun (fun _ : CxPts p σ => (1 : ℝ))).IsConj
        (Weight.ofFun (fun _ : CxPts p σ' => (1 : ℝ))) := fun _ _ _ _ _ _ _ => rfl
    obtain ⟨Φ, hΦ⟩ := ((HC.arExists k X p D hX).2 (Option Unit)
      (fun o : Option Unit => o.elim (ArInt.fnB (fun σ (_ : CxPts p σ) => (1 : ℝ)) hu1 hc1) fun _ => C)).1
    have h1 := ((HC.arMix.fnB HC.arExists hX hΦ (Pi.single () 1)).1 σ).1
    rw [(isometric_comb_single (fun _ : Unit => C) ()).chernPart_eq σ D 1] at h1
    exact (integrable_const_iff.1 (integrableOn_univ.1 h1)).resolve_left one_ne_zero

  have hpt (σ : k →+* ℂ) : ∀ y ∈ offSupp p σ ((C'.pow m).div hr'),
      logNorm ((C'.pow m).φ σ) r' y ≤ m * u := by
    intro y hy
    rw [hdiv] at hy
    rw [hlog σ hy]
    have hy' : y ∈ ptsIn p σ (nonzeroLocus s') := by
      have := hy
      rwa [offSupp_divOfSec] at this
    rw [logNorm_ratOfSec _ hy']
    have h1 := hs σ y
    change (((C.φ σ).addFn fun _ => 2 * u).pow m).nsq (secVal p σ s') y ≤ 1 at h1
    rw [nsq_pow_addFn_const] at h1
    have h2 : ((C.φ σ).pow m).nsq (secVal p σ s') y ≤ Real.exp (m * (2 * u)) := by
      have := Real.exp_pos (m * (2 * u))
      rw [Real.exp_neg] at h1
      rwa [mul_inv_le_iff₀ (Real.exp_pos _), one_mul] at h1
    have h0 := ((C.φ σ).pow m).nsq_nonneg (secVal p σ s') y
    have h3 : Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) ≤ m * (2 * u) := by
      rcases h0.eq_or_lt with e | e
      · rw [← e, Real.log_zero]; positivity
      · exact (Real.log_le_iff_le_exp e).2 h2
    change Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) / 2 ≤ _
    linarith
  have hA : C'.archInt (C'.pow m) D hr' ≤ m * u * gdeg C D := by
    rw [HermLB.archInt, gdeg, chInt, mul_finsum]
    refine finsum_le_finsum' (Set.toFinite _) (Set.toFinite _) fun σ => ?_
    have hS : MeasurableSet (offSupp p σ ((C'.pow m).div hr')) := (isOpen_offSupp _).measurableSet
    have hint := hI σ
    rw [← hiso.chernIntegrableOn_eq] at hint
    rw [← hiso.chernInt_eq]
    haveI := hfin σ
    simp only [Weight.chernInt, hneg σ, Measure.restrict_zero, integral_zero_measure, sub_zero,
      setIntegral_const, smul_eq_mul, mul_one]
    calc ∫ y in offSupp p σ ((C'.pow m).div hr'), logNorm ((C'.pow m).φ σ) r' y ∂(C.φ σ).chernPart D 1
        ≤ ∫ y in offSupp p σ ((C'.pow m).div hr'), (m * u : ℝ) ∂(C.φ σ).chernPart D 1 :=
          setIntegral_mono_on hint.1 (integrable_const _).integrableOn hS (hpt σ)
      _ = ((C.φ σ).chernPart D 1).real (offSupp p σ ((C'.pow m).div hr')) * (m * u) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ((C.φ σ).chernPart D 1).real Set.univ * (m * u) :=
          mul_le_mul_of_nonneg_right (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
            (by positivity)
      _ = m * u * ((C.φ σ).chernPart D 1).real Set.univ := by ring
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have : 0 ≤ (m : ℝ) * (h (genericPoint X) + u * gdeg C D) := by
    have := hrec
    nlinarith
  exact nonneg_of_mul_nonneg_right this hmpos

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenNef

theorem isNef_of_gen_small : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  intro _ k _ X _ p D hX M n s hsp hsm hs
  have hcov : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) = ⊤ :=
    top_le_iff.1 fun x _ =>
      have ⟨i, hi⟩ := hs x
      Opens.mem_iSup.2 ⟨i, hi⟩
  exact GlobalTheory.VolBr.Model.isNef_of_small hX M hsp
    (GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX M (GlobalTheory.isGenerated_of_finite s hcov))
    fun x => have ⟨i, hi⟩ := hs x; ⟨s i, hsm i, hi⟩

end GlobalTheory.GenNef

end
end
