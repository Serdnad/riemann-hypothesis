module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSource
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle090
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceFormRealCoordinatesIntegralGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvAdelic

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec, mt_unitary, form]

theorem unitary_of_form (S : HSp D) (M : Mx D S.rank S.rank)
    (h : ∀ x y, form S (M *ᵥ x) (M *ᵥ y) = form S x y) : adj M * (gA S * M) = gA S := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  have e : (fun k => cA D ((Pi.single i 1 : VA S) k)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [form_mulVec, form, e] at this
  simpa using this

theorem form_vecX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) :
    form S (vecX d a) (vecX d a) = 0 := by
  rw [vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

@[reducible] def starRingA (D : D7) : StarRing (AE D) where
  star := cA D
  star_involutive := cA_cA
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add (cA D)

@[reducible] def invTwo (D : D7) : Invertible (2 : AE D) where
  invOf := half D
  invOf_mul_self := by rw [mul_two, half_add_half]
  mul_invOf_self := by rw [two_mul, half_add_half]

theorem form_transv (S : HSp D) (w v : VA S) (hw : form S w w = 0) (hv : form S w v = 0) (x y : VA S) :
    form S (transv S w v x) (transv S w v y) = form S x y := by
  letI := starRingA D
  letI := invTwo D
  exact (GlobalTheory.eichlerTransvection_unitary_inverse_conj (AE D) (Fin S.rank) (gA S) (adj_gA S) (form S)
    (fun _ _ => rfl) (transv S) (fun _ _ _ => rfl)).1 w v hw hv x y

def transvLin (S : HSp D) (w v : VA S) : VA S →ₗ[AE D] VA S where
  toFun := transv S w v
  map_add' x y := by
    funext i
    simp only [transv, form, Matrix.mulVec_add, dotProduct_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' s x := by
    funext i
    simp only [transv, form, Matrix.mulVec_smul, dotProduct_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

theorem toMatrix_transvLin (S : HSp D) (w v y : VA S) :
    LinearMap.toMatrix' (transvLin S w v) *ᵥ y = transv S w v y := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem act_transv (S : HSp D) (g : GA D S) (w v y : VA S) :
    act S g (transv S w v y) = transv S (act S g w) (act S g v) (act S g y) := by
  rw [transv, transv, form_act, form_act, form_act]
  simp only [act, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem act_mul (S : HSp D) (g h : GA D S) (y : VA S) : act S (g * h) y = act S g (act S h y) := by
  rw [act, act, act, mt_mul, Matrix.mulVec_mulVec]

theorem transv_unitary_conj :
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D ∧ GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvConj D := by
  intro D
  refine ⟨fun S S₀ ρ d a v hv => ?_, fun S S₀ ρ d a v _ u g hu y => ?_⟩
  · refine ⟨ofMat S (LinearMap.toMatrix' (transvLin S (vecX d a) v)) (unitary_of_form S _ fun x y => ?_), fun y => ?_⟩
    · rw [toMatrix_transvLin, toMatrix_transvLin, form_transv S _ _ (form_vecX d a) hv]
    · rw [act, mt_ofMat, toMatrix_transvLin]
  · rw [act_mul, act_mul, hu, act_transv, ← act_mul S g g⁻¹, mul_inv_cancel]
    congr 1
    rw [act, mt_one, Matrix.one_mulVec]

end GlobalTheory.TransvAdelic

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.exists_doubling_chart_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ (c : w.adicCompletion E →+* w.adicCompletion E) (e : GLoc σ J v ≃* GU c n), IsInertChart σ J L h c e → ∃ f : GLoc σ Q v ≃* GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n, (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD c n) ∧ (∀ y, f (ioH _ σ hQ (y, 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n) ∧ ∀ (p : siegelH (Fv F v) σ Q) (hp : f p ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n ⟨f p, hp⟩ = Units.map (toCompl h).toMonoidHom (aH _ σ Q p) := by
  first | exact @GlobalTheory.DblInert.exists_dblChart | exact GlobalTheory.DblInert.exists_dblChart | (intros; apply GlobalTheory.DblInert.exists_dblChart <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.Doubling.AbsSplit

theorem norm_eq_zpow {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a : Fv F v} (ha : a ≠ 0) :
    ‖a‖ = (qV F v : ℝ) ^ (-ordL a) := by
  have h0 : Valued.v a ≠ 0 := (map_ne_zero _).2 ha
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0, ordL, dite_eq_right h0, neg_neg]
  simp [qV, WithZero.toAdd_unzero_eq_log h0]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem absEv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV E w : ℝ) ^ (-(ordL (toCompl h x.1) + ordL (toCompl h' x.1))) := by
  intro F E _ _ _ _ _ σ hE v w h w' h' hne x
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq hE hne h h'
  obtain ⟨τ', hτ', -⟩ := existsUnique_splitPrime_eq hE hne.symm h' h
  obtain rfl : τ' = τ.comp σ := (eq_or_eq_comp_conj hE τ τ').resolve_left fun e => hne (hτ.symm.trans (e ▸ hτ'))
  have hN : Algebra.norm (Fv F v) x.1 = splitProj τ x.1 * splitProj (τ.comp σ) x.1 := by
    have := congrArg (splitProj τ) (algebraMap_norm_eq hE x.1)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  have hq : qV E w = qV F v := hτ ▸ GlobalTheory.LFun.SplitTie.qV_splitPrime τ
  have e1 : ordL (toCompl h x.1) = ordL (splitProj τ x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, GlobalTheory.LFun.ConjPlace.valued_complMap hE h hτ])
  have e2 : ordL (toCompl h' x.1) = ordL (splitProj (τ.comp σ) x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', GlobalTheory.LFun.ConjPlace.valued_complMap hE h' hτ'])
  have hq0 : (qV F v : ℝ) ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    unfold qV
    exact_mod_cast (by omega)
  rw [absEv_apply, coe_nnnorm, hN, norm_mul, hq, e1, e2, neg_add, zpow_add₀ hq0,
    norm_eq_zpow v (x.isUnit.map (splitProj τ)).ne_zero, norm_eq_zpow v (x.isUnit.map (splitProj (τ.comp σ))).ne_zero]

end GlobalTheory.Doubling.AbsSplit
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatMap_laws_factor_fourierJacobi_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.PartRed.flRow_factor | exact GlobalTheory.PartRed.flRow_factor | (intros; apply GlobalTheory.PartRed.flRow_factor <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem mtor_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ (-e) : GL (A ⊕ D) k) = (mtor ϖ e)⁻¹ := by
  unfold mtor torusElt
  rw [← map_inv]
  congr 1
  funext i
  rcases i with i | i <;> simp [_root_.zpow_neg]

theorem sum_eq_genVal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ) (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → ∀ (s : Finset D) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ), IsReps (mtor ϖ (-indic s)) R d → ∑ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * mtor ϖ (-indic s)) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b ⟨datum ξ⁻¹, hΦ⟩ x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ ξ μS μT hξ hμ W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb s R d hR
  set g : GL (A ⊕ D) k := mtor ϖ (indic s) with hg
  have hginv : (mtor ϖ (-indic s) : GL (A ⊕ D) k) = g⁻¹ := mtor_neg ϖ (indic s)
  rw [hginv] at hR ⊢
  set Φ : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦdef

  have h1 : ∀ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = b Φ (ρ g x) := by
    intro j hj
    obtain ⟨hjJ, hdj⟩ := hR.1 j hj
    have hjiJ : j⁻¹ ∈ parahoric k A D := inv_mem hjJ
    have hne := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j⁻¹ hjiJ).1
    have hprod := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j hjJ).2 (d j) (Units.mk0 _ hne) hdj rfl
    have hx1 : ρ j⁻¹ x = (ξ (Units.mk0 _ hne) : ℂ) • x := hx.1 j⁻¹ hjiJ (Units.mk0 _ hne) rfl
    have he := hb (j * g⁻¹) 1 Φ (ρ (g * j⁻¹) x)
    have hone : (j * g⁻¹) * (g * j⁻¹) = 1 := by group
    rw [← Module.End.mul_apply, ← map_mul, hone, map_one, Module.End.one_apply, map_one, Module.End.one_apply,
      map_mul, Module.End.mul_apply, hx1, map_smul, map_smul] at he
    rw [show (⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) = ⟨omTwo μS μT (j * g⁻¹) 1 Φ, hW _ _ Φ Φ.2⟩ from rfl,
      he, smul_smul, hprod, one_smul]

  have htame : IsTame ξ⁻¹ := fun y hy => by simp [hξ y hy]
  have hunr : IsUnram (μT⁻¹ * ξ) := fun y hy => by
    have := hμ y hy
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢
    rw [← inv_inv (ξ y), ← mul_inv, this, inv_one]
  have h2 : ∀ j ∈ parahoric k A D, ∀ dd : kˣ, (dd : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      ∀ z, b Φ (ρ j z) = (ξ dd : ℂ) • b Φ z := by
    intro j hj dd hdd z
    have hom : omTwo μS μT j (1 : GL (A ⊕ D') k) (datum ξ⁻¹) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • datum ξ⁻¹ := by
      have := GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D D' ξ⁻¹ (μT⁻¹ * ξ) htame hunr j hj dd hdd
      rw [show μT⁻¹ * ξ * ξ⁻¹ = μT⁻¹ by rw [mul_assoc, mul_inv_cancel, mul_one]] at this
      unfold omTwo
      rw [this]
      funext y
      simp
    have he := hb j 1 Φ z
    have hsub : (⟨omTwo μS μT j 1 Φ, hW j 1 Φ Φ.2⟩ : W) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • Φ := Subtype.ext hom
    rw [hsub, map_smul, LinearMap.smul_apply, map_one, Module.End.one_apply] at he
    rw [← he, smul_smul]
    simp

  obtain ⟨R'', d'', hR''⟩ := (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k A D).1 g
  have hcard := (GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq k A D g R'' R d'' d hR'' hR).1
  have hT := hx.2.2 s R'' d'' hR''
  have hsum2 : genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b Φ x = R''.card • b Φ (ρ g x) := by

    rw [← map_smul, hT, map_sum, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hjJ, hdj⟩ := hR''.1 j hj
    rw [map_smul, show (mtor ϖ (indic s) : GL (A ⊕ D) k) = g from rfl, map_mul, Module.End.mul_apply,
      h2 j hjJ (d'' j) hdj, smul_smul]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const, hsum2, hcard]

end GlobalTheory.ParHeckeTransfer
end
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem continuous_lin_mvZ {T : Type} [TopologicalSpace T] (g : T → ι → Matrix (Fin a) (Fin a) ℂ)
    (hg : Continuous g) (h : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b) :
    ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, Continuous fun x => Λ (mvZ (g x) h P) := by
  induction P using MvPolynomial.induction_on with
  | C c => intro Λ; simp only [mvZ, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro Λ; simp only [map_add (f := _)]; exact (hp Λ).add (hq Λ)
  | mul_X p v hp =>
    intro Λ
    have key : ∀ x, Λ (mvZ (g x) h (p * X v)) = ∑ i, ∑ j, (h v.1 i v.2.1 * g x v.1 v.2.2 j) *
        (Λ ∘ₗ LinearMap.mulRight ℂ (X (v.1, i, j))) (mvZ (g x) h p) := by
      intro x
      rw [map_mul]
      conv_lhs => rw [show mvZ (g x) h (X v) = ∑ i, ∑ j, C (h v.1 i v.2.1 * g x v.1 v.2.2 j) * X (v.1, i, j) by simp [mvZ, aeval_X]]

      simp only [Finset.mul_sum, map_sum, LinearMap.comp_apply, LinearMap.mulRight_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [C_mul', mul_smul_comm, map_smul, smul_eq_mul]
    simp_rw [key]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    refine Continuous.mul (continuous_const.mul ?_) (hp _)
    exact ((continuous_apply j).comp ((continuous_apply v.2.2).comp ((continuous_apply v.1).comp hg)))

theorem continuous_evalAt_mul (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => evalAt (fun τ => u τ * y τ) F := by
  unfold evalAt
  refine (MvPolynomial.continuous_eval F).comp (continuous_pi fun x => ?_)
  exact (((continuous_apply x.1).matrix_mul continuous_const).matrix_elem x.2.1 x.2.2)

theorem isCompact_entries_le_one :
    IsCompact {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} := by
  have : {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} =
      Set.univ.pi fun _ : ι => (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => Metric.closedBall (0:ℂ) 1 : Set (Matrix (Fin a) (Fin a) ℂ)) := by
    ext u
    constructor
    · intro hu τ _ i _ j _
      have := hu τ i j
      show dist (u τ i j) 0 ≤ 1
      simpa using this
    · intro hu τ i j
      have : dist (u τ i j) 0 ≤ 1 := hu τ trivial i trivial j trivial
      simpa using this
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem subY_eq_sum_averages : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b) (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ y' : ι → Matrix (Fin b) (Fin b) ℂ, ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → FP ι a b), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∑ j, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F ∂ν = Λ (subY hab y' F) := by
  intro ι _ a b hab lam n K _ _ _ _ _ ν _ r hr y'
  obtain ⟨m, y, P, hy, hT⟩ := GlobalTheory.T.exists_invertibleFamily_eval_span ι a lam n (FP ι a b) (subY hab y').toLinearMap
  refine ⟨m, y, P, hy, ?_⟩
  intro F hF Λ
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  have vn := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).2
  have hstar : ∀ k τ, star (r k τ) * r k τ = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff').1 (hr.uni k τ)
  have hstar' : ∀ k τ, r k τ * star (r k τ) = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff).1 (hr.uni k τ)
  have hinv : ∀ k τ, (r k τ)⁻¹ = star (r k τ) := fun k τ => Matrix.inv_eq_left_inv (hstar k τ)
  have hpt : ∀ k, ∑ j, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F
      = Λ (subY hab y' F) := by
    intro k
    have hG : subY hab y' (lft (r k) F) = ∑ j, evalAt (y j) (lft (r k) F) • P j := hT _ (vn (r k) F hF)
    have e1 : mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (subY hab y' (lft (r k) F)) = subY hab y' F := by
      rw [h1, h4]
      have ha : (fun τ => r k τ * (r k τ)⁻¹) = fun _ => (1 : Matrix (Fin a) (Fin a) ℂ) := by
        funext τ; rw [hinv, hstar']
      have hb : (fun τ => (1 : Matrix (Fin b) (Fin b) ℂ) * y' τ) = y' := by funext τ; simp
      rw [ha, hb, h5]

    rw [← e1, hG, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, h6, mul_comm]
  have hst : Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ) := continuous_pi fun τ => (continuous_apply τ).star
  have hcont : ∀ j, Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
      Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F := fun j => by
    have e1 := continuous_lin_mvZ (fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ)) hst (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) (P j) Λ
    exact e1.mul (continuous_evalAt_mul (y j) F)
  have hint : ∀ j ∈ Finset.univ, Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) *
      evalAt (fun τ => r k τ * y j τ) F) ν := by
    intro j _
    have hfun : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F)
        = (fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
          Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F) ∘ r := by
      funext k; simp only [Function.comp_apply, hinv]
    rw [hfun]
    obtain ⟨C, hC⟩ := (isCompact_entries_le_one (ι := ι) (a := a)).exists_bound_of_continuousOn (hcont j).continuousOn
    refine Integrable.of_bound ((hcont j).comp hr.cont).aestronglyMeasurable C (Filter.Eventually.of_forall fun k => ?_)
    exact hC _ fun τ i i' => entry_norm_bound_of_unitary (hr.uni k τ) i i'
  rw [← integral_finsetSum _ hint]
  simp_rw [hpt]
  simp

end GlobalTheory.KJInf

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.EntryDatumS

open GlobalTheory.ColNorms.EntryDatum

theorem smallDatum_xiEntry_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.unfoldedEntry_typePrime_support_period_size
  refine ⟨C, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p' => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hg : ∀ i, Pr.g i = N.g i := H.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (p : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j p P x
    have hP := h1 P.1 P.2
    unfold frsF
    rw [dite_eq_left hP]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ p.deco ⟨P.1, hP⟩).1 x
  have key := smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 p'.deco.1 p'.deco.2 (frsF sel mu p) (frsF sel mu p')
    (hfr p) (hfr p') (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P => XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) _
    (hC CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be)
  have e : ∏ P : rowSG Pr sel mu, (Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2) =
      ((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    rw [Finset.prod_pow, ← Nat.cast_prod, h4, hg 0, hg 1]
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [e] at key
  exact key

end GlobalTheory.Core.Ht2.EntryDatumS
end
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.cusp_integralBasis_covolume_constant : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ), 0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  first | exact @GlobalTheory.CuspGeo.covolume_const | exact GlobalTheory.CuspGeo.covolume_const | (intros; apply GlobalTheory.CuspGeo.covolume_const <;> assumption)
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.traceForm_real_coordinates_integral_gram : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)), IsRealCoord I ρ → ∃ (X : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (c : ℕ), μ ≠ 0 ∧ 1 ≤ c ∧ ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ B B' : Matrix (Fin N) (Fin N) ℤ, B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e ∧ gm I ρ y e * B'.map (Int.cast : ℤ → ℝ) * (gm I ρ y e)ᵀ = μ • X ∧ ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := by
  first | exact @GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | exact GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | (intros; apply GlobalTheory.CuspGeo.TrReal.trace_form_real_coord <;> assumption)
end
