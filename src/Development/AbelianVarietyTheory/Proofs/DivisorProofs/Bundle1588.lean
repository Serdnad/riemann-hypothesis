module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ (ψ : Sm E a) (h : smoothing ν α ψ.1 ∈ Sm E a), ∀ z ∈ Zalg E a, (z ⟨smoothing ν α ψ.1, h⟩).1 = smoothing ν α (z ψ).1 := by
  first | exact @GlobalTheory.CentreSmooth.zalg_smoothing | exact GlobalTheory.CentreSmooth.zalg_smoothing | (intros; apply GlobalTheory.CentreSmooth.zalg_smoothing <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a, smoothing ν α ψ ∈ Sm E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_Sm | exact GlobalTheory.AutGrowth.smoothing_mem_Sm | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_Sm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  first | exact @GlobalTheory.DblVacUnip.unip_mem | exact GlobalTheory.DblVacUnip.unip_mem | (intros; apply GlobalTheory.DblVacUnip.unip_mem <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

theorem _root_.GlobalTheory.T.mem_compactPart_centralizer_iff_torus_integral_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (hγ : γ ∈ UL n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h ∈ twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩, (h ∈ cptPart (twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩) ↔ torusOf w B ψ h.1 ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  first | exact @GlobalTheory.KapOrb.CptInt.mem_cptPart_iff_torusOf_mem_intUnits | exact GlobalTheory.KapOrb.CptInt.mem_cptPart_iff_torusOf_mem_intUnits | (intros; apply GlobalTheory.KapOrb.CptInt.mem_cptPart_iff_torusOf_mem_intUnits <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.heisenberg_creation_operators_commute_of_ccr : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockM H j * GlobalTheory.CCRFock.fockM H k = GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockM H j := by
  first | exact @GlobalTheory.CCRFock.fockM_comm | exact GlobalTheory.CCRFock.fockM_comm | (intros; apply GlobalTheory.CCRFock.fockM_comm <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CoefModel

section BaseChange

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (lam : ι → DomWeight n)

theorem fockS_map_int {s : Type} (P : MvPolynomial s ℤ) (g : MvPolynomial s K) :
    fockS (map φ (map (Int.castRingHom K) P)) (map φ g) = φ (fockS (map (Int.castRingHom K) P) g) := by

  rw [fockS_eq_sum _ _ (map (Int.castRingHom K) P).support (support_map_subset _ _), fockS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem pairK_mapVV_int (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) (P : MvPolynomial (ι × Fin n × Fin n) ℤ)
    (hx : (x : Pol K ι n) = map (Int.castRingHom K) P) :
    pairK lam (fun τ => (G τ).map φ) (mapVV φ lam x) (mapVV φ lam y) = φ (pairK lam G x y) := by
  have h1 : (map φ).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map φ)ᵀ).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp [blockAct_X]
  have h2 : map φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map φ)ᵀ) (map φ y.1) :=
    congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y.1) h1
  have h3 : φ (gramTw lam G) = gramTw lam fun τ => (G τ).map φ := by
    unfold gramTw
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  have h4 : φ (extNorm K lam) = extNorm ℂ lam := by
    unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← map_extremal φ n (lam τ), ← map_extremal (Int.castRingHom K) n (lam τ), fockS_map_int]
  have h5 := fockS_map_int φ P (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1)
  rw [← hx] at h5
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, mapVV_coe, mapVV_coe, ← h2, fockL_apply, fockL_apply,
    h5, map_mul, map_div₀, h3, h4]

end BaseChange

def reindexFam {ι M : Type} [Monoid M] (e : ι → ι) : (ι → M) →* (ι → M) :=
  MonoidHom.pi fun τ => Pi.evalMonoidHom (fun _ => M) (e τ)

theorem reindexFam_apply {ι M : Type} [Monoid M] (e : ι → ι) (g : ι → M) (τ : ι) : reindexFam e g τ = g (e τ) := rfl

end GlobalTheory.CoefModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

variable {D : D7}

theorem exists_coef_round_at (V : HSp D) (hV : ∀ τ, (V.gram.map (tauE D τ)).PosDef)
    (lam : D.what₂.Tau → DomWeight V.rank) (σ : D.what₂.LL →+* ℂ) (p : D.what₂.Tau ≃ D.what₂.Tau)
    (hp : ∀ τ, labE σ τ = tauE D (p τ)) :
    ∃ (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W), c.Is ∧
      (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
        ∀ v, c₁ (rhoVr (labLL D) lam γE v) = c.ρ (γ : GA D V) (c₁ v)) ∧
      (LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL lam a)) ∧
      Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤ ∧
      ∀ a y, inner ℂ (c₁ (bVV D.what₂.LL lam a)) (c₁ y) = σ (pairVr (labLL D) lam V.gram (bVV D.what₂.LL lam a) y) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨hc, hs⟩ := realGL_laws hθ V
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hG : ∀ τ, (((V.gram.map (tauE D (p τ)))⁻¹)ᵀ).PosDef := fun τ => (hV (p τ)).inv.transpose
  have hlab : ∀ τ x, σ (labLL D τ x) = tauE D (p τ) x := fun τ x => DFunLike.congr_fun (hp τ) x
  refine ⟨coefOf lam hG (invTrK.comp ((reindexFam p).comp (realGL θ V))),
    (toHilb lam hG).toLinearMap.comp (mapVV σ lam), coefOf_is lam hG _ (fun h hh => ?_) (fun h τ => ?_)
      (fun τ => ?_) (fun g hg => ?_), fun γ γE hγ v => ?_, ?_, ?_, fun a y => ?_⟩
  · have : realGL θ V h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom V h) = 1
      rw [show infHom V h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, this, map_one, map_one]
  · exact invTr_unitary (g := realGL θ V h (p τ)) (GlobalTheory.RecDictModel.archM_unitary V (hθ (p τ)) h)
  · refine ((hc (p τ)).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ (p τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (reindexFam p.symm (invTrK g)) fun ρ => by
      have := invTr_unitary (hg (p.symm ρ))
      rwa [p.apply_symm_apply, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (hV ρ).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e]
    refine funext fun τ => ?_
    show inside₂ ℂ _ (inside₂ ℂ _ (g (p.symm (p τ)))) = g τ
    rw [p.symm_apply_apply, invTr_invTr]
  · show toHilb lam hG (mapVV _ lam (rhoK lam (invTrK (embGL (labLL D) γE)) v)) =
      rhoH lam hG (invTrK (reindexFam p (realGL θ V γ))) (toHilb lam hG (mapVV _ lam v))
    have e : (fun τ => Formalism.UG.bc σ (invTrK (embGL (labLL D) γE) τ)) = invTrK (reindexFam p (realGL θ V γ)) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, reindexFam_apply, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    rw [rhoH_toHilb, mapVV_rhoK, e]
  · exact (linearIndependent_mapVV σ lam).map' (toHilb lam hG).toLinearMap (LinearEquiv.ker _)
  · exact span_mapVV σ lam
  · obtain ⟨P, hP⟩ := bVVfun_int D.what₂.LL lam a
    show inner ℂ (toHilb lam hG (mapVV σ lam (bVV D.what₂.LL lam a))) (toHilb lam hG (mapVV σ lam y)) =
      σ (pairK lam (gramKd (labLL D) V.gram) (bVV D.what₂.LL lam a) y)
    rw [inner_toHilb, ← pairK_mapVV_int σ lam _ _ y P ((bVV_coe _ lam a).trans hP)]
    have e : (fun τ => ((V.gram.map (tauE D (p τ)))⁻¹)ᵀ) = fun τ => (gramKd (labLL D) V.gram τ).map σ := by
      funext τ
      have e1 : V.gram.map (tauE D (p τ)) = (V.gram.map (labLL D τ)).map σ := by
        ext a b
        exact (hlab _ _).symm
      have hu : IsUnit (V.gram.map (labLL D τ)).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact ((_root_.map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)).isUnit
      rw [gramKd, Matrix.transpose_map, e1]
      congr 1
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg (fun G => pairK lam G (mapVV σ lam (bVV D.what₂.LL lam a)) (mapVV σ lam y)) e

theorem exists_coefAt_of_posDef (i : Fin D.R.m) (h : (Vc D i).IsPosDef) (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) :
    ∃ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ := by
  have hl := (GlobalTheory.GalLift.labels_overK σ).1 hσ
  have hV : ∀ τ, ((Vc D i).gram.map (tauE D τ)).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [h (tauE D τ)] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hg : gramV D i = (Vc D i).gram := by
    rw [gramV, GlobalTheory.StdFrame.neg_eq_false_of_posDef D i h, if_neg Bool.false_ne_true]
  have H := exists_coef_round_at (Vc D i) hV (lamV D i) σ (Equiv.ofBijective _ hl.1).symm fun τ =>
    (congrArg (labE σ) ((Equiv.ofBijective _ hl.1).apply_symm_apply τ).symm).trans (hl.2 _)
  obtain ⟨c, c₁, h1, h2, h3, h4, h5⟩ := H
  exact ⟨c, c₁, h1, h2, h3, h4, fun a b => hg ▸ h5 a _⟩

end GlobalTheory.CoefModel
end
end

section

open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_matrixAdjoinTensorUnramified_of_commute_separable : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r), Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := by
  first | (exact @GlobalTheory.PolyTensorCommutant.exists_phi_eq) | (exact GlobalTheory.PolyTensorCommutant.exists_phi_eq) | (intros; apply GlobalTheory.PolyTensorCommutant.exists_phi_eq  <;> assumption)
end

section

open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

theorem _root_.GlobalTheory.T.matrixAdjoinTensorUnramifiedToMatrix_injective : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → Function.Injective (GlobalTheory.PolyTensor.phi p K n γ r) := by
  first | (exact @GlobalTheory.PolyTensor.phi_injective) | (exact GlobalTheory.PolyTensor.phi_injective) | (intros; apply GlobalTheory.PolyTensor.phi_injective <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.flat_tensorSubalgebraMvPolynomialEval_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  first | exact @GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | exact GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | (intros; apply GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v, GlobalTheory.DblVac.BigCell W v g →
      ∃ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W ∧ ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ g = q * p := by
  first | exact @GlobalTheory.DblVacGauss.gauss_decomp | exact GlobalTheory.DblVacGauss.gauss_decomp | (intros; apply GlobalTheory.DblVacGauss.gauss_decomp <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_continuous_unitaryDiagonalEmbedding_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      ∃ ι : Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J),
        Continuous ι ∧
        (∀ h, Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ J h) 0 0 1)) ∧
        (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ι γ ∈ Formalism.IndefR.DatumF.GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) ∧
        (∀ e h, Formalism.IndefR.DatumF.SuppAtF σ e J h → Formalism.IndefR.DatumF.SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h)) ∧
        (∀ e h y, Formalism.IndefR.DatumF.IsDetAtF σ e J h y →
          Formalism.IndefR.DatumF.IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) y) := by
  first | exact @GlobalTheory.DiagEmbU.exists_diagEmb | exact GlobalTheory.DiagEmbU.exists_diagEmb | (intros; apply GlobalTheory.DiagEmbU.exists_diagEmb <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.thetaTransform_doubledTarget_boxProduct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun | exact GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun | (intros; apply GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun <;> assumption)
end
