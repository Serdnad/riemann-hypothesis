module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerScalesDoubledVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacTransport

theorem acts_dblVacCond_of_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ₁)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ₁))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v dd omd hsp θ hθ g hg φ hφ φ₁ hφ₁ hvac hAct w₁ hw₁ w₂ hw₂ r hr
  have hS := hsp.2.1
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨δ₁, k₁, δ₂, k₂, he⟩ := GlobalTheory.DblVacLine.fromCols_mul_transpose G.V' G.W v (GlobalTheory.InertDbl.matD g⁻¹)
    (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hback : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g (Matrix.fromCols δ₁ δ₂) = Matrix.fromCols w₁ w₂ := by
    change Matrix.fromCols δ₁ δ₂ * (GlobalTheory.InertDbl.matD g)ᵀ = _
    have e : GlobalTheory.InertDbl.matD g * GlobalTheory.InertDbl.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [← he, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsym : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
        (Matrix.fromCols δ₁ δ₂) (Matrix.fromCols δ₁ δ₂) =
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
        (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) := by
    rw [← he]
    exact GlobalTheory.InertSph.symp_mul_transpose (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) _ _ _ (GlobalTheory.InertDbl.matD g⁻¹) (g⁻¹).2 _
  have hi := hS.impl g (Matrix.fromCols δ₁ δ₂) _ hrφ.2
  simp only [actB] at hback hi
  rw [hback] at hi
  rw [← hAct r hrφ, ← hi, hvac δ₁ k₁ δ₂ k₂ r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.DblVacTransport
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_scales_doubledVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.DblVacEigen.eigen_box | exact GlobalTheory.DblVacEigen.eigen_box | (intros; apply GlobalTheory.DblVacEigen.eigen_box <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_bigCell_stabiliser_of_localRingBigCell_lemma : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  first | exact @GlobalTheory.InertBigCell.exists_bigCell | exact GlobalTheory.InertBigCell.exists_bigCell | (intros; apply GlobalTheory.InertBigCell.exists_bigCell <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weilRep_real_fixes_fock_maximal_minors : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
  ∀ g ∈ GinfC X.A, ∀ T, X.om (g, 1) (X.fock T) = X.fock T := by
  first | exact @GlobalTheory.NormDict.om_real_fock_eq | exact GlobalTheory.NormDict.om_real_fock_eq | (intros; apply GlobalTheory.NormDict.om_real_fock_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.depthPeriodic_of_cosetIndicatorExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  first | exact @GlobalTheory.DepthUnf.depthOK_of_isCosetExpansion | exact GlobalTheory.DepthUnf.depthOK_of_isCosetExpansion | (intros; apply GlobalTheory.DepthUnf.depthOK_of_isCosetExpansion <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  first | exact @GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK | exact GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK | (intros; apply GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

open CategoryTheory.Limits MonoidalCategory

theorem one_left_eq {k : Type} [Field k] {X : Over (Sp k)} [MonObj X] (T : Over (Sp k)) :
    (1 : T ⟶ X).left = T.hom ≫ (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ X).left := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left]
  rfl

theorem isoSpec_hom_comp_spec {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (g : X ⟶ Spec R) :
    X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem exists_kerPow_zero_finrank_eq_deg : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f →
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  intro k _ A B f hf
  obtain ⟨-, hflat, -, hrank⟩ := isogeny_flat_finrank k A B f hf
  haveI : IsFinite f.hom.left := hf.1
  haveI := hflat
  let e : Sp k ⟶ B.X.left := (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X)
  let P := pullback f.hom.left e
  let g : P ⟶ Sp k := pullback.snd f.hom.left e
  haveI : IsAffine P := isAffine_of_isAffineHom g
  let H : Type := Γ(P, ⊤)
  letI : Algebra k H := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hg : P.isoSpec.hom ≫ spMap (algebraMap k H) = g := isoSpec_hom_comp_spec g
  have hig : P.isoSpec.inv ≫ g = spMap (algebraMap k H) := by rw [← hg, Iso.inv_hom_id_assoc]
  have hw : (P.isoSpec.inv ≫ pullback.fst f.hom.left e) ≫ A.X.hom = spMap (algebraMap k H) := by
    rw [← Over.w f.hom, Category.assoc, pullback.condition_assoc, he, Category.comp_id, hig]
  let i : ptOver k H ⟶ A.X := Over.homMk (P.isoSpec.inv ≫ pullback.fst f.hom.left e) hw
  have hi : i.left = P.isoSpec.inv ≫ pullback.fst f.hom.left e := rfl
  refine ⟨H, inferInstance, inferInstance, i, ⟨⟨?_, pow_zero i⟩, ?_⟩, ?_⟩
  · ext1
    rw [Over.comp_left, one_left_eq, hi, Category.assoc, pullback.condition, ← Category.assoc, hig]
    rfl
  · intro R _ _ x hx _
    have hx' : x.left ≫ f.hom.left = spMap (algebraMap k R) ≫ e := by
      have := congrArg Over.Hom.left hx
      rw [Over.comp_left, one_left_eq] at this
      exact this
    let l : Sp R ⟶ P := pullback.lift x.left (spMap (algebraMap k R)) hx'
    obtain ⟨φ0, hφ0⟩ := Spec.map_surjective (l ≫ P.isoSpec.hom)
    have hc : CommRingCat.ofHom (algebraMap k H) ≫ φ0 = CommRingCat.ofHom (algebraMap k R) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ0, Category.assoc, hg]
      exact pullback.lift_snd _ _ _
    let φ : H →ₐ[k] R :=
      { φ0.hom with commutes' := fun c => congrArg (fun u => u.hom c) hc }
    have hφ : spMap φ.toRingHom = l ≫ P.isoSpec.hom := hφ0
    refine ⟨φ, ?_, fun ψ hψ => ?_⟩
    · change spMap φ.toRingHom ≫ i.left = x.left
      rw [hφ, hi, Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _
    · have h1 : spMap ψ.toRingHom ≫ P.isoSpec.inv = l := by
        apply pullback.hom_ext
        · rw [Category.assoc, ← hi]
          exact hψ.trans (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hig, pullback.lift_snd]
          change Spec.map _ ≫ Spec.map _ = Spec.map _
          rw [← Spec.map_comp]
          congr 1
          ext c
          exact ψ.commutes c
      have h2 : spMap ψ.toRingHom = spMap φ.toRingHom := by
        rw [hφ, ← h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have h3 := Spec.map_injective h2
      exact AlgHom.ext fun a => congrArg (fun u => u.hom a) h3
  · haveI : IsFinite (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Flat (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Module.Finite k H := by
      rw [← RingHom.finite_algebraMap]
      exact (IsFinite.SpecMap_iff _).1 ‹_›
    let pt : Sp k := IsLocalRing.closedPoint k
    have h1 := Scheme.Hom.finrank_pullback_snd f.hom.left e pt
    rw [hrank] at h1
    rw [← h1]
    change _ = Scheme.Hom.finrank g pt
    rw [← hg, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl

end GlobalTheory.AV.KerPart
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

theorem mem_prime_dual_iff {K : Type} [Field K] (p : Ideal (DualNumber K)) [hp : p.IsPrime] (x : DualNumber K) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra h
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx hu)
  · intro h
    have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext h rfl
    have h2 : x * x = 0 := by rw [hx, TrivSqZeroExt.inr_mul_inr]
    exact (hp.mem_or_mem (h2 ▸ p.zero_mem)).elim id id

theorem dual_pt_eq {K : Type} [Field K] (p q : Sp (DualNumber K)) : p = q := by
  apply PrimeSpectrum.ext
  ext x
  have hp : p.asIdeal.IsPrime := p.isPrime
  have hq : q.asIdeal.IsPrime := q.isPrime
  exact (mem_prime_dual_iff (K := K) p.asIdeal x).trans (mem_prime_dual_iff (K := K) q.asIdeal x).symm

theorem top_le_of_red {K : Type} [Field K] {T : Scheme.{0}} (φ : DualNumber K →+* K) (w : Sp (DualNumber K) ⟶ T)
    {V : T.Opens} (h : ⊤ ≤ (spMap φ ≫ w) ⁻¹ᵁ V) : ⊤ ≤ w ⁻¹ᵁ V := by
  intro p _
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have e : p = spMap φ q := dual_pt_eq _ _
  have hq := h (Set.mem_univ q)
  rw [e]
  exact hq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem ev_resU {T : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ T) {U V : T.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ z ⁻¹ᵁ V) (hU : ⊤ ≤ z ⁻¹ᵁ U) (u : Γ(T, U)ˣ) :
    GlobalTheory.FlagMod.ev z V hV (res e u).val = GlobalTheory.FlagMod.ev z U hU u.val :=
  GlobalTheory.FlagMod.ev_res z e hV hU u.val

theorem tAt_congr {K : Type} [CommRing K] (k k' : X.F.J) {w w' : Sp K ⟶ X.YY} (e : w = w')
    (h : ⊤ ≤ w ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) (h' : ⊤ ≤ w' ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    X.F.TAt k k' w h = X.F.TAt k k' w' h' := by
  subst e; rfl


open Classical in
theorem ev_div_g (i i' : M.K.bundle.ι) (k k' : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X)
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k')))
    (hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i')) (hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k)
                 (i', flagIdx M _ k')).val =
      GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
        (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val := by
  set e := exOf Dw (FlagTan.kap Dw) 0
  have hL : ⊤ ≤ z ⁻¹ᵁ (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k) ⊓
      ((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k')) := fun p hp => ⟨(hg hp).1.2, (hg hp).2.2⟩
  have hh1 : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ ((L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k PUnit.unit) ⊓
      (L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k' PUnit.unit)) := fun p hp => ⟨mem_pIdx.2 (hh hp).1, mem_pIdx.2 (hh hp).2⟩
  have hh2 : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := fun p hp => hh hp
  have eL : GlobalTheory.FlagMod.ev z _ hL (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).g (flagIdx M _ k) (flagIdx M _ k')).val =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix)).val := by
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ z hL hh1]
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ (z ≫ M.σ) hh1 hh2]
    refine (X.F.ev_LL_g e k k' _ hh2).trans ?_
    rw [tAt_congr k k' (Category.assoc _ _ _) hh2 hh]
  have ei : ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix) : Kˣ) : K)⁻¹ =
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ e ix : Kˣ) : K) := by
    rw [← Units.val_inv_eq_inv_val, ← Finset.prod_inv_distrib]
    simp only [zpow_neg, inv_inv]
  dsimp only [LB.div]
  refine ((GlobalTheory.FlagMod.ev z _ hg).map_mul _ _).trans (congrArg₂ (· * ·) (ev_resU z _ hg hK _)
    ((map_units_inv (GlobalTheory.FlagMod.ev z _ hg) _).trans ?_))
  refine (congrArg Inv.inv (ev_resU z _ hg hL _)).trans ?_
  rw [eL, ei]

theorem red_comp_eq {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P : FrPt Xo c K}
    (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) :
    spMap (FlagTan.red c K).toRingHom ≫ zw = z := by
  have hx : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun p hp => by
    have := ho hp
    rw [M.off_eq] at this
    exact this
  have h1 : (spMap (FlagTan.red c K).toRingHom ≫ zw) ≫ M.σ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z)]
    simp only [Category.assoc]
    have e1 : zw ≫ M.σ ≫ inc₀ X Z = X.ptY w := hl
    have e2 : z ≫ M.σ ≫ inc₀ X Z = X.ptY P := hP
    rw [e1, e2]
    exact X.ptY_frMap hw
  exact (M.existsUnique_lift (z ≫ M.σ) hx).unique h1 rfl

theorem top_le_of_isDef {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {P : FrPt Xo c K} (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) {V : M.X.Opens} (hV : ⊤ ≤ z ⁻¹ᵁ V) :
    ⊤ ≤ zw ⁻¹ᵁ V :=
  top_le_of_red _ zw (by rw [red_comp_eq M z ho hP hw zw hl]; exact hV)


open Classical in
theorem ksRel_of_ksRel {i i' : M.K.bundle.ι} {k k' : X.F.J} {K : Type} [Field K] {z : Sp K ⟶ M.X}
    (hs : ⊤ ≤ z ⁻¹ᵁ ksOpen M i k) (hs' : ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k')
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) {x' : K}
    (hx' : KSRel M i' k' z x') :
    KSRel M i k z (GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g
      (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x') := by
  intro _ P Q t v zv O hO g hz hzv hk hQ ht hv hl
  have ho : ⊤ ≤ z ⁻¹ᵁ M.off := fun p hp => (hs hp).1
  have hi' : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i' := fun p hp => (hs' hp).2.1
  have hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i') := fun p hp => ⟨(hs hp).2.1, (hs' hp).2.1⟩
  have hk' : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k' := fun p hp => mem_pIdx.1 (mem_pIdx.1 (hs' hp).2.2)
  have hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := GlobalTheory.FlagMod.le_preimage_inf hk hk'
  have hlies := hQ.lies
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd Q) hlies.1 k' hk'
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  have hB := hQ.frBor hQ' hh
  have ht' := g1 _ _ _ _ _ (g2 _ _ _ hB) ht
  have hP : z ≫ toFlag M = X.ptY P := FlagCover.eq_ptY (hlies.frBor ht)
  have hzv' : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := fun b =>
    GlobalTheory.FlagMod.le_preimage_inf (hzv b) (top_le_of_isDef M z ho hP (hv.isDef b) (zv b) (hl b) hi')
  have hz' : ⊤ ≤ z ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := GlobalTheory.FlagMod.le_preimage_inf hz hi'
  have key := hx' P Q' _ v zv (O ⊓ M.K.bundle.U i') inf_le_right (fun a => resG M.X inf_le_left (g a)) hz' hzv' hk'
    hQ' ht' hv hl
  have hdet : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) (O ⊓ M.K.bundle.U i') (hzv' _)
      (resG M.X inf_le_left (g a))).snd) = Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd := by
    ext a b
    simp only [Matrix.of_apply]
    rw [evalPt_res]
  rw [hdet] at key
  have hJ : evalPt z O hz (M.K.jacobian i hO g) = GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) := by
    rw [← evalPt_res z inf_le_left hz hz', CanonLB.resG_jacobian,
      CanonLB.jacobian_change _ i i' (inf_le_left.trans hO) inf_le_right, map_mul]
    congr 1
    exact evalPt_res z _ hK hz' _
  rw [ev_div_g M i i' k k' z hg hK hh, hJ]
  have hu : (∏ ix, ((X.F.TAt k k' (z ≫ toFlag M) hh)⁻¹ * t) ix ^ exOf Dw (FlagTan.kap Dw) 0 ix) =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)⁻¹ *
        ∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ix _ => ?_
    rw [Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow]
  rw [hu, Units.val_mul] at key
  have hTT := Units.mul_inv (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)
  linear_combination (GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K)) * key +
    ((∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K) * GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) * hTT

end GlobalTheory.CompHS


open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS in
theorem GlobalTheory.CompHS.ksRel_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i i' : M.K.bundle.ι) (k k' : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k' → ∀ (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) (x x' : K), KSRel M i k z x → KSRel M i' k' z x' → x = GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x' := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS i i' k k' K _ z hs hs' hg x x' hx hx'
  exact (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS i k K z hs).1 x _ hx (ksRel_of_ksRel M hs hs' hg hx')
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

theorem _root_.GlobalTheory.T.deformationChartPoint_reduction_eq_specialFibre : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l), spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ l = spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i := by
  first | exact @GlobalTheory.CechKS.chartPt_red | exact GlobalTheory.CechKS.chartPt_red | (intros; apply GlobalTheory.CechKS.chartPt_red <;> assumption)
end

section


theorem _root_.GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  first | exact @GlobalTheory.Proof.abelianDeRhamFree_of_hodge | exact GlobalTheory.Proof.abelianDeRhamFree_of_hodge | (intros; apply GlobalTheory.Proof.abelianDeRhamFree_of_hodge <;> assumption)
end
