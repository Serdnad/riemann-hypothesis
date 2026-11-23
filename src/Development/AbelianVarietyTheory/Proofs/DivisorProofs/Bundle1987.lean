module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeTranslationInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.scaled_lattice_translation_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
    (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i))) → T f' = T f) →
    (∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
        T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      T f = c * ∑' ξ : κ → F, {ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun ξ => f (fun i => mixedEmbedding F (ξ i))) ξ := by
  first | exact @GlobalTheory.LatUniq.main_lat | exact GlobalTheory.LatUniq.main_lat | (intros; apply GlobalTheory.LatUniq.main_lat <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_admitted_eq_diagonalLagrangian_thetaIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ l₂ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l₂ Φ = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.LagrThetaAdm.exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt | exact GlobalTheory.LagrThetaAdm.exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt | (intros; apply GlobalTheory.LagrThetaAdm.exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolPush

theorem meas_translate_eq : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  intro D V θ A m rp K μ hV hθ hA hm hc hrp hK hμ g hg B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  have h1 : rp g = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp g hg
  rw [← GlobalTheory.CovTop.VolBox.meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB,
    ← measure_preimage_mul μ g⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
  congr 1
  ext h
  show finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B ↔ finE V (g⁻¹ * h) ∈ K ∧ rp (g⁻¹ * h) ∈ B
  rw [map_mul rp, map_inv rp, h1, inv_one, one_mul]

end GlobalTheory.CovTop.VolPush
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.measure_translateLevel_realBox_le_index_mul : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  first | exact @GlobalTheory.CovTop.VolBox.meas_translate_le | exact GlobalTheory.CovTop.VolBox.meas_translate_le | (intros; apply GlobalTheory.CovTop.VolBox.meas_translate_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.exists_unipotent_maps_for_theta_triple : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) →+ Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      (∀ Y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (uT Y) ∧ (uT Y).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
        GlobalTheory.VacShape.coBar Bs Γ (uT Y) = Y) ∧
      (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (uM z) ∧
        (uM z).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 ∧ (uM z).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = -z) ∧
      (∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
        evFin D.host.F Bs.v₁ (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x u) =
          ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁)) i j * GlobalTheory.VacShape.coBar Bs Γ u i j -
            ∑ i, ∑ j, GlobalTheory.VacShape.coBar Bs Γ x i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁)) i j) := by
  first | exact @GlobalTheory.LinCoords.coords | exact GlobalTheory.LinCoords.coords | (intros; apply GlobalTheory.LinCoords.coords <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryAutForms_weight_level_le_tensor_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  first | exact @GlobalTheory.BCT.TrKer.forms_le_range | exact GlobalTheory.BCT.TrKer.forms_le_range | (intros; apply GlobalTheory.BCT.TrKer.forms_le_range <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open GlobalTheory.TriMove GlobalTheory.Mem.Isom
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

private theorem opPow_comm {ι X X' : Type} (tr : (X → ℂ) →ₗ[ℂ] (X' → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (A' : ι → (X' → ℂ) → (X' → ℂ)) (h : ∀ k g, A' k (tr g) = tr (A k g)) (k : ι →₀ ℕ) (f : X → ℂ) :
    opPow A' k (tr f) = tr (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [ih, h]

private theorem pure_comm {D : D7} {m n m' n' : ℕ} (hm : m = m') (hn : n = n') {X X' : Type}
    (tr : (X → ℂ) →ₗ[ℂ] (X' → ℂ)) (A : FVar D m n → (X → ℂ) → (X → ℂ))
    (A' : FVar D m' n' → (X' → ℂ) → (X' → ℂ))
    (h : ∀ (k : FVar D m n) g, A' (k.1, finCongr hm k.2.1, finCongr hn k.2.2) (tr g) = tr (A k g)) (f : X → ℂ)
    (P : MvPolynomial (FVar D m n) ℂ) :
    pureTensorL A' (tr f) (polMove hm hn P) = tr (pureTensorL A f P) := by
  subst hm hn
  have e : polMove (D := D) (rfl : m = m) (rfl : n = n) P = P := MvPolynomial.rename_id_apply P
  rw [e]
  have e2 : pureTensorL A' (tr f) = tr ∘ₗ pureTensorL A f := by
    refine (MvPolynomial.basisMonomials (FVar D m n) ℂ).ext fun k => ?_
    unfold pureTensorL
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]
    exact opPow_comm tr A A' h k f
  rw [e2]
  rfl

private theorem unitMap_move {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (pS : Matrix (Fin n') (Fin n) ℂ) (qS : Matrix (Fin n) (Fin n') ℂ) (pq : pS * qS = 1)
    (pT : Matrix (Fin m') (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    unitMap (pS * B * (rdx hn : Matrix (Fin n) (Fin n') ℂ)) (pT * B' * (rdx hm : Matrix (Fin m) (Fin m') ℂ)) (finCongr hm i) (finCongr hn j) = pT * unitMap B B' i j * qS := by
  subst hm hn
  have e1 : rdx (K := ℂ) (rfl : m = m) = 1 := rfl
  have e2 : rdx (K := ℂ) (rfl : n = n) = 1 := rfl
  unfold unitMap
  rw [e1, e2, Matrix.mul_one, Matrix.mul_one, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv pq]
  simp only [Matrix.mul_assoc]
  rfl

private theorem cplxO_move {m n m' n' : ℕ} (ε : Bool)
    (pS : Matrix (Fin n') (Fin n) ℂ) (qS : Matrix (Fin n) (Fin n') ℂ) (qp : qS * pS = 1)
    (pT : Matrix (Fin m') (Fin m) ℂ) (qT : Matrix (Fin m) (Fin m') ℂ) (qp' : qT * pT = 1)
    (s : Matrix (Fin n) (Fin n) ℂ) (s' : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (GlobalTheory.Grid.sgnM ε (pS * s * qS)) (pT * s' * qT) (pT * z * qS) = pT * cplxO (GlobalTheory.Grid.sgnM ε s) s' z * qS := by
  have e : GlobalTheory.Grid.sgnM ε (pS * s * qS) = pS * GlobalTheory.Grid.sgnM ε s * qS := by
    cases ε
    · rfl
    · show -(pS * s * qS) = pS * (-s) * qS
      rw [Matrix.mul_neg, Matrix.neg_mul]
  unfold cplxO
  rw [e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = pT * s' * (qT * pT) * z * (qS * pS) * GlobalTheory.Grid.sgnM ε s * qS := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [qp, qp', Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private theorem trace_move {A : Type} [CommRing A] {m n m' n' : ℕ} (s : A →+* A)
    {H : Matrix (Fin n) (Fin n) A} {H' : Matrix (Fin n') (Fin n') A} {Q : Matrix (Fin n) (Fin n') A}
    (hH : Q * H' * cT s Q = H)
    {J : Matrix (Fin m) (Fin m) A} {J' : Matrix (Fin m') (Fin m') A} {P : Matrix (Fin m') (Fin m) A}
    (hJ : cT s P * J' * P = J) (x y : Matrix (Fin m) (Fin n) A) :
    Matrix.trace (H' * (cT s (P * y * Q) * J' * (P * x * Q))) = Matrix.trace (H * (cT s y * J * x)) := by
  rw [← hH, ← hJ, cT_mul, cT_mul]
  calc _ = Matrix.trace ((H' * cT s Q * (cT s y * (cT s P * J' * P) * x)) * Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

variable {D : D7}

private theorem hO_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (S.gram⁻¹.map (incA D) * (cT (cA D) y * T.gram.map (incA D) * x)) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact sum_form (cA D) (T.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b

variable {S S' T T' : HSp D}

private theorem gram_inv_move (I : IsoMat S S') :
    I.Q * S'.gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q = S.gram⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← I.gram]
  calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * (S'.gram * (I.P * I.Q) * S'.gram⁻¹) *
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [I.PQ, Matrix.mul_one, Matrix.mul_nonsing_inv _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S'), Matrix.mul_one, ← cT_mul, I.QP,
        cT_one]

private theorem hO_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    hO S' T' (homMap IS IT x) (homMap IS IT y) = hO S T x y := by
  rw [hO_trace, hO_trace]
  refine trace_move (cA D) ?_ (map_gram (incA D) _ (cA D) (fun _ => rfl) IT.gram) x y
  rw [← gram_inv_move IS, Matrix.map_mul, Matrix.map_mul]
  rfl

private theorem heisO_homMap (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (IS : IsoMat S S') (IT : IsoMat T T') (u : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ (GlobalTheory.Grid.sgn ε S') T' (homMap (S := S) (S' := S') IS IT u) (trH (S := S) (S' := S') IS IT f) = trH (S := S) (S' := S') IS IT (heisO ψ (GlobalTheory.Grid.sgn ε S) T u f) := by
  funext w
  obtain ⟨w, rfl⟩ := (homMap IS IT).surjective w
  have e : hO (GlobalTheory.Grid.sgn ε S') T' (homMap IS IT w) (homMap IS IT u) = hO (GlobalTheory.Grid.sgn ε S) T w u := by
    cases ε
    · exact hO_homMap IS IT w u
    · exact (GlobalTheory.Grid.hO_neg S' T' _ _).trans ((congrArg Neg.neg (hO_homMap IS IT w u)).trans (GlobalTheory.Grid.hO_neg S T _ _).symm)
  simp only [heisO, trH, ← map_add (f := _), AddEquiv.symm_apply_apply, symplOH, symplO, e]

private theorem lineAt_spec {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

private theorem lineAt_homMap {θ : InfFam D} (hθ : IsInfFam θ) (IS : IsoMat S S') (IT : IsoMat T T') (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (IT.pT τ * z * IS.qT τ) t = homMap IS IT (lineAt θ τ z t) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨h1, h2, h3⟩ := lineAt_spec hθ τ z
  have key : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) ((homMap IS IT).toAddMonoidHom.comp (lineAt θ τ z)) := by
    refine ⟨(continuous_const.matrix_mul h1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul (HMul.hMul IT.aP (lineAt θ τ z t)) IS.aQ).map (finPart D) = 0
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · let ρ : AE D →+* ℂ := (θ τ').comp (infPart D)
      have hρ : ∀ x : D.host.E, ρ (incA D x) = tauE D τ' x := fun x => by
        have := (hθ τ').1 x
        rw [← this]
        simp [ρ, incA, inclR, infPart]
      have e1 : IT.aP.map ρ = IT.pT τ' := by ext i j; exact hρ _
      have e2 : IS.aQ.map ρ = IS.qT τ' := by ext i j; exact hρ _
      have e3 : (lineAt θ τ z t).map ρ = _ := h3 t τ'
      show (HMul.hMul (HMul.hMul IT.aP (lineAt θ τ z t)) IS.aQ).map ρ = _
      rw [Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
      split_ifs with c
      · subst c
        rw [Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (lineAt_spec hθ τ _) key]
  rfl

private theorem dRho_homMap (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (ε : Bool) (IS : IsoMat S S')
    (IT : IsoMat T T') (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ (GlobalTheory.Grid.sgn ε S') T') θ τ (IT.pT τ * z * IS.qT τ) (trH (S := S) (S' := S') IS IT f) =
      trH (S := S) (S' := S') IS IT (dRho (heisO ψ (GlobalTheory.Grid.sgn ε S) T) θ τ z f) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  simp only [lineAt_homMap hθ, heisO_homMap]
  rfl

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ → ∀ (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
  pureTensorO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (fun τ => GlobalTheory.TriMove.basMove (S' := S') IS τ (BS τ)) (fun τ => GlobalTheory.TriMove.basMove (S' := T') IT τ (BT τ)) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) (GlobalTheory.TriMove.polMove IT.rank_eq IS.rank_eq P) =
    GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT (pureTensorO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT BS BT f P) := by
  intro D ψ θ hθ ε S S' T T' IS IT sS BS sT BT f P
  refine pure_comm IT.rank_eq IS.rank_eq (GlobalTheory.TriMove.trLE IS IT).toLinearMap _ _ (fun k g => ?_) f P
  have e : ∀ g, (GlobalTheory.TriMove.trLE IS IT).toLinearMap g = GlobalTheory.TriMove.trH IS IT g := fun _ => rfl
  have e1 : unitMap (GlobalTheory.TriMove.basMove IS k.1 (BS k.1)) (GlobalTheory.TriMove.basMove IT k.1 (BT k.1)) (finCongr IT.rank_eq k.2.1)
      (finCongr IS.rank_eq k.2.2) = _ :=
    unitMap_move IT.rank_eq IS.rank_eq _ _ (IS.pT_qT k.1) (IT.pT k.1) (BS k.1) (BT k.1) k.2.1 k.2.2
  rw [e, e]
  unfold aPlusAll aPlus crea GlobalTheory.TriMove.cartMove
  dsimp only
  rw [e1, cplxO_move ε _ _ (IS.qT_pT k.1) _ _ (IT.qT_pT k.1), dRho_homMap ψ hθ, dRho_homMap ψ hθ]
  rfl
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriMove.StdFstMove

variable {D : D7}

private theorem rdi_mul_rdx {K : Type} [CommRing K] {m n m' n' : ℕ} (h : m = n) (h' : m' = n') (M : Matrix (Fin m) (Fin m') K) :
    HMul.hMul (HMul.hMul (rdi (K := K) h) M) (rdx (K := K) h') = M.submatrix (finCongr h).symm (finCongr h').symm := by
  subst h; subst h'
  ext i j
  simp [rdi, rdx, Matrix.mul_apply, Matrix.one_apply]

private theorem isIntM_re {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    Formalism.IndefR.Datum.IsIntM (D := D) (M.submatrix (finCongr hb).symm (finCongr ha).symm) ↔ Formalism.IndefR.Datum.IsIntM (D := D) M := by
  subst ha; subst hb; simp

private theorem inId_re (I : Ideal (𝓞 D.host.E)) {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    (∀ i j, a' ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (M.submatrix (finCongr hb).symm (finCongr ha).symm i j)) ↔
      ∀ i j, a ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (M i j) := by
  subst ha; subst hb; simp

private theorem unitChar_re (ν : (AE D)ˣ →* Circle) (e : AE D) {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (Formalism.IndefR.Datum.topL a' (M.submatrix (finCongr hb).symm (finCongr ha).symm)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (Formalism.IndefR.Datum.topL a M) := by
  subst ha; subst hb; simp

private theorem fixed_two {R : Type} [CommRing R] {p q r s : ℕ} (e : R) (M : Matrix (Fin p) (Fin q) R) (N : Matrix (Fin r) (Fin s) R)
    (x : Matrix (Fin q) (Fin r) R) (H : ∀ i j, e * x i j = x i j) (i : Fin p) (j : Fin s) :
    e * (M * x * N) i j = (M * x * N) i j := by
  have hx : e • x = x := by ext i j; exact H i j
  have : e • (M * x * N) = M * x * N := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, hx]
  exact congrFun (congrFun this i) j

variable {S S' T T' : HSp D}

private theorem isHalf_homMap (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (e : AE D) (x : WO S T) :
    Formalism.IndefR.Datum.IsHalf e (homMap IS IT x) ↔ Formalism.IndefR.Datum.IsHalf e x := by
  constructor
  · intro h
    have hx : x = HMul.hMul (HMul.hMul IT.aQ (homMap IS IT x)) IS.aP := ((homMap IS IT).symm_apply_apply x).symm
    intro i j
    rw [hx]
    exact fixed_two e _ _ _ h i j
  · intro h i j
    exact fixed_two e _ _ _ h i j

private theorem map_aP (I : GlobalTheory.Mem.Isom.IsoMat S S') : I.aP.map (Formalism.IndefR.Datum.toEAf D) = fP I := by
  ext i j; rfl

private theorem map_aQ (I : GlobalTheory.Mem.Isom.IsoMat S S') : I.aQ.map (Formalism.IndefR.Datum.toEAf D) = fQ I := by
  ext i j; rfl

private theorem frMapO_homMap (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T')
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO S T) :
    frMapO S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT x) =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (frMapO S T βS βT x)) (rdx (K := Lev.EAf D) IS.rank_eq) := by
  unfold frMapO
  rw [homMap_apply]
  show HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (βT⁻¹).val) (fQ IT))
      ((HMul.hMul (HMul.hMul IT.aP x) IS.aQ).map (Formalism.IndefR.Datum.toEAf D)))
      (HMul.hMul (HMul.hMul (fP IS) βS.val) (rdx (K := Lev.EAf D) IS.rank_eq)) = _
  rw [Matrix.map_mul, Matrix.map_mul, map_aP, map_aQ]
  calc _ = HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (βT⁻¹).val) (HMul.hMul (fQ IT) (fP IT)))
            (x.map (Formalism.IndefR.Datum.toEAf D))) (HMul.hMul (fQ IS) (fP IS))) βS.val) (rdx (K := Lev.EAf D) IS.rank_eq) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [fQ_fP, fQ_fP, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc (rdi _), ← Matrix.mul_assoc (rdi _)]

private theorem stdFst_move : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT) := by
  intro D S S' T T' IS IT ν e I βS βT
  classical
  funext w
  obtain ⟨x, rfl⟩ := (homMap IS IT).surjective w
  unfold trH
  rw [AddEquiv.symm_apply_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [frMapO_homMap, rdi_mul_rdx]
  exact if_congr (and_congr (isHalf_homMap IS IT e x) (and_congr (isIntM_re _ _ _) (inId_re I _ _ _))) (unitChar_re ν e _ _ _) rfl

end GlobalTheory.TriMove.StdFstMove

end

theorem _root_.GlobalTheory.T.standardPairFirstMemberHalf_isometry_moved : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT) := @GlobalTheory.TriMove.StdFstMove.stdFst_move
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1 := by
  first | exact @GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one | exact GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one | (intros; apply GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one <;> assumption)
end
