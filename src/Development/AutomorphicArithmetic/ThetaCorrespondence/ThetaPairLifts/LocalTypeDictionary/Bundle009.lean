module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle455
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle344
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle453
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle479
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
namespace GlobalTheory.RowEx.RatioField
open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
end GlobalTheory.RowEx.RatioField
namespace GlobalTheory.RowEx.RatioField
open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
theorem twistRatio_mem_numberField : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.LNe → NFRatio := by
  intro _ hTR hFD _
  obtain ⟨CF0, hF⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, hF⟩ := hF ε CF hCF
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hsc => ?_⟩
  have hRec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hS.size, hS.host⟩
  haveI : Finite T := hS.fin
  have key : ∀ (sc : Consts) (G : GridData R.toLevCh sc), sc = ⟨1, CF, large₂.sc.b⟩ →
      InNF fun _ σ => ∀ i j, LRatiosIn G σ A.μ0 i j := by
    rintro sc G rfl
    obtain ⟨hcm, -, hfd, hbc, -⟩ := hF C0 le_rfl D large₂ he hx hRec T R.toLevCh A.μ0 hS.core.lev G
    exact inNF_ratios hTR hS.core.lev G hcm hfd hbc
  exact key ch.sc ch.G hsc
end GlobalTheory.RowEx.RatioField
end
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.FiniteGKSum
open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology
section Sums
variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)
end Sums
section Closure
variable {D : D7} {V : HSp D}
end Closure
section Avg
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}
end Avg
end GlobalTheory.FiniteGKSum
namespace GlobalTheory.FiniteGKSum
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.SeriesToClosure
  GlobalTheory.FiniteGKSum in
theorem finite_sum_of_gKModule_maps : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := by
  intro hPr D θ V S M hθ τ φ hφ hT ⟨W, hWf, hφW, hWK⟩
  haveI := hWf
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hT
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hE'
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P' (M.fr_unit τ) hP'
    (M.fr_gram τ) hJ' _ _ (M.σ τ) σ' (M.ds τ) hD'
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hPr.harishChandraModules (M.ds τ)
  have hP := M.fr_unit τ
  have hJ := M.fr_gram τ
  have hx' : ∀ x, HasTypeAll (lieSet (M.ε τ)) (UJset (M.ε τ)) (M.σ τ) (res θ V τ (M.fr τ) φ x) := fun x =>
    hasTypeAll_transport _ H' (M.H τ) _ (M.σ τ) (gramAt D V τ) (Jm (M.ε τ)) (M.fr τ) (isUnit_gram hP' hJ') hP hJ U
      hU (fun g => φ (x * atTau θ V τ g)) (hasTypeAll_iff.2 (hx x))
  choose Sx hS hc v ℓ C h using hx'
  have hZ : ∀ e, KFinFun (M.ε τ) e →
      avg θ V τ (M.ε τ) (M.fr τ) e φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) := by
    intro e he
    obtain ⟨m, a, c, ha, hQ, hA⟩ := exists_rank_one hθ hP hJ hσ he
    choose T hT hTv using fun j => exists_gkMap hθ hP hJ hσ hφ hS hc h (hA j)
    refine ⟨m, T, fun j => ⟨a j, mem_kFin_iff.2 (ha j)⟩, hT, funext fun x => ?_⟩
    have h1 := (moves_avg hθ hP hJ hσ he φ x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 1 (one_mem_UJ _)

    simp only [res_one hθ hP, sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (ha j))).hasSum)
    simp only [Finset.sum_apply, hTv]
    exact h2
  have hk : Continuous fun k : KG (M.ε τ) => atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hmem : φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W := by
    haveI : FiniteDimensional ℂ (gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W : Submodule ℂ _) :=
      Submodule.finiteDimensional_of_le inf_le_right
    refine mem_of_approx fun K hK δ hδ => ?_
    obtain ⟨e, he, hap⟩ := GlobalTheory.T.exists_compactFinite_approxIdentity _ (M.ε τ) (GA D V)
      (fun x k => φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ)))
      (hφ.cont.comp (continuous_fst.mul (hk.comp continuous_snd))) K hK δ hδ
    refine ⟨avg θ V τ (M.ε τ) (M.fr τ) e φ, ⟨hZ e he, avg_mem hθ hP hJ hWK hφ.cont hφW he⟩, fun x hxK => ?_⟩
    have h4 : φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK (1 : KG (M.ε τ)) * M.fr τ)) = φ x := res_one hθ hP φ x
    have h3 := hap x hxK
    rw [h4] at h3
    exact h3
  obtain ⟨m, T, p, hT, hsum⟩ := hmem.1
  exact ⟨m, T, p, hT, hsum⟩
end GlobalTheory.FiniteGKSum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.gKModule_map_finite_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := by
  first | exact @_root_.GlobalTheory.FiniteGKSum.finite_sum_of_gKModule_maps | exact _root_.GlobalTheory.FiniteGKSum.finite_sum_of_gKModule_maps | (intros; apply _root_.GlobalTheory.FiniteGKSum.finite_sum_of_gKModule_maps <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.GKGlobalise
theorem gelfandKirillov_local_to_global : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  intro hP D θ V S M hθ F ⟨haut, hcusp, hK, hL⟩
  have hHC := hP.harishChandraModules
  have hCW := hP.casselmanWallach
  have hk : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ = GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) := fun τ => (kFin_eq M τ).symm
  let e : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) :=
    fun τ => (LinearEquiv.ofEq _ _ (hk τ)).toLinearMap
  let T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M := F.compLinearMap e
  have hupd : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) τ (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      T₀ (Function.update u τ w) = F (Function.update (fun τ' => e τ' (u τ')) τ (e τ w)) := by
    intro u τ w
    show F (fun τ' => e τ' (Function.update u τ w τ')) = _
    congr 1
    funext τ'
    exact Function.apply_update (fun τ => e τ) u τ w τ'
  have hGK : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M ∅ 1 0 ∅ T₀ := by
    refine ⟨fun u => (haut _).toIsAutFun, fun u => (haut _).smooth, fun u => hcusp _,
      fun u => ?_, fun u => GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ (haut _),
      fun u k hk => by simp at hk, ?_, ?_⟩
    · rw [Measure.restrict_zero]; exact memLp_measure_zero
    · intro τ k hkm u w hw
      rw [hupd]
      exact hK τ k (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hkm) hkm (fun τ' => e τ' (u τ')) (e τ w) hw
    · intro τ X hX u w hw
      rw [hupd]
      refine hL τ X hX (fun τ' => e τ' (u τ')) (e τ w) ?_
      have hsm : (u τ : M.H τ) ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (GlobalTheory.SmVec.trRep (M.σ τ) (M.fr τ)) := by
        rw [← GlobalTheory.SmVec.sm_eq]; exact kFin_le_sm hHC M τ (u τ).2
      have h1 := GlobalTheory.SmVec.hasDerivAt_dRep hsm (X := X) hX
      show HasDerivAt _ (w : M.H τ) 0
      rw [hw]
      exact h1
  obtain ⟨U, N, hU, hTU⟩ := GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M ∅ 1 0 ∅ T₀ hGK
  obtain ⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩ :=
    GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU
  choose π dπ hπ using hπ
  have hmem : ∀ u, T₀ u ∈ LinearMap.range ι := fun u => by
    have ha := hGK.1 u
    obtain ⟨x, hx⟩ := (hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hGK.2.1 u, hGK.2.2.1 u, (hTU u).2⟩
    exact ⟨x, hx⟩
  let eι := LinearEquiv.ofInjective ι hinj
  let T₀' : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E :=
    eι.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)
  have hT₀' : ∀ u, ι (T₀' u) = T₀ u := fun u => by
    have h1 := congrArg Subtype.val (eι.apply_symm_apply ⟨T₀ u, hmem u⟩)
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  have hK' : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u) := by
    intro τ k hk u w hw
    apply hinj
    rw [(hπ τ).2.1 k (GlobalTheory.GKExt.kset_sub hk), hT₀', hT₀']
    have hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := GlobalTheory.GKExt.conj_back (M.fr_unit τ)
    have hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [hk']; exact hk
    refine (hGK.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl
    rw [hw]
    show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _
    rw [hk']
  have hL' : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M)
      (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) →
      T₀' (Function.update u τ w) = dπ τ X (T₀' u) := by
    intro τ X hX u w hw
    apply hinj
    rw [(hπ τ).2.2 X hX, hT₀', hT₀']
    have hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X := by
      funext y
      unfold dRep
      congr 1
      funext t
      show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _
      rw [GlobalTheory.GKExt.exp_conj_inv (M.fr_unit τ), GlobalTheory.GKExt.conj_back (M.fr_unit τ)]
    exact hGK.2.2.2.2.2.2.2 τ _ (GlobalTheory.GKExt.conj_mem_lieAt M τ hX) u w (by rw [hw, hd])
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'),
      (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g) := by
    intro τ τ' hne g hg g' hg'
    ext x
    apply hinj
    simp only [ContinuousLinearMap.comp_apply]
    rw [(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]
    funext y
    simp only [rTr, mul_assoc]
    exact congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))
  obtain ⟨TE, hTE1, hTE2, hTE3⟩ := GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK' hL'
  obtain ⟨hequiv, hcont⟩ := GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp
    (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3
  let T : Formalism.IndefR.Mult.MMap M := ι.compMultilinearMap TE
  have hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ := fun v u h => by
    show ι (TE v) = T₀ u
    rw [hTE1 v u h, hT₀']
  have hMult : Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T := by
    refine ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1, fun v k hk => by simp at hk, hequiv, hcont⟩
    exact GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by
      have h := (hrange (ι (TE v))).1 ⟨TE v, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont
  refine ⟨T, hMult, fun u => ?_⟩
  let ue : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M := fun τ => ⟨(u τ : M.H τ), by rw [← kFin_eq M τ]; exact (u τ).2⟩
  refine ⟨fun τ => ⟨(u τ : M.H τ), kFin_le_sm hHC M τ (ue τ).2⟩, fun τ => rfl, ?_⟩
  rw [hext _ ue (fun τ => rfl)]
  show F (fun τ => e τ (ue τ)) = F u
  congr 1
end GlobalTheory.GKGlobalise
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.gelfandKirillov_globalization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  first | exact @_root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | exact _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | (intros; apply _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
namespace GlobalTheory.KFinStruct
section Model
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.KFinVec
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
end Model
theorem kFinite_vector_structure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau),
    (∃ p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), p ≠ 0) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), M.rep τ g (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) ∧
    (∀ X ∈ lieAt V τ, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0) ∧
    ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤ := by
  intro hPr D V S M τ
  rw [kFin_eq]
  obtain ⟨h1, h2, h3⟩ := model hPr.kFiniteVectorsUnitary (M.ds τ) (M.fr_unit τ) (M.fr_gram τ)
  exact ⟨h1, fun g _ hg v => GlobalTheory.KFinVec.isKStableOn_kFinSub _ _ _ hg _ v.2, h2, h3⟩
end GlobalTheory.KFinStruct
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.structure_of_kFinite_vectors : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau),
    (∃ p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), p ≠ 0) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), M.rep τ g (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) ∧
    (∀ X ∈ lieAt V τ, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0) ∧
    ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤ := by
  first | exact @_root_.GlobalTheory.KFinStruct.kFinite_vector_structure | exact _root_.GlobalTheory.KFinStruct.kFinite_vector_structure | (intros; apply _root_.GlobalTheory.KFinStruct.kFinite_vector_structure <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopDict
open Matrix
theorem theta_parameter_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j X hG hX A A₁ AV AV₁ hA hA₁ hAV hAV₁
  exact dict_frames X _ _ _ _ _ _ hX.2.2.2.2.2.2.2 A A₁ (frSum AV AV₁)
    (hG.2.2.2.1.trans (funext fun τ => (hA τ).2.symm)) (hG.2.2.2.2.1.trans (funext fun τ => (hA₁ τ).2.symm))
    (hG.2.2.2.2.2 AV AV₁ hAV hAV₁)
end GlobalTheory.TopDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.theta_parameter_dictionary_bijective : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  first | exact @_root_.GlobalTheory.TopDict.theta_parameter_dictionary | exact _root_.GlobalTheory.TopDict.theta_parameter_dictionary | (intros; apply _root_.GlobalTheory.TopDict.theta_parameter_dictionary <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
noncomputable section
namespace GlobalTheory.ThetaRatPair
theorem theta_sum_omega_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine det_ne_zero_of_map W.J (B.emb w).1 fun h0 => det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ
end GlobalTheory.ThetaRatPair
end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

theorem _root_.GlobalTheory.T.theta_pair_sum_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @_root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | exact _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | (intros; apply _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational <;> assumption)
end
end
