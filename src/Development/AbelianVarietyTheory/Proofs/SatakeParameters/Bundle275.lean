module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle271
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle082
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle251
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle250
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.LetterDescent

open TensorProduct

variable {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁] [AddCommGroup D₂]
  [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (F : Type) [Field F] [Algebra LL F]

def baseBil (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] F ⊗[LL] D₃ :=
  ((LinearMap.baseChangeHom LL F D₂ D₃) ∘ₗ β).liftBaseChange F

theorem baseBil_tmul (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (a b : F) (x : D₁) (y : D₂) :
    baseBil F β (a ⊗ₜ x) (b ⊗ₜ y) = (a * b) ⊗ₜ β x y := by
  simp [baseBil, LinearMap.liftBaseChange_tmul, TensorProduct.smul_tmul']

theorem baseBil_left (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₁ : Module.End LL D₁) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β (f₁ x) y = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β (f₁.baseChange F w) z = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add (f := _), LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

theorem baseBil_right (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₂ : Module.End LL D₂) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β x (f₂ y) = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β w (f₂.baseChange F z) = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add (f := _), LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

end GlobalTheory.LetterDescent

namespace GlobalTheory.LetterDescent

open TensorProduct

theorem exists_letter_tensor_map {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (m₁ : U →+* Module.End LL D₁)
    (m₂ : U →+* Module.End LL D₂) (m₃ : U →+* Module.End LL D₃) (F : Type) [Field F] [Algebra LL F]
    (τ : U →+* F) (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (h₁ : ∀ c x y, β (m₁ c x) y = m₃ c (β x y))
    (h₂ : ∀ c x y, β x (m₂ c y) = m₃ c (β x y)) :
    ∃ Φ : GlobalTheory.Pst.Letter m₁ F τ ⊗[F] GlobalTheory.Pst.Letter m₂ F τ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ,
      ∀ x y, Φ (GlobalTheory.Pst.letterMk m₁ F τ x ⊗ₜ GlobalTheory.Pst.letterMk m₂ F τ y) =
        GlobalTheory.Pst.letterMk m₃ F τ (β x y) := by
  let C : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ :=
    (baseBil F β).compr₂ (GlobalTheory.Pst.letterQ m₃ F τ)
  have hmem : ∀ (c : U) (v : F ⊗[LL] D₃),
      GlobalTheory.Pst.letterQ m₃ F τ ((m₃ c).baseChange F v - τ c • v) = 0 := by
    intro c v
    rw [← LinearMap.mem_ker, GlobalTheory.Pst.ker_letterQ]
    exact Submodule.mem_iSup_of_mem c ⟨v, rfl⟩
  have k₂ : GlobalTheory.Pst.letterKer m₂ F τ ≤ LinearMap.ker C.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    ext w
    simp only [C, LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul, baseBil_right F β (m₂ c) (m₃ c) (h₂ c), LinearMap.zero_apply]
    rw [← map_smul, ← map_sub]
    exact hmem c _
  let C₂ := (GlobalTheory.Pst.letterKer m₂ F τ).liftQ C.flip k₂
  have k₁ : GlobalTheory.Pst.letterKer m₁ F τ ≤ LinearMap.ker C₂.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun q => ?_
    obtain ⟨z, rfl⟩ := GlobalTheory.Pst.letterQ_surjective m₂ F τ q
    change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (((m₁ c).baseChange F - τ c • LinearMap.id : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₁) w) z) = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, baseBil_left F β (m₁ c) (m₃ c) (h₁ c)]
    exact hmem c _
  refine ⟨TensorProduct.lift ((GlobalTheory.Pst.letterKer m₁ F τ).liftQ C₂.flip k₁), fun x y => ?_⟩
  change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (1 ⊗ₜ x) (1 ⊗ₜ y)) = _
  rw [baseBil_tmul, mul_one]
  rfl

end GlobalTheory.LetterDescent
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Pst.EnlargeParam

open GlobalTheory.Pst.EnlargeCoeff Module

section General

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L₁ L₂ : FinExt l}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
  [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
  {ρ₁ : Representation ↥L₁.1 ↥(GK Bw.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK Bw.Kw) V₂}
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]

theorem wdRep_iso (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = (a : Om l))
    {f : V₁ →ₗ[ℚ_[l]] V₂} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v)) (hfs : ∀ (a : ↥L₁.1) v, f (a • v) = s a • f v)
    {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁) (hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v))
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v)
    (hdim : finrank ℂ (WDSpace P ι ρ₁) = finrank ℂ (WDSpace P ι ρ₂)) :
    (wdRep P ι Bw h hj ρ₁).Iso (wdRep P ι Bw h hj ρ₂) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have hT : ∀ (a : ↥L₁.1) (x : ↥(Dpst P ρ₁)), dQ P hf (a • x) = s a • dQ P hf x := fun a x =>
    Subtype.ext (tensQ_smul P s hfs a x.1)
  letI := algC ι L₁
  letI := algC ι L₂
  let Φ := chg (mulD P ρ₁) (mulD P ρ₂) ℂ (urC ι) s (fun a => congrArg ι (hs a)) (dQ P hf) hT (dQ_mulD P hf)
  have hΦρ : ∀ σ y, Φ (wdRho P ι Bw h hj ρ₁ σ y) = wdRho P ι Bw h hj ρ₂ σ (Φ y) := fun σ y =>
    chg_letterMap _ _ _ _ _ _ _ _ _ _ (weilD_mulD Bw h P ρ₁ hj σ) _ (weilD_mulD Bw h P ρ₂ hj σ)
      (dQ_weilD P Bw h hf σ) y
  have hΦN : ∀ y, Φ (wdN P ι ρ₁ y) = wdN P ι ρ₂ (Φ y) := fun y =>
    chg_letterMap _ _ _ _ _ _ _ _ _ _ (monD_mulD P ρ₁) _ (monD_mulD P ρ₂)
      (fun x => Subtype.ext (tensQ_onB P f _ x.1)) y
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ j, b j • dQ P hf (dQ P (hπ j) x) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, coe_dQ]
      exact (sum_tensQ P b π hsum x.1).symm
    have hms := map_sum (AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂))
      (fun j => b j • dQ P hf (dQ P (hπ j) x)) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hms
    rw [hx, hms]
    refine Submodule.sum_mem _ fun j _ => ?_
    change wdMk P ι ρ₂ ((Dpst P ρ₂).module.toSMul.smul (b j) (dQ P hf (dQ P (hπ j) x))) ∈ Φ.range
    rw [wdMk_smul]
    exact Submodule.smul_mem _ _ ⟨wdMk P ι ρ₁ (dQ P (hπ j) x), chg_mk _ _ _ _ _ _ _ _ _ _⟩
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact IsFrobSS.iso (GlobalTheory.TwistParamAbove.isFrobSS_wdRep P ι Bw h hj ρ₁)
    (GlobalTheory.TwistParamAbove.isFrobSS_wdRep P ι Bw h hj ρ₂) (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩) hΦρ hΦN

end General

theorem wdPst_enlarge {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1) :
    IsPst P (Bw.repE L₁ r₁) →
    wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) =
      wdPst P ι Bw h hj (Bw.repE L₁ r₁) := by
  intro hV₁
  have hV₂ := GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hV₁
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨n, b, π, hπ, hsum⟩ := exists_decomp hL (m := m)
  have hf : ∀ g v, incV hL m (Bw.repE L₁ r₁ g v) =
      Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g (incV hL m v) :=
    fun g v => incV_mulVec hL _ v
  have hπ' : ∀ (j : Fin n) (g : ↥(GK Bw.Kw)) (v : Fin m → ↥L₂.1),
      π j (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g v) = Bw.repE L₁ r₁ g (π j v) :=
    fun j g v => hπ j (r₁ (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L₁.1) v
  have hdim : finrank ℂ (WDSpace P ι (Bw.repE L₁ r₁)) =
      finrank ℂ (WDSpace P ι (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :=
    (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₁ _ _ hV₁).trans ((Module.finrank_fin_fun _).trans
      ((Module.finrank_fin_fun _).symm.trans (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₂ _ _ hV₂).symm))
  rw [wdPst_of_isPst ι Bw h hj hV₂, wdPst_of_isPst ι Bw h hj hV₁]
  exact (WD.sound (wdRep_iso P ι Bw h hj (IntermediateField.inclusion hL).toRingHom (fun _ => rfl) hf
    (incV_smul hL) b π hπ' hsum hdim)).symm

end GlobalTheory.Pst.EnlargeParam
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertFormFix.mul_idem_of_trivOutside {E : Type} [Field E] [NumberField E] [IsCMField E] (F : Subfield E)
    (hF : F = maximalRealSubfield E) (P : HeightOneSpectrum (𝓞 E))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : NG.OverPl P v) (x : AL E)
    (hx : ∀ w, w ≠ v → compAt E w x = 0) :
    ((GlobalTheory.AdelicU.singleFin (P.under (𝓞 F)) 1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) *
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  subst hF
  have hvv : P.under (𝓞 (maximalRealSubfield E)) = v := HeightOneSpectrum.ext hv
  subst hvv
  have hx' : x = GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x := by
    have h0 := GlobalTheory.AL_eq_zero_of_compAt E (x - GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x)
      (fun w => by
        rw [RingHom.map_sub, RingHom.map_mul]
        by_cases hw : w = P.under (𝓞 (maximalRealSubfield E))
        · rw [hw, GlobalTheory.CongSplit.compAt_idemAt_self, one_mul, sub_self]
        · rw [GlobalTheory.CongSplit.compAt_idemAt_ne E _ hw, hx w hw, zero_mul, sub_zero])
    exact (sub_eq_zero.1 h0)
  conv_rhs => rw [hx']
  rw [RingEquiv.map_mul]
  congr 1

theorem GlobalTheory.InertFormFix.finPart_mul_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ x : AL D.host.E, (∀ w, w ≠ v → compAt D.host.E w x = 0) → Formalism.L2.Theta.finPart D f * (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  intro D hF P e f hP v hv x hx
  have hf := GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hP rfl
  subst hf
  exact GlobalTheory.InertFormFix.mul_idem_of_trivOutside D.host.F hF P v hv x hx



theorem GlobalTheory.InertFormFix.suppF_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (Q : Formalism.IndefR.principalLevelFrame.RowPsi V n), Formalism.IndefR.principalLevelFrame.StdPsi hF Q → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ κ : GAf D.host.E n, TrivOutside {v} κ → Formalism.IndefR.Mult.SuppF V f (Q.ψ κ) := by
  intro D hF V n Q hQ P e f hP v hv κ hT
  obtain ⟨⟨β, β', hββ', hβ'β, hmat⟩, -⟩ := hQ
  rw [GlobalTheory.SphTrans.suppF_iff f (Q.into κ), hmat κ]
  have hT' : ∀ w, w ≠ v → (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E w) = 1 :=
    fun w hw => hT w (by simpa using hw)
  change Formalism.L2.Theta.finPart D f • (β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1) = β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1
  set M : Matrix (Fin n) (Fin n) (AL D.host.E) := κ.1.1 with hMdef
  set K := M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hKdef
  have hcore : ∀ a b, Formalism.L2.Theta.finPart D f * (K - 1) a b = (K - 1) a b := by
    intro a b
    have hx : ∀ w, w ≠ v → compAt D.host.E w (M a b - (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) = 0 := by
      intro w hw
      have h1 := congrFun (congrFun (hT' w hw) a) b
      rw [Matrix.map_apply] at h1
      rw [RingHom.map_sub, h1]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingHom.map_zero, sub_zero]
    have h2 := GlobalTheory.InertFormFix.finPart_mul_of_trivOutside D hF P e f hP v hv _ hx
    have e3 : (K - 1) a b = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm (M a b -
        (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) := by
      rw [Matrix.sub_apply, hKdef, Matrix.map_apply, RingEquiv.map_sub]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingEquiv.map_one]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingEquiv.map_zero]
    rw [e3, h2]
  have hK : Formalism.L2.Theta.finPart D f • (K - 1) = K - 1 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, hcore]
  have e1 : β * K * β' - 1 = β * (K - 1) * β' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hββ']
  rw [e1]
  conv_rhs => rw [← hK]
  rw [Matrix.mul_smul, Matrix.smul_mul]

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SameParahoric

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hci : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (N : ℕ)
    (hN : ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1)
    (hglob : ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) =
      μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))
    (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ) :
    ξ d = μ (Units.map c.toRingHom.toMonoidHom d) := by
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toRingHom.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toRingHom.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toRingHom.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

theorem isParahoricVec_of_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  intro L _ _ _ s r t W _ _ π ξ μ c hc hci hμ ⟨N, hN⟩ hglob u hvec
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous c hc
  have hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1 := fun x hx =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx
  have hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 →
      c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun x hx =>
    (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  intro h hK hlow x hx
  obtain ⟨hi1, hi2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff h).1 hK
  let g := Matrix.GeneralLinearGroup.map c.symm.toRingHom h
  have hg : ∀ a b, g.val a b = c.symm (h.val a b) := fun a b => rfl
  have hg' : ∀ a b, (g⁻¹).val a b = c.symm ((h⁻¹).val a b) := fun a b => rfl
  have hpara : NG.ParaRT s r g := by
    refine ⟨GlobalTheory.ConjParahoric.mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (hi1 a b))
      (fun a b => hg' a b ▸ hle _ (hi2 a b)), fun a b ha hb => ?_⟩
    rw [hg]
    have ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a := by ext; simp; omega
    have eb : Fin.castAdd t (⟨b.val, hb⟩ : Fin r) = b := by ext; simp
    have := hlow ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩
    rw [ea, eb] at this
    exact hlt _ this
  have hDD : c.symm (x : s.w.adicCompletion L) = NG.detDD s r g := by
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self (GlobalTheory.ConjParahoric.lowerEquiv r t), hx]
    refine (RingHom.map_det c.symm.toRingHom _).trans ?_
    congr 1
  have key := hvec g hpara (Units.map c.symm.toRingHom.toMonoidHom x) hDD
  have hpp : Matrix.GeneralLinearGroup.map c.toRingHom g = h :=
    Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
  have hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom x) = x :=
    Units.ext (c.apply_symm_apply _)
  rw [hpp, GlobalTheory.SameParahoric.eq_comp s ξ μ c hc hci hμ N hN hglob, hcc] at key
  exact key

end GlobalTheory.SameParahoric
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → GlobalTheory.SplitWeil.IsTame μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = (μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))⁻¹) → ∀ u : W, u ≠ 0 → (∀ g h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → h.val = (g⁻¹).val.transpose → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom h) u = ((ξ d : ℂˣ) : ℂ) • u) → ∃ u' : W, u' ≠ 0 ∧ GlobalTheory.ThetaGL.IsParahoricVec μ π u' := by
  first | exact @GlobalTheory.ConjParahoric.exists_parahoricVec | exact GlobalTheory.ConjParahoric.exists_parahoricVec | (intros; apply GlobalTheory.ConjParahoric.exists_parahoricVec <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.genericGerm_differentialForm_pullback_dominant : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  first | (exact @GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (exact GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (intros; apply GlobalTheory.HodgeCoh.formGermI_res_mapOver  <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.normalisedFamily_standardBases_integrality_alt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  first | exact @GlobalTheory.KerStd.normalisedFamily_standardBases_integrality | exact GlobalTheory.KerStd.normalisedFamily_standardBases_integrality | (intros; apply GlobalTheory.KerStd.normalisedFamily_standardBases_integrality <;> assumption)
end
