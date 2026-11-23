module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.ncard_rationalPoints_translatedCompact_le_pow : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (Ω : Set (GA D V)), IsCompact Ω → ∃ N : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ u ∈ GinfC V, ∀ y : GA D V, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = x * u * o}.Finite ∧ (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = x * u * o}.ncard : ℕ) : ℝ) ≤ C * normInf θ V u ^ N := by
  first | exact @GlobalTheory.RatCount.ncard_rational_le | exact GlobalTheory.RatCount.ncard_rational_le | (intros; apply GlobalTheory.RatCount.ncard_rational_le <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  first | exact @GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood | exact GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood | (intros; apply GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  first | exact @GlobalTheory.HolDict.PrincLev.principal_level | exact GlobalTheory.HolDict.PrincLev.principal_level | (intros; apply GlobalTheory.HolDict.PrincLev.principal_level <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dictionary_character_trivial_on_principal_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k ∈ T.Kf ((i : ℕ) + 1) σ, T.mu ((i : ℕ) + 1) σ k = 1 := by
  first | exact @GlobalTheory.MuLevel.mu_eq_one_of_mem_level | exact GlobalTheory.MuLevel.mu_eq_one_of_mem_level | (intros; apply GlobalTheory.MuLevel.mu_eq_one_of_mem_level <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finiteGroup_rightAction_components : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → ∃ mv : (T.U ((i : ℕ) + 1) σ).Comp → G → (T.U ((i : ℕ) + 1) σ).Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 = x) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = mv (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g := by
  first | exact @GlobalTheory.CompAct.exists_action_components | exact GlobalTheory.CompAct.exists_action_components | (intros; apply GlobalTheory.CompAct.exists_action_components <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.AdTh.CoefExt

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (φ : K →+* K')
  {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]

theorem map_actP (B : I → GL (Fin n) K) (F : Pol K I n) :
    MvPolynomial.map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) := by
  have h1 : (MvPolynomial.map φ).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc φ (B τ))).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map φ (trAct B F) = trAct (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) :=
    congrArg (fun ψ : Pol K I n →+* Pol K' I n => ψ F) h1
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

def up (v : VV K lam) : VV K' lam := ⟨MvPolynomial.map φ (v : Pol K I n), GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ v.2⟩

theorem up_sum (a : VVIdx lam → K) (v : VVIdx lam → VV K lam) :
    up φ lam (∑ j, a j • v j) = ∑ j, φ (a j) • up φ lam (v j) := by
  apply Subtype.ext

  simp only [up, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eq_C_mul, map_mul, map_C]

theorem exists_coord (v : VV K' lam) : ∃ a : VVIdx lam → K', v = ∑ j, a j • up φ lam (bVV K lam j) := by
  have hv : v ∈ Submodule.span K' (Set.range (bVV K' lam)) := by rw [(bVV K' lam).span_eq]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam j
    refine ⟨fun k => φ ((bVV K lam).repr ⟨F, hF⟩ k), ?_⟩
    rw [← up_sum, (bVV K lam).sum_repr]
    exact Subtype.ext ((bVV_coe _ _ _).trans hj)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [← Finset.sum_add_distrib, add_smul]⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun j => c * a j, by simp [Finset.smul_sum, mul_smul]⟩

theorem up_rhoVr {E : Type} [Field E] [NumberField E] [NumberField K] [NumberField K'] (emb : I → E →+* K)
    (g : GL (Fin n) E) (v : VV K lam) :
    up φ lam (rhoVr emb lam g v) = rhoVr (fun τ => φ.comp (emb τ)) lam g (up φ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map φ (actP lam (invTrK (embGL emb g)) (v : Pol K I n)) =
    actP lam (invTrK (embGL (fun τ => φ.comp (emb τ)) g)) (MvPolynomial.map φ (v : Pol K I n))
  rw [map_actP]
  rfl

variable {φ lam} {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

theorem equivariant (hE : ∀ v, c' (up φ lam v) = c₀ v) (T : W →ₗ[ℂ] W) (S : VV K lam →ₗ[K] VV K lam)
    (S' : VV K' lam →ₗ[K'] VV K' lam) (hS : ∀ v, up φ lam (S v) = S' (up φ lam v)) (hT : ∀ v, c₀ (S v) = T (c₀ v))
    (v : VV K' lam) : c' (S' v) = T (c' v) := by
  obtain ⟨a, rfl⟩ := exists_coord φ lam v

  simp only [map_sum, map_smul, map_smulₛₗ, ← hS, hE, hT, RingHom.id_apply]

theorem span_top (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hs : Submodule.span ℂ (Set.range fun j => c₀ (bVV K lam j)) = ⊤) : Submodule.span ℂ (Set.range c') = ⊤ := by
  refine top_le_iff.1 (hs ▸ Submodule.span_mono ?_)
  rintro _ ⟨j, rfl⟩
  exact ⟨_, hE _⟩

theorem linearIndependent (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) {m : ℕ} (b : Fin m → VV K' lam) (hb : LinearIndependent K' b) :
    LinearIndependent ℂ fun j => c' (b j) := by
  classical
  letI : Algebra K' ℂ := σ'.toAlgebra
  choose a ha using fun j => exists_coord φ lam (b j)
  have h1 : LinearIndependent K' a := by
    refine LinearIndependent.of_comp (Fintype.linearCombination K' fun k => up φ lam (bVV K lam k)) ?_
    convert hb using 1
    funext j
    rw [ha j]
    simp [Fintype.linearCombination_apply]
  have h2 : LinearIndependent ℂ fun j => algebraMap K' ℂ ∘ a j := linearIndependent_algebraMap_comp_iff.2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k))
    (LinearMap.ker_eq_bot'.2 fun g hg => funext (Fintype.linearIndependent_iff.1 hli g (by simpa [Fintype.linearCombination_apply] using hg)))
  have e : (fun j => c' (b j)) = ⇑(Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k)) ∘ fun j => algebraMap K' ℂ ∘ a j := by
    funext j
    rw [ha j]

    simp only [map_sum, map_smulₛₗ, hE, Function.comp_apply, Fintype.linearCombination_apply]
    rfl
  rw [e]
  exact h3

theorem pairVr_extremal {E : Type} [Field E] [NumberField E] [NumberField K] [StarRing K] (emb : I → E →+* K)
    (v : VV K lam) (hv : (v : Pol K I n) = ten fun τ => extremal K n (lam τ)) : pairVr emb lam 1 v v = 1 := by
  have hG : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    simp [gramKd]
  have h := pairingExtremal_holds K I n lam (fun _ => 1) 1 (fun τ => by simp)
  rw [polyAction_one₂] at h
  rw [pairVr, pairK_apply, hG, hv, h]

end GlobalTheory.AdTh.CoefExt

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem inner_of_coefTie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : Formalism.L2.DIV.CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ : J →* ℂˣ} {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : Formalism.L2.DIV.VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (v w : Formalism.L2.DIV.VV D.what₂.LL lam) :
    inner ℂ (c0 v) (c0 w) = D.what₂.embLL (pair v w) := by
  obtain ⟨e, -, he, hp, -⟩ := h
  have hi := P.coef_pair (e.symm v) (e.symm w)
  rwa [he, he, ← hp, e.apply_symm_apply, e.apply_symm_apply] at hi



theorem coefMap_norm_equivariant_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ‖O.c0' O.hw‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, O.c0' (rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (O.c0' v)) ∧ Submodule.span ℂ (Set.range O.c0') = ⊤ ∧ ∀ (m : ℕ) (b : Fin m → VsV D i O.c'.F), LinearIndependent O.c'.F b → LinearIndependent ℂ (fun j => O.c0' (b j)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hσ := hP.lift.field
  have hE : ∀ v, O.c0' (CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT.mapL i
  refine ⟨?_, ?_, CoefExt.span_top (W := (R.cV i).W) hE h3,
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩
  · have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hP.lift.std.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up O.jL (lamV D i) v = O.hw := by
      apply Subtype.ext
      have hw := hP.io.1
      unfold hwOK at hw
      refine Eq.trans ?_ hw.symm
      show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
      rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      exact Formalism.L2.DIV.map_extremal _ _ _
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [← hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  · intro γ γE hγ v
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm
    rw [rhoM, dite_eq_left hu, hγE, hemb]
    exact CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _
      (CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v

end GlobalTheory.AdTh

end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilInner

theorem integral_mul_conj_self {G : Type} [MeasurableSpace G] (ν : Measure G) {f : G → ℂ} (hf : Measurable f) :
    ∫ w, f w * conj (f w) ∂ν = ((∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν).toReal : ℂ) := by
  have e : ∀ w, f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 2
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_mul_conj {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] {f g : G → ℂ}
    (hf : Measurable f) (hg : Measurable g) (bf : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (bg : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C) :
    Integrable (fun w => f w * conj (g w)) ν := by
  obtain ⟨C, hC⟩ := bf
  obtain ⟨C', hC'⟩ := bg
  refine Integrable.of_bound (hf.mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable (C * C')
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))

theorem inner_eq_of_meanSquare {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    (P : (G → ℂ) → Prop) (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (c : ℂ) f, P f → P (c • f))
    (hm : ∀ f, P f → Measurable f) (hb : ∀ f, P f → ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C)
    (A : Module.End ℂ (G → ℂ)) (hA : ∀ f, P f → P (A f))
    (hu : ∀ f, P f → ∫⁻ w, ‖A f w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν) {f g : G → ℂ} (hf : P f) (hg : P g) :
    ∫ w, A f w * conj (A g w) ∂ν = ∫ w, f w * conj (g w) ∂ν := by
  have hI : ∀ f g, P f → P g → Integrable (fun w => f w * conj (g w)) ν := fun f g hf hg =>
    integrable_mul_conj ν (hm f hf) (hm g hg) (hb f hf) (hb g hg)
  have hN : ∀ f, P f → ∫ w, A f w * conj (A f w) ∂ν = ∫ w, f w * conj (f w) ∂ν := fun f hf => by
    rw [integral_mul_conj_self ν (hm _ (hA f hf)), integral_mul_conj_self ν (hm f hf), hu f hf]
  have ex : ∀ (c : ℂ) f g, P f → P g → ∫ w, (f + c • g) w * conj ((f + c • g) w) ∂ν =
      ∫ w, f w * conj (f w) ∂ν + conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν +
        c * conj c * ∫ w, g w * conj (g w) ∂ν := by
    intro c f g hf hg
    have i1 := hI f f hf hf
    have i2 := (hI f g hf hg).const_mul (conj c)
    have i3 := (hI g f hg hf).const_mul c
    have i4 := (hI g g hg hg).const_mul (c * conj c)
    have i12 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w))) ν := i1.add i2
    have i13 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w)) + c * (g w * conj (f w))) ν :=
      i12.add i3
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2,
      ← integral_add i12 i3, ← integral_add i13 i4]
    congr 1
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have key : ∀ c : ℂ, conj c * ∫ w, A f w * conj (A g w) ∂ν + c * ∫ w, A g w * conj (A f w) ∂ν =
      conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν := by
    intro c
    have h := hN _ (hadd f _ hf (hsmul c g hg))
    rw [map_add (f := _), map_smul, ex c _ _ (hA f hf) (hA g hg), ex c f g hf hg, hN f hf, hN g hg] at h
    linear_combination h
  have h1 := key 1
  have h2 := key I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (I / 2) * h2 + (1 / 2 : ℂ) *
    (∫ w, A f w * conj (A g w) ∂ν - ∫ w, A g w * conj (A f w) ∂ν - ∫ w, f w * conj (g w) ∂ν +
      ∫ w, g w * conj (f w) ∂ν) * Complex.I_mul_I

theorem om_inner : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ p f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∫ w in 𝓕, om p f w * conj (om p f' w) ∂μ = ∫ w in 𝓕, f w * conj (f' w) ∂μ := by
  intro D ψ V W χV χW om hom μ 𝓕 hc p f f' hf hf'
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  exact inner_eq_of_meanSquare (μ.restrict 𝓕) (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) (fun _ h => h.cont.measurable)
    (fun _ h => GlobalTheory.OrientedHeis.theta_bounded hom.std h) (om p) (hom.om_pres p)
    (hom.om_unit μ 𝓕 hc.1 hc.2.1 p) hf hf'

end GlobalTheory.WeilInner
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePull

theorem unimod_comap_frame : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).Unimod := by
  intro D V fr Λ hG hΛ v
  have hstar : ∀ x : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = x) → ∃ b : 𝓞 D.host.E, (b : D.host.E) = star x := by
    rintro x ⟨b, rfl⟩
    exact ⟨Formalism.L2.Pj.barE D b, Formalism.L2.Pj.barE_eq_star D b⟩
  have hcT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 = fr.1ᴴ := by
    ext i j
    rfl
  have key : ∀ w : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star ((fr.1 *ᵥ w) i) * V.gram i j * (fr.1 *ᵥ v) j = ∑ j, star (w j) * v j := by
    intro w
    have e1 : ∀ x y : Fin V.rank → D.host.E,
        ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
      intro x y
      simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      rfl
    rw [e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← hcT, hG, Matrix.one_mulVec]
    rfl
  have hsum : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (w j) * v j) = ∑ j, star (v j) * w j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hsum' : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (v j) * w j) = ∑ j, star (w j) * v j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  change fr.1 *ᵥ v ∈ Λ ↔ ∀ w, fr.1 *ᵥ w ∈ Λ → ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star (v j) * w j
  rw [hΛ.2]
  constructor
  · intro H w hw
    have := hstar _ (H _ hw)
    rwa [key, hsum] at this
  · intro H x hx
    have hw : fr.1 *ᵥ ((fr⁻¹).1 *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := hstar _ (H ((fr⁻¹).1 *ᵥ x) (by rw [hw]; exact hx))
    rw [hsum', ← key, hw] at this
    exact this

end GlobalTheory.FramePull
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevelOpen

theorem isOpen_levG : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsOpen {g : GfC V | (g : GA D V) ∈ levG V β L} := by
  intro D V β L
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨U, hU, hle⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L
  have h1 : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := hU.preimage continuous_subtype_val
  exact Subgroup.isOpen_mono (H₂ := (levG V β L).subgroupOf (GfC V)) (fun g hg => (hle g.1 hg g.2).1) h1

end GlobalTheory.LevelOpen
end

section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_hom_eq_of_tangent_eq : ∀ (k : Type) [Field k] [CharZero k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (f f' : A ⟶ B) [IsMonHom f] [IsMonHom f'], (∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ f = v ≫ f') → f = f' := by
  first | exact @GlobalTheory.LieFaithful.hom_eq_of_tangent_eq | exact GlobalTheory.LieFaithful.hom_eq_of_tangent_eq | (intros; apply GlobalTheory.LieFaithful.hom_eq_of_tangent_eq <;> assumption)
end
