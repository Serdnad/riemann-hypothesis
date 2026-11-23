module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenve
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle578
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle580
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricFor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfAutomorphismMapsParahoric
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle573
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle571
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.additiveCharacter_eq_of_common_unipotentLevel_eigenvector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (p m : ℕ) (θ : GAf L n ≃* GAf L n) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (F : GAf L n → V) (F' : GAf L n → V') (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (ψ₀ ψ₀' : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), p.Prime → s.Above p → m.Coprime p → 2 ≤ r → r ≤ n → FrameAut θ → F ≠ 0 → F' ≠ 0 → NG.IsPsi0 s ψ₀ → NG.IsPsi0 s ψ₀' → NG.LevelUni J χ s r ψ₀ ξ → NG.LevelUni J' χ' s r ψ₀' ξ' → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ : J', Eig F' κ (χ' κ : ℂˣ)) → (∀ κ, TrivOutside {s.v} κ → NG.UniRT s r (s.loc n κ) → ∃ c c' : ℂ, Eig F (θ κ) c ∧ Eig F' (θ κ) c' ∧ c ^ m = c' ^ m) → ∀ y, Valued.v y ≤ 1 → ψ₀ y = ψ₀' y := by
  first | exact @GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | exact GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | (intros; apply GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.finrank_algebraicModularForms_complexification : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (W W' : Type) [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') (J : Subgroup (GAf L n)) (χ : J →* Kˣ), WtMatch e ρ ρ' → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional K (NX.TypeSpF L n K ρ J χ) → Module.finrank ℂ (NG.TypeSp ρ' J (cx e χ)) = Module.finrank K (NX.TypeSpF L n K ρ J χ) := by
  first | exact @GlobalTheory.LevCmp.finrank_typeSp_cx | exact GlobalTheory.LevCmp.finrank_typeSp_cx | (intros; apply GlobalTheory.LevCmp.finrank_typeSp_cx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.productLevel_eq_of_local_agreement : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  first | exact @GlobalTheory.LevCmp.levEq_of_agree | exact GlobalTheory.LevCmp.levEq_of_agree | (intros; apply GlobalTheory.LevCmp.levEq_of_agree <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel


theorem _root_.GlobalTheory.T.matchingMatrices_of_baseChange_representation : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  first | exact @GlobalTheory.BcMatch.bcmatch_main | exact GlobalTheory.BcMatch.bcmatch_main | (intros; apply GlobalTheory.BcMatch.bcmatch_main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  first | exact @GlobalTheory.LevShapeBound.bound | exact GlobalTheory.LevShapeBound.bound | (intros; apply GlobalTheory.LevShapeBound.bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.isProductLevel_definiteFormsRealisationAtTwist : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  first | exact @GlobalTheory.LevProd.main | exact GlobalTheory.LevProd.main | (intros; apply GlobalTheory.LevProd.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  first | exact @GlobalTheory.LevParaLoc.levelPara_loc | exact GlobalTheory.LevParaLoc.levelPara_loc | (intros; apply GlobalTheory.LevParaLoc.levelPara_loc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  first | exact @GlobalTheory.LevCmp.galOf_of_orderDvd | exact GlobalTheory.LevCmp.galOf_of_orderDvd | (intros; apply GlobalTheory.LevCmp.galOf_of_orderDvd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.mem_parahoric_of_scalar_action_on_ramifiedParahoricForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  first | exact @GlobalTheory.ParaRigid.mem_para_of_eig | exact GlobalTheory.ParaRigid.mem_para_of_eig | (intros; apply GlobalTheory.ParaRigid.mem_para_of_eig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.splitPlace_eq_of_automorphism_maps_parahoric : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s s' s₁ : SplitPlace L) (θ : GAf L n ≃* GAf L n), 0 < r → r < n → s'.v = s.v → s₁.v = s.v → FrameAut θ → (∀ κ, TrivOutside {s.v} κ → NG.ParaRT s₁ r (s₁.loc n κ) → NG.ParaRT s r (s.loc n (θ κ)) ∧ NG.ParaRT s' r (s'.loc n (θ κ))) → s' = s := by
  first | exact @GlobalTheory.ParaOpp.splitPlace_eq_of_para | exact GlobalTheory.ParaOpp.splitPlace_eq_of_para | (intros; apply GlobalTheory.ParaOpp.splitPlace_eq_of_para <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel


theorem _root_.GlobalTheory.T.weightMatrices_match_of_coeffSpace_iso :
    ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K)
    (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀]
    [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀)
    (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam),
    (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) →
    ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam),
    (∀ γ x, T' (ρ' γ x) =
      rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T' x)) →
    GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' :=
  @GlobalTheory.CoefMatch.wtMatch_of_coef
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up

theorem cenTw_read {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩ : P.q.Over))).nd)).coeff ((sgTw x N).iso g)) → (sideTw x N).cen μ c = x.s.cen μ c0 := by
  intro μ c c0 h
  have e : (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)) = (((by with_unfolding_all exact (c :)) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))) : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)) :=
    MonoidAlgebra.coeff_injective (Finsupp.ext fun g => (by with_unfolding_all exact ((h g) :)))
  have e2 : c0 = ((by with_unfolding_all exact (c :)) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))) := Subtype.ext e
  exact (by with_unfolding_all exact ((congrArg (x.s.cen μ) e2).symm :))

theorem readTw_ex {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) :
    ∃ r : ReadPk m (sideTw x N), r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) := (by with_unfolding_all exact (
  (GlobalTheory.T.adelicRowsReading_transport_laterHeckeGaloisStage x (nTw x N) x.fits.grp (fitsTw x N).grpAt (fitsTw x N).cen m hc hh (sgTw x N) (sideTw x N) rfl HEq.rfl
    (cenTw_read x N)) :))

theorem jMtTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin) :
    ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1 := by
  cases m with
  | mk z intersectionNumber_baseChange exAt inGeo Xg tr core eta W1 y tup t tA =>
    obtain rfl : z = datTw x N := hm
    have e : HEq t.lf.jMt x.m.t.lf.jMt := (by with_unfolding_all exact ((hh.jMt.trans x.coh.jMt.symm) :))
    have e2 : t.lf.jMt = ((by with_unfolding_all exact (x.m.t.lf.jMt :)) : type_of% t.lf.jMt) := eq_of_heq ((by with_unfolding_all exact (e :)))
    intro μ h i y
    exact (by with_unfolding_all exact (((hp.jMt μ h i y).trans ((heq_of_eq (congrArg (fun φ : type_of% t.lf.jMt => φ μ i y) e2)).trans (x.pin.jMt μ h i y).symm)) :))

theorem eWTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin) :
    ∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y) := by
  cases m with
  | mk z intersectionNumber_baseChange exAt inGeo Xg tr core eta W1 y tup t tA =>
    obtain rfl : z = datTw x N := hm
    have e : HEq t.lf.eW x.m.t.lf.eW := (by with_unfolding_all exact ((hh.eW.trans x.coh.eW.symm) :))
    have e2 : t.lf.eW = ((by with_unfolding_all exact (x.m.t.lf.eW :)) : type_of% t.lf.eW) := eq_of_heq ((by with_unfolding_all exact (e :)))
    intro i y
    exact (by with_unfolding_all exact (((hp.eW i y).trans ((heq_of_eq (congrArg (fun φ : type_of% t.lf.eW => φ i y) e2)).trans (x.pin.eW i y).symm)) :))

theorem readTw : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)), m.z = datTw x N → m.Copy → m.Coh → ∃ r : ReadPk m (sideTw x N), r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) ∧ (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) ∧ (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) := by
  intro K B f T w P x N m hm hc hh
  have H := readTw_ex x N m hc hh
  refine H.elim fun r h => ?_
  exact Exists.intro r (And.intro h.1 (And.intro h.2 (And.intro (jMtTw x N m hm hh r h.1) (eWTw x N m hm hh r h.1))))

end GlobalTheory.HeightCounting.Up
end
end
