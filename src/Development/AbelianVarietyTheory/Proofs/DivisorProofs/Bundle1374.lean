module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.archimedeanStandardChar_eq_exp_realLinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F, psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  first | exact @GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | exact GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | (intros; apply GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realTrace_archimedeanEmbeddings_nondegenerate : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → ∀ a : Ainf D.host.F, a ≠ 0 →
      ∃ b : Ainf D.host.F, (∑ ρ, θ ρ ((a * b) ⊗ₜ[D.host.F] (1 : D.host.E))).re ≠ 0 := by
  first | exact @GlobalTheory.InfTraceNondeg.realTrace_nondeg | exact GlobalTheory.InfTraceNondeg.realTrace_nondeg | (intros; apply GlobalTheory.InfTraceNondeg.realTrace_nondeg <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  first | exact @GlobalTheory.lift_mem_levVP | exact GlobalTheory.lift_mem_levVP | (intros; apply GlobalTheory.lift_mem_levVP <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.OneMapAllCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Hom.group in
theorem levR_congr (c : Coeff l) (hA : l.A = 1) {p q : (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ a, p.1 a - q.1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR p y y' ↔ levR q y y' := by
  have e : ∀ a, Xo.univ.eta (p.1 a) = Xo.univ.eta (q.1 a) := fun a => by
    rw [← sub_add_cancel (p.1 a) (q.1 a), Xo.univ.eta_add, Xo.univ.eta_ker _ (h a), one_mul]
  have e1 : ∀ a, Xo.univ.etaA a = 1 := fun a => by
    have := Xo.univ.etaA_ker a
    rwa [hA, one_smul] at this
  unfold levR IsLevMove
  simp only [e, e1]

variable {G : Type} [Group G] {lev lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem rel_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g y y') =
      fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev' g y y' := by
  funext S _ _ g y y'
  exact propext (levR_congr c hA (h g) y y')

theorem actLev_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    actLev (Xo := Xo) c lev = actLev c lev' := by
  funext g
  unfold actLev
  rw [rel_congr c hA h]

theorem second_level_eq_one {c : Coeff l} {n : ℕ} {Tup : Type} {dδ : Tup → DeltaDat Xo c n} (h : CovPin Xo c dδ) (t : Tup) :
    l.A = 1 := by
  have h1 := (h t).1.1.2.2
  rw [(h t).2.1] at h1
  exact Nat.dvd_one.1 h1

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def TypeCoprime : Prop :=
  ∀ PP ∈ R.Pg, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal






def LevUnique (i : Fin D.R.m) : Prop :=
  ∀ lev lev' : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev' →
      ∀ g a, lev g a - lev' g a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La)

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

variable {T R κ v₀ O ph}

variable (T R κ v₀ O ph)

end GlobalTheory.OneMapAllCompare
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftResInj

theorem resInjL_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.models_inf → RecTie.ResInjL (RecTie.toLiftReal R F tupT hm hTop hinj) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hθ i w hw h0
  let U : MMap (R.MW i (sg0 D A)) := PiTensorProduct.lift.symm w
  have hU : U ∈ Mult.Mult R.θ (R.MW i (sg0 D A)) _ _ := (Mult.mem_multT _ _ _ _ w).1 hw
  have hT : U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
      have e := LinearMap.congr_fun h0 (PiTensorProduct.tprod ℂ v)
      have e2 : w (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
      rw [PiTensorProduct.map_tprod] at e2
      show (PiTensorProduct.lift.symm w : MMap (R.MW i (sg0 D A))) (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0
      exact e2)
  have e3 : PiTensorProduct.lift U = w := LinearEquiv.apply_symm_apply _ w
  rw [← e3, hT]
  exact map_zero _

end GlobalTheory.LiftResInj

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsTransportF (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (ψ : AddChar (AF F) ℂ) {ξ : AF F ⊗[F] E} {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {κ : Type} [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ)
    (ω : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ))
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ)) : Prop :=
  ∀ (a : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA)) (b : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) (g : GAF σ JS) (h : GAF σ JT),
    mtF σ JT h = a.1.1 → mtF σ JS g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ schA F κ, om (a, b) Φ ∈ schA F κ ∧ thetaTr F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr F co ψ Φ)

end GlobalTheory.WeilSchrodinger

end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
noncomputable section

namespace GlobalTheory.TypeBase

def piCongrLeftMul {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) : (∀ a, P (e a)) ≃* ∀ b, P b :=
  { Equiv.piCongrLeft P e with
    map_mul' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.mul_apply, Equiv.piCongrLeft_apply_apply] }

theorem piCongrLeftMul_apply {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) (f : ∀ a, P (e a)) (a : α) :
    piCongrLeftMul P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

def bcEquiv {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A ≃+* B) :
    GL n A ≃* GL n B :=
  MonoidHom.toMulEquiv (Formalism.UG.bc (f : A →+* B)) (Formalism.UG.bc (f.symm : B →+* A))
    (by ext g i j; simp [Formalism.UG.bc]) (by ext g i j; simp [Formalism.UG.bc])

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A →+* B)
    (g : GL n A) (i j : n) : ((Formalism.UG.bc f g : GL n B) : Matrix n n B) i j = f ((g : Matrix n n A) i j) := rfl

theorem bc_mem_unip_iff {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A ≃+* B) (g : GL (Fin r) A) :
    Formalism.UG.bc (f : A →+* B) g ∈ unip B r ↔ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.unitri r A := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := h1 (show j.val < i.val from hij)
      rw [bc_apply] at h
      exact f.injective (h.trans (map_zero f).symm)
    · have h := h2 i
      rw [bc_apply] at h
      exact f.injective (h.trans (map_one f).symm)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [bc_apply, h1 (show id j < id i from hij), map_zero]
    · rw [bc_apply, h2 i, map_one]

theorem edgeSum_bc {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A →+* B) (g : GL (Fin r) A) :
    edgeSum supEdge (Formalism.UG.bc f g) = f (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag (g : Matrix (Fin r) (Fin r) A)) := by

  simp only [edgeSum, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag, supEdge, bc_apply, map_sum, apply_ite f, map_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr

theorem det_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

theorem exists_char {Ks : Type} [Field Ks] (σ : Ks →+* ℂ) (p : ℕ) [Fact p.Prime] {ζ : Ks} (hζ : IsPrimitiveRoot ζ p)
    {k : Type} [CommRing k] (f : ZMod p ≃+* k) (χ : AddChar k ℂ) :
    ∃ ψ : AddChar (ZMod p) Ks, ∀ x, σ (ψ x) = χ (f x) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hz : χ (f 1) ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero,
      AddChar.map_zero_eq_one]
  obtain ⟨k, -, hk⟩ := (hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one hz
  have hc : (ζ ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨AddChar.zmodChar p hc, fun x => ?_⟩
  rw [AddChar.zmodChar_apply, map_pow, map_pow, hk, ← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_zmod_val]

theorem baseLevelCharacter_eq_prod_superdiagonalSum {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) (g) (hg : g ∈ (P0 Pg r ψ).H) :
    (((P0 Pg r ψ).chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : Pg, ψ PP.1 (edgeSum supEdge (g PP)) := by
  unfold P0 LevelP.ofLocal
  dsimp only
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, Units.coe_prod]
  rfl

theorem mem_lastZeroOrthImageSubspace_iff {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (g : G0 Pg r) :
    g ∈ (P0 Pg r ψ).H ↔ ∀ PP, g PP ∈ unip (kP PP.1) r := by
  simp [P0, LevelP.ofLocal, Subgroup.mem_pi]

end GlobalTheory.TypeBase

namespace GlobalTheory.TypeBase

theorem base_level_unip_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.grp_chiW → (∀ k, ∃ ζ : Ks, IsPrimitiveRoot ζ (D.host.g k)) → ∀ (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), ∃ (t : LevelGroup D.host ≃* G) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) Ks), (∀ u v, R.eG (t u) (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) ∧ (∀ v, ψ v ≠ 1) ∧ (∀ u, t u ∈ (F.lvl false).P ↔ u ∈ levelU D.host) ∧ ∀ u (h : t u ∈ (F.lvl false).P), algebraMap Ks D.what₂.LL (psiU ψ u) = ((F.lvl false).ψ ⟨t u, h⟩ : D.what₂.LLˣ) ∧ ∀ i, (R.FW i).chi (t u) = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hlevels hchiW hζ e iso
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let φ : LevelGroup D.host ≃* G0 R.Pg D.R.r :=
    (MulEquiv.piCongrRight fun v : Sq D.host => (bcEquiv (n := Fin D.R.r) (iso v))).trans
      (piCongrLeftMul (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e)
  have hφ : ∀ u v, φ u (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v) := fun u v =>
    piCongrLeftMul_apply (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e
      (fun v => Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) v
  have hex : ∀ v : Sq D.host, ∃ ψ : AddChar (ZMod (D.host.g v.1)) Ks,
      ∀ x, D.what₂.embLL (algebraMap Ks D.what₂.LL (ψ x)) = ψ0 (e v).1 (iso v x) := by
    intro v
    obtain ⟨ζ, hz⟩ := hζ v.1
    exact exists_char (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)) _ hz (iso v) (ψ0 (e v).1)
  choose ψ hψ using hex
  refine ⟨φ.trans R.eG.symm, ψ, fun u v => ?_, fun v h1 => ?_, fun u => ?_, fun u h => ?_⟩
  · show R.eG (R.eG.symm (φ u)) (e v) = _
    rw [MulEquiv.apply_symm_apply, hφ]
  · apply hgen (e v).1 (e v).2
    ext y
    obtain ⟨x, rfl⟩ := (iso v).surjective y
    rw [← hψ v x, h1, AddChar.one_apply, map_one, map_one, AddChar.one_apply]
  · show φ u ∈ (R.levR F false).H ↔ _
    rw [hlev, mem_lastZeroOrthImageSubspace_iff, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.levelU, Subgroup.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact (e.forall_congr fun v => by rw [hφ, bc_mem_unip_iff]).symm
  · have hm : φ u ∈ (P0 R.Pg D.R.r ψ0).H := by rw [← hlev]; exact h
    have hun : ∀ PP, φ u PP ∈ unip (kP PP.1) D.R.r := (mem_lastZeroOrthImageSubspace_iff _ _ _ _).1 hm
    refine ⟨?_, fun i => ?_⟩
    · apply D.what₂.embLL.injective
      have e1 : (R.levR F false).chi ⟨φ u, h⟩ =
          Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩) := rfl
      have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
          ((X.chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (g PP)) := by
        rintro X rfl g hg
        exact baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ g hg
      have h2 := key _ hlev (φ u) h
      rw [e1, Units.coe_map] at h2
      rw [show D.what₂.embLL (((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (φ u PP)) from h2]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.psiU, map_prod]
      refine Finset.prod_equiv e (by simp) fun v _ => ?_
      rw [hψ, hφ, edgeSum_bc, RingEquiv.coe_toRingHom]
    · apply Units.ext
      apply D.what₂.embLL.injective
      have hg : R.eG ((φ.trans R.eG.symm) u) = φ u := R.eG.apply_symm_apply _
      rw [hchiW i, hg, Finset.prod_eq_one (fun PP _ => by rw [det_unip (hun PP), map_one, Units.val_one]),
        Units.val_one, map_one]

end GlobalTheory.TypeBase
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.star_rows_level_character_eq_lifts_level_character : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (g : GA D (Yc D 0)), star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) g) = levChi _ (R.βY 0) (R.dat0 (R.levL F b (sg0 D A))) g := by
  first | exact @GlobalTheory.ChiStarLev.star_levChi_levR | exact GlobalTheory.ChiStarLev.star_levChi_levR | (intros; apply GlobalTheory.ChiStarLev.star_levChi_levR <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idelicCharacter_eq_prod_unramifiedValue_zpow : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (m : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ Q ∈ S, χ.UnrAt Q ∧ Valued.v (ι (finPart D (x : AE D)) Q) = WithZero.exp (-m Q)) → (∀ Q, Q ∉ S → ι (finPart D (x : AE D)) Q = 1) → ((c x : Circle) : ℂ) = ((∏ Q ∈ S, χ.val Q ^ m Q : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.CharUnramVal.char_eq_prod_val_zpow | exact GlobalTheory.CharUnramVal.char_eq_prod_val_zpow | (intros; apply GlobalTheory.CharUnramVal.char_eq_prod_val_zpow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.complex_points_parts_distinct_types_orthogonal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → ∀ p q : A3.fam3.base3.Ix, p ≠ q → ∀ x ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ∀ y ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ⟪x, y⟫_ℂ = 0 := by
  first | exact @GlobalTheory.Div.parts_orth_complex | exact GlobalTheory.Div.parts_orth_complex | (intros; apply GlobalTheory.Div.parts_orth_complex <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.level_rows_eq_type_vectors_of_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toCx3 F).EEl false = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P0 F.ψ0 ∧ (R.toCx3 F).EEl true = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P1 F.ψ1 := by
  first | exact @GlobalTheory.LevelRows3.eel_eq_typeSp3 | exact GlobalTheory.LevelRows3.eel_eq_typeSp3 | (intros; apply GlobalTheory.LevelRows3.eel_eq_typeSp3 <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.thetaVectorUpToUnits_thMoved_of_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' (B.thMoved a b L L') := by
  first | exact @GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum | exact GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum | (intros; apply GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum <;> assumption)
end
