module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle205
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundedCommutantVacua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle591
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle586
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle598
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle330
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle365
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle238
import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle600
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.ChainFr (Fr ptF IsVacF)

noncomputable section

namespace GlobalTheory.ArchRec.LieAtPlace

variable {D : D7}


open scoped ComplexOrder in
theorem cart_isCartanInv {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have h2 : (A.fr τ)⁻¹ * A.fr τ = 1 := mul_eq_one_comm.1 h1
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJ' := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hG : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ]; unfold Fr.cart
    calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : A.cart τ * A.cart τ = 1 := by
    unfold Fr.cart
    calc _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← A.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (A.fr_unit τ))

theorem exists_fr {V : HSp D} {τ : D.what₂.Tau} {s fr : Mn V.rank} {ε : Fin V.rank → Bool}
    (h : IsFrameOf (gramAt D V τ) s ε fr) : ∃ A : Fr V, A.ε τ = ε ∧ A.fr τ = fr ∧ A.cart τ = s := by
  classical
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V).1
  refine ⟨⟨Function.update A.ε τ ε, Function.update A.fr τ fr, fun ρ => ?_, fun ρ => ?_⟩, by simp, by simp, ?_⟩
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self]; exact h.1
    · rw [Function.update_of_ne e]; exact A.fr_unit ρ
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self, Function.update_self]; exact h.2.1
    · rw [Function.update_of_ne e, Function.update_of_ne e]; exact A.fr_gram ρ
  · simp [Fr.cart, h.2.2]

theorem pure_rename {ι κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : κ → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (h : ∀ k, A (e k) = A' k) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial κ ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), MvPolynomial.rename_X, hX, hX', hp, h]

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem ptF_rename (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) (τ : D.what₂.Tau)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : LPol T.rank S.rank) :
    ptF ψ θ A B f (MvPolynomial.rename (fun s => (τ, s)) P) =
      ptAt ψ θ S T τ (A.cart τ) (B.cart τ) (A.fr τ)⁻¹ (B.fr τ)⁻¹ f P := by
  have hS := cart_isCartanInv A
  have hT := cart_isCartanInv B
  refine pure_rename (fun v Q => ?_) (fun v Q => ?_) _ (fun k => rfl) P
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ τ _ hS hT τ _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h

theorem ins_one {a b : ℕ} (τ : D.what₂.Tau) (p : LPol b a) :
    GlobalTheory.Chain.RealIt.GlueProof.ins τ (fun _ => 1) p = (MvPolynomial.rename (fun s => (τ, s)) p : PolF D b a) := by
  rw [GlobalTheory.Chain.RealIt.GlueProof.ins_apply]
  simp [GlobalTheory.Chain.RealIt.GlueProof.rest]

theorem derAll_of_one (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {sS frS : Mn S.rank} {εS : Fin S.rank → Bool} {sT frT : Mn T.rank} {εT : Fin T.rank → Bool}
    (hS : IsFrameOf (gramAt D S τ) sS εS frS) (hT : IsFrameOf (gramAt D T τ) sT εT frT)
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {γ : ℝ → GA D S × GA D T} (hγ : QuadGen ψ θ τ ω γ)
    {f₀ : WO S T → ℂ} (h0 : IsThetaFunO ψ S T f₀) (v0 : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f₀) (n0 : f₀ ≠ 0)
    {P P' : LPol T.rank S.rank}
    (hd : ∀ z, HasDerivAt (fun t : ℝ => ω (γ t) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P) z)
      (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P' z) 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f) :
    DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P') := by
  obtain ⟨k, c, z, z', lam, hq⟩ := hγ
  choose L hL using GlobalTheory.T.exists_fockPolynomial_operator_heisenberg_derivative D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have hc := GlobalTheory.T.fockVectors_at_one_realPlace_over_vacuum D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have key : ∀ g, IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g →
      DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P)
        (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P)) := fun g hg vg => by
    have h := hq _ ((hc g hg vg).1 P)
    simp only [hL _ g hg vg] at h
    have e : ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P) =
        (∑ i, c i • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g (L (z i) (L (z' i) P))) +
          lam • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ptAt, map_add (f := _), map_sum, map_smul]
    rw [e]
    exact h
  have e : P' = (∑ i, c i • L (z i) (L (z' i) P)) + lam • P := by
    refine ((hc f₀ h0 v0).2 n0).1 (funext fun w => (hd w).unique ?_)
    simpa using (key f₀ h0 v0).1 1 w
  rw [e]
  exact key f hf hv

theorem lieAt_of_vacAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ aS aT : ℚ, HasInfExp D χS τ aS → HasInfExp D χT τ aT → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → LieAt ψ θ τ ω εS frS εT frT aS aT (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) := by
  intro D ψ θ S T χS χT ω τ hθ hW aS aT haS haT sS frS εS sT frT εT hS hT f hf hv
  have hψ := hW.std
  obtain ⟨A, rfl, rfl, rfl⟩ := exists_fr hS
  obtain ⟨B, rfl, rfl, rfl⟩ := exists_fr hT
  obtain ⟨f₀, h0, n0⟩ := GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua.exists_isVac_ne_zero hψ hθ (cart_isCartanInv A) (cart_isCartanInv B)
  have hl := GlobalTheory.T.lieAction_fockOperators_scalars_trace D S T A B θ ψ χS χT ω f₀ τ aS aT hθ hW haS haT h0
  have hg := GlobalTheory.T.weilGenerator_quadratic_oneParameter_at_place D ψ θ S T χS χT ω τ hθ hW
  refine ⟨fun X hX P => ?_, fun Y hY P => ?_⟩
  · refine derAll_of_one hψ hθ hS hT (hg.1 X hX) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.1 X hX (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockS_ins, ← map_smul, ← map_add (f := _), ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · refine derAll_of_one hψ hθ hS hT (hg.2 Y hY) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.2 Y hY (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockT_ins, ← map_smul, ← map_add (f := _), ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1] at h
    exact h

end GlobalTheory.ArchRec.LieAtPlace

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx


theorem _root_.GlobalTheory.T.exists_halfCosetRepresentatives_card_dvd : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  first | exact @GlobalTheory.HalfCosetCount.halfCoset_reps_card | exact GlobalTheory.HalfCosetCount.halfCoset_reps_card | (intros; apply GlobalTheory.HalfCosetCount.halfCoset_reps_card <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepExists

theorem exists_lastStep_intertwiner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ItX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hLev hFam hMod hW
  obtain ⟨-, It, hIt⟩ := GlobalTheory.T.definite_lastStep_real_intertwiner D G Pl0 T A Ks R hLev hFam hMod hW.ωX hW.vX
  exact ⟨It, fun t => hIt t⟩

end GlobalTheory.Twist.LastStepExists
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeEval
section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem postOn_eq_of_mem (R : RealDat D A Ks) (F : Face D A) {S : MMap (MP R)} (hS : S ∈ EP R F) :
    postOn (MP R) R.e0 S = S :=
  sub_eq_zero.mp (LinearMap.mem_ker.mp hS.2)

theorem rg_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (φ : L2X X) (h2 : star (Gd.Rg (star φ)) = φ) :
    Gd.Rg (star φ) = star φ :=
  calc Gd.Rg (star φ) = star (star (Gd.Rg (star φ))) := (star_star _).symm
    _ = star φ := by rw [h2]

theorem ev_sub (R : RealDat D A Ks) (v₀ : (MP R).Vec) (S S' : MMap (MP R)) (y : GA D (Yc D 0)) :
    ev (MP R) v₀ (S - S') y = ev (MP R) v₀ S y - ev (MP R) v₀ S' y := by
  simp [ev_apply]
  rfl

end SlopeTestRemainingChoices

theorem evalTieT_of_levelMatch : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hE Gd t ht hConj hRow
  obtain ⟨c, hc, hsm⟩ := GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep hDS R F X h hLev hGrp hMod hHost hE
  let v₀ : (MP R).Vec := fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by
    simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(c τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  have hne : ∀ τ, (v₀ τ : (MP R).H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨σ, red, hA, -, -⟩ := id hRow
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  refine ⟨c0, Formalism.IndefR.AutomorphicEvaluation.evalTieT_of _ _ _ _ X Gd _ t c0 v₀ hnorm ?_ ?_ ?_⟩
  · intro S hS
    obtain ⟨hmem, hint, -⟩ := hN v₀ hnorm S hS
    have hHH := GlobalTheory.T.conj_rowEvaluation_translate_mem_rowSpace R F X h hLev hGrp hMod hHost hE t c v₀ ht hA hc hv₀ S hS _ hmem.coeFn_toLp
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hS.1 _ hmem.coeFn_toLp
    rw [postOn_eq_of_mem R F hS] at h1
    have hfix : Gd.Rg (star (hmem.toLp _)) = star (hmem.toLp _) :=
      rg_fix X Gd _ (Lp.ext (h1.trans hmem.coeFn_toLp.symm))
    refine ⟨⟨hmem.toLp _, Submodule.mem_inf.mpr ⟨hHH, LinearMap.mem_ker.mpr (sub_eq_zero.mpr hfix)⟩⟩,
      hmem.coeFn_toLp, ?_⟩
    show ‖(hmem.toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hmem]
    exact hint
  · intro Φ
    have hF : star (Φ : L2X X) ∈ goodSub X Gd := Φ.2
    have hfix : Gd.Rg (star (Φ : L2X X)) = star (Φ : L2X X) :=
      sub_eq_zero.mp (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hF).2)
    obtain ⟨S, hSM, hSF⟩ := GlobalTheory.T.conjRow_eq_translatedEvaluation_cuspFormMap hDS R F X h hLev hGrp hMod hHost hE t c v₀ ht hConj hc hv₀ (Φ : L2X X)
      (Submodule.mem_inf.mp hF).1
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hSM _ hSF
    rw [hfix, star_star] at h1
    have hz := GlobalTheory.T.multiplicityMap_eq_zero_of_translated_evaluation_ae_zero R F X h hLev hGrp hMod t v₀ hne S hSM _ rfl (by
      filter_upwards [h1, hSF] with x h1x h2x
      refine (ev_sub R v₀ _ _ _).trans ?_
      exact sub_eq_zero.mpr (h1x.symm.trans h2x))
    exact ⟨S, ⟨hSM, LinearMap.mem_ker.mpr hz⟩, hSF⟩
  · intro S hS h0
    obtain ⟨-, hint, hzero⟩ := hN v₀ hnorm S hS
    have hI : ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = 0 := by
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [h0] with x hx
      have : ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = 0 := hx
      simp [this]
    rw [hI] at hint
    have hre : (ipM (MP R) R.ν0 R.fd0 S S).re = 0 := by
      rcases mul_eq_zero.mp hint.symm with h' | h'
      · exact absurd h' hc0.ne'
      · exact h'
    exact hzero hre

end GlobalTheory.SeeEval
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx


theorem _root_.GlobalTheory.T.halfLattice_charSum_detects_nsmul_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  first | exact @GlobalTheory.CharSumHalf.charSum_detects_multiple | exact GlobalTheory.CharSumHalf.charSum_detects_multiple | (intros; apply GlobalTheory.CharSumHalf.charSum_detects_multiple <;> assumption)
end
