module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle335
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle294
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle585
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.BottomDeg

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}


open Classical in
theorem pureTensorO_scal_pm {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hs : ∀ τ, sS τ = 1 ∨ sS τ = -1) (ht : ∀ τ, sT τ = 1 ∨ sT τ = -1)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (ζ : D.what₂.Tau → ℂ) (hζ : ∀ τ, ‖ζ τ‖ = 1)
    (α : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T sS sT (fun τ => ζ τ • BS τ) BT f (MvPolynomial.monomial α 1) =
      (∏ τ, (if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) •
        pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial α 1) := by
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) (fun τ => ζ τ • BS τ) BT i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [GlobalTheory.FockScal.unitMap_smul _ _ (hz ρ),
      GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.FockScal.cplxO_pm (hs ρ) (ht ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f) :=
    fun _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f :=
    fun _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact GlobalTheory.FockScal.pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α


open Classical in
theorem scalar_exists {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (τ₀ : D.what₂.Tau) :
    ∃ C w : ℂ, (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) ∧
      ∀ (k : FVar D WW.rank A.rank →₀ ℕ) (h : GA D WW),
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h := by
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  obtain ⟨z', hz', -, h1, h2⟩ := GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ (neg A) τ₀ (Complex.exp Complex.I) he
  set ζ : D.what₂.Tau → ℂ := fun τ => if τ = τ₀ then Complex.exp Complex.I else 1 with hζdef
  have hζ : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) z') = ζ τ • (1 : Matrix (Fin (neg A).rank) (Fin (neg A).rank) ℂ) := by
    intro τ
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [hζdef, if_pos rfl, h1]
    · simp only [hζdef, if_neg hτ, h2 τ hτ, one_smul]
  have hζn : ∀ τ, ‖ζ τ‖ = 1 := fun τ => by
    by_cases hτ : τ = τ₀
    · simp only [hζdef, if_pos hτ, he]
    · simp only [hζdef, if_neg hτ, norm_one]
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet z' hz'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one WW _
  obtain ⟨C, hC⟩ : ∃ C : ℂ, om' (z', 1) (X.f t) = C • X.f t :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
      z' hz' 1 (one_mem _) (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1 (X.f t) hf hfock⟩

  have hop : ∀ k : FVar D WW.rank A.rank →₀ ℕ, _ := fun k =>
    GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
      X.rA.B (fun τ => ζ τ • X.rA.B τ) X.rW.s X.rW.s X.rW.B X.rW.B z' 1
      (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [hζ τ, Matrix.smul_mul, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.one_mul]) (X.f t) hf (MvPolynomial.monomial k 1)
  set w : ℂ := if (-X.rA.s τ₀ = 1 ↔ X.rW.s τ₀ = 1) then (Complex.exp Complex.I)⁻¹ else Complex.exp Complex.I with hw
  have hscal : ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      om' (z', 1) (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t)
        (MvPolynomial.monomial k 1)) =
        (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) •
          pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1) := by
    intro k
    rw [(hop k).2, hC, GlobalTheory.FiniteFock.pureTensorO_smul,
      pureTensorO_scal_pm (S := neg A) (T := WW) hψ hθ (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (fun τ => Or.inr (by rw [hsA])) (fun τ => Or.inl (hsW τ)) (X.f t) hf ζ hζn k,
      smul_smul]
    congr 2
    rw [Finset.prod_eq_single τ₀]
    · simp only [hζdef, if_pos rfl, hw]
    · intro ρ _ hρ
      simp only [hζdef, if_neg hρ, inv_one, ite_self, one_pow]
    · simp
  refine ⟨C, w, by rw [hw]; split_ifs; exacts [Or.inr rfl, Or.inl rfl], fun k h => ?_⟩
  set φ := pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1)
    with hφ
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ (neg A) WW _ _ om' hom φ (hop k).1
  have hker : ∀ g : GA D A, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g = thetaKO om' ((ofSgn true A).symm g) h φ :=
    fun g => by
      show thetaKO (X.ω t) g h φ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) φ 0
      rw [MulEquiv.apply_symm_apply]
      rfl
  have hleft : ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (γ * g) =
      X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro γ hγ g
    rw [hker, hker, map_mul]
    have := hK.1 _ ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])) 1 (one_mem _)
      ((ofSgn true A).symm g) h
    rwa [one_mul] at this
  have hright : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') =
      (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro g
    rw [hker, hker, map_mul, MulEquiv.symm_apply_apply]
    have := hK.2 z' 1 _ (hscal k) ((ofSgn true A).symm g) h
    rwa [mul_one] at this
  show ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m =
    _ * ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m
  calc _ = ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') ∂X.m :=
        (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A X.m X.fd hI.meas.1 hI.meas.2 _ hleft (ofSgn true A z')).symm
    _ = _ := by
        simp_rw [hright]
        exact integral_const_mul _ _

end GlobalTheory.BottomDeg

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) =
      AlgHom.id ℂ (MvPolynomial (ι × Fin N × Fin n) ℂ) := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X]
    obtain ⟨τ, a, b⟩ := p
    rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [Matrix.one_apply, hx]) (by simp),
      Finset.sum_eq_single b (fun y _ hy => by simp [Matrix.one_apply, hy]) (by simp)]
    simp
  exact congrArg (fun f => f P) key

theorem mul_conjT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    M * Matrix.conjTranspose M = 1 := Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 h

theorem map_conj_mul_conjT {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M * Matrix.conjTranspose M = 1) :
    M.map (starRingEnd ℂ) * Matrix.conjTranspose (M.map (starRingEnd ℂ)) = 1 := by
  have e := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
  convert e using 2
  ext a b
  simp [Matrix.conjTranspose_apply]

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem conj_invT_of_unitary' {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conjT_mul_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    Matrix.conjTranspose (compAt θ τ (Formalism.L2.Theta.mt V g)) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact h1

theorem om_pureTensorO_vac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (g : GA D A)
    (h : GA D WW) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ) :
    IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) ∧
    (X.ω t).toSgn true ((ofSgn true A).symm g, h)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac)
        (GlobalTheory.CompactHowe.substF (fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW h)).map (starRingEnd ℂ))
          (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW X.vac := hI.isVac.2.theta
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  set v : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW h) with hv
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * v τ) ((ofSgn true A).symm g) h
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hsW, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hBW, Matrix.mul_one, Matrix.one_mul]) X.vac hf P
  refine ⟨hop.1, ?_⟩
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B v _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ =>
    conj_invT_of_unitary' (conjT_mul_compAt hθ hX.std.1 g τ)
  rw [funext hunit] at key
  rw [e1, e2]
  exact key

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem isAlgebraic_compAt_of_mem_GQ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {γ : GA D V}
    (hγ : γ ∈ GQ V) (τ : D.what₂.Tau) (a b : Fin V.rank) :
    IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V γ) a b) := by
  obtain ⟨γ₀, h0⟩ := GlobalTheory.Member.exists_isRat_of_mem_GQ V hγ
  have key : compAt θ τ (Formalism.L2.Theta.mt V γ) a b = tauE D τ (γ₀.1 a b) := by
    unfold compAt Formalism.L2.Theta.mt
    rw [h0]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  first
    | exact h.algHom (starRingEnd ℂ).toRatAlgHom
    | exact IsAlgebraic.map (starRingEnd ℂ).toRatAlgHom h
    | exact (isAlgebraic_algHom_iff (starRingEnd ℂ).toRatAlgHom (starRingEnd ℂ).injective).2 h

end GlobalTheory.MovedJet

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealFockPos

variable {D : D7}

theorem det_ne_zero_of_frame {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) :
    G.det ≠ 0 ∧ B.det ≠ 0 := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h2
  exact ⟨right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one h2), right_ne_zero_of_mul_eq_one h2⟩

theorem mul_eq_mul_conj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.det ≠ 0) :
    A * B = B * (B⁻¹ * A * B) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.one_mul]

theorem scalar_identity (G H : ℂ) (hG : G ≠ 0) (hH : H ≠ 0) (e₁ e₂ : ℤ) (nS nT : ℕ) :
    (G ^ (-e₂ - (nT : ℤ)))⁻¹ * H ^ (e₁ - (nS : ℤ)) * (H ^ nS * G⁻¹ ^ nT) = G ^ e₂ * H ^ e₁ := by
  rw [inv_pow, ← zpow_natCast H, ← zpow_natCast G, ← zpow_neg G, ← zpow_neg G]
  calc G ^ (-(-e₂ - (nT : ℤ))) * H ^ (e₁ - (nS : ℤ)) * (H ^ (nS : ℤ) * G ^ (-(nT : ℤ)))
      = G ^ (-(-e₂ - (nT : ℤ))) * G ^ (-(nT : ℤ)) * (H ^ (e₁ - (nS : ℤ)) * H ^ (nS : ℤ)) := by ring
    _ = G ^ (-(-e₂ - (nT : ℤ)) + -(nT : ℤ)) * H ^ (e₁ - (nS : ℤ) + (nS : ℤ)) := by
      rw [← zpow_add₀ hG, ← zpow_add₀ hH]
    _ = G ^ e₂ * H ^ e₁ := by congr 2 <;> ring

theorem om_pureTensorO_pos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ + (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) (fun τ => (((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)⁻¹)ᵀ) P) := by
  intro D ψ θ S T χS χT om hom hθ BS BT hBS hBT a b ha hb e₁ e₂ he₁ he₂ f hf hv g hg h hh P
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (BS τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBS τ)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (BT τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBT τ)
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBS τ)
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBT τ)
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) h hh
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT g hg h hh (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) x y hx hy f hf hv
  have expT : ∀ τ, HasInfExp D (χT * (η ^ T.rank)⁻¹) τ ((-e₂ τ - T.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    push_cast; rw [he₂]; ring
  have expS : ∀ τ, HasInfExp D (χS * (η ^ S.rank)⁻¹) τ ((e₁ τ - S.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (ha τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    push_cast; rw [he₁]; ring
  have vx := hxv _ (fun τ => -e₂ τ - T.rank) expT
  have vy := hyv _ (fun τ => e₁ τ - S.rank) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) (fun _ => 1) (fun _ => 1) BT
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) g h (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  have fS : (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) =
      fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dS τ).2
  have fT : (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) =
      fun τ => BT τ * ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dT τ).2
  rw [hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, fS, fT,
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS _ BT _ f hf P]
  congr 1
  rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h)
  rw [Matrix.det_mul, Matrix.det_one] at inv'
  have h0 := left_ne_zero_of_mul_eq_one inv'
  rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv]
  exact scalar_identity _ _ g0 h0 (e₁ τ) (e₂ τ) S.rank T.rank

end GlobalTheory.RealFockPos

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (Am : Fr M) (Bx : Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
      IsStable θ M (fun g => ω (g, 1)) (algF ψ θ ε Am Bx) ∧ IsStable θ X (fun h => ω (1, h)) (algF ψ θ ε Am Bx) := by
  first | exact @GlobalTheory.AlgStable.algF_isStable | exact GlobalTheory.AlgStable.algF_isStable | (intros; apply GlobalTheory.AlgStable.algF_isStable <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωY → R.chain_vY → ∀ t k, k + 1 < D.R.m → ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ → IsLevelLift (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) g0 κ' → (levChi _ (R.βY k) (flagL (R.datYt t k R.triv)) κ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = (levChi _ (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)) κ')⁻¹ • R.vY t k := by
  first | exact @GlobalTheory.StepVecLaw.stepVec_lifts | exact GlobalTheory.StepVecLaw.stepVec_lifts | (intros; apply GlobalTheory.StepVecLaw.stepVec_lifts <;> assumption)
end
