module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelAllNonFreeUnreadEntries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelIntegratesFreeEntries
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle085
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  first | exact @GlobalTheory.LFun.isFrameAt_sumLat_blkGL | exact GlobalTheory.LFun.isFrameAt_sumLat_blkGL | (intros; apply GlobalTheory.LFun.isFrameAt_sumLat_blkGL <;> assumption)
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.RealCoordCusp

theorem normSq_det_UJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Complex.normSq (uMat g).det = 1 := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Formalism.REAL.Jm_mul_self ε)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h1 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h2 : star (uMat g).det * (uMat g).det = 1 := by
    have : (star (uMat g).det * (uMat g).det - 1) * (Formalism.REAL.Jm ε).det = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd h hJ
  have h3 : ((Complex.normSq (uMat g).det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h2
  exact_mod_cast h3

variable (I : AutInst)

abbrev Idx : Type := Σ _ : Fin I.n, Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)

def cBasis : Module.Basis (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) ℝ (InfinitePlace I.F → Fin I.n → ℂ) :=
  Pi.basis fun _ => Pi.basis fun _ => Complex.basisOneI

theorem card_eq : Fintype.card (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) = Fintype.card (Idx I) := by
  simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Formalism.L2.SG.Pf.Tau.card_infinite_places, Formalism.L2.SG.Pf.Tau.card_integral_basis]
  ring

def rho : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin (Fintype.card (Idx I)) → ℝ) :=
  ((cBasis I).reindex (Fintype.equivFinOfCardEq (card_eq I))).equivFun

theorem rho_isRealCoord : IsRealCoord I (rho I) := by
  intro x y
  simp only [rho, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply, dotProduct]
  rw [(Fintype.equivFinOfCardEq (card_eq I)).symm.sum_comp
    (fun s => (cBasis I).repr x s * (cBasis I).repr y s)]
  simp only [cBasis, Fintype.sum_sigma, Pi.basis_repr, Complex.coe_basisOneI_repr, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bQ : Module.Basis (Idx I) ℚ (Fin I.n → I.E) := Pi.basis fun _ => integralBasis I.E

def eB : Fin (Fintype.card (Idx I)) → Fin I.n → I.E := fun k => bQ I ((Fintype.equivFin (Idx I)).symm k)

theorem bQ_apply (p : Idx I) : bQ I p = Pi.single p.1 (integralBasis I.E p.2) := by
  simp [bQ, Pi.basis_apply]

theorem eB_isZBasis : IsZBasis I (eB I) := by
  refine ⟨((bQ I).linearIndependent.comp _ (Fintype.equivFin (Idx I)).symm.injective).restrict_scalars' ℤ, ?_⟩
  intro u
  constructor
  · intro hu
    have hm := Formalism.L2.SG.Pf.Tau.mem_integral_vectors I I.n u (fun k => ⟨⟨u k, hu k⟩, rfl⟩)
    rw [Formalism.L2.SG.Pf.Tau.t8O, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨fun k => c ((Fintype.equivFin (Idx I)).symm k), ?_⟩
    rw [← hc, ← (Fintype.equivFin (Idx I)).symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [eB, bQ_apply]
  · rintro ⟨z, rfl⟩ i
    rw [← mem_integralClosure_iff]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine zsmul_mem ?_ _
    rw [eB, bQ_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      rw [mem_integralClosure_iff, integralBasis_apply]
      exact (RingOfIntegers.basis I.E _).isIntegral_coe
    · exact zero_mem _

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bm (y : I.Ginf) : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (uMat (y v)⁻¹)).restrictScalars ℝ).comp (LinearMap.proj v)

theorem vec_eq (y : I.Ginf) (u : Fin I.n → I.E) : GlobalTheory.CuspGeo.vec I y u = bm I y (GlobalTheory.CuspGeo.vec I 1 u) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  simp [GlobalTheory.CuspGeo.vec, bm, h1]

theorem det_bm (y : I.Ginf) : LinearMap.det (bm I y) = 1 := by
  rw [bm, LinearMap.det_pi]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  exact normSq_det_UJ _

theorem gm_eq {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) :
    gm I ρ y e = LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) * gm I ρ 1 e := by
  ext i j
  rw [Matrix.mul_apply]
  change ρ (GlobalTheory.CuspGeo.vec I y (e j)) i = (LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) *ᵥ
    (fun k => ρ (GlobalTheory.CuspGeo.vec I 1 (e j)) k)) i
  rw [LinearMap.toMatrix'_mulVec]
  simp [vec_eq I y]

theorem det_gm {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) : (gm I ρ y e).det = (gm I ρ 1 e).det := by
  rw [gm_eq, Matrix.det_mul, LinearMap.det_toMatrix', LinearMap.det_conj, det_bm, one_mul]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def qm : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (I.P v)⁻¹).restrictScalars ℝ).comp (LinearMap.proj v)

def sw : (Fin I.n × InfinitePlace I.F → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun z := fun v i => z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem qm_injective : Function.Injective (qm I) := by
  intro x y h
  funext v
  have h0 := congrFun h v
  simp only [qm, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearMap.coe_restrictScalars, Matrix.toLin'_apply] at h0
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h2 := congrArg (fun w => I.P v *ᵥ w) h0
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2
  exact h2

theorem sw_injective : Function.Injective (sw I) := by
  intro x y h
  funext q
  exact congrFun (congrFun h q.2) q.1

theorem vec_one_bQ (p : Idx I) :
    GlobalTheory.CuspGeo.vec I 1 (bQ I p) = qm I (sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p)) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  have h2 : (fun i => I.φ v (bQ I p i)) = sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p) v := by
    funext i
    rw [bQ_apply, Pi.single_apply]
    change _ = Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p (i, v)
    rw [Formalism.L2.SG.Pf.Tau.placeCoordsBasis_apply]
    split_ifs with h
    · subst h; rfl
    · exact map_zero _
  simp only [GlobalTheory.CuspGeo.vec, Pi.one_apply, inv_one, h1, Matrix.one_mulVec]
  rw [h2]
  rfl

theorem det_gm_one_ne : (gm I (rho I) 1 (eB I)).det ≠ 0 := by
  have hli : LinearIndependent ℝ (fun j => (gm I (rho I) 1 (eB I))ᵀ j) := by
    have hf : LinearMap.ker ((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) = ⊥ :=
      LinearMap.ker_eq_bot.2 ((rho I).injective.comp ((qm_injective I).comp (sw_injective I)))
    have h := ((Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n).linearIndependent.map' _ hf).comp _
      (Fintype.equivFin (Idx I)).symm.injective
    have heq : (fun j => (gm I (rho I) 1 (eB I))ᵀ j) =
        ((⇑((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) ∘ ⇑(Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n)) ∘
          ⇑(Fintype.equivFin (Idx I)).symm) := by
      funext j
      funext i
      simp only [Matrix.transpose_apply, gm, Matrix.of_apply, Function.comp_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe]
      rw [eB, vec_one_bQ]
    rw [heq]
    exact h
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero

end GlobalTheory.RealCoordCusp


open GlobalTheory.RealCoordCusp in
theorem GlobalTheory.CuspGeo.covolume_const : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E)
    (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ),
    0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  intro I
  refine ⟨_, eB I, rho I, |(gm I (rho I) 1 (eB I)).det|, abs_pos.2 (det_gm_one_ne I), eB_isZBasis I,
    rho_isRealCoord I, fun y => by rw [det_gm]⟩
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem finM_eq_one_iff_mem_GinfC :
    ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V), finM V hn g = 1 ↔ g ∈ GinfC V := by
  intro D V n hn g
  subst hn
  have e0 : finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := by simp [finM]
  have e : (Formalism.L2.Theta.mt V g).map (toEAf D) = (finHom V g).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e0, e]
  constructor
  · intro h
    show finHom V g = 1
    apply Units.ext
    have hinj := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    apply Matrix.map_injective hinj
    show (finHom V g).val.map _ = (1 : Matrix _ _ _).map _
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro hk
    have h : finHom V g = 1 := hk
    have h2 : (finHom V g).val = 1 := by rw [h]; rfl
    rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.AdForm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPartIso

section Swap

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (φ : A →+* B) (h : Continuous φ) : Continuous (bc (n := Fin n) φ) :=
  Continuous.units_map _ (continuous_id.matrix_map h)

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') {g : GL (Fin n) A} (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' J' := by
  have hg' : cT σ g.1 * J * g.1 = J := hg
  have h2 := congrArg (fun M => M.map φ) hg'
  simp only [Matrix.map_mul, hJ] at h2
  have e1 : cT σ' (g.1.map φ) = (cT σ g.1).map φ := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, h]
  change cT σ' (g.1.map φ) * J' * g.1.map φ = J'
  rw [e1]; exact h2

def ujEquiv {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (σ : A →+* A) (σ' : B →+* B) (φ : A ≃+* B) (hc : Continuous φ) (hc' : Continuous φ.symm)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') : UJ σ J ≃ₜ* UJ σ' J' where
  toFun g := ⟨bc φ.toRingHom g.1, bc_mem _ _ φ.toRingHom h _ _ hJ g.2⟩
  invFun g := ⟨bc φ.symm.toRingHom g.1, bc_mem _ _ φ.symm.toRingHom (fun x => φ.injective (by
      change φ (σ (φ.symm x)) = φ (φ.symm (σ' x))
      rw [← h, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])) _ _
      (hJ ▸ Matrix.ext fun _ _ => φ.symm_apply_apply _) g.2⟩
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.symm_apply_apply _))
  right_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.apply_symm_apply _))
  map_mul' g h := Subtype.ext (map_mul (bc φ.toRingHom) g.1 h.1)
  continuous_toFun := ((continuous_bc φ.toRingHom hc).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_bc φ.symm.toRingHom hc').comp continuous_subtype_val).subtype_mk _

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

def swapR : R ⊗[F] E ≃+* E ⊗[F] R := (Algebra.TensorProduct.comm F R E).toRingEquiv

theorem continuous_swapR :
    @Continuous _ _ _ (tensTopL (F := F) (E := E) R) (swapR (F := F) (E := E) R) ∧
    @Continuous _ _ (tensTopL (F := F) (E := E) R) _ (swapR (F := F) (E := E) R).symm := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) R
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd R (E ⊗[F] R)
  haveI := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let L : R ⊗[F] E ≃ₗ[R] E ⊗[F] R :=
    { (swapR (F := F) (E := E) R).toAddEquiv with
      map_smul' := fun c y => by
        change swapR (F := F) (E := E) R (c • y) = c • swapR (F := F) (E := E) R y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl }
  exact ⟨IsModuleTopology.continuous_of_linearMap L.toLinearMap,
    IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [TopologicalSpace R] in
theorem swapR_sig (x : R ⊗[F] E) :
    Formalism.UG.sigR σ R (swapR R x) = swapR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def swapU : letI := tensTopL (F := F) (E := E) R; HA R σ J ≃ₜ* UPts σ J R :=
  letI := tensTopL (F := F) (E := E) R
  ujEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.UG.sigR σ R) (swapR R) (continuous_swapR R).1 (continuous_swapR R).2
    (swapR_sig R σ) (JR R J) (J.map (inclE (F := F) R)) (Matrix.ext fun _ _ => rfl)

end Swap

section Fin

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def finEquiv : finPts σ J ≃ₜ* GFin σ J where
  toFun g := projFin σ J g.1
  invFun y := ⟨ofFin σ J y, mem_finPts.2 (projInf_ofFin σ J y)⟩
  left_inv g := Subtype.ext (ext_inf_fin σ J ((projInf_ofFin σ J _).trans (mem_finPts.1 g.2).symm)
    (projFin_ofFin σ J _))
  right_inv y := projFin_ofFin σ J y
  map_mul' g h := map_mul (projFin σ J) g.1 h.1
  continuous_toFun := (continuous_projFin σ J).comp continuous_subtype_val
  continuous_invFun := (continuous_ofFin σ J).subtype_mk _

end Fin

theorem exists_finIso : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F); ∃ e : ↥(GfC V) ≃ₜ* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), ∀ g, (e g).1.1 = finM V hn g.1 := by
  intro D V n hn
  subst hn
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  exact ⟨(finEquiv D.sp.cm.sig V.gram).trans
    (swapU (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.sp.cm.sig V.gram), fun g => rfl⟩

end GlobalTheory.FinPartIso
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.exchangeToPositionOne_uniform_in_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ P σ l → (∀ u ∈ U, σ u v = v) → toOne ν σ P l v = comb e (fun g => l (σ g v)) ∧ l v = comb e' fun g => toOne ν σ P l (σ g v) := by
  first | exact @GlobalTheory.PosOne.toOne_uniform | exact GlobalTheory.PosOne.toOne_uniform | (intros; apply GlobalTheory.PosOne.toOne_uniform <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.not_sq_dvd_of_rationalPrimeSplitsCompletely : ∀ (E : Type) [Field E] [NumberField E] (T : ℕ), T.Prime → GlobalTheory.St.G.SplitsIn E T → ∀ w : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ w.asIdeal → ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} := by
  first | exact @GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn | exact GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn | (intros; apply GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.GelfandTwo

theorem sum_rhoStd_sq (n : ℕ) :
    ∑ a : Fin n, (Formalism.QuantumDeterminants.rhoStd n a : ℂ) * (Formalism.QuantumDeterminants.rhoStd n a : ℂ) = ((Formalism.BasicNotions.TH.rhoSq n : ℚ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.rhoStd, Formalism.BasicNotions.TH.rhoSq]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun i => (((n : ℂ) - 1) / 2 - (i : ℂ)) * (((n : ℂ) - 1) / 2 - (i : ℂ))) n]
  exact Finset.sum_congr rfl fun i _ => (sq _).symm

theorem gelfVal_two (n : ℕ) (lam : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal lam 2 = ∑ a, lam a ^ 2 - ((Formalism.BasicNotions.TH.rhoSq n : ℚ) : ℂ) := by
  rw [GlobalTheory.CasimirEigen.gelfVal_two_eq, sum_rhoStd_sq]
  simp only [sq]

end GlobalTheory.GelfandTwo
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evC n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  first | exact @GlobalTheory.FlatFactor.LowStage.kerRed_evAll | exact GlobalTheory.FlatFactor.LowStage.kerRed_evAll | (intros; apply GlobalTheory.FlatFactor.LowStage.kerRed_evAll <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatFactorReduction_kernel_integrates_free_entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  first | exact @GlobalTheory.FlatFactor.UpStage.kerRed_itFree | exact GlobalTheory.FlatFactor.UpStage.kerRed_itFree | (intros; apply GlobalTheory.FlatFactor.UpStage.kerRed_itFree <;> assumption)
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.exists_pow_heckeChar_unramified_everywhere : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  first | exact @GlobalTheory.Corev.UnrPow.exists_pow_unrAt | exact GlobalTheory.Corev.UnrPow.exists_pow_unrAt | (intros; apply GlobalTheory.Corev.UnrPow.exists_pow_unrAt <;> assumption)
end
