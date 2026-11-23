module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle235
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle238
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

def powB : Module.Basis (Fin r) E (Fld P) :=
  (AdjoinRoot.powerBasis P.2.2.1.ne_zero).basis.reindex
    (finCongr ((AdjoinRoot.powerBasis_dim P.2.2.1.ne_zero).trans P.2.2.2.1))

def gramOne : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i j => Algebra.trace E (Fld P) (powB P j * star' P (powB P i))

variable (k : Type) [CommRing k] [Algebra F k]

def coordF (i : Fin r) : k ⊗[F] Fld P →ₗ[F] k ⊗[F] E :=
  LinearMap.lTensor k (((powB P).coord i).restrictScalars F)

theorem coordF_tmul (i : Fin r) (a : k) (z : Fld P) : coordF P k i (a ⊗ₜ[F] z) = a ⊗ₜ[F] (powB P).repr z i := rfl

theorem smul_eq_map_mul (c : k ⊗[F] E) (y : k ⊗[F] Fld P) :
    c • y = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) c * y :=
  Algebra.smul_def c y

theorem coordF_smul (i : Fin r) (c : k ⊗[F] E) (y : k ⊗[F] Fld P) : coordF P k i (c • y) = c * coordF P k i y := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' h h' => rw [add_smul, map_add (f := _), h, h', add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => rw [smul_add, map_add (f := _), h, h', map_add (f := _), mul_add]
    | tmul a' z =>
      rw [smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, coordF_tmul,
        coordF_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      change (powB P).repr (algebraMap E (Fld P) e * z) i = e * _
      rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

def coordInv (w : Fin r → k ⊗[F] E) : k ⊗[F] Fld P := ∑ i, w i • ((1 : k) ⊗ₜ[F] powB P i)

theorem coordF_coordInv (w : Fin r → k ⊗[F] E) (j : Fin r) : coordF P k j (coordInv P k w) = w j := by

  simp only [coordInv, map_sum, coordF_smul, coordF_tmul, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j (fun i _ h => by rw [Finsupp.single_apply, if_neg h, TensorProduct.tmul_zero, mul_zero])
    (by simp), Finsupp.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]

theorem coordInv_coordF (y : k ⊗[F] Fld P) : coordInv P k (fun i => coordF P k i y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add y y' h h' =>
    conv_rhs => rw [← h, ← h']
    simp only [coordInv, map_add (f := _), add_smul, Finset.sum_add_distrib]
  | tmul a z =>
    simp only [coordInv, coordF_tmul, smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
    rw [← TensorProduct.tmul_sum]
    congr 1
    conv_rhs => rw [← (powB P).sum_repr z]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm

def coordEquiv : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E) where
  toFun y i := coordF P k i y
  map_add' y y' := funext fun i => map_add _ _ _
  map_smul' c y := funext fun i => coordF_smul P k i c y
  invFun := coordInv P k
  left_inv y := coordInv_coordF P k y
  right_inv w := funext fun j => coordF_coordInv P k w j

theorem coordEquiv_apply (y : k ⊗[F] Fld P) (i : Fin r) : coordEquiv P k y i = coordF P k i y := rfl

end GlobalTheory.TrUnitLat
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem cxRoots_root (i : Fin r) : eval₂ τ.1 (cxRoots τ.1 P i) P.1 = 0 := by
  rw [← eval_map, cxRoots_spec, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem cxRoots_injective : Function.Injective (cxRoots τ.1 P) := by
  have hs : (P.1.map τ.1).Separable := (PerfectField.separable_of_irreducible P.2.2.1).map
  have hn := nodup_roots hs
  rw [cxRoots_spec, ← Finset.prod_map_val,
    show Multiset.map (fun i => X - C (cxRoots τ.1 P i)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Finset.univ.val.map (cxRoots τ.1 P)) by rw [Multiset.map_map]; rfl,
    roots_multiset_prod_X_sub_C] at hn
  exact fun i j h => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).1 hn i (by simp) j (by simp) h

theorem finrank_Fld : Module.finrank E (Fld P) = r :=
  ((AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim _)).trans P.2.2.2.1

def psiL (i : Fin r) : Fld P →+* ℂ := AdjoinRoot.lift τ.1 (cxRoots τ.1 P i) (cxRoots_root P τ i)

@[simp] theorem psiL_algebraMap (i : Fin r) (e : E) : psiL P τ i (algebraMap E (Fld P) e) = τ.1 e :=
  AdjoinRoot.lift_of _

@[simp] theorem psiL_alpha (i : Fin r) : psiL P τ i (alpha P) = cxRoots τ.1 P i := AdjoinRoot.lift_root _

theorem psiL_algebraMap_F (i : Fin r) (a : F) : psiL P τ i (algebraMap F (Fld P) a) = w.embedding a := by
  rw [IsScalarTower.algebraMap_apply F E (Fld P), psiL_algebraMap]
  exact RingHom.congr_fun τ.2 a

def Psi (i : Fin r) : w.Completion ⊗[F] Fld P →+* ℂ :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  (Algebra.TensorProduct.productMap
    ({ InfinitePlace.Completion.extensionEmbedding w with
        commutes' := fun a => by
          change InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion a) = w.embedding a
          rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
            Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbedding_coe,
            ← WithAbs.equiv_symm_apply, RingEquiv.apply_symm_apply] } :
      w.Completion →ₐ[F] ℂ)
    ({ psiL P τ i with commutes' := fun a => psiL_algebraMap_F P τ i a } : Fld P →ₐ[F] ℂ)).toRingHom

@[simp] theorem Psi_tmul (i : Fin r) (a : w.Completion) (y : Fld P) :
    Psi P τ i (a ⊗ₜ[F] y) = InfinitePlace.Completion.extensionEmbedding w a * psiL P τ i y := rfl

def PsiAll : w.Completion ⊗[F] Fld P →+* (Fin r → ℂ) := Pi.ringHom (Psi P τ)

@[simp] theorem PsiAll_apply (y : w.Completion ⊗[F] Fld P) (i : Fin r) : PsiAll P τ y i = Psi P τ i y := rfl

end GlobalTheory.TrEll.RealTorus
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory

theorem trEll_latticeConj_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  intro F E _ _ _ _ _ σ _ r n n' P J J' L L' v j hj
  obtain ⟨a, ha, -, hja⟩ := hj
  have iso : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J x φ → IsIsom P (Fv F v) J' x (φ.trans a) := by
    intro x φ h y y'
    have e := ha (φ y) (φ y')
    simp only [GlobalTheory.AdelicU.hLin, hR] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e]
    exact h y y'
  have iso' : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J' x φ → IsIsom P (Fv F v) J x (φ.trans a.symm) := by
    intro x φ h y y'
    have e := ha (a.symm (φ y)) (a.symm (φ y'))
    simp only [GlobalTheory.AdelicU.hLin, hR, LinearEquiv.apply_symm_apply] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← e]
    exact h y y'
  have tor : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
      (h : IsIsom P (Fv F v) J x φ) (t : Tor P (Fv F v)), torEmb (iso x φ h) t = j (torEmb h t) := by
    intro x φ h t
    apply GlobalTheory.AdelicU.matHom_injective (Fv F v) σ J'
    apply Units.ext
    have key : ∀ w, (GlobalTheory.AdelicU.matHom _ σ J' (torEmb (iso x φ h) t)).1 *ᵥ w =
        (GlobalTheory.AdelicU.matHom _ σ J' (j (torEmb h t))).1 *ᵥ w := by
      intro w
      obtain ⟨y, rfl⟩ := (φ.trans a).surjective w
      rw [LinearEquiv.trans_apply, hja]
      change mulMat (φ.trans a) (torUnit t).1 *ᵥ (φ.trans a) y = a (mulMat φ (torUnit t).1 *ᵥ φ y)
      rw [mulMat_mulVec, mulMat_mulVec]
      rfl
    exact Matrix.ext_of_mulVec_single fun i => key _
  refine ⟨?_, fun x φ h => ⟨φ.trans a, iso _ φ h, tor _ φ h _, tor _ φ h⟩⟩
  ext q
  constructor
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a.symm, e, iso' _ φ h⟩
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a, e, iso _ φ h⟩

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField


theorem _root_.GlobalTheory.T.exists_heckeElement_idempotentPart_splitPlace_lattice : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ ∀ v ∈ latG V g,
      (finPart D e • finVec V v ∈ latGHat V (g * a₀) ↔
        finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  first | exact @GlobalTheory.HeckeLocLift.exists_hecke_ePart | exact GlobalTheory.HeckeLocLift.exists_hecke_ePart | (intros; apply GlobalTheory.HeckeLocLift.exists_hecke_ePart <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.contDiff_rightConvolution_along_one_parameter_products : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g : GA D V, ContDiff ℝ ∞ fun t : Fin k → ℝ => GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP | exact GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP | (intros; apply GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section
namespace GlobalTheory.SplitChartLink

theorem block_frame_conjugation_identity {G H : Type} [Group G] [Group H] (f : G →* H) (a x : G) :
    (f a)⁻¹ * f (a * x * a⁻¹) * f a = 1⁻¹ * f x * 1 := by
  simp only [map_mul, map_inv]
  group

theorem rdA_matHom_embV {D : D7} (T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (g : Gv T v) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom T (embV T v g)) =
      splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) g := by
  have h1 : GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g =
      Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom T (embV T v g)) := by
    have h2 := GlobalTheory.AdelicU.matHom_proj D.sp.cm.sig T.gram v (embV T v g)
    rw [GlobalTheory.AdelicU.proj_emb_self] at h2
    exact h2
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [splitHom_val, h1, GlobalTheory.SplitProjChart.splitProj_emb]
  rfl

theorem link : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∃ φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε ∧ (∃ BS, GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS) ∧ ∃ BT, GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT ∧ ∃ ψ : Fv D.host.F v ≃+* w.adicCompletion D.host.E, (∀ a, Valued.v (ψ a) = Valued.v a) ∧ qV D.host.F v = qV D.host.E w ∧ ∃ κ ∈ KGL v (n := T.rank), ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT (embV T v (e.symm x)) = κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x * κ := by
  intro D S T v w h hv e he ε hε
  obtain ⟨v', φ, hφ, hP⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 ε w hε
  have hv' : v' = v := by
    have := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v' φ w hP).1
    subst h
    exact HeightOneSpectrum.ext this.symm
  subst hv'
  have hE : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  set τ := GlobalTheory.SplitProjChart.emb φ with hτdef
  have hφτ : splitProj τ = φ := GlobalTheory.SplitProjChart.splitProj_emb φ
  have hτ : splitPrime τ = w := ((GlobalTheory.SplitIdemDict.isProjAt_iff τ w).1 (hφτ ▸ hP)).symm
  obtain ⟨hch, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v' φ ε hφ
  have hemb : chartEmb hch = τ := AlgHom.ext fun x => by
    rw [chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  have hfr : ∀ (V : HSp D) β, GlobalTheory.SplitHecke.Frame V ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) β ↔ IsSplitBasis τ (frameLat V) β :=
    fun V β => by rw [GlobalTheory.AdelicU.SplitFrame.frame_iff_isSplitBasis hφ.1 hch, hemb]
  set ψ := ConjPlace.complEquiv hE h hτ with hψ
  obtain ⟨⟨a, ha, hea⟩, -⟩ := he
  have hBT : IsSplitBasis τ (frameLat T) (Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') a) := by
    rw [← ConjPlace.isFrameAt_iff hE h hτ]
    convert ha
    exact Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat S
  obtain ⟨BS, hBS⟩ := exists_isSplitBasis τ (frameLat S) hE
  refine ⟨φ, hφ, ⟨BS, (hfr S BS).2 hBS⟩, _, (hfr T _).2 hBT, ψ, ConjPlace.valued_complMap hE h hτ, ?_, 1, one_mem _, ?_⟩
  · rw [← hτ, GlobalTheory.LFun.SplitTie.qV_splitPrime]
  · intro x
    have h3 := hea (e.symm x)
    rw [MulEquiv.apply_symm_apply, ConjPlace.locMat_eq hE h hτ, ← hψ] at h3
    have h4 : splitHom D.sp.cm.sig T.gram τ (e.symm x) =
        Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') (a * x * a⁻¹) := by
      have h5 : Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) =
          a * x * a⁻¹ := by
        generalize Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) = y at h3 ⊢
        subst h3
        group
      rw [← h5]
      exact Units.ext (Matrix.ext fun i j => (ψ.symm_apply_apply _).symm)
    have h6 : Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x =
        Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x := rfl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo, rdA_matHom_embV,
      show splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) (e.symm x) = _ from h4, ← h6]
    exact block_frame_conjugation_identity _ a x

end GlobalTheory.SplitChartLink
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPoly

open Polynomial

theorem coeff_heckePolyOf_le (n q : ℕ) (a : ℕ → ℂ) {i : ℕ} (hi : i ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i = (-1) ^ i * (q : ℂ) ^ (i * (i - 1) / 2) * a i := by
  unfold Formalism.L2.Col.heckePolyOf
  rw [finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem heckePolyOf_eq_zero (n q : ℕ) (a : ℕ → ℂ) (h : ∀ k ≤ n, a k = 0) :
    Formalism.L2.Col.heckePolyOf n q a = 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (by simpa [Nat.lt_succ_iff] using hk)]
  simp

theorem single_mem_span (nX nY q : ℕ) (hq : q ≠ 0) (c : ℂ) (hc : c ≠ 0) (B : Polynomial ℂ) (hB : B ≠ 0)
    (z : ℕ → ℕ → ℂ)
    (h : ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) =
      (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B)
    (j : Fin (nY + 1)) :
    Pi.single j (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i) := by
  by_contra hj
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hj inferInstance
  set a : ℕ → ℂ := fun i => if hi : i < nY + 1 then f (Pi.single ⟨i, hi⟩ 1) else 0 with ha
  have hfv : ∀ k : ℕ, f (fun i : Fin (nY + 1) => z k i) = ∑ i ∈ Finset.range (nY + 1), z k i * a i := by
    intro k
    rw [← Fin.sum_univ_eq_sum_range (fun i => z k i * a i)]
    conv_lhs => rw [show (fun i : Fin (nY + 1) => z k i) = ∑ i : Fin (nY + 1), z k i • Pi.single i (1 : ℂ) by
      ext m; simp [Finset.sum_apply, Pi.single_apply]]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := Fin.is_le i
    simp [ha, hi]
  have hzero : ∀ k ≤ nX, ∑ i ∈ Finset.range (nY + 1), z k i * a i = 0 := by
    intro k hk
    rw [← hfv k]
    have hm : f (fun i : Fin (nY + 1) => z k i) ∈ Submodule.map f (Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩)
    rw [hmap] at hm
    simpa using hm
  have h0 := h a
  rw [heckePolyOf_eq_zero _ _ _ hzero] at h0
  have hcomp : (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) = 0 := by
    rcases mul_eq_zero.1 h0.symm with h1 | h1
    · exact h1
    · exact absurd h1 hB
  have hco := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j) hcomp
  simp only [comp_C_mul_X_coeff, coeff_zero] at hco
  rw [coeff_heckePolyOf_le _ _ _ (Nat.lt_succ_iff.1 j.isLt)] at hco
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have haj : a j = 0 := by
    simpa [hc, hqc] using hco
  apply hf
  have hjle := Fin.is_le j
  simpa [ha, hjle] using haj

end GlobalTheory.SpanPoly

namespace GlobalTheory.SpanPoly

theorem single_splitLab_mem_span : ∀ (nX nY q : ℕ), q ≠ 0 → ∀ (c : ℂ), c ≠ 0 → ∀ (B : Polynomial ℂ), B ≠ 0 → ∀ (z : ℕ → ℕ → ℂ), (∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B) → ∀ j ≤ nY, Finsupp.single (splitLab nY j) (1 : ℂ) ∈ Submodule.span ℂ ((fun k => GlobalTheory.Hk3.splitC nY (z k)) '' Set.Iic nX) := by
  intro nX nY q hq c hc B hB z h j hj
  let φ : (Fin (nY + 1) → ℂ) →ₗ[ℂ] (List ℤ →₀ ℂ) :=
    ∑ i : Fin (nY + 1), (Finsupp.lsingle (splitLab nY i)).comp (LinearMap.proj i)
  have hφz : ∀ k, φ (fun i : Fin (nY + 1) => z k i) = GlobalTheory.Hk3.splitC nY (z k) := by
    intro k
    unfold GlobalTheory.Hk3.splitC
    rw [← Fin.sum_univ_eq_sum_range (fun i => Finsupp.single (splitLab nY i) (z k i))]
    simp [φ]
  have hφe : φ (Pi.single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1)) 1) = Finsupp.single (splitLab nY j) (1 : ℂ) := by
    simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Finsupp.lsingle_apply]
    rw [Finset.sum_eq_single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1))]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  rw [← hφe]
  have hm := Submodule.mem_map_of_mem (f := φ) (single_mem_span nX nY q hq c hc B hB z h ⟨j, Nat.lt_succ_of_le hj⟩)
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨k, Set.mem_Iic.2 (Nat.lt_succ_iff.1 k.isLt), (hφz k).symm⟩

end GlobalTheory.SpanPoly
end
