module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle263
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle261
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle008
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.Divisibility.Bundle003
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle002
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups GlobalTheory.ThetaProjEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCommutation

theorem exists_fin_part {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = q := by
  obtain ⟨h, rfl⟩ := (finHom V).rangeRestrict_surjective q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
  refine ⟨k, hk, Subtype.ext ?_⟩
  show finHom V k = finHom V (a * k)
  rw [map_mul, show finHom V a = 1 from ha, one_mul]

theorem finiteGroupLevelAction_eq_inv_smul_translate {H W : Type} [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup H} (ch : Q →* ℂˣ)
    (q : Q) (k : H) (hk : k = q) (c : ℂ) (hc : c = ch q) (f : H → W) (h : H) :
    Bridge.g0Act ch q f h = c⁻¹ • f (h * k) := by
  rw [hk, hc, Bridge.g0Act, Units.val_inv_eq_inv_val]

theorem ch_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) := rfl

theorem exists_adelic_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) (g0 : G0 L.Pg L.r) (hq : rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) = g0)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    ∃ k, IsLevelLift V β L g0 k ∧ ∀ (f : Bridge.Gf V → W) h,
      Bridge.g0Act (levEnv V β L).ch q f h = (levChi V β (flagL L) k)⁻¹ • f (h * (finHom V).rangeRestrict k) := by
  obtain ⟨k, hk, e⟩ := exists_fin_part V q.1
  have e1 : finE V k = Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) :=
    congrArg (fun x : Bridge.Gf V => Formalism.UG.bc (swapAE D) x.1) e
  refine ⟨k, ⟨hk, ?_, ?_⟩, finiteGroupLevelAction_eq_inv_smul_translate _ q _ e _ ?_⟩
  · rw [e1]; exact q.2.1
  · rw [e1]; exact hq
  · exact congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq V β L q).symm)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem algW_apply (i : Fin D.R.m) (c : G → ℂ) (U : MMap (R.MW i (sg0 D A))) :
    algW R i c U = ∑ g, c g • FWT.actW R i (sg0 D A) g U := by
  refine MultilinearMap.ext fun v => ?_
  show (∑ g, c g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (U v) = _
  rw [LinearMap.sum_apply, _root_.sum_apply]
  rfl

theorem map_comb {G H X Y : Type} [Fintype G] [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (Θ : H →ₗ[ℂ] Y) (c : G → ℂ) (a : G → X) (b : G → Y) (y : H)
    (hy : e y = ∑ g, c g • a g) (h1 : ∀ g, ∃ z, e z = a g) (h2 : ∀ g z, e z = a g → Θ z = b g) :
    Θ y = ∑ g, c g • b g := by
  choose z hz using h1
  have h3 : y = ∑ g, c g • z g := he (by simp only [hy, map_sum, map_smul, hz])

  simp only [h3, map_sum, map_smul, h2 _ _ (hz _)]

end GlobalTheory.ThetaCommutation

end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TorCentTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}
  {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k]


omit [FiniteDimensional F E] [TopologicalSpace k] [IsTopologicalRing k] in
theorem isScalarTower_base : IsScalarTower k (k ⊗[F] E) (k ⊗[F] Fld P) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change c ⊗ₜ[F] (1 : Fld P) = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) (c ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

theorem continuous_mulMat (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) : Continuous (mulMat φ) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : ContinuousAdd (k ⊗[F] E) := IsModuleTopology.toContinuousAdd k _
  haveI := isScalarTower_base (k := k) (P := P)
  refine continuous_matrix fun i j => ?_
  have e : ∀ l, mulMat φ l i j = φ (l * φ.symm (Pi.single j 1)) i := fun l => by
    rw [← mulMat_mulVec, φ.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [e]
  exact IsModuleTopology.continuous_of_linearMap (((LinearMap.proj i).comp (φ.toLinearMap.comp
    (LinearMap.mulRight (k ⊗[F] E) (φ.symm (Pi.single j 1))))).restrictScalars k)

theorem torUnit_val (t : Tor P k) : (torUnit t).1 = (matHom k (star' P) (one₁ P) t).1 0 0 :=
  Matrix.det_fin_one _

theorem continuous_torUnit : Continuous fun t : Tor P k => (torUnit t).1 := by
  simp only [torUnit_val]
  exact (Units.continuous_val.comp (isEmbedding_matHom k (star' P) (one₁ P)).continuous).matrix_elem 0 0

theorem matHom_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (matHom k σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl

theorem torUnit_eq {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (torUnit t).1 = φ.symm ((matHom k σ J (torEmb h t)).1 *ᵥ φ 1) := by
  rw [matHom_torEmb, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_one]

theorem continuous_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) : Continuous (torEmb h) := by
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  refine (isEmbedding_matHom k σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun t => (matHom k σ J (torEmb h t)).1
    simp only [matHom_torEmb]
    exact (continuous_mulMat φ).comp continuous_torUnit
  · change Continuous fun t => (matHom k σ J (torEmb h t))⁻¹.1
    simp only [← map_inv, matHom_torEmb]
    exact (continuous_mulMat φ).comp (continuous_torUnit.comp continuous_inv)

theorem continuous_back (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) :
    Continuous fun g : HA k σ J => φ.symm ((matHom k σ J g).1 *ᵥ φ 1) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  haveI := isScalarTower_base (k := k) (P := P)
  haveI : ContinuousAdd (k ⊗[F] Fld P) := IsModuleTopology.toContinuousAdd k _
  have h1 : Continuous (φ.symm.toLinearMap.restrictScalars k) := IsModuleTopology.continuous_of_linearMap _
  refine h1.comp (Continuous.matrix_mulVec ?_ continuous_const)
  exact Units.continuous_val.comp (isEmbedding_matHom k σ J).continuous

theorem torEquiv_cent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ e : Tor P k ≃ₜ* cent (gam h), (∀ t, (e t).1 = torEmb h t) ∧ ∀ dt : Measure (Tor P k), centMeas h dt = dt.map e := by
  intro F E _ _ _ _ _ σ hCM r n P J hJ k _ _ _ _ _ x φ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  obtain ⟨-, -, hinj, hrange⟩ := GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hCM r n P J hJ k x φ h
  let e0 : Tor P k ≃* cent (gam h) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  have he : ∀ t, (e0 t).1 = torEmb h t := fun t => rfl
  have hs : ∀ s, torEmb h (e0.symm s) = s.1 := fun s => by rw [← he, e0.apply_symm_apply]
  have hback : ∀ s, (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0 = φ.symm ((matHom k σ J s.1).1 *ᵥ φ 1) :=
    fun s => by rw [← torUnit_val, GlobalTheory.TorCentTop.torUnit_eq h, hs]
  let e : Tor P k ≃ₜ* cent (gam h) :=
    { e0 with
      continuous_toFun := continuous_induced_rng.2 (GlobalTheory.TorCentTop.continuous_torEmb h)
      continuous_invFun := by
        refine (isEmbedding_matHom k (star' P) (one₁ P)).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0
          simp only [hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp continuous_subtype_val
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s))⁻¹.1 0 0
          simp only [← map_inv, hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp (continuous_subtype_val.comp continuous_inv) }
  refine ⟨e, fun t => rfl, fun dt => ?_⟩
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  have eh : (k ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → k) :=
    let b := (Algebra.TensorProduct.basis k (Module.finBasis F E)).equivFun
    { b.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap }
  haveI : T2Space (k ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : T2Space (GL (Fin n) (k ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (HA k σ J) := (isEmbedding_matHom k σ J).t2Space
  have hset : (cent (gam h) : Set (HA k σ J)) = {g | gam h * g = g * gam h} := by
    ext g; simp [cent, Subgroup.mem_centralizer_iff]
  have hclosed : IsClosed (cent (gam h) : Set (HA k σ J)) := by
    rw [hset]; exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hf : (torEmb h : Tor P k → HA k σ J) = Subtype.val ∘ e := funext fun t => rfl
  unfold centMeas
  rw [hf, ← Measure.map_map measurable_subtype_coe (map_continuous e).measurable]
  exact (MeasurableEmbedding.subtype_coe hclosed.measurableSet).comap_map _

end GlobalTheory.TorCentTop
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl UA)
open Formalism.L2.Theta (GA GfC finHom frameMat)
open Formalism.IndefR.Lev (EAf finE)
open Formalism.IndefR.Datum (IsSelfDualC)
open Formalism.UG (cT hform)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsomCorrection

section Algebra

variable {A : Type} [CommRing A] (σ : A →+* A)

theorem cT_mul_rect {l m n : ℕ} (M : Matrix (Fin l) (Fin m) A) (N : Matrix (Fin m) (Fin n) A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  rw [cT, Matrix.map_mul, transpose_mul]
  rfl

theorem gram_of_form {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x : Matrix (Fin m) (Fin n) A)
    (h : ∀ i j, hform σ J' (x *ᵥ Pi.single i 1) (x *ᵥ Pi.single j 1) = J i j) :
    cT σ x * J' * x = J := by
  ext i j
  rw [← h i j]
  simp only [hform, mulVec_single_one, Matrix.mul_apply, cT, transpose_apply, map_apply, col_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

theorem exists_unitary {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) (y' : Matrix (Fin n) (Fin m) A) (h1 : y * y' = 1) (h2 : y' * y = 1)
    (hb : Function.Surjective x.mulVec) (hx : cT σ x * J' * x = J) (hy : cT σ y * J' * y = J) :
    ∃ g : GL (Fin m) A, cT σ g.1 * J' * g.1 = J' ∧ g.1 * y = x := by
  have hu : IsUnit (x * y') := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w, rfl⟩ := hb v
    exact ⟨y *ᵥ w, by rw [mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [hu.unit_spec, cT_mul_rect]
    have e : cT σ y' * cT σ y = 1 := by
      rw [← cT_mul_rect, h1, cT, Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    calc cT σ y' * cT σ x * J' * (x * y') = cT σ y' * (cT σ x * J' * x) * y' := by simp only [Matrix.mul_assoc]
      _ = (cT σ y' * cT σ y) * J' * (y * y') := by rw [hx, ← hy]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [e, h1, Matrix.one_mul, Matrix.mul_one]
  · rw [hu.unit_spec, Matrix.mul_assoc, h2, Matrix.mul_one]

end Algebra

variable {D : D7}

theorem exists_finE (V : HSp D) (g : GL (Fin V.rank) (EAf D)) (hg : g ∈ UA D.sp.cm V.gram) :
    ∃ k ∈ GfC V, finE V k = g := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨g, hg⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, ?_⟩
  have e := congrArg Subtype.val hb
  have e2 := GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram b
  refine Eq.trans ?_ (e2.symm.trans e)
  exact congrArg (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)) k2

theorem mA_mul (X Y Z : HSp D) (f : X.V →ₗ[D.host.E] Y.V) (g : Y.V →ₗ[D.host.E] Z.V) :
    mA Z Y g * mA Y X f = mA Z X (g.comp f) := by
  rw [mA, mA, mA, ← Matrix.map_mul, frameMat, frameMat, frameMat, LinearMap.toMatrix_comp X.frame Y.frame Z.frame]

theorem mA_id (X : HSp D) : mA X X LinearMap.id = 1 := by
  rw [mA, frameMat, LinearMap.toMatrix_id, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem vA_frame (X : HSp D) (i : Fin X.rank) : vA X (X.frame i) = Pi.single i 1 := by
  funext j
  have : Formalism.L2.Herm.crd X (X.frame i) j = X.frame.repr (X.frame i) j := rfl
  rw [vA, this, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm, RingHom.map_one]
  · rw [if_neg h, if_neg (Ne.symm h), RingHom.map_zero]

theorem gram_mA (Y Y' : HSp D) (f : Y.V →ₗ[D.host.E] Y'.V) (hf : HSpace.IsIsomEmb Y Y' f) :
    HMul.hMul (HMul.hMul (cT (cjA D) (mA Y' Y f)) (Y'.gram.map (inc D))) (mA Y' Y f) = Y.gram.map (inc D) := by
  refine gram_of_form _ _ _ _ fun i j => ?_
  rw [← vA_frame, ← vA_frame, mA_mulVec_vA, mA_mulVec_vA, ← hA_eq, hA_vA, HSpace.hD, hf]
  rfl

theorem correction_of_transport : ∀ D : D7, TransportSt D → CorrectionSt D := by
  intro D hT Y Y' io hio Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  have hr : Y.rank = Y'.rank := by rw [← Y.rank_eq, ← Y'.rank_eq, io.finrank_eq]
  obtain ⟨⟨x, hx⟩, -⟩ := hT Y Y' hr Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  obtain ⟨g, hg, hgx⟩ := exists_unitary (cjA D) (Y'.gram.map (inc D)) (Y.gram.map (inc D)) x
    (mA Y' Y io.toLinearMap) (mA Y Y' io.symm.toLinearMap)
    (by rw [mA_mul, LinearEquiv.comp_symm, mA_id]) (by rw [mA_mul, LinearEquiv.symm_comp, mA_id]) hx.1.1.2
    (gram_of_form _ _ _ _ fun i j => (hx.1.2 _ _).trans (hform_single _ _ i j)) (gram_mA Y Y' _ hio)
  obtain ⟨k, hk, e⟩ := exists_finE Y' g hg
  refine ⟨k, hk, ?_⟩
  rw [e, hgx]
  exact hx

end GlobalTheory.AdIsomCorrection
end

section

namespace LinearIndependenceOfCarries
section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ReadingExt

open Module

theorem li_of_carries {LL K WL V : Type} [Field LL] [Field K] [AddCommGroup WL] [Module LL WL] [AddCommGroup V] [Module K V]
    {emb : LL →+* K} (e : WL →ₛₗ[emb] V)
    (hC : ∀ (ι : Type) (b : Basis ι LL WL), ∃ c : Basis ι K V, ∀ i, c i = e (b i))
    {ι : Type} {v : ι → WL} (hv : LinearIndependent LL v) : LinearIndependent K (fun a => e (v a)) := by
  have hs := hv.linearIndepOn_id
  obtain ⟨c, hc⟩ := hC _ (Basis.extend hs)
  have hsub := hs.subset_extend (Set.subset_univ _)
  let f : ι → ↥(hs.extend (Set.subset_univ _)) := fun a => ⟨v a, hsub ⟨a, rfl⟩⟩
  have hf : Function.Injective f := fun a b h => hv.injective (congrArg Subtype.val h)
  have h2 := c.linearIndependent.comp f hf
  have h3 : (c ∘ f) = fun a => e (v a) := by
    funext a
    simp only [Function.comp, hc, Basis.extend_apply_self, f]
  rwa [h3] at h2

theorem comp_cast_of_heq {K : Type} {a b : ℕ} (h : b = a) (z : Fin a → K) (y : Fin b → K) (hz : HEq z y) :
    z ∘ finCongr h = y := by
  subst h
  exact eq_of_heq hz

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in

theorem fracExt_algebraMap (c : NChoice D) (w : D.what₂.places.Pl) (x : D.ntw.O (c.twI w)) :
    fracExt c w (algebraMap _ (FractionRing (D.ntw.O (c.twI w))) x) =
      algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) x := by
  rw [IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w))]
  simp [fracExt, IsFractionRing.map]




end GlobalTheory.CompanionTheory.ReadingExt

end
end

end LinearIndependenceOfCarries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.classTerm_eq_volume_mul_orbitalIntegral : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → IsMulCommutative (cent γ) → ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)), IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → dt 𝓣 < ⊤ → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ γ dt f c → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (dt.real 𝓣 * c) := by
  first | exact @GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt | exact GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt | (intros; apply GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_goodProjector_move_petersson : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (Φ : GA D (Wc D i) → ℂ), (∀ γ ∈ GQ (Wc D i), ∀ g, Φ (γ * g) = Φ g) → (∀ y : (R.HW i σ).H, IntegrableOn (fun g => star (Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g) (R.fdW i) (R.νW i)) → ∀ y : (R.HW i σ).H, ∫ g in R.fdW i, star (R.eWf i σ Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g ∂(R.νW i) = ∫ g in R.fdW i, star (Φ g) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) := by
  first | exact @GlobalTheory.EwfMove.integral_eWf_move | exact GlobalTheory.EwfMove.integral_eWf_move | (intros; apply GlobalTheory.EwfMove.integral_eWf_move <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Hk3



theorem GlobalTheory.Hk3.SysE.matched_keeps_eigen : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh hhn P hg cX c0 hM x l hx
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have hX01 := (GlobalTheory.DefiniteOps.definite_ops R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX, hXo, hXn⟩
  have comm : ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg c0 (R.Th t y)).symm
  have eX : LinearMap.adjoint (hX P cX) = hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hXn.2 P hg cX
  have cX' : Commute (hX P cX) (hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hXn.1 P P hg hg _ _
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX P cX) B) _ _ eX.symm cX'
  have eE : LinearMap.adjoint (h P c0) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := hhn.2 P hg c0
  have cE : Commute (h P c0) (h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := hhn.1 P P hg hg _ _
  have nE : Commute (h P c0) (LinearMap.adjoint (h P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h P c0) B) _ _ eE.symm cE
  have up : hX P cX (LinearMap.adjoint (R.Th t) x) = l • LinearMap.adjoint (R.Th t) x :=
    GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h P c0)
      (fun _ u => comm u) (fun _ => nX) (fun _ => nE) () l x hx
  have c1 := comm (LinearMap.adjoint (R.Th t) x)
  have c2 : R.Th t (hX P cX (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
    exact (congrArg (R.Th t) up).trans ((R.Th t).map_smul l _)
  exact c1.symm.trans c2
end
