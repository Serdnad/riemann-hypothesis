module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle181
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem epsGen_epsEv_apply {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) e u = u.fst + u.snd * ptAlg (R := R) (D := DualNumber R) e DualNumber.eps := by
  simp [epsEv, DualNumber.lift_apply_apply]

theorem epsGen_epsEv_nat {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) (E := E') (spOver ψ ≫ e) (epsHom ψ u) = ψ (epsEv (R := R) e u) := by
  obtain ⟨h1, h2, -⟩ := dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ u
  simp only [epsGen_epsEv_apply, h1, h2, ptAlg_comp, AlgHom.comp_apply, map_add, map_mul]

theorem epsGen_spMap_eq {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (p : Sp E) :
    (spMap (epsEv (R := R) e : DualNumber E →+* E)).base p =
      (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p := by
  apply PrimeSpectrum.ext
  ext u
  have hc : ptAlg (R := R) (D := DualNumber R) (E := E) e DualNumber.eps ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, ← map_mul, DualNumber.eps_mul_eps, map_zero]; exact p.asIdeal.zero_mem)
  change epsEv (R := R) e u ∈ p.asIdeal ↔ u.fst ∈ p.asIdeal
  rw [epsGen_epsEv_apply]
  constructor
  · intro h
    have := p.asIdeal.sub_mem h (p.asIdeal.mul_mem_left u.snd hc)
    simpa using this
  · intro h
    exact p.asIdeal.add_mem h (p.asIdeal.mul_mem_left u.snd hc)

theorem epsGen_mem {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) {Y : Scheme.{0}}
    (y : Sp (DualNumber E) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (spMap (epsEv (R := R) e : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U) :
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (Set.mem_univ p)
  change y.base ((spMap (epsEv (R := R) e : DualNumber E →+* E)).base p) ∈ U at this
  change y.base ((spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p) ∈ U
  rwa [← epsGen_spMap_eq (R := R) e p]

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem epsGen_red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV (R := R) (D := E) v x =
      x ≫ AbDual.inl A B := by
  apply GlobalTheory.PtExt.EpsGenCob.red_ptV <;> assumption

theorem epsGen_key (v : epsR R ⟶ B) {E : Type} [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) :
    z ≫ lift (fst A (epsR R)) (snd A (epsR R) ≫ v) =
      spOver (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp
        (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      simp [epsEv]
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp (EpsWeil.epsMap R E) =
        ptAlg (R := R) (D := DualNumber R) (E := E) (z ≫ snd A (epsR R)) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap, epsEv]
    rw [this, spOver_ptAlg, Category.assoc]

theorem exists_isPtGen_of_isEpsGen : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ T, IsEpsGen (R := R) (A := A) P v T →
    ∃ t, IsPtGen (R := R) P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  intro R _ A B _ _ P _ v hv T hT
  obtain ⟨T1, T2, T3⟩ := hT
  have memV : ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
      ⊤ ≤ (ptV (R := R) (D := E) v x).left ⁻¹ᵁ P.U i := by
    intro E _ _ x i h
    apply dualNumberPoint_preimage_top_of_reduction _ E (ptV (R := R) (D := E) v x).left (P.U i)
    have h1 : ⊤ ≤ (x ≫ AbDual.inl A B).left ⁻¹ᵁ P.U i := h
    rw [← epsGen_red_ptV (R := R) (E := E) hv x] at h1
    exact h1
  have memA : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) (i : P.ι),
      ⊤ ≤ (z ≫ CartesianMonoidalCategory.lift (fst A (epsR R)) (snd A (epsR R) ≫ v)).left ⁻¹ᵁ P.U i →
      ⊤ ≤ (z ≫ fst _ _).left ⁻¹ᵁ chartsA P i := by
    intro E _ _ z i h
    rw [epsGen_key (R := R) (E := E) v z, Over.comp_left, spOver_left] at h
    have h2 := epsGen_mem (R := R) (E := E) (z ≫ snd A (epsR R)) _ _ h
    have h3 : ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R E E) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ P.U i := h2
    rw [epsGen_red_ptV hv] at h3
    exact h3
  refine ⟨fun E _ _ z i ↦ epsEv (R := R) (E := E) (z ≫ snd A (epsR R))
    (T E (z ≫ fst A (epsR R)) i), ?_, ?_, ?_⟩
  · intro E _ _ z i h
    exact (T1 E (z ≫ fst _ _) i (memA E z i h)).map _
  · intro E _ _ E' _ _ ψ z i h
    have h' := memA E z i h
    simp only [Category.assoc]
    rw [T2 E E' ψ (z ≫ fst A (epsR R)) i h', epsGen_epsEv_nat]
  · intro E _ _ z i j hi hj
    have hi' := memA E z i hi
    have hj' := memA E z j hj
    have hij : ⊤ ≤ (ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ (P.U i ⊓ P.U j) :=
      fun p hp ↦ ⟨memV E _ i hi' hp, memV E _ j hj' hp⟩
    simp only
    rw [T3 E (z ≫ fst A (epsR R)) i j hi' hj', map_mul, epsGen_key (R := R) (E := E) v z,
      Over.comp_left, spOver_left, evalSectionAtPointOrZero_specMap_comp _ _ E
        (epsEv (R := R) (E := E) (z ≫ snd A (epsR R)) : DualNumber E →+* E) _ _ _ hij]
    rfl

end GlobalTheory.PtExt
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.VoganRoot

open Finset Formalism.REAL

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  apply GlobalTheory.Jet.Schmid.rhoN_add_rhoC <;> assumption

theorem nsq_sub_root {n : ℕ} (u : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    Formalism.REAL.nsq (u - Formalism.REAL.root a b) = Formalism.REAL.nsq u - 2 * (u a - u b) + 2 := by
  apply GlobalTheory.Jet.Schmid.nsq_sub_root <;> assumption

theorem vNormSq_lowK_sub_root_lt {n : ℕ} (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : StrictAnti μ)
    {a b : Fin n} (hab : a < b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ) := by
  apply GlobalTheory.Jet.Schmid.vNormSq_sub_root_lt <;> assumption

end GlobalTheory.HolDict.VoganRoot

theorem GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → ∀ a c : Fin n, ε a = true → ε c = false → vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - Formalism.REAL.root a c) < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  intro n p ε lam hl hε a c ha hc
  rw [hε] at ha hc
  have hac : a < c := by
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ha hc
    exact Fin.lt_def.mpr (by omega)
  exact GlobalTheory.HolDict.VoganRoot.vNormSq_lowK_sub_root_lt ε hl.1 hac
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.SchwartzBox

theorem norm_le_max_comp {V : Type} [NormedAddCommGroup V] {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ ⊕ κ' → V) :
    ‖x‖ ≤ max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun j => ?_
  cases j with
  | inl i => exact le_max_of_le_left (norm_le_pi_norm (x ∘ Sum.inl) i)
  | inr i => exact le_max_of_le_right (norm_le_pi_norm (x ∘ Sum.inr) i)

def restr (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ → ι) :
    (ι → V) →L[ℝ] (κ → V) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) (e i)

theorem restr_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) (x : ι → V) : restr V e x = x ∘ e := rfl

theorem norm_restr_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) : ‖restr V e‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => norm_le_pi_norm x (e i)

theorem norm_iteratedFDeriv_restr_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι]
    [Fintype κ] (e : κ → ι) (f : SchwartzMap (κ → V) ℂ) (i : ℕ) (x : ι → V) :
    ‖iteratedFDeriv ℝ i (fun y => f (y ∘ e)) x‖ ≤ ‖iteratedFDeriv ℝ i f (x ∘ e)‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (restr V e) (f.smooth ⊤) x (i := i) (by exact_mod_cast le_top)
  have h' : (fun y => f (y ∘ e)) = (f ∘ restr V e) := rfl
  rw [h', h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (restr V e x)‖ * ∏ _j : Fin i, ‖restr V e‖
      ≤ ‖iteratedFDeriv ℝ i f (restr V e x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_restr_le V e
    _ = _ := mul_one _

theorem exists_schwartz_box {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ) (f₂ : SchwartzMap (κ' → V) ℂ) :
    ∃ f : SchwartzMap (κ ⊕ κ' → V) ℂ, ∀ x, f x = f₁ (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr) := by
  apply GlobalTheory.CompanionTheory.ThetaBox.exists_schwartz_box <;> assumption

theorem sb_box {X : Type} [TopologicalSpace X] {κ κ' : Type} {g₁ : (κ → X) → ℂ} {g₂ : (κ' → X) → ℂ}
    (hg₁ : g₁ ∈ SB (κ → X)) (hg₂ : g₂ ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  obtain ⟨hl₁, hc₁⟩ := hg₁
  obtain ⟨hl₂, hc₂⟩ := hg₂
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  have he : ∀ z, e z = (z ∘ Sum.inl, z ∘ Sum.inr) := fun _ => rfl
  refine ⟨?_, ?_⟩
  · have c₁ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inl := continuous_pi fun i => continuous_apply _
    have c₂ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inr := continuous_pi fun i => continuous_apply _
    exact (hl₁.comp_continuous c₁).mul (hl₂.comp_continuous c₂)
  · refine HasCompactSupport.intro' (K := e ⁻¹' (tsupport g₁ ×ˢ tsupport g₂))
      (e.isCompact_preimage.2 (hc₁.prod hc₂))
      (((isClosed_tsupport _).prod (isClosed_tsupport _)).preimage e.continuous) fun z hz => ?_
    rw [Set.mem_preimage, he, Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]

theorem boxFun_zero_left {R κ κ' : Type} (φ : (κ' → R) → ℂ) : boxFun (0 : (κ → R) → ℂ) φ = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_left {R κ κ' : Type} (a b : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (a + b) φ = boxFun a φ + boxFun b φ := by
  funext x; simp [boxFun, add_mul]

theorem boxFun_smul_left {R κ κ' : Type} (c : ℂ) (a : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (c • a) φ = c • boxFun a φ := by
  funext x; simp [boxFun, mul_assoc]

theorem boxFun_zero_right {R κ κ' : Type} (φ : (κ → R) → ℂ) : boxFun φ (0 : (κ' → R) → ℂ) = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_right {R κ κ' : Type} (φ : (κ → R) → ℂ) (a b : (κ' → R) → ℂ) :
    boxFun φ (a + b) = boxFun φ a + boxFun φ b := by
  funext x; simp [boxFun, mul_add]

theorem boxFun_smul_right {R κ κ' : Type} (c : ℂ) (φ : (κ → R) → ℂ) (a : (κ' → R) → ℂ) :
    boxFun φ (c • a) = c • boxFun φ a := by
  funext x; simp [boxFun]; ring


open scoped Classical in
theorem boxFun_mem_schA (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  intro φ₁ h₁ φ₂ h₂
  have gen : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      ∀ Φ₂ ∈ {Φ | ∃ (f : SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ Φ₂ ∈ schA F (κ ⊕ κ') := by
    rintro _ ⟨f₁, g₁, hg₁, rfl⟩ _ ⟨f₂, g₂, hg₂, rfl⟩
    obtain ⟨f, hf⟩ := exists_schwartz_box f₁ f₂
    refine Submodule.subset_span ⟨f, fun z => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr), sb_box hg₁ hg₂, ?_⟩
    funext x
    simp only [boxFun, pureA, hf]
    simp only [Function.comp_def]
    ring
  have gen₂ : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
    intro Φ₁ hΦ₁
    induction h₂ using Submodule.span_induction with
    | mem x hx => exact gen Φ₁ hΦ₁ x hx
    | zero => rw [boxFun_zero_right]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [boxFun_add_right]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [boxFun_smul_right]; exact Submodule.smul_mem _ c hx
  induction h₁ using Submodule.span_induction with
  | mem x hx => exact gen₂ x hx
  | zero => rw [boxFun_zero_left]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [boxFun_add_left]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [boxFun_smul_left]; exact Submodule.smul_mem _ c hx

end GlobalTheory.SchwartzBox
end
end

section

noncomputable section

namespace GlobalTheory.UnrEuler

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]




end GlobalTheory.UnrEuler
end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolomorphicDiscreteSeriesDecomposition

theorem dRepC_eq_sum : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (v : D), GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = ((∑ a, ∑ b, Z a b • E a b v : D) : H) := by
  intro n ε H _ _ σ D E hK Z v
  have hG : IsUnit (Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  obtain ⟨h1, h2⟩ := GlobalTheory.SmVec.parts_mem hG (Formalism.REAL.Jm_conjTranspose ε) Z
  have key : ∀ X, inG ε X → Formalism.L2.Theta.dRep σ X (v : H) = ∑ a, ∑ b, X a b • (E a b v : H) := fun X hX => by
    have := hK.real X hX v
    simp only [Complex.coe_smul] at this
    exact this.deriv
  unfold GlobalTheory.SmVec.dRepC
  rw [key _ h1, key _ h2]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring

end GlobalTheory.HolomorphicDiscreteSeriesDecomposition
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ConjIdeleReal

theorem adeleMap_eq_baseChange (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L = GroundTheory.Global.AdeleBaseChange.adeleMap K L := by
  ext a : 1
  apply Prod.ext
  · funext w
    open scoped NumberField.LiesOver in
    change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
    rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
  · apply FiniteAdeleRing.ext
    intro w
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w _ =
      GroundTheory.Global.SemiLocal.completionMap _ w _
    rfl

theorem ideleConj_ideleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b := by
  intro E _ _ _ b
  let alg : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have tw : @IsScalarTower (maximalRealSubfield E) E E _ (@Algebra.toSMul _ _ _ _ alg) _ :=
    @IsScalarTower.of_algebraMap_eq (maximalRealSubfield E) E E _ _ _ _ alg _ fun x =>
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x).symm
  have h := @GroundTheory.Global.AdeleBaseChange.adeleMap_adeleMap (maximalRealSubfield E) E E _ _ _ _ _ _ _ alg _ tw
    (b : AdeleRing _ _)
  rw [← adeleMap_eq_baseChange, ← adeleMap_eq_baseChange] at h
  apply Units.ext
  exact h

end GlobalTheory.ConjIdeleReal
end
end

section


theorem _root_.GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  first | exact @GlobalTheory.DerivAtOrigin.statement | exact GlobalTheory.DerivAtOrigin.statement | (intros; apply GlobalTheory.DerivAtOrigin.statement <;> assumption)
end

section


theorem _root_.GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  first | exact @GlobalTheory.HeckeStrip.completedLBoundedInStrips | exact GlobalTheory.HeckeStrip.completedLBoundedInStrips | (intros; apply GlobalTheory.HeckeStrip.completedLBoundedInStrips <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.fractionalIdealNorm_eq_finiteIdeleModule : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := by
  first | exact @GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf | exact GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf | (intros; apply GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf <;> assumption)
end
