module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.LocalFields.LocalArtinBaseChange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import GroundTheory.PAdicHodge.Bundle004
public import GroundTheory.PAdicHodge.UnramifiedClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle260
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle238
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle306
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import GroundTheory.LocalFields.ExplicitQp
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhiTw

variable {k : Type} [Field k]

theorem twKer_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ)
    (h : ∀ n : N, χ (n : G) = 1) : twKer (twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, twist_apply, h, Units.val_one, one_smul]

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  have h0 : ∀ i : Fin n, glEmbMat k n A (Fin.last n) (Fin.castSucc i) = 0 := fun i => by
    simp [glEmbMat]
  have h1 : glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by simp [glEmbMat]
  have h2 : (glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [glEmbMat]
  simp only [h0, h1, h2]
  simp [← two_mul, pow_mul]

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have e : ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + colMat k n v.toAdd := rfl
  rw [e, Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    induction i using Fin.lastCases with
    | last => simp [colMat]
    | cast i => simp [colMat, Fin.castSucc_ne_last]
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := (ne_of_lt hij').symm
    have hj : j ≠ Fin.last n := (lt_of_lt_of_le hij' (Fin.le_last i)).ne
    simp [colMat, hj, hne]

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpowM_unip (n : ℕ) (t : ℝ) (u : MirUin k n) : dpowM n t (u : Mir k n) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hd : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
    ext1
    rw [hv']
    exact det_unip n v
  show dpow (n + 1) t ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [dpow, detChar_apply, hd, map_one]

theorem dpowM_levi (n : ℕ) (t : ℝ) (p : Mir k n) :
    dpowM (n + 1) t ((levi k (n + 1)).comp (Mir k n).subtype p) = dpowM n t p := by
  have hd : Matrix.GeneralLinearGroup.det (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) =
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) := by
    ext1
    exact det_glEmbMat (n + 1) _
  show dpow (n + 2) t (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) = dpow (n + 1) t (p : GL (Fin (n + 1)) k)
  rw [dpow, dpow, detChar_apply, detChar_apply, hd]

theorem phiMinus_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (j + 1)) W) (t : ℝ),
    Nonempty ((phiMinus k ψ (twist τ (dpowM (j + 1) t))).Equiv (twist (phiMinus k ψ τ) (dpowM j t))) := by
  intro k _ _ _ _ ψ j W _ _ τ t
  have hK := twKer_twist τ (MirUin k (j + 1)) (mirChar k ψ j) (dpowM (j + 1) t) (dpowM_unip (j + 1) t)
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq _ _ hK) fun p => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  show Submodule.Quotient.mk ((twist τ (dpowM (j + 1) t)) ((levi k (j + 1)).comp (Mir k j).subtype p) v) =
    twist (phiMinus k ψ τ) (dpowM j t) p (Submodule.Quotient.mk v)
  rw [twist_apply, twist_apply, dpowM_levi]
  rfl

end Local

end GlobalTheory.CompanionTheory.LeibPhiTw

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem giso_tw_prod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (A : GRep k r) (B : GRep k t) (s : ℝ) : GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) :=
  ⟨(GlobalTheory.LocGL.multiProdTwistEquiv (two (stdSum rfl)) (twoRep A.ρ B.ρ)
      (GlobalTheory.LocGL.isSmoothChar_absPow (k := k) (s : ℂ))).trans
    (GlobalTheory.LocGL.multiProdEquiv _ fun x => match x with
      | false => Representation.Equiv.refl _
      | true => Representation.Equiv.refl _)⟩

end GlobalTheory.CompanionTheory.LeibOrd

end
end

section


theorem _root_.GlobalTheory.T.curve_branch_length_holds : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | exact GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | (intros; apply GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTNorm

variable {l : ℕ} [Fact l.Prime]

attribute [-instance] GroundTheory.PAdicHodge.subfield_valuativeRel GroundTheory.PAdicHodge.subfield_compatible GroundTheory.PAdicHodge.subfield_isValuativeTopology GroundTheory.PAdicHodge.subfield_isNontrivial GroundTheory.PAdicHodge.isNonarchimedeanLocalField_intermediateField GroundTheory.PAdicHodge.isNonarchimedeanLocalField_tower GroundTheory.PAdicHodge.valuativeExtension_padic GroundTheory.PAdicHodge.valuativeExtension_intermediateField GroundTheory.PAdicHodge.subfield_isUltrametricDist

theorem unramifiedDegree_eq_one_of_fix (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (g : Om l ≃ₐ[↥K.1] Om l)
    (h : ∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) :
    unramifiedDegree ↥K.1 (Om l) g = 1 := by
  rw [unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, GlobalTheory.CompanionTheory.LTLink.natCast_residue_eq_zero (l := l) (F := ↥K.1), zero_mul]
  exact h _ (GroundTheory.PAdicHodge.mem_unramifiedClosure_of_pow_eq_one (Nat.pos_of_ne_zero hm0)
    (((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hcop).symm) hζm)

theorem exists_norm_unit (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (u : 𝒪[↥K.1]ˣ) :
    ∃ v : ℤ_[l]ˣ, ((v : ℤ_[l]) : ℚ_[l]) = Algebra.norm ℚ_[l] ((u : 𝒪[↥K.1]) : ↥K.1) := by
  have hint : ∀ a : 𝒪[↥K.1], ∃ y : ℤ_[l], (y : ℚ_[l]) = Algebra.norm ℚ_[l] (a : ↥K.1) := by
    intro a
    have h1 : IsIntegral ℤ_[l] (a : ↥K.1) :=
      (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr
        ((GlobalTheory.CompanionTheory.LTHodge.UnitAct.valuation_le_one_iff (a : ↥K.1)).mp a.2)
    have h2 : IsIntegral ℤ_[l] (Algebra.norm ℚ_[l] (a : ↥K.1)) := Algebra.isIntegral_norm ℚ_[l] h1
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hint (u : 𝒪[↥K.1])
  obtain ⟨y', hy'⟩ := hint ((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1])
  have hm : ((y * y' : ℤ_[l]) : ℚ_[l]) = 1 := by
    rw [PadicInt.coe_mul, hy, hy', ← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]
    simp
  have hm1 : y * y' = 1 := by
    apply Subtype.ext
    exact hm
  exact ⟨⟨y, y', hm1, by rw [mul_comm]; exact hm1⟩, hy⟩

theorem toZModPow_eq_of_pow (a b : ℤ_[l])
    (h : ∀ (n : ℕ) (ζ : Om l), ζ ^ l ^ n = 1 →
      ζ ^ (PadicInt.toZModPow n a).val = ζ ^ (PadicInt.toZModPow n b).val) : a = b := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  have hl : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have : NeZero (l ^ n) := ⟨hl.ne'⟩
  have : NeZero ((l ^ n : ℕ) : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ z : Om l, IsPrimitiveRoot z (l ^ n) :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n)
  have h1 := h n ζ hζ.pow_eq_one
  have h2 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
  exact ZMod.val_injective _ h2

theorem mem_maximalAbelian {n : ℕ} {ζ : Om l} (hζ : ζ ^ l ^ n = 1) :
    ζ ∈ maximalAbelianExtension ℚ_[l] (Om l) := by
  rw [GroundTheory.LocalField.Padic.maximalAbelianExtension_eq_adjoin_rootsOfUnity l (Om l)]
  exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, hζ⟩

theorem norm_eq_cyclo : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ), IsLTChar K χ →
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  intro l _ K χ hχ _ g hg hfix
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hR : Set.range (algebraMap ↥K.1 (Om l)) = (K.1 : Set (Om l)) := Subtype.range_coe
  obtain ⟨π, hπ, hmain⟩ := GlobalTheory.CompanionTheory.LTHodge.UnitAct.main hχ (F := ↥K.1) hR
  let g' : ↥(GK K) := ⟨g, hg⟩
  let τ : Om l ≃ₐ[↥K.1] Om l := GlobalTheory.CompanionTheory.LTHodge.CharEx.gal K g'
  obtain ⟨u, huχ, hact⟩ := hmain τ g' (fun y => rfl)
  have hdeg : unramifiedDegree ↥K.1 (Om l) τ = 1 := unramifiedDegree_eq_one_of_fix K τ hfix
  have hart := GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia hπ (isLubinTateSeries_ltPoly π) u τ hdeg hact
  obtain ⟨v, hv⟩ := exists_norm_unit K u
  have hχu : ((χ g' : (↥K.1)ˣ) : ↥K.1) = ((u : 𝒪[↥K.1]) : ↥K.1) := Subtype.ext huχ.symm
  change Algebra.norm ℚ_[l] ((χ g' : (↥K.1)ˣ) : ↥K.1) = _
  rw [hχu, ← hv]

  let x : (↥K.1)ˣ := unitsIncl ↥K.1 u⁻¹
  let w : ℚ_[l]ˣ := normUnits ℚ_[l] ↥K.1 x
  have hw : (w : ℚ_[l]) = (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * (l : ℚ_[l]) ^ (0 : ℤ) := by
    have e1 : (w : ℚ_[l]) = Algebra.norm ℚ_[l] ((x : (↥K.1)ˣ) : ↥K.1) := coe_normUnits x
    have e2 : ((x : (↥K.1)ˣ) : ↥K.1) * ((u : 𝒪[↥K.1]) : ↥K.1) = 1 := by
      have h := congrArg (fun c : 𝒪[↥K.1] => (c : ↥K.1)) (Units.inv_mul u)
      simpa [x, unitsIncl] using h
    have e3 : (w : ℚ_[l]) * ((v : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [e1, hv, ← map_mul, e2, map_one]
    have e4 : ((v : ℤ_[l]) : ℚ_[l]) * (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
    rw [zpow_zero, mul_one]
    calc (w : ℚ_[l]) = (w : ℚ_[l]) * (((v : ℤ_[l]) : ℚ_[l]) * (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) := by
          rw [e4, mul_one]
      _ = _ := by rw [← mul_assoc, e3, one_mul]
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (localReciprocityLimit ℚ_[l] (Om l) w)
  have key : ∀ (n : ℕ) (ζ : Om l), ζ ^ l ^ n = 1 → g ζ = σ ζ := by
    intro n ζ hζ
    have hy := mem_maximalAbelian hζ
    have h1 := hart ζ (maximalAbelianExtension_le_restrictScalars K.1 hy)
    have h2 := localArtinMap_apply_of_mem K.1 x hy
    have h3 : localArtinMap ℚ_[l] (Om l) (normUnits ℚ_[l] ↥K.1 x) =
        topologicalAbelianizationEquiv ℚ_[l] (Om l) (σ : TopologicalAbelianization (Om l ≃ₐ[ℚ_[l]] Om l)) := by
      rw [localArtinMap_apply]
      exact congrArg _ hσ.symm
    rw [h3, topologicalAbelianizationEquiv_mk_apply] at h2
    exact h1.symm.trans h2
  have hfin : (v : ℤ_[l]) = ((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) := by
    refine toZModPow_eq_of_pow _ _ fun n ζ hζ => ?_
    have h1 := GroundTheory.PAdicHodge.cycloChar_spec (K := ⊥) (Formalism.Per6.toBot g) hζ
    have h2 := GroundTheory.LocalField.Padic.apply_of_pow_eq_one_of_prime_pow l w v⁻¹ 0 hw hσ hζ
    rw [inv_inv] at h2
    rw [← h2, ← key n ζ hζ]
    exact h1
  rw [hfin]

end GlobalTheory.CompanionTheory.LTNorm
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BaireCoset

open scoped Pointwise

theorem baire_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (P : Subgroup G), IsClosed (P : Set G) → ∀ Kc : Set G, IsCompact Kc → (∀ g, ∃ p ∈ P, ∃ c ∈ Kc, g = p * c) → ∀ L : ℕ → Subgroup G, Monotone L → (∀ j, IsCompact (L j : Set G)) → ∀ (x : G) (S : Set G), IsOpen S → (∀ p ∈ P, ∀ g ∈ S, p * g ∈ S) → IsClosed (S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n}) → ∃ j, ∀ g ∈ S, (∃ p ∈ P, ∃ j', ∃ n ∈ L j', g = p * x * n) → ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n := by
  intro G _ _ _ _ _ P hP Kc hKc hcov L hL hLc x S hS hSP hT
  set C : Set G := {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n} with hC
  let A : ℕ → Set G := fun j => {g | ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n}
  have hAmono : ∀ {i j}, i ≤ j → A i ⊆ A j := by
    rintro i j hij g ⟨p, hp, n, hn, rfl⟩
    exact ⟨p, hp, n, hL hij hn, rfl⟩
  have hCA : ∀ g ∈ C, ∃ j, g ∈ A j := by
    rintro g ⟨p, hp, j, n, hn, rfl⟩
    exact ⟨j, p, hp, n, hn, rfl⟩
  have hAclosed : ∀ j, IsClosed (A j) := by
    intro j
    have hc : IsCompact ((fun n : G => x * n) '' (L j : Set G)) :=
      (hLc j).image (continuous_const.mul continuous_id)
    have hEq : A j = (P : Set G) * ((fun n : G => x * n) '' (L j : Set G)) := by
      ext g
      constructor
      · rintro ⟨p, hp, n, hn, rfl⟩
        exact Set.mem_mul.2 ⟨p, hp, x * n, ⟨n, hn, rfl⟩, (mul_assoc _ _ _).symm⟩
      · intro h
        obtain ⟨p, hp, _, ⟨n, hn, rfl⟩, rfl⟩ := Set.mem_mul.1 h
        exact ⟨p, hp, n, hn, (mul_assoc _ _ _).symm⟩
    rw [hEq]
    exact hP.mul_right_of_isCompact hc
  have hCP : ∀ p ∈ P, ∀ g ∈ C, p * g ∈ C := by
    rintro p hp g ⟨q, hq, j, n, hn, rfl⟩
    exact ⟨p * q, P.mul_mem hp hq, j, n, hn, by simp only [mul_assoc]⟩
  have hCL : ∀ j, ∀ m ∈ L j, ∀ g ∈ C, g * m ∈ C := by
    rintro j m hm g ⟨q, hq, i, n, hn, rfl⟩
    exact ⟨q, hq, max i j, n * m,
      (L (max i j)).mul_mem (hL (le_max_left i j) hn) (hL (le_max_right i j) hm),
      by simp only [mul_assoc]⟩
  by_cases hne : (S ∩ C).Nonempty
  · haveI : Nonempty ↥(S ∩ C) := hne.to_subtype
    haveI : LocallyCompactSpace ↥(S ∩ C) := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
    obtain ⟨j0, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
      (f := fun j => ((↑) : ↥(S ∩ C) → G) ⁻¹' A j)
      (fun j => (hAclosed j).preimage continuous_subtype_val)
      (by
        refine Set.eq_univ_of_forall fun t => ?_
        obtain ⟨j, hj⟩ := hCA t t.2.2
        exact Set.mem_iUnion.2 ⟨j, hj⟩)
    obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1
      (isOpen_interior (s := ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0))
    have hyV : (y : G) ∈ V := by
      have h : y ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := by rw [hVeq]; exact hy
      exact h
    have hVA : ∀ g ∈ V, g ∈ S → g ∈ C → g ∈ A j0 := by
      intro g hgV hgS hgC
      have h : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := hgV
      rw [hVeq] at h
      have h2 : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0 := interior_subset h
      exact h2
    obtain ⟨p, hp, n, hn, hyeq⟩ := hVA y hyV y.2.1 y.2.2
    let V₁ : Set G := (fun g => p * g * n) ⁻¹' (V ∩ S)
    have hV₁o : IsOpen V₁ :=
      (hV.inter hS).preimage ((continuous_const.mul continuous_id).mul continuous_const)
    have hxV₁ : x ∈ V₁ := by
      show p * x * n ∈ V ∩ S
      rw [← hyeq]
      exact ⟨hyV, y.2.1⟩
    have hnL : ∀ g ∈ V₁, g ∈ C → g ∈ A j0 := by
      intro g hgV hgC
      obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hVA (p * g * n) hgV.1 hgV.2 (hCL j0 n hn _ (hCP p hp g hgC))
      refine ⟨p⁻¹ * p₂, P.mul_mem (P.inv_mem hp) hp₂, n₂ * n⁻¹,
        (L j0).mul_mem hn₂ ((L j0).inv_mem hn), ?_⟩
      calc g = p⁻¹ * (p * g * n) * n⁻¹ := by group
        _ = p⁻¹ * (p₂ * x * n₂) * n⁻¹ := by rw [e]
        _ = p⁻¹ * p₂ * x * (n₂ * n⁻¹) := by group
    let O : ℕ → Set G := fun j => ⋃₀ {W | IsOpen W ∧ W ∩ C ⊆ A j}
    have hOo : ∀ j, IsOpen (O j) := fun j => isOpen_sUnion fun W hW => hW.1
    have hOm : Monotone O := fun i j hij =>
      Set.sUnion_subset_sUnion fun W hW => ⟨hW.1, hW.2.trans (hAmono hij)⟩
    have hOA : ∀ j, O j ∩ C ⊆ A j := by
      rintro j g ⟨⟨W, hW, hgW⟩, hgC⟩
      exact hW.2 ⟨hgW, hgC⟩
    have hAO : ∀ j, j0 ≤ j → A j ⊆ O j := by
      rintro j hj _ ⟨p', hp', m, hm, rfl⟩
      refine ⟨(fun g => p'⁻¹ * g * m⁻¹) ⁻¹' V₁,
        ⟨hV₁o.preimage ((continuous_const.mul continuous_id).mul continuous_const), ?_⟩, ?_⟩
      · rintro g ⟨hgW, hgC⟩
        have hu : p'⁻¹ * g * m⁻¹ ∈ C :=
          hCL j _ ((L j).inv_mem hm) _ (hCP _ (P.inv_mem hp') g hgC)
        have hu' : p'⁻¹ * g * m⁻¹ ∈ A j := hAmono hj (hnL _ hgW hu)
        obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hu'
        refine ⟨p' * p₂, P.mul_mem hp' hp₂, n₂ * m, (L j).mul_mem hn₂ hm, ?_⟩
        calc g = p' * (p'⁻¹ * g * m⁻¹) * m := by group
          _ = p' * (p₂ * x * n₂) * m := by rw [e]
          _ = p' * p₂ * x * (n₂ * m) := by group
      · show p'⁻¹ * (p' * x * m) * m⁻¹ ∈ V₁
        have : p'⁻¹ * (p' * x * m) * m⁻¹ = x := by group
        rw [this]
        exact hxV₁
    obtain ⟨i, hi⟩ := (hKc.inter_right hT).elim_directed_cover O hOo
      (by
        rintro g ⟨_, hgS, hgC⟩
        obtain ⟨j, hj⟩ := hCA g hgC
        exact Set.mem_iUnion.2 ⟨max j j0,
          hAO _ (le_max_right j j0) (hAmono (le_max_left j j0) hj)⟩)
      hOm.directed_le
    refine ⟨i, fun g hgS hgC => ?_⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    have hcS : c ∈ S := by
      have := hSP q⁻¹ (P.inv_mem hq) _ hgS
      rwa [inv_mul_cancel_left] at this
    have hcC : c ∈ C := by
      have := hCP q⁻¹ (P.inv_mem hq) _ hgC
      rwa [inv_mul_cancel_left] at this
    obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hOA i ⟨hi ⟨hc, hcS, hcC⟩, hcC⟩
    exact ⟨q * p₂, P.mul_mem hq hp₂, n₂, hn₂, by rw [e]; simp only [mul_assoc]⟩
  · refine ⟨0, fun g hgS hgC => ?_⟩
    exact absurd ⟨g, hgS, hgC⟩ hne

end GlobalTheory.CompanionTheory.BaireCoset
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensorRank

theorem rank_piTensorProduct_le_one {α : Type} [Fintype α] (M : α → Type)
    [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)]
    (h : ∀ a, Module.rank ℂ (M a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  choose v₀ hv₀ using fun a => rank_le_one_iff.mp (h a)
  rw [rank_le_one_iff]
  refine ⟨PiTensorProduct.tprod ℂ v₀, fun x => ?_⟩
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    choose c hc using fun a => hv₀ a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • v₀ a := funext fun a => (hc a).symm
    rw [hf, MultilinearMap.map_smul_univ, mul_smul]
    simp only [RingHom.id_apply]
  · rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by rw [add_smul, hr, hs]⟩

end GlobalTheory.CompanionTheory.TensorRank
end

section

open Matrix

theorem _root_.GlobalTheory.T.relIndex_lattice_eq_haar_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k) (A₀ A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → A₀ ≤ A → A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom → ((A₀.relIndex A : ℕ) : ℝ) = (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) * ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | exact GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | (intros; apply GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul <;> assumption)
end
