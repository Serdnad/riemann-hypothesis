module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem setLIntegral_comp_addEquiv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (e : G ≃+ G) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ Γ ↔ x ∈ Γ) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) (hfin : μ F ≠ ⊤) (φ : G → ENNReal)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in F, φ (e w) ∂μ = ∫⁻ w in F, φ w ∂μ := by
  let m : G ≃ᵐ G :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  have hν : (μ.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he)
  have hF' : IsAddFundamentalDomain Γ (e ⁻¹' F) (μ.map e.symm) := by
    let f : Γ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simp)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e.symm = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  have hac : μ.map e.symm ≪ μ := hc ▸ Measure.smul_absolutelyContinuous
  have hF'' : IsAddFundamentalDomain Γ F (μ.map e.symm) := hF.mono hac
  have h1 : (μ.map e.symm) (e ⁻¹' F) = μ F := hmp.measure_preimage_equiv F
  have h2 : (μ.map e.symm) F = μ F := (hF''.measure_eq hF').trans h1
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  have hc1 : (c : ENNReal) = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [h2, one_mul])
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc2, one_smul] at hc
  have h3 : ∫⁻ w in e ⁻¹' F, φ (e w) ∂(μ.map e.symm) = ∫⁻ w in F, φ w ∂μ :=
    hmp.setLIntegral_comp_preimage_emb m.measurableEmbedding φ F
  rw [hc] at h3 hF'
  rw [← h3]
  refine hF.setLIntegral_eq hF' (fun w => φ (e w)) fun g x => ?_
  show φ (e ((g : G) + x)) = φ (e x)
  rw [map_add (f := _), hφ _ ((hΓ _).2 g.2)]

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem mt_mul (V : HSp D) (g g' : GA D V) : Formalism.L2.Theta.mt V (g * g') = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g' := rfl

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul, Matrix.mul_assoc,
    ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem symplOH_actO (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplOH S T (actO S T g h x) (actO S T g h y) = symplOH S T x y := by
  unfold symplOH
  rw [GlobalTheory.SymplOInv.symplO_actO]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem exists_actO_ratW {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ∃ y, actO S T γ γ' (ratW T S x) = ratW T S y := by
  obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actO ratW
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

theorem actO_mem_ratL {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) {x : WO S T}
    (hx : x ∈ ratL T S) : actO S T γ γ' x ∈ ratL T S := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actO_ratW hγ hγ' y
  exact ⟨z, hz.symm⟩

theorem isThetaFunO_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) :
    IsThetaFunO ψ S T fun w => f (actO S T γ γ' w) := by
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := GlobalTheory.LatLevel.continuous_actO S T γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actO_ratW hγ hγ' x
    rw [actO_add, ← symplOH_actO γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.LatLevel.actO_map_inf S T γ γ' h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← symplOH_actO γ γ' w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have h3 : ∀ t, (actO S T γ γ' (L t)).map (finPart D) = 0 := fun t => by
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem rational_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (fun w => f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ (∀ w₀, (fun w => heisO ψ S T w₀ f (actO S T γ⁻¹ γ'⁻¹ w)) = heisO ψ S T (actO S T γ γ' w₀) (fun w => f (actO S T γ⁻¹ γ'⁻¹ w))) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∫⁻ w in 𝓕, ‖f (actO S T γ⁻¹ γ'⁻¹ w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  intro D ψ hψ S T γ hγ γ' hγ' f hf
  have hi := (GQ S).inv_mem hγ
  have hi' := (GQ T).inv_mem hγ'
  refine ⟨isThetaFunO_comp hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext w
    unfold heisO
    beta_reduce
    rw [actO_add, actO_inv_actO, ← symplOH_actO γ⁻¹ γ'⁻¹ w, actO_inv_actO]
  · obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : Countable (ratL T S) := countable_of_discrete_addSubgroup _
    have hinv : ∀ x, actO S T γ γ' (actO S T γ⁻¹ γ'⁻¹ x) = x := fun x => by
      have := actO_inv_actO γ⁻¹ γ'⁻¹ x
      rwa [inv_inv, inv_inv] at this
    let e : WO S T ≃+ WO S T :=
      { toFun := actO S T γ⁻¹ γ'⁻¹
        invFun := actO S T γ γ'
        left_inv := hinv
        right_inv := actO_inv_actO γ γ'
        map_add' := actO_add _ _ }
    refine setLIntegral_comp_addEquiv (G := WO S T) (ratL T S) e (GlobalTheory.LatLevel.continuous_actO S T _ _)
      (GlobalTheory.LatLevel.continuous_actO S T _ _) (fun x => ⟨fun hx => ?_, actO_mem_ratL hi hi'⟩) μ h𝓕
      (measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hcov μ h𝓕).ne
      (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact actO_mem_ratL hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h6 : f (ratW T S y + x) = _ := hf.quasi y x
      have h7 : ‖f (ratW T S y + x)‖ = ‖f x‖ := by
        rw [h6, norm_mul, hψ.1.2.1, one_mul]
      show ‖f (ratW T S y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]

end GlobalTheory.RatSubst

end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameLawsTheta

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (realOf movS frameFn Fam)
open scoped ComplexOrder

theorem exists_isONBasis {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) :
    ∃ (p : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), IsONBasis G s B p := by
  obtain ⟨p, q, B, B', hBB', hB'B, hG, hs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2
  have hpq : p + q = n := by
    have h1 : Fintype.card (Fin n) ≤ Fintype.card (Fin p ⊕ Fin q) := by
      calc Fintype.card (Fin n) = (1 : Matrix (Fin n) (Fin n) ℂ).rank := (Matrix.rank_one).symm
        _ = (B * B').rank := by rw [hBB']
        _ ≤ B'.rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card (Fin p ⊕ Fin q) := Matrix.rank_le_card_height _
    have h2 : Fintype.card (Fin p ⊕ Fin q) ≤ Fintype.card (Fin n) := by
      calc Fintype.card (Fin p ⊕ Fin q) = (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).rank := (Matrix.rank_one).symm
        _ = (B' * B).rank := by rw [hB'B]
        _ ≤ B.rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_height _
    simp only [Fintype.card_fin, Fintype.card_sum] at h1 h2
    omega
  subst hpq
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  have hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply] <;> split_ifs <;> simp
  have he : ∀ a : Fin (p + q), Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) (e a) =
      ((if (a : ℕ) < p then 1 else -1 : ℤ) : ℂ) := by
    intro a
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · simp [e, i.isLt]
    · simp [e]
  refine ⟨p, B.submatrix id e, fun a => if (a : ℕ) < p then 1 else -1, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : (a : ℕ) < p
    · exact Or.inl ⟨by simp [ha], ha⟩
    · exact Or.inr ⟨by simp [ha], by omega⟩
  · have : (B.submatrix id e)ᴴ * G * B.submatrix id e = (Bᴴ * G * B).submatrix e e := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
        Matrix.submatrix_id_id, Matrix.conjTranspose_submatrix]
    rw [this, hG, hd, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; rw [Function.comp_apply, he a]; split_ifs with hh <;> simp [hh]
  · have : s * B.submatrix id e = (s * B).submatrix id e := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
    rw [this, hs, hd]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, id]
    erw [Matrix.mul_diagonal]
    rw [he j]
    split_ifs <;> simp

variable {D : D7}

end GlobalTheory.FrameLawsTheta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticForm_unitaryPairAction : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  first | exact @GlobalTheory.SymplOInv.symplO_actO | exact GlobalTheory.SymplOInv.symplO_actO | (intros; apply GlobalTheory.SymplOInv.symplO_actO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  first | exact @GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne | exact GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne | (intros; apply GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne <;> assumption)
end

section

namespace GlobalTheory.FrameEquiv

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem mulFun_eq_one_of_eq_one_on_maxCompact : ∀ (D : D7) (T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) → ∀ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') → (∀ k ∈ GinfC T, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) → χ k = 1) → ∀ u ∈ GinfC T, χ u = 1 :=
  fun D T θ hθ s hs χ hm hK =>
    GlobalTheory.UnitaryChar.char_eq_one D θ T hθ s hs χ hm fun k hk h => hK k hk fun τ => (h τ).symm

end GlobalTheory.FrameEquiv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.selfDual_comap_orthonormalFrame_unimodular : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).Unimod := by
  first | exact @GlobalTheory.FramePull.unimod_comap_frame | exact GlobalTheory.FramePull.unimod_comap_frame | (intros; apply GlobalTheory.FramePull.unimod_comap_frame <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeLocVals

def embField (E : Type) [Field E] [NumberField E] : IntermediateField ℚ ℂ :=
  ⨆ ψ : E →+* ℂ, ψ.toRatAlgHom.fieldRange

variable {E : Type} [Field E] [NumberField E]

instance embField_fd : FiniteDimensional ℚ (embField E) := by
  haveI : ∀ ψ : E →+* ℂ, FiniteDimensional ℚ ψ.toRatAlgHom.fieldRange := fun ψ =>
    ψ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  exact IntermediateField.finiteDimensional_iSup_of_finite

theorem emb_mem (ψ : E →+* ℂ) (k : E) : ψ k ∈ embField E :=
  le_iSup (fun ψ : E →+* ℂ => ψ.toRatAlgHom.fieldRange) ψ ⟨k, rfl⟩

theorem inf_mem_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) (k : Eˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ embField E := by
  rw [h k]
  refine prod_mem fun i _ => ?_
  have h0 : φ i (k : E) ≠ 0 := by simp
  rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ h0]
  exact zpow_mem (div_mem (emb_mem _ _) (emb_mem ((starRingEnd ℂ).comp (φ i)) (k : E))) _

theorem exists_inter_of_subfield (C : Subfield ℂ) [FiniteDimensional ℚ C] :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C : Set ℂ) ⊆ M := by
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simpa using SubfieldClass.ratCast_mem C x
  let e : C ≃ₗ[ℚ] M :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun q x => Subtype.ext (by simp [Rat.smul_def])
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨M, e.finiteDimensional, fun _ h => h⟩

end GlobalTheory.HeckeLocVals

namespace GlobalTheory.HeckeLocVals

variable {E : Type} [Field E] [NumberField E]

theorem zpow_fsum {G : Type} [CommGroup G] (a : G) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem algType_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) : ∃ m : (E →+* ℂ) → ℤ, ∀ k : Eˣ,
      ((χ.inf k : ℂˣ) : ℂ) * ∏ ψ : E →+* ℂ, ((‖ψ (k : E)‖ : ℝ) : ℂ) ^ (((0 : ℝ)) : ℂ) = ∏ ψ : E →+* ℂ, ψ (k : E) ^ m ψ := by
  classical
  refine ⟨fun ψ => ∑ i, ((if φ i = ψ then c i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0)), fun k => ?_⟩
  simp only [Complex.ofReal_zero, Complex.cpow_zero, Finset.prod_const_one, mul_one]
  rw [h k]
  let u : (E →+* ℂ) → ℂˣ := fun ψ => Units.mk0 (ψ (k : E)) (by simp)
  have hu : ∀ ψ (n : ℤ), ψ (k : E) ^ n = ((u ψ ^ n : ℂˣ) : ℂ) := fun ψ n => by
    rw [Units.val_zpow_eq_zpow_val]; rfl
  have hL : ∀ i, (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ (2 * c i) =
      ((u (φ i) ^ c i * (u ((starRingEnd ℂ).comp (φ i)) ^ c i)⁻¹ : ℂˣ) : ℂ) := fun i => by
    rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ (by simp), div_zpow]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← hu, ← hu, div_eq_mul_inv]
    rfl
  simp_rw [hL, hu]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  symm
  rw [Finset.prod_congr rfl fun ψ _ => (zpow_fsum (u ψ) Finset.univ _).trans (Finset.prod_congr rfl fun i _ => zpow_sub (u ψ) _ _),
    Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have e1 : ∏ ψ : E →+* ℂ, u ψ ^ (if φ i = ψ then c i else 0) = u (φ i) ^ c i := by
    rw [Finset.prod_eq_single (φ i) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  have e2 : ∏ ψ : E →+* ℂ, u ψ ^ (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0) =
      u ((starRingEnd ℂ).comp (φ i)) ^ c i := by
    rw [Finset.prod_eq_single ((starRingEnd ℂ).comp (φ i)) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  rw [e1, e2]

theorem locVals_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ v x, ((χ.loc v x : ℂˣ) : ℂ) ∈ M := by
  obtain ⟨m, hm⟩ := algType_of_even h
  obtain ⟨C, hC, hv⟩ := CharEx.algValsFin E χ 0 m hm
  obtain ⟨C', hC', hCC⟩ := exists_inter_of_subfield C
  refine ⟨C' ⊔ embField E, inferInstance, fun v x => ?_⟩
  have hle : GlobalTheory.Mem.Fld.valueField χ 0 ≤ C' ⊔ embField E := by
    rw [GlobalTheory.Mem.Fld.valueField_le_iff]
    intro w hw
    obtain ⟨y, hy⟩ := hv w hw
    exact ⟨⟨y, le_sup_left (a := C') (hCC y.2)⟩, hy⟩
  exact GlobalTheory.HeckeValField.mem_unitsIn.1
    (GlobalTheory.HeckeValField.loc_mem χ hle (fun k => le_sup_right (a := C') (inf_mem_of_even h k)) v x)

end GlobalTheory.HeckeLocVals
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_rational_middle_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z)) = 0) := by
  intro F E _ _ _ _ _ σ hσ K _ _ _ hd M J hM hJ hu x y hx hy
  obtain ⟨w, h1, h2⟩ := GlobalTheory.T.exists_local_unitNorm_vector_isotropic_hermitian F E σ hσ K M J hM hJ hu x y hx hy
  obtain ⟨z, hz, n1, n2⟩ := GlobalTheory.T.unitNorm_gramDet_rational_approximation F E σ hσ K hd M J hJ x y hx w h1 h2
  exact ⟨z, hz, GlobalTheory.T.unitNorm_gramDet_plane_reduction F E σ hσ K M J hJ x z hx n1, GlobalTheory.T.unitNorm_gramDet_plane_reduction F E σ hσ K M J hJ z y hz n2⟩

end GlobalTheory.PlaneNorm
end
end
