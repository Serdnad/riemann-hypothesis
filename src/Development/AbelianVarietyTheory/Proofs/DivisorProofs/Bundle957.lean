module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle923
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.GlobalFields.WeilGroups.QuasiCharacter
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import Formalism.PairingDivisors.StatementH
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle001
public import Formalism.PieriBlockIdeals.StatementE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle805
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Mathlib.Analysis.Matrix.Order

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RMDeform

theorem exists_lift_abelian (GD : GlobalTheory.Published.GrothendieckDeformation) (ADR : GlobalTheory.Published.AbelianDeRham)
    {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) {g : ℕ}
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap π) i) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (E : Submodule R (Crys κ (spMap π) A₀)) (hE : ∃ N, IsCompl E N)
    (hF : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI A₀).Corr d y) :
    ∃ (A' : Over (Sp R)) (_ : GrpObj A') (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ liftFil κ h' = E := by
  obtain ⟨HC, HL, -⟩ := GD R I κ hκ R₀ π hπ hI
  have b := (HC g A₀ A i h hA hg).1
  have c := HC.crysToDR_bijective h hA hg
  obtain ⟨N, hN⟩ := hE
  have adm : GlobalTheory.Published.GrothendieckMessing.IsAdmissible h (E.map (crysToDR κ h)) := by
    refine ⟨⟨N.map (crysToDR κ h), (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).isCompl hN⟩,
      fun y ↦ ?_⟩
    rw [hF]
    constructor
    · rintro ⟨d, hd, e⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).2 e⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, e⟩
      exact ⟨d, hd, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).1 e⟩
  obtain ⟨A', _, i', h', hA', hg', e⟩ := HL g A₀ A i h hA hg _ adm
  exact ⟨A', inferInstance, i', h', hA', hg', by rw [e, Submodule.comap_map_eq_of_injective c.1]⟩

theorem lbIso_pull_square {X₀ X Y₀ Y : Scheme.{0}} {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB)
    {l : X₀ ⟶ X} (e : LBIso (P.pull l) P₀) (a₀ : Y₀ ⟶ X₀) (a : Y ⟶ X) (y : Y₀ ⟶ Y) (w : a₀ ≫ l = y ≫ a) :
    LBIso (P₀.pull a₀) ((P.pull a).pull y) := by
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hP₀, ← (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP l) hP₀).2 e, GlobalTheory.CechPic.cls_pull hP,
    GlobalTheory.CechPic.cls_pull (pull_isLB hP a), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp,
    ← GlobalTheory.CechPic.pull_comp, w]

end GlobalTheory.RMDeform
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finite_omega_of_eq_zero {p : ℕ} {K : Type} [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) : Module.Finite K G.omega := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm

theorem finrank_rigExt_omega (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) :
    Module.Finite K G.omega ∧ Module.Finite K ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) ∧ Module.finrank K ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) = G.height ∧
      Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  have h1 := finite_omega_of_eq_zero h G
  have h2 := finite_omega_of_eq_zero h G.dual
  have e1 : Module.finrank K G.omega = Module.finrank K (Cot K (G.A 1)) :=
    (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).finrank_eq
  have e2 : Module.finrank K G.dual.omega = Module.finrank K (Cot K (G.dual.A 1)) :=
    (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective h)).finrank_eq
  have hsum : Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
    rw [e1, e2]
    exact le_antisymm (GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height p K h G) (GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim p K h G)

  have hr := (G.rigToLie h).rank_range_add_rank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), rank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    (LinearEquiv.ofInjective _ (G.rigOfOmega_injective_of_eq_zero h)).rank_eq.symm] at hr
  have hfin : Module.Finite K G.RigExt := by
    haveI : Module.Free K G.RigExt := Module.Free.of_divisionRing K _
    rw [← Module.rank_lt_aleph0_iff, ← hr]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 K _) (Module.rank_lt_aleph0 K _)
  refine ⟨h1, hfin, ?_, hsum⟩
  have e := (G.rigToLie h).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), finrank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    LinearMap.finrank_range_of_inj (G.rigOfOmega_injective_of_eq_zero h)] at e
  change Module.finrank K G.RigExt = G.height
  rw [← e, ← hsum, add_comm, Subspace.dual_finrank_eq]

end GlobalTheory.PDivGroup
end

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory

theorem inZl_of_twisted_difference {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime]
    (g : G) (q : ℕ) (hq : l ∣ q) (x : G → ℚ)
    (hx : ∀ C, InZl l (x C - (q : ℚ) * x (C * g))) : ∀ C, InZl l (x C) := by
  by_contra h
  push_neg at h
  obtain ⟨C0, hC0⟩ := h
  obtain ⟨C, hC⟩ := Finite.exists_max (fun C => ‖((x C : ℚ) : ℚ_[l])‖)
  have h0 : 1 < ‖((x C0 : ℚ) : ℚ_[l])‖ := by
    unfold InZl at hC0; push_neg at hC0; exact hC0
  have h1 : 1 < ‖((x C : ℚ) : ℚ_[l])‖ := lt_of_lt_of_le h0 (hC C0)
  have hqn : ‖((q : ℚ) : ℚ_[l])‖ < 1 := by
    rw [Rat.cast_natCast]
    exact Padic.norm_natCast_lt_one_iff.2 hq
  have hy : ‖(((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l])‖ ≤ 1 := hx C
  have hsplit : ((x C : ℚ) : ℚ_[l]) =
      (((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l]) + ((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l]) := by
    push_cast; ring
  have hprod : ‖((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l])‖ < ‖((x C : ℚ) : ℚ_[l])‖ := by
    rw [norm_mul]
    have hle : ‖((x (C * g) : ℚ) : ℚ_[l])‖ ≤ ‖((x C : ℚ) : ℚ_[l])‖ := hC (C * g)
    calc ‖((q : ℚ) : ℚ_[l])‖ * ‖((x (C * g) : ℚ) : ℚ_[l])‖
        ≤ ‖((q : ℚ) : ℚ_[l])‖ * ‖((x C : ℚ) : ℚ_[l])‖ :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ < 1 * ‖((x C : ℚ) : ℚ_[l])‖ :=
          mul_lt_mul_of_pos_right hqn (by linarith)
      _ = ‖((x C : ℚ) : ℚ_[l])‖ := one_mul _
  have hna := Padic.nonarchimedean (p := l)
    (((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l]) (((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l]))
  rw [← hsplit] at hna
  rcases le_max_iff.1 hna with h2 | h2
  · linarith
  · linarith

end GlobalTheory
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem monomial_eq_zmon_mul_emb {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (μ : Fin (n + 1) × Fin n →₀ ℕ)
    (hμ : ∀ s, μ (Fin.last n, s) = b s) (c : K) :
    ∃ f, (monomial μ c : BP K n) = zmon K n b * emb K n f := by
  refine ⟨C c * ∏ a : Fin n, ∏ s : Fin n, X (a, s) ^ μ (a.castSucc, s), ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_castSucc]
  simp only [hμ, zmon, emb, map_mul, map_prod, map_pow, rename_X, rename_C]
  ring

theorem eq_zmon_mul_emb_of_homogeneous {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (H : BP K n)
    (hH : IsWeightedHomogeneous (zW n) H (fun s => (b s : ℤ))) : ∃ f, H = zmon K n b * emb K n f := by
  have h : ∀ μ ∈ H.support, ∃ f, (monomial μ (AddMonoidAlgebra.coeff H μ) : BP K n) = zmon K n b * emb K n f := by
    intro μ hμ
    refine monomial_eq_zmon_mul_emb b μ (fun s => ?_) _
    have h1 := congrFun (hH (mem_support_iff.1 hμ)) s
    rw [bm_weight_zW] at h1
    exact_mod_cast h1
  choose! g hg using h
  refine ⟨∑ μ ∈ H.support, g μ, ?_⟩

  rw [map_sum, Finset.mul_sum, ← Finset.sum_congr rfl hg]
  exact H.as_sum

theorem zmon_mul_emb_injective {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) {f g : MvPolynomial (Fin n × Fin n) K}
    (h : zmon K n b * emb K n f = zmon K n b * emb K n g) : f = g := by
  have hz : zmon K n b ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (X_ne_zero _)
  refine rename_injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) ?_
    (mul_left_cancel₀ hz h)
  exact (Fin.castSucc_injective n).prodMap Function.injective_id

theorem zcomp_top_eq_zmon_mul_emb (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n)
    (hG : G ∈ dualWeyl K (n + 1) n lam) (b : Fin n → ℕ) (hb : ∀ s, b s ≤ lam s)
    (hmax : ∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) :
    ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  obtain ⟨f, hf⟩ := eq_zmon_mul_emb_of_homogeneous b _ (bmD_zcomp_isWH (fun s => (b s : ℤ)) G)
  refine ⟨f, bm_mem_dualWeyl_iff.2 ⟨fun s => ?_, fun l j hlj => ?_⟩, hf⟩
  · have h := bmD_weight lam G hG (fun s => (b s : ℤ)) s
    rw [hf, bmE_lead, bm_ndE_self] at h
    apply zmon_mul_emb_injective b
    rw [h, map_smul, mul_smul_comm, Nat.cast_sub (hb s)]
    push_cast
    rfl
  · have h := bmD_raise lam G hG (fun s => (b s : ℤ)) hmax l j hlj
    rw [hf, bmE_lead] at h
    apply zmon_mul_emb_injective b
    rw [h, map_zero, mul_zero]

end GlobalTheory.BrCompare
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HeckeNormPow

def toQC {K : Type} [Field K] [NumberField K] (χ : HChar K) : GroundTheory.Global.QuasiCharacter K where
  toMonoidHom := QuotientGroup.lift _ χ.1 (by
    rintro _ ⟨a, rfl⟩
    exact χ.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 χ.2.1

theorem norm_val_eq_rpow : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), ∃ s : ℝ,
    ∀ w : HeightOneSpectrum (𝓞 K), ‖((χ.val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ s := by
  intro K _ _ χ
  obtain ⟨s, hs⟩ := GroundTheory.Global.QuasiCharacter.exists_norm_eq_rpow (toQC χ)
  refine ⟨-s, fun w => ?_⟩
  have h1 := hs
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (unif_spec w)] at h1
  have h2 : ((χ.val w : ℂˣ) : ℂ) = (((toQC χ) (GroundTheory.Global.IdeleClassGroup.mk K
      (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w)))) : ℂˣ) : ℂ) := rfl
  rw [h2, h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

end GlobalTheory.HeckeNormPow
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.Proof.DualMatrixMetricMeans

section Mat
open scoped Matrix.Norms.L2Operator

end Mat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem meanInf_eq [_root_.NumberField.IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    meanInf K g = (1 / (nPl K : ℝ)) * ∑ v, g v := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  unfold meanInf
  rw [Formalism.HN.twist_finrank_eq K]
  field_simp

theorem meanInf_const [_root_.NumberField.IsTotallyComplex K] (c : ℝ) : meanInf K (fun _ => c) = c := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  rw [meanInf_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change 1 / (nPl K : ℝ) * ((nPl K : ℝ) * c) = c
  field_simp


end GlobalTheory.Proof.DualMatrixMetricMeans
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA

noncomputable section

namespace GlobalTheory.LeviCut

theorem eV_coe {N : ℕ} (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    (eV N ν a b x : MvPolynomial (Fin N × Fin N) ℚ) = LR.der N N a b x := by
  unfold eV
  rw [dite_eq_left ⟨a.2, b.2⟩]
  rfl

theorem cut_incl (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ K w Λ : ℕ)
    (h₁ : ∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)),
      (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i)))
    (h₂ : ∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
      (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j)))
    (hK : ∀ i j, ν i ≤ ν j + K) (hw' : K + (p + q) ≤ w + 1)
    (hΛ : ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) :
    ∀ x ∈ dualWeyl ℤ (p + q) (p + q) ν, ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x ∈ weyl ℤ (p + q) (p + q) le_rfl ν := by
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hL p q ν hν c₁ c₂ h₁ h₂
  obtain ⟨hrel, hspan, hdom, hst1, hst2⟩ := hN (p + q) ν hν
  obtain ⟨hrel', hbdd'⟩ := hA _ (p + q) K _ hrel (hB (p + q) ν hν K hK) hspan
  set e := eV (p + q) ν with he
  set S₀ := gridP (fun c d => adj (e c d)) K p q p T with hS₀
  have hinv : ∀ c < p + q, ∀ d < p + q, adj (e c d) S₀ = 0 :=
    hG _ p q K _ hrel' hbdd' T (fun c hc d hd hcd => by
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [hT1 c hc d hd hcd, sub_self])
  let v : dualWeyl ℚ (p + q) (p + q) ν := ⟨hw ℚ le_rfl ν, hwMem ℚ _ _ le_rfl ν hν⟩
  let φ : dualWeyl ℚ (p + q) (p + q) ν →ₗ[ℚ] ℚ :=
    { toFun := fun x => fockQ (hw ℚ le_rfl ν) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
      map_add' := fun x y => LR.fock_add_right _ _ _
      map_smul' := fun c x => LR.fock_smul_right _ _ _ }
  have hwz : ∀ c : Fin (p + q), wtZ ν c = ν c := fun c => by simp [wtZ]
  have hv : IsWt (p + q) e (wtZ ν) v := by
    intro c hc
    apply Subtype.ext
    have h1 := eV_coe ν ⟨c, hc⟩ ⟨c, hc⟩ v
    have h2 := (LR.der_diag_iff _ _).1 (LR.hw_rowHom ν hν) ⟨c, hc⟩
    have h3 := hwz ⟨c, hc⟩
    simp only at h1 h3
    rw [he, h1, h3]
    simpa using h2
  have hsc := hS _ p q K e (wtZ ν) v φ T hrel hdom hv (fun i j hij hj => by
    have hi : i < p + q := hij.trans hj
    have hr := LR.der_hw_raise ν ⟨i, hi⟩ ⟨j, hj⟩ hij
    have h3 := hwz ⟨i, hi⟩
    have h4 := hwz ⟨j, hj⟩
    simp only at h3 h4
    refine ⟨Subtype.ext ?_, fun x => ?_, ?_, ?_⟩
    · exact (eV_coe ν ⟨i, hi⟩ ⟨j, hj⟩ v).trans hr
    · have h1 := eV_coe ν ⟨j, hj⟩ ⟨i, hi⟩ x
      change fockQ _ (eV (p + q) ν j i x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
      simp only at h1
      rw [h1, ← LR.fock_der, hr]
      simpa using LR.fock_smul_left (0 : ℚ) 0 (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
    · rw [h3, h4]; exact_mod_cast hν (show (⟨i, hi⟩ : Fin (p + q)) ≤ ⟨j, hj⟩ from hij.le)
    · rw [h3, h4]; exact_mod_cast hK _ _) hT3
  set z : ℤ := ∏ i ∈ Finset.range p, ∏ j ∈ Finset.Ico p (p + q), (wtZ ν i - wtZ ν j + (j : ℤ) - (i : ℤ)) with hz
  have hone : (z : ℚ) • S₀ = 1 := by
    refine hSch (p + q) ν hν _ (fun c hc d hd => ?_) ?_
    · have := hinv c hc d hd
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [mul_smul_comm, smul_mul_assoc, ← he, this]
    · change φ (((z : ℚ) • S₀) v) = _
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm, hsc]
      exact hT4
  intro x hx
  let x' : dualWeyl ℚ (p + q) (p + q) ν := ⟨intQ _ _ x, (dualWeylIntRat _ _ ν x).1 hx⟩
  have hx' : x' ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν) := ⟨x, hx, rfl⟩
  have h5 := Submodule.smul_mem _ z (hI _ p q K w Λ e _ _ hst1 hst2 hw' hΛ (c₁ * c₂) T hT2 x' hx')
  rw [smul_comm, ← hS₀] at h5
  have h6 : z • S₀ x' = x' := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← LinearMap.smul_apply, hone]; rfl
  rw [h6] at h5
  obtain ⟨y, hy, hyx⟩ := h5
  have h7 : y = ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x := by
    apply map_injective (Int.castRingHom ℚ) (fun a b h => by simpa using h)
    change intQ _ _ y = intQ _ _ _
    rw [hyx, map_smul, map_smul]
    rfl
  exact h7 ▸ hy

theorem ExCut₂ (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (hD : BetaDen) : Formalism.CohomologicalDescent.E.ExCut := by
  intro N lam hlam l hl lo w hU a ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hcast : ∀ c, c = b → exZ c c le_rfl (LD.res c (fun i => lam (a + i))) l =
      exZ b b le_rfl (LD.res b (fun i => lam (a + i))) l := by rintro c rfl; rfl
  rw [hcast (a + b - a) (by omega), Nat.add_sub_cancel_left]
  have hA1 : Antitone (LD.res a lam) := fun i j hij =>
    hlam (show (Fin.castAdd b i) ≤ Fin.castAdd b j from hij)
  have hA2 : Antitone (LD.res b (fun i => lam (a + i))) := fun i j hij =>
    hlam (show (Fin.natAdd a i) ≤ Fin.natAdd a j by rw [Fin.le_def] at hij ⊢; simpa using hij)
  obtain ⟨m₁, hm₁, h₁⟩ := exact_z_specialization a a le_rfl _ hA1 l hl
  obtain ⟨m₂, hm₂, h₂⟩ := exact_z_specialization b b le_rfl _ hA2 l hl
  obtain ⟨m, hm, hden⟩ := hD l w hl
  have hsp : ∀ i j : Fin (a + b), i ≤ j → lam i + j ≤ lam j + w + i := fun i j _ => by
    have h1 := (hU i i.2).2
    have h2 := (hU j j.2).1
    simp only [UnitNormBounds.UN] at h1 h2
    omega
  have hK : ∀ i j : Fin (a + b), LD.res (a + b) lam i ≤ LD.res (a + b) lam j + (w + 1 - (a + b)) := fun i j => by
    have hpos : 0 < a + b := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
    have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ i by simp [Fin.le_def])
    have h3 := hlam (show j ≤ (⟨a + b - 1, by omega⟩ : Fin (a + b)) by rw [Fin.le_def]; have := j.2; simp only; omega)
    simp only [LD.res] at h1 h2 h3 ⊢
    omega
  have hw' : (w + 1 - (a + b)) + (a + b) ≤ w + 1 := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · omega
    · have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
      have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ ⟨a + b - 1, by omega⟩ by simp [Fin.le_def])
      simp only [LD.res] at h1 h2
      omega
  have key := cut_incl hG hA hS hI hN hB hSch hL a b (LD.res (a + b) lam) hlam _ _ _ w _ h₁ h₂ hK hw' hden
  refine Nat.sInf_le ⟨m₁ * m₂ * m ^ (a * b), ?_, fun x hx => ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
      · exact hm₁ h
      · exact hm₂ h
    · exact hm (hl.dvd_of_dvd_pow h)
  · convert key x hx using 3
    rw [pow_add, pow_add, mul_pow, ← pow_mul, mul_comm (Nat.log l w)]
    ring

theorem exCut : Formalism.CohomologicalDescent.E.ExCut :=
  ExCut₂ (GlobalTheory.T.grid_invariance_of_rank_one_two GlobalTheory.T.rank_one_projector_weight_zero_invariance GlobalTheory.T.rank_two_consecutive_projector_invariance) GlobalTheory.T.adjoint_action_endomorphism_weight_bound (GlobalTheory.T.projectorGridScalar_of_projectorScalar GlobalTheory.T.projector_value_highest_weight_vector) GlobalTheory.T.projector_grid_denominator_bound
    GlobalTheory.T.dualWeylModuleStructureGl_proof GlobalTheory.T.dualWeylWeightSpreadBound_proof GlobalTheory.T.dualWeyl_schur_endomorphism
    (GlobalTheory.T.dualWeylLeviProjectionDenominators_of_hypotheses (GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable) GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal GlobalTheory.T.dualWeyl_restriction_rowOperators) GlobalTheory.T.beta_integral_denominator_bound

end GlobalTheory.LeviCut
end
end
