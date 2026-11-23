module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle390
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.Cusp.ConjLevi

variable {D : D7} {V : HSp D}

theorem ratAct_mul_apply (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one_apply (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem ratAct_inv_apply (g : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V g⁻¹ (GlobalTheory.Cusp.ratAct D.sp.cm V g v) = v := by
  rw [← ratAct_mul_apply, inv_mul_cancel, ratAct_one_apply]

theorem conj_maps (γ g : GF V) (S : Submodule D.host.E V.V)
    (h : ∀ v ∈ S, GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ S) :
    ∀ w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g),
      GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ * g⁻¹) w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [ratAct_mul_apply, ratAct_inv_apply, ratAct_mul_apply]
  exact ⟨_, h y hy, rfl⟩

theorem map_span_range (g : GF V) {a : ℕ} (x : Fin a → V.V) (y : Fin a → V.V)
    (hx : ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = y i) :
    (Submodule.span D.host.E (Set.range x)).map (GlobalTheory.Cusp.ratAct D.sp.cm V g) =
      Submodule.span D.host.E (Set.range y) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hx i

end GlobalTheory.Cusp.ConjLevi


open GlobalTheory.Cusp.ConjLevi in
theorem GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) (γ g : GF V) {a : ℕ} (ha : a ≤ wittIndex V) (j : Fin (wittIndex V)), j.val + 1 = a → ∀ (x x' : Fin a → V.V), (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i)) → (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i)) → (∀ v ∈ Submodule.span D.host.E (Set.range x), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x)) → (∀ v ∈ Submodule.span D.host.E (Set.range x'), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x')) → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) {stdVec j} := by
  intro D V Φ γ g a ha j hj x x' hx hx' h1 h2
  have hmem : ∀ i : Fin (wittIndex V), i ≤ j ↔ ∃ k : Fin a, Fin.castLE ha k = i := fun i => by
    constructor
    · intro hi
      exact ⟨⟨i.val, by have := Fin.le_def.1 hi; omega⟩, Fin.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact Fin.le_def.2 (by simp only [Fin.val_castLE]; omega)
  have hE : Φ.sub (stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.e (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      exact Or.inl ⟨_, by rw [if_pos ((hmem _).2 ⟨k, rfl⟩)], rfl⟩
  have hF : Φ.sub (-stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.f (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec, Pi.neg_apply]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      refine Or.inr ⟨_, ?_, rfl⟩
      rw [if_pos ((hmem _).2 ⟨k, rfl⟩)]
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  unfold WittFrame.levi
  simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hE, ← map_span_range g x _ hx]
    exact conj_maps γ g _ h1
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hF, ← map_span_range g x' _ hx']
    exact conj_maps γ g _ h2
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.WittCarry

theorem exists_GF_carry_hyperbolic : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) {a : ℕ} (ha : a ≤ wittIndex V) (x x' : Fin a → V.V), LinearIndependent D.host.E (Sum.elim x x') → (∀ i j, V.hD (x i) (x j) = 0) → (∀ i j, V.hD (x' i) (x' j) = 0) → (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) → ∃ g : GF V, ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i) ∧ GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i) := by
  intro D V Φ a ha x x' hli h1 h2 h3
  classical
  have hs : ∀ u w, star (V.hT u w) = V.hT w u := fun u w => V.herm.eq u w
  have hn : ∀ u, (∀ w, V.hT u w = 0) → u = 0 := fun u hu => V.nondeg.1 u hu
  have sw : ∀ u w, V.hD u w = star (V.hD w u) := fun u w => (hs u w).symm
  have hcast : ∀ i j : Fin a, (Fin.castLE ha i = Fin.castLE ha j) ↔ i = j :=
    fun i j => (Fin.castLE_injective ha).eq_iff
  let e' : Fin a → V.V := fun i => Φ.e (Fin.castLE ha i)
  let f' : Fin a → V.V := fun i => Φ.f (Fin.castLE ha i)
  have hli' : LinearIndependent D.host.E (Sum.elim e' f') := by
    refine LinearIndependent.of_pairwise_dual_eq_zero_one _
      (Sum.elim (fun i => V.hT (f' i)) (fun i => V.hT (e' i))) ?_ ?_
    · rintro (i | i) (j | j) hij
      · have : Fin.castLE ha j ≠ Fin.castLE ha i := fun h => hij (congrArg Sum.inl ((hcast j i).1 h).symm)
        exact (Φ.ef _ _).trans (if_neg this)
      · exact Φ.ff _ _
      · exact Φ.ee _ _
      · have : Fin.castLE ha i ≠ Fin.castLE ha j := fun h => hij (congrArg Sum.inr ((hcast i j).1 h))
        show V.hD (f' j) (e' i) = 0
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j))) = 0
        rw [Φ.ef, if_neg this, star_zero]
    · rintro (i | i)
      · exact (Φ.ef _ _).trans (if_pos rfl)
      · show V.hD (f' i) (e' i) = 1
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha i))) = 1
        rw [Φ.ef, if_pos rfl, star_one]
  have hg : ∀ p q, V.hT (Sum.elim x x' p) (Sum.elim x x' q) = V.hT (Sum.elim e' f' p) (Sum.elim e' f' q) := by
    rintro (i | i) (j | j)
    · show V.hD (x j) (x i) = V.hD (e' j) (e' i)
      rw [h1, Φ.ee]
    · show V.hD (x' j) (x i) = V.hD (f' j) (e' i)
      rw [sw, sw (f' j)]
      show star (V.hD (x i) (x' j)) = star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j)))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x j) (x' i) = V.hD (e' j) (f' i)
      show _ = V.hD (Φ.e (Fin.castLE ha j)) (Φ.f (Fin.castLE ha i))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x' j) (x' i) = V.hD (f' j) (f' i)
      rw [h2, Φ.ff]
  obtain ⟨g, hgB, hgv⟩ := GlobalTheory.LocOver.WittFrames.exists_isom_of_gram witt_extension_theorem V.hT hs hn _ _ hli hli' hg
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.toLinearMap
  let N : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.symm.toLinearMap
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  let U : GL (Fin V.rank) D.host.E := ⟨M, N, hMN, hNM⟩
  have hrat : ∀ γ : GF V, γ.1 = U → GlobalTheory.Cusp.ratAct D.sp.cm V γ = g.toLinearMap := fun γ h => by
    show Matrix.toLin V.frame V.frame γ.1.1 = _
    rw [h]; exact Matrix.toLin_toMatrix _ _ _
  refine ⟨⟨U, ?_⟩, fun i => ?_⟩
  · show Formalism.UG.cT _ M * V.gram * M = V.gram
    funext i j
    have hexp : ∀ k, g (V.frame k) = ∑ l, M l k • V.frame l := fun k => by
      conv_lhs => rw [← V.frame.sum_repr (g (V.frame k))]
      simp [M, LinearMap.toMatrix_apply]
    rw [show V.gram i j = V.hT (V.frame i) (V.frame j) from rfl, ← hgB, hexp, hexp]

    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    have hσ : ∀ z, (D.sp.cm.sig : D.host.E →+* D.host.E) z = star z := fun z => rfl
    simp only [hσ, starRingEnd_apply, HSpace.gram, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [hrat _ rfl]
    exact ⟨hgv (Sum.inl i), hgv (Sum.inr i)⟩

end GlobalTheory.WittCarry
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SplitApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU.Supp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

theorem det_ne_zero_of_map {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) (h : (J.map f).det ≠ 0) :
    J.det ≠ 0 := by
  intro h0
  apply h
  rw [show J.map f = f.mapMatrix J from rfl, ← RingHom.map_det, h0, map_zero]


omit [NumberField E] in
theorem cA_apply (y : AF F ⊗[F] E) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ y = sigR (AF F) σ y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]


omit [NumberField F] in
theorem isHermND_smul_transpose {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hs : ∀ i j, σ (J j i) = -J i j)
    (hd : J.det ≠ 0) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) : IsHermND σ (δ • Jᵀ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hσδ, hs j i]
    ring
  · rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hδ) hd

theorem mem_UG_iff_mem_HR {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0)
    (g : GL (Fin n) (AF F ⊗[F] E)) :
    g ∈ GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) ↔ g ∈ HR (AF F) σ (δ • Jᵀ) := by
  set G : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) with hG
  set K := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J with hK
  have hc : G.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = G.map (sigR (AF F) σ) := by
    ext i j; exact cA_apply _
  have hJR : JR (AF F) (δ • Jᵀ) = inclR (F := F) (AF F) δ • Kᵀ := by
    ext i j; simp [JR, hK, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
  have hunit : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
  show Gᵀ * K * G.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = K ↔
    Formalism.UG.cT (sigR (AF F) σ) G * JR (AF F) (δ • Jᵀ) * G = JR (AF F) (δ • Jᵀ)
  rw [hc, hJR, Formalism.UG.cT]
  constructor
  · intro h
    have h1 := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h1
    rw [Matrix.mul_smul, Matrix.smul_mul, h1]
  · intro h
    have h' : (G.map (sigR (AF F) σ))ᵀ * Kᵀ * G = Kᵀ := by
      have h1 := congrArg (fun M => inclR (F := F) (AF F) δ⁻¹ • M) h
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hunit, one_smul] at h1
      exact h1
    have h1 := congrArg Matrix.transpose h'
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at h1
    exact h1

def toUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) :
    HA (AF F) σ (δ • Jᵀ) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J where
  toFun g := ⟨HA.mat (AF F) σ _ g, (mem_UG_iff_mem_HR J hδ _).2 (show HR (AF F) σ (δ • Jᵀ) from g).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_toUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) :
    Continuous (toUA (σ := σ) J hδ) :=
  Continuous.subtype_mk (continuous_subtype_val (p := fun g => g ∈ HR (AF F) σ (δ • Jᵀ))) _

theorem isPlacesIdem_placeIdem (v : HeightOneSpectrum (𝓞 F)) : GlobalTheory.Published.IsPlacesIdem ∅ {v} (placeIdem v) :=
  ⟨fun w hw => absurd hw (Finset.notMem_empty w), fun _ _ => rfl,
    fun u hu => by rw [Finset.mem_singleton.1 hu]; exact GlobalTheory.AdelicU.evalV_singleFin_self v 1,
    fun u hu => GlobalTheory.AdelicU.evalV_singleFin_ne (fun h => hu (Finset.mem_singleton.2 h)) 1⟩

theorem mul_placeIdem {v : HeightOneSpectrum (𝓞 F)} {u : AF F} (hu : GlobalTheory.AdelicU.evFin F v u = 0) :
    u * placeIdem v = 0 := by
  have h2 : sndA F u * GlobalTheory.AdelicU.singleFin v 1 = 0 := by
    apply RestrictedProduct.ext
    intro w
    change evalV F w (sndA F u * GlobalTheory.AdelicU.singleFin v 1) = 0
    rw [map_mul]
    by_cases e : w = v
    · subst e; rw [show evalV F w (sndA F u) = 0 from hu, zero_mul]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, mul_zero]
  exact Prod.ext (mul_zero _) h2

omit [NumberField E] in
theorem singleTens_mul_self {v : HeightOneSpectrum (𝓞 F)} (y : Fv F v ⊗[F] E) :
    singleTens E v y * singleTens E v y = singleTens E v (y * y) := (map_mul _ _ _).symm

theorem splitIdemAd_mul_self (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) :
    splitIdemAd h τ * splitIdemAd h τ = splitIdemAd h τ := by
  rw [splitIdemAd, singleTens_mul_self, GlobalTheory.AdelicU.splitIdem_mul_self]

theorem splitIdemAd_mul_sigR (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) :
    splitIdemAd h τ * sigR (AF F) σ (splitIdemAd h τ) = 0 := by
  rw [splitIdemAd, sigR_singleTens, GlobalTheory.AdelicU.sigR_splitIdem, ← map_mul, mul_sub, mul_one,
    GlobalTheory.AdelicU.splitIdem_mul_self, sub_self, map_zero]

theorem splitIdemAd_add_sigR (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) :
    splitIdemAd h τ + sigR (AF F) σ (splitIdemAd h τ) = algebraMap (AF F) (AF F ⊗[F] E) (placeIdem v) := by
  rw [splitIdemAd, sigR_singleTens, GlobalTheory.AdelicU.sigR_splitIdem, ← map_add (f := _), add_sub_cancel, singleTens_one]

theorem strongApprox_split : GlobalTheory.Published.StrongApproxSU → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : Bs.P) (s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J), (mat s).det = 1 →
      s ∈ closure {x | ∃ γ ∈ ratU σ Γ.W.J, ∃ k ∈ UAt σ Γ.W (evFin F v.1), x = γ * k} := by
  intro H F E _ _ _ _ _ σ a a' Bs Γ X om om' hT v s hs
  have hcm := hT.base.cm
  let w0 := (inferInstance : Nonempty (InfinitePlace F)).some
  have hWd : Γ.W.J.det ≠ 0 := by
    have h0 := det_ne_zero_of_hasSig (hT.geo.hW.sig w0)
    rw [Matrix.det_smul] at h0
    exact det_ne_zero_of_map _ _ (right_ne_zero_of_mul h0)
  have h2 : 2 ≤ a + a' := by have := hT.geo.aBig; omega
  obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
  have hδ : x - σ x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσδ : σ (x - σ x) = -(x - σ x) := by rw [map_sub, GlobalTheory.AdelicU.cm_conj_conj hcm, neg_sub]
  have hJ' := isHermND_smul_transpose hT.geo.hW.skew hWd hδ hσδ
  have hidem := isPlacesIdem_placeIdem (F := F) v.1
  have hnc := GlobalTheory.Published.StrongApprox.not_isCompact_split σ h2 hJ' v.1 (placeIdem v.1)
    (hidem.2.2.1 v.1 (Finset.mem_singleton_self _)) (splitIdemAd hcm (Bs.τ v)) (splitIdemAd_mul_self hcm _)
    (splitIdemAd_mul_sigR hcm _) (splitIdemAd_add_sigR hcm _)
  let s' : HA (AF F) σ ((x - σ x) • Γ.W.Jᵀ) :=
    (⟨s.1, (mem_UG_iff_mem_HR _ hδ _).1 s.2⟩ : HR (AF F) σ ((x - σ x) • Γ.W.Jᵀ))
  have hs' : s' ∈ GlobalTheory.Published.SUAdelic σ ((x - σ x) • Γ.W.Jᵀ) := GlobalTheory.Published.StrongApprox.mem_SUAdelic.2 hs
  have hcl := H F E σ hcm _ _ h2 hJ' ∅ {v.1} _ hidem hnc s' hs'
  have e : toUA Γ.W.J hδ s' = s := rfl
  rw [← e]
  refine map_mem_closure (continuous_toUA Γ.W.J hδ) hcl ?_
  rintro y ⟨γ, hγ, k, hk, rfl⟩
  refine ⟨toUA Γ.W.J hδ γ, ?_, toUA Γ.W.J hδ k, ?_, map_mul _ _ _⟩
  · obtain ⟨γ0, -, hγ0⟩ := Subgroup.mem_map.1 hγ.2
    exact Subgroup.mem_subgroupOf.2 ⟨γ0, hγ0⟩
  · intro u hu
    ext i j
    have hk2 := hk.2 i j
    change u • ((HA.mat (AF F) σ _ k).1 - 1 : Matrix (Fin (a + a')) (Fin (a + a')) (AF F ⊗[F] E)) i j = 0
    rw [Algebra.smul_def, ← hk2, ← mul_assoc, ← map_mul, mul_placeIdem hu, map_zero, zero_mul]

end GlobalTheory.SplitApprox
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.IndefR.Links (ChrEq)

noncomputable section

namespace GlobalTheory.UnrCharZeta

open GlobalTheory.LFun GlobalTheory.PRep
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open Formalism.L2.Host (HChar aboveF)
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

section Seg

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

end Seg

variable {D : D7}

section Char

variable {E : Type} [Field E] [NumberField E]

theorem loc_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    (ν⁻¹).loc w x = (ν.loc w x)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single, GlobalTheory.CMVal.finPart_inv]

theorem unrAt_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).UnrAt w ↔ ν.UnrAt w := by
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [loc_inv, inv_eq_one]

theorem val_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).val w = (ν.val w)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_unifAt, ← GlobalTheory.CMVal.finPart_unifAt, GlobalTheory.CMVal.finPart_inv]

end Char

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Global

section Bottom

open GlobalTheory.FunObj.SqNum (botBig botSmall)

end Bottom

end GlobalTheory.UnrCharZeta

end
end
