module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTriple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle295
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Mathlib.GroupTheory.Nilpotent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle297
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ),
    Nonempty (Frac Ω ε) := by
  intro Ω _ _ _ ε
  classical
  haveI : IsDomain (ring ε.range) := GlobalTheory.T.modularFunctionRingOver_isDomain ε.range
  obtain ⟨hmem, hconst⟩ := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  obtain ⟨-, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨e, he_inj, he_exp⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  obtain ⟨hexp_mem, -, -, -, -, -⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨⟨G, hG⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units

  let cst : Ω →+* ring ε.range :=
    { toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (funext fun _ => by simp)
      map_mul' := fun x y => Subtype.ext (funext fun _ => by simp)
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun x y => Subtype.ext (funext fun _ => by simp) }
  have hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x := fun _ => rfl
  have hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x := by
    intro x
    refine huniq _ _ _ (he_exp (cst x)) ?_
    simpa [hcst, HahnSeries.algebraMap_apply'] using hC x

  have hsl := fun g : GQ => GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun ε.range g hexp_mem
  choose σ hσ using hsl
  have hslc : ∀ g x, σ g (cst x) = cst x := by
    intro g x
    apply Subtype.ext
    rw [hσ]
    rfl

  have hga := fun s : Ω ≃ₐ[ℚ] Ω => GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply Ω ε s.toRingEquiv
  choose τ hτ using hga

  let A : ring ε.range →+* Mero := G.comp (ring ε.range).subtype
  have hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) := fun a => hG a
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs :=
    fun a => (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ ((hmem _).1 a.2))
  have hAunit : ∀ a, a ≠ 0 → IsUnit (A a) := by
    intro a ha
    rw [hA]
    refine (hunit _ (hdiff a) ?_).2
    intro h0
    apply ha
    have h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero) := by
      rw [h0, ← hA, map_zero]
    have heq := hid _ _ (hdiff a) (hdiff 0) h0'
    apply Subtype.ext
    funext t
    have := heq t (hHs t)
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  obtain ⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩ :=
    GlobalTheory.T.exists_fractionField_extension_of_maps Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit
  refine ⟨{
    K := K
    fld := fK
    alg := aK
    io := io
    io_inj := hinj
    io_surj := hsurj
    io_c := fun x a ha => ?_
    exp := e'
    exp_io := fun a => ?_
    sl := sl'
    sl_io := fun g a a' ha => ?_
    gal := ga'
    gal_exp := fun s f r => ?_
    an := A'
    an_io := fun a => ?_ }⟩
  · have : a = cst x := Subtype.ext ha
    rw [this, hioc]
  · rw [he']
    exact he_exp a
  · rw [hsl']
    congr 1
    exact Subtype.ext ((hσ g a).trans ha.symm)
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)
    have hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r) := by
      intro h r
      have := hΦ h r
      simpa using this
    have key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a)) := by
      intro a
      rw [hga', he', he']
      ext r
      rw [hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']
      rfl
    obtain ⟨a, b, hb, hf⟩ := hsurj f
    have hib : io b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hf' : f = io a * (io b)⁻¹ := by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]
    have hfe : e' (ga' s f) = Φ (e' f) := by
      rw [hf']
      simp only [map_mul, map_inv₀, key]
    rw [hfe, hΦ']
  · rw [hA', hA]
    rfl

end GlobalTheory.FN
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

theorem _root_.GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  first | exact @GlobalTheory.Eis.Conv.CovSkew.cover_skew | exact GlobalTheory.Eis.Conv.CovSkew.cover_skew | (intros; apply GlobalTheory.Eis.Conv.CovSkew.cover_skew <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.norm_padicModelAbscissa_le_one_of_torsion_coprime : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ (N : ℕ) (v : ℂ), 0 < N → Nat.Coprime N p → (N : ℂ) * v ∈ g.abelian₂ → v ∉ g.abelian₂ → ‖GlobalTheory.EvenTheta.xAt g v‖ ≤ 1 := by
  first | exact @GlobalTheory.TorsionAbscissa.norm_xAt_le_of_mul | exact GlobalTheory.TorsionAbscissa.norm_xAt_le_of_mul | (intros; apply GlobalTheory.TorsionAbscissa.norm_xAt_le_of_mul <;> assumption)
end

section

noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4.TopEta

open GlobalTheory.KZ GlobalTheory.NeedB GlobalTheory.KEdge

section General

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def toK : geo F K Ω →* (Ω ≃ₐ[K] Ω) :=
  MonoidHom.mk' (fun g => { (g : Ω ≃ₐ[F] Ω).toRingEquiv with commutes' := (TopW.mem_geo _).1 g.2 })
    (fun _ _ => AlgEquiv.ext fun _ => rfl)

theorem continuous_toK [Algebra.IsAlgebraic F Ω] : Continuous (toK : geo F K Ω →* (Ω ≃ₐ[K] Ω)) := by
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hsub⟩ := hs
  let b := Module.finBasis K E
  have hop : IsOpen (⋂ i, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) (b i : Ω) : Set (Ω ≃ₐ[F] Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := F) (b i : Ω)
  refine Filter.mem_map.2 (Filter.mem_of_superset ((hop.preimage continuous_subtype_val).mem_nhds ?_) ?_)
  · simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    exact fun i => Subgroup.one_mem _
  · intro g hg
    simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hg
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hlin : (((toK g).toLinearMap).comp E.val.toLinearMap) = E.val.toLinearMap :=
      b.ext fun i => hg i
    exact LinearMap.congr_fun hlin ⟨z, hz⟩

theorem exists_extend [Algebra.IsAlgebraic F Ω] {N : ℕ} {ζ α β : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)}
    (hx : ∀ g, (x g).toAdd = kum (K := F) (N := N) ζ α g) (hy : ∀ g, (y g).toAdd = kum (K := F) (N := N) ζ β g)
    (R : Subring K) (η : (Ω ≃ₐ[K] Ω) → ZMod N) (h1 : IsLocallyConstant η)
    (h2 : ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g)
    (h3 : ∀ B : ValuationSubring Ω, Over R B → ∀ g, Inert B g → η g = 0) :
    ∃ η' : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η' ∧ IsLocallyConstant (fun g : geo F K Ω => η' g) ∧
      ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over R B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η' g = 0 := by
  classical
  refine ⟨fun g => if h : g ∈ geo F K Ω then η (toK ⟨g, h⟩) else 0, fun g hg h hh => ?_, ?_, fun B g hB hi hg => ?_⟩
  · simp only [dif_pos hg, dif_pos hh, dif_pos (mul_mem hg hh)]
    rw [hx, hy]
    have e : toK (⟨g * h, mul_mem hg hh⟩ : geo F K Ω) = toK ⟨g, hg⟩ * toK ⟨h, hh⟩ := map_mul toK ⟨g, hg⟩ ⟨h, hh⟩
    rw [e]
    exact h2 (toK ⟨g, hg⟩) (toK ⟨h, hh⟩)
  · have e : (fun g : geo F K Ω => if h : (g : Ω ≃ₐ[F] Ω) ∈ geo F K Ω then η (toK ⟨(g : Ω ≃ₐ[F] Ω), h⟩) else 0) = η ∘ toK :=
      funext fun g => by rw [dif_pos g.2]; rfl
    rw [e]
    exact h1.comp_continuous continuous_toK
  · simp only [dif_pos hg]
    exact h3 B hB _ hi

end General

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem fixMu_eq {M : ℕ} (hM : M ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) :
    fixMu Ω M = (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup := by
  haveI : NeZero M := ⟨hM⟩
  unfold fixMu
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.subset_adjoin ℚ {ζ} rfl) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

attribute [local instance] algMdl

theorem normal_top [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) : Normal (topF X M) (topL X M) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have h := LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) (isPrimitiveRoot_eOm ε hM) le_rfl
  rw [← fixMu_eq hM (isPrimitiveRoot_eOm ε hM)] at h
  exact h

theorem over_iff (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M)) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    Over (FunctionField.ringOfIntegers Ω (topL X M)).toSubring B ↔
      ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) →
        algebraMap (topL X M) (topBar X M) f ∈ B := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  constructor
  · intro h f hf
    apply h
    have : ∃ P : Polynomial Ω, algebraMap (Polynomial Ω) (topL X M) P = f := by
      rcases hf with hf | ⟨c, hc⟩
      · exact ⟨Polynomial.X, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_X, hf]))⟩
      · exact ⟨C c, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_C, hc]))⟩
    obtain ⟨P, rfl⟩ := this
    exact Subalgebra.algebraMap_mem _ P
  · intro h f hf
    have hP : ∀ P : Polynomial Ω,
        ((algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M))) P ∈ B := by
      intro P
      induction P using Polynomial.induction_on with
      | C c => exact h _ (Or.inr ⟨c, ((coe_jPoly X _ _).trans (by rw [aeval_C])).symm⟩)
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | monomial k c hk =>
        rw [pow_succ, ← mul_assoc, map_mul]
        exact mul_mem hk (h _ (Or.inl ((coe_jPoly X _ _).trans (by rw [aeval_X]))))
    obtain ⟨q, hq, h0⟩ : IsIntegral (Polynomial Ω) f := hf
    let φ : Polynomial Ω →+* B := RingHom.codRestrict _ B hP
    have hi : IsIntegral B (algebraMap (topL X M) (topBar X M) f) := by
      refine ⟨q.map φ, hq.map φ, ?_⟩
      rw [eval₂_map]
      have := congrArg (algebraMap (topL X M) (topBar X M)) h0
      rw [hom_eval₂, map_zero] at this
      exact this
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hy]
    exact y.2

theorem spec_of_units [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M l n : ℕ} (hM : M ≠ 0) (hl : l ≠ 0) (hlM : l ^ n ∣ M) {u v : X.K}
    (hu : TopUnits.IsTopUnit X M u) (hv : TopUnits.IsTopUnit X M v) :
    (∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η) ∧
      ∀ φ : topGal X M, IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) φ
        (topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
          (topEta X M (topChar X M l n u) (topChar X M l n v)) φ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero Ω := algebraRat.charZero Ω
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  letI := algRat X (CongruenceSubgroup.Gamma M)
  haveI := isScalarTower_poly_rat X (CongruenceSubgroup.Gamma M)
  haveI : FiniteDimensional (RatFunc Ω) (topL X M) := GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X _ M (Nat.pos_of_ne_zero hM) le_rfl
  haveI := normal_top X hM
  haveI : Algebra.IsAlgebraic (topF X M) (topBar X M) := Algebra.IsAlgebraic.trans _ (topL X M) _
  obtain ⟨hu0, huF, huL, hu1, hu2⟩ := hu
  obtain ⟨hv0, hvF, hvL, hv1, hv2⟩ := hv
  have hN : 0 < l ^ n := Nat.pos_of_ne_zero (pow_ne_zero n hl)
  have hζ := isPrimitiveRoot_topZeta X M hl n
  have hα := topRoot_pow X M hN.ne' huL
  have hβ := topRoot_pow X M hN.ne' hvL
  have hx := topChar_apply X hl hlM huF hu0
  have hy := topChar_apply X hl hlM hvF hv0
  have ha : ∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η := by
    obtain ⟨-, -, -, -, η, h1, h2, h3⟩ := GlobalTheory.T.kummerCupProduct_coboundary_theorem Ω (topL X M) (topBar X M) (l ^ n) _ hN hζ ⟨u, huL⟩ ⟨v, hvL⟩ _ _
      (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 hα hβ
    obtain ⟨η', g1, g2, g3⟩ := exists_extend hx hy _ η h1 h2 h3
    exact ⟨η', g1, g2, fun B g hB => g3 B g ((over_iff X M B).2 hB)⟩
  refine ⟨ha, fun φ => ?_⟩
  obtain ⟨g1, g2, g3⟩ := isTopEta_topEta X M ha
  refine isTopW_topW Ω (topL X M) (topBar X M) (topF X M) (l ^ n) _ hN hζ (topGal_topZeta X hl hlM)
    (map_mem_ringOfIntegers_of_fix_mdl Ω ε X _ _) ⟨u, huF⟩ ⟨v, hvF⟩ (topRoot X M (l ^ n) u) (topRoot X M (l ^ n) v)
    (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 ?_ ?_ _ _ hx hy _ g1 g2
    (fun B g hB => g3 B g ((over_iff X M B).1 hB)) φ
  · rw [hα, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl
  · rw [hβ, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl

end GlobalTheory.K4.TopEta

namespace GlobalTheory.K4

open GlobalTheory.KZ

attribute [local instance] algMdl

end GlobalTheory.K4
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTripleData_of_neighbourTriple : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → ∀ A B C : Lat D N', Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) A) (La D (tor0 D cc δ) (stdL D N) B) (La D (tor0 D cc δ) (stdL D N) C) P N := by
  first | exact @GlobalTheory.TriangleColumns.triDat_of_tri | exact GlobalTheory.TriangleColumns.triDat_of_tri | (intros; apply GlobalTheory.TriangleColumns.triDat_of_tri <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_hermitian_log_unitaryBlockDiagonal : ∀ (p q : ℕ) (k : UpqT p q), k ∈ Kc p q → ∃ H : Mat p q, Hᴴ = H ∧ IsKC H ∧ (∀ a b, ‖H a b‖ ≤ Real.pi) ∧ UpqT.mat k = NormedSpace.exp (Complex.I • H) := by
  first | exact @GlobalTheory.CartanInt.UnitLog.exists_unitlog | exact GlobalTheory.CartanInt.UnitLog.exists_unitlog | (intros; apply GlobalTheory.CartanInt.UnitLog.exists_unitlog <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_radius_exp_sub_one_le_and_exists_log : ∀ (p q : ℕ), ∃ ρ : ℝ, 0 < ρ ∧ (∀ Y : Mat p q, l1 Y < ρ → l1 (NormedSpace.exp Y - 1) ≤ 21 / 20 * l1 Y) ∧ ∀ g : UpqT p q, l1 (UpqT.mat g - 1) < ρ → ∃ X : lieU p q, UpqT.mat g = NormedSpace.exp (X : Mat p q) ∧ l1 (X : Mat p q) ≤ 21 / 20 * l1 (UpqT.mat g - 1) := by
  first | exact @GlobalTheory.CartanInt.ExpLocal.exp_log_near_one | exact GlobalTheory.CartanInt.ExpLocal.exp_log_near_one | (intros; apply GlobalTheory.CartanInt.ExpLocal.exp_log_near_one <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_muModel_measure_of_eigenfunctional : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → ‖ι.symm α‖ = 1 → (∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ → MF (2 * e + 1) (N * l) (ch ε) a → lam B c a = 0) → (∀ a, MF (2 * e + 1) (N * l) (ch χ) a → lam B c (Uo l a) = α * lam B c a) → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → MeasMu ι e ((-1) ^ e * ψ (-1)) (hat θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c ((2 / (N.totient : ℂ)) * val B c l α 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e))) := by
  first | exact @GlobalTheory.EisM.measMu_of_eig | exact GlobalTheory.EisM.measMu_of_eig | (intros; apply GlobalTheory.EisM.measMu_of_eig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_isometric_chart_blockHermitian : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q, Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧ (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧ ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) → ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  first | exact @GlobalTheory.CartanInt.HermChart.exists_chart | exact GlobalTheory.CartanInt.HermChart.exists_chart | (intros; apply GlobalTheory.CartanInt.HermChart.exists_chart <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_volume_transport_of_lattice_isometry : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), (∀ x y, V'.hT (e x) (e y) = V.hT x y) → (∀ x, x ∈ V.L0 ↔ e x ∈ V'.L0) → ∃ φ : GA D V ≃* GA D V', Continuous φ ∧ Continuous φ.symm ∧ (∀ g, g ∈ GQ V ↔ φ g ∈ GQ V') ∧ ∀ (P Q : ℕ) (μ : Measure (GA D V)), IsVolMeas D V P Q μ → IsVolMeas D V' P Q (μ.map φ) := by
  first | exact @GlobalTheory.VolTransport.transport | exact GlobalTheory.VolTransport.transport | (intros; apply GlobalTheory.VolTransport.transport <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.meanSquare_evenTheta_conjugateLattice : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ t : ℂ, nrm1Sq (Λ.map (starRingEnd ℂ).toAddMonoidHom) (GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t)) = nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  first | exact @GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq | exact GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq | (intros; apply GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq <;> assumption)
end
