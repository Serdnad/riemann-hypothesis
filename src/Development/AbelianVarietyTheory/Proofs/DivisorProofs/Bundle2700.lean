module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle008
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.SurjD

theorem exists_fin_sum_tmul {R D M : Type*} [CommRing R] [CommRing D] [Algebra R D] [AddCommGroup M]
    [Module R M] (z : D ⊗[R] M) : ∃ (n : ℕ) (d : Fin n → D) (m : Fin n → M), z = ∑ i, d i ⊗ₜ m i := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  refine ⟨S.card, fun i ↦ (S.equivFin.symm i).1.1, fun i ↦ (S.equivFin.symm i).1.2, ?_⟩
  rw [hS, ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp S.equivFin.symm (fun p : S ↦ p.1.1 ⊗ₜ p.1.2)).symm

theorem cohom_of_cob {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {u a b c : Fn1 X} (h : Cohom W u a) (k : Fn0 X) (hk : IsCob W c k)
    (ha : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D), a D D' φ x = c D D' φ x + b D D' φ x) : Cohom W u b := by
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨fun D _ _ x ↦ k₀ D x + k D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have h1 := hk₀ D D' φ x hx
  have h2 := hk D D' φ x hx
  have h3 := ha D D' φ x
  simp only [Fn1.add, Fn1.neg, map_add] at h1 ⊢
  linear_combination h1 + h2 + h3

end GlobalTheory.PtExt.SurjD


open GlobalTheory.PtExt.SurjD in
theorem GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  intro H R _ B _ g hB hg D _ _ u hu
  obtain ⟨B', _, π, q, hpb, hB', hg', hq, hfst, hsnd⟩ :=
    GlobalTheory.exists_baseChange_spAlg_prod R D B g hB hg
  have w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← Over.w (fst (SpAlg R D) B), ← Category.assoc, hfst]
    rfl
  have hu' := (GlobalTheory.T.pointCochainPullbackBaseChange_cocycle_coboundary_whole R D (algebraMap R D) _ B' q w u).1 hu
  have hsurj := GlobalTheory.PtExt.toH1O_surjective_of_abelian H D B' g hB' hg'
  obtain ⟨f', hf'⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective D B' hsurj (bcPull w u) hu'
  obtain ⟨hFree, -, hBC⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  have hbc := (hBC R B g hB hg D B' π hpb).1
  have hall : prim (dp0 D) (𝟙 _) B' = ⊤ := (hFree D B' g hB' hg').1
  have hmem : H1.mk _ f' ∈ prim (dp0 D) (𝟙 _) B' := by rw [hall]; exact Submodule.mem_top
  obtain ⟨z, hz⟩ := hbc.2 ⟨H1.mk _ f', hmem⟩
  obtain ⟨n, d, m, rfl⟩ := exists_fin_sum_tmul z
  choose β hβ using fun i ↦ H1.mk_surjective _ (m i).1
  refine ⟨n, d, β, ?_⟩
  let mB := (GlobalTheory.Published.AbelianDeRham.bcMor hpb).isMor
  let S : Z1 (O (dp0 D) (B'.hom ≫ 𝟙 _)) := ∑ i, d i • mB.coef.pullbackOneCocycle (β i)
  have hcl : H1.mk _ f' = H1.mk _ S := by
    have e := congrArg Subtype.val hz

    simp only [map_sum, _root_.GlobalTheory.DeRham.liftSemi_tmul] at e
    rw [← e]

    simp only [S, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, GrpMor.coe_pull]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hβ i]
    rfl
  obtain ⟨g₀, hg₀⟩ := H1.mk_eq_mk.1 hcl
  obtain ⟨hadd, -, hcob⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  obtain ⟨k, hk⟩ := hcob g₀
  have hsplit : f' = ⟨d0 _ g₀, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g₀⟩ + S := Subtype.ext (by simp [hg₀])
  have hC : Cohom (whole B') (bcPull w u) (fv S) := by
    refine cohom_of_cob hf' k hk ?_
    rw [hsplit, hadd]
    intros
    rfl
  have hsum := GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq R D B B' q w π hfst hsnd mB (Fin n) d β
  obtain ⟨k', hk'⟩ : ∃ k, IsCob (whole B') (bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg)) k := by
    obtain ⟨k', hk'⟩ := hC
    refine ⟨k', ?_⟩
    have e : bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg) = (bcPull w u).add (fv S).neg := by
      rw [← hsum]; rfl
    rw [e]; exact hk'
  have hsm : IsCoc (whole _) (sumMul d fun i ↦ fv (β i)) :=
    (GlobalTheory.PtExt.SumMulFacts.main R D B (Fin n) d _).1 fun i ↦ (fv_isCoc_and_ev_eq R B (β i)).1
  have hdiff : IsCoc (whole _) (u.add (sumMul d fun i ↦ fv (β i)).neg) := by
    intro E _ _ E' _ _ E'' _ _ φ ψ x hx
    have h1 := hu E E' E'' φ ψ x hx
    have h2 := hsm E E' E'' φ ψ x hx
    simp only [Fn1.add, Fn1.neg, map_add (f := _), map_neg]
    linear_combination h1 - h2
  exact GlobalTheory.T.isPointwiseCoboundary_of_pullbackBaseChange_isIso R D (algebraMap R D) _ B' q w hq _ hdiff ⟨k', hk'⟩
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCuspTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem cuspW_congr {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : cuspW Xo c U G = cuspW Xo c U G' := by
  ext f
  rw [mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem wtOf_four_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 4).1 (τ, i) = -4 := by
  unfold Datum.mult at hi
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h] at hi
    simp only [wtOf, dif_pos h, dif_pos hi, Pi.zero_apply, zero_sub]
  · rw [if_neg h] at hi
    have h' : conjEmb τ (H.rt : E) = H.rt0 := conj_mem h
    simp only [wtOf, dif_neg h, dif_pos h', dif_pos hi, Pi.zero_apply, neg_zero, zero_sub]

theorem exZ_four_add (n : ℕ) :
    exZ Dw (wtZ (fun _ => 4) n + wtOf Dw 0 4) = exZ Dw (wtZ 0 (n + 8)) := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · show ((n : ℤ) + 2 * 4) = ((n + 8 : ℕ) : ℤ)
    push_cast; ring
  · show ((4 : ℕ) : ℤ) + (wtOf Dw 0 4).1 (τ, i) = ((0 : ℕ) : ℤ)
    rw [wtOf_four_fst τ i i.2]
    simp

theorem exists_twist {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (Z : Comp Xo c) :
    ∃ s : Rul Xo c, (∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + wtOf Dw 0 4)) ∧
      ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 ≠ 0 := by
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨ρ, -⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0)
    hL.geo hL.pos hKmem hKval
  have hadd : wtOf Dw 0 4 + wtOf Dw 0 (-4) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  have hex : exZ Dw (wtOf Dw 0 4) = -((4 : ℤ) • GlobalTheory.ShFam.keyEx Dw) := by
    rw [← GlobalTheory.KeyArchNorm.exZ_wtOf, ← GlobalTheory.FlatTw.exZ_neg_eq, neg_eq_of_add_eq_zero_left hadd]
  set s : Rul Xo c := idem Z * ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 4)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hKmem)
    rwa [zero_add, ← hex] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsK : s * (K : Rul Xo c) = idem Z := by rw [hs, mul_assoc, Units.inv_mul, mul_one]
  have hnorm : ∀ σ, GoodEmb c σ → ∃ C : ℝ, 0 < C ∧ ∀ z ∈ framesOn (U σ) Z,
      homN (U σ) x (wtOf Dw 0 4) s z * C = 1 := by
    intro σ hσ
    obtain ⟨C, hC0, -, hC⟩ := GlobalTheory.KeyArchNorm.homN_key_const κ k₁ k₂ k₅ E H Dw l Xo c _ e σ r (U σ) x K hσ (hL.unf σ hσ)
      (hL.xi σ hσ) ⟨ρ⟩ hL.pos hKmem hKval
    refine ⟨C, hC0, fun z hz => ?_⟩
    obtain ⟨hy, hlies⟩ := hz
    have h1 : homN (U σ) x (wtOf Dw 0 (-4)) (K : Rul Xo c) z = C := hC z.1 z.2 hy
    have ht := tested_of_homN_ne (U σ) x hy (h1.trans_ne hC0.ne')
    rw [← h1, ← homN_mul (U σ) x (even_wtOf _ _) (even_wtOf _ _) _ _ z hy, hadd, hsK]
    exact homN_idem (U σ) x hy hlies ht
  refine ⟨s, GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 4) s ⟨ρ⟩ hL.unf hL.pos (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_four_fst τ j hj, wtOf_four_fst τ i (hij.trans_lt hj)]) hsm hsupp
    (fun σ hσ => ?_), fun σ hσ z hz h0 => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hnorm σ hσ
    exact ⟨C⁻¹, fun z hz => (eq_inv_of_mul_eq_one_left (hC z hz)).le⟩
  · obtain ⟨C, -, hC⟩ := hnorm σ hσ
    have h3 := hC z hz
    have h4 : homN (U σ) x (wtOf Dw 0 4) s z = 0 := by
      simp [homN, ptN, Data.pnorm, h0]
    rw [h4, zero_mul] at h3
    exact zero_ne_one h3

theorem exists_scalar_of_four {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) {n : ℕ} (hn : Even n) {f : Rul Xo c} (hf : f ∈ cusp Xo c U (fun _ => 4) n)
    {z : Σ k, Frame ((U σ).X k).Ψ r} (hz : z ∈ framesOn (U σ) Z) (hne : rdU (U σ) f z.1 z.2 ≠ 0) :
    ∃ f₀ ∈ cusp Xo c U 0 (n + 8), rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  obtain ⟨s, hs, hs0⟩ := exists_twist hL Z
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 4) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  have hev : Even (wtZ (E := E) (fun _ => 4) n).2 := by
    show Even ((n : ℕ) : ℤ)
    exact_mod_cast hn
  have h1 := (hs _ hev g g.2).1
  rw [cuspW_congr hL.unf (exZ_four_add n), cuspW_wtZ] at h1
  refine ⟨_, h1, ?_⟩
  have h2 := hs0 σ hσ z hz
  obtain ⟨hy, hlies⟩ := hz
  have e : rdU (U σ) (g : Rul Xo c) z.1 z.2 = rdU (U σ) f z.1 z.2 := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, e]
  exact mul_ne_zero hne h2

theorem exists_scalar_of_model {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) {n : ℕ} (hn : Even n) (hb : 4 * (finrank ℚ E * r) + 4 ≤ n)
    {k : (U σ).Comp} {y : Frame ((U σ).X k).Ψ r} (hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z)
    {P : Frame ((U σ).X k).Ψ r → ℂ} (hP : P ∈ ((U σ).X k).SS (laU (U σ) 0 (n + 8) k)) (hne : P y ≠ 0) :
    ∃ f₀ ∈ cusp Xo c U 0 (n + 8), rdU (U σ) f₀ k y ≠ 0 := by
  classical
  have hla : laU (U σ) (fun _ => 4) n = laU (U σ) 0 (n + 8) := by
    funext k' τ j
    have e : (n + 8) / 2 = n / 2 + 4 := by omega
    simp only [laU, Pi.zero_apply, e]
    split_ifs <;> push_cast <;> ring
  let P₀ : FDSec (U σ).X := Pi.single k (((U σ).X k).dom.indicator P)
  have hQ : P₀ ∈ holSub0 (U σ).X (laU (U σ) (fun _ => 4) n) := by
    rw [hla]
    refine ⟨holCusp_mem_holSub _ _ fun k' => ?_, fun k' y' hy' => ?_⟩
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact (GlobalTheory.DomCongr.bddSec_cusp_congr E r _ _ P _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
      · simp only [P₀, Pi.single_eq_of_ne h]
        exact (siegelSpaceAlgebra_holds (E := E) r ((U σ).X k') (laU (U σ) 0 (n + 8) k') (laU (U σ) 0 (n + 8) k') 0).1.1
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact Set.indicator_of_notMem hy' _
      · simp only [P₀, Pi.single_eq_of_ne h, Pi.zero_apply]
  have hQy : P₀ k y ≠ 0 := by
    simp only [P₀, Pi.single_eq_same]
    rw [Set.indicator_of_mem hz.1]; exact hne
  have hspan := hL.onto _ hσ (fun _ => 4) n ⟨fun _ => antitone_const, hn⟩ (fun _ _ _ => by norm_num) hb hQ
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 4) n, rdU (U σ) f k y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let ev : FDSec (U σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U (fun _ => 4) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    exact hQy (hle hspan)
  exact exists_scalar_of_four hL hσ Z hn hf hz hfy

theorem exists_scalar_of_models
    (hP : ∀ X : Data E r, 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0)
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  obtain ⟨k, hk⟩ := GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  have hp0 : ((U σ).X k).p0 = Dw.q := (hU.2.1 k).1
  have hla : ∀ n : ℕ, laU (U σ) 0 n k = fun (τ : ((U σ).X k).Ψ) (j : Fin r) =>
      if ((U σ).X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) := fun n => by
    funext τ j
    simp [laU]
  obtain ⟨n, hn, hev, P, hPm, y, hy, hne⟩ := hP ((U σ).X k) (by omega) (by omega)
    (fun n hn γ hγ => by rw [← hla]; exact hL.chi σ hσ 0 n ⟨fun _ => antitone_const, hn⟩ k γ hγ)
    (4 * (finrank ℚ E * r) + 12)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have hm : Even m := by
    obtain ⟨t, ht⟩ := hev
    exact ⟨t - 4, by omega⟩
  have hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
    rw [hk]; exact ⟨rfl, hy⟩
  rw [← hla] at hPm
  obtain ⟨f, hf, hf0⟩ := exists_scalar_of_model hL hσ Z hm (by omega) hz hPm hne
  exact ⟨m + 8, by omega, hev, f, hf, ⟨k, y⟩, hz, hf0⟩

end GlobalTheory.ScalarCuspTwist
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaSpecialise

namespace GlobalTheory.IntExpand

theorem gs_secPull {X Y Z : Scheme.{0}} {L : LB X} (s : L.Sec) (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j : (L.pull φ).ι) (hz : r z ∈ (L.pull φ).U j) :
    gs r z ((L.pull φ).U j) ((GlobalTheory.Cartier.secPull s φ).f j) = gs (r ≫ φ) z (L.U (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  unfold GlobalTheory.Cartier.secPull
  exact (gs_res r z _ hz _).trans (gs_pull r φ z _ (Set.mem_iInter.1 hz PUnit.unit) _)

theorem gs_secMaps {X Z : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : GlobalTheory.Cartier.SecMaps w a b) (r : Z ⟶ X) (z : Z) (p : B.ι) (q : A.ι) (hp : r z ∈ B.U p)
    (hq : r z ∈ A.U q) :
    gs r z (B.U p) (b.f p) = ↑(gm r z ((B.div A).U (p, q)) (w.s (p, q))) * gs r z (A.U q) (a.f q) := by
  have e := congrArg (gs r z (B.U p ⊓ A.U q)) (h.on p q (W := B.U p ⊓ A.U q) inf_le_left inf_le_right)
  have hm : r z ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  rw [gs_mul r z _ hm] at e
  unfold resG at e
  rw [gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  rw [e, gs_unit r z _ (by exact hm)]
  rfl

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  intro V _ _ _ _ hV D A G _ _ hG U w₀ hw s σ hS C _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let σ₁ : H0 U.LG.L 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.secOne U.LG.L σ
  have h1 : ∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i) := fun i h =>
    fn_ext fun x hx => (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ (𝟙 _) x _ hx).trans (by
      rw [Category.comp_id]; exact (gs_res (𝟙 _) x h hx (σ.f i)).symm)
  let sK : U.SecK 1 := genericSec U.toUnifPre 1 σ₁
  have hsK : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) sK (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ₁ (pullback.fst G.hom (jK V)) 1 :=
    (secScal_one_iff U.LG.isLB).2 fun y J hJ => (sval_pullOver _ _ _ _ hJ).symm
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨f, hf, hEf⟩ := GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 σ₁ sK hsK E hE
  obtain ⟨ϑ, hϑ⟩ := GlobalTheory.FamBaseChange.main GlobalTheory.globalFns_holds V _ D 1 E f hEf C
  let th : GlobalTheory.UT.SecA A C 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.pull1 A.L (snd (TFK (R := V) C) A.A).left s
  have hth : MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th := by
    refine fun i h => fn_ext fun x hx => ?_
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s (𝟙 _) x _ hx).trans (gs_appLE _ _ _ h (𝟙 _) x hx (s.f i)).symm
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  obtain ⟨u, hu, hu₁⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw _ n₁ rfl
  have ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := V) C) A.A).left) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))
      ((snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) th σ₁ := by
    intro Z r z p q hp hq
    obtain ⟨p0, rfl⟩ : ∃ p0, p = fun _ => p0 := ⟨p 0, funext fun k => congrArg p (Subsingleton.elim k 0)⟩
    obtain ⟨q0, rfl⟩ : ∃ q0, q = fun _ => q0 := ⟨q 0, funext fun k => congrArg q (Subsingleton.elim k 0)⟩
    have hp0 := hp 0
    have hq0 := hq 0
    have e1 := hu₁ Z (r ≫ (snd (TFK (R := V) C) A.A).left) z p0 q0 hp0 hq0
    have c2 : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left =
        r ≫ (snd (TFK (R := V) C) A.A).left := by
      rw [Category.assoc, n₁, Category.comp_id]
    have mB : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (U.LG.L.pull (pullback.fst G.hom (jK V))).U (fun _ => p0) := Set.mem_iInter.2 fun _ => hp0
    have mA : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (A.L.pull U.gen.hom.left).U (fun _ => q0) := Set.mem_iInter.2 fun _ => by
      show (((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left) z ∈ A.L.U q0
      rw [c2]; exact hq0
    have e2 := GlobalTheory.IntExpand.gs_secMaps hS _ z (fun _ => p0) (fun _ => q0) mB mA
    rw [GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mB, GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mA, c2] at e2
    refine (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ
      (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) z (fun _ => p0)
      (Set.mem_iInter.2 fun _ => by exact hp0)).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s r z (fun _ => q0) (Set.mem_iInter.2 fun _ => hq0)).symm)
    rw [Fin.prod_univ_one]
    dsimp only
    rw [Nat.cast_one, zpow_one, e1]
    have c1 : (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left =
        ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK V) := by
      simp only [Category.assoc, Category.comp_id]
    rw [c1]
    exact e2
  refine ⟨σ₁, f, th, ϑ, h1, hf, hth, expandsF_of_integral U.toUnifPre C hu₁ σ₁ f hf ϑ ?_ th ht, hϑ⟩
  intro α y J hJ
  exact (((secScal_one_iff D.toPre.P.isLB).1 (hϑ α)) y J hJ).symm

end GlobalTheory.IntExpand
end

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.GeoSwap

open HermLB

section Shift

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}



theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

end Shift

end GlobalTheory.CovTest.GeoSwap

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_basic_properties : (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (a : R) (j : Fin N), symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j) ∧ (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (σ : Equiv.Perm (Fin N)), symTup (fun b => c (σ b)) = symTup c) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (i : R →+* R') (N : ℕ) (c : Fin N → R) (j : Fin N), i (symTup c j) = symTup (fun b => i (c b)) j) ∧ ∀ (K : Type) [Field K] (N : ℕ) (c : Fin N → K), (∃ a, c a ≠ 0) → ∃ j, symTup c j ≠ 0 := by
  first | exact @GlobalTheory.UMin.symTup_basic | exact GlobalTheory.UMin.symTup_basic | (intros; apply GlobalTheory.UMin.symTup_basic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) (e : Fin N → K), ∃ T : Finset (Fin N → K), ∀ (c : Fin N → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) → ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T := by
  first | exact @GlobalTheory.UMin.symTup_scale_finite | exact GlobalTheory.UMin.symTup_scale_finite | (intros; apply GlobalTheory.UMin.symTup_scale_finite <;> assumption)
end
