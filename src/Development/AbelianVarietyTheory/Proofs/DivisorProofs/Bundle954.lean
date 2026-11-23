module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle913
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle929
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCoefFock

variable {K : Type} [Field K] {n : ℕ}

def spl (K : Type) [Field K] (n : ℕ) : BP K n →+* MvPolynomial (Unit × Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  (map (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) :
      MvPolynomial (Unit × Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K).toRingHom).comp
    ((GlobalTheory.BranchFormula.splitLast K Unit (rfl : n + 1 = n + 1)).toRingHom.comp
      ((rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) :
        _ →ₐ[K] _).toRingHom.comp (incl K n).toRingHom))

theorem coefOne_eq (b : Fin n → ℕ) (x : BP K n) :
    coefOne K n b (incl K n x) = AddMonoidAlgebra.coeff (spl K n x) (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) := by
  unfold coefOne
  rw [GlobalTheory.BranchFormula.coefLast_eq_coeff]
  simp [spl, coeff_map]

theorem spl_C (a : K) : spl K n (C a) = C (C a) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_up (a s : Fin n) : spl K n (X (a.castSucc, s)) = C (X (a, s)) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_last (s : Fin n) : spl K n (X (Fin.last n, s)) = X ((), s) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

def lastV (n : ℕ) (p : Unit × Fin n) : Fin (n + 1) × Fin n := (Fin.last n, p.2)

theorem lastV_inj : Function.Injective (lastV n) := fun _ _ h =>
  Prod.ext rfl (Prod.ext_iff.1 h).2

theorem pderiv_rename_of_ne {σ τ : Type} (e : σ → τ) (v : τ) (h : ∀ u, e u ≠ v) (f : MvPolynomial σ K) :
    pderiv v (rename e f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p u hp => simp [hp, pderiv_X_of_ne (h u)]

theorem fockB_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockB (C a) g = a * constantCoeff g :=
  @fockL_C_left K _ starRingOfComm _ a g

theorem emb_inj : Function.Injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) :=
  (Fin.castSucc_injective n).prodMap Function.injective_id

theorem key (x : BP K n) (β : Unit × Fin n →₀ ℕ) (p : MvPolynomial (Fin n × Fin n) K) :
    fockB x (rename (lastV n) (monomial β (1 : K)) * emb K n p) =
      ((∏ u, (β u).factorial : ℕ) : K) * fockB (AddMonoidAlgebra.coeff (spl K n x) β) p := by
  classical
  induction x using MvPolynomial.induction_on generalizing β p with
  | C a =>
    rw [fockB_C_left, spl_C, coeff_C, map_mul, constantCoeff_rename, constantCoeff_monomial, emb, constantCoeff_rename]
    by_cases h : β = 0
    · subst h; simp [fockB_C_left]
    · rw [if_neg h, if_neg (Ne.symm h), ← fockBL_apply]; simp
  | add f g hf hg =>
    simp only [← fockBL_apply, map_add (f := _), LinearMap.add_apply, MvPolynomial.coeff_add] at *
    rw [hf, hg, mul_add]
  | mul_X f v hf =>
    obtain ⟨a, s⟩ := v
    rw [mul_comm f, fockB_X_mul, map_mul (spl K n), Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | cast a =>
      rw [pderiv_rename_of_ne (lastV n) (a.castSucc, s) (fun u h => (Fin.castSucc_lt_last a).ne' (Prod.ext_iff.1 h).1),
        mul_zero, add_zero, spl_up, coeff_C_mul, fockB_X_mul, ← hf]
      congr 2
      exact pderiv_rename emb_inj (a, s) p
    | last =>
      have h1 : pderiv (Fin.last n, s) (emb K n p) = 0 :=
        pderiv_rename_of_ne _ _ (fun u h => (Fin.castSucc_lt_last u.1).ne (congrArg Prod.fst h)) p
      have h2 : pderiv (Fin.last n, s) (rename (lastV n) (monomial β (1 : K))) =
          (β ((), s) : K) • rename (lastV n) (monomial (β - Finsupp.single ((), s) 1) (1 : K)) := by
        have := pderiv_rename (R := K) lastV_inj ((), s) (monomial β (1 : K))
        rw [pderiv_monomial] at this
        rw [← map_smul, smul_monomial, smul_eq_mul, mul_comm]
        exact this
      rw [h1, mul_zero, zero_add, h2, mul_comm, smul_mul_assoc, ← fockBL_apply, map_smul, fockBL_apply, hf,
        spl_last, coeff_X_mul', smul_eq_mul]
      split_ifs with h
      · rw [← mul_assoc, ← Nat.cast_mul]
        congr 2
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ((), s)),
          ← Finset.mul_prod_erase _ (fun u => (β u).factorial) (Finset.mem_univ ((), s)), ← mul_assoc]
        congr 1
        · simpa using Nat.mul_factorial_pred (Finsupp.mem_support_iff.1 h)
        · refine Finset.prod_congr rfl fun u hu => ?_
          simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hu)]
      · rw [Finsupp.notMem_support_iff.1 h, ← fockBL_apply (0 : MvPolynomial (Fin n × Fin n) K)]
        simp

theorem zmon_eq (b : Fin n → ℕ) :
    zmon K n b = rename (lastV n) (monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (1 : K)) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
  simp [zmon, lastV]

theorem spl_zmon (b : Fin n → ℕ) :
    spl K n (zmon K n b) = monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  simp [zmon, spl_last]

theorem spl_emb (q : MvPolynomial (Fin n × Fin n) K) : spl K n (emb K n q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [emb, rename_C, spl_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, hp, bmF_emb_X, spl_up, map_mul]

theorem fockB_zmon_emb : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  intro K _ n b
  have h1 : ∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) =
      (bfact b : K) * fockB (coefOne K n b (incl K n x)) p := by
    intro x p
    rw [zmon_eq, key, coefOne_eq, Fintype.prod_prod_type]
    simp [bfact]
  refine ⟨h1, fun p q => ?_⟩
  rw [h1, coefOne_eq, map_mul, spl_zmon, spl_emb, mul_comm (monomial _ _), coeff_C_mul]
  simp

end GlobalTheory.BrCoefFock
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FunctionFieldCoords

theorem map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem functionFieldMap_finite {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W)
    [IsDominant f] (h : f.residueDegree (genericPoint M) ≠ 0) : (functionFieldMap f).Finite := by
  have hfin : (f.residueFieldMap (genericPoint M)).hom.Finite := by
    letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
    change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
      at h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  have hsurj : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      Function.Surjective (W.presheaf.stalkSpecializes h).hom := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact fun a => ⟨a, rfl⟩
  have hinj : Function.Injective (M.residue (genericPoint M)).hom :=
    RingHom.injective (f := ((M.residue (genericPoint M)).hom : M.functionField →+* _))
  let e := RingEquiv.ofBijective (M.residue (genericPoint M)).hom
    ⟨hinj, M.residue_surjective _⟩
  have key : ∀ (hs : f (genericPoint M) ⤳ genericPoint W),
      ((W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
    intro hs
    have hc : (M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (f.residueFieldMap (genericPoint M)).hom.comp
          ((W.residue _).hom.comp (W.presheaf.stalkSpecializes hs).hom) := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
        Category.assoc, Category.assoc, Scheme.residue_residueFieldMap]
    have h1 : ((M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
      rw [hc]
      exact hfin.comp (RingHom.Finite.of_surjective _
        ((W.residue_surjective _).comp (hsurj hs (map_genericPoint_eq f))))
    have h2 : (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (e.symm : _ →+* _).comp ((M.residue (genericPoint M)).hom.comp
          (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom) := by
      ext a
      exact (e.symm_apply_apply _).symm
    rw [h2]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp h1
  exact key _

end GlobalTheory.FunctionFieldCoords

theorem GlobalTheory.functionField_coords : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f], f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) ∧ ∀ x, (∀ j, co j x = 0) → x = 0 := by
  intro M W _ _ f _ h
  letI := (functionFieldMap f).toAlgebra
  haveI : Module.Finite W.functionField M.functionField :=
    GlobalTheory.FunctionFieldCoords.functionFieldMap_finite f h
  let b := Module.finBasis W.functionField M.functionField
  refine ⟨Module.finrank W.functionField M.functionField, fun j => (b.coord j).toAddMonoidHom,
    fun j c x => ?_, fun x hx => ?_⟩
  · change b.coord j (c • x) = c * b.coord j x
    rw [map_smul, smul_eq_mul]
  · exact b.ext_elem fun i => by simpa using hx i
end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.twisted_estimate_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → 300 ≤ T → IsCut T θ → (∀ y, y ∉ A.zeroSet s → δ * psi A L s y ≤ -T + 1 → y ∈ Ω) → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∃ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F ∧ ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu ≤ 30 * ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ _ ι La _ A E L s hs hsq δ hδ hlev Λ τ z β hdat Ω h T θ hhd hT hθ hΩcov hfin
  obtain ⟨hτ, hpos, hz, hβ, _hdense, C, hC0, hC⟩ := hdat
  obtain ⟨hΩ, hh, hh0⟩ := hhd
  obtain ⟨X, hXz, hXe⟩ := GlobalTheory.T.nonvanishingSet_etale_stein n Y ι La A Λ τ z hτ hpos hz
  have hU : IsOpen (nz A τ) := hz.isOpen
  have hpt := GlobalTheory.OTY.TwEst.nz_facts A L Λ s τ C hC0 hsq hC
  obtain ⟨hsmφ, hsmψ, hlevi⟩ := GlobalTheory.T.frameWeight_singularWeight_smooth_leviNonneg n Y ι La A E L s hs δ hlev (nz A τ) z β hz hβ
    (fun y hy => (hpt y hy).1)
  obtain ⟨hqd, hqm, hq⟩ := GlobalTheory.T.sectionQuotient_holomorphic_measurable n Y ι La A (A.kap + E) (nz A τ) Ω β h hU hΩ hβ hh hh0
  have hψm : Measurable (psi A L s) :=
    (GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn n Y ι La A (A.kap + E) Ω h hΩ hh hh0).2 L s hs
  have htr := GlobalTheory.T.lintegral_weightedAtlas_frame_etale_transfer n Y ι La A E (nz A τ) z β hz hβ
  have hGholo : ∀ e : OpenPartialHomeomorph (nz A τ) (V n), IsChart n X.z e →
      DifferentiableOn ℂ ((fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) := by
    rw [hXz]
    exact (GlobalTheory.T.etale_holomorphic_iff_chart_holomorphic n Y ι La A (nz A τ) z hz Ω (GlobalTheory.OTY.TwEst.quot A h β) hΩ).2 hqd
  have hGm : Measurable (fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) := by
    have h1 := hqm.comp (measurable_subtype_coe : Measurable (Subtype.val : nz A τ → Y))
    convert h1 using 1
    ext y
    exact (GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe (nz A τ)
      (fun x => GlobalTheory.OTY.TwEst.quot A h β x) y).symm
  have hθc : Continuous θ := hθ.1.continuous
  have hθb : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1 := hθ.2.2.2.1
  have hwint := GlobalTheory.T.weighted_l2_estimate_twisted_sections n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ θ hθc hθb
  obtain ⟨F0, hF0, hest⟩ := GlobalTheory.T.twisted_extension_etaleStein_logGrowthWeight n (nz A τ) X
    (fun y => GlobalTheory.OTY.TwEst.wt A E β z y) (fun y => psi A L s y)
    (fun y => GlobalTheory.OTY.TwEst.quot A h β y) (Subtype.val ⁻¹' Ω) δ T θ
    (by rw [hXz]; exact hsmφ) (by rw [hXz]; exact hsmψ) (fun x => (hpt x x.2).2.1) hδ hT hθ
    (by rw [hXz]; exact hlevi) (hΩ.preimage continuous_subtype_val) hGm hGholo
    (fun x hx => hΩcov x (hpt x x.2).1 hx)
    ⟨n, n * Real.log C, fun x => by rw [hXe]; exact (hpt x x.2).2.2⟩
    (by rw [hXz]; exact lt_of_le_of_lt hwint hfin)
  rw [hXz] at hF0 hest
  obtain ⟨hFsec, hFm⟩ := GlobalTheory.T.isSection_holomorphic_mul_frame_extendByZero n Y ι La A (A.kap + E) (nz A τ) z β F0 hz hβ hF0
  refine ⟨fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 (nz A τ) F0 y, hFsec, ?_⟩
  exact (GlobalTheory.T.twistedEstimate_lhs_transfer n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T θ F0 hθc hFm).trans_le
    (hest.trans (mul_le_mul_of_nonneg_left
      (GlobalTheory.T.twistedEstimate_rhs_le_manifold n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T) (by norm_num)))
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem push_mem_liftFil_of_injective : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  intro H R _ I h R₀ _ π hπ hI S _ σ hσ J hJ S₀ _ πS hπS hJk ι₀ hι g A₀ _ A _ i hA AS₀ _ AS _ iS hAS hAab hAg
    hASab hASg φA ψA hφA hψA hiA g' B₀ _ B _ j hB BS₀ _ BS _ jS hBS hBab hBg hBSab hBSg φB ψB hφB hψB hjB
    f₀ _ fS₀ _ hf hyp d hd
  obtain ⟨_, _, HBC, HR, _⟩ := H
  letI : Algebra S R := σ.toAlgebra
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ by
    rw [← hI, RingHom.mem_ker]
    have : πS a = 0 := by rw [← RingHom.mem_ker, hJk]; exact ha
    rw [← RingHom.comp_apply, ← hι, RingHom.comp_apply, this, map_zero]
  have hdp : IsDPMorphism (divided₂ hJ) (divided₂ h) σ := isDPMorphism_sqDP hJ h σ hJI
  have hbase : spMap ι₀ ≫ spMap πS = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hι]
  have mA := GrpMor.of_isGrpPullback hdp hbase hψA
  have mB := GrpMor.of_isGrpPullback hdp hbase hψB
  have nA := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφA
  have nB := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφB
  have hBCA := HBC S AS g hASab hASg R A φA hφA
  obtain ⟨y, hy⟩ := hBCA.1.exists (crysToDR (divided₂ hJ) hAS d)
  obtain ⟨d', rfl⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective HR hAab hAg (isDPNilpotent_squareZero h) hπ hI hA).2 y
  have hsurj := (HR S AS g hASab hASg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) S₀ πS hπS hJk AS₀ iS hAS).2
  have hm : mA.Corr d d' := fun c ↦ by
    obtain ⟨c0, rfl⟩ := hsurj c
    have k : GrpMor (dp0 S) (𝟙 (Sp S)) AS (divided₂ h) (spMap π) A₀ σ
        (spMap ι₀ ≫ spMap πS) (ψA ≫ iS) := GrpMor.of_isGrpPullback (IsDPMorphism.comp _ mA.dp (liftMor (divided₂ hJ) hAS).dp) (by simpa using hbase) (IsGrpPullback.comp hψA hAS)
    rw [GrpMor.pull_pull (liftMor (divided₂ hJ) hAS) mA k (fun _ ↦ rfl) rfl c0,
      ← GrpMor.pull_pull nA (liftMor (divided₂ h) hA) k (fun _ ↦ rfl) hiA c0]
    exact (crysToDR_apply _ hA d' _).symm.trans ((hy c0).trans (congrArg σ (crysToDR_apply _ hAS d c0)))
  have hd' : d' ∈ liftFil (divided₂ h) hA := by
    have hle : PrimitiveSubmodule A ≤ LinearMap.ker (crysToDR (divided₂ h) hA d') := by
      rw [hBCA.2, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hy c]
      rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hd
      rw [hd c hc, map_zero]
    exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hle hc
  have hpush := hyp d' hd'
  have hcorr := GrpMor.Corr.push (m := mA) mB fS₀ f₀ hf.symm hm
  have hx := crysToDR_corr (divided₂ hJ) hBS hB mB nB hjB hcorr
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hpush
  intro c hc
  apply hσ
  show σ _ = σ 0
  rw [map_zero]
  exact (hx c).symm.trans (hpush _ (nB.isMor.pullback1_mem_hodgeFiltration hc))

end GlobalTheory.SqLift
end

section

set_option autoImplicit false

namespace GlobalTheory.PeriodFamily

theorem taylor_sum_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → ∀ {K : Type} (f : K → (I → ℂ) → ℂ), (∀ a, AnalyticAt ℂ (f a) 0) → ∃ n' : Fin r → K → D, (∀ j a, n' j a ∈ J) ∧ (∀ j a b, n' j a * n' j b = 0) ∧ ∀ a, GlobalTheory.PeriodFamily.taylor N (fun i ↦ ∑ j, n j i) (f a) - algebraMap ℂ D (f a 0) = ∑ j, n' j a := by
  intro I _ _ D _ _ J N hJ r
  induction r with
  | zero =>
    intro n _ _ K f _
    refine ⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun a ↦ ?_⟩
    have h := taylor_sub_value_mem_span N (fun i ↦ ∑ j, n j i) (f a)
    have h0 : Ideal.span (Set.range (fun i ↦ ∑ j, n j i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro x ⟨i, rfl⟩
      simp
    rw [h0, Ideal.mem_bot] at h
    rw [h]
    simp
  | succ r ih =>
    intro n hn hsq K f hf
    obtain ⟨n', h1, h2, h3⟩ := ih (fun j ↦ n j.succ) (fun j i ↦ hn _ _) (fun j i i' ↦ hsq _ _ _) f hf
    refine ⟨Fin.cons (fun a ↦ ∑ i, taylor N (fun i ↦ ∑ j : Fin r, n j.succ i)
      (fun z ↦ fderiv ℂ (f a) z (Pi.single i 1)) * n 0 i) n', ?_, ?_, fun a ↦ ?_⟩
    · intro j a
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hn _ _)
      · simpa only [Fin.cons_succ] using h1 j a
    · intro j a b
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun i' _ ↦ ?_
        rw [mul_mul_mul_comm, hsq, mul_zero]
      · simpa only [Fin.cons_succ] using h2 j a b
    · have he : (fun i ↦ ∑ j, n j i) = fun i ↦ (∑ j : Fin r, n j.succ i) + n 0 i := by
        funext i
        rw [Fin.sum_univ_succ, add_comm]
      have hle : Ideal.span (Set.range (fun i ↦ ∑ j : Fin r, n j.succ i) ∪ Set.range (n 0)) ≤ J := by
        rw [Ideal.span_le]
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Ideal.sum_mem _ fun j _ ↦ hn _ _
        · exact hn _ _
      rw [he, taylor_add_of_mul_eq_zero N (fun i ↦ ∑ j : Fin r, n j.succ i) (n 0)
        (fun s hs ↦ hJ s fun a ↦ hle (hs a)) (hsq 0) (f a) (hf a), Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← h3 a]
      ring

end GlobalTheory.PeriodFamily
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.totalDegree_le_of_mem_dualWeylLattice : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  first | exact @GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | exact GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | (intros; apply GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl <;> assumption)
end

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.PrimesOverL

theorem primes_over_l : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ), l.Prime →
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  first
  | exact @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | (apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above ..)

end GlobalTheory.PrimesOverL
end
