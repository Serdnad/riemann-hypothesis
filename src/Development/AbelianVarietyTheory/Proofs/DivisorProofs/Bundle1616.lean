module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix


open GlobalTheory.Mean4O.CombForm in
theorem exists_subAtlas : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp π _ hπ e A hA hs
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, h⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, h, hπ]⟩
  haveI : CompactSpace (CxPts q σ) := CxPts.compactSpace σ hq
  haveI : T2Space (CxPts q σ) := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI : SecondCountableTopology (CxPts q σ) := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hp
  have hc : Continuous (ptMap π hπ σ) := PtsOver.continuous_map π hπ _
  have hinj : Function.Injective (ptMap π hπ σ) := fun a b h =>
    Subtype.ext ((cancel_mono π).1 (congrArg Subtype.val h))
  have hE : IsClosedEmbedding (ptMap π hπ σ) := hc.isClosedEmbedding hinj
  let h : CxPts q σ ≃ₜ Set.range (ptMap π hπ σ) := hE.isEmbedding.toHomeomorph
  haveI : CompactSpace (Set.range (ptMap π hπ σ)) := h.compactSpace
  let A' : FinHolAtlas e (CxPts q σ) := (AnRead.all q σ e).finAtlas
  have hA' : IsAlgAtlas A' := AnRead.isAlgAtlas_finAtlas _
  have hm : HoloMap A' A (ptMap π hπ σ) := hA.holoMap hA' (f := π) fun _ => rfl
  have hB : HoloMap (tAtlas A' h) A Subtype.val := ⟨continuous_subtype_val, fun j l => hm.2 j l⟩
  refine ⟨tAtlas A' h, hB, fun L v hv => ?_⟩
  have hsm (i : Fin e) : (L i).φ.IsSmooth hA.anRead := (Weight.isCInf_iff_isSmooth _).1 (L i).cInf
  have hv' : Continuous fun y => v (ptMap π hπ σ y) := hv.comp hc
  have hP (i : Fin e) : IsPotential A' ((L i).pull π hπ).φ.locPot :=
    Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth _).1 ((L i).pull π hπ).cInf)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact k Y q σ e A' hA' (fun i => (L i).pull π hπ) _ hv'.measurable
  rw [h₂ (h₁.2 (mIntegrableCont _ _ hP _ hv')),
    GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport e _ _ A' h _ _
      (fun i => isPotentialPullback A _ _ hB _ ((hsm i).isPotential hA))
      (hv.comp continuous_subtype_val)]
  exact (SameForm.mInt_eq (fun i => (hsm i).sameForm_pull hA hA' π hπ) _).symm

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle : ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (A : MLine p σ), ∃ Q : MLine p σ, Q.φ.SemiPosReg D ∧ (A.tens Q).φ.SemiPosReg D := by
  first | exact @GlobalTheory.Mix.exists_semiPosReg_tens | exact GlobalTheory.Mix.exists_semiPosReg_tens | (intros; apply GlobalTheory.Mix.exists_semiPosReg_tens <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.VKill

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_exp {P : Mt n} (hP : IsUnit P) (X : Mt n) (t : ℝ) :
    P * NormedSpace.exp (t • X) * P⁻¹ = NormedSpace.exp (t • (P * X * P⁻¹)) := by
  rw [← Matrix.exp_conj P _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem dRep_conj {P : Mt n} (hP : IsUnit P) (σ : Mt n → (H →L[ℂ] H)) (X : Mt n) (v : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X v = dRep σ (P * X * P⁻¹) v := by
  unfold dRep
  simp only [conj_exp hP]

theorem conjH_conj {P : Mt n} (hP : IsUnit P) (J Z : Mt n) :
    conjH (Pᴴ * J * P) (P⁻¹ * Z * P) = P⁻¹ * conjH J Z * P := by
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h1 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h2 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold conjH
  simp only [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, Matrix.mul_neg,
    Matrix.neg_mul]

theorem dRepC_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) :
    dRepC (Pᴴ * J * P) (fun g => σ (P * g * P⁻¹)) (P⁻¹ * Z * P) v = dRepC J σ Z v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ (c : ℂ) (Y : Mt n), P * (c • (P⁻¹ * Y * P)) * P⁻¹ = c • Y := fun c Y => by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  unfold dRepC
  rw [dRep_conj hP, dRep_conj hP, conjH_conj hP, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.sub_mul, ← Matrix.mul_sub,
    h2, h2]

theorem conj_prod {P : Mt n} (hP : IsUnit P) (l : List (Mt n)) :
    P * l.prod * P⁻¹ = (l.map fun g => P * g * P⁻¹).prod := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  induction l with
  | nil => simp [Matrix.mul_nonsing_inv _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem smooth_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (v : H)
    (h : SmoothVec (lieH (Pᴴ * J * P)) (fun g => σ (P * g * P⁻¹)) v) : SmoothVec (lieH J) σ v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ Y : Mt n, P * (P⁻¹ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h3 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h4 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  intro k Xs hX
  have := h k (fun i => P⁻¹ * Xs i * P) (fun i => by
    have e : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    show (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) = 0
    have e2 : (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) =
        Pᴴ * ((Xs i)ᴴ * J + J * Xs i) * P := by
      simp only [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, h4, Matrix.mul_add, Matrix.add_mul]
    rw [e2, e, Matrix.mul_zero, Matrix.zero_mul])
  simp only [conj_prod hP, List.map_ofFn, Function.comp_def, conj_exp hP] at this
  simp only [Matrix.mul_assoc, h2, h1, Matrix.mul_one] at this
  exact this

theorem jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).IsHermitian := by
  unfold Formalism.REAL.Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext a
  by_cases h : ε a <;> simp [h]

theorem jm_det (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  by_cases h : ε a <;> simp [h]

theorem borel_extVec (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec) (_hθ : IsInfFam θ) (hM : HolShape M) (hw : WtIs M w) (hv : IsExtVec M v)
    (τ : D.what₂.Tau) :
    SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c →
      dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
        if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  obtain ⟨hc, hU, -, hx⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  obtain ⟨-, hx⟩ := hx hM
  obtain ⟨hHC, p, hp, hε⟩ := hM τ
  obtain ⟨-, hlow, hwt⟩ := hv τ
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hG := M.fr_gram τ
  have hH : (gramAt D V τ).IsHermitian := by
    rw [← hG]; exact Matrix.isHermitian_conjTranspose_mul_mul _ (jm_herm _)
  have hD : (gramAt D V τ).det ≠ 0 := by
    rw [← hG, det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero hPd.star.ne_zero (jm_det _)) hPd.ne_zero
  have hs : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) :=
    (GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ hH hD hU).1 _ (v τ).2
  refine ⟨hs, fun a c hac => ?_⟩
  have hs' : SmoothVec (lieH (Formalism.REAL.Jm (M.ε τ))) (M.σ τ) (v τ : M.H τ) := by
    refine smooth_conj hP _ _ _ ?_
    rw [hG]; exact hs
  have hl : (v τ : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hlow
  have hB := GlobalTheory.T.extremal_lowest_Ktype_killed_by_compact_roots _ _ _ _ _ (M.ds τ) _ hl hs' hwt
  have hm := GlobalTheory.T.lowest_Ktype_holomorphic_killed_by_lowering_roots _ p _ _ _ _ hHC hε (M.ds τ) _ hl hs'
  have e : dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
      dRepC (Formalism.REAL.Jm (M.ε τ)) (M.σ τ)
        (Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1) (v τ : M.H τ) := by
    rw [hx a c, ← hG]
    exact dRepC_conj hP _ _ _ _
  rw [e]
  split_ifs with h
  · subst h
    rw [hB.1]
    have := hw τ a
    unfold extWt at this
    rw [← this]
    simp
  · have hlt : (a : ℕ) < c := lt_of_le_of_ne hac fun h' => h (Fin.ext h')
    have hq := nNeg_shape hp hε
    have hcn := c.2
    have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
      intro b
      have := b.2
      rw [hε, hq]
      unfold arr
      split_ifs with hb
      · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
      · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
    by_cases ha : (a : ℕ) < V.rank - p
    · by_cases hc' : (c : ℕ) < V.rank - p
      · refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
        rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_pos ha, if_pos hc']
        omega
      · exact hm _ _ (by rw [hsg]; simp [hc']) (by rw [hsg]; simp [ha])
    · have hc' : ¬ (c : ℕ) < V.rank - p := by omega
      refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
      rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_neg ha, if_neg hc']
      omega

end GlobalTheory.HolDict.VKill
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.BallFinite

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_rep (P : Pair p) (a c : ℤ) : ∃ M : HermLB p, P.Rep a c M := by
  obtain ⟨hL, hA, -⟩ := GlobalTheory.T.represents_base_bundles_and_trivial k X p P
  have h1 : ∃ M : HermLB p, P.Rep a 0 M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hL
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := GlobalTheory.T.represents_hermitianLineBundle_dual k X p P _ _ _ (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hL)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  have h2 : ∃ M : HermLB p, P.Rep 0 c M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A n hA
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := GlobalTheory.T.represents_hermitianLineBundle_dual k X p P _ _ _ (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A n hA)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  obtain ⟨M₁, h₁⟩ := h1
  obtain ⟨M₂, h₂⟩ := h2
  have := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ _ _ M₁ M₂ h₁ h₂
  rw [add_zero, zero_add] at this
  exact ⟨_, this⟩

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem smallSec_tens_shift (N M : HermLB p) (t : ℝ) :
    ((N.tens M).shift (fun _ => t) fun _ => rfl).smallSec ⊆ (N.tens (M.shift (fun _ => t) fun _ => rfl)).smallSec :=
  fun u hu σ y => by
    refine le_of_eq_of_le ?_ (hu σ y)
    simp only [Weight.nsq, HermLB.tens, HermLB.shift, Weight.tens, Weight.addFn]
    congr 2
    ring

theorem bl_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t →
    ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  intro hHS k _ X _ p D hX P b s t hG a c R hC
  obtain ⟨M, hM⟩ := exists_rep P a c
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit (fun _ => P.A)).1
  have hSI := ((hC.arIso k X p D hX).2 Unit (fun _ => P.A) Φ hΦ).1 ()
  obtain ⟨m, hm⟩ := ((hHS k X p D hX P.A (M.shift (fun _ => R) fun _ => rfl) _ hG.nef hSI).1).exists
  have hA := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have hAm := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A m hA
  have hT := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ _ _ _ _ hAm hM
  have hsm : (((P.A.pow m).tens M).shift (fun _ => R) fun _ => rfl).smallSec.Finite :=
    hm.subset (smallSec_tens_shift _ _ _)
  have hB : (P.Bl (m * 0 + a) (m * 1 + c) (Real.exp R)).Finite := by
    have e := (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P _ _ _ hT R 0).2.2
    rw [← Set.encard_lt_top_iff, ← e]
    exact hsm.encard_lt_top
  have hs := hG.s_mem
  obtain ⟨hsH, hsn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs.1 m
  refine (hB.preimage (f := fun f => s ^ m * f) (mul_right_injective₀ (pow_ne_zero m hG.s_ne)).injOn).subset ?_
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P _ _ _ _ (s ^ m) f hsH hf.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2, hsn]
  have n1 : P.nu 0 1 σ y s ≤ 1 := hs.2 σ y
  calc _ ≤ 1 * P.nu a c σ y f :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (nu_nonneg P 0 1 σ y s) n1) (nu_nonneg P a c σ y f)
    _ ≤ Real.exp R := by rw [one_mul]; exact (hf.2 σ y).trans (by linarith [Real.add_one_le_exp R])

end GlobalTheory.VolBr.BallFinite
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a b M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a) (m * b) (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + ((D + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  first | exact @GlobalTheory.VolBr.lc_tendsto_of_rep | exact GlobalTheory.VolBr.lc_tendsto_of_rep | (intros; apply GlobalTheory.VolBr.lc_tendsto_of_rep <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extremalWeight_eq_character_exponent_add : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC (Wc D i), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) u = ∏ ρ, (archM (Wc D i) (R.θ ρ) u).det ^ e ρ) ∧ ∀ k ρ (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin (Wc D i).rank, w ρ a = (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) k τ (Fin.cast (rank_Wc i) a) + e ρ := by
  first | exact @GlobalTheory.HolDict.extWt_eq_laU_add | exact GlobalTheory.HolDict.extWt_eq_laU_add | (intros; apply GlobalTheory.HolDict.extWt_eq_laU_add <;> assumption)
end

section

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount.OrbKProd

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd

theorem finsum_prod_mul {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact finsum_prod_mul_of_finite u v hu hv
    · rw [finsum_of_infinite_support hv, mul_zero]
      by_cases h0 : ∀ a, u a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        apply finsum_of_infinite_support
        intro hfin
        apply hv
        refine (hfin.image Prod.snd).subset ?_
        intro b hb
        exact ⟨(a, b), by simp only [Function.mem_support] at hb ⊢; exact mul_ne_zero ha hb, rfl⟩
  · rw [finsum_of_infinite_support hu, zero_mul]
    by_cases h0 : ∀ b, v b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      apply finsum_of_infinite_support
      intro hfin
      apply hu
      refine (hfin.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, b), by simp only [Function.mem_support] at ha ⊢; exact mul_ne_zero ha hb, rfl⟩

section Vol

variable {G : Type} [Group G]

theorem vol_eq_idxRatio (C H : Subgroup G) : vol C H = GlobalTheory.FunObj.idxRatio H C := rfl

theorem vol_prod {G' : Type} [Group G'] (C H : Subgroup G) (C' H' : Subgroup G') :
    vol (C.prod C') (H.prod H') = vol C H * vol C' H' := by
  unfold vol
  rw [relIndex_prod_prod, relIndex_prod_prod]
  push_cast
  exact mul_div_mul_comm _ _ _ _

theorem map_conj_mul (K : Subgroup G) (t x : G) :
    K.map (MulAut.conj (t * x)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  have h := map_conj_mul_three_subgroup_of_mem K K.one_mem t x
  rwa [mul_one] at h

theorem inf_map_conj (T A : Subgroup G) {t : G} (ht : t ∈ T) :
    T ⊓ A.map (MulAut.conj t).toMonoidHom = (T ⊓ A).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, map_conj_self _ ht]

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Vol

section Term

variable {G : Type} [Group G]

def oTerm (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) (x : G) : ℂ :=
  ((vol C (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℚ) : ℂ)⁻¹ * f (x⁻¹ * δ * θ x)

theorem orbC_eq (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) :
    orbC θ K C δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), oTerm θ K C δ f (Quotient.out q) :=
  rfl

theorem f_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    f ((t * x * k)⁻¹ * δ * θ (t * x * k)) = f (x⁻¹ * δ * θ x) := by
  have ht0 : t * δ = δ * θ t := ht
  have ht' : θ t = δ⁻¹ * (t * δ) := eq_inv_mul_of_mul_eq ht0.symm
  rw [← hf k hk (x⁻¹ * δ * θ x)]
  congr 1
  simp only [map_mul, _root_.mul_inv_rev, ht']
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Term

end GlobalTheory.LKCount.OrbKProd
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ s ∈ (A.tens B.dual).smallSec, s ≠ 0 := by
  first | exact @GlobalTheory.HSNef.le_iff_exists_smallSec | exact GlobalTheory.HSNef.le_iff_exists_smallSec | (intros; apply GlobalTheory.HSNef.le_iff_exists_smallSec <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → (∀ j, 0 ≤ w j) → M.IsNef D := by
  first | exact @GlobalTheory.HSNef.FSNef.isNef_of_isFS | exact GlobalTheory.HSNef.FSNef.isNef_of_isFS | (intros; apply GlobalTheory.HSNef.FSNef.isNef_of_isFS <;> assumption)
end
