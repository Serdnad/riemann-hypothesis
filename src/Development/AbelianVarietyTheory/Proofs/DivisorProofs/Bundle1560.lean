module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle066
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

noncomputable def upperConeRescale {E : Type} [Field E] (a : ℕ) (N : Matrix (Fin a) (Fin a) ℝ)
    (M : Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) :=
  Matrix.of fun p q => (fun _ => ((N p q : ℝ) : ℂ)) * M p q

lemma continuous_upperConeRescale {E : Type} [Field E] (a : ℕ) :
    Continuous (fun x : Matrix (Fin a) (Fin a) ℝ × Matrix (Fin a) (Fin a) (Cinf E) => upperConeRescale a x.1 x.2) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [upperConeRescale, Matrix.of_apply]
  refine Continuous.mul ?_ ?_
  · refine continuous_pi fun _ => ?_
    exact Complex.continuous_ofReal.comp ((continuous_apply q).comp ((continuous_apply p).comp continuous_fst))
  · exact (continuous_apply q).comp ((continuous_apply p).comp continuous_snd)

lemma upperCone_conj_diag_eq {E : Type} [Field E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (d : GL (Fin a) (Cinf E)) (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)))
    (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M.BlockTriangular id) :
    (d⁻¹).val * M * d.val = upperConeRescale a (fun p q => if p ≤ q then r q / r p else 0) M := by
  have hD : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) := by
    have h1 : d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i x
      have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
      simp [this]
    calc (d⁻¹).val = (d⁻¹).val * (d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ))) := by
          rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [hD, hd]
  ext p q x
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [upperConeRescale, Matrix.of_apply, Pi.mul_apply]
  by_cases hpq : p ≤ q
  · rw [if_pos hpq]
    have : (r p : ℂ) ≠ 0 := by exact_mod_cast (hr p).ne'
    push_cast
    field_simp
  · rw [if_neg hpq]
    have h0 : M p q = 0 := hM (lt_of_not_ge hpq)
    simp [h0]

end GlobalTheory

theorem GlobalTheory.upperCone_conj_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  intro E _ _ _ a ω hω htri t ht
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  set K : Set (Matrix (Fin a) (Fin a) ℝ) := Set.univ.pi (fun _ => Set.univ.pi (fun _ => Set.Icc (0:ℝ) C)) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  set A : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 x.2.val) '' (K ×ˢ ω)
  set B : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 (x.2⁻¹).val) '' (K ×ˢ ω)
  have hAc : IsCompact A := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)))
  have hBc : IsCompact B := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_coe_inv.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (A ×ˢ (MulOpposite.op '' B)), ?_, ?_⟩
  · exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hAc.prod (hBc.image MulOpposite.continuous_op))
  intro r d hr hcone hd b hb
  have hN : (fun p q : Fin a => if p ≤ q then r q / r p else 0) ∈ K := by
    simp only [hK, Set.mem_pi]
    intro p _ q _
    rw [Set.mem_Icc]
    by_cases hpq : p ≤ q
    · simp only [if_pos hpq]
      exact ⟨div_nonneg (hr q).le (hr p).le, hC r hr hcone p q hpq⟩
    · simp only [if_neg hpq]
      exact ⟨le_rfl, hC0⟩
  have hbinv : (b⁻¹).val.BlockTriangular id := by
    have := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (htri b hb)
  refine ⟨?_, ?_⟩
  · refine ⟨(_, b), ⟨hN, hb⟩, ?_⟩
    simp only [Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd b.val (htri b hb)).symm
  · refine ⟨(d⁻¹ * b * d)⁻¹.val, ⟨(_, b), ⟨hN, hb⟩, ?_⟩, rfl⟩
    have : (d⁻¹ * b * d)⁻¹ = d⁻¹ * b⁻¹ * d := by group
    simp only [this, Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd (b⁻¹).val hbinv).symm
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.ConstTermGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_alt : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_alt)

theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_left_le {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (c * y) ≤ B * height y := by
  have c1 : Continuous fun u : GL (Fin a) (Cinf E) => toL u.val :=
    (Units.continuous_val : Continuous fun u : GL (Fin a) (Cinf E) => u.val)
  have c2 : Continuous fun u : GL (Fin a) (Cinf E) => toL (u⁻¹).val :=
    (Units.continuous_coe_inv : Continuous fun u : GL (Fin a) (Cinf E) => (u⁻¹).val)
  obtain ⟨M1, h1⟩ := hΩ.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨M2, h2⟩ := hΩ.exists_bound_of_continuousOn c2.continuousOn
  have M0 : (0 : ℝ) ≤ max 0 (max M1 M2) := le_max_left _ _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  refine ⟨1 + a * max 0 (max M1 M2), by positivity, fun c hc y => ?_⟩
  have m1 : ‖toL c.val‖ ≤ max 0 (max M1 M2) := (h1 c hc).trans ((le_max_left _ _).trans (le_max_right _ _))
  have m2 : ‖toL (c⁻¹).val‖ ≤ max 0 (max M1 M2) := (h2 c hc).trans ((le_max_right _ _).trans (le_max_right _ _))
  have e2 : ((c * y)⁻¹ : GL (Fin a) (Cinf E)).val = (y⁻¹).val * (c⁻¹).val := by
    rw [_root_.mul_inv_rev]; rfl
  have p1 := norm_toL_mul_le c.val y.val
  have p2 := norm_toL_mul_le (y⁻¹).val (c⁻¹).val
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have q1 : (a : ℝ) * (‖toL c.val‖ * ‖toL y.val‖) ≤ a * max 0 (max M1 M2) * ‖toL y.val‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right m1 n1) ha
  have q2 : (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * max 0 (max M1 M2) * ‖toL (y⁻¹).val‖ := by
    calc (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * (‖toL (y⁻¹).val‖ * max 0 (max M1 M2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 n2) ha
      _ = _ := by ring
  have aM : (0 : ℝ) ≤ a * max 0 (max M1 M2) := by positivity
  unfold height
  rw [show toL (c * y).val = toL (c.val * y.val) from rfl, e2]
  nlinarith

theorem uniform_growth (φ : Sm E a) (hopen : IsOpen {k | finRep E a k φ = φ})
    (hgr : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N)
    {Ω : Set (GA E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), ∀ h ∈ Ω, ∀ y, ‖φ.1 (h * infGL E a y)‖ ≤ C * height y ^ N := by
  have hS : ∀ s : GL (Fin a) (Af E), finRep E a s φ = φ → ∀ x, φ.1 (x * finGL E a s) = φ.1 x := fun s hs x => by
    have := congrFun (congrArg Subtype.val hs) x
    exact this
  have hU : ∀ t : GL (Fin a) (Af E), IsOpen ((fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) := fun t =>
    hopen.preimage (continuous_const.mul continuous_id)
  have hKf : IsCompact (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E) '' Ω) := hΩ.image continuous_mapFin
  obtain ⟨T, hT⟩ := hKf.elim_finite_subcover (fun t => (fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) hU
    (fun k _ => Set.mem_iUnion.2 ⟨k, by
      change finRep E a (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]; rfl⟩)
  choose C N hCN using hgr
  obtain ⟨B, hB0, hB⟩ := height_mul_left_le (hΩ.image (continuous_mapInf (E := E) (a := a)))
  refine ⟨∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t), ∑ t ∈ T, N (finGL E a t), fun h hh y => ?_⟩
  obtain ⟨t, htT, hkt⟩ := Set.mem_iUnion₂.1 (hT ⟨h, hh, rfl⟩)
  have e : h * infGL E a y = finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y) *
      finGL E a (t⁻¹ * Matrix.GeneralLinearGroup.map (pFin E) h) := by
    apply ga_ext
    · simp only [map_mul, pInf_infGL, pInf_finGL, one_mul, mul_one]
    · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul, mul_one, mul_inv_cancel_left]
  rw [e, hS _ hkt]
  have hcy := hB _ ⟨h, hh, rfl⟩ y
  have h0 := one_le_height (Matrix.GeneralLinearGroup.map (pInf E) h * y)
  have hy := one_le_height y
  calc ‖φ.1 (finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y))‖
      ≤ C (finGL E a t) * height (Matrix.GeneralLinearGroup.map (pInf E) h * y) ^ N (finGL E a t) := hCN _ _
    _ ≤ |C (finGL E a t)| * (B * height y) ^ N (finGL E a t) :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by linarith) hcy _) (pow_nonneg (by linarith) _) (abs_nonneg _)
    _ = |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ N (finGL E a t) := by ring
    _ ≤ |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy
          (Finset.single_le_sum (f := fun t => N (finGL E a t)) (fun _ _ => Nat.zero_le _) htT))
          (mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _))
    _ ≤ (∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t)) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun t => |C (finGL E a t)| * B ^ N (finGL E a t))
          (fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _)) htT) (pow_nonneg (by linarith) _)

theorem norm_constTerm_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N) →
    ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hleft hopen hgr g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hc : Continuous fun x : BlockIx a r → Ad E => unip x * g :=
    GlobalTheory.CuspRep.CuspidalL2GL.continuous_unip.mul continuous_const
  obtain ⟨C, N, hC⟩ := uniform_growth φ hopen hgr (hK.image hc)
  refine ⟨C, N, fun y => ?_⟩
  have hb : ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
    intro x
    obtain ⟨γ, ⟨z, rfl⟩, hγ⟩ := hcov x
    have hu : unip ((AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) z) =
        ratGL E a (unip z) := unip_algebraMap z
    have e : φ.1 (unip (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r) z + x) * g *
        infGL E a y) = φ.1 (unip x * (g * infGL E a y)) := by
      rw [unip_add, hu]
      simp only [mul_assoc]
      exact hleft _ _
    rw [← e]
    exact hC _ ⟨_, hγ, rfl⟩ y
  have hfin : μ 𝓕 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
  calc _ ≤ C * height y ^ N * (μ 𝓕).toReal := norm_setIntegral_le_of_norm_le_const hfin (fun x _ => hb x)
    _ = C * height y ^ N := by rw [h1]; simp

end GlobalTheory.ConstTermGrowth

end
end

section

noncomputable section

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem IsCuspForm.mem_cuspForms {φ : Sm E a} (h : IsCuspForm φ) : φ.1 ∈ cuspForms E a :=
  (UpperTheory.V.Cm.isCuspForm_iff φ).1 h

theorem IsCuspForm.constantTerm_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a) (h : IsCuspForm φ) : AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 :=
  h.mem_cuspForms.2

end GlobalTheory.CuspRep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  first | exact @GlobalTheory.IdGenRat.exists_sections_vanish_generate | exact GlobalTheory.IdGenRat.exists_sections_vanish_generate | (intros; apply GlobalTheory.IdGenRat.exists_sections_vanish_generate <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowForm

section Abstract

variable {K X Y : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem exists_descent {H W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] {σ₁ σ₂ : K →+* ℂ} (e : σ₁ = σ₂)
    (φ : Y →ₛₗ[σ₁] W) (ψ : X →ₛₗ[σ₂] H) (T : H →ₗ[ℂ] W) (c : ℂ) (h : ∀ x, ∃! y, φ y = c • T (ψ x)) :
    ∃ θ : X →ₗ[K] Y, ∀ x, φ (θ x) = c • T (ψ x) := by
  subst e
  choose f hf hu using h
  refine ⟨⟨⟨f, fun x x' => (hu _ _ ?_).symm⟩, fun a x => (hu _ _ ?_).symm⟩, hf⟩
  · simp only [map_add (f := _), hf, smul_add]
  · simp only [map_smulₛₗ, hf, RingHom.id_apply, smul_comm c]

theorem mem_orth_ker [FiniteDimensional K X] {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {σ : K →+* ℂ} (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W)
    (U : W ≃ₗᵢ[ℂ] W) (g : W →ₗ[ℂ] W) (κ : ℂ) (h1 : Submodule.span ℂ (Set.range j) = ⊤)
    (h2 : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (h3 : ∀ x, U (jW (θ x)) = κ • g (th (j x))) {x : X} (h4 : ∀ u, θ u = 0 → ⟪j x, j u⟫_ℂ = 0) :
    j x ∈ (LinearMap.ker th)ᗮ := by
  have key := GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW
    ((U.symm.toLinearEquiv : W →ₗ[ℂ] W) ∘ₗ (κ • (g ∘ₗ th))) h1 h2 fun x => by
      show U.symm (κ • g (th (j x))) = _
      rw [← h3, U.symm_apply_apply]
  have h5 : LinearMap.ker th ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := fun w hw => key (by
    show U.symm (κ • g (th w)) = 0
    rw [LinearMap.mem_ker.1 hw, map_zero, smul_zero, map_zero])
  refine Submodule.orthogonal_le h5 ((Submodule.mem_orthogonal' _ _).2 fun w hw => ?_)
  have h6 : Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) ≤ LinearMap.ker (innerₛₗ ℂ (j x)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact h4 u hu
  exact h6 hw

theorem re_inner_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem csumAt_conj [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    csumAt S ((starRingEnd ℂ).comp σ) f g = starRingEnd ℂ (csumAt S σ f g) := by
  unfold csumAt

  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, map_sum, map_mul, RingHom.comp_apply]
  rfl

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem toF_mem (i : Fin D.R.m) (t : T0) (y : Fin ((A.fam.L i t).dZ (liftLvl F) (liftSub R F i t)) → D.what₂.LL) :
    (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y ∈ liftSub R F i t := by
  obtain ⟨f, hf, e⟩ : ((A.fam.L i t).zE (liftLvl F) (liftSub R F i t)).mulVec y ∈
    (A.fam.L i t).Z0 (liftLvl F) (liftSub R F i t) := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y = f :=
    (congrArg (A.fam.L i t).S.basis.equivFun.symm e.symm).trans ((A.fam.L i t).S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem norm_wC (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (z : Fin (finrank D.what₂.LL (R.WL F false i)) → D.what₂.LL) :
    ‖(R.toCx F).wC false i v (cpt v.embedding z)‖ ^ 2 =
      (RealDat.nP F false)⁻¹ * ‖(R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z)‖ ^ 2 := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx F).wC false i v (cpt v.embedding z)) :
      R.WS F false i (sgAt D.what₂.embLL v)) : (R.HW i (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z) := by
    have e0 : (R.toCx F).wC false i v (cpt v.embedding z) = ∑ k, v.embedding (z k) • (R.toCx F).bW false i v k := rfl
    refine (congrArg (fun a => ((Tw.out (s := twAt D.what₂.embLL v) a : R.WS F false i (sgAt D.what₂.embLL v)) :
      (R.HW i (sgAt D.what₂.embLL v)).H)) e0).trans ?_
    refine (congrArg Subtype.val (out_sum _)).trans ((Submodule.coe_sum _ _ _).trans ?_)
    unfold coordMap

    rw [Fintype.linearCombination_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show cj (twAt D.what₂.embLL v) (v.embedding (z k)) •
      ((((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (R.bL F false i k)) = _
    rw [map_smulₛₗ, emb_eq D.what₂.embLL v, cj_cj, smul_comm]
  have e2 := congrArg norm e
  refine (congrArg (· ^ 2) e2).trans ?_
  show ‖_ • _‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (RealDat.nP_pos false).le]

end GlobalTheory.LowForm

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_indep_of_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  intro Y L A φ ψ hLA hφ hψ
  obtain ⟨w, hw⟩ := hLA
  obtain ⟨h1, h2⟩ := GlobalTheory.T.chernMass_lineBundleWeightOfIso Y L A φ ψ.isLB w hw hφ
  rw [← h2]
  exact GlobalTheory.T.chernIntegral_top_independent_of_smooth_weight Y A _ ψ h1 hψ

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem sig_X'_eq_sig_Y (D : D7) (τ : D.host.E →+* ℂ) : D.sp.X'.sig τ = (D.sp.Y D.R.m).sig τ := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hw : (Matrix.of fun i j => (D.sp.Y D.R.m).hT (D.sp.eYm (D.sp.X'.frame i)) (D.sp.eYm (D.sp.X'.frame j))) =
      D.sp.X'.gram := by
    exact Matrix.ext fun i j => D.sp.eYm_isom _ _
  have hs := D.sp.X'_sig τ
  rw [← hw] at hs
  have k := sig_family (D.sp.Y D.R.m) τ hτ _ hs (D.sp.Y_sig D.R.m τ)
  have h3 := sig_sum _ D.sp.X'_sig τ
  have h4 := sig_sum _ (D.sp.Y_sig D.R.m) τ
  have hYr : (D.sp.Y D.R.m).rank = D.sp.X'.rank := by
    rw [D.sp.Y_rank D.R.m le_rfl, D.sp.X'_rank]; rfl
  rw [hYr] at k h4
  exact Prod.ext (by omega) (by omega)

theorem colY_isV : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ j, j ≤ D.R.m → (columnBlock L j).IsV (rankV D 0 j) ((D.R.m - j) / 2) := by
  intro D T L μ0 hL j hj
  have hr : rankV D 0 j = D.R.rankY j := by
    simp only [rankV, zero_mul, add_zero]; rfl
  rw [hr]
  rcases hj.eq_or_lt with rfl | hlt
  · rw [colY_m]
    refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX⟩
    exact (sig_X'_eq_sig_Y D τ).trans (D.Y_sigval _ le_rfl τ)
  · rw [colY_lt L hlt]
    have e : min j D.R.m = j := min_eq_left hj
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hlt)⟩
    · exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [e])
    · exact (D.Y_sigval _ (min_le_right _ _) τ).trans (by rw [e]; rfl)

end GlobalTheory.ChiGrid
end
