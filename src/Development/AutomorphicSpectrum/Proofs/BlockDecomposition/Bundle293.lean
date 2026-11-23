module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructure
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle233
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
public import GroundTheory.AutomorphicForms.InductionParabolic
public import GroundTheory.AutomorphicForms.Satake
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle287
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle282
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.affine_cover_cohomology_finite : ∀ {O : Type} [CommRing O] [IsNoetherianRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = ⊤) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB (fun W => ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top).hom) U K) (p : ℕ),
    Module.Finite O (K.cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.VBGlue.finite_H_cx | exact GlobalTheory.CompanionTheory.VBGlue.finite_H_cx | (intros; apply GlobalTheory.CompanionTheory.VBGlue.finite_H_cx <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCModulus

theorem prod_zpow_eq {ι : Type*} {x : ℝ} (hx : x ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hx, ih]

theorem exponent_eq {h : ℕ} (d : Fin h → ℕ) (j : Fin h) :
    ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
  set f : Fin h → Fin h → ℤ := fun a b =>
    (d a : ℤ) * ((d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0))) with hf
  have hm : ∀ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = ∑ b, f a b := by
    intro a
    rw [← Finset.mul_sum]
    congr 1
    simp [modExp, Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]
  have hanti : ∀ a b, f b a = - f a b := by
    intro a b
    simp only [hf]
    ring
  have hcancel : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = 0 := by
    have h1 : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = ∑ a with a ≤ j, ∑ b with b ≤ j, f b a :=
      Finset.sum_comm
    have h2 : ∑ a with a ≤ j, ∑ b with b ≤ j, f b a = - ∑ a with a ≤ j, ∑ b with b ≤ j, f a b := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => hanti a b
    omega
  have hcross : ∑ a with a ≤ j, ∑ b with j < b, f a b =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have hab : a < b := lt_of_le_of_lt (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
    simp [hf, hab, hab.not_gt]
  calc ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0)
      = ∑ a with a ≤ j, ∑ b, f a b := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun a _ => by rw [hm]
    _ = ∑ a with a ≤ j, ((∑ b with b ≤ j, f a b) + ∑ b with j < b, f a b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ j)]
        simp only [not_le]
    _ = _ := by rw [Finset.sum_add_distrib, hcancel, zero_add, hcross]

theorem nabs_lt_one_of_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (ht : ValuativeRel.valuation k (t : k) < 1) :
    nabs k t < 1 := by
  obtain ⟨-, -, hle, hone, -⟩ := nabs_properties k
  have h1 : nabs k (1 : kˣ) = 1 := (hone 1).2 (by simp)
  refine lt_of_le_of_ne ?_ fun h => ht.ne ((hone t).1 h)
  rw [← h1]
  exact (hle t 1).2 (by simpa using ht.le)

theorem modulus_zj_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) →
    ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h →
    modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  intro k _ _ _ _ h N d _ hpos t ht j hj
  have hx1 := nabs_lt_one_of_valuation_lt_one k t ht
  obtain ⟨hmul, hx0', -, hone, -⟩ := nabs_properties k
  have hx0 := hx0' t
  have hdet : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) =
      if a ≤ j then nabs k t ^ d a else 1 := by
    intro a
    have hpow : ∀ n : ℕ, nabs k (t ^ n) = nabs k t ^ n := by
      intro n
      induction n with
      | zero => simpa using (hone 1).2 (by simp)
      | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
    by_cases ha : a ≤ j
    · have h1 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a := by
        apply Units.ext
        simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      rw [h1, hpow, if_pos ha]
    · have h1 : Zl.JC.zj d t j a = 1 := by simp [Zl.JC.zj, ha]
      rw [h1, if_neg ha, map_one]
      exact (hone 1).2 (by simp)
  have hE : 0 < (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    refine mul_pos (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨j, by simp⟩)
      (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨⟨j.val + 1, hj⟩, ?_⟩)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩
  have hmod : modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) =
      nabs k t ^ ((∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ)) := by
    rw [← exponent_eq, ← prod_zpow_eq hx0.ne']
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hdet]
    split_ifs with ha
    · rw [zpow_mul, zpow_natCast]
    · simp
  rw [hmod]
  exact zpow_lt_one₀ hx0 hx1 hE

end GlobalTheory.CompanionTheory.JCModulus
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ParabolicCompare

theorem unipRad_stdBlocks_eq_unipotentRadical (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    unipRad k (stdBlocks d hd) = GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd) := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GroundTheory.Automorphic.Parabolic.mem_unipotentRadical,
    GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_parab]
  refine and_congr Iff.rfl ⟨fun H i j hij => ?_, fun H a i j => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
    obtain rfl : a = b := by simpa [Zl.JC.blockIdx] using hij
    have := H a i j
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')
  · rw [H _ _ (by simp [Zl.JC.blockIdx])]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')

end GlobalTheory.CompanionTheory.ParabolicCompare
end

section


theorem _root_.GlobalTheory.T.positive_cone_structure : PositivityTheory.RgBcC.ConeSt := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.coneSt | exact GlobalTheory.CompanionTheory.ConeHaar.coneSt | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.coneSt <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.WordAdj

open GlobalTheory.CompanionTheory.WaveK.Sym (integrable_inner cpt_inner_left)
open GlobalTheory.CompanionTheory.WaveSpd (val_mem_GLs)

section Ops

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (X : Mat n) : ∀ y ∈ GLs n, R < lg y → Rd X u y = 0 := by
  intro y hy hR
  unfold LgFacts at hL
  have hc : ContinuousOn lg (GLs n) := (hL n).2.2.2.1.continuousOn
  have ho : IsOpen (GLs n) := by
    unfold GLs
    exact isOpen_ne_fun (by fun_prop) continuous_const
  have hU : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) := hc.isOpen_inter_preimage ho isOpen_Ioi
  have hev : u =ᶠ[nhds y] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds ⟨hy, hR⟩) fun z hz => hu z hz.1 hz.2
  unfold Rd
  rw [hev.fderiv_eq]
  simp

theorem Eu_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (a b : Fin n) : ∀ y ∈ GLs n, R < lg y → Eu s a b u y = 0 := by
  intro y hy hR
  have h1 := Rd_van hL hu (single a b 1) y hy hR
  have h2 := Rd_van hL hu (single a b Complex.I) y hy hR
  unfold Eu
  cases s <;> simp [h1, h2]

theorem Epow_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (m : ℕ) (a b : Fin n) : ∀ y ∈ GLs n, R < lg y → Epow s m a b u y = 0 := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, hu y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => Eu_van hL (ih c b) s a c y hy hR

theorem gel_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (m : ℕ) : ∀ y ∈ GLs n, R < lg y → gel s m u y = 0 := by
  intro y hy hR
  unfold gel
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => Epow_van hL hu s m a a y hy hR

theorem cpt_zOp (hL : LgFacts) (w : List (Bool × ℕ)) {u : Mat n → V} (hu : Cpt u) :
    Cpt (zOp w u) := by
  unfold Cpt at hu ⊢
  obtain ⟨R, hR⟩ := hu
  refine ⟨R, ?_⟩
  induction w with
  | nil => exact hR
  | cons p w ih => exact gel_van hL ih p.1 p.2

theorem zOp_contDiffOn (w : List (Bool × ℕ)) {u : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) :
    ContDiffOn ℝ ∞ (zOp w u) (GLs n) := by
  induction w with
  | nil => exact hu
  | cons p w ih => exact GlobalTheory.CompanionTheory.RCalc.gel_contDiffOn p.1 p.2 ih

theorem zOp_append (w w' : List (Bool × ℕ)) (u : Mat n → V) :
    zOp (w ++ w') u = zOp w (zOp w' u) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    show gel p.1 p.2 (zOp (w ++ w') u) = gel p.1 p.2 (zOp w (zOp w' u))
    rw [ih]

end Ops

private theorem isHecke_div_and_resEtaPow_div (n : ℕ) (s : Bool) (m : ℕ) : ∃ (M : ℕ) (e : Fin M → ℂ) (v : Fin M → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal [(s, m)] χ) = ∑ j, e j * zVal (v j) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ = ∑ j, e j * ∫ y : G n, ⟪f y.val, zOp (v j) h y.val⟫_ℂ ∂μ) := by
  obtain ⟨M, d, w, hv, ho⟩ := GlobalTheory.T.gelfand_operator_center_expansion n m
  refine ⟨M, fun j => (-1) ^ m * d j, fun j => (w j).map (fun k => (!s, k)), ?_, ?_⟩
  · intro χ hχ
    have h1 : zVal [(s, m)] χ = GlobalTheory.Dec.gelfVal (χ s) m := by simp [zVal]
    rw [h1, conj_gelfVal_of_isHerm n χ hχ s m]
    have h3 : ∀ j, zVal ((w j).map (fun k => (!s, k))) χ = ((w j).map (GlobalTheory.Dec.gelfVal (χ (!s)))).prod := by
      intro j
      simp [zVal, List.map_map, Function.comp_def]
    rw [Finset.sum_congr rfl (fun j _ => by rw [h3 j, mul_assoc]), ← Finset.mul_sum, ← hv (χ (!s)), ← mul_assoc, ← mul_pow]
    simp
  · intro hL hR _ _ μ _ V _ _ _ f h hf hh cf ch
    rw [GlobalTheory.T.gelfand_operator_adjoint hL hR n μ V s m f h hf hh cf ch]
    have hpt : ∀ y : G n, ⟪f y.val, GlobalTheory.CompanionTheory.WaveMult.gelT (!s) m h y.val⟫_ℂ = ∑ j, d j * ⟪f y.val, zOp ((w j).map (fun k => (!s, k))) h y.val⟫_ℂ := by
      intro y
      rw [ho hR (!s) h hh y.val (val_mem_GLs y), inner_sum]
      simp only [inner_smul_right]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun j _ => (integrable_inner μ hL hf (zOp_contDiffOn _ hh) (cpt_inner_left cf)).const_mul (d j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring

private theorem isPair_and_isPair_of_isTriple {M N : ℕ} (F : Fin M → Fin N → ℂ) : ∑ k : Fin (M * N), F (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = ∑ j, ∑ i, F j i :=
  (Equiv.sum_comp finProdFinEquiv.symm (fun q => F q.1 q.2)).trans (Fintype.sum_prod_type _)

theorem word_adjoint : ∀ (n : ℕ) (w : List (Bool × ℕ)), ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪zOp w f y.val, h y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i) h y.val⟫_ℂ ∂μ) := by
  intro n w
  induction w with
  | nil =>
    refine ⟨1, fun _ => 1, fun _ => [], ?_, ?_⟩
    · intro χ _
      simp [zVal]
    · intro _ _ _ _ μ _ V _ _ _ f h _ _ _ _
      simp [zOp]
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    obtain ⟨N, c, w₁, hz, hi⟩ := ih
    obtain ⟨M, e, v, hz1, hi1⟩ := isHecke_div_and_resEtaPow_div n s m
    refine ⟨M * N, fun k => e (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2,
      fun k => w₁ (finProdFinEquiv.symm k).2 ++ v (finProdFinEquiv.symm k).1, ?_, ?_⟩
    · intro χ hχ
      have hs := isPair_and_isPair_of_isTriple (fun j i => e j * c i * zVal (w₁ i ++ v j) χ)
      beta_reduce at hs
      rw [hs]
      have h1 : zVal ((s, m) :: w) χ = zVal [(s, m)] χ * zVal w χ := zVal_append [(s, m)] w χ
      rw [h1, map_mul, hz1 χ hχ, hz χ hχ, Finset.sum_mul_sum]
      simp only [zVal_append]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    · intro hL hR _ _ μ _ V _ _ _ f h hf hh cf ch
      have hs := isPair_and_isPair_of_isTriple (fun j i => e j * c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i ++ v j) h y.val⟫_ℂ ∂μ)
      beta_reduce at hs
      rw [hs]
      have hwf := zOp_contDiffOn w hf
      have cwf := cpt_zOp hL w cf
      have step1 : ∫ y : G n, ⟪zOp ((s, m) :: w) f y.val, h y.val⟫_ℂ ∂μ =
          ∑ j, e j * ∫ y : G n, ⟪zOp w f y.val, zOp (v j) h y.val⟫_ℂ ∂μ :=
        hi1 hL hR μ V (zOp w f) h hwf hh cwf ch
      rw [step1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hi hL hR μ V f (zOp (v j) h) hf (zOp_contDiffOn _ hh) cf (cpt_zOp hL _ ch), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zOp_append]
      ring

end GlobalTheory.CompanionTheory.WaveMult.WordAdj
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.closed_derivative_system_smooth : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family | exact GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family | (intros; apply GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family <;> assumption)
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_kernel_convolution : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ) (k k' K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsBump g' T' → IsKer μ E w g k → IsKer μ E w' g' k' → IsKer μ E (w ++ w') (gconv g g') K → ∀ y ∈ GLs n, conv μ E k k' y = K y := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer | exact GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.PinLift

theorem gl_one_comm {k : Type} [Field k] (a b : GL (Fin 1) k) : a * b = b * a := by
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi
  subst hj
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one]
  exact mul_comm _ _

noncomputable def torusCharHom {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) :
    (∀ _ : Fin n, GL (Fin 1) k) →* ℂ where
  toFun := PositivityTheory.Lbc.torusChar ξ
  map_one' := by simp [PositivityTheory.Lbc.torusChar]
  map_mul' a b := by simp [PositivityTheory.Lbc.torusChar, Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.PinLift
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.admissible_central_levi_congruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (m : ℕ), 1 ≤ m → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β, a * u * a⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β) → (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, a⁻¹ * z * a ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β) → ∀ (y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) (Λ : ℂ), y ≠ 0 → (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y → ∃ (w : V) (l : Module.Dual ℂ V), (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧ (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧ ∀ j : ℕ, l (π (a ^ j) w) = Λ ^ j := by
  first | exact @GlobalTheory.CompanionTheory.JacquetCoeff.exists_coeff_geometric | exact GlobalTheory.CompanionTheory.JacquetCoeff.exists_coeff_geometric | (intros; apply GlobalTheory.CompanionTheory.JacquetCoeff.exists_coeff_geometric <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.admissible_central_levi_fixed_submodule : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → ∀ (W T : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π)) (Λ : ℂ), Λ ≠ 0 → T ≤ W → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w ∈ W) → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w - Λ • w ∈ T) → (∃ w ∈ W, w ∉ T) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π, y ≠ 0 ∧ (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) ∧ GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y := by
  first | exact @GlobalTheory.CompanionTheory.JacquetEigen.exists_eigenvector_fixed | exact GlobalTheory.CompanionTheory.JacquetEigen.exists_eigenvector_fixed | (intros; apply GlobalTheory.CompanionTheory.JacquetEigen.exists_eigenvector_fixed <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical


theorem _root_.GlobalTheory.T.subquotient_principal_series_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient | exact GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient | (intros; apply GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient <;> assumption)
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem sliceBranches : GroundTheory.Heights₂.Heights.SliceBranches.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranches.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full
    GlobalTheory.T.branch_proper_at_point_holds
    GroundTheory.Heights₂.Heights.SliceMatricesOpen.full
    GroundTheory.Heights₂.Heights.ImplicitCurve.full

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end
