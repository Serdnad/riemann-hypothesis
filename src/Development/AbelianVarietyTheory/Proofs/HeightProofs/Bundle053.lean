module

public import Formalism.LocalRingCardinality.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle044
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.LocalRingCardinality.DataHost
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FullTranscendenceDegree
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle002
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open GlobalTheory.EX

theorem x_le_zBase_of_pow_le_n {D : D7} (L : SizeData₂ D) (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ)) :
    L.sc.x ≤ zBase L := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hL : 1 ≤ L.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow hx.le he.le
  have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hf : (D.R.n : ℝ) ≤ D.R.f := by
    unfold Ranks.f; exact_mod_cast (by omega : D.R.n ≤ 2 * D.R.n)
  have hr : (1 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hxf : L.sc.x ≤ (D.R.f : ℝ) := h1.trans (hn.trans hf)
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  unfold zBase
  calc L.sc.x ≤ (D.R.f : ℝ) * 1 * 1 := by linarith
    _ ≤ _ := by gcongr

end GlobalTheory.FinalJoin2

end
end

section

noncomputable section

namespace GlobalTheory.BignessCompare

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree (CuspAt XP Generates ptNorm l2Norm FullTrdeg SmallForm ExistsNonzeroCuspFormOfWeightPair CurveModelAt CurveModelExists
  ptNorm_nonneg)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} [Fintype κ]

theorem bdd_of_mem_holSub (X : κ → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, ∀ p : FPt X, (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ M := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    refine ⟨∑ c, |C c|, fun p => (hC p.1 p.2 p.2.2).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  | zero => exact ⟨0, fun p => (pnorm_zero _ _ _).le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    exact ⟨a + b, fun p => (pnorm_add_le _ _ _ _ _).trans (add_le_add (ha p) (hb p))⟩
  | smul a P _ hP =>
    obtain ⟨b, hb⟩ := hP
    exact ⟨‖a‖ * b, fun p => (pnorm_smul _ _ a _ _).le.trans (mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))⟩

end Model

section Weights

variable {D : D7} {j : ℕ}

end Weights

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
  (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)


end Record

section Inst

variable {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {ka wL wF : WeightFamilies.Wt D j}






end Inst

end GlobalTheory.BignessCompare
end
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin.NoPoint

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem subsingleton_sections_of_no_leadingTerm (G : GlobalFamilyData X ka wL wF) (hd : G.del = 0) (la : HeightOneSpectrum (𝓞 B.KO))
    (hB : InBasis G la) : Subsingleton (SectionSheafQuotient X la G.w wF) := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have h := hB.2
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  exact (Submodule.subsingleton_iff (Kp X la G.N)).1 (subsingleton_of_bot_eq_top h)

theorem heights_of_del_zero (G : GlobalFamilyData X ka wL wF) (Q : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have hI : ∀ la, (Q la).Ila = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    unfold LocalPointData.Ila
    exact Module.length_eq_zero
  have hN : ∀ la, (Q la).Net = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    haveI : Subsingleton (OsK X la G.w) := (hC la).2.2.1.subsingleton
    haveI : IsEmpty (PtsG G la) := ⟨fun ζ => ζ.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    unfold LocalPointData.Net
    exact finsum_of_isEmpty _
  have hd' : (G.del : ℝ) = 0 := by rw [hd]; exact Nat.cast_zero
  refine ⟨fun la => by simp [hI la], by simp [hI, summable_zero], by simp [hI, hd'],
    fun _ => ⟨by simp [hN, summable_zero], by simp [hN, hd']⟩⟩

theorem inBasis_xplus (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : InBasis G la) : InBasis (gd2Xplus G E hM) la := h

theorem heights_xplus_of_del_zero (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E)
    (Q : ∀ la, LocalPointData (gd2Xplus G E hM) la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet :=
  heights_of_del_zero (gd2Xplus G E hM) Q Gc PH Prw Pet hd (fun la => inBasis_xplus G E hM la (hB la)) hC

end Abstract




theorem heights_no_point : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (Q : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la) (Gc PH Prw Pet : ℝ), G.del = 0 → (∀ la, InBasis G la) → (∀ la, (Q la).InCurve) → Heights Q Gc PH Prw Pet :=
  fun _ _ h j hj _ _ _ _ _ _ _ _ _ _ _ _ _ G Q Gc PH Prw Pet hd hB hC =>
    heights_xplus_of_del_zero G (extAll h j hj) (intAtExt_extAll h j hj) Q Gc PH Prw Pet hd hB hC

end GlobalTheory.RunJoin.NoPoint
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.Cover

theorem zeta_mul_mem (F : IntermediateField ℚ ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : n.Coprime m)
    (h1 : zeta m ∈ F) (h2 : zeta n ∈ F) : zeta (m * n) ∈ F := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  have huv' : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : zeta (m * n) = zeta m ^ u * zeta n ^ v := by
    unfold zeta
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * huv'
  rw [e]
  exact mul_mem (zpow_mem h1 u) (zpow_mem h2 v)

theorem FO_le_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem half_of_split (D : D7) {p : ℕ} (hp : SplitOK D p) (P : HeightOneSpectrum (𝓞 D.host.K))
    (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (I : Ideal (𝓞 D.host.E))
    (hI : I = P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {w0E D}} ∧
      I * I.map (bH D) = Ideal.span {(p : 𝓞 D.host.E)} ∧ I ⊔ I.map (bH D) = ⊤ := by
  obtain ⟨e, he1, he2, hpb⟩ := LPb.pb_eq_JK D hp P hP
  rw [hpb, LPb.map_JK] at hI
  subst hI
  refine ⟨fromK_of_gen ⟨_, rfl, ?_⟩, ?_, ?_⟩
  · rintro y (rfl | hy)
    · exact Subalgebra.natCast_mem _ _
    · rw [Set.mem_singleton_iff.1 hy]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
  · rw [LPb.QE_map_bar, LPb.QE_mul D _ _ he1 he2]
  · rw [LPb.QE_map_bar, ← Ideal.isCoprime_iff_sup_eq]
    exact LPb.QE_cop_self D _ _ he2

end GlobalTheory.FinalJoin.Cover
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.HaarSmallBall

variable {n : ℕ} {ε : Fin n → Bool}

lemma toMK_mem_unitary (k : Formalism.REAL.KG ε) : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  ((Formalism.REAL.mem_KG ε (k : Formalism.REAL.UJ ε)).1 k.2).1

lemma toMK_mul' (a b : Formalism.REAL.KG ε) : toMK (a * b) = toMK a * toMK b := rfl

lemma toMK_inv'' (k : Formalism.REAL.KG ε) : toMK k⁻¹ = star (toMK k) := by
  show ((((k : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Matrix (Fin n) (Fin n) ℂ) = _
  exact Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (toMK_mem_unitary k))

lemma norm_entry_le_one (k : Formalism.REAL.KG ε) (i j : Fin n) : ‖toMK k i j‖ ≤ 1 :=
  entry_norm_bound_of_unitary (toMK_mem_unitary k) i j

lemma hs_translate_le (a b : Formalism.REAL.KG ε) (η : ℝ)
    (hη : ∀ i j, ‖toMK b i j - toMK a i j‖ ≤ η) :
    Formalism.REAL.hs (toMK (a⁻¹ * b) - 1) ≤ (n : ℝ) * n * ((n : ℝ) * η) ^ 2 := by
  have hA : star (toMK a) * toMK a = 1 := Unitary.star_mul_self_of_mem (toMK_mem_unitary a)
  have heq : toMK (a⁻¹ * b) - 1 = star (toMK a) * (toMK b - toMK a) := by
    rw [toMK_mul', toMK_inv'', Matrix.mul_sub, hA]
  rw [heq]
  have hent : ∀ i j, ‖(star (toMK a) * (toMK b - toMK a)) i j‖ ≤ (n : ℝ) * η := by
    intro i j
    rw [Matrix.mul_apply]
    calc ‖∑ l, star (toMK a) i l * (toMK b - toMK a) l j‖
        ≤ ∑ l, ‖star (toMK a) i l * (toMK b - toMK a) l j‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin n, η := by
          apply Finset.sum_le_sum
          intro l _
          rw [norm_mul, Matrix.star_apply, norm_star, Matrix.sub_apply]
          calc ‖toMK a l i‖ * ‖toMK b l j - toMK a l j‖ ≤ 1 * η :=
                mul_le_mul (norm_entry_le_one a l i) (hη l j) (norm_nonneg _) zero_le_one
            _ = η := one_mul η
      _ = (n : ℝ) * η := by simp
  unfold Formalism.REAL.hs
  calc ∑ i, ∑ j, ‖(star (toMK a) * (toMK b - toMK a)) i j‖ ^ 2
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((n : ℝ) * η) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hent i j) 2
    _ = (n : ℝ) * n * ((n : ℝ) * η) ^ 2 := by simp [Finset.sum_const]; ring

noncomputable def cell (h x : ℝ) : Fin (⌊2 / h⌋₊ + 1) :=
  ⟨min ⌊(x + 1) / h⌋₊ ⌊2 / h⌋₊, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma abs_sub_lt_of_cell_eq {h x y : ℝ} (hh : 0 < h) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hc : cell h x = cell h y) : |x - y| < h := by
  have hx' := abs_le.1 hx
  have hy' := abs_le.1 hy
  have ha0 : 0 ≤ (x + 1) / h := div_nonneg (by linarith) hh.le
  have hb0 : 0 ≤ (y + 1) / h := div_nonneg (by linarith) hh.le
  have hfa : ⌊(x + 1) / h⌋₊ ≤ ⌊2 / h⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hfb : ⌊(y + 1) / h⌋₊ ≤ ⌊2 / h⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hc' : ⌊(x + 1) / h⌋₊ = ⌊(y + 1) / h⌋₊ := by
    have := congrArg Fin.val hc
    simp only [cell, min_eq_left hfa, min_eq_left hfb] at this
    exact this
  have h1 := Nat.floor_le ha0
  have h2 := Nat.lt_floor_add_one ((x + 1) / h)
  have h3 := Nat.floor_le hb0
  have h4 := Nat.lt_floor_add_one ((y + 1) / h)
  rw [hc'] at h1 h2
  have hab : |(x + 1) / h - (y + 1) / h| < 1 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have : (x + 1) / h - (y + 1) / h = (x - y) / h := by ring
  rw [this, abs_div, abs_of_pos hh, div_lt_one hh] at hab
  exact hab

end GlobalTheory.HaarSmallBall

namespace GlobalTheory.HaarSmallBall

variable {n : ℕ} {ε : Fin n → Bool}

noncomputable def roundK (h : ℝ) (k : Formalism.REAL.KG ε) :
    Fin n → Fin n → Fin (⌊2 / h⌋₊ + 1) × Fin (⌊2 / h⌋₊ + 1) :=
  fun i j => (cell h (toMK k i j).re, cell h (toMK k i j).im)

lemma norm_sub_lt_of_round_eq {h : ℝ} (hh : 0 < h) {a b : Formalism.REAL.KG ε}
    (hab : roundK h b = roundK h a) (i j : Fin n) : ‖toMK b i j - toMK a i j‖ ≤ 2 * h := by
  have e := congrFun (congrFun hab i) j
  simp only [roundK, Prod.mk.injEq] at e
  have hre := abs_sub_lt_of_cell_eq hh ((Complex.abs_re_le_norm _).trans (norm_entry_le_one b i j))
    ((Complex.abs_re_le_norm _).trans (norm_entry_le_one a i j)) e.1
  have him := abs_sub_lt_of_cell_eq hh ((Complex.abs_im_le_norm _).trans (norm_entry_le_one b i j))
    ((Complex.abs_im_le_norm _).trans (norm_entry_le_one a i j)) e.2
  calc ‖toMK b i j - toMK a i j‖ ≤ |(toMK b i j - toMK a i j).re| + |(toMK b i j - toMK a i j).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * h := by rw [Complex.sub_re, Complex.sub_im]; linarith

theorem smallBall : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → c * δ ^ D ≤ (muK ε {k | Formalism.REAL.hs (toMK k - 1) ≤ δ}).toReal := by
  intro n ε
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, 0, fun δ hδ _ => ?_⟩
    have hset : {k : Formalism.REAL.KG ε | Formalism.REAL.hs (toMK k - 1) ≤ δ} = Set.univ := by
      ext k; simp [Formalism.REAL.hs, hδ.le]
    rw [hset, measure_univ]; simp
  set C : ℝ := 5 * (n : ℝ) ^ 2 with hC
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCpos : 0 < C := by positivity
  refine ⟨(C ^ (2 * n * n))⁻¹, by positivity, 2 * n * n, fun δ hδ hδ1 => ?_⟩
  set h : ℝ := δ / (2 * (n : ℝ) ^ 2) with hhdef
  have hh : 0 < h := by positivity
  set B : Set (Formalism.REAL.KG ε) := {k | Formalism.REAL.hs (toMK k - 1) ≤ δ} with hB
  set m : ℕ := ⌊2 / h⌋₊ + 1 with hm
  let R : Formalism.REAL.KG ε → Fin n → Fin n → Fin m × Fin m := roundK (ε := ε) h

  have hfib : ∀ g, muK ε (R ⁻¹' {g}) ≤ muK ε B := by
    intro g
    by_cases hne : (R ⁻¹' {g}).Nonempty
    · obtain ⟨a, ha⟩ := hne
      calc muK ε (R ⁻¹' {g}) ≤ muK ε ((fun x => a⁻¹ * x) ⁻¹' B) := by
            apply measure_mono
            intro b hb
            have hab : R b = R a := by
              rw [Set.mem_preimage, Set.mem_singleton_iff] at ha hb; rw [ha, hb]
            show Formalism.REAL.hs (toMK (a⁻¹ * b) - 1) ≤ δ
            refine (hs_translate_le a b (2 * h) (norm_sub_lt_of_round_eq hh hab)).trans ?_
            have : (n : ℝ) * n * ((n : ℝ) * (2 * h)) ^ 2 = δ ^ 2 := by
              rw [hhdef]; field_simp
            rw [this]; nlinarith
        _ = muK ε B := measure_preimage_mul _ _ _
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp
  have hcov : (1 : ENNReal) ≤
      (Fintype.card (Fin n → Fin n → Fin m × Fin m) : ENNReal) * muK ε B := by
    calc (1 : ENNReal) = muK ε Set.univ := measure_univ.symm
      _ = muK ε (⋃ g, R ⁻¹' {g}) := by
          congr 1; ext k; simp
      _ ≤ ∑ g, muK ε (R ⁻¹' {g}) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _g : Fin n → Fin n → Fin m × Fin m, muK ε B := Finset.sum_le_sum fun g _ => hfib g
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card (Fin n → Fin n → Fin m × Fin m) : ℝ) = (m : ℝ) ^ (2 * n * n) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    push_cast; ring
  have hcovR : (1 : ℝ) ≤ (m : ℝ) ^ (2 * n * n) * (muK ε B).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)) hcov
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hcard, ENNReal.toReal_one] at this
    exact this
  have hmδ : (m : ℝ) * δ ≤ C := by
    have hfl : ((⌊2 / h⌋₊ : ℕ) : ℝ) ≤ 2 / h := Nat.floor_le (by positivity)
    have h2h : 2 / h * δ = 4 * (n : ℝ) ^ 2 := by rw [hhdef]; field_simp; ring
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    calc (m : ℝ) * δ = ((⌊2 / h⌋₊ : ℕ) : ℝ) * δ + δ := by rw [hm]; push_cast; ring
      _ ≤ 2 / h * δ + δ := by nlinarith
      _ ≤ C := by rw [h2h, hC]; nlinarith
  have hpow : ((m : ℝ) * δ) ^ (2 * n * n) ≤ C ^ (2 * n * n) :=
    pow_le_pow_left₀ (by positivity) hmδ _
  have hμ0 : 0 ≤ (muK ε B).toReal := ENNReal.toReal_nonneg
  rw [inv_mul_le_iff₀ (by positivity)]
  calc δ ^ (2 * n * n) ≤ δ ^ (2 * n * n) * ((m : ℝ) ^ (2 * n * n) * (muK ε B).toReal) :=
        le_mul_of_one_le_right (by positivity) hcovR
    _ = ((m : ℝ) * δ) ^ (2 * n * n) * (muK ε B).toReal := by rw [mul_pow]; ring
    _ ≤ C ^ (2 * n * n) * (muK ε B).toReal := mul_le_mul_of_nonneg_right hpow hμ0

end GlobalTheory.HaarSmallBall
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.compactUnitaryHaar_smallBall_lower_bound : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → c * δ ^ D ≤ (muK ε {k | Formalism.REAL.hs (toMK k - 1) ≤ δ}).toReal := by
  first | exact @GlobalTheory.HaarSmallBall.smallBall | exact GlobalTheory.HaarSmallBall.smallBall | (intros; apply GlobalTheory.HaarSmallBall.smallBall <;> assumption)

end
end
