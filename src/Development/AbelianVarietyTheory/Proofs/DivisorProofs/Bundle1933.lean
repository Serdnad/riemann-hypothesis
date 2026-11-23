module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult.OneLevel

variable {D : D7}

def levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GA D V) :=
  levelOpen D.sp.cm.sig V.gram (frameLat V) ⊓
    (⨅ v : T.S, (stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)).comap (proj D.sp.cm.sig V.gram v.1)) ⊓
    U.frame.iwahori.comap (proj D.sp.cm.sig V.gram U.u)

def level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GfC V) := (levelAd T U).subgroupOf (GfC V)

theorem mem_levelAd {V : HSp D} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {g : GA D V} :
    g ∈ levelAd T U ↔ (∀ v, proj D.sp.cm.sig V.gram v g ∈ Kv V v) ∧
      (∀ v : T.S, proj D.sp.cm.sig V.gram v.1 g ∈ stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)) ∧
      proj D.sp.cm.sig V.gram U.u g ∈ U.frame.iwahori := by
  simp [levelAd, mem_levelOpen, Subgroup.mem_iInf, and_assoc]

theorem isOpen_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (levelAd T U : Set (GA D V)) := by
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  simp only [levelAd, Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_comap]
  refine ((isOpen_levelOpen _ _ _).inter (isOpen_iInter_of_finite fun v => ?_)).inter
    (U.frame.isOpen_iwahori.preimage (continuous_proj _ _ _))
  exact (isOpen_stabLocOne _ _ _ (isCMExt_host D)).preimage (continuous_proj _ _ _)

theorem isClosed_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsClosed (levelAd T U : Set (GA D V)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_levelAd T U)

theorem isOpen_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (level T U : Set (GfC V)) := by
  rw [level, Subgroup.coe_subgroupOf]
  exact (isOpen_levelAd T U).preimage continuous_subtype_val

theorem isCompact_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsCompact (level T U : Set (GfC V)) := by
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  rw [Subtype.isCompact_iff]
  have e : ((↑) : GfC V → GA D V) '' (level T U : Set (GfC V)) =
      (levelFin D.sp.cm.sig V.gram (frameLat V) : Set (GA D V)) ∩ levelAd T U := by
    ext g
    simp only [level, Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, mem_levelFin]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.2, (mem_levelAd.1 hx).1⟩, hx⟩
    · rintro ⟨⟨hf, -⟩, hg⟩
      exact ⟨⟨g, hf⟩, hg, rfl⟩
  rw [e]
  exact (isCompact_levelFin _ _ _).inter_right (isClosed_levelAd T U)

theorem conv_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {f f' : G → ℂ} {a : G} (ha : ∀ y, f (a * y) = f y) (x : G) : conv μ f f' (a * x) = conv μ f f' x := by
  simp only [conv]
  rw [← integral_mul_left_eq_self _ a]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [ha, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end GlobalTheory.TrMult.OneLevel


open GlobalTheory.TrMult.OneLevel in
theorem GlobalTheory.TrMult.oneLevel : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ ff, IsTestFin T U μf ff → SphRest T U ff → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ ∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g := by
  intro D V T U
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  refine ⟨level T U, isOpen_level T U, isCompact_level T U, fun μf hμ ff hT hS => ⟨hT.isFinFamily, fun k hk g => ?_⟩⟩
  obtain ⟨hK, hOne, hI⟩ := mem_levelAd.1 (Subgroup.mem_subgroupOf.1 hk)
  simp only [finFn]
  refine finprod_congr fun v => ?_
  rw [Subgroup.coe_mul, map_mul]
  generalize proj D.sp.cm.sig V.gram v (g : GA D V) = x
  by_cases hv : v ∈ T.S
  · obtain ⟨h, -, e⟩ := hT.2.1 ⟨v, hv⟩
    have he : ∀ y, T.idem μf ⟨v, hv⟩ (proj D.sp.cm.sig V.gram v (k : GA D V) * y) = T.idem μf ⟨v, hv⟩ y := fun y =>
      (typeIdem_mul_ker (μf v) (T.frame ⟨v, hv⟩).red (T.τ ⟨v, hv⟩) (k := ⟨_, hK v⟩)
        (((T.frame ⟨v, hv⟩).red_eq_one_iff _).2 (hOne ⟨v, hv⟩)) y).1
    simp only at e
    rw [e]
    exact conv_mul_left _ (conv_mul_left _ he) x
  · by_cases hu : v = U.u
    · subst hu
      obtain ⟨t, -, e⟩ := hT.2.2.1
      rw [e]
      simp only [SplitAt.cosetFn, SplitAt.iwahoriCoset, Set.indicator]
      congr 1
      apply propext
      rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨(proj D.sp.cm.sig V.gram U.u (k : GA D V))⁻¹ * a, mul_mem (inv_mem hI) ha, b, hb, ?_⟩
        simp only [mul_assoc]
        rw [eq_inv_mul_iff_mul_eq]
        simpa only [mul_assoc] using e
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨_ * a, mul_mem hI ha, b, hb, by group⟩
    · simpa using hS v hv hu _ (hK v) 1 (one_mem _) x
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem lowMul_upU_leadMinor_ne_zero (K : Type) [Field K] (s : ℕ) (y : Low s → K) (b : Matrix (Fin s) (Fin s) K) (hb : ∀ i j, i < j → b i j = 0) (hdet : b.det ≠ 0) :
    (upU y).det = 1 ∧ ∀ k : ℕ, ((b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 := by
  have hU : ∀ a c : Fin s, c < a → upU y a c = 0 := by
    intro a c h
    simp [upU, Matrix.of_apply, not_lt.mpr h.le, h.ne']
  have hUd : ∀ a : Fin s, upU y a a = 1 := by
    intro a; simp [upU, Matrix.of_apply]
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h1 : b.det = ∏ i, b i i := Matrix.det_of_lowerTriangular b (fun i j h => hb i j h)
    rw [h1] at hdet
    intro i
    exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular (fun a c h => hU a c h)]
    simp [hUd]
  · intro k
    have hmul : (b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
          (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) =
        b.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) *
          (upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
            (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < k)]
      have h0 : ∑ l : {a : Fin s // ¬ (a : ℕ) < k}, b i.1 l.1 * upU y l.1 j.1 = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        have : i.1 < l.1 := by
          have := i.2; have := l.2; rw [Fin.lt_iff_val_lt_val]; omega
        rw [hb _ _ this, zero_mul]
      rw [h0, add_zero]
    rw [hmul, Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => hb i.1 j.1 h)]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i.1)
    · rw [Matrix.det_of_upperTriangular (fun i j h => hU i.1 j.1 h)]
      simp [hUd]

end GlobalTheory.FlagCell2
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.CellPotSmooth

theorem upM_fb_contDiffAt_two {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (τ : ι) (w : V n) :
    MContDiffAt 2 (fun w => upM (fb ε w) τ) w := by
  intro a b
  simp only [upM, upU, Matrix.of_apply, fb]
  split_ifs with h1 h2
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨τ, ⟨(b, a), h1⟩⟩))).contDiff.restrict_scalars ℝ).contDiffAt
  · exact contDiffAt_const
  · exact contDiffAt_const

theorem G_bsL_smooth {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (τ : ι)
    (hG : MContDiffAt 2 (fun v => G v τ) (bsL ε w)) : MContDiffAt 2 (fun w => G (bsL ε w) τ) w := by
  intro a b
  exact (hG a b).comp w (((bsL ε).contDiff.restrict_scalars ℝ).contDiffAt)

theorem upU_isUnit {s : ℕ} (y : Low s → ℂ) : IsUnit (upU y) := by
  rw [Matrix.isUnit_iff_isUnit_det, upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  exact isUnit_one

theorem leadMinor_re_pos {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (hA : A.PosDef) (j : ℕ) : 0 < (leadMinor A j).re := by
  have h := (hA.submatrix (Subtype.val_injective (p := fun a : Fin s => (a : ℕ) < j))).det_pos
  exact (Complex.pos_iff.1 h).1

theorem cellPot_contDiffAt : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  intro ι m n d ε G w x hP hG
  set A : V n → Matrix (Fin (m x.1)) (Fin (m x.1)) ℂ :=
    fun w => upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ with hAdef
  have hA : MContDiffAt 2 A w :=
    ((upM_fb_contDiffAt_two ε x.1 w).mul (G_bsL_smooth ε G w x.1 hG)).mul (upM_fb_contDiffAt_two ε x.1 w).conjTranspose
  have hPA : (A w).PosDef := by
    refine hP.mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2 (upU_isUnit _)
  have hm : ∀ j : ℕ, ContDiffAt ℝ 2 (fun w => (leadMinor (A w) j).re) w := fun j =>
    Complex.reCLM.contDiff.contDiffAt.comp w (hA.submatrix _ _).det
  have h1 := leadMinor_re_pos hPA (x.2 + 1)
  have h0 := leadMinor_re_pos hPA x.2
  have hpos : 0 < grD (A w) x.2 := div_pos h1 h0
  refine ⟨?_, hpos⟩
  have hd : ContDiffAt ℝ 2 (fun w => grD (A w) x.2) w := (hm _).div (hm _) h0.ne'
  exact (hd.log hpos.ne').neg

end GlobalTheory.CellPotSmooth
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_row_eq {s : ℕ} (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a : Fin s) (ha : a ≤ i) (k : Fin s) :
    upU y' a k = upU y a k := by
  simp only [upU, Matrix.of_apply]
  split_ifs with hk
  · exact h ⟨(k, a), hk⟩ ha
  · rfl
  · rfl

theorem upU_gram_entry_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a c : Fin s) (ha : a ≤ i) (hc : c ≤ i) :
    (upU y' * G * (upU y')ᴴ) a c = (upU y * G * (upU y)ᴴ) a c := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, upU_row_eq y y' i h a ha,
    upU_row_eq y y' i h c hc]

theorem leadMinor_upU_gram_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (j : ℕ) (hj : j ≤ (i : ℕ) + 1) :
    leadMinor (upU y' * G * (upU y')ᴴ) j = leadMinor (upU y * G * (upU y)ᴴ) j := by
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  apply upU_gram_entry_eq G y y' i h
  · rw [Fin.le_def]; have := a.2; omega
  · rw [Fin.le_def]; have := b.2; omega

theorem grD_upU_gram_eq : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  intro s G y y' i h
  unfold grD
  rw [leadMinor_upU_gram_eq G y y' i h _ (by simp), leadMinor_upU_gram_eq G y y' i h _ (by omega)]

end GlobalTheory.FlagCell2
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem isOpen_setOf_mem_frames {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] [Finite ι] {m k : ι → ℕ}
    {M : GlobalTheory.ZH.RatModel F Ω} (S : Fr M m k) (B : Mat m Ω) : IsOpen {z : M.Z | B ∈ S.S z} := by
  have hP (g : Mat m Ω) : IsOpen {z : M.Z | Par k (M.O z).toSubring g} := by
    have : {z : M.Z | Par k (M.O z).toSubring g} = ⋂ τ, ((⋂ i, ⋂ j, {z : M.Z | g τ i j ∈ M.O z}) ∩
        ({_z : M.Z | (g τ).det ≠ 0} ∩ ({z : M.Z | (g τ).det⁻¹ ∈ M.O z} ∩
          {_z : M.Z | ∀ i j : Fin (m τ), (i : ℕ) < k τ → i < j → g τ i j = 0}))) := by
      ext z
      simp only [Par, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      rfl
    rw [this]
    exact isOpen_iInter_of_finite fun τ => (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      M.isOpen_setOf_mem_O _).inter (isOpen_const.inter ((M.isOpen_setOf_mem_O _).inter isOpen_const))
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨U, A, hzU, -, hU⟩ := S.loc z
  exact ⟨(U : Set M.Z) ∩ {z' | Par k (M.O z').toSubring (B * A⁻¹)}, fun w hw => (hU w hw.1 B).2 hw.2,
    U.isOpen.inter (hP _), hzU, (hU z hzU B).1 hz⟩

theorem isOpen_inCell_and_regAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f →
    ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), IsOpen {y : Y.X | InCell E E' φ f A u y} ∧
      ∀ y, InCell E E' φ f A u y → ∀ j, RegAt y (u j) := by
  intro F _ X Y ι _ m E E' φ f hR A u
  refine ⟨((isOpen_setOf_mem_frames E A).preimage f.continuous).inter (isOpen_setOf_mem_frames E' _), ?_⟩
  rintro y ⟨hA, hu⟩ ⟨τ, ⟨b, a⟩, hab⟩
  have h := hR.sub y _ hu A hA
  have hd : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
    have := Mat.det_map A (φ : X.Fn →+* Y.Fn) τ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA τ))
  rw [mul_assoc, Mat.mul_inv hd, mul_one] at h
  have h2 := (h τ).1 a b
  have hab' : a < b := hab
  have e : upM u τ a b = u ⟨τ, ⟨(b, a), hab⟩⟩ := by
    simp only [upM, upU, Matrix.of_apply, dif_pos hab']
  rw [e] at h2
  exact mem_O_ratOf.1 h2

end GlobalTheory.FlagCell2
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCellDens

theorem telesc (s : ℕ) (Δ : ℕ → ℝ) (h0 : Δ 0 = 1) (hp : ∀ k, k ≤ s → Δ k ≠ 0) :
    ∏ i ∈ Finset.range s, (Δ (i + 1) / Δ i) ^ (s - i) = ∏ i ∈ Finset.range s, Δ (i + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih' := ih fun k hk => hp k (by omega)
    have e1 : ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) ^ (s + 1 - i) =
        (∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) ^ (s - i)) *
          ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show s + 1 - i = (s - i) + 1 by omega, pow_succ]
    have e2 : ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) = Δ (s + 1) := by
      rw [Finset.prod_div_distrib]
      have a1 := Finset.prod_range_succ' Δ (s + 1)
      have a2 := Finset.prod_range_succ Δ (s + 1)
      have hne : ∏ i ∈ Finset.range (s + 1), Δ i ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i hi => hp i (by rw [Finset.mem_range] at hi; omega)
      rw [h0, mul_one] at a1
      rw [a1] at a2
      field_simp
      linarith [a2]
    rw [e1, e2, Finset.prod_range_succ, ih', Nat.sub_self, pow_zero, mul_one, Finset.prod_range_succ]

theorem key (s : ℕ) (Δ : ℕ → ℝ) (h0 : Δ 0 = 1) (hp : ∀ k, k ≤ s → 0 < Δ k) :
    ∏ i : Fin s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) =
      Δ s ^ ((s : ℤ) - 1) * ∏ i : Fin s, Δ i ^ (-2 : ℤ) := by
  have hne : ∀ k, k ≤ s → Δ k ≠ 0 := fun k hk => (hp k hk).ne'
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) s,
    Fin.prod_univ_eq_prod_range (fun i : ℕ => Δ i ^ (-2 : ℤ)) s]
  have e1 : ∏ i ∈ Finset.range s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) =
      ∏ i ∈ Finset.range s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ (s - i)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show s - 1 - i + 1 = s - i by omega]
  rw [e1, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    telesc s Δ h0 hne, Finset.prod_zpow]
  have a1 := Finset.prod_range_succ' Δ s
  have a2 := Finset.prod_range_succ Δ s
  rw [h0, mul_one] at a1
  rw [a1] at a2
  rw [a2]
  have hP : ∏ i ∈ Finset.range s, Δ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => hne i (by rw [Finset.mem_range] at hi; omega)
  have hs := hne s le_rfl
  rw [zpow_sub₀ hs, zpow_natCast, zpow_one, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
  field_simp

end GlobalTheory.FlagCellDens

namespace GlobalTheory.FlagCellDens

theorem leadMinor_pos {s : ℕ} {M : Matrix (Fin s) (Fin s) ℂ} (hM : M.PosDef) (k : ℕ) :
    0 < (leadMinor M k).re ∧ (leadMinor M k).im = 0 := by
  have h := (hM.submatrix (e := (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)) Subtype.val_injective).det_pos
  have := Complex.pos_iff.1 h
  exact ⟨this.1, this.2.symm⟩

theorem leadMinor_self {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) : leadMinor M s = M.det := by
  have := Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin s => (a : ℕ) < s)
    fun a => a.2) M
  exact this

def lowEquiv {s k : ℕ} (hk : k ≤ s) : Fin k ≃ {a : Fin s // (a : ℕ) < k} where
  toFun j := ⟨Fin.castLE hk j, j.2⟩
  invFun a := ⟨a.1.1, a.2⟩
  left_inv j := rfl
  right_inv a := rfl

theorem lminor_transpose {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i : Fin (s + 1)) :
    ReciprocityTheory.ChartRestriction.G.FD.lminor Mᵀ i = leadMinor M i := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor leadMinor
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have := Matrix.det_submatrix_equiv_self (lowEquiv (Nat.le_of_lt_succ i.isLt))
    (M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < i} → Fin s) Subtype.val)
  rw [← this, Matrix.submatrix_submatrix]
  rfl

end GlobalTheory.FlagCellDens


open GlobalTheory.FlagCellDens in
theorem GlobalTheory.FlagCellDens.main : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ), ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ) * (G.det.re / (leadMinor (upU y * G * (upU y)ᴴ) i).re / grD (upU y * G * (upU y)ᴴ) i ^ ((s - 1 - i : ℕ) + 1))) = GlobalTheory.TrueCx.flagConst s * G.det.re ^ ((s : ℤ) - 1) * GlobalTheory.FlagFibre.dens Gᵀ y := by
  intro s G hG y
  set M := upU y * G * (upU y)ᴴ with hMdef
  have hU : (upU y).det = 1 := by rw [upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  have hM : M.PosDef := hG.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [hU]; exact isUnit_one)))
  have hdet : M.det = G.det := by
    rw [hMdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hU]; simp
  have hT : (GlobalTheory.FlagFibre.uni y)ᴴ * Gᵀ * GlobalTheory.FlagFibre.uni y = Mᵀ := by
    rw [hMdef, upU_eq]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    congr 1
  set Δ : ℕ → ℝ := fun k => (leadMinor M k).re with hΔ
  have hGs : G.det.re = Δ s := by rw [hΔ]; simp only [leadMinor_self, hdet]
  have hnorm : ∀ i : Fin s, ‖ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni y)ᴴ * Gᵀ * GlobalTheory.FlagFibre.uni y) i.castSucc‖ = Δ i := by
    intro i
    rw [hT, lminor_transpose]
    obtain ⟨h1, h2⟩ := leadMinor_pos hM i
    have : leadMinor M (i.castSucc : ℕ) = ((leadMinor M i).re : ℂ) := Complex.ext (by simp) (by simp [h2])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
  have h0 : Δ 0 = 1 := by
    simp only [hΔ, leadMinor]
    haveI : IsEmpty {a : Fin s // (a : ℕ) < 0} := ⟨fun a => Nat.not_lt_zero _ a.2⟩
    rw [Matrix.det_isEmpty]; simp
  have hp : ∀ k, k ≤ s → 0 < Δ k := fun k _ => (leadMinor_pos hM k).1
  rw [Finset.prod_mul_distrib, GlobalTheory.FlagFibre.dens]
  simp only [hnorm]
  have hc : ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ)) = GlobalTheory.TrueCx.flagConst s := by
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ))) s,
      Finset.prod_range_reflect (fun i : ℕ => ((i.factorial : ℝ) / Real.pi ^ i)) s]
    rfl
  rw [hc, mul_assoc]
  congr 1
  rw [hGs]
  exact key s Δ h0 hp
end

section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

theorem _root_.GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → IsAlgebraic ℚ β → |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree = |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  first | exact @GlobalTheory.NormTower.abs_norm_coeff_zero_pow | exact GlobalTheory.NormTower.abs_norm_coeff_zero_pow | (intros; apply GlobalTheory.NormTower.abs_norm_coeff_zero_pow <;> assumption)
end
