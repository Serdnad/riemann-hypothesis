module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Determinant
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreReduction

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem idealOver_int (y : (Σ k, ι k) → Ω) : GenOnFibres.idealOver y ℤ = mCoordIdeal y := by
  have h : (MvPolynomial.map (Int.castRingHom ℤ) : MRingOver ℤ ι →+* MRingOver ℤ ι) = RingHom.id _ := by
    refine RingHom.ext fun f => ?_
    rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, map_id]
    rfl
  show Ideal.map _ _ = _
  rw [h, Ideal.map_id]

def redRing (y : (Σ k, ι k) → Ω) (p : ℕ) :
    (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+* (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  Ideal.quotientMap _ (MvPolynomial.map (Int.castRingHom (ZMod p))) (by
    rw [idealOver_int]
    exact Ideal.le_comap_map)

theorem redRing_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (f : MRingOver ℤ ι) :
    redRing y p (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom (ZMod p)) f) :=
  Ideal.quotientMap_mk

theorem redRing_smul (y : (Σ k, ι k) → Ω) (p : ℕ) (r : MRingOver ℤ ι)
    (x : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) :
    redRing y p (r • x) = MvPolynomial.map (Int.castRingHom (ZMod p)) r • redRing y p x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GenOnFibres.smul_mk, redRing_mk, redRing_mk, GenOnFibres.smul_mk, map_mul]

theorem map_mem_cellMon (p : ℕ) {I : ∀ k, Finset (ι k)} {t : MRingOver ℤ ι} (ht : t ∈ KH.cellMon ℤ I) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) t ∈ KH.cellMon (ZMod p) I := by
  unfold KH.cellMon at ht ⊢
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [map_X]
    exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul f g _ _ hf hg => rw [map_mul]; exact mul_mem hf hg

def redLocFun (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)) :
    LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  x.liftOn (fun mt => LocalizedModule.mk (redRing y p mt.1) ⟨_, map_mem_cellMon p mt.2.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine LocalizedModule.mk_eq.mpr ⟨⟨_, map_mem_cellMon p u.2⟩, ?_⟩
    have h := congrArg (redRing y p) hu
    simp only [Submonoid.smul_def, redRing_smul] at h ⊢
    exact h)

theorem redLocFun_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLocFun y p I (LocalizedModule.mk m t) =
      LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ := by
  unfold redLocFun
  exact LocalizedModule.liftOn_mk _ _ _

def redLoc (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k)) :
    LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+
      LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) where
  toFun := redLocFun y p I
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, redLocFun_mk, map_zero, LocalizedModule.zero_mk]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, redLocFun_mk, redLocFun_mk, redLocFun_mk,
        LocalizedModule.mk_add_mk, (redRing y p).map_add]
      simp only [Submonoid.smul_def, redRing_smul]
      congr 1
      exact Subtype.ext (map_mul _ _ _)

theorem redLoc_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLoc y p I (LocalizedModule.mk m t) = LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ :=
  redLocFun_mk y p I m t

def redCoch (y : (Σ k, ι k) → Ω) (p n : ℕ) :
    KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n →+
      KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n :=
  { toFun := fun w I => redLoc y p I.1 (w I)
    map_zero' := funext fun I => map_zero (redLoc y p I.1)
    map_add' := fun w w' => funext fun I => map_add (redLoc y p I.1) (w I) (w' I) }

theorem redCoch_apply (y : (Σ k, ι k) → Ω) (p n : ℕ)
    (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) (I : KH.Cell K ι n) :
    redCoch y p n w I = redLoc y p I.1 (w I) :=
  rfl

end FibreReduction

def ReductionComplex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p (n + 1) (KH.cechD ℤ ι _ n w) =
        KH.cechD (ZMod p) ι _ n (FibreReduction.redCoch y p n w)) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w ∈
        KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n) ∧
    (∀ n : ℕ, ∀ z ∈ KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n,
      ∃ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, FibreReduction.redCoch y p n w = z) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w') ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), (p : ℤ) • w = 0 → w = 0) ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace G1

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (b : Fin n → K → ℤ),
    (∀ j k, 0 ≤ b j k) → 0 ≤ geoNum n V b
  | 0, V, b, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, b, hb => by
    rw [geoNum]
    split_ifs with h
    · refine Finset.sum_nonneg fun k _ => mul_nonneg (hb _ k) ?_
      exact finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W (Fin.init b) fun j k => hb _ k)
    · exact le_rfl

theorem finsum_nonpos' {α : Sort*} {g : α → ℝ} (h : ∀ x, g x ≤ 0) : ∑ᶠ x, g x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -g x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0

theorem mcPts_anti {P W : Ideal (MRing ι)} (h : P ≤ W) : mcPts W ⊆ mcPts P :=
  fun _ hz => ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem exists_monomial_not_mem {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ monomial μ (1 : ℤ) ∉ P := by
  classical
  choose c hc using hP.2.2
  let μ : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  refine ⟨μ, fun k => ?_, ?_⟩
  · simp [μ]
  · intro hmem
    have := hP.1
    rw [monomial_eq, C_1, one_mul, Finsupp.prod] at hmem
    obtain ⟨p, hp, hpP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    have hX := hP.1.mem_of_pow_mem _ hpP
    have hμp : μ p ≠ 0 := Finsupp.mem_support_iff.1 hp
    obtain ⟨k, j⟩ := p
    by_cases hj : j = c k
    · subst hj
      exact hc k hX
    · exact hμp (by simp [μ, hj])

theorem isMultiHomog_monomial {μ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k) :
    IsMultiHomog (monomial μ (1 : ℤ)) a := by
  intro m hm k
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  exact hμ k

theorem eval_monomial_one (μ : (Σ k, ι k) →₀ ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
  rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype]
  intro p
  simp

theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [ContinuousLinearMap.sum_apply, smul_eq_mul] using this

theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 A.h (γ y) :=
    (hsp.1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) := hh.log (A.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (A.h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (A.h z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

theorem arInt_nonpos {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {s : MRing ι}
    (hs : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z) (e : ℕ) :
    arInt P s A (fun _ : Fin e => A) ≤ 0 := by
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (fun (_ : Fin e) z => Real.log (A.h z))
        (logNorm A s) y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        have hpos := A.pos _ hz.1
        have hg : logNorm A s (hγ.choose y) ≤ 0 :=
          Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
            ((div_le_one hpos).2 (hs _ hz))
        exact mul_nonpos_of_nonpos_of_nonneg hg (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos' fun w => finsum_nonpos' fun _ => key w
  · exact le_rfl

theorem nonneg_of_family (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (a : K → ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : A.a = fun k => (a k : ℤ))
    (P0 : Ideal (MRing ι)) (n : ℕ) :
    ∀ P : Ideal (MRing ι), IsArithVar P n → P0 ≤ P → IsSemipositiveRel P0 P A →
      MonomialsBounded P A a → 0 ≤ I P n (fun _ => A) := by
  induction n with
  | zero =>
    intro P hP
    exact (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι P hP).elim
  | succ m ih =>
    intro P hP hP0 hsp hmb
    obtain ⟨μ, hμ, hμP⟩ := exists_monomial_not_mem hP.2.1 a
    set s : MRing ι := monomial μ (1 : ℤ) with hsdef
    have hsa : IsMultiHomog s a := isMultiHomog_monomial hμ
    have hAa : ∀ k, A.a k = a k := fun k => by rw [hA]
    have hsmall : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z := by
      intro z hz
      rw [hsdef, eval_monomial_one]
      exact hmb z hz μ hμ
    have hR := hI.2.2 P m (fun _ => A) A s a hP (fun _ => hsp.1) hsp.1 hAa hsa hμP
    have hconst : (Fin.snoc (fun _ : Fin m => A) A : Fin (m + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = fun _ => A := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [hconst] at hR
    rw [hR, recR]
    refine sub_nonneg.2 (le_trans (arInt_nonpos hP0 hsp hsmall m)
      (finsum_nonneg fun W => finsum_nonneg fun hW => mul_nonneg (Nat.cast_nonneg _) ?_))
    have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
    split_ifs with hH
    · have hWar := (divSuppArith K ι P m A s W hP ⟨a, hAa, hsa, hμP⟩ hW).1 hH
      exact ih W hWar (hP0.trans hPW) ⟨hsp.1, fun z hz w hw => hsp.2 z (mcPts_anti hPW hz) w hw⟩
        (fun z hz μ' hμ' => hmb z (mcPts_anti hPW hz) μ' hμ')
    · refine mul_nonneg (Int.cast_nonneg (geoNum_nonneg m W _ fun j k => ?_))
        (Real.log_natCast_nonneg _)
      simp [hA]

end G1

theorem G1.proof : G1.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II _ hII hP _ hA hP0 hsp hmb _
  exact G1.nonneg_of_family (II K ι) (hII K ι) a A hA P0 (D + 1) _ hP hP0 hsp hmb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiIndex

noncomputable section

open Module

variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem basis_det_eq {N : Type*} [AddCommGroup N] [Module ℤ N] {r : ℕ} (b : Basis (Fin r) ℤ N)
    (A : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → N) (hv : ∀ k, v k = ∑ l, A k l • b l) : b.det v = A.det := by
  classical
  rw [Basis.det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j

  rw [Matrix.transpose_apply, Basis.toMatrix_apply, hv i, map_sum]
  simp only [map_zsmul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem log_relIndex_sub {r : ℕ} {e e' : Fin r → Ω} (he : LinearIndependent ℤ e) (he' : LinearIndependent ℤ e')
    (T : Matrix (Fin r) (Fin r) ℚ) (hT : ∀ k, e' k = ∑ l, (T k l : Ω) * e l) (hdet : T.det ≠ 0) :
    Real.log ((Submodule.span ℤ (Set.range e)).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e')).toAddSubgroup) -
      Real.log ((Submodule.span ℤ (Set.range e')).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e)).toAddSubgroup) =
      -Real.log |(T.det : ℝ)| := by
  classical
  obtain ⟨c, hc0, hc⟩ := ChangeOfLattice.exists_clear_den T
  choose A hA using hc
  set L := Submodule.span ℤ (Set.range e) with hLdef
  set L' := Submodule.span ℤ (Set.range e') with hL'def
  set f : Fin r → Ω := fun k => (c : Ω) * e' k with hfdef
  have hAΩ : ∀ k l, (c : Ω) * (T k l : Ω) = (A k l : Ω) := fun k l => by
    have h := congrArg (fun q : ℚ => (q : Ω)) (hA k l)
    push_cast at h
    exact h
  have hf : ∀ k, f k = ∑ l, A k l • e l := by
    intro k
    simp only [hfdef, hT k, Finset.mul_sum, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, hAΩ]
  have hc0' : (c : Ω) ≠ 0 := by exact_mod_cast hc0
  have hfli : LinearIndependent ℤ f := ChangeOfLattice.linearIndependent_const_mul hc0' he'
  have hfc : ∀ k, f k = ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l • e' l := by
    intro k
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp [hfdef, zsmul_eq_mul]
  set M := Submodule.span ℤ (Set.range f) with hMdef
  have hML : M ≤ L := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hf k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML' : M ≤ L' := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hfc k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML₀ : M.toAddSubgroup ≤ L.toAddSubgroup := hML
  have hML'₀ : M.toAddSubgroup ≤ L'.toAddSubgroup := hML'

  have i1 : M.toAddSubgroup.relIndex L'.toAddSubgroup = (c ^ r : ℕ) := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L'.toAddSubgroup hML'₀ (Basis.span hfli)
      (Basis.span he')]
    refine (congrArg Int.natAbs (basis_det_eq _ ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) _ ?_)).trans ?_
    · intro k
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [AddSubgroupClass.coe_zsmul]
      show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
        ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l •
          ((Basis.span he' l : Submodule.span ℤ (Set.range e')) : Ω)
      simp only [Basis.coe_span_apply]
      exact hfc k
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast]
  have i2 : M.toAddSubgroup.relIndex L.toAddSubgroup = (Matrix.of A).det.natAbs := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L.toAddSubgroup hML₀ (Basis.span hfli)
      (Basis.span he)]
    refine congrArg Int.natAbs (basis_det_eq _ (Matrix.of A) _ fun k => ?_)
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [AddSubgroupClass.coe_zsmul, Matrix.of_apply]
    show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
      ∑ l, A k l • ((Basis.span he l : Submodule.span ℤ (Set.range e)) : Ω)
    simp only [Basis.coe_span_apply]
    exact hf k
  have hAdet : (((Matrix.of A).det : ℤ) : ℝ) = (c : ℝ) ^ r * (T.det : ℝ) := by
    have hmap : (Int.castRingHom ℚ).mapMatrix (Matrix.of A) = (c : ℚ) • T := by
      ext i j
      simp [← hA i j]
    have h1 : (((Matrix.of A).det : ℤ) : ℚ) = (c : ℚ) ^ r * T.det := by
      rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, hmap, Matrix.det_smul, Fintype.card_fin]
    rw [← Rat.cast_intCast, h1, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  have hcr : (c : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc0)
  have hTr : (T.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have h1 : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [i2]
    intro h0
    have : (((Matrix.of A).det : ℤ) : ℝ) = 0 := by
      rw [Int.natAbs_eq_zero.1 h0, Int.cast_zero]
    rw [hAdet] at this
    exact mul_ne_zero hcr hTr this
  have h2 : M.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 := by
    rw [i1]
    exact pow_ne_zero _ hc0
  rw [ChangeOfLattice.log_relIndex_cocycle hML₀ hML'₀ h1 h2, i1, i2, Nat.cast_natAbs, Int.cast_abs, hAdet, Nat.cast_pow]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ r), Real.log_mul hcr (abs_ne_zero.2 hTr)]
  ring

end

end ResChiIndex

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
