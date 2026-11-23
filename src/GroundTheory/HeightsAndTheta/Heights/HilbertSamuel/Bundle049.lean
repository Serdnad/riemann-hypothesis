module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import Mathlib.Topology.Sheaves.Presheaf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle040
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

namespace ChartConstantsDetermined

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_chart_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = eval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  have h := MvPolynomial.ringHom_ext
    (f := (aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω).toRingHom)
    (g := (eval (fun k => (y ⟨k, c k⟩)⁻¹)).comp (mConeMap y).toRingHom)
    (fun r => by simp) (fun p => by simp [mConeMap, div_eq_mul_inv])
  exact RingHom.congr_fun h f

theorem aeval_chart_of_isMultiHomog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [aeval_chart_eq, ProjLine.mConeMap_eq_of_isMultiHomog y hf]
  simp only [map_mul, eval_C, map_prod, map_pow, eval_X]

theorem aeval_chart_eq_zero (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = 0 := by
  rw [aeval_chart_eq, show mConeMap y f = 0 from RingHom.mem_ker.mp hf, map_zero]

variable (F : Type) [Field F] [NumberField F] [Algebra F Ω]

def chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : ↥(chartRingZ y c ⊔ intsIn F Ω) :=
  ⟨y p / y ⟨p.1, c p.1⟩, le_sup_left (a := chartRingZ y c) (Algebra.subset_adjoin (Set.mem_range_self p))⟩

variable {F}

def pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : (Σ k, ι k) → ℂ :=
  fun p => w (chartCoord F y c p)

theorem coe_aeval_chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    ((aeval (chartCoord F y c) f : ↥(chartRingZ y c ⊔ intsIn F Ω)) : Ω) =
      aeval (fun p => y p / y ⟨p.1, c p.1⟩) f := by
  show (Subalgebra.val _) (aeval (chartCoord F y c) f) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem eval_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ)
    (f : MRing ι) :
    eval (pointOf y c w) (map (Int.castRingHom ℂ) f) = w (aeval (chartCoord F y c) f) := by
  rw [eval_map]
  have h := MvPolynomial.ringHom_ext (f := eval₂Hom (Int.castRingHom ℂ) (pointOf y c w))
    (g := w.comp (aeval (chartCoord F y c) : MRing ι →ₐ[ℤ] _).toRingHom)
    (fun r => by simp) (fun p => by simp [pointOf])
  exact RingHom.congr_fun h f

theorem pointOf_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : pointOf y c w ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : chartCoord F y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [chartCoord, hc k])
    simp [pointOf, h1]
  · rw [eval_pointOf]
    have h0 : aeval (chartCoord F y c) f = 0 :=
      Subtype.ext (by rw [coe_aeval_chartCoord]; simpa using aeval_chart_eq_zero y c hf)
    simp [h0]

def intsMap {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : 𝓞 F →+* ℂ :=
  w.comp ((Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom.comp
    (((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict).toRingHom)

theorem intsMap_apply {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) (a : 𝓞 F) :
    intsMap w a = w ⟨algebraMap F Ω (algebraMap (𝓞 F) F a),
      le_sup_right (a := chartRingZ y c) (AlgHom.mem_range_self _ a)⟩ := rfl

theorem intsMap_injective {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    Function.Injective (intsMap w) := by
  refine (RingHom.injective_iff_ker_eq_bot _).mpr (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  refine eq_bot_iff.2 fun n hn => ?_
  rw [Ideal.mem_bot]
  simpa [Ideal.mem_comap, RingHom.mem_ker] using hn

theorem liesOver_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    LiesOver y (IsFractionRing.lift (K := F) (intsMap_injective w)) (pointOf y c w) := by
  intro d g h θ hg hh hrel
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) θ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hψb : intsMap w b ≠ 0 := (map_ne_zero_iff _ (intsMap_injective w)).mpr hb0
  have hB : algebraMap F Ω (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap, eval_pointOf, eval_pointOf,
    div_mul_eq_mul_div, eq_div_iff hψb, intsMap_apply, intsMap_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, coe_aeval_chartCoord]
  rw [aeval_chart_of_isMultiHomog y c hg, aeval_chart_of_isMultiHomog y c hh, hrel, map_div₀]
  field_simp

theorem proof : Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hU c hc w w' hw
  have hz : pointOf y c w = pointOf y c w' := funext fun p =>
    RingHom.congr_fun hw ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin (Set.mem_range_self p)⟩
  obtain ⟨sg, -, huniq⟩ := hU _ (pointOf_mem y c hc w)
  have e1 := huniq _ (liesOver_pointOf y c w)
  have e2 := huniq (IsFractionRing.lift (K := F) (intsMap_injective w'))
    (by rw [hz]; exact liesOver_pointOf y c w')
  ext x
  rcases x with ⟨_, a, rfl⟩
  show intsMap w a = intsMap w' a
  rw [← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w) a,
    ← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w') a, e1, e2]

end ChartConstantsDetermined

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem EmbeddingPieces.proof (hA : PiecesAdditive.Statement) (hD : PieceDegree.Statement) :
    EmbeddingPieces.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D L c w hP hbir hL hex hw
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg => EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hind : ∀ (d : (F →+* ℂ) → ℝ), ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg, LiesOver y sg z →
      ∑ s, d s * (S s).indicator (fun _ => (1 : ℝ)) z = d sg := by
    intro d z hz sg hsg
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  have hwL : ptsIntegral (mCoordIdeal y) (pot L) w = ptsIntegral (mCoordIdeal y) (pot L)
      (fun z => ∑ s, c s * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    rw [hind c z hz sg hsg]
    exact (hw z hz sg hsg).self_of_nhds
  have h1 : ptsIntegral (mCoordIdeal y) (pot L) (fun _ => 1) = ptsIntegral (mCoordIdeal y) (pot L)
      (fun z => ∑ s, (fun _ => (1 : ℝ)) s * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    rw [hind _ z hz sg hsg]
  rw [hwL, h1, hA K ι _ D L (F →+* ℂ) S c hP hL hSc hSs hex',
    hA K ι _ D L (F →+* ℂ) S (fun _ => 1) hP hL hSc hSs hex']
  rcases isEmpty_or_nonempty (F →+* ℂ) with he | ⟨⟨s0⟩⟩
  · simp [Finset.univ_eq_empty]
  · have hI : ∀ s, ptsIntegral (mCoordIdeal y) (pot L) ((S s).indicator fun _ => (1 : ℝ)) =
        ptsIntegral (mCoordIdeal y) (pot L) ((S s0).indicator fun _ => (1 : ℝ)) :=
      fun s => hD K ι Ω F y D L s s0 hP hbir hL hex
    simp only [hI, ← Finset.sum_mul, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (F →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenerationOfH1GenAmple

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chartExp (c : ∀ k, ι k) (n : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then n q.1 else 0

def chartMon (c : ∀ k, ι k) (n : K → ℕ) : MRingOver S ι :=
  monomial (chartExp c n) 1

theorem chartMon_homog (c : ∀ k, ι k) (n : K → ℕ) : IsMultiHomog (chartMon (S := S) c n) n :=
  GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => by simp [chartExp]

theorem chartMon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (n : K → ℕ) :
    chartMon (S := S) c n ∈ KH.cellMon S I := by
  unfold chartMon
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  have hq' : q.2 = c q.1 := by
    by_contra h
    simp [chartExp, h] at hq
  obtain ⟨k, i⟩ := q
  simp only at hq'
  subst hq'
  exact ⟨k, c k, hc k, rfl⟩

variable {V : Ideal (MRingOver S ι)}

theorem smul_quot (f : MRingOver S ι) (m : MRingOver S ι ⧸ V) : f • m = Ideal.Quotient.mk V f * m := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
  rfl

theorem smul_mul_eq_mul_smul {T : Submonoid (MRingOver S ι)} (p : MRingOver S ι)
    (x y : LocalizedModule T (MRingOver S ι ⧸ V)) : (p • x) * y = x * (p • y) := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.smul'_mk,
        LocalizedModule.mk_mul_mk, smul_mul_assoc, mul_smul_comm]

theorem generatedV_of_generatedMod {d : K → ℤ} (h : GeneratedMod S ι (KH.quotPart S V) d) :
    KH.GeneratedV S V d := by
  classical
  intro I
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  let dp : K → ℕ := fun k => (d k).toNat
  let dm : K → ℕ := fun k => (-d k).toNat
  have hd : ∀ k, (dp k : ℤ) - dm k = d k := fun k => Int.toNat_sub_toNat_neg (d k)
  let P : MRingOver S ι := chartMon c dp
  let Q : MRingOver S ι := chartMon c dm
  have hP : P ∈ KH.cellMon S I.1 := chartMon_mem hc dp
  have hQ : Q ∈ KH.cellMon S I.1 := chartMon_mem hc dm
  have hpart : ∀ (f : MRingOver S ι) (a : K → ℕ), IsMultiHomog f a →
      Ideal.Quotient.mk V f ∈ KH.quotPart S V (fun k => (a k : ℤ)) := fun f a hf =>
    Submodule.subset_span ⟨f, ⟨fun k => Int.natCast_nonneg _, by simpa using hf⟩, rfl⟩
  let x : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V P) ⟨Q, hQ⟩
  have hx : x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) d := by
    refine GenTwistGenerated.mk_mem_locPart _ _ dm (chartMon_homog c dm) ?_
    have e : (d + fun k => (dm k : ℤ)) = fun k => (dp k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply]
      omega
    rw [e]
    exact hpart P dp (chartMon_homog c dp)
  obtain ⟨t, a, r, p, z, ht, hta, hpa, hz, htx⟩ := h I x hx
  let w : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V Q) ⟨t * P, mul_mem ht hP⟩
  refine ⟨r, z, fun j => p j • w, hz, fun j => ?_, ?_⟩
  · have e0 : p j • Ideal.Quotient.mk V Q = Ideal.Quotient.mk V (p j * Q) := by
      rw [smul_quot, map_mul]
    have e1 : p j • w =
        LocalizedModule.mk (Ideal.Quotient.mk V (p j * Q)) ⟨t * P, mul_mem ht hP⟩ :=
      (LocalizedModule.smul'_mk ..).trans (congrArg (fun m => LocalizedModule.mk m _) e0)
    refine (congrArg (· ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-d)) e1).mpr ?_
    refine GenTwistGenerated.mk_mem_locPart _ _ (a + dp)
      (GenTwistGenerated.isMultiHomog_mul hta (chartMon_homog c dp)) ?_
    have e2 : (-d + fun k => ((a + dp) k : ℤ)) = fun k => ((a + dm) k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply, Pi.neg_apply, Nat.cast_add]
      omega
    rw [e2]
    exact hpart _ _ (GenTwistGenerated.isMultiHomog_mul (hpa j) (chartMon_homog c dm))
  · calc ∑ j, p j • w * z j I = ∑ j, w * (p j • z j I) :=
          Finset.sum_congr rfl fun j _ => smul_mul_eq_mul_smul (p j) w (z j I)
      _ = w * (t • x) := by rw [← Finset.mul_sum, htx]
      _ = 1 := by
        have e3 : Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P) =
            ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V)) := by
          rw [Submonoid.smul_def, smul_quot, smul_quot, mul_one]
          simp only [Submonoid.coe_mul, map_mul]
          ring
        calc w * (t • x)
            = w * LocalizedModule.mk (t • Ideal.Quotient.mk V P) ⟨Q, hQ⟩ :=
              congrArg (w * ·) (LocalizedModule.smul'_mk ..)
          _ = LocalizedModule.mk (Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P))
                (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) := LocalizedModule.mk_mul_mk
          _ = LocalizedModule.mk ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) •
                (1 : MRingOver S ι ⧸ V)) (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) :=
              congrArg (fun m => LocalizedModule.mk m _) e3
          _ = LocalizedModule.mk 1 1 := LocalizedModule.mk_cancel _ _
          _ = 1 := OreLocalization.one_def.symm

end GenerationOfH1GenAmple

theorem GenerationOfH1GenAmple.proof (hQ : QuotPartGraded.Statement) : GenerationOfH1GenAmple.Statement := by
  intro S _ K _ _ ι _ _ V N hV hH e
  have hann : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ V) := fun v hv =>
    Module.mem_annihilator.mpr fun m => by
      rw [GenerationOfH1GenAmple.smul_quot, Ideal.Quotient.eq_zero_iff_mem.mpr hv, zero_mul]
  obtain ⟨c₁, hc₁⟩ := hH (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance (hQ S K ι V hV) hann e
  exact ⟨c₁, fun c hc => GenerationOfH1GenAmple.generatedV_of_generatedMod (hc₁ c hc).2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockStepLocal

theorem nonempty_of_isArithVar {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {x : Ix κ → Ω}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) : Nonempty κ := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : IsEmpty (Σ k : Unit, GlobalTheory κ k) := ⟨fun p => h.false p.2⟩
  have h1 : ringKrullDim (MRing (GlobalTheory κ)) = 1 := by
    rw [ringKrullDim_mvPolynomial_of_isEmpty]
    exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField
  have h2 := ringKrullDim_quotient_le (coordIdeal ℤ x : Ideal (MRing (GlobalTheory κ)))
  rw [hX.2.2.2, h1] at h2
  have h3 : ((D + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by simpa using h2
  have h4 := WithBot.coe_le_coe.1 h3
  norm_cast at h4

theorem choose_div_factorial {D i : ℕ} (hi : i ≤ D) (u : ℝ) :
    (D.choose i : ℝ) * u / (D.factorial : ℝ) = u / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)) := by
  have e : ((D.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((D - i).factorial : ℝ) = (D.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have h0 : (D.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((D - i).factorial : ℝ) ≠ 0 := by positivity
  rw [← e]
  field_simp

end TwoBlockStepLocal


open TwoBlockStepLocal in
theorem TwoBlockStepLocal.proof (hA : TwoBlockPieceCycle.Statement) (hM : TwoBlockCycleExpand.Statement)
    (hR : TwoBlockCoeffCycle.Statement) : TwoBlockStepLocal.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨c⟩ := nonempty_of_isArithVar hX
  obtain ⟨l, hl⟩ : ∃ l : Ix κ → ℤ, x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j := by
    have hc : x ⟨(), c⟩ ∈ Submodule.span ℤ (Set.range (matAct B x)) :=
      hsp (Submodule.subset_span ⟨⟨(), c⟩, rfl⟩)
    obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hc
    exact ⟨l, by rw [← hl]; simp [zsmul_eq_mul]⟩
  obtain ⟨a₀, C, h⟩ := hA D Ω κ x B c l hX hx hB hsp hl
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  convert h a b ha hb using 3
  rw [hM D Ω κ x B c l hX hx hB hsp hl a b, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiD : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [hR D Ω κ I x B m m' c l hI hX hx hB hm hm' hsp hl i hiD,
    show (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i) =
      (D.choose i : ℝ) * ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i)) by ring,
    choose_div_factorial hiD]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem RelLatticeFinite.proof (hL : RelSectionsLarge.Statement) : RelLatticeFinite.Statement := by
  intro K _ ι _ Ω _ y a n m g hy
  have hN : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := adjoin_isNoetherianRing g
  obtain ⟨n₁, hn₁⟩ := hL K ι Ω (Algebra.adjoin ℤ (Set.range g)) hN y hy
  choose c0 hc0 using hy
  set R := Algebra.adjoin ℤ (Set.range g)
  let e : K → ℕ := fun k => n₁ + ((n : ℤ) * a k).natAbs
  let b : K → ℕ := fun k => ((n : ℤ) * a k + e k).toNat
  have hb : ∀ k, ((b k : ℕ) : ℤ) = (n : ℤ) * a k + e k := by
    intro k
    refine Int.toNat_of_nonneg ?_
    simp only [e]
    push_cast
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  have hbn : ∀ k, n₁ ≤ b k := by
    intro k
    have h1 := hb k
    simp only [e] at h1
    push_cast at h1
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  set mon : Ω := ∏ k, y ⟨k, c0 k⟩ ^ e k
  have hmon : mon ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  let φ : Ω →ₗ[R] Ω := LinearMap.mulRight R mon
  have hφ : Function.Injective φ := mul_left_injective₀ hmon
  have hmap : (relChartLat R y a n).map φ ≤ relSecM R y b := by
    rintro _ ⟨s, hs, rfl⟩
    exact hn₁ b hbn (mul_prod_mem_relChartLat R y e c0 (fun k => hb k) hs)
  have : IsNoetherian R (relSecM R y b) := isNoetherian_of_fg_of_noetherian _ (relSecM_fg R y b)
  exact Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le_of_isNoetherian hmap)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
