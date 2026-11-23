module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace InvGrp

variable {k r : ℕ}

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM; fun_prop

theorem map_invol_eq (HU : HaarUnique) {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn U μ) (f : Mt k r → Mt k r) (hf : Continuous f) (hff : ∀ x, f (f x) = x)
    (hfU : ∀ x : Mt k r, (x : Mat k r) ∈ U → (f x : Mat k r) ∈ U)
    (hl : ∀ a ∈ U, ∃ b ∈ U, ∀ x, lmulM a (f x) = f (lmulM b x)) : μ.map f = μ := by
  have hfm : Measurable f := hf.measurable
  have hUc : IsClosed (show Set (Mt k r) from U) := hU.closed
  have hUm : MeasurableSet (show Set (Mt k r) from U) := hUc.measurableSet
  have h1 : (μ.map f) Uᶜ = 0 := by
    rw [Measure.map_apply hfm hUm.compl]
    refine measure_mono_null (fun x hx => ?_) hμ.conc
    intro hxU
    exact hx (hfU x hxU)
  have h2 : ∀ a ∈ U, (μ.map f).map (lmulM a) = μ.map f := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hl a ha
    rw [Measure.map_map (continuous_lmulM a).measurable hfm]
    have : lmulM a ∘ f = f ∘ lmulM b := funext hab
    rw [this, ← Measure.map_map hfm (continuous_lmulM b).measurable, hμ.left b hb]
  have h3 : ∀ K : Set (Mt k r), IsCompact K → (μ.map f) K < ∞ := by
    intro K hK
    rw [Measure.map_apply hfm hK.measurableSet]
    have : f ⁻¹' K = f '' K := by
      ext x; constructor
      · intro hx; exact ⟨f x, hx, hff x⟩
      · rintro ⟨y, hy, rfl⟩; show f (f y) ∈ K; rw [hff]; exact hy
    rw [this]
    exact hμ.finite_compact _ (hK.image hf)
  obtain ⟨c, hc⟩ := HU k r U μ (μ.map f) hU hμ h1 h2 h3
  have hff' : f ∘ f = id := funext hff
  have hback : (μ.map f).map f = μ := by
    rw [Measure.map_map hfm hfm, hff', Measure.map_id]
  have hcc : (c * c) • μ = μ := by
    conv_rhs => rw [← hback]
    rw [hc, Measure.map_smul c hfm.aemeasurable, hc, smul_smul]

  obtain ⟨K, hK, hK0⟩ : ∃ K : Set (Mt k r), IsCompact K ∧ μ K ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hμ.ne_zero
    have : μ Set.univ = 0 := by
      rw [← Metric.iUnion_closedBall_nat (0 : Mt k r)]
      exact measure_iUnion_null fun n => hcon _ (isCompact_closedBall _ _)
    exact Measure.measure_univ_eq_zero.mp this
  have hKt : μ K ≠ ∞ := (hμ.finite_compact K hK).ne
  have hval : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    have := congrArg (fun ν : Measure (Mt k r) => ν K) hcc
    simpa using this
  have hc1 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp hval
  have hc2 : (c : ℝ) * c = 1 := by
    have : c * c = 1 := by exact_mod_cast hc1
    exact_mod_cast this
  have hcpos : (0 : ℝ) ≤ c := c.2
  have hc3 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [hc, hc3, one_smul]

end InvGrp

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.HaarSigmaFiniteUniqueness

section Grp

variable {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G] [MeasurableInv G]

theorem eq_smul_of_sigmaFinite (μ ν : Measure G) [SigmaFinite μ] [SigmaFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • ν := by
  obtain ⟨n, hn⟩ : ∃ n, ν (spanningSets (μ + ν) n) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hν
    have : ν Set.univ = 0 := by
      rw [← iUnion_spanningSets (μ + ν)]
      exact measure_iUnion_null h
    exact Measure.measure_univ_eq_zero.mp this
  have hS := measurableSet_spanningSets (μ + ν) n
  have hfin := measure_spanningSets_lt_top (μ + ν) n
  rw [Measure.add_apply] at hfin
  have hνf : ν (spanningSets (μ + ν) n) ≠ ∞ := (lt_of_le_of_lt le_add_self hfin).ne
  have hμf : μ (spanningSets (μ + ν) n) ≠ ∞ := (lt_of_le_of_lt le_self_add hfin).ne
  have heq : μ = (μ (spanningSets (μ + ν) n) / ν (spanningSets (μ + ν) n)) • ν := by
    first
    | exact measure_eq_div_smul μ ν (spanningSets (μ + ν) n) hn hνf
    | exact measure_eq_div_smul μ ν hS hn hνf
    | exact measure_eq_div_smul μ ν (spanningSets (μ + ν) n) hS hn hνf
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hn hνf ht
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hn hνf
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hS ht hn hνf
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
  have hμ0 : μ (spanningSets (μ + ν) n) ≠ 0 := by
    intro h0
    apply hμ
    rw [heq, h0, ENNReal.zero_div, zero_smul]
  refine ⟨(μ (spanningSets (μ + ν) n) / ν (spanningSets (μ + ν) n)).toNNReal, ?_, ?_⟩
  · intro h
    rw [ENNReal.toNNReal_eq_zero_iff, ENNReal.div_eq_zero_iff] at h
    rcases h with (h | h) | h
    · exact hμ0 h
    · exact hνf h
    · exact ENNReal.div_ne_top hμf hn h
  · rw [ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.div_ne_top hμf hn)]
    exact heq

end Grp

section Mat

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def Aset (U : Set (Mat k r)) : Set (Mt k r) := {x | Matrix.of x ∈ U}

variable {U : Set (Mat k r)}

private theorem continuous_matrix_of_Mt : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) :=
  continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))

theorem isClosed_Aset (hU : IsClosedSubgroup U) : IsClosed (Aset U) := by
  exact hU.closed.preimage continuous_matrix_of_Mt

theorem measurableSet_Aset (hU : IsClosedSubgroup U) : MeasurableSet (Aset U) := by
  exact (isClosed_Aset hU).measurableSet

def toM (a : Aset U) : Mat k r := Matrix.of a.1

theorem toM_inj {a b : Aset U} (h : toM a = toM b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

variable [hU : Fact (IsClosedSubgroup U)]

instance : Mul (Aset U) := ⟨fun a b => ⟨(toM a * toM b : Mat k r), hU.out.mul_mem _ a.2 _ b.2⟩⟩
instance : One (Aset U) := ⟨⟨(1 : Mat k r), hU.out.one_mem⟩⟩
instance : Inv (Aset U) := ⟨fun a => ⟨((toM a)⁻¹ : Mat k r), hU.out.inv_mem _ a.2⟩⟩

theorem toM_mul (a b : Aset U) : toM (a * b) = toM a * toM b := rfl
theorem toM_one : toM (1 : Aset U) = 1 := rfl
theorem toM_inv (a : Aset U) : toM a⁻¹ = (toM a)⁻¹ := rfl

instance : Group (Aset U) where
  mul_assoc a b c := toM_inj (by simp only [toM_mul]; exact Matrix.mul_assoc _ _ _)
  one_mul a := toM_inj (by simp only [toM_mul, toM_one]; exact Matrix.one_mul _)
  mul_one a := toM_inj (by simp only [toM_mul, toM_one]; exact Matrix.mul_one _)
  inv_mul_cancel a := toM_inj (by
    simp only [toM_mul, toM_one, toM_inv]
    exact Matrix.nonsing_inv_mul _ (hU.out.unit _ a.2))

theorem continuous_toM : Continuous (toM : Aset U → Mat k r) := by
  exact continuous_matrix_of_Mt.comp continuous_subtype_val

theorem continuous_mulA : Continuous fun p : Aset U × Aset U => p.1 * p.2 := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun p : Aset U × Aset U => (toM p.1 * toM p.2 : Mat k r)
  exact (continuous_toM.comp continuous_fst).mul (continuous_toM.comp continuous_snd)

theorem continuous_invA : Continuous fun a : Aset U => a⁻¹ := by
  refine Continuous.subtype_mk ?_ _
  have h : (fun a : Aset U => (toM a)⁻¹) = fun a => (toM a).det⁻¹ • (toM a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  show Continuous fun a : Aset U => ((toM a)⁻¹ : Mat k r)
  rw [h]
  exact ((continuous_toM.matrix_det).inv₀ fun a => (hU.out.unit _ a.2).ne_zero).smul continuous_toM.matrix_adjugate

instance : MeasurableMul₂ (Aset U) := ⟨continuous_mulA.measurable⟩
instance : MeasurableInv (Aset U) := ⟨continuous_invA.measurable⟩

end Mat

section Transfer

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {U : Set (Mat k r)} [hU : Fact (IsClosedSubgroup U)]

theorem mEmb : MeasurableEmbedding (Subtype.val : Aset U → Mt k r) := by
  exact MeasurableEmbedding.subtype_coe (measurableSet_Aset hU.out)

theorem map_comap_val (μ : Measure (Mt k r)) (hc : μ (Aset U)ᶜ = 0) :
    (μ.comap (Subtype.val : Aset U → Mt k r)).map Subtype.val = μ := by
  rw [(mEmb (U := U)).map_comap μ]
  first | rw [Subtype.range_coe] | rw [Subtype.range_val] | skip
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hc)

theorem sigmaFinite_comap (μ : Measure (Mt k r)) [SigmaFinite μ] :
    SigmaFinite (μ.comap (Subtype.val : Aset U → Mt k r)) := by
  refine SigmaFinite.of_map _ (mEmb (U := U)).measurable.aemeasurable ?_
  rw [(mEmb (U := U)).map_comap μ]
  infer_instance

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  exact (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (a * Matrix.of x : Mat k r))

theorem isMulLeftInvariant_comap (μ : Measure (Mt k r)) (hc : μ (Aset U)ᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (lmulM a) = μ) :
    (μ.comap (Subtype.val : Aset U → Mt k r)).IsMulLeftInvariant := by
  constructor
  intro g
  have hm : Measurable (fun x : Aset U => g * x) := by
    refine Measurable.subtype_mk ?_
    exact (continuous_lmulM (toM g)).measurable.comp measurable_subtype_coe
  have hval : Subtype.val ∘ (fun x : Aset U => g * x) = lmulM (toM g) ∘ Subtype.val := rfl
  have hmap : ((μ.comap (Subtype.val : Aset U → Mt k r)).map (fun x : Aset U => g * x)).map Subtype.val
      = (μ.comap (Subtype.val : Aset U → Mt k r)).map Subtype.val := by
    rw [Measure.map_map (mEmb (U := U)).measurable hm, hval,
      ← Measure.map_map (continuous_lmulM (toM g)).measurable (mEmb (U := U)).measurable,
      map_comap_val μ hc, hl (toM g) g.2]
  ext s hs
  have h1 := congrArg (fun m : Measure (Mt k r) => m (Subtype.val '' s)) hmap
  rwa [(mEmb (U := U)).map_apply, (mEmb (U := U)).map_apply,
    Set.preimage_image_eq _ Subtype.val_injective] at h1

end Transfer

end ReciprocityTheory.ChartRestriction.DS.Mult1.HaarSigmaFiniteUniqueness

end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

structure SigData (k r : ℕ) where
  Hs : Type
  [hN : NormedAddCommGroup Hs]
  [hI : InnerProductSpace ℂ Hs]
  [hC : CompleteSpace Hs]
  σ : Mat k r → (Hs →L[ℂ] Hs)
  rep : Formalism.MainNotions.S.IsURepOn (GV k r) σ
  irr : Formalism.MainNotions.S.IsIrredOn (GV k r) σ
  w : Hs
  w_norm : ‖w‖ = 1
  a : ℝ
  Cw : ℝ
  dec : ∀ x ∈ GV k r, ‖⟪w, σ x w⟫_ℂ‖ ≤ Cw * gN x ^ (-a)

attribute [instance] SigData.hN SigData.hI SigData.hC

variable {k r : ℕ}

def nR (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def aM (k r : ℕ) : ℝ := 4 * nR k r ^ 3

def AG (k r : ℕ) : ℝ := nR k r ^ 2

def AS (k r : ℕ) : ℝ := nR k r ^ 3

def mc (X : SigData k r) (u v : X.Hs) (g : Mat k r) : ℂ := ⟪v, X.σ g u⟫_ℂ

def VflA (X : SigData k r) (b : ℝ) : Set X.Hs :=
  {u | ∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u X.w x‖ ≤ C * gN x ^ (-b)}

def Vfl (X : SigData k r) : Set X.Hs := VflA X X.a

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

structure IsDiag (D : RealPlaceData k r Wp Wp) : Prop where
  z_eq : D.z' = D.z
  π_eq : D.π' = D.π
  μW_eq : D.μW' = D.μW
  mass : D.μW Set.univ = 1
  irr : Formalism.MainNotions.S.IsIrredOn (UWset k r D.z) D.π

def psiD (D : RealPlaceData k r Wp Wq) (m : Mat k r) : ℂ := psi k r D.z cStd m

def SqIntG (D : RealPlaceData k r Wp Wq) (X : SigData k r) : Prop :=
  ∀ v w : X.Hs, MemLp (fun g : Mt k r => mc X v w (Matrix.of g)) 2 D.μG

def IsFdegG (D : RealPlaceData k r Wp Wq) (X : SigData k r) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : X.Hs,
    Integrable (fun g : Mt k r => mc X v w (Matrix.of g) * star (mc X v' w' (Matrix.of g))) D.μG ∧
    ∫ g : Mt k r, mc X v w (Matrix.of g) * star (mc X v' w' (Matrix.of g)) ∂D.μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def beInt (D : RealPlaceData k r Wp Wq) (X : SigData k r) (u u' : X.Hs) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (mc X u u' (Matrix.of p.2 * Matrix.of p.1) * star (psiD D (Matrix.of p.2))) • D.π (Matrix.of p.1)⁻¹

def beOp (D : RealPlaceData k r Wp Wq) (X : SigData k r) (u u' : X.Hs) : Wp →L[ℂ] Wp :=
  ∫ p, beInt D X u u' p ∂(D.μW.prod D.μN)

def rk1 (a b : Wp) : Wp →L[ℂ] Wp := (innerSL ℂ b).smulRight a

def IsSMapOn (D : RealPlaceData k r Wp Wq) (X : SigData k r) (E : Set X.Hs) (l : X.Hs → Wp) : Prop :=
  (∀ u ∈ E, ∀ v ∈ E, l (u + v) = l u + l v) ∧ (∀ (c : ℂ), ∀ u ∈ E, l (c • u) = c • l u) ∧
    ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ u ∈ E, l (X.σ (m * h) u) = psiD D m • D.π h (l u)

def IsMultOneMap (D : RealPlaceData k r Wp Wq) (X : SigData k r) (l : X.Hs → Wp) : Prop :=
  IsSMapOn D X (Vfl X) l ∧ ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, beOp D X u u' = rk1 (l u) (l u')

def IsTestG (φ : Mat k r → ℂ) : Prop :=
  CkOn ⊤ (GV k r) φ ∧ ∃ K : Set (Mat k r), IsCompact K ∧ ∀ g ∈ GV k r, g ∉ K → φ g = 0

def sigInt (D : RealPlaceData k r Wp Wq) (X : SigData k r) (φ : Mat k r → ℂ) (v : X.Hs) : X.Hs :=
  ∫ g : Mt k r, φ (Matrix.of g) • X.σ (Matrix.of g) v ∂D.μG

def DDinf (D : RealPlaceData k r Wp Wq) (X : SigData k r) : Set X.Hs :=
  {v | ∃ φ, IsTestG φ ∧ v = sigInt D X φ X.w}

def IsZFrame (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  γᴴ * Hb k * γ = Hb k ∧
    embWb k r γ *ᵥ bvec (wI k r (Fin.last k)) = (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z

def gbar (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (g : Mat k r) : Mat k r :=
  embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) * (embWb k r γ)⁻¹

def th (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (g : Mat k r) : Mat k r := (gbar k r γ g)⁻¹

def w1 (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ :=
  embWb k r γ *ᵥ bvec (wI k r 0)

def UUset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Set (Mat k r) :=
  {u | u ∈ UWset k r z ∧ u *ᵥ w1 k r γ = w1 k r γ}

def mud (k : ℕ) (d : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  if i = 0 ∧ j = 0 then -(starRingEnd ℂ d)
  else if i = Fin.last k ∧ j = 0 then -((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)
  else if i = 0 ∧ j = Fin.last k then ((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)
  else if i = Fin.last k ∧ j = Fin.last k then d
  else if i = j then 1 else 0

def g0 (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (c : Fin r → ℂ) (d : ℂ) : Mat k r :=
  bigCell k r c (γ * mud k d * γ⁻¹)

def scalF (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (f : Mat k r → ℂ) :
    Mat k r → (Wp →L[ℂ] Wp) := fun g => f g • ContinuousLinearMap.id ℂ Wp

def Ef (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (q : (Fin r → ℂ) × ℂ) : ℝ≥0∞ :=
  ∫⁻ p, ‖rho D p F (gq D q)‖ₑ ∂D.μSS

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
