module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle122
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralAdeleIdealOfIdealPrincipalAndInter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProductExpChartAllRealPlacesLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothContinuousConvolutionRealPointsUnitary
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.PathVar

theorem uMat_inj {n : ℕ} {ε : Fin n → Bool} {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (s t : ℝ) :
    expU ((s + t) • X) = expU (s • X) * expU (t • X) := by
  apply uMat_inj
  rw [uMat_mul', uMat_expU, uMat_expU, uMat_expU, add_smul, Submodule.coe_add]
  apply Matrix.exp_add_of_commute
  simp only [Submodule.coe_smul]
  exact ((Commute.refl (X : Matrix (Fin n) (Fin n) ℂ)).smul_left s).smul_right t

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : expU ((0 : ℝ) • X) = 1 := by
  apply uMat_inj
  rw [uMat_expU, zero_smul, Submodule.coe_zero, NormedSpace.exp_zero]
  rfl

noncomputable def pt (B : RowsAut) (E : gInf B) (z : B.I.GA) (t : ℝ) : B.I.GA :=
  z * ((fun v => expU (t • E v)), 1)

theorem pt_add (B : RowsAut) (E : gInf B) (z : B.I.GA) (s t : ℝ) :
    pt B E z (s + t) = pt B E z s * ((fun v => expU (t • E v)), 1) := by
  unfold pt
  rw [mul_assoc]
  congr 1
  refine Prod.ext ?_ (by simp)
  funext v
  exact expU_add _ _ _

theorem pt_zero (B : RowsAut) (E : gInf B) (z : B.I.GA) : pt B E z 0 = z := by
  unfold pt
  have : (((fun v => expU ((0 : ℝ) • E v)), 1) : B.I.GA) = 1 := by
    refine Prod.ext ?_ rfl
    funext v
    exact expU_zero _
  rw [this, mul_one]

theorem hasDerivAt_vv (B : RowsAut) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (h : ∀ i, IsReps B (T i) (Fr i)) {P : ℕ} {u : B.Hs} (hu : u ∈ VP B P)
    (E : gInf B) (z : B.I.GA) (s : ℝ) :
    HasDerivAt (fun t => vv B Fr u (pt B E z t)) (vv B Fr (dAct B E u) (pt B E z s)) s := by
  have h1 : ∀ i, HasDerivAt (fun t => Fr i u (pt B E z t)) (Fr i (dAct B E u) (pt B E z s)) s := by
    intro i
    have h0 := (h i P u hu).2.2 E (pt B E z s)
    rw [← sub_self s] at h0
    have h2 := h0.comp_sub_const s s
    simp only [← pt_add, add_sub_cancel] at h2
    exact h2
  have h2 : HasDerivAt (fun t => fun i => Fr i u (pt B E z t)) (fun i => Fr i (dAct B E u) (pt B E z s)) s :=
    hasDerivAt_pi.2 h1
  exact ((EuclideanSpace.equiv (Fin D) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2

theorem hs_smul_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Formalism.REAL.hs (s • X) ≤ Formalism.REAL.hs X := by
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.smul_apply, norm_smul, Real.norm_of_nonneg h0]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg _) h1) 2

theorem pt_mem_omega (B : RowsAut) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (ρ : ℝ)
    (A Z : gInf B)
    (hρ : Real.sqrt (∑ v, Formalism.REAL.hs (A v).1) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v).1) ≤ ρ)
    (hN : ∀ s t : ℝ, ∃ m : B.I.Ginf, ((m, 1) : B.I.GA) ∈ B.I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • (A v).1) * NormedSpace.exp ((t : ℂ) • (Z v).1))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    pt B Z (pt B A x s) t ∈ omega B.I x W ρ := by
  refine ⟨by simp [pt], fun v => (s • A v).1, fun v => (t • Z v).1, fun v => ⟨(s • A v).2, (t • Z v).2⟩, ?_,
    fun v => rfl, fun s' t' => ?_⟩
  · refine le_trans (add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)) hρ
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ hs.1 hs.2
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ ht.1 ht.2
  · obtain ⟨m, hm, hm'⟩ := hN (s' * s) (t' * t)
    refine ⟨m, hm, fun v => ?_⟩
    rw [hm' v]
    simp only [Submodule.coe_smul, Complex.coe_smul, smul_smul]

theorem leg (B : RowsAut) (b M : ℝ) (P : ℕ) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (hS : StepBoundAt B b P) (h : ∀ i, IsReps B (T i) (Fr i)) (hM : 0 ≤ M)
    (E : gInf B) (z : B.I.GA)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ VP B (P + 1), ‖vv B Fr u (pt B E z t)‖ ≤ M * ‖u‖)
    {u : B.Hs} (hu : u ∈ VP B P) :
    ‖vv B Fr u (pt B E z 1) - vv B Fr u z‖ ≤
      Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t => vv B Fr u (pt B E z t)) (f' := fun s => vv B Fr (dAct B E u) (pt B E z s))
    (C := Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖))
    (fun s _ => (hasDerivAt_vv B T Fr h hu E z s).hasDerivWithinAt)
    (fun s hs => by
      refine (hb s (Set.Ico_subset_Icc_self hs) _ (hS.2.2.2.2.2.2 E u hu)).trans ?_
      refine (mul_le_mul_of_nonneg_left (hS.2.2.2.2.2.1 E u hu) hM).trans (le_of_eq ?_)
      ring)
  simpa only [pt_zero] using this

theorem path_variation : ∀ (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)), StepBoundAt B b P → (∀ i, IsReps B (T i) (Fr i)) → 0 ≤ M → (∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P, ‖vv B Fr u y - vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro B b ρ M P D T Fr x W hS h hM hb y hy u hu
  obtain ⟨hy2, A0, Z0, hg, hρ, hy1, hN⟩ := hy
  let A : gInf B := fun v => ⟨A0 v, (hg v).1⟩
  let Z : gInf B := fun v => ⟨Z0 v, (hg v).2⟩
  have hmem := fun s t hs ht => pt_mem_omega B x W ρ A Z hρ hN (s := s) (t := t) hs ht
  have hyeq : y = pt B Z (pt B A x 1) 1 := by
    refine Prod.ext ?_ (by simp [pt, hy2])
    funext v
    apply uMat_inj
    rw [hy1 v]
    simp only [pt, one_smul]
    rfl
  have h1 := leg B b M P T Fr hS h hM A x (fun t ht w hw => by
    have := hb _ (hmem t 0 ht (by simp)) w hw
    rwa [pt_zero] at this) hu
  have h2 := leg B b M P T Fr hS h hM Z (pt B A x 1) (fun t ht w hw => hb _ (hmem 1 t (by simp) ht) w hw) hu
  have hK : 0 ≤ Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    unfold beP; positivity
  rw [← hyeq] at h2
  calc _ ≤ ‖vv B Fr u y - vv B Fr u (pt B A x 1)‖ + ‖vv B Fr u (pt B A x 1) - vv B Fr u x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Real.sqrt (∑ v, Formalism.REAL.hs (A0 v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z0 v))) *
        (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
        rw [add_mul, add_comm]; exact add_le_add h1 h2
    _ ≤ ρ * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := mul_le_mul_of_nonneg_right hρ hK
    _ = _ := by ring

end GlobalTheory.PathVar
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassOrbit

theorem mass_orbit_class {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d₁ : S.Datum) (Λ₁ : Submodule L.O S.V)
    (h₁ : S.IsTerm d₁ Λ₁) (d : S.Datum) :
    (S.mass d fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • S.Fr d₁ Λ₁) =
      ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ := by
  have act := @GlobalTheory.FrameAct.stabiliser_acts_on_terms F _ _ _ _ _ E _ _ _ L r k S
  have trm := @GlobalTheory.HL.TermBasic.term_basic F _ _ _ _ _ E _ _ _ L r k S
  have vol := (@GlobalTheory.HL.volSt F _ _ _ _ _ E _ _ _ L r k S).2
  have hT : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) := fun d Λ H h hh => (act d Λ H h hh).1
  have hF : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.Fr d (h • Λ) = h • S.Fr d Λ :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.1
  have hB : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.2.2.2.1
  have hI : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ H => (trm d Λ H).2.2.2.2.2.2.1
  rw [GlobalTheory.HL.mass_eq_sumCls L r k S d _ (by
    rintro h hh Λ H ⟨hb, s, hs, e⟩
    refine ⟨(hB d Λ H h hh).2 hb, h * s, S.St.mul_mem hh hs, ?_⟩
    rw [hF d Λ H h hh, e, mul_smul])]
  set C₁ := S.Fr d₁ Λ₁ with hC
  unfold Frames.sumCls
  rw [tsum_eq_single (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁)]
  · have hrel : (MulAction.orbitRel S.St (Set S.FrP))
        (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out C₁ := Quotient.mk_out C₁
    obtain ⟨⟨h, hh⟩, e⟩ := MulAction.orbitRel_apply.1 hrel
    have e' : (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out = h • C₁ := e.symm
    have hint : S.IsIntCls (h • C₁) := by
      rw [hC, ← hF d₁ Λ₁ h₁ h hh]
      exact hI _ _ (hT _ _ h₁ h hh)
    change (if S.IsIntCls (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out then
      ENNReal.ofReal (S.wC (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out) *
        S.nT d (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out _ else 0) = _
    rw [e', if_pos hint, (vol C₁ (hI _ _ h₁).1).2.2.2 h hh]
    congr 1
    unfold Frames.nT
    congr 1
    have hset : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = h • C₁} =
        (fun Λ : Submodule L.O S.V => h • Λ) '' {Λ | S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C₁} := by
      ext Λ
      constructor
      · rintro ⟨H, ⟨hb, -⟩, e⟩
        have hi := S.St.inv_mem hh
        refine ⟨h⁻¹ • Λ, ⟨hT _ _ H _ hi, (hB _ _ H _ hi).2 hb, ?_⟩, smul_inv_smul h Λ⟩
        rw [hF _ _ H _ hi, e, inv_smul_smul]
      · rintro ⟨Λ', ⟨H, hb, e⟩, rfl⟩
        have e2 : S.Fr d (h • Λ') = h • C₁ := by rw [hF _ _ H _ hh, e]
        exact ⟨hT _ _ H _ hh, ⟨(hB _ _ H _ hh).2 hb, h, hh, e2⟩, e2⟩
    rw [hset]
    exact (MulAction.injective h).encard_image _
  · intro o ho
    have h0 : S.nT d o.out (fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) = 0 := by
      unfold Frames.nT
      have : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = o.out} = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨-, s, hs, e⟩, e2⟩
        apply ho
        rw [← Quotient.out_eq o]
        apply Quotient.sound
        exact MulAction.orbitRel_apply.2 ⟨⟨s, hs⟩, by rw [← e2, e]; rfl⟩
      rw [this]
      simp
    simp only [h0, mul_zero, ite_self]

end GlobalTheory.HL.MassOrbit
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitChoice

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) (hm : (p : 𝓞 E) ∈ P) (hN : Ideal.absNorm P = p) (h2 : (p : 𝓞 E) ∉ P ^ 2) (k : ℕ)
    (a : 𝓞 E) : ∃ m : ℤ, a - m ∈ P ^ k := by
  first
  | exact @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | (apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow ..)

theorem not_isConj_self (I : AutInst) {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 I.E))
    (hm : (p : 𝓞 I.E) ∈ v.asIdeal) (hN : Ideal.absNorm v.asIdeal = p) (h2 : (p : 𝓞 I.E) ∉ v.asIdeal ^ 2) :
    ¬ IsConj I v v := by
  intro h
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hmap : v.asIdeal.map st ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (h a (st a) (hst a)).1 ha
  have hfix : ∀ a, st a = a := fun a => by
    have hall : ∀ k, st a - a ∈ v.asIdeal ^ k := fun k => by
      obtain ⟨m, hm'⟩ := exists_int_sub_mem_pow hp v.asIdeal v.isMaximal hm hN h2 k a
      have h3 : st (a - m) ∈ v.asIdeal ^ k := by
        have := Ideal.mem_map_of_mem st hm'
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono hmap k this
      rw [map_sub, map_intCast] at h3
      simpa using sub_mem h3 hm'
    have := Ideal.iInf_pow_eq_bot_of_isDomain v.asIdeal v.isPrime.ne_top
    have h4 : st a - a ∈ (⊥ : Ideal (𝓞 I.E)) := this ▸ Ideal.mem_iInf.2 hall
    exact sub_eq_zero.1 h4
  have hfixE : ∀ x : I.E, star x = x := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 I.E) x
    have ha : star (algebraMap (𝓞 I.E) I.E a) = algebraMap (𝓞 I.E) I.E a := by
      rw [← hst a, hfix]
    have hb : star (algebraMap (𝓞 I.E) I.E b) = algebraMap (𝓞 I.E) I.E b := by
      rw [← hst b, hfix]
    rw [star_div₀, ha, hb]
  have hsurj : Function.Surjective (algebraMap I.F I.E) := fun x => (I.cm.fixed x).1 (hfixE x)
  have h1 : Module.finrank I.F I.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap I.F I.E).injective, hsurj⟩
  have := I.cm.deg2
  omega

theorem ncard_places_eq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard =
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  rw [← Set.ncard_image_of_injective _ (fun _ _ h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hv
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
    have : (p : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at this
    exact this

theorem exists_isChoice_and_isChoice_of_card : ∀ (I : AutInst) (g : Fin 2 → ℕ), (∀ k, (g k).Prime) → g 0 ≠ g 1 → (∀ k (P : Ideal (𝓞 I.E)), P.IsMaximal → ((g k : ℕ) : 𝓞 I.E) ∈ P → Ideal.absNorm P = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ P ^ 2) → (∃ w : ∀ _ : Fin 2, Fin I.f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin I.f) w) ∧ ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Fintype.card (Pl k) = I.f) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) → (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  intro I g hg hne h
  have hdeg : Module.finrank ℚ I.E = 2 * I.f := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, AutInst.f, mul_comm]
  refine GlobalTheory.Mem.RowsBundle.isChoice_of_card I g hg hne (fun k v hv => ?_) Module.finrank_pos fun k => ?_
  · obtain ⟨h1, h2⟩ := h k v.asIdeal v.isMaximal hv
    exact ⟨h1, h2, not_isConj_self I (hg k) v hv h1 h2⟩
  · rw [ncard_places_eq (hg k),
      GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E (g k) (hg k) (h k), hdeg]

end GlobalTheory.SplitChoice
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem extId_eq_map_psi (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, e⟩
    exact ⟨a, ha, Subtype.ext e.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem extId_mul_sup_natCast_conj : ∀ (I : AutInst), (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), extId I (𝔞 * 𝔟) = extId I 𝔞 * extId I 𝔟) ∧ (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), 𝔞 ⊔ 𝔟 = ⊤ → extId I 𝔞 ⊔ extId I 𝔟 = ⊤) ∧ (∀ m : ℕ, extId I (Ideal.span {(m : 𝓞 I.E)}) = Ideal.span {(m : IntAf I.F I.E)}) ∧ (∀ w : HeightOneSpectrum (𝓞 I.E), ∃ w', IsConj I w w') ∧ (∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w' w) ∧ (∀ w w' w'' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w w'' → w' = w'') ∧ ∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → ∀ z ∈ extId I w.asIdeal, ∃ z' ∈ extId I w'.asIdeal, (z' : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.sigR I.cm.sig (Af I.F) z := by
  intro I
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  have hsig : ∀ z ∈ IntAf I.F I.E, Formalism.UG.sigR I.cm.sig (Af I.F) z ∈ IntAf I.F I.E :=
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2
  refine ⟨fun a b => ?_, fun a b h => ?_, fun m => ?_, fun w => ?_, fun w w' h => ?_,
    fun w w' w'' h h' => ?_, fun w w' h z hz => ?_⟩
  · simp only [extId_eq_map_psi, Ideal.map_mul]
  · simp only [extId_eq_map_psi, ← Ideal.map_sup, h, Ideal.map_top]
  · rw [extId_eq_map_psi, Ideal.map_span, Set.image_singleton, map_natCast]
  · refine ⟨w.comap st hsurj, fun a b hab => ?_⟩
    have : b = st a := RingOfIntegers.ext hab
    subst this
    show _ ↔ st (st a) ∈ w.asIdeal
    rw [hst2]
  · intro a b hab
    exact (h b a (by rw [hab, star_star])).symm
  · refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    have e : (b : I.E) = star (st b : I.E) := by rw [hst, star_star]
    exact (h (st b) b e).symm.trans (h' (st b) b e)
  · have key : (⟨_, hsig z z.2⟩ : IntAf I.F I.E) ∈ extId I w'.asIdeal := by
      unfold extId at hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, e⟩ := hx
        refine Ideal.subset_span ⟨st a, (h a (st a) (hst a)).1 ha, ?_⟩
        show Formalism.UG.sigR I.cm.sig (Af I.F) x = _
        rw [e]
        rfl
      | zero =>
        convert (extId I w'.asIdeal).zero_mem using 1
        exact Subtype.ext (map_zero _)
      | add x y _ _ hx hy =>
        convert add_mem hx hy using 1
        exact Subtype.ext (map_add _ _ _)
      | smul a x _ hx =>
        convert Ideal.mul_mem_left _ ⟨_, hsig a a.2⟩ hx using 1
        exact Subtype.ext (map_mul _ _ _)
    exact ⟨_, key, rfl⟩

end GlobalTheory.RowLev
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

theorem _root_.GlobalTheory.T.integralAdeleIdealOfIdeal_principal_and_inter : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → (∃ t : IntAf I.F I.E, IsUnit (t : (I.E ⊗[I.F] Af I.F)) ∧ extId I 𝔞 = Ideal.span {t}) ∧ ∀ (a : 𝓞 I.E) (h : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E), (⟨_, h⟩ : IntAf I.F I.E) ∈ extId I 𝔞 ↔ a ∈ 𝔞 := by
  first | exact @GlobalTheory.RowLev.extId_principal_and_inter | exact GlobalTheory.RowLev.extId_principal_and_inter | (intros; apply GlobalTheory.RowLev.extId_principal_and_inter <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.exists_measurable_cutoff_fibre_integral_one_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∃ β : G → ENNReal, Measurable β ∧ (∀ y, β y ≠ ⊤) ∧ ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1 := by
  first | exact @GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one | exact GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one | (intros; apply GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.realUnipotentRadical_embeds_adelicRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W → ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧ ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  first | exact @GlobalTheory.RadEmb.radical_embeds | exact GlobalTheory.RadEmb.radical_embeds | (intros; apply GlobalTheory.RadEmb.radical_embeds <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.weil_formula_with_cutoff_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∀ β : G → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → (∀ f : G → ENNReal, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ y, β y * ∫⁻ m, f (m * y) ∂ν ∂μ) ∧ ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) μ ∧ ∫ y, f y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν ∂μ := by
  first | exact @GlobalTheory.weil_formula_cutoff | exact GlobalTheory.weil_formula_cutoff | (intros; apply GlobalTheory.weil_formula_cutoff <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.lintegral_productExpChart_allRealPlaces_le : ∀ (I : AutInst) (c : InfinitePlace I.F → ℝ) (s : ℝ) (E : InfinitePlace I.F → Fin (I.n ^ 2) → Matrix (Fin I.n) (Fin I.n) ℂ) (Θ : (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ) → I.Ginf), (∀ v, IsGauge (I.ε v) (c v)) → (∀ v i, inG (I.ε v) (E v i)) → (∀ v i j, ((E v i * (E v j)ᴴ).trace).re = if i = j then 1 else 0) → 0 < s → 12 * (I.n : ℝ) ^ 3 * s ≤ 1 → 8 * (I.n : ℝ) ^ 5 * s ≤ 1 → (∀ t v, uMat (Θ t v) = (List.ofFn fun i => NormedSpace.exp ((t v i : ℂ) • E v i)).prod) → ∃ S : Set I.Ginf, MeasurableSet S ∧ (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) ∧ ∀ Φ : I.Ginf → ENNReal, Measurable Φ → ∫⁻ t in Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s), Φ (Θ t) ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in S, Φ y ∂(muInf I) := by
  first | exact @GlobalTheory.ProductChartAll.lintegral_chart_all_le | exact GlobalTheory.ProductChartAll.lintegral_chart_all_le | (intros; apply GlobalTheory.ProductChartAll.lintegral_chart_all_le <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.smooth_continuous_convolution_realPointsUnitary : ∀ (I : AutInst) (a F : I.Ginf → ℂ), SmoothInf I a → HasCompactSupport a → LocallyIntegrable F (muInf I) → SmoothInf I (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) ∧ Continuous (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) := by
  first | exact @GlobalTheory.SmoothConv.smooth_convolution | exact GlobalTheory.SmoothConv.smooth_convolution | (intros; apply GlobalTheory.SmoothConv.smooth_convolution <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.riemannianHaarGauge_exists_pos_unique : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c := by
  first | exact @GlobalTheory.GaugeConst.gauge_exists_pos_unique | exact GlobalTheory.GaugeConst.gauge_exists_pos_unique | (intros; apply GlobalTheory.GaugeConst.gauge_exists_pos_unique <;> assumption)
end
