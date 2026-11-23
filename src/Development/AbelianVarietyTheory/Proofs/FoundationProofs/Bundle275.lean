module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gamma_le_gamma_of_dvd {K M : ℕ} (h : K ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma K := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h1
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h2
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h3
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h4

theorem mem_gam_of_mem_gamma {N l : ℕ} {δ : SL(2, ℤ)} (hN : δ ∈ CongruenceSubgroup.Gamma N)
    (hl : δ ∈ CongruenceSubgroup.Gamma l) : δ ∈ Gam N l := by
  rw [CongruenceSubgroup.Gamma_mem] at hN hl
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem N δ).2 ⟨hN.1, hN.2.2.2, hN.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 hl.2.2.1

theorem cls_pow_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (g : X.Kˣ) : X.cls l n (g ^ (l ^ n)) = 0 := by
  unfold Tower.cls
  rw [Submodule.Quotient.mk_eq_zero]
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul (g ^ (l ^ n)) : X.Kl l) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul g : X.Kl l) := by
    rw [ofMul_pow, TensorProduct.tmul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) Submodule.mem_top

theorem eq_zero_of_btZ_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  intro Ω _ _ _ ε X hε hj N l hl hN b hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, ⟨f, a, c, M₁, hM₁, hev, ⟨ha, hc, hc0, hroot⟩, hinv⟩, M₂, hM₂, hχ⟩ := hb n u
  have hlpos : 0 < l := hl.out.pos
  obtain ⟨g, hg⟩ := kummer_root_mem ε X hε hj (l ^ n) (pow_pos hlpos n) f a c (M₁ * M₂ * N * l)
    (by positivity) ha hc hc0 hroot (by
      intro γ hγ
      have h1 : γ ∈ CongruenceSubgroup.Gamma M₁ := gamma_le_gamma_of_dvd ⟨M₂ * N * l, by ring⟩ hγ
      have h2 : γ ∈ CongruenceSubgroup.Gamma M₂ := gamma_le_gamma_of_dvd ⟨M₁ * N * l, by ring⟩ hγ
      have h3 : γ ∈ CongruenceSubgroup.Gamma N := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * l, by ring⟩ hγ
      have h4 : γ ∈ CongruenceSubgroup.Gamma l := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * N, by ring⟩ hγ
      have h0 : χ γ = 0 := by
        have := hχ ⟨γ, mem_gam_of_mem_gamma h3 h4⟩ h2
        simpa using this.symm
      refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz => ?_)
      have := hinv γ h1 z hz
      rw [h0] at this
      simpa using this)
  have : AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
    rw [hev, hg, cls_pow_eq_zero]
  exact this

end GlobalTheory.KZ.BettiB
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory Matrix
open scoped NNReal

noncomputable section

namespace GlobalTheory.DetSqrtCover

variable {p q : ℕ}

theorem exp_add_smul (X : Mat p q) (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)

theorem det_exp (X : Mat p q) : (NormedSpace.exp X).det = Complex.exp X.trace := by
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf
  have hd : ∀ t, HasDerivAt f (f t * X.trace) t := by
    intro t
    have h0 : HasDerivAt f X.trace (t - t) := by
      rw [sub_self]; exact GlobalTheory.RealPar.Cover.hasDerivAt_det_exp X
    have h1 := (h0.comp_sub_const t t).const_mul (f t)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Matrix.det_mul, ← exp_add_smul, add_sub_cancel]
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2

theorem exp_mul_exp_neg (X : Mat p q) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, add_neg_cancel, NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Mat p q) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

def expGL (X : Mat p q) : GL (Ix p q) ℂ :=
  ⟨NormedSpace.exp X, NormedSpace.exp (-X), exp_mul_exp_neg X, exp_neg_mul_exp X⟩

theorem continuous_mexp : Continuous fun X : Mat p q => NormedSpace.exp X := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem continuous_expGL : Continuous (expGL : Mat p q → GL (Ix p q) ℂ) :=
  Units.continuous_iff.2 ⟨continuous_mexp, continuous_mexp.comp continuous_neg⟩

theorem expGL_mem {X : Mat p q} (hX : X ∈ upq p q) : expGL X ∈ Formalism.UG.Upq p q := by
  have hJ : Jm p q * Jm p q = 1 := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  let U : (Mat p q)ˣ := ⟨Jm p q, Jm p q, hJ, hJ⟩
  have h1 : Xᴴ = U.val * (-X) * U⁻¹.val := by
    change Xᴴ = Jm p q * (-X) * Jm p q
    have h : Xᴴ * Jm p q = Jm p q * (-X) := by
      rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← h, Matrix.mul_assoc, hJ, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᴴ = Jm p q * NormedSpace.exp (-X) * Jm p q := by
    rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_units_conj]
    rfl
  rw [GlobalTheory.RealPar.mem_Upq]
  change (NormedSpace.exp X)ᴴ * Jm p q * NormedSpace.exp X = Jm p q
  rw [h2, Matrix.mul_assoc _ (Jm p q) (Jm p q), hJ, Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

def expHalf (X : Mat p q) : ℂˣ := Units.mk0 (Complex.exp (X.trace / 2)) (Complex.exp_ne_zero _)

theorem continuous_expHalf : Continuous (expHalf : Mat p q → ℂˣ) :=
  Units.isEmbedding_val₀.continuous_iff.2
    (Complex.continuous_exp.comp (continuous_id.matrix_trace.div_const 2))

theorem expHalf_sq (X : Mat p q) : ((expHalf X : ℂˣ) : ℂ) ^ 2 = (NormedSpace.exp X).det := by
  rw [det_exp, expHalf, Units.val_mk0, sq, ← Complex.exp_add, add_halves]

def cover (p q : ℕ) : Subgroup (GL (Ix p q) ℂ × ℂˣ) where
  carrier := {z | z.1 ∈ Formalism.UG.Upq p q ∧ (z.2 : ℂ) ^ 2 = (z.1 : Mat p q).det}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    simp only [Prod.snd_mul, Prod.fst_mul, Units.val_mul, Matrix.det_mul, mul_pow, ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
    simp only [Prod.snd_inv, Prod.fst_inv, Units.val_inv_eq_inv_val, inv_pow, ha.2, Matrix.coe_units_inv,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv']⟩

theorem isClosed_cover : IsClosed (cover p q : Set (GL (Ix p q) ℂ × ℂˣ)) := by
  have c1 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.1 : Mat p q) := Units.continuous_val.comp continuous_fst
  have c2 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.2 : ℂ) := Units.continuous_val.comp continuous_snd
  exact (isClosed_eq ((c1.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul c1)
    (continuous_const (y := Jm p q))).inter (isClosed_eq (c2.pow 2) c1.matrix_det)

instance locallyCompact_cover : LocallyCompactSpace (cover p q) := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  haveI : LocallyCompactSpace (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Ix p q) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace ℂᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace ℂˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact isClosed_cover.locallyCompactSpace

instance measurable_cover : MeasurableSpace (cover p q) := borel _

instance borel_cover : BorelSpace (cover p q) := ⟨rfl⟩


open Classical in
def expLift (X : Mat p q) : cover p q :=
  if h : X ∈ upq p q then ⟨(expGL X, expHalf X), expGL_mem h, expHalf_sq X⟩ else 1

theorem expLift_val {X : Mat p q} (h : X ∈ upq p q) : (expLift X).1 = (expGL X, expHalf X) := by
  rw [expLift, dite_eq_left h]

def grpOf (p q : ℕ) (ν : Measure (cover p q)) [ν.IsHaarMeasure] : GrpData p q where
  G := cover p q
  haar := ν
  cov := (MonoidHom.fst _ _).comp (cover p q).subtype
  sq := (MonoidHom.snd _ _).comp (cover p q).subtype
  cov_mem x := x.2.1
  sq_sq x := x.2.2
  bij g hg w hw := ⟨⟨(g, w), hg, hw⟩, ⟨rfl, rfl⟩, fun _ hy => Subtype.ext (Prod.ext hy.1 hy.2)⟩
  emb := Topology.IsEmbedding.subtypeVal
  expt := expLift
  expt_cov X hX := by
    change ((expLift X).1.1 : Mat p q) = _
    rw [expLift_val hX]; rfl
  expt_cont := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (continuous_expGL.prodMk continuous_expHalf).continuousOn.congr fun X hX => expLift_val hX
  expt_zero := by
    apply Subtype.ext
    rw [expLift_val (by simp [upq])]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact NormedSpace.exp_zero
    · simp [expHalf]
  expt_add X hX s t := by
    apply Subtype.ext
    have h := GlobalTheory.RealPar.KStabLie.smul_mem_upq hX
    rw [Subgroup.coe_mul, expLift_val (h _), expLift_val (h _), expLift_val (h _)]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact exp_add_smul X s t
    · simp [expHalf, add_smul, add_div, Complex.exp_add]

def covHom (T : GrpData p q) : T.G →* UpqT p q :=
  (T.cov.codRestrict (Formalism.UG.Upq p q) T.cov_mem : T.G →* Formalism.UG.Upq p q)

theorem continuous_covU (T : GrpData p q) : Continuous T.covU :=
  Continuous.subtype_mk (continuous_fst.comp T.emb.continuous) _

theorem surjective_covU (T : GrpData p q) : Function.Surjective T.covU := by
  rintro ⟨g, hg⟩
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : Mat p q).det) two_pos
  have h0 : w ≠ 0 := by
    rintro rfl
    exact g.det_ne_zero (by rw [← hw]; simp)
  obtain ⟨x, hx, -⟩ := T.bij g hg (Units.mk0 w h0) hw
  exact ⟨x, Subtype.ext hx.1⟩

theorem isProperMap_covU (T : GrpData p q) : IsProperMap T.covU := by
  haveI : T2Space (UpqT p q) := inferInstanceAs (T2Space (Formalism.UG.Upq p q))
  haveI : LocallyCompactSpace (UpqT p q) :=
    (UpqUnimodular.modelEquiv p q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_covU T, fun K hK => ?_⟩
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hK' : IsCompact ((fun g : Formalism.UG.Upq p q => g.1) '' K) := hK.image continuous_subtype_val
  refine ((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hK'.prod hS)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_covU T)) fun x hx => ⟨⟨T.covU x, hx, rfl⟩, ?_⟩
  simpa using GlobalTheory.RealPar.Cover.norm_sq x

theorem isHaarMeasure_map_covU (T : GrpData p q) : (T.haar.map T.covU).IsHaarMeasure := by
  haveI : IsTopologicalGroup (UpqT p q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  haveI : T2Space (UpqT p q) := inferInstanceAs (T2Space (Formalism.UG.Upq p q))
  haveI : LocallyCompactSpace (UpqT p q) :=
    (UpqUnimodular.modelEquiv p q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact Measure.isHaarMeasure_map T.haar (covHom T) (continuous_covU T) (surjective_covU T)
    (isProperMap_iff_tendsto_cocompact.1 (isProperMap_covU T)).2

theorem exists_grpData_map_haar : ∀ (p q : ℕ) (μ : Measure (UpqT p q)), μ.IsHaarMeasure →
    ∃ T : GrpData p q, Measure.map T.covU T.haar = μ := by
  intro p q μ hμ
  haveI := isHaarMeasure_map_covU (grpOf p q Measure.haar)
  obtain ⟨t, ht⟩ := GlobalTheory.CompactDualUnique.exists_eq_smul μ
    ((grpOf p q Measure.haar).haar.map (grpOf p q Measure.haar).covU)
  have h0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact isOpen_univ.measure_ne_zero μ Set.univ_nonempty (by rw [ht]; rfl)
  haveI : (t • (Measure.haar : Measure (cover p q))).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ h0
  refine ⟨grpOf p q (t • Measure.haar), ?_⟩
  rw [ht]
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  exact Measure.map_smul _ (continuous_covU _).aemeasurable

end GlobalTheory.DetSqrtCover

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm : ∀ D : D7, oddRep D := by
  first | exact @GlobalTheory.NormSum.exists_rep_trivial_at | exact GlobalTheory.NormSum.exists_rep_trivial_at | (intros; apply GlobalTheory.NormSum.exists_rep_trivial_at <;> assumption)
end
