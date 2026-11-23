module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CurveFormSign
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009

@[expose] public section

section

noncomputable section

namespace GlobalTheory.OneArcCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

theorem mono_spMap_iff {O F : Type} [CommRing O] [Field F] [CharZero F] [FiniteDimensional ℚ F] (β : O →+* F) :
    Mono (spMap β) ↔ GeneratesFrac β := by
  have e : Mono (spMap β) ↔ Epi (CommRingCat.ofHom β) := by
    constructor
    · intro h
      have h' : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op) := h
      have := Scheme.Spec.mono_of_mono_map h'
      exact (inferInstance : Epi (CommRingCat.ofHom β).op.unop)
    · intro h
      exact (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op))
  rw [e]
  constructor
  · intro h x
    let K : Subfield F := Subfield.closure (Set.range β)
    let β₁ : O →+* K := β.codRestrict K fun r => Subfield.subset_closure ⟨r, rfl⟩
    have h₁ : Epi (CommRingCat.ofHom β₁ ≫ CommRingCat.ofHom K.subtype) := h
    have h₂ : Epi (CommRingCat.ofHom K.subtype) := epi_of_epi (CommRingCat.ofHom β₁) _
    have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have h₃ : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
    obtain ⟨⟨x', hx'⟩, rfl⟩ := RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom K.subtype) h₃ x
    obtain ⟨p, hp, q, hq, rfl⟩ := Subfield.mem_closure_iff.1 hx'
    have hc : Subring.closure (Set.range β) = β.range := Subring.closure_eq β.range
    rw [hc] at hp hq
    obtain ⟨r, rfl⟩ := hp
    obtain ⟨s, rfl⟩ := hq
    by_cases hs : β s = 0
    · exact ⟨0, 1, by simp, by simp [hs]⟩
    · exact ⟨r, s, hs, div_mul_cancel₀ _ hs⟩
  · intro h
    refine ⟨fun {A} f g hfg => ?_⟩
    ext x
    obtain ⟨r, s, hs, hx⟩ := h x
    have k : ∀ r, f.hom (β r) = g.hom (β r) := fun r => congrArg (fun q => q.hom r) hfg
    have hu : IsUnit (f.hom (β s)) := (IsUnit.mk0 _ hs).map f.hom
    refine hu.mul_right_cancel ?_
    rw [← map_mul, hx, k r, k s, ← map_mul, hx]

theorem mem_abLocus_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by
  have key : ∀ {T : Scheme.{0}} (t : T ⟶ S'),
      IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f)) := by
    intro T t
    have hp := (IsPullback.of_hasPullback G'.hom t).paste_horiz h
    have e := hp.isoPullback_hom_snd
    constructor
    · intro _
      rw [← hp.isoPullback_inv_snd]; infer_instance
    · intro _
      rw [← e]; infer_instance
  constructor
  · intro hx K _ _ t ⟨p, hp⟩
    exact (key t).2 (hx K (t ≫ f) ⟨p, by rw [← hp]; simp⟩)
  · intro hx
    let K := AlgebraicClosure (S'.residueField x)
    let t : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) K)) ≫ S'.fromSpecResidueField x
    have p : Sp K := (default : PrimeSpectrum K)
    have ht : t p = x := Scheme.fromSpecResidueField_apply x _
    exact abLocusOne S G hG K (t ≫ f) ((key t).1 (hx K t ⟨p, ht⟩)) ⟨p, congrArg (fun z => f z) ht⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

end GlobalTheory.OneArcCompare
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.TorusWt

variable {p q n : ℕ}

def torX (θ : Ix p q → ℝ) : Mat p q := Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem torX_mem (θ : Ix p q → ℝ) : torX θ ∈ upq p q := by
  change _ = _
  ext a b
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  rw [hJ, torX, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add]
  by_cases h : a = b
  · subst h; simp; ring
  · simp [h]

theorem smul_torX (t : ℝ) (θ : Ix p q → ℝ) : t • torX θ = torX fun a => t * θ a := by
  ext a b
  by_cases h : a = b
  · subst h; simp [torX, mul_assoc]
  · simp [torX, h]

theorem torX_eq_sum (θ : Ix p q → ℝ) : torX θ = ∑ a, ((θ a : ℂ) * Complex.I) • Eab a a := by
  ext a b
  simp only [torX, Eab, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

theorem reindex_cov_expt (T : GrpData p q) (e : Ix p q ≃ Fin n) (θ : Fin n → ℝ) :
    Matrix.reindex e e ((T.cov (T.expt (torX fun a => θ (e a))) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem _), torX, Matrix.exp_diagonal]
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp [Matrix.diagonal_apply, Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem flow_eq {T : GrpData p q} (R : DSRep T) {X : Mat p q} (hX : X ∈ upq p q) {v : R.HK.V} {c : ℂ}
    (hv : R.HK.act X v = c • v) : R.U.π (T.expt X) (R.ι v) = Complex.exp c • R.ι v := by
  set f : ℝ → R.U.H := fun t => R.U.π (T.expt (t • X)) (R.ι v) with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h0 := R.der X hX v
    rw [hv, map_smul] at h0
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • R.ι v) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • R.ι v) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((R.U.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert (preTransparency := .reducible) h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem isWtOn_iff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (μ : Fin n → ℝ) (v : R.HK.V), IsWtOn (Formalism.REAL.Kset ε) σ μ (R.ι v) ↔ ∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v := by
  intro p q n e ε T R σ _ hF μ v
  have key : ∀ θ : Fin n → ℝ, R.U.π (T.expt (torX fun a => θ (e a))) =
      σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := fun θ => by
    rw [hF, reindex_cov_expt]
  constructor
  · intro h a
    set θ : Fin n → ℝ := Pi.single (e a) 1 with hθ
    have h0 := R.der _ (torX_mem fun b => θ (e b)) v
    have h1 : (fun t : ℝ => R.U.π (T.expt (t • torX fun b => θ (e b))) (R.ι v)) =
        fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v := by
      funext t
      rw [smul_torX, key fun b => t * θ b, h _ (diag_mem_Kset ε _)]
      congr 2
      rw [Finset.sum_eq_single (e a)]
      · simp [hθ]; ring
      · intro c _ hc; simp [hθ, hc]
      · simp
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v)
        ((μ (e a) * Complex.I) • R.ι v) 0 := by
      have : HasDerivAt (fun t : ℝ => ((μ (e a) * Complex.I) * (t : ℂ))) (μ (e a) * Complex.I) 0 := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (μ (e a) * Complex.I))
      simpa using this.cexp.smul_const (R.ι v)
    rw [h1] at h0
    have h3 := h0.unique h2
    rw [← map_smul] at h3
    have h4 := R.ι_inj h3
    have h5 : (torX fun b => θ (e b)) = Complex.I • Eab a a := by
      rw [torX_eq_sum, Finset.sum_eq_single a]
      · simp [hθ]
      · intro c _ hc; simp [hθ, hc]
      · simp
    rw [h5, map_smul, LinearMap.smul_apply, mul_comm, mul_smul] at h4
    exact smul_right_injective _ Complex.I_ne_zero h4
  · intro h θ _
    rw [← key]
    apply flow_eq R (torX_mem _)

    rw [torX_eq_sum, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, h, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← e.sum_comp]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.RealPar.TorusWt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealPar.SqInt

variable {p q n : ℕ}

def reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Matrix a a ℂ →* Matrix b b ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom

theorem reixHom_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b)
    (g : Matrix a a ℂ) : reixHom e g = Matrix.reindex e e g := rfl

theorem continuous_reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Continuous (reixHom e) :=
  continuous_id.matrix_reindex e e

def covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) : T.G →* Formalism.REAL.UJ ε :=
  ((Units.map (reixHom e)).comp T.cov).codRestrict (Formalism.REAL.UJ ε) fun x => h.cov_mem T x

theorem umat_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    umat (covU h T x) = Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := rfl

theorem continuous_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Continuous (covU h T) :=
  Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp (continuous_fst.comp T.emb.continuous)) _

theorem surjective_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Function.Surjective (covU h T) := by
  intro g
  obtain ⟨x, hx⟩ := h.cov_surj T (g := umat g) g.2
  exact ⟨x, Subtype.ext (Units.ext hx)⟩

theorem isClosedEmbedding_emb (T : GrpData p q) :
    Topology.IsClosedEmbedding (fun x : T.G => (T.cov x, T.sq x)) := by
  refine ⟨T.emb, ?_⟩
  have : Set.range (fun x : T.G => (T.cov x, T.sq x)) =
      {z : GL (Ix p q) ℂ × ℂˣ | (z.1 : Mat p q)ᴴ * Jm p q * z.1 = Jm p q} ∩
        {z | (z.2 : ℂ) ^ 2 = (z.1 : Mat p q).det} := by
    ext ⟨g, w⟩
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact ⟨T.cov_mem x, T.sq_sq x⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx, -⟩ := T.bij g h1 w h2
      exact ⟨x, Prod.ext hx.1 hx.2⟩
  rw [this]
  have c1 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.1 : Mat p q) := Units.continuous_val.comp continuous_fst
  have c2 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.2 : ℂ) := Units.continuous_val.comp continuous_snd
  exact (isClosed_eq ((c1.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul c1) continuous_const).inter
    (isClosed_eq (c2.pow 2) c1.matrix_det)

theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖(T.sq x : ℂ)‖ = 1 := by
  have h1 := (mem_Upq _).1 (T.cov_mem x)
  have hJ : (Jm p q).det ≠ 0 := by
    have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
      rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
    rw [Matrix.det_reindex_self] at this
    exact left_ne_zero_of_mul_eq_one this
  have h2 := congrArg (fun A => ‖Matrix.det A‖) h1
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, ← T.sq_sq x, norm_pow] at h2
  have h3 : ‖(T.sq x : ℂ)‖ ^ 4 = 1 := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.2 hJ)
    rw [one_mul]
    conv_rhs => rw [← h2]
    ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h3

theorem isProperMap_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    IsProperMap (covU h T) := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_covU h T, fun K hK => ?_⟩
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hK' : IsCompact ((fun g : Formalism.REAL.UJ ε => (Units.map (reixHom e.symm) g.1 : GL (Ix p q) ℂ)) '' K) :=
    hK.image (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val)
  refine ((isClosedEmbedding_emb T).isCompact_preimage (hK'.prod hS)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_covU h T)) fun x hx => ⟨⟨covU h T x, hx, Units.ext ?_⟩, ?_⟩
  · change Matrix.reindex e.symm e.symm (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q)) = _
    simp
  · simpa using norm_sq_eq_one h T x

theorem isHaarMeasure_map_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    (T.haar.map (covU h T)).IsHaarMeasure :=
  Measure.isHaarMeasure_map T.haar (covU h T) (continuous_covU h T) (surjective_covU h T)
    (isProperMap_iff_tendsto_cocompact.1 (isProperMap_covU h T)).2

theorem isSqIntOn_of_factors : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsSqIntOn ε σ := by
  intro p q n e ε T R σ h hF v w
  have hc : coefOn (ε := ε) σ v w ∘ covU h T = fun g => inner ℂ w (R.U.π g v) := by
    funext x
    simp only [Function.comp, coefOn, umat_covU, hF x]
  have hc1 : Continuous fun g => (inner ℂ w (R.U.π g v) : ℂ) := continuous_const.inner (R.U.cont v)
  have hq := (isProperMap_covU h T).isClosedMap.isQuotientMap (continuous_covU h T) (surjective_covU h T)
  have hc2 : Continuous (coefOn (ε := ε) σ v w) := hq.continuous_iff.2 (hc ▸ hc1)
  haveI := isHaarMeasure_map_covU h T
  rw [Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (T.haar.map (covU h T))]
  refine MemLp.smul_measure ?_ ENNReal.coe_ne_top
  rw [memLp_map_measure_iff hc2.aestronglyMeasurable (continuous_covU h T).measurable.aemeasurable, hc,
    memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable]
  exact (R.schur v w).1

end GlobalTheory.RealPar.SqInt

end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

namespace GlobalTheory.CMPointCompare

section Dictionary

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} {B G' : Over Y} [GrpObj C] [GrpObj G] [GrpObj B] [GrpObj G']
  {f : Y ⟶ S} {x : Y ⟶ X} {β : B.left ⟶ C.left} {π : G'.left ⟶ G.left}

variable (hβ : IsGrpPullback B C f β) (hπ : IsGrpPullback G' G x π)

end Dictionary

section Intertwine

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} [GrpObj C] [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}
  {Φ : MapOver C G f x}

end Intertwine

section General

open GlobalTheory.CM

theorem hom_ext_of_complexPoints {R : Type} [CommRing R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {B G : Over (Sp R)} [Smooth B.hom] [IsSeparated G.hom] {a b : B ⟶ G}
    (h : ∀ p : Over.mk (spMap σ) ⟶ B, p ≫ a = p ≫ b) : a = b := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom σ) hσ
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback B.hom (spMap σ)) ?_
  have : IsReduced (pullback B.hom (spMap σ)) :=
    isReduced_of_smooth_complex _ (pullback.snd B.hom (spMap σ)) inferInstance
  refine ComplexPoints.hom_ext_of_points (pullback.snd B.hom (spMap σ)) G.hom (by simp) fun x hx => ?_
  have e := congrArg (fun z => z.left) (h (Over.homMk (x ≫ pullback.fst _ _) (by
    show (x ≫ _) ≫ _ = spMap σ
    rw [Category.assoc, pullback.condition, reassoc_of% hx])))
  exact (Category.assoc _ _ _).symm.trans (e.trans (Category.assoc _ _ _))

end General

section Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)

end Linear

end GlobalTheory.CMPointCompare
end
end
