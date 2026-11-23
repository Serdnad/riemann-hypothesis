module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle410
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle288
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle209
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle413
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle280
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle411
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_padic_lift_mul_principalCongruence_of_reduction : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, Valued.v z < 1 → ‖θ z‖ < 1) → ∀ (A : GL (Fin n) (v.adicCompletion F)) (γ : GL (Fin n) (ZMod g)), (∀ a b, Valued.v ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1) → ∃ k ∈ (GlobalTheory.GLp.red g n).ker, Matrix.GeneralLinearGroup.map θ.toRingHom A = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n k := by
  first | exact @GlobalTheory.LiftRed.liftred_exists | exact GlobalTheory.LiftRed.liftred_exists | (intros; apply GlobalTheory.LiftRed.liftred_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  first | exact @GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | exact GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | (intros; apply GlobalTheory.GLp.inc_map_sub_one_valued_lt_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SerSys.LabDepth

open GlobalTheory.WeilDeligne

section Transport

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
  (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (i : ℚ_[p] ≃+* w.adicCompletion F) (hi : Continuous i)
include hw hi

theorem norm_symm_le (z : w.adicCompletion F) (hz : ‖z‖ ≤ 1) : ‖i.symm z‖ ≤ 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have h2 : ‖t⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one t⁻¹ (-1)).2 (by simpa using h1)
    exact this
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h3 : ‖t⁻¹ / (p : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one₀ (by have := (Fact.out : p.Prime).one_lt; positivity)]
    simpa using h2
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h3
  have e : z⁻¹ = (p : w.adicCompletion F) * i.toRingHom (t⁻¹ / (p : ℚ_[p])) := by
    rw [map_div₀, map_inv₀, map_natCast]
    change z⁻¹ = (p : w.adicCompletion F) * ((i t)⁻¹ / p)
    rw [ht, RingEquiv.apply_symm_apply]
    have hpE : (p : w.adicCompletion F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    field_simp
  have h5 : ‖z⁻¹‖ < 1 := by
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h4) (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w p hw)
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  rw [norm_inv] at h5
  have := (one_le_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith


omit hw in
theorem norm_symm_lt (z : w.adicCompletion F) (hz : ‖z‖ < 1) : ‖i.symm z‖ < 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h1
  have e : i.toRingHom t⁻¹ = z⁻¹ := by
    rw [map_inv₀]; change (i t)⁻¹ = z⁻¹; rw [ht, RingEquiv.apply_symm_apply]
  rw [e, norm_inv] at h4
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  have := (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith

theorem exists_ker_red {n : ℕ} (u : GL (Fin n) (w.adicCompletion F))
    (hu : u ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion F) (Fin n)) :
    ∃ y : (GlobalTheory.GLp.red p n).ker, GlobalTheory.GLp.inc p n y = Matrix.GeneralLinearGroup.map i.symm.toRingHom u := by
  rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne w n).2, GlobalTheory.AdelicU.mem_princ_iff,
    GlobalTheory.AdelicU.mem_GLint_iff] at hu
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  have hM : ∀ a b, ‖i.symm (u.1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1 a b)))
  have hN : ∀ a b, ‖i.symm ((u⁻¹).1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h2 a b)))
  let M : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm (u.1 a b), hM a b⟩
  let N : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm ((u⁻¹).1 a b), hN a b⟩
  have hMm : M.map (PadicInt.Coe.ringHom (p := p)) = u.1.map i.symm := rfl
  have hNm : N.map (PadicInt.Coe.ringHom (p := p)) = (u⁻¹).1.map i.symm := rfl
  have hinj : Function.Injective (Matrix.map · (PadicInt.Coe.ringHom (p := p)) : Matrix (Fin n) (Fin n) ℤ_[p] → _) :=
    Matrix.map_injective Subtype.coe_injective
  have e1 : M * N = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  have e2 : N * M = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
  let y : GL (Fin n) ℤ_[p] := ⟨M, N, e1, e2⟩
  have hy : GlobalTheory.GLp.red p n y = 1 := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    change PadicInt.toZMod (M a b) = (1 : Matrix (Fin n) (Fin n) (ZMod p)) a b
    have h4 : M a b - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) a b ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      have h5 := norm_symm_lt w p i hi _ (Valued.toNormedField.norm_lt_one_iff.2 (h3 a b))
      convert h5 using 1
      rw [PadicInt.norm_def, PadicInt.coe_sub, Matrix.sub_apply, map_sub]
      congr 1
      by_cases hab : a = b
      · subst hab; simp; rfl
      · simp [Matrix.one_apply_ne hab]; rfl
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h4
    rw [h4]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  exact ⟨⟨y, hy⟩, Units.ext rfl⟩

end Transport

theorem exists_pull (D : D7) (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : QRep (D.host.g k) n)
    (hπ : IrrSm π) (hfix : fixK1 π.ρ ≠ ⊥) :
    ∃ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)),
      Nonempty (π ≅ pull I k v σ) ∧
      GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥ := by
  let _ := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  have hi : Continuous (I.i k v).symm := by
    refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
    exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).symm.toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨⟨π, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom), fun x => (hπ.2 x).preimage hc,
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp ((GlobalTheory.GLp.Model.isIrrRep_iff _).1 hπ.1) _ fun g => ⟨_, hg g⟩⟩,
    ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ π) fun g => LinearMap.ext fun x => ?_)⟩, ?_⟩
  · change π.ρ g x = π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
    rw [hg]
  · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
    refine (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, hy0⟩
    obtain ⟨z, hz⟩ := exists_ker_red (D.naut.plGw k v) (D.host.g k) (D.naut.plGw_over k v) (I.i k v) (I.cont k v) u hu
    change π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom u) y = y
    rw [← hz]
    have := (Submodule.mem_iInf _).1 hy z
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

theorem tame_of_isTameWD {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x : WD h}
    (hx : GlobalTheory.LocLanglands.IsTameWD x) : x.tame := by
  obtain ⟨n, a, rfl, ha⟩ := hx
  refine (WD.tame_mk a).2 fun σ hσ => ha σ ⟨Wild_le_Ine hσ, fun y hy => ?_⟩
  have e : (σ : G E Ω) y - y = ((σ : G E Ω) y / y - 1) * y := by field_simp
  have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
  rw [e, map_mul]
  exact mul_lt_of_lt_one_left h0 (hσ y hy)

end GlobalTheory.SerSys.LabDepth

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin
open GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem principalCongruence_fixed_vector_rational_local_field {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥) :
    fixK1 (pull I k v τ).ρ ≠ ⊥ := by
  have hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hle : ∀ t : ℚ_[D.host.g k], ‖t‖ ≤ 1 → ‖I.i k v t‖ ≤ 1 := fun t ht =>
    GlobalTheory.TypeRec.Model.emb_le (D.naut.plGw k v) (D.host.g k) (I.i k v).toRingHom (I.cont k v) t ht
  have hlt : ∀ t : ℚ_[D.host.g k], ‖t‖ < 1 → ‖I.i k v t‖ < 1 := by
    intro t ht
    have hp := (Fact.out : (D.host.g k).Prime)
    have h2 : ‖t‖ ≤ ((D.host.g k : ℕ) : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one t (-1)).2 (by simpa using ht)
    have hp0 : ((D.host.g k : ℕ) : ℚ_[D.host.g k]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h3 : ‖t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one₀ (by have := hp.one_lt; positivity)]
      simpa using h2
    have e : I.i k v t = ((D.host.g k : ℕ) : (D.naut.plGw k v).adicCompletion D.host.E) *
        I.i k v (t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])) := by
      rw [← map_natCast (I.i k v) (D.host.g k), ← map_mul, mul_div_cancel₀ _ hp0]
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hle _ h3))
      (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt (D.naut.plGw k v) (D.host.g k) hw)
  have hint : ∀ (q : GL (Fin n) ℤ_[D.host.g k]) a b,
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n q)).1 a b ∈
        (D.naut.plGw k v).adicCompletionIntegers D.host.E := by
    intro q a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (Valued.toNormedField.norm_le_one_iff.1 (hle _ (PadicInt.norm_le_one (q.1 a b))))
  have hone : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) a b =
      I.i k v (((1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b : ℤ_[D.host.g k]) : ℚ_[D.host.g k]) := by
    intro a b
    by_cases h' : a = b
    · subst h'; simp
    · simp [Matrix.one_apply_ne h']
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun z => ?_, hy0⟩
  have hu : Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z) ∈
      GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n) := by
    rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne (D.naut.plGw k v) n).2, GlobalTheory.AdelicU.mem_princ_iff,
      GlobalTheory.AdelicU.mem_GLint_iff]
    refine ⟨⟨fun a b => hint _ a b, fun a b => ?_⟩, fun a b => ?_⟩
    · rw [← map_inv, ← map_inv]
      exact hint _ a b
    · have hz : GlobalTheory.GLp.red (D.host.g k) n z = 1 := z.2
      have hab : PadicInt.toZMod ((z : GL (Fin n) ℤ_[D.host.g k]).1 a b) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (D.host.g k))) a b :=
        congrArg (fun m : GL (Fin n) (ZMod (D.host.g k)) => m.1 a b) hz
      have h4 : (z : GL (Fin n) ℤ_[D.host.g k]).1 a b - (1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b ∈
          RingHom.ker (PadicInt.toZMod (p := D.host.g k)) := by
        rw [RingHom.mem_ker, map_sub, hab]
        by_cases h' : a = b
        · subst h'; simp
        · simp [Matrix.one_apply_ne h']
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h4
      have h5 := hlt _ h4
      apply Valued.toNormedField.norm_lt_one_iff.1
      rw [Matrix.sub_apply, hone a b]
      convert h5 using 2
      rw [PadicInt.coe_sub, map_sub]
      rfl
  change τ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z)) y - y = 0
  rw [sub_eq_zero]
  exact GlobalTheory.Parabolic.mem_fixed.1 hy _ hu

theorem principalCongruenceFixedVectors_ne_bot_of_iso {g : ℕ} [Fact g.Prime] {n : ℕ} {π π' : QRep g n} (e : π ≅ π') (h : fixK1 π'.ρ ≠ ⊥) :
    fixK1 π.ρ ≠ ⊥ := by
  intro hb
  apply h
  rw [Submodule.eq_bot_iff] at hb ⊢
  intro x hx
  have hy : (e.inv.hom x) ∈ fixK1 π.ρ := by
    simp only [fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro q
    rw [← Rep.hom_comm_apply, hx q]
  have h0 := hb _ hy
  have : e.hom.hom (e.inv.hom x) = x := by simp
  rw [← this, h0, map_zero]

end GlobalTheory.LabPin

namespace GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.LabPin
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedTermLattice_isGlobalTerm_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) ∧ ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U))⁻¹ * Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U') * (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  first | exact @GlobalTheory.HL.MovedTermPhase.main | exact GlobalTheory.HL.MovedTermPhase.main | (intros; apply GlobalTheory.HL.MovedTermPhase.main <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.signedLocalTerm_defect_iff_unsignedLocalTerm : ∀ {D : D7} (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ), locBBne Z p Λ F F' Tn T'n ↔ LocNG.BBne (H := locH Z p) (locU Z p Λ F F' Tn T'n) := by
  first | exact @GlobalTheory.SignDefect.locBBne_iff_locU | exact GlobalTheory.SignDefect.locBBne_iff_locU | (intros; apply GlobalTheory.SignDefect.locBBne_iff_locU <;> assumption)
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Side

theorem urep_irred_of_ds {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : IsDSHpk k r ε lam σ) : IsURepOn (GG k r) σ ∧ IsIrredOn (GG k r) σ := by
  obtain ⟨P, ⟨⟨hP, hH⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, hi, -⟩ := h
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv _ hd
  have hiP : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have mem : ∀ g, g ∈ GG k r ↔ P * g * P⁻¹ ∈ UJset ε := uHConj _ ε _ P hd hH
  have back : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hiP]; simp
  have forth : ∀ g : Mat k r, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPi]; simp
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simpa [hiP] using h1
  · intro a ha b hb
    have := hm _ ((mem a).1 ha) _ ((mem b).1 hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hiP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    simpa only [e, back] using this
  · intro g hg v
    have := hn _ ((mem g).1 hg) v
    simpa only [back] using this
  · intro v
    have hcont : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp hcont.continuousOn (s := GG k r) (fun g hg => (mem g).1 hg)
    refine this.congr fun g _ => ?_
    simp only [Function.comp, back]
  · intro S hS hst
    refine hi S hS fun g hg v hv => hst _ ((mem _).2 ?_) v hv
    rw [forth]; exact hg

theorem isHaarOn_smul {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {c : ℝ}
    (hc : 0 < c) : IsHaarOn S (ENNReal.ofReal c • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ENNReal.ofReal c • μ = c.toNNReal • μ := rfl
    rw [this]; infer_instance
  · intro h0
    rcases Measure.ennreal_smul_eq_zero.1 h0 with h | h
    · exact (ENNReal.ofReal_pos.2 hc).ne' h
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]
    apply Measurable.aemeasurable
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun l _ => measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply l))

theorem oneSide_of_bessel {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {u : Fin k → ℝ}
    {s : ℂ} {μG μW μN νS : Measure (Mt k r)} {B : H → Wp} {v : H} {c : ℝ}
    (hσ : IsURepOn (GG k r) σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muS μW μN) νS)
    (hB : IsBesselMapSm z (psi k r z s) σ π B) (hv : IsSmoothVec σ v) (hc : 0 < c)
    (hl : l2SG νS (fun g => B (σ g v)) = ENNReal.ofReal (c * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z s) μG μW μN νS (fun g => B (σ g v)) c := by
  have := FiniteDimensional.complete ℂ Wp
  obtain ⟨hnt, hu, hi⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  refine ⟨hz, hT, hnt, hu, hi, hG, hW, hW1, hN, hq, fun n hn => (psiChar k r z s hz n hn).2, ?_, ?_, hc, hl⟩
  · intro h hh m hm g hg
    have hdet : IsUnit (Hpk k r).det :=
      Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
    have hhm : h * m ∈ GG k r := (uHGroup _ _ hdet).2.1 h hh.1 m hm.1
    have hs : IsSmoothVec σ (σ g v) := ((GlobalTheory.T.smooth_vectors_dense_invariant k r σ v hσ).2.2.2.1 v hv).1 g hg
    have := hB.2.2.1 h hh m hm (σ g v) hs
    show B (σ (h * m * g) v) = _
    rw [hσ.1.2 _ hhm _ hg]
    exact this
  · exact (GlobalTheory.T.diffQuotient_besselMap_tendsto k r σ z _ π B v 0 hσ hB hv (by simp [InLieHpk])).2.1

theorem both_sides : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) lam (A : LocS W), 0 < θ → 0 < D.host.v → HypTT D w w' → GoodW D τ w w' θ W → GoodS D lam A → IsURepOn (GG D.R.k D.R.rS) A.σ ∧ IsIrredOn (GG D.R.k D.R.rS) A.σ ∧ W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS ∧ OneSide W.z W.π (psiS D W.z) W.μG W.μW W.μN W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' W.μN W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hθ hv hTT hW hA
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, w1', w2, w2', hN, q1, q2⟩ := hW
  obtain ⟨-, hds, b1, b2, hsm, -, -, hc, l1, l2, -⟩ := hA
  obtain ⟨hu, hi⟩ := urep_irred_of_ds hds
  have hpos : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  have hμ : W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS := by
    have e : haarLie (Nset D.R.k D.R.rS) (kapN D θ) = kapN D θ • haarLie (Nset D.R.k D.R.rS) 1 := by
      unfold haarLie; rw [one_smul]
    rw [hN, e, GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, smul_smul, ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_pow (by norm_num)]
    simp [kapN]
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμ]; exact isHaarOn_smul (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn _ _) (by positivity)
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  exact ⟨hu, hi, hμ, oneSide_of_bessel hu z1 hT1 c1 hG w1 w1' hNH q1 b1 hsm hc l1,
    oneSide_of_bessel hu z2 hT2 c2 hG w2 w2' hNH q2 b2 hsm hc l2⟩

end GlobalTheory.Amp.Side
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.cell_data_support : Hyps → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbInt.orbInt_integrable | exact GlobalTheory.CellOrbInt.orbInt_integrable | (intros; apply GlobalTheory.CellOrbInt.orbInt_integrable <;> assumption)
end

section


theorem _root_.GlobalTheory.T.adaptedNormalForm_gives_real_normal_form : GlobalTheory.TypeAsm.FrameC := by
  first | exact @GlobalTheory.TypeAsm.frameC_holds | exact GlobalTheory.TypeAsm.frameC_holds | (intros; apply GlobalTheory.TypeAsm.frameC_holds <;> assumption)
end

section


theorem _root_.GlobalTheory.T.rowsMeanC_holds : GlobalTheory.TypeAsm.RowsMeanC := by
  first | exact @GlobalTheory.TypeAsm.rowsMean | exact GlobalTheory.TypeAsm.rowsMean | (intros; apply GlobalTheory.TypeAsm.rowsMean <;> assumption)
end
