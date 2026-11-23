module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle244
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle247
public import Mathlib.Analysis.Complex.Norm
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmVec Matrix

noncomputable section
namespace GlobalTheory.SmVecGelfComm

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def RealLin (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep π (X + Y) w = dRep π X w + dRep π Y w) ∧
    ∀ (a : ℝ), ∀ X ∈ lieG G, dRep π (a • X) w = (a : ℂ) • dRep π X w

theorem lie_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h : Xᴴ * G + G * X = 0 := hX
  show _ + _ = 0
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, h, smul_zero]

theorem conjG_add (Z W : Matrix (Fin n) (Fin n) ℂ) : conjG G (Z + W) = conjG G Z + conjG G W := by
  simp only [conjG, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem conjG_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (c • Z) = star c • conjG G Z := by
  simp only [conjG, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem dRepC_add_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π (Z + W) w = dRepC G π Z w + dRepC G π W w := by
  have e1 : (1 / 2 : ℂ) • (Z + W + conjG G (Z + W)) =
      (1 / 2 : ℂ) • (Z + conjG G Z) + (1 / 2 : ℂ) • (W + conjG G W) := by rw [conjG_add]; module
  have e2 : (1 / (2 * Complex.I)) • (Z + W - conjG G (Z + W)) =
      (1 / (2 * Complex.I)) • (Z - conjG G Z) + (1 / (2 * Complex.I)) • (W - conjG G W) := by
    rw [conjG_add]; module
  unfold dRepC
  rw [e1, e2, hl.1 _ (parts_mem hG hh Z).1 _ (parts_mem hG hh W).1,
    hl.1 _ (parts_mem hG hh Z).2 _ (parts_mem hG hh W).2]
  module

theorem dRepC_smul_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (c : ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) : dRepC G π (c • Z) w = c • dRepC G π Z w := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  have hs : star ((a : ℂ) + b * Complex.I) = a - b * Complex.I := by simp [sub_eq_add_neg]
  have hi : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    simp
  have hI := Complex.I_mul_I
  obtain ⟨h1, h2⟩ := parts_mem hG hh Z
  have e1 : (1 / 2 : ℂ) • (((a : ℂ) + b * Complex.I) • Z + conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      a • (1 / 2 : ℂ) • (Z + conjG G Z) + (-b) • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  have e2 : (1 / (2 * Complex.I)) • (((a : ℂ) + b * Complex.I) • Z - conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      b • (1 / 2 : ℂ) • (Z + conjG G Z) + a • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    match_scalars
    · linear_combination (-(b : ℂ) / 2) * hI
    · linear_combination (-(b : ℂ) / 2) * hI
  unfold dRepC
  rw [e1, e2, hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2), hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2),
    hl.2 _ _ h1, hl.2 _ _ h1, hl.2 _ _ h2, hl.2 _ _ h2]
  push_cast
  match_scalars
  · ring
  · linear_combination (-(b : ℂ)) * hI

def dLin (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] H where
  toFun Z := dRepC G π Z w
  map_add' := dRepC_add_left hG hh hl
  map_smul' := dRepC_smul_left hG hh hl

theorem dRepC_eq_sum (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z w = ∑ c, ∑ d, Z c d • dRepC G π (Matrix.single c d 1) w := by
  have e : Z = ∑ c, ∑ d, Z c d • Matrix.single c d (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp
  show dLin hG hh hl Z = _
  conv_lhs => rw [e]

  simp only [map_sum, map_smul]
  rfl

theorem conjG_conj (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (g⁻¹ * Z * g) = g⁻¹ * conjG G Z * g := by
  have h : gᴴ * G * g = G := hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hD := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  have h3 : G⁻¹ * gᴴ = g⁻¹ * G⁻¹ := by
    calc G⁻¹ * gᴴ = G⁻¹ * (gᴴ * G) * G⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
      _ = _ := by rw [← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hD, Matrix.one_mul]
  calc conjG G (g⁻¹ * Z * g) = -((G⁻¹ * gᴴ) * Zᴴ * ((g⁻¹)ᴴ * G)) := by
        simp only [conjG, conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h3, h2]; simp only [conjG, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

theorem dRepC_rep (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z (π g w) = π g (dRepC G π (g⁻¹ * Z * g) w) := by
  unfold dRepC
  rw [dRep_rep hG hπ hw hg (parts_mem hG hh Z).1, dRep_rep hG hπ hw hg (parts_mem hG hh Z).2, conjG_conj hG hg,
    map_add, map_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

def dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (smSub G π) where
  toFun w := ⟨dRepC G π Z w, dRepC_mem hG hh hπ Z w.2⟩
  map_add' v w := Subtype.ext <| by
    show dRepC G π Z (v + w) = dRepC G π Z v + dRepC G π Z w
    unfold dRepC
    rw [dRep_add v.2 w.2 (parts_mem hG hh Z).1, dRep_add v.2 w.2 (parts_mem hG hh Z).2]
    module
  map_smul' c w := Subtype.ext <| by
    show dRepC G π Z (c • w) = c • dRepC G π Z w
    unfold dRepC
    rw [dRep_smul c w.2 (parts_mem hG hh Z).1, dRep_smul c w.2 (parts_mem hG hh Z).2]
    module

def gEnd (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : Module.End ℂ (smSub G π) :=
  (π g : H →ₗ[ℂ] H).restrict fun _ hw => rep_mem hG hπ hw hg

theorem gEnd_coe (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (w : smSub G π) : ((gEnd hG hπ hg w : smSub G π) : H) = π g w := rfl

theorem foldr_dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : smSub G π) :
    (((l.map (dEnd hG hh hπ)).prod w : smSub G π) : H) = (l.map (dRepC G π)).foldr (fun f acc => f acc) (w : H) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.foldr_cons, ← ih]
    rfl

theorem gelfH_eq (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) (w : smSub G π) :
    gelfH G π k w =
      ((∑ c, (Matrix.of (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) ^ (k + 1)) c c) w : smSub G π) := by
  rw [← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, Submodule.coe_sum, gelfH]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have := foldr_dEnd hG hh hπ (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) w
  rw [List.map_ofFn, List.map_ofFn] at this
  exact this.symm

theorem gelfH_rep_of (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (hl : ∀ w ∈ smSub G π, RealLin G π w) (k : ℕ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {w : H} (hw : w ∈ smSub G π) : gelfH G π k (π g w) = π g (gelfH G π k w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hQP : gᵀ * (g⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, nonsing_inv_mul _ hd, Matrix.transpose_one]
  have h := GlobalTheory.Dec.GelfAd.trace_pow_comm (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) (gEnd hG hπ hg) _ _ hQP
    (fun a b => by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [Module.End.mul_apply, Module.End.mul_apply]
      refine (dRepC_rep hG hh hπ v.2 hg _).trans ?_
      rw [gEnd_coe]
      congr 1
      rw [dRepC_eq_sum hG hh (hl v v.2)]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      congr 1
      simp [Matrix.mul_apply, Matrix.single, ite_and]) (k + 1)
  have h2 := congrArg (fun T : Module.End ℂ (smSub G π) => ((T ⟨w, hw⟩ : smSub G π) : H)) h
  simp only [Module.End.mul_apply] at h2
  rw [← gelfH_eq] at h2
  refine h2.trans ?_
  rw [gEnd_coe, ← gelfH_eq]

theorem gelfH_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P →
    Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (k : ℕ), ∀ g ∈ Formalism.QuantumDeterminants.UH G,
    ∀ w ∈ smSub G (trRep σ P),
    gelfH G (trRep σ P) k ((trRep σ P) g w) = (trRep σ P) g (gelfH G (trRep σ P) k w) :=
  fun n ε H _ _ _ σ P G hP h hσ k _ hg _ hw =>
    gelfH_rep_of (gram_unit hP h) (gram_herm h) (isURepOn_trRep hP h hσ) (GlobalTheory.T.derived_action_smooth_vector_real_linear n ε H σ P G hP h hσ) k hg hw

end GlobalTheory.SmVecGelfComm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

section General

variable (F : Type) [Field F] [NumberField F]

def ratChar (x : F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))

theorem ratChar_add (x y : F) : ratChar F (x + y) = ratChar F x * ratChar F y := by
  rw [ratChar, ratChar, ratChar, ← Complex.exp_add, map_add (f := _)]
  congr 1
  push_cast
  ring

theorem ratChar_zero : ratChar F 0 = 1 := by simp [ratChar]

theorem norm_ratChar (x : F) : ‖ratChar F x‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((Algebra.trace ℚ F x : ℚ) : ℝ))
  rw [← this, ratChar]
  congr 2
  push_cast
  ring

theorem ratChar_integer (r : 𝓞 F) : ratChar F (r : F) = 1 := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) := Algebra.isIntegral_trace r.isIntegral_coe
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [ratChar, ← hk, eq_intCast, Rat.cast_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem ratChar_of_integral (x : F)
    (h : ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) : ratChar F x = 1 := by
  have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
  rw [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
    FractionalIdeal.mem_one_iff] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ratChar_integer F r

theorem exists_finChar : ∃ χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ, Continuous χ ∧ (∀ y, ‖χ y‖ = 1) ∧
    ∀ x : F, χ (algebraMap F _ x) = ratChar F x := by
  choose e s hs he using GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos
  simp only [one_smul] at he
  have key : ∀ (y : FiniteAdeleRing (𝓞 F) F) (a : F) (w : FiniteAdeleRing (𝓞 F) F),
      (∀ v, w v ∈ v.adicCompletionIntegers F) → y = algebraMap F _ a + w → ratChar F (e y) = ratChar F a := by
    intro y a w hw h
    have h2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (e y - a) = w - s y := by
      rw [map_sub]
      linear_combination h - he y
    have h3 := ratChar_of_integral F (e y - a) fun v => by
      rw [h2]; exact sub_mem (hw v) (hs y v)
    rw [show e y = a + (e y - a) by ring, ratChar_add, h3, mul_one]
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    { toFun := fun y => ratChar F (e y)
      map_zero_eq_one' := (key 0 0 0 (fun v => zero_mem _) (by simp)).trans (ratChar_zero F)
      map_add_eq_mul' := fun x y => by
        rw [← ratChar_add]
        refine key _ _ (s x + s y) (fun v => add_mem (hs x v) (hs y v)) ?_
        rw [map_add (f := _)]
        linear_combination he x + he y }
  refine ⟨χ, ?_, fun y => norm_ratChar F _, fun x => key _ x 0 (fun v => zero_mem _) (add_zero _).symm⟩
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc : Continuous fun z : FiniteAdeleRing (𝓞 F) F => z - y := continuous_id.sub continuous_const
  have hU := ((GlobalTheory.AdLat.OpenLat.isOpen_integral F).preimage hc).mem_nhds (x := y) (by
    intro v
    simp only [sub_self]
    exact zero_mem _)
  refine (continuousAt_const (y := χ y)).congr (Filter.mem_of_superset hU fun z hz => ?_)
  refine (key z (e y) (s y + (z - y)) (fun v => add_mem (hs y v) (hz v)) ?_).symm
  linear_combination he y

theorem exists_char_of_trace (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := by
  obtain ⟨χ, hc, hn, hr⟩ := exists_finChar F
  have him : ∀ x, (L x).im = 0 := by
    have : (fun x => (L x).im) = fun _ => (0 : ℝ) := by
      refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer (Complex.continuous_im.comp hL)
        continuous_const ?_
      funext x
      show (L (algebraMap F _ x)).im = 0
      rw [hT, Complex.ratCast_im]
    exact congrFun this
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun a => Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, Complex.exp_add, AddChar.map_add_eq_mul]
        ring }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := fun x => by
    show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) * χ 0 = _
    rw [AddChar.map_zero_eq_one, mul_one]
  refine ⟨ψ, ⟨?_, fun a => ?_, fun a => ?_, ?_⟩, hinf⟩
  · exact (Complex.continuous_exp.comp (continuous_const.mul (hL.comp continuous_fst))).mul
      (hc.comp continuous_snd)
  · show ‖Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)‖ = 1
    rw [norm_mul, hn, mul_one, Complex.norm_exp]
    simp [him]
  · show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F (algebraMap F _ a))) *
      χ (sndA F (algebraMap F _ a)) = 1
    rw [AlgHom.commutes, AlgHom.commutes, hT, hr, ratChar, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  · have hd : ((Module.finrank ℚ F : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ)))) 0, ?_⟩
    have h := hinf (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ))))
    rw [hT, Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_cancel₀ _ hd, psiInf] at h
    have e : 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ((-(1 / 2) : ℚ) : ℂ) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [h, e, Complex.exp_pi_mul_I]
    norm_num

end General

theorem exists_isStdChar : ∀ D : D7, ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
  obtain ⟨ψ, h1, h2⟩ := exists_char_of_trace D.host.F L (continuous_finsetSum _ fun ρ _ => (hθ ρ).2) fun x => by
    show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace]
  refine ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => ?_⟩
  rw [h2, GlobalTheory.DualPairCompare.sum_infFam θ' hθ', ← GlobalTheory.DualPairCompare.sum_infFam θ hθ]
  rfl

end GlobalTheory.StdAdelicChar

end
end

section

noncomputable section

namespace GlobalTheory.Mem.PlaceVal

section General

open Formalism.L2.DIV Formalism.BasicNotions Formalism.BasicNotions.TH

theorem exists_ext_pol {K K' I W : Type} [Field K] [Field K'] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ} (ι : K →+* K')
    (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) (U : Submodule K (MvPolynomial I K)) (c : U →ₛₗ[σ] W) :
    ∃ c' : MvPolynomial I K' →ₛₗ[σ'] W, ∀ v : U, c' (MvPolynomial.map ι (v : MvPolynomial I K)) = c v := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let _ : Module K' W := Module.compHom W σ'
  let f : MvPolynomial I K' →ₗ[K'] W :=
    (MvPolynomial.basisMonomials I K').constr K' fun m => c (π (MvPolynomial.monomial m 1))
  have hf : ∀ m, f (MvPolynomial.monomial m 1) = c (π (MvPolynomial.monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials I K').constr_basis K' (fun m => c (π (MvPolynomial.monomial m 1))) m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have key : ∀ p : MvPolynomial I K, f (MvPolynomial.map ι p) = c (π p) := fun p => by
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
      have e1 : MvPolynomial.map ι (MvPolynomial.monomial m a) = ι a • MvPolynomial.monomial m (1 : K') := by
        rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      have e2 : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [e1, f.map_smul, hf, e2, π.map_smul, map_smulₛₗ, ← RingHom.congr_fun hσ a]
      rfl
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  refine ⟨{ toFun := f, map_add' := f.map_add, map_smul' := fun a p => f.map_smul a p }, fun v => (key v).trans ?_⟩
  exact congrArg c (LinearMap.congr_fun hπ v)

theorem exists_ext_VV {K K' I W : Type} [Field K] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}
    (ι : K →+* K') (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) {n : ℕ} (lam : I → DomWeight n) (c : VV K lam →ₛₗ[σ] W) :
    ∃ c' : VV K' lam →ₛₗ[σ'] W, ∀ v : VV K lam, ∃ v' : VV K' lam,
      (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) ∧ c' v' = c v := by
  obtain ⟨c', hc⟩ := exists_ext_pol ι σ' hσ (VV K lam) c
  exact ⟨c'.comp (VV K' lam).subtype, fun v => ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩, rfl, hc v⟩⟩

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem exists_coef_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR _ _ i K' _ jL σ' hσ
  obtain ⟨gramR, c0R, c0L, hT⟩ := hR.fam.tie
  obtain ⟨c0', hc⟩ := exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', ⟨gramR, c0R, c0L, hT, hc⟩, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal⟩

end GlobalTheory.Mem.PlaceVal
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_basisInvariant_haar_family_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  first | exact @GlobalTheory.GaugeRef.exists_isHaar_basisInv | exact GlobalTheory.GaugeRef.exists_isHaar_basisInv | (intros; apply GlobalTheory.GaugeRef.exists_isHaar_basisInv <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RefCharValues

theorem sign_zpow_even (z : ℂ) (h : z ≠ 0) (k : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * k) = (z / starRingEnd ℂ z) ^ k := by
  rw [zpow_mul]
  congr 1
  have h1 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using h
  rw [zpow_ofNat, div_pow, h1]
  field_simp

end GlobalTheory.RefCharValues
end
end
