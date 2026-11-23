module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle020
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartPhiE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin

namespace SplitChar

theorem exists_place_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at hn
    have hr : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℤ (𝓞 F) := pow_le_pow_right₀ (by norm_num) hr
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h2mem : (2 : 𝓞 F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h0 : (2 : 𝓞 F) = 0 := (Submodule.mem_bot _).mp h2mem
    have h0' : (2 : F) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0
      rwa [map_ofNat, map_zero] at this
    exact two_ne_zero h0'
  exact ⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩

theorem exists_splitIdem_D (D : D7) : ∃ e, IsSplitIdem D e := by
  obtain ⟨v, hv⟩ := exists_place_two D.host.F
  obtain ⟨e, ε, he, -, -⟩ := twoSplitIdem D v hv
  exact ⟨e, he⟩

variable {D : D7}

end SplitChar

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem hO_add_left (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_add_left (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO
  rw [hO_add_left, mul_add, map_add (f := _)]

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add (f := _)]

theorem symplO_zero_left (y : WO S T) : symplO S T 0 y = 0 := by
  have h := symplO_add_left S T 0 0 y
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_zero_right (x : WO S T) : symplO S T x 0 = 0 := by
  have h := symplO_add_right S T x 0 0
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_add_left S T x (-x) y
  have h0 : x + -x = 0 := by simp
  rw [h0, symplO_zero_left] at h
  linear_combination -1 * h

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  have h0 : y + -y = 0 := by simp
  rw [h0, symplO_zero_right] at h
  linear_combination -1 * h

abbrev MO : Type := Matrix (Fin T.rank) (Fin S.rank) (AE D)

def hOM (x y : MO S T) : Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
  HMul.hMul (HMul.hMul (HMul.hMul (Brg.GI S) (y.map (cA D))ᵀ) (Brg.GG T)) x

theorem hO_eq_trace (x y : MO S T) : hO S T x y = (hOM S T x y).trace := by
  unfold hO hOM
  simp only [Brg.GI, Brg.GG, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext d; rw [Finset.sum_comm]

theorem cA_trace {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) : cA D M.trace = ((M.map (cA D))ᵀ).trace := by
  rw [Matrix.trace_transpose]

  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem hO_swap (x y : MO S T) : hO S T y x = cA D (hO S T x y) := by
  have e0 : (y.map (cA D)).map (cA D) = y := by ext i j; simp [cA_cA]
  have e2 : ((hOM S T x y).map (cA D))ᵀ =
      HMul.hMul (HMul.hMul (HMul.hMul (x.map (cA D))ᵀ (Brg.GG T)) y) (Brg.GI S) := by
    unfold hOM
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Brg.GI_herm, Brg.GG_herm, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, cA_trace, e2, Matrix.trace_mul_comm]
  unfold hOM
  simp only [Matrix.mul_assoc]

theorem symplO_swap (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [hO_swap S T x y]
  have e : incA D D.host.xi0 * cA D (hO S T x y) = cA D (cA D (incA D D.host.xi0) * hO S T x y) := by
    rw [map_mul, cA_cA]
  rw [e, Brg.trace_cA, Brg.cA_inc, Brg.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_add_left (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH
  rw [symplO_add_left, mul_add]

theorem symplOH_add_right (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH
  rw [symplO_add_right, mul_add]

theorem symplOH_swap (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_swap, mul_neg]

theorem symplOH_two (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem incA_eq_tmul (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem trace_incA (e : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  rw [incA_eq_tmul]
  exact Formalism.IndefR.PHeisTh.trace_tmul _

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E :=
  Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
    show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (a ⊗ₜ[D.host.F] w)) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    show a ⊗ₜ[D.host.F] star (star w) = _
    rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finPart_cA (z : AE D) : finPart D (cA D z) = cF D (finPart D z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a w => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cF_int {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) : cF D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a, ha, starO y, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem cF_cF (z : Af D.host.F ⊗[D.host.F] D.host.E) : cF D (cF D z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
    show a ⊗ₜ[D.host.F] star (star w) = _
    rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem intAf_mul {a a' : Af D.host.F} (ha : a ∈ intAf D.host.F) (ha' : a' ∈ intAf D.host.F) :
    a * a' ∈ intAf D.host.F := fun w => by rw [map_mul]; exact mul_mem (ha w) (ha' w)

theorem intAE_mul {z z' : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) (hz' : z' ∈ intAE D) :
    z * z' ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    induction hz' using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨a', ha', y', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨a * a', intAf_mul ha ha', y * y', by push_cast; rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx



theorem idem_class (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P)
    (e₀ : AE D) (ι : D.host.E →ₐ[D.host.F] (belowPl P).adicCompletion D.host.F)
    (hs₀ : e₀ + cA D e₀ = phiE (belowPl P) 1)
    (hz : ∀ z : AE D, z * e₀ = e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D z)))
    (hκ : compV (belowPl P) ι (finPart D e₀) = 1) (he₀ : e₀ * e₀ = e₀) (hc₀ : e₀ * cA D e₀ = 0)
    (e : AE D) (h1 : e * e = e) (h2 : e * cA D e = 0) (h3 : e + cA D e = phiE (belowPl P) 1) :
    e = e₀ ∨ e = cA D e₀ := by
  have hκφ : compV (belowPl P) ι (finPart D (phiE (belowPl P) 1)) = 1 := compV_phiE (belowPl P) ι 1
  have hsum : compV (belowPl P) ι (finPart D e) + compV (belowPl P) ι (finPart D (cA D e)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), h3, hκφ]
  have hidem : compV (belowPl P) ι (finPart D e) * compV (belowPl P) ι (finPart D e) =
      compV (belowPl P) ι (finPart D e) := by rw [← map_mul, ← map_mul, h1]
  have heps : e * phiE (belowPl P) 1 = e := by rw [← h3, mul_add, h1, h2, add_zero]
  have heps₀ : e₀ * phiE (belowPl P) 1 = e₀ := by rw [← hs₀, mul_add, he₀, hc₀, add_zero]
  have hceps₀ : cA D e₀ * phiE (belowPl P) 1 = cA D e₀ := by
    have := congrArg (cA D) heps₀; rwa [map_mul, cA_phiE] at this
  have hA := hz e
  have hB : e * cA D e₀ = cA D e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D (cA D e))) := by
    have := congrArg (cA D) (hz (cA D e))
    rwa [map_mul, map_mul, cA_cA, cA_phiE] at this
  have hdec : e = e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D e)) +
      cA D e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D (cA D e))) := by
    linear_combination hA + hB - e * hs₀ - heps
  have hq : compV (belowPl P) ι (finPart D e) * (compV (belowPl P) ι (finPart D e) - 1) = 0 := by
    linear_combination hidem
  rcases mul_eq_zero.1 hq with h0 | h1''
  · right
    have hc1 : compV (belowPl P) ι (finPart D (cA D e)) = 1 := by rw [h0, zero_add] at hsum; exact hsum
    rw [hdec, h0, hc1, phiE_zero, mul_zero, zero_add, hceps₀]
  · left
    have h1' : compV (belowPl P) ι (finPart D e) = 1 := by linear_combination h1''
    have hc0 : compV (belowPl P) ι (finPart D (cA D e)) = 0 := by rw [h1'] at hsum; linear_combination hsum
    rw [hdec, h1', hc0, phiE_zero, mul_zero, add_zero, heps₀]

theorem sglV_orth {F : Type} [Field F] [NumberField F] {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) :
    sglV v (1 : v.adicCompletion F) * sglV w 1 = 0 := by
  apply af_ext; intro u
  rw [map_mul, map_zero]
  by_cases hu : u = v
  · subst hu; rw [sglV_ne w _ h, mul_zero]
  · rw [sglV_ne v _ hu, zero_mul]

theorem phiE_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) : phiE (D := D) v 1 * phiE w 1 = 0 := by
  unfold phiE
  rw [← map_mul]
  have : sA v 1 * sA w 1 = 0 := Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (sglV_orth h)
  rw [this, map_zero]

theorem placeIdem_eq {w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D w ε) : ε = sA w 1 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α = sglV w 1 := by
    apply af_ext; intro u
    by_cases hu : u = w
    · subst hu; rw [h1, sglV_same]
    · rw [h0 u hu, sglV_ne w _ hu]
  rw [this]; rfl

theorem below_of_idemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) :
    e + cA D e = phiE (belowPl P) 1 := by
  obtain ⟨⟨h1, h2, w, ε, hpl, hs⟩, hcl⟩ := he
  rw [placeIdem_eq hpl] at hs
  change e + cA D e = phiE w 1 at hs
  by_cases hw : w = belowPl P
  · rw [← hw]; exact hs
  exfalso
  have heps : e * phiE w 1 = e := by rw [← hs, mul_add, h1, h2, add_zero]
  have hint : finPart D e ∈ intAE D := by
    have h := hcl 1 one_ne_zero
    have h1P : (1 : 𝓞 D.host.E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    have := not_not.1 (mt h.2 h1P)
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E)⁻¹ = 1 by simp, map_one, mul_one] at this
  have hne : ¬ (belowPl P).asIdeal ≤ w.asIdeal := by
    intro hle
    apply hw
    exact (HeightOneSpectrum.ext ((belowPl P).isMaximal.eq_of_le w.isPrime.ne_top hle)).symm
  obtain ⟨x, hxv, hxw⟩ := Set.not_subset.1 hne
  have hx0 : x ≠ 0 := fun h => hxw (h ▸ zero_mem _)
  have hy : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal := hxv
  have hy0 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]; exact hx0
  have hnot := (hcl _ hy0).1 hy
  apply hnot
  have hxF : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E)⁻¹ =
      algebraMap D.host.F D.host.E ((x : D.host.F)⁻¹) := by rw [algebraMap_O, map_inv₀]
  have hv1 : Valued.v (((x : D.host.F) : w.adicCompletion D.host.F)) = 1 :=
    le_antisymm (val_coe_le_one w x) (not_lt.1 fun h => hxw ((val_coe_lt_one_iff w x).1 h))
  obtain ⟨c, hc⟩ : ∃ c : w.adicCompletion D.host.F, c = algebraMap D.host.F (w.adicCompletion D.host.F) ((x : D.host.F)⁻¹) * 1 :=
    ⟨_, rfl⟩
  have hc1 : Valued.v c ≤ 1 := by
    rw [hc, mul_one, map_inv₀, algebraMap_adic_eq, map_inv₀, hv1, inv_one]
  rw [hxF, incA_alg, ← heps, mul_assoc, mul_comm (phiE w 1), phiE_smul, ← hc, map_mul, finPart_phiE]
  exact intAE_mul hint (AddSubgroup.subset_closure ⟨sglV w c, sglV_int w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ w).2 hc1), 1, by simp⟩)

theorem cA_mul_incA (z : AE D) (x : D.host.E) : cA D (z * incA D x) = cA D z * incA D (star x) := by
  rw [map_mul, cA_incA]

theorem conj_of_cA {P Q : HeightOneSpectrum (𝓞 D.host.E)} {e e' : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P)
    (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hc : e' = cA D e) : Lev.IsConjPl (D := D) P Q := by
  intro x hx
  refine ⟨starO x, ?_, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    have : starO (0 : 𝓞 D.host.E) = 0 := FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (by
      show star ((0 : 𝓞 D.host.E) : D.host.E) = _; simp)
    rw [this]; exact zero_mem _
  have hs0 : starO x ≠ 0 := by
    intro h; apply hx0
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    have : star ((x : 𝓞 D.host.E) : D.host.E) = 0 := congrArg (fun y : 𝓞 D.host.E => (y : D.host.E)) h
    simpa using this
  rw [he'.2 _ hs0, hc]
  intro hmem
  apply (he.2 x hx0).1 hx
  have : finPart D (cA D e * incA D ((starO x : D.host.E)⁻¹)) = cF D (finPart D (e * incA D ((x : D.host.E)⁻¹))) := by
    rw [← finPart_cA, cA_mul_incA, coe_starO, star_inv₀]
  rw [this] at hmem
  have := cF_int hmem
  rwa [cF_cF] at this

end Formalism.IndefR.Fin

end
end
