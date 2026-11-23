module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle711
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle713
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ReadAdj

open GlobalTheory.AdelicLatMove

variable {D : D7}

theorem toEAf_onto : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem cF_cF (z : Formalism.IndefR.Datum.EAf D) : cF D (cF D z) = z := by
  obtain ⟨a, rfl⟩ := toEAf_onto z
  exact GlobalTheory.PlaceVec.cF_cF_toEAf a

theorem frMapAdj_smul_eq (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (a : AE D)
    (x : WO S T) : frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((a • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D a) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_half (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {e : AE D}
    {x : WO S T} (hx : IsHalf (cA D e) x) : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
  conv_rhs => rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx]
  rw [frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA]

theorem frMapAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x - y) = frMapAdj S T βS βT x - frMapAdj S T βS βT y := by
  have h := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem frMapAdj_eq_zero (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {x : WO S T}
    (h : frMapAdj S T βS βT x = 0) : x.map (toEAf D) = 0 := by
  have h1 := congrArg (fun N => (S.gram.map (eToEAf D) * βS.val) * N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) h
  simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv
    (GlobalTheory.PlaceVec.gram_map_mul_inv S) βT.mul_inv (GlobalTheory.PlaceVec.gram_map_mul_inv T)] at h1
  ext i j
  have h2 := congrFun (congrFun h1 j) i
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at h2
  have h3 := congrArg (cF D) h2
  rw [cF_cF, map_zero] at h3
  simpa using h3

theorem phi_toEAf_idem {e : AE D} (he : e * e = e) {F : Type} [CommRing F] (φ : Formalism.IndefR.Datum.EAf D →+* F)
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) : φ (toEAf D e) = 1 := by
  have h : toEAf D e * (toEAf D e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  have := (hker _).2 h
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this

theorem finPart_eq_zero_of_toEAf {a : AE D} (h : toEAf D a = 0) : finPart D a = 0 :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (by rw [map_zero]; exact h)

theorem gram_inv_map_mul (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.PlaceVec.gram_map_mul_inv S)

theorem rdAdj_read : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)),
    Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι →
    (∀ m, ∃ x : WO S T, IsHalf (cA D e) x ∧ rdAdj S T βS βT φ x = m) ∧
    (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → rdAdj S T βS βT φ x = rdAdj S T βS βT φ x' → x = x') ∧
    (∀ x : WO S T, IsHalf (cA D e) x → (IsIntM (frMapAdj S T βS βT x) ↔
      ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))) ∧
    ∀ (x : WO S T) (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), IsIntM (frMapAdj S T βS βT x) →
      rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) →
      (redM PP (frMapAdj S T βS βT x)).map ι = z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) := by
  intro D S T βS βT e PP v φ ι hI hL
  obtain ⟨hsurj, hker, hint, hred⟩ := hL
  have hs : IsSplitIdem D e := hI.1
  have hc : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have h1 : φ (toEAf D e) = 1 := phi_toEAf_idem hs.1 φ hker
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    choose N hN using fun i j => hsurj (m i j)
    set Q : Matrix (Fin S.rank) (Fin T.rank) (Formalism.IndefR.Datum.EAf D) :=
      (S.gram.map (eToEAf D) * βS.val) * Matrix.of N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D)) with hQ
    choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) => toEAf_onto (Q j i)
    set x' : WO S T := Matrix.of fun i j => cA D (w i j) with hx'
    have hfx : frMapAdj S T βS βT x' = Matrix.of N := by
      rw [GlobalTheory.PlaceVec.frMapAdj_eq]
      have hX : ((x'.map (toEAf D)).map (cF D))ᵀ = Q := by
        ext i j
        simp only [Matrix.transpose_apply, Matrix.map_apply, hx', Matrix.of_apply, toEAf_cA, cF_cF, hw]
      rw [hX, hQ]
      exact GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ (gram_inv_map_mul S) βS.inv_mul (gram_inv_map_mul T)
        βT.inv_mul
    refine ⟨cA D e • x', fun i j => ?_, ?_⟩
    · show cA D e * (cA D e * x' i j) = cA D e * x' i j
      rw [← mul_assoc, hc.1]
    · ext i j
      simp only [rdAdj, Matrix.map_apply, frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA, hfx, Matrix.smul_apply,
        smul_eq_mul, map_mul, Matrix.of_apply, hN]
      rw [show φ (toEAf D e) = 1 from h1, one_mul]
  · intro x x' hx hx' h
    have hd : IsHalf (cA D e) (x - x') := fun i j => by
      show cA D e * (x i j - x' i j) = x i j - x' i j
      rw [mul_sub, hx i j, hx' i j]
    have h0 : frMapAdj S T βS βT (x - x') = 0 := by
      ext i j
      have e1 := congrFun (congrFun h i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT (x - x') i j) = 0 := by
        rw [frMapAdj_sub, Matrix.sub_apply, map_sub, e1, sub_self]
      have e3 := (hker _).1 e2
      have e4 := congrFun (congrFun (frMapAdj_half S T βS βT hd) i) j
      rw [Matrix.smul_apply, smul_eq_mul, e3] at e4
      rw [← e4, Matrix.zero_apply]
    have hf := frMapAdj_eq_zero S T βS βT h0
    have hinf := GlobalTheory.SplitScalar.half_fin hc hd
    ext i j
    refine sub_eq_zero.1 (GlobalTheory.SplitScalar.adele_ext ?_ ?_)
    · have := congrFun (congrFun hinf i) j
      rw [map_zero]; exact this
    · rw [map_zero]
      exact finPart_eq_zero_of_toEAf (congrFun (congrFun hf i) j)
  · intro x hx
    have hh := fun i j => congrFun (congrFun (frMapAdj_half S T βS βT hx) i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    constructor
    · intro hI'
      refine ⟨Matrix.of fun i j => ⟨φ (frMapAdj S T βS βT x i j), (hint _).1 (by rw [hh i j]; exact hI' i j)⟩, ?_⟩
      ext i j
      rfl
    · rintro ⟨z, hz⟩ i j
      have e1 := congrFun (congrFun hz i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT x i j) ∈ v.adicCompletionIntegers D.host.F := by
        rw [e1]; exact (z i j).2
      rw [← hh i j]
      exact (hint _).2 e2
  · intro x z hI' hz
    ext i j
    have e1 := congrFun (congrFun hz i) j
    simp only [rdAdj, Matrix.map_apply] at e1
    simp only [Matrix.map_apply, redM, dif_pos (hI' i j)]
    exact hred ⟨_, hI' i j⟩ (z i j) e1.symm

end GlobalTheory.DownLift.ReadAdj

end
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

namespace FrobPP

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O)

theorem coeff_natCast_mul_double {R : Type} [CommRing R] (m : ℕ) (G : R⟦X⟧⟦X⟧) (i n : ℕ) :
    coeff n (coeff i ((m : R⟦X⟧⟦X⟧) * G)) = (m : R) * coeff n (coeff i G) := by
  rw [← map_natCast (C : R⟦X⟧ →+* R⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : R →+* R⟦X⟧), coeff_C_mul]

theorem ofW_add (w w' : ℕ × ℕ → Wq l a) : ofW t K e (w + w') = ofW t K e w + ofW t K e w' := by
  funext τ; ext i n; simp [coeff_ofW, add_div]

theorem ofW_zero : ofW t K e (0 : ℕ × ℕ → Wq l a) = 0 := by
  funext τ; ext i n; simp [coeff_ofW]

theorem ofW_neg (w : ℕ × ℕ → Wq l a) : ofW t K e (-w) = -ofW t K e w := by
  funext τ; ext i n; simp [coeff_ofW, neg_div]


variable (K e) in
def ofWHom : (ℕ × ℕ → Wq l a) →+ (ZMod a → K⟦X⟧⟦X⟧) where
  toFun := ofW t K e
  map_zero' := ofW_zero t
  map_add' := ofW_add t

theorem Q_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x + y ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; obtain ⟨w', rfl⟩ := hy; exact ⟨w + w', ofW_add t w w'⟩

theorem Q_neg {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) : -x ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; exact ⟨-w, ofW_neg t w⟩

theorem Q_sub {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x - y ∈ QSet t K e := by
  rw [sub_eq_add_neg]; exact Q_add t hx (Q_neg t hy)

theorem Q_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := ⟨0, ofW_zero t⟩

theorem Q_natCast (m : ℕ) : (m : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨Pi.single (0, 0) (m : Wq l a), funext fun τ => ?_⟩
  ext i n
  rw [coeff_ofW, Pi.natCast_apply, ← mul_one ((m : K⟦X⟧⟦X⟧)), coeff_natCast_mul_double]
  rcases i with _ | i <;> rcases n with _ | n <;> simp [dpDen, Pi.single_apply, coeff_one]

theorem Q_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x * y ∈ QSet t K e :=
  GlobalTheory.T.mul_mem_crystallinePrismDividedPowerFamilies l a e O K t x hx y hy

theorem Q_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (k : ℕ) : x ^ k ∈ QSet t K e := by
  induction k with
  | zero => simpa using Q_natCast t (K := K) (e := e) 1
  | succ k ih => rw [pow_succ]; exact Q_mul t ih hx

theorem Q_sum {ι : Type} (s : Finset ι) (f : ι → ZMod a → K⟦X⟧⟦X⟧) (h : ∀ i ∈ s, f i ∈ QSet t K e) :
    ∑ i ∈ s, f i ∈ QSet t K e :=
  Finset.sum_induction f (· ∈ QSet t K e) (fun _ _ => Q_add t) (Q_zero t) h

variable {φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧}

theorem good_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x + y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_add t hxQ hyQ, by rw [map_add (f := _)]; exact Q_add t hfxQ hfyQ,
    A + B - x * y * ∑ k ∈ Finset.Ioo 0 l, x ^ (k - 1) * y ^ (l - k - 1) * ((l.choose k / l : ℕ) : ZMod a → K⟦X⟧⟦X⟧),
    ?_, ?_⟩
  · exact Q_sub t (Q_add t hA hB) (Q_mul t (Q_mul t hxQ hyQ) (Q_sum t _ _ fun k _ =>
      Q_mul t (Q_mul t (Q_pow t hxQ _) (Q_pow t hyQ _)) (Q_natCast t _)))
  · rw [map_add (f := _), hxA, hyB, add_pow_prime_eq hl.out]; ring

theorem good_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x * y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_mul t hxQ hyQ, by rw [map_mul]; exact Q_mul t hfxQ hfyQ,
    A * y ^ l + B * x ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * A * B, ?_, ?_⟩
  · exact Q_add t (Q_add t (Q_mul t hA (Q_pow t hyQ _)) (Q_mul t hB (Q_pow t hxQ _)))
      (Q_mul t (Q_mul t (Q_natCast t _) hA) hB)
  · rw [map_mul, hxA, hyB]; ring

theorem good_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨Q_zero t, by rw [map_zero]; exact Q_zero t, 0, Q_zero t, by simp [zero_pow hl.out.ne_zero]⟩

theorem good_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨by simpa using Q_natCast t (K := K) (e := e) 1, by rw [map_one]; simpa using Q_natCast t (K := K) (e := e) 1,
    0, Q_zero t, by simp⟩

theorem good_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (k : ℕ) : x ^ k ∈ GoodSet t e φ₂ := by
  induction k with
  | zero => rw [pow_zero]; exact good_one t
  | succ k ih => rw [pow_succ]; exact good_mul t ih hx

theorem good_fin (hφC : ∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) (hφX : φ₂ X = (C X + X) ^ l - C (X ^ l))
    (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)) :
    ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂ := by
  have h : (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, Pi.single p (w p) := by
    funext q; rw [Finset.sum_apply]; simp [Pi.single_apply, Finset.sum_ite_eq']
  have h2 : ofW t K e (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, ofW t K e (Pi.single p (w p)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h]; exact map_sum (ofWHom (K := K) (e := e) t) _ s
  rw [h2]
  refine Finset.sum_induction _ (· ∈ GoodSet t e φ₂) (fun _ _ => good_add t) (good_zero t) fun p _ => ?_
  rw [GlobalTheory.T.dividedPowerFamily_single_eq_mul l a e O K t p.1 p.2 (w p)]
  exact good_mul t (good_mul t (good_mul t (GlobalTheory.T.constantCoeffFamily_frobenius_congr_pow l a e O K t φ₂ hφC hφX _)
    (good_pow t (GlobalTheory.T.uniformizerFamily_frobenius_congr_pow l a e O K t φ₂ hφC hφX) _)) (GlobalTheory.T.dividedUniformizerPower_frobenius_congr_pow l a e O K t φ₂ hφC hφX _))
    (GlobalTheory.T.dividedVariablePower_frobenius_congr_pow l a e O K t φ₂ hφC hφX (fun x hx y hy => Q_mul t hx hy) _)

theorem ofW_mem_PPSet {w : ℕ × ℕ → Wq l a} (hw : LTo0 l w) : ofW t K e w ∈ PPSet t K e := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨w, hw, fun τ i n => ?_⟩
  rw [coeff_ofW]
  have : ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
  exact mul_div_cancel₀ _ this

end Main

theorem frob_mem_PPSet_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ F ∈ PPSet t K e, frob2 φ₂ F ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, frob2 φ₂ F = F ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh φ₂ hφC hφsh F hF
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hφX : φ₂ X = (C X + X) ^ l - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    have h2 : φ₂ X = sh (X ^ l) - C (X ^ l) := by rw [h, map_sub, hφsh, hφC, frob_X]
    rw [h2, map_pow, sh_X sh hsh]
  obtain ⟨w, hw, hFw⟩ := hF
  have hF' : F = ofW t K e w := funext fun τ => by
    ext i n
    have h0 : ((dpDen e i n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
    rw [coeff_ofW, eq_div_iff h0, mul_comm]
    exact hFw τ i n
  have hQ := GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower l a e O K t φ₂ (good_fin t hφC hφX) (GlobalTheory.T.coeff_frobeniusDoublePowerSeries_congr_box l K φ₂ hφC hφX) (fun i n G H => GlobalTheory.T.coeff_coeff_pow_eq_of_coeff_coeff_eq_le K l i n G H)
  obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hQ F ⟨w, hF'.symm⟩
  rw [hF'] at hv hB ⊢
  obtain ⟨hv0, hb0⟩ := GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower l a e O K t φ₂ (GlobalTheory.T.unramifiedWittEmbeddingTwisted_algebraMap_injective l a e O K t) (fun x hx y hy => Q_mul t hx hy) hQ
    (GlobalTheory.T.frobenius_pow_mem_finiteSupportDoublePowerSeries l a e O K t φ₂ hφC hφX) w hw v b hv.symm hB
  exact ⟨hv ▸ ofW_mem_PPSet t hv0, ofW t K e b, ofW_mem_PPSet t hb0, hB⟩

end FrobPP

end GlobalTheory.CrysPrism
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.taylor_formula_pi_invPrime_mod_eisenstein_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → ∀ R : ℕ, GlobalTheory.GalStep.galOD O g (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ))) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (descN K i (f τ))) ∈ Ideal.span {GlobalTheory.GalStep.ED K t ϖ ^ R} := by
  first | exact @GlobalTheory.GalStep.taylor_iD_mod_ED | exact GlobalTheory.GalStep.taylor_iD_mod_ED | (intros; apply GlobalTheory.GalStep.taylor_iD_mod_ED <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)), IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧ infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  first | exact @GlobalTheory.IdemSumBranch.branch | exact GlobalTheory.IdemSumBranch.branch | (intros; apply GlobalTheory.IdemSumBranch.branch <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.RedAt

theorem redFn_finE_eq_one : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (PP : Pl D.host.E), finE W k ∈ St β → (∀ a b, Valued.v (GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b)) < 1) → redFn β PP (finE W k) = 1 := by
  intro D W β k PP hk hv
  obtain ⟨y, hy⟩ := hk
  have hyv : (Formalism.L2.DIV.intGL _ _ _ y).val
      = (HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val :
          Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) := by
    have h2 : Formalism.L2.DIV.intGL _ _ _ y = β⁻¹ * finE W k * β := by
      rw [← hy]; simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, mul_assoc]
    rw [h2]; rfl
  rw [← hy, GlobalTheory.LiftLevel.redFn_eq_one_iff]
  intro i j
  rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
  have := hv i j
  rw [← hyv] at this
  convert this using 3
  simp [Matrix.sub_apply, Matrix.one_apply, Formalism.L2.DIV.intGL, Formalism.UG.bc]
  split_ifs <;> simp

end GlobalTheory.RedAt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  first | exact @GlobalTheory.SplitStabFrame.finE_mem_St_of_split | exact GlobalTheory.SplitStabFrame.finE_mem_St_of_split | (intros; apply GlobalTheory.SplitStabFrame.finE_mem_St_of_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  first | exact @GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF | exact GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF | (intros; apply GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  first | exact @GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | exact GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | (intros; apply GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm <;> assumption)
end
