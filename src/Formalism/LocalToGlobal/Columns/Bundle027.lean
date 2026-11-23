module

public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.Bundle015
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.Columns.TwQLevU
public import Formalism.LocalToGlobal.Columns.Bundle009
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.QthExistsBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (φ : E →+* v.adicCompletion F)
  (hint : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) ≤ 1)
  (hPv : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal)
  (hF : ∀ x : F, φ (algebraMap F E x) = algebraMap F (v.adicCompletion F) x)
  (hvP : IsOver v P)

theorem qsp_approx (D : 𝓞 F) (hD : D ≠ 0) (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ (r : 𝓞 F) (y : v.adicCompletion F), y ∈ v.adicCompletionIntegers F ∧
      x = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) D * y := by
  obtain ⟨r, y, hy, e⟩ := integral_adele_approximation_holds F D hD (afsplitI v x) (afsplitI_mem_intAd v _ hx)
  refine ⟨r, y v, hy v, ?_⟩
  have := congrArg (fun z : Formalism.L2.Herm.Af F => z v) e
  rw [afsplitI_self] at this
  exact this

theorem qsp_std_mulVec {M : Matrix (Fin n) (Fin n) (𝓞 F)} {x : Sp E n} (hx : x ∈ stdLat E n) :
    (M.map (algebraMap (𝓞 F) E)).mulVec x ∈ stdLat E n := by
  intro i _
  have h : ∀ j, x j ∈ (1 : Submodule (𝓞 E) E) := fun j => hx j trivial
  show (M.map (algebraMap (𝓞 F) E)).mulVec x i ∈ (1 : Submodule (𝓞 E) E)
  rw [Matrix.mulVec, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j)
  refine Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 E) (M i j) * a, ?_⟩
  rw [Matrix.map_apply, ← ha, map_mul, ← IsScalarTower.algebraMap_apply]



include hint hPv hF hvP in
theorem qsp_dense (D : 𝓞 F) (hD : D ≠ 0) (hDv : D ∈ v.asIdeal) (k : GL (Fin n) (v.adicCompletion F))
    (hk : qbInt (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hk' : qbInt ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    ∃ g : ↥(GLint E n P), (qbIota P φ g)⁻¹ * k ∈ qbK (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  classical
  choose r y hy e using fun i j => qsp_approx D hD ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) (hk i j)
  let R : Matrix (Fin n) (Fin n) (𝓞 F) := fun i j => r i j
  let ME : Matrix (Fin n) (Fin n) E := R.map (algebraMap (𝓞 F) E)
  let O := v.adicCompletionIntegers F
  have hDval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by
    rw [csApprox_val_int]; exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v D).2 hDv

  let kO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, hk i j⟩
  let kiO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, hk' i j⟩
  let RO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, glo_algMap_int v (r i j)⟩
  have hkk : kO * kiO = 1 := by
    have h1 : (O.subtype).mapMatrix (kO * kiO) = (O.subtype).mapMatrix 1 := by
      rw [map_mul, map_one]
      show ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h1 i) j)
  have hdetk : IsUnit kO.det := Matrix.isUnit_det_of_right_inverse hkk
  have hres : (IsLocalRing.residue O).mapMatrix kO = (IsLocalRing.residue O).mapMatrix RO := by
    ext i j
    show IsLocalRing.residue O (kO i j) = IsLocalRing.residue O (RO i j)
    rw [← sub_eq_zero, ← map_sub]
    apply glo_res_zero v
    show Valued.v ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - algebraMap (𝓞 F) (v.adicCompletion F) (r i j)) < 1
    rw [e i j, add_sub_cancel_left, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy i j))) hDval
  have hRO : IsLocalRing.residue O RO.det ≠ 0 := by
    rw [RingHom.map_det, ← hres, ← RingHom.map_det]
    exact (hdetk.map (IsLocalRing.residue O)).ne_zero
  have hROval : ((RO.det : O) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) R.det := by
    have h1 : (O.subtype).mapMatrix RO = (algebraMap (𝓞 F) (v.adicCompletion F)).mapMatrix R := rfl
    have h2 := RingHom.map_det (O.subtype) RO
    rw [h1, ← RingHom.map_det] at h2
    exact h2
  have hdetv : R.det ∉ v.asIdeal := fun h => by
    apply hRO
    apply glo_res_zero v
    rw [hROval, csApprox_val_int]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 h
  have hdetE : ME.det = algebraMap (𝓞 F) E R.det := (RingHom.map_det _ R).symm
  have hdet0 : ME.det ≠ 0 := by
    rw [hdetE]
    intro h0
    apply hdetv
    have : R.det = 0 := by
      have hinj : Function.Injective (algebraMap (𝓞 F) E) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 F) F E]
        exact (algebraMap F E).injective.comp (IsFractionRing.injective (𝓞 F) F)
      exact hinj (by rw [h0, map_zero])
    rw [this]; exact zero_mem _
  have hdetP : algebraMap (𝓞 F) (𝓞 E) R.det ∉ P.asIdeal := fun h => hdetv (by rw [hvP]; exact h)
  let Mu : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero ME hdet0
  let g : Sp E n ≃ₗ[E] Sp E n := (toGLm E n).symm Mu
  have hgx : ∀ x, g x = ME.mulVec x := fun x => rfl
  have hg : g ∈ GLint E n P := by
    intro x
    rw [hgx]
    constructor
    · intro hx
      obtain ⟨s, hs, hsx⟩ := (qsp_mem_locP P).1 hx
      refine (qsp_mem_locP P).2 ⟨s * algebraMap (𝓞 F) (𝓞 E) R.det, P.asIdeal.primeCompl.mul_mem hs hdetP, ?_⟩
      have h1 : (ME.adjugate).mulVec (s • ME.mulVec x) = (s * algebraMap (𝓞 F) (𝓞 E) R.det) • x := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
          hdetE, mul_smul]
        congr 1
      rw [← h1]
      have hadj : ME.adjugate = R.adjugate.map (algebraMap (𝓞 F) E) := (RingHom.map_adjugate _ R).symm
      rw [hadj]
      exact qsp_std_mulVec hsx
    · intro hx
      obtain ⟨s, hs, hsx⟩ := (qsp_mem_locP P).1 hx
      refine (qsp_mem_locP P).2 ⟨s, hs, ?_⟩
      rw [← Matrix.mulVec_smul]
      exact qsp_std_mulVec hsx
  refine ⟨⟨g, hg⟩, ?_⟩
  have hιg : ∀ i j, ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j =
      algebraMap (𝓞 F) (v.adicCompletion F) (r i j) := fun i j => by
    rw [qbIota_apply]
    have hM : toGLm E n g = Mu := (toGLm E n).apply_symm_apply Mu
    rw [show ((⟨g, hg⟩ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) = g from rfl, hM]
    show φ (ME i j) = _
    show φ (algebraMap (𝓞 F) E (r i j)) = _
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, hF, ← IsScalarTower.algebraMap_apply]
  have hι1 := qbIota_int P φ hint hPv ⟨g, hg⟩
  have hι2 := qbIota_int_inv P φ hint hPv ⟨g, hg⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact qbInt_mul hι2 hk
  · rw [mul_inv_rev, inv_inv, Units.val_mul]; exact qbInt_mul hk' hι1
  · have hh : (((qbIota P φ ⟨g, hg⟩)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : (((qbIota P φ ⟨g, hg⟩)⁻¹ * k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - 1 =
        (((qbIota P φ ⟨g, hg⟩)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
          ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) := by
      rw [Units.val_mul, _root_.mul_sub, hh]
    rw [e2]
    refine qbDiv_mul_left hι2 fun i j => ⟨y i j, hy i j, ?_⟩
    rw [Matrix.sub_apply, hιg, e i j, add_sub_cancel_left]

end Dense

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Approx

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem tfVal_mem {u : 𝓞 E} {N : ℕ} (hu : u ∈ P.asIdeal ^ N) : P.valuation E (algebraMap (𝓞 E) E u) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem P u N).mpr hu

theorem tfApprox (a : E) (ha : P.valuation E a ≤ 1) (N : ℕ) : ∃ r : 𝓞 E, P.valuation E (a - algebraMap (𝓞 E) E r) ≤ WithZero.exp (-(N : ℤ)) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := by
    first
      | exact pow_ne_zero _ P.ne_bot
  obtain ⟨t, htP, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPN
  have hc : algebraMap E (P.adicCompletion E) a ∈ P.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  obtain ⟨r, hr⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_local P
    (algebraMap E (P.adicCompletion E) a) hc t ht0
  refine ⟨r, ?_⟩
  rw [← map_sub] at hr
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hr
  exact hr.trans ((HeightOneSpectrum.intValuation_le_pow_iff_mem P t N).mpr htP)

end Approx

section Idx

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : ℕ)

def tfRed (g : ↥(GLint E n P)) : Fin n → Fin n → 𝓞 E ⧸ P.asIdeal ^ N := fun i j =>
  Ideal.Quotient.mk _ (tfApprox P _ (qsp_entry_int P g i j) N).choose

theorem tfRed_eq {g g' : ↥(GLint E n P)} (h : tfRed P N g = tfRed P N g') : lqPrinc P N ((g⁻¹ * g' : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  classical
  have hmat : ∀ x : ↥(GLint E n P), ((toGLm E n x.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      LinearMap.toMatrix' ((x.1 : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) := fun x => rfl
  have hclose : ∀ l k, P.valuation E (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k) ≤ WithZero.exp (-(N : ℤ)) := by
    intro l k
    have hr := (tfApprox P _ (qsp_entry_int P g l k) N).choose_spec
    have hr' := (tfApprox P _ (qsp_entry_int P g' l k) N).choose_spec
    have hmk := congrFun (congrFun h l) k
    simp only [tfRed] at hmk
    have hrr := tfVal_mem P (Ideal.Quotient.eq.mp hmk)
    rw [map_sub] at hrr
    have e : ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
        ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k =
        (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
          algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
        (-(algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
          -(((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose)) := by ring
    rw [e]
    refine Valuation.map_add_le _ hr' (Valuation.map_add_le _ ?_ ?_)
    · rw [Valuation.map_neg]
      exact hrr
    · rw [Valuation.map_neg]
      exact hr
  have hM1 : ((toGLm E n (g⁻¹ * g').1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    rw [Subgroup.coe_mul, map_mul, Units.val_mul]
  have hM2 : ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, map_one,
      Units.val_one]
  intro i j
  rw [← hmat (g⁻¹ * g'), hM1, ← hM2, ← Matrix.mul_sub, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul, Matrix.sub_apply]
  exact le_trans (mul_le_of_le_one_left' (qsp_entry_int P g⁻¹ i l)) (hclose l j)

theorem tfFinite_quot (hN : 0 < N) : Finite (𝓞 E ⧸ P.asIdeal ^ N) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := pow_ne_zero _ P.ne_bot
  first
    | exact @Finite.of_fintype _ (Ideal.fintypeQuotientOfFreeOfNeBot _ hPN)
    | exact Ideal.finiteQuotientOfFreeOfNeBot _ hPN

theorem tfFinite_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → g ∈ H) :
    Finite (↥(GLint E n P) ⧸ H) := by
  classical
  haveI := tfFinite_quot P N hN
  let q : Set.range (tfRed P N) → (↥(GLint E n P) ⧸ H) := fun v => QuotientGroup.mk v.2.choose
  refine Finite.of_surjective q ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine ⟨⟨tfRed P N g, g, rfl⟩, ?_⟩
    show QuotientGroup.mk _ = QuotientGroup.mk g
    rw [QuotientGroup.eq]
    apply hH
    exact tfRed_eq P N (⟨tfRed P N g, g, rfl⟩ : Set.range (tfRed P N)).2.choose_spec

theorem tfRoot_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) (x : ↥H) :
    ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
  classical
  haveI := tfFinite_quot P N hN
  have key : ∀ k1 k2 : ℕ, k1 < k2 →
      tfRed P N ((x : ↥(GLint E n P)) ^ k1) = tfRed P N ((x : ↥(GLint E n P)) ^ k2) →
      ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
    intro k1 k2 hlt heq
    have hp := tfRed_eq P N heq
    have hpow : ((x : ↥(GLint E n P)) ^ k1)⁻¹ * (x : ↥(GLint E n P)) ^ k2 =
        (x : ↥(GLint E n P)) ^ (k2 - k1) := by
      rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hpow] at hp
    obtain ⟨hmem, hlam⟩ := hH _ hp
    refine ⟨k2 - k1, by omega, ?_⟩
    have hx : (⟨(x : ↥(GLint E n P)) ^ (k2 - k1), hmem⟩ : ↥H) = x ^ (k2 - k1) := by
      apply Subtype.ext
      simp
    rw [← map_pow, ← hx, hlam]
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => tfRed P N ((x : ↥(GLint E n P)) ^ k))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key k1 k2 hlt heq
  · exact key k2 k1 hlt heq.symm

end Idx

section Pi

theorem tfPiChar {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    piChar H lam x = ∏ i, lam i ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ := by
  simp only [piChar, MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
  rfl

end Pi

section Fam

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q)

theorem thetaOpen_finIdx (h : ThetaOpen Θ) (P : Q) : Finite (↥(GLint E n P.1) ⧸ (Θ P).H) := by
  obtain ⟨N, hN, hg⟩ := h P
  exact tfFinite_of_princ P.1 N hN (Θ P).H (fun g hgp => (hg g hgp).1)

theorem thetaOpen_root (h : ThetaOpen Θ) (c : ↥Θ.grp) : ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : Kˣ) : K) ^ m = 1 := by
  classical
  have hP : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ ^ m = 1 := by
    intro P
    obtain ⟨N, hN, hg⟩ := h P
    exact tfRoot_of_princ P.1 N hN (Θ P).H (Θ P).lam hg _
  choose m hm0 hm using hP
  have key : (Θ.chr c) ^ (∏ P, m P) = 1 := by
    have hc : Θ.chr c = ∏ P, (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ :=
      tfPiChar (fun P => (Θ P).H) (fun P => (Θ P).lam) c
    rw [hc, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun P _ => ?_
    obtain ⟨d, hd⟩ : m P ∣ ∏ Q, m Q := Finset.dvd_prod_of_mem _ (Finset.mem_univ P)
    rw [hd, pow_mul, hm P, one_pow]
  refine ⟨∏ P, m P, Finset.prod_pos fun P _ => hm0 P, ?_⟩
  rw [← Units.val_pow_eq_pow_val, key, Units.val_one]

end Fam

section Tw

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))

end Tw

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Close

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : (q : E) ≠ 0)

theorem qth_vq_le : P.valuation E (q : E) ≤ 1 := by
  exact (qth_intAt_iff P _).1 ⟨(q : 𝓞 E), 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩

theorem qth_mulVec {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m) (x : Sp E m) :
    W x = x + (((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1).mulVec x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, toGLm_mulVec]
  abel

include hq0 in
theorem qth_close_scl {m : ℕ} (e : ℕ → ℤ) (he : ∀ l, e l = 0 ∨ e l = 1) (W : Sp E m ≃ₗ[E] Sp E m)
    (hW : ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E))
    {x : Sp E m} (hx : x ∈ LocE.sclLat P q m e) : W x ∈ LocE.sclLat P q m e := by
  rw [ciMem_sclLat] at hx ⊢
  intro l
  rw [qth_intAt_iff, qth_mulVec W x]
  set M := ((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hM
  have hyj : ∀ j : Fin m, P.valuation E (((q : E) ^ e j.1)⁻¹ * x j) ≤ 1 :=
    fun j => (qth_intAt_iff P _).1 (hx j)
  have hqe : ∀ j : Fin m, P.valuation E ((q : E) ^ (e j.1)) ≤ 1 := by
    intro j
    rcases he j with h | h <;> rw [h]
    · simp
    · rw [zpow_one]
      exact qth_vq_le P q
  have hv0 : P.valuation E (q : E) ≠ 0 := by simpa using hq0
  have hcM : ∀ j, P.valuation E (((q : E) ^ e l.1)⁻¹ * (M - 1) l j) ≤ 1 := by
    intro j
    rcases he l with h | h <;> rw [h]
    · simp only [zpow_zero, inv_one, one_mul]
      exact (hW l j).trans (qth_vq_le P q)
    · rw [zpow_one, map_mul, map_inv₀]
      calc (P.valuation E (q : E))⁻¹ * P.valuation E ((M - 1) l j)
          ≤ (P.valuation E (q : E))⁻¹ * P.valuation E (q : E) := by gcongr; exact hW l j
        _ = 1 := inv_mul_cancel₀ hv0
  have hsplit : ((q : E) ^ e l.1)⁻¹ * (x + (M - 1).mulVec x) l = ((q : E) ^ e l.1)⁻¹ * x l +
      ∑ j, (((q : E) ^ e l.1)⁻¹ * (M - 1) l j) * (q : E) ^ (e j.1) * (((q : E) ^ e j.1)⁻¹ * x j) := by
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hz : (q : E) ^ (e j.1) ≠ 0 := zpow_ne_zero _ hq0
    have h1 : (q : E) ^ (e j.1) * (((q : E) ^ (e j.1))⁻¹ * x j) = x j := by
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    rw [mul_assoc _ ((q : E) ^ (e j.1)), h1]
    ring
  rw [hsplit]
  refine Valuation.map_add_le _ (hyj l) (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul, map_mul]
  exact mul_le_one' (mul_le_one' (hcM j) (hqe j)) (hyj j)

include hq0 in
theorem qth_close_std {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m)
    (hW : ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E))
    {x : Sp E m} (hx : x ∈ stdAt E m P) : W x ∈ stdAt E m P := by
  rw [ciMem_stdAt] at hx ⊢
  intro i
  rw [qth_mulVec W x]
  have hxi : ∀ j, P.valuation E (x j) ≤ 1 := fun j => (qth_intAt_iff P _).1 (hx j)
  rw [qth_intAt_iff]
  show P.valuation E (x i + ∑ j, (((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j * x j) ≤ 1
  refine Valuation.map_add_le _ (hxi i) (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul]
  exact mul_le_one' ((hW i j).trans (qth_vq_le P q)) (hxi j)

end Close

end Formalism.L2.Col
end
end
