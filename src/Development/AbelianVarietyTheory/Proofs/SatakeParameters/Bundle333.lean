module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle327
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimes
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem core (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (M Dd : ℕ) (hD : 2 * M ≤ Dd) (y0 V₀ V₁ : Sp E n) (g k : Sp E n →ₗ[E] Sp E n)
    (hgI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (g x l))
    (hkI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (k x l))
    (hkD : ∀ w : Sp E n, (∀ l, IntAt P (w l)) → ∀ l, IntAt P ((q ^ Dd)⁻¹ * (k w - w) l))
    (hgy : ∀ l, IntAt P ((q ^ M)⁻¹ * (g y0 - y0) l)) (hy0 : ∀ l, IntAt P (q ^ M * y0 l))
    (h0 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₀ - y0) l)) (h1 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₁ - y0) l)) :
    ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - V₀) l) := by
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)
  obtain ⟨s, hs⟩ : ∃ s, Dd = 2 * M + s := ⟨Dd - 2 * M, by omega⟩

  have hA : ∀ l, IntAt P ((q ^ M)⁻¹ * (k y0 - y0) l) := by
    intro l
    have h := hkD ((q ^ M) • y0) (fun l => by simpa [smul_eq_mul] using hy0 l) l
    have e : (q ^ M)⁻¹ * (k y0 - y0) l = q ^ s * ((q ^ Dd)⁻¹ * (k ((q ^ M) • y0) - (q ^ M) • y0) l) := by
      simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hs, pow_add, pow_mul]
      field_simp
      ring
    rw [e]
    exact mem_intS.1 ((intS P).mul_mem (mem_intS.2 (hqpow s)) (mem_intS.2 h))

  have hB : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - k y0) l) := by
    intro l
    have h := hkI ((q ^ M)⁻¹ • (V₁ - y0)) (fun l => by simpa [smul_eq_mul] using h1 l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  have hC : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - y0) l) := by
    intro l
    have e : (q ^ M)⁻¹ * (k V₁ - y0) l = (q ^ M)⁻¹ * (k V₁ - k y0) l + (q ^ M)⁻¹ * (k y0 - y0) l := by
      simp only [Pi.sub_apply]; ring
    rw [e]; exact (hB l).add (hA l)
  have hE : ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - g y0) l) := by
    intro l
    have h := hgI ((q ^ M)⁻¹ • (k V₁ - y0)) (fun l => by simpa [smul_eq_mul] using hC l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  intro l
  have e : (q ^ M)⁻¹ * (g (k V₁) - V₀) l =
      (q ^ M)⁻¹ * (g (k V₁) - g y0) l + (q ^ M)⁻¹ * (g y0 - y0) l + (-1 : E) * ((q ^ M)⁻¹ * (V₀ - y0) l) := by
    simp only [Pi.sub_apply]; ring
  rw [e]
  exact mem_intS.1 ((intS P).add_mem ((intS P).add_mem (mem_intS.2 (hE l)) (mem_intS.2 (hgy l)))
    ((intS P).mul_mem ((intS P).neg_mem (intS P).one_mem) (mem_intS.2 (h0 l))))

end GlobalTheory.LocQCoset

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

theorem coset_agree : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hi β P hPG p p₁ g k hg hgy hk hkD hF
  have hok := t.idx_ok μ
  have hq := qOf_ne (E := t.X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : t.X.E) := intAt_nat (P := P.1) _
  have memS : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), x ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ↔ ∀ l, IntAt P.1 (x l) :=
    fun x => mem_localization_standardLattice P.1 x
  have rep : ∀ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p' P).symm (repY (cosetOf A (t.m2 + 1) hi β p')))
        (y0At A (t.m2 + 1) hi β P) := by
    intro p'
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p') (fun P => y0At A (t.m2 + 1) hi β P)
    have hrep : repY (cosetOf A (t.m2 + 1) hi β p') ∈ cosetOf A (t.m2 + 1) hi β p' :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p') ⟨r, hr⟩
    exact hrep P
  have unf : ∀ y y' : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y y' →
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M)⁻¹ * (y - y') l) := by
    intro y y' h
    unfold SameCoset at h
    simpa only [if_neg hPG] using h
  have bnd : ∀ y : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
      ∀ l, IntAt P.1 (((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M * y l) :=
    fun y h => (GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie hi β P y h).2 hPG
  refine ⟨(memS _).2 fun l => ?_, (memS _).2 fun l => ?_, (memS _).2 fun l => ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p) l
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p₁) l
  · have hW : (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) =
        g (k ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) := by
      apply (frsF t.sel (t.tup μ) p P).injective
      rw [LinearEquiv.apply_symm_apply, ← hF, LinearEquiv.apply_symm_apply]
    have hgI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (g.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hg x).2 ((memS x).2 hx))
    have hkI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (k.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hk x).2 ((memS x).2 hx))
    have hkD' : ∀ w : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (w l)) →
        ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k.toLinearMap w - w) l) := by
      intro w hw l
      simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using (memS _).1 (hkD w ((memS w).2 hw)) l
    have hrefl : SameCoset t.sel (t.tup μ) (t.cst μ) P (y0At A (t.m2 + 1) hi β P) (y0At A (t.m2 + 1) hi β P) := by
      unfold SameCoset
      intro l
      rw [sub_self, Pi.zero_apply, mul_zero]
      simpa using intAt_nat (E := t.X.E) (P := P.1) 0
    have hy0 := bnd _ hrefl
    have := core _ hq hqi (t.cst μ).M ((t.cst μ).D P) (hok.depthQ P hPG) (y0At A (t.m2 + 1) hi β P) _ _
      g.toLinearMap k.toLinearMap hgI hkI hkD' (unf _ _ hgy) hy0 (unf _ _ (rep p)) (unf _ _ (rep p₁)) l
    rw [hW]
    simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using this

end GlobalTheory.LocQCoset

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMuDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := intAtA_mul
  one_mem' := by simpa using intAtA_int (F := F) (P := P) 1
  add_mem' := intAtA_add
  zero_mem' := by simpa using intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

end Frame

end GlobalTheory.TopMuDet

end

theorem GlobalTheory.TwTop.muOf_det_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))) (z : SB t μ → t.X.K)
    (g' : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1)))) (z' : SB t μ → t.X.K),
    (∀ P, A.cplRel β P (g P) (z P) ∧ InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 (g P)) →
    (∀ P, TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P (g' P) (z' P) ∧
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 (g' P)) →
    muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu hi β β' κ κ' g z g' z' hg hg'
  have hlt : t.m2 + 1 < D.R.m := by omega
  have hok := (t.idx_ok μ).cst_ok
  obtain ⟨h1, -⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1) (Nat.le_of_succ_le hi) β κ
    (fun P => ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hok.D_pos P) (hg P).2)
  have hdep : ∀ P : SB t μ, 1 ≤ topDep t.sel (t.tup μ) (t.cst μ) P := by
    intro P
    unfold topDep
    split_ifs
    · exact le_rfl
    · have := hok.M_pos
      omega
  obtain ⟨-, h2⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1 + 1) hi β' κ'
    (fun P => ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hdep P) (hg' P).2)
  rw [Finset.prod_mul_distrib, map_mul, ← mul_assoc, h1, one_mul, h2]
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwRat

theorem ratUnitCol : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi γ hγ
  exact GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹)
    (GlobalTheory.unitary_conj_orthonormal D _ _ _ (hP.crd_orth i hi) hγ)

end GlobalTheory.TwRat
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hj : t.m2 + 1 ≤ D.R.m) (β' : (St (t.m2 + 1) hj).Ch)
    (x' x₁' : UA D (t.m2 + 1) hj) (κ' : ((St (t.m2 + 1) hj).K β').lev.U) p', x₁'.1 = x'.1 * κ'.1 → IsPtAd A a (t.m2 + 1) hj β' x' p' →
    ∃ (q' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
      IsPtAd A a (t.m2 + 1) hj β' x₁' q' ∧
      (∀ (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) w, phiT t.X.K p.deco.1 q'.deco.1 w = phiT t.X.K p.deco.1 p'.deco.1 w) ∧
      (∀ P, frsF t.sel (t.tup μ) q' P = frsF t.sel (t.tup μ) p' P * ((κ'' P)⁻¹).1) ∧
      ∀ P, InFrame t.seam (A.fb (t.m2 + 1) hj β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) := by
  first | exact @GlobalTheory.CplPt.ptAd_levCpl | exact GlobalTheory.CplPt.ptAd_levCpl | (intros; apply GlobalTheory.CplPt.ptAd_levCpl <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.coupledStep_chart_level_at_bad_primes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∃ c : SB t μ → t.X.Kˣ,
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
        ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P) (c P)) ∧
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = ((((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.chi κ' : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CplLev.levAt_cpl | exact GlobalTheory.CplLev.levAt_cpl | (intros; apply GlobalTheory.CplLev.levAt_cpl <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem sNum_lev_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), SNum (t.O u μ).S (t.rd u μ).lev := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ _
  exact Formalism.L2.Ker.level_structure_counting D L hT Gi Gl Kc Dx cX ex t u μ

end GlobalTheory.TwV
end

section

noncomputable section

namespace GlobalTheory.TwV

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inFr_symm_inFr_cancel {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a)
    (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (z : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' z) = z := by
  refine LinearMap.ext fun x => ?_
  simp [Formalism.L2.Col.inFr]



theorem moved_pair_datum_eq_adelic_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J Xi j hj h1 h2 La La' z
  unfold GlobalTheory.TwU.xiM Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dite_eq_left ⟨hj, h1, h2⟩, inFr_symm_inFr_cancel]

end GlobalTheory.TwV

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem finStab_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), FinStab (sysS H X std).Lv := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  show FinStab Lv
  intro j c La hLa
  by_cases hj : j ≤ D.R.m
  · exact Nat.finite_of_card_ne_zero ((labAt X H).stab_dvd j hj c La hLa).1.ne'
  · exact (J.empty j (by omega)).elim c

end GlobalTheory.TwV
end
