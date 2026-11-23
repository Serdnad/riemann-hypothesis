module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftGen
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle071
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents



theorem liftOrb_of (hSR : SRLift) : LiftOrb := by
  intro F _ _ _ E _ _ _ _ M hOK m Z Z' ⟨φ⟩ hκ
  classical
  set e : Fin (m + 1) → M.R := Pi.single (Fin.last m) 1 with he
  have hmkZ : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z.Z.mulVec x) : M.Cok Z) = 0 :=
    fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hmkZ' : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z'.Z.mulVec x) : M.Cok Z') = 0 :=
    fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

  have hcol : ∀ j : Fin (m + 1), ∃ w : Fin (m + 1) → M.R,
      (Submodule.Quotient.mk w : M.Cok Z') = φ.1 (Submodule.Quotient.mk (Pi.single j 1)) ∧
      mu M Z' w = mu M Z (Pi.single j 1) ∧ (j = Fin.last m → w = e) := by
    intro j
    by_cases hj : j = Fin.last m
    · subst hj
      refine ⟨e, φ.2.1.symm, ?_, fun _ => rfl⟩
      rw [he, mu_e, mu_e, hκ]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ.1 (Submodule.Quotient.mk (Pi.single j 1)))
      have hl := φ.2.2 (Submodule.Quotient.mk (Pi.single j 1))
      rw [← hv, lam_mk, lam_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hl
      obtain ⟨t, ht⟩ := hl
      refine ⟨v - Z'.Z.mulVec (t • e), ?_, ?_, fun h => absurd h hj⟩
      · rw [Submodule.Quotient.mk_sub, hmkZ', sub_zero, hv]
      · have ht' : ((t : M.R) : E) = mu M Z' v - mu M Z (Pi.single j 1) := ht
        rw [sub_eq_add_neg, ← Matrix.mulVec_neg, mu_add, mu_Z]
        simp only [Pi.neg_apply, Pi.smul_apply, he, Pi.single_eq_same, smul_eq_mul, mul_one, NegMemClass.coe_neg]
        rw [ht']
        ring
  choose w hw1 hw2 hw3 using hcol
  set l₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => w j i with hl₁
  have hl₁v : ∀ x, l₁.mulVec x = ∑ j, x j • w j := by
    intro x; funext i
    simp [hl₁, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hx : ∀ x : Fin (m + 1) → M.R, ∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R) = x := by
    intro x; funext i; simp [Finset.sum_apply, Pi.single_apply]
  have hP1 : ∀ x, (Submodule.Quotient.mk (l₁.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x) := by
    intro x
    conv_rhs => rw [← hx x]
    rw [hl₁v]
    have e1 : (Submodule.Quotient.mk (∑ j, x j • w j) : M.Cok Z') =
        ∑ j, x j • (Submodule.Quotient.mk (w j) : M.Cok Z') := by

      rw [← Submodule.mkQ_apply, map_sum]; simp
    have e2 : (Submodule.Quotient.mk (∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R)) : M.Cok Z) =
        ∑ j, x j • (Submodule.Quotient.mk (Pi.single j 1) : M.Cok Z) := by

      rw [← Submodule.mkQ_apply, map_sum]; simp

    rw [e1, e2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hw1 j]
  have hP2 : ∀ x, mu M Z' (l₁.mulVec x) = mu M Z x := by
    intro x
    conv_rhs => rw [← hx x]
    rw [hl₁v, mu_sum, mu_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mu_smul, mu_smul, hw2 j]
  have hl₁e : ∀ i, l₁ i (Fin.last m) = if i = Fin.last m then 1 else 0 := by
    intro i
    simp only [hl₁, Matrix.of_apply, hw3 _ rfl, he, Pi.single_apply]

  have hK1 : ∀ y ∈ headK M Z', (Submodule.Quotient.mk y : M.Cok Z') = 0 := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (mem_headK M Z').1 hy
    exact hmkZ' x
  have hK2 : ∀ y ∈ headK M Z', mu M Z' y = 0 := by
    intro y hy
    obtain ⟨x, hx0, rfl⟩ := (mem_headK M Z').1 hy
    rw [mu_Z, hx0]; simp

  have hb : ∃ y₀, Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e) ∧ y₀ (Fin.last m) = 1 := by
    have h0 : (Submodule.Quotient.mk (l₁.mulVec (Z.Z.mulVec e)) : M.Cok Z') = 0 := by
      rw [hP1, hmkZ, map_zero]
    obtain ⟨y₀, hy₀⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
    have hy₀' : Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e) := hy₀
    refine ⟨y₀, hy₀', ?_⟩
    have := hP2 (Z.Z.mulVec e)
    rw [← hy₀', mu_Z, mu_Z, he, Pi.single_eq_same] at this
    exact Subtype.ext (by simpa using this)
  obtain ⟨y₀, hy₀, hy₀l⟩ := hb
  have hspan : ∀ v : Fin (m + 1) → M.R, ∃ x, v - l₁.mulVec x ∈ headK M Z' := by
    intro v
    obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v))
    have h1 : (Submodule.Quotient.mk (v - l₁.mulVec x₀) : M.Cok Z') = 0 := by
      rw [Submodule.Quotient.mk_sub, hP1, hx₀, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
    simp only [Matrix.mulVecLin_apply] at hy
    refine ⟨x₀ + y (Fin.last m) • Z.Z.mulVec e, (mem_headK M Z').2 ⟨y - y (Fin.last m) • y₀, ?_, ?_⟩⟩
    · simp [hy₀l]
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hy₀, hy, Matrix.mulVec_add, Matrix.mulVec_smul]
      abel
  obtain ⟨H, hHK, hHl, hdet⟩ := hSR M hOK m l₁ (headK M Z') hl₁e hspan
  set l := l₁ + H with hl
  have hHx : ∀ x, H.mulVec x ∈ headK M Z' := by
    intro x
    have : H.mulVec x = ∑ j, x j • (fun i => H i j) := by
      funext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hHK j)
  have hQ1 : ∀ x, (Submodule.Quotient.mk (l.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x) := by
    intro x
    rw [hl, Matrix.add_mulVec, Submodule.Quotient.mk_add, hK1 _ (hHx x), add_zero, hP1]
  have hQ2 : ∀ x, mu M Z' (l.mulVec x) = mu M Z x := by
    intro x
    rw [hl, Matrix.add_mulVec, mu_add, hK2 _ (hHx x), add_zero, hP2]
  have hle : ∀ i, l i (Fin.last m) = if i = Fin.last m then 1 else 0 := by
    intro i; rw [hl, Matrix.add_apply, hl₁e, hHl, add_zero]

  have hcolρ : ∀ j, ∃ x, Z'.Z.mulVec x = l.mulVec (Z.Z.mulVec (Pi.single j 1)) := by
    intro j
    have h0 : (Submodule.Quotient.mk (l.mulVec (Z.Z.mulVec (Pi.single j 1))) : M.Cok Z') = 0 := by
      rw [hQ1, hmkZ, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0
  choose xs hxs using hcolρ
  set ρ₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => xs j i with hρ₀
  have hZρ : Z'.Z * ρ₀ = l * Z.Z := by
    ext i j
    have h1 : (Z'.Z * ρ₀) i j = (Z'.Z.mulVec (xs j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hρ₀]
    have h2 : (l * Z.Z) i j = (l.mulVec (Z.Z.mulVec (Pi.single j 1))) i := by
      rw [Matrix.mulVec_mulVec]; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, h2, hxs j]
  have hρl : ∀ j, ρ₀ (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    have := hQ2 (Z.Z.mulVec (Pi.single j 1))
    rw [← hxs j, mu_Z, mu_Z] at this
    apply Subtype.ext
    simp only [hρ₀, Matrix.of_apply]
    rw [this]
    by_cases h : j = Fin.last m
    · subst h; simp
    · simp [Pi.single_apply, h, Ne.symm h]

  have hlu : IsUnit (l.det) := hdet
  have honto : ∀ x, ∃ y, ρ₀.mulVec y = x := by
    intro x
    set u := l⁻¹.mulVec (Z'.Z.mulVec x) with hu
    have hlu' : l.mulVec u = Z'.Z.mulVec x := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hlu, Matrix.one_mulVec]
    have hmu : (Submodule.Quotient.mk u : M.Cok Z) = 0 := by
      have h1 := hQ1 u
      rw [hlu', hmkZ'] at h1
      exact (φ.1.map_eq_zero_iff).1 h1.symm
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmu
    simp only [Matrix.mulVecLin_apply] at hy
    refine ⟨y, mulVec_inj M Z' ?_⟩
    rw [Matrix.mulVec_mulVec, hZρ, ← Matrix.mulVec_mulVec, hy, hlu']
  choose ys hys using fun i : Fin (m + 1) => honto (Pi.single i 1)
  have hright : ρ₀ * (Matrix.of fun i j => ys j i) = 1 := by
    ext i j
    have := congrFun (hys j) i
    simp only [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [this, Matrix.one_apply, Pi.single_apply]
  have hρu : IsUnit ρ₀.det := by
    have := congrArg Matrix.det hright
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  refine ⟨l, ρ₀⁻¹, hlu, (Matrix.isUnit_nonsing_inv_det_iff).2 hρu, hle, fun j => ?_, ?_⟩
  · have h1 : Matrix.vecMul e ρ₀ = e := by
      funext j
      simp only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [hρl]
    have h2 : Matrix.vecMul e ρ₀⁻¹ = e := by
      conv_lhs => rw [← h1]
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hρu, Matrix.vecMul_one]
    have := congrFun h2 j
    simp only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    rw [this]
  · calc Z'.Z = Z'.Z * ρ₀ * ρ₀⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρu, Matrix.mul_one]
      _ = l * Z.Z * ρ₀⁻¹ := by rw [hZρ]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def RFinMax : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → {m : Ideal M.R | m.IsMaximal}.Finite

theorem srLift_of_finMax (h : RFinMax) : SRLift := by
  intro F _ _ _ E _ _ _ _ M hOK n A K hA hK
  exact Formalism.L2.SG.Pf.SRL.srLift_of_finite (h M hOK) A K hA hK

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.PCountEx

section ZM

end ZM

section Approx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem approxF (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0) (b : ∀ p, (A p).Fp) :
    ∃ f : F, (∀ p ∈ S, haveI := (A p).lf
        valuation (A p).Fp ((A p).ιF f - b p) ≤ valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c))) ∧
      ∀ p ∉ S, (A p).ιF f ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) :=
  by apply _root_.UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF <;> assumption

end Approx

section ApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem iotaE_mem_O (p : HeightOneSpectrum (𝓞 F)) (e : 𝓞 E) : (A p).ιE (e : E) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have h : IsIntegral ℤ ((A p).ιE (e : E)) := e.2.map (A p).ιE.toIntAlgHom
  exact h.tower_top

theorem alg_mem_O (p : HeightOneSpectrum (𝓞 F)) {t : (A p).Fp} (ht : t ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) :
    algebraMap (A p).Fp (A p).Ep t ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have h := isIntegral_algebraMap (R := 𝒪[(A p).Fp]) (A := (A p).Ep) (x := ⟨t, ht⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[(A p).Fp] (A p).Fp (A p).Ep] at h
  exact h

theorem exists_int_span : ∃ (n : ℕ) (e : Fin n → 𝓞 E), Submodule.span F (Set.range fun j => (e j : E)) = ⊤ := by
  let b := Module.finBasis F E
  have hm : ∀ i, ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * b i) := fun i => by
    have hx : IsAlgebraic ℤ (b i) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (b i))
    obtain ⟨k, hk0, hk⟩ := hx.exists_integral_multiple
    exact ⟨k, hk0, by simpa [zsmul_eq_mul, Algebra.smul_def] using hk⟩
  choose k hk0 hk using hm
  refine ⟨Module.finrank F E, fun i => ⟨(k i : E) * b i, hk i⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e1 : b.repr x i • b i = (b.repr x i * ((k i : F))⁻¹) • ((k i : E) * b i) := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀, map_intCast]
    have hk' : ((k i : ℤ) : E) ≠ 0 := by exact_mod_cast hk0 i
    field_simp
  rw [e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem approxE (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0) (a : ∀ p, (A p).Ep) :
    ∃ x : E, (∀ p ∈ S, ∃ o ∈ (A p).O,
        (A p).ιE x - a p = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, (A p).ιE x ∈ (A p).O := by
  obtain ⟨n, e, he⟩ := exists_int_span (F := F) (E := E)

  have hco : ∀ p, ∃ l : Fin n → (A p).Fp, ∑ j, l j • (A p).ιE (e j : E) = a p := by
    intro p
    have hsp : Submodule.span (A p).Fp (Set.range fun j => (A p).ιE (e j : E)) = ⊤ := by
      rw [eq_top_iff, ← (A p).span, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span F (Set.range fun j => (e j : E)) := by rw [he]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨j, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul t y _ hy =>
        rw [Algebra.smul_def, map_mul, (A p).compat, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hy
    have ha : a p ∈ Submodule.span (A p).Fp (Set.range fun j => (A p).ιE (e j : E)) := by rw [hsp]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun _).1 ha
  choose l hl using hco

  have hf := fun j : Fin n => approxF A S c hc (fun p => l p j)
  choose f hfS hfO using hf
  refine ⟨∑ j, algebraMap F E (f j) * (e j : E), fun p hp => ?_, fun q hq => ?_⟩
  · haveI := (A p).lf
    have hcF : (A p).ιF (algebraMap (𝓞 F) F c) ≠ 0 := by
      rw [map_ne_zero_iff _ (A p).ιF.injective, Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
      exact hc
    have hv0 : valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c)) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hcF
    refine ⟨∑ j, algebraMap (A p).Fp (A p).Ep
        (((A p).ιF (f j) - l p j) / (A p).ιF (algebraMap (𝓞 F) F c)) * (A p).ιE (e j : E), ?_, ?_⟩
    · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ (alg_mem_O A p ?_) (iotaE_mem_O A p (e j))
      rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 hv0)]
      exact hfS j p hp
    · rw [← hl p, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, (A p).compat, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hcF, ← sub_mul,
        map_sub]
  · haveI := (A q).lf

    rw [map_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [map_mul, (A q).compat]
    exact Subring.mul_mem _ (alg_mem_O A q (hfO j q hq)) (iotaE_mem_O A q (e j))

end ApproxE

end Formalism.L2.SG.Pf.PCountEx
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem perp_anti {S T : Submodule E V} (h : S ≤ T) : H.perp T ≤ H.perp S :=
  fun _ hv x hx => hv x (h hx)

theorem X_le_Xp {r : ℕ} (f : Fin (r + 1) → V) : H.X f ≤ H.Xp f :=
  Submodule.span_mono (Set.range_subset_iff.mpr fun a => ⟨a.castSucc, rfl⟩)

theorem mem_perp_isotropicSpan_of_mem_framePerp {r : ℕ} {f f' : Fin (r + 1) → V} {w : V} (hw : w ∈ H.W0 f f') :
    w ∈ H.perp (H.X f) :=
  perp_anti H ((X_le_Xp H f).trans le_sup_left) hw

theorem mem_perp_isotropicSpan_of_mem_framePerp' {r : ℕ} {f f' : Fin (r + 1) → V} {w : V} (hw : w ∈ H.W0 f f') :
    w ∈ H.perp (H.X f') :=
  perp_anti H ((X_le_Xp H f').trans le_sup_right) hw

theorem sub_mem_X_of_mkW_eq {r : ℕ} {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))}
    (h : H.mkW f x = H.mkW f y) : (x : V) - y ∈ H.X f := by
  have h' := (Submodule.Quotient.eq _).mp h
  simpa using h'

end Basic

section Stmt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def Lemma0L (M : Model F E) (r : ℕ) : Prop :=
  M.split = none → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f'))

theorem lemma0L_holds (M : Model F E) (r : ℕ) : Lemma0L M r := by
  intro hsplit V _ _ H t hgen w hw
  classical
  have hprim := hgen.2
  simp only [HermSp.MMfam, hsplit] at hprim
  obtain ⟨hmem, hli, hspan⟩ := hprim
  constructor
  · intro hwL
    exact ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩⟩
  · rintro ⟨⟨x, hxL, hxw⟩, ⟨x', hx'L, hx'w⟩⟩
    have hp : (x : V) - w ∈ Submodule.span E (Set.range fun a : Fin r => t.f a.castSucc) :=
      sub_mem_X_of_mkW_eq H (y := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) hxw
    have hq : (x' : V) - w ∈ Submodule.span E (Set.range fun a : Fin r => t.f' a.castSucc) :=
      sub_mem_X_of_mkW_eq H (y := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩) hx'w
    obtain ⟨cp, hcp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
    obtain ⟨cq, hcq⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
    have hdiff : (x : V) - x' ∈ t.abelian₂ := t.abelian₂.sub_mem hxL hx'L
    have hdiffE : (x : V) - x' ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
      have e : (x : V) - x' = ((x : V) - w) - ((x' : V) - w) := by abel
      rw [e]
      refine Submodule.sub_mem _ ?_ ?_
      · exact (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a.castSucc, rfl⟩)) hp
      · exact (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a.castSucc, rfl⟩)) hq
    obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan _ hdiff hdiffE)
    have hinjl : Function.Injective (fun a : Fin r => (Sum.inl a.castSucc : Fin (r + 1) ⊕ Fin (r + 1))) :=
      Sum.inl_injective.comp (Fin.castSucc_injective r)
    have hinjr : Function.Injective (fun a : Fin r => (Sum.inr a.castSucc : Fin (r + 1) ⊕ Fin (r + 1))) :=
      Sum.inr_injective.comp (Fin.castSucc_injective r)
    set e1 : (Fin (r + 1) ⊕ Fin (r + 1)) →₀ E :=
      cp.mapDomain (fun a => Sum.inl a.castSucc) - cq.mapDomain (fun a => Sum.inr a.castSucc) with he1
    set e2 : (Fin (r + 1) ⊕ Fin (r + 1)) →₀ E := l.mapRange (fun a : M.L.O => (a : E)) rfl with he2
    have h1 : Finsupp.linearCombination E (Sum.elim t.f t.f') e1 = (x : V) - x' := by
      rw [he1, map_sub, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain,
        Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
      have e : (x : V) - x' = ((x : V) - w) - ((x' : V) - w) := by abel
      rw [e, ← hcp, ← hcq]
      rfl
    have h2 : Finsupp.linearCombination E (Sum.elim t.f t.f') e2 = (x : V) - x' := by
      rw [← hl, he2, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      rfl
    have he : e1 = e2 := hli (h1.trans h2.symm)
    have hcoef : ∀ a : Fin r, cp a = (l (Sum.inl a.castSucc) : E) := by
      intro a
      have h := congrArg (fun e => e (Sum.inl a.castSucc)) he
      simp only [he1, he2, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at h
      rw [Finsupp.mapDomain_apply_of_injective hinjl, Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨b, hb⟩
        simp at hb), sub_zero] at h
      exact h
    have hpL : (x : V) - w ∈ t.abelian₂ := by
      rw [← hcp]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [hcoef a]
      exact t.abelian₂.smul_mem (l (Sum.inl a.castSucc)) (hmem (Sum.inl a.castSucc))
    have e : w = (x : V) - ((x : V) - w) := by abel
    rw [e]
    exact t.abelian₂.sub_mem hxL hpL

end Stmt

end Formalism.L2.SG.LsDatumA
end
end
