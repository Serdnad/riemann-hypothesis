module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DVIsDiffVal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OneMemOev
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CfCoe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

def OmVDdTr : Prop :=
  ∀ d : 𝓞 D.host.F, d ∈ differentIdeal ℤ (𝓞 D.host.F) ↔
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)

theorem iota_alg_inj : Function.Injective (fun x : X.B.I.F => X.ιE (algebraMap X.B.I.F X.B.I.E x)) :=
  X.ιE.injective.comp (algebraMap X.B.I.F X.B.I.E).injective

theorem pre_int (d : 𝓞 D.host.F) : ∃ x : 𝓞 X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  obtain ⟨a, ha⟩ := (X.ιE_F ((d : D.host.F) : D.host.E)).1 (d : D.host.F).2
  set f : X.B.I.F →+* D.host.E := (X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E) with hf
  have hd : IsIntegral ℤ (((d : D.host.F) : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe d).map ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom
  have ha' : f a = ((d : D.host.F) : D.host.E) := ha
  rw [← ha'] at hd
  have hai : IsIntegral ℤ a := (isIntegral_algHom_iff f.toIntAlgHom (iota_alg_inj X)).1 hd
  exact ⟨⟨a, (mem_integralClosure_iff ℤ _).2 hai⟩, ha⟩

theorem pow_tr (hT : OmVDdTr X) (k : ℕ) (d : 𝓞 D.host.F) (hd : d ∈ differentIdeal ℤ (𝓞 D.host.F) ^ k) :
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ k ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  induction k generalizing d with
  | zero =>
    obtain ⟨x, hx⟩ := pre_int X d
    exact ⟨x, by simp, hx⟩
  | succ k ih =>
    rw [pow_succ'] at hd
    refine Submodule.mul_induction_on
      (C := fun d : 𝓞 D.host.F => ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ (k + 1) ∧
        X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)) hd ?_ ?_
    · intro a ha b hb
      obtain ⟨x1, hx1, e1⟩ := (hT a).1 ha
      obtain ⟨x2, hx2, e2⟩ := ih b hb
      refine ⟨x1 * x2, by rw [pow_succ']; exact Submodule.mul_mem_mul hx1 hx2, ?_⟩
      have : ((x1 * x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) * (x2 : X.B.I.F) := rfl
      rw [this, map_mul, map_mul, e1, e2]; rfl
    · rintro a b ⟨x1, hx1, e1⟩ ⟨x2, hx2, e2⟩
      refine ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, ?_⟩
      have : ((x1 + x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) + (x2 : X.B.I.F) := rfl
      rw [this, map_add (f := _), map_add (f := _), e1, e2]; rfl

def Qi (v : PlX X) (c : Fv X.B.I.F v) : Ideal (𝓞 D.host.E) where
  carrier := {i | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (i : D.host.E)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((0 : 𝓞 D.host.E) : D.host.E)) ∈
      OEv (E := X.B.I.E) v
    simp only [map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro i j hi hj
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((i : D.host.E) + (j : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_add (f := _), map_add (f := _), mul_add]; exact Submodule.add_mem _ hi hj
  smul_mem' := by
    intro o i hi
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((o : D.host.E) * (i : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hi

theorem alg_int_mem (v : PlX X) (c : Fv X.B.I.F v) (hc : Valued.v c ≤ 1) :
    algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c ∈ OEv (E := X.B.I.E) v := by
  have e : algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c =
      (⟨c, hc⟩ : v.adicCompletionIntegers X.B.I.F) • (1 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e]; exact Submodule.smul_mem _ _ (one_mem_oev v)

theorem ddS_pow (k : ℕ) : ddS D ^ k = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
    (differentIdeal ℤ (𝓞 D.host.F) ^ k) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [Ideal.map_pow, FractionalIdeal.coeIdeal_pow]; rfl

theorem dd1 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ ddS D ^ k) :
    sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  rw [ddS_pow, FractionalIdeal.mem_coeIdeal] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F) ^ k) ≤
      Qi X v ((dV v)⁻¹ ^ k) := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    obtain ⟨x, hx, ex⟩ := pow_tr X hT k d hd
    show sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (X.ιE.symm ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E)) ∈ OEv (E := X.B.I.E) v
    have e1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E) = ((d : D.host.F) : D.host.E) := rfl
    rw [e1, ← ex, RingEquiv.symm_apply_apply, ← alg_alg]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) _ * _ ∈ _
    rw [← map_mul]
    refine alg_int_mem X v _ ?_
    rw [map_mul]
    show Valued.v ((dV v)⁻¹ ^ k) * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F)) ≤ 1
    rw [map_pow, map_inv₀]
    have h1 := val_pow_le v k x hx
    have h0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
    calc (Valued.v (dV v))⁻¹ ^ k * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F))
        ≤ (Valued.v (dV v))⁻¹ ^ k * Valued.v (dV v) ^ k := mul_le_mul' le_rfl h1
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  exact hle hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

section

noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))
  (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
  (he1 : gramR (Fv F v) σ J e = 1)


include he1 in
theorem prim_iff (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (x : lamA v Λ a) :
    IsPrim v Λ (x : TupV (E := E) v n a) ↔ LinearIndependent K (phi σ J v Λ hSD he π a x) := by
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  have hcomb : ∀ d : Fin a → OR (E := E) v,
      (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) ∈ latLoc (E := E) v Λ := fun d =>
    Submodule.sum_mem _ fun i _ => Orb.oSmul v Λ hL _ (d i).2 _ (memA v Λ x i)
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hP κ hκ i
    choose d hd using fun j => hπ.1 (κ j)
    have hw := hcomb d
    have hz : ∀ p, π ⟨hR (Fv F v) σ J (e p) (∑ j, (d j : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) j),
        (hSD _).1 hw _ (bas_mem v Λ he p)⟩ = 0 := by
      intro p
      refine (coord_comb σ J v Λ hSD he π x d p _).trans ?_
      have := congrFun hκ p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simpa [hd] using this
    obtain ⟨w', hw', hww⟩ := ker_vec σ J v Λ hSD he he1 hπ hw hz
    have hc := hP.2 (fun j => sc (E := E) v ϖ⁻¹ * d j) (by
      have e2 : (∑ j, (sc (E := E) v ϖ⁻¹ * d j) • (x : TupV (E := E) v n a) j) =
          sc (E := E) v ϖ⁻¹ • ∑ j, (d j : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
      rw [e2, hww, smul_smul, sc_mul, inv_mul_cancel₀ h0, sc_one, one_smul]
      exact hw') i
    rw [← hd i]
    apply (hπ.2.1 _).2
    refine ⟨_, hc, ?_⟩
    rw [← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]
  · intro hLI
    refine ⟨fun i => memA v Λ x i, fun c hc => ?_⟩
    have key : ∀ m : ℕ, ∀ c : Fin a → Fv F v ⊗[F] E,
        (∑ i, c i • (x : TupV (E := E) v n a) i) ∈ latLoc (E := E) v Λ →
        (∀ i, sc (E := E) v (ϖ ^ m) * c i ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v := by
      intro m
      induction m with
      | zero => intro c _ hm i; simpa [sc_one] using hm i
      | succ m ih =>
        intro c hc hm
        apply ih c hc
        set u := ∑ i, c i • (x : TupV (E := E) v n a) i with hu
        have hpm : sc (E := E) v (ϖ ^ m) ∈ OEv (E := E) v := by
          simpa using sc_mul_mem_oEv v (pow_mem hint m) (Orb.oSub (E := E) v).1
        have hu' : sc (E := E) v (ϖ ^ m) • u ∈ latLoc (E := E) v Λ := Orb.oSmul v Λ hL _ hpm _ hc
        let d : Fin a → OR (E := E) v := fun i => ⟨_, hm i⟩
        have hwe : (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) =
            sc (E := E) v ϖ • (sc (E := E) v (ϖ ^ m) • u) := by
          rw [smul_smul, sc_mul, ← pow_succ', hu, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
        have hw := hcomb d
        have hz : ∀ p, ∑ i, π (d i) * phi σ J v Λ hSD he π a x i p = 0 := by
          intro p
          rw [← coord_comb σ J v Λ hSD he π x d p ((hSD _).1 hw _ (bas_mem v Λ he p))]
          apply (hπ.2.1 _).2
          refine ⟨hR (Fv F v) σ J (e p) (sc (E := E) v (ϖ ^ m) • u),
            (hSD _).1 hu' _ (bas_mem v Λ he p), ?_⟩
          show hR (Fv F v) σ J (e p) (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) = _
          rw [hwe, Orb.hR_smul_right]
        have hd0 := hLI (fun i => π (d i)) (by
          funext p
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact hz p)
        intro i
        obtain ⟨g, hg, hge⟩ := (hπ.2.1 (d i)).1 (hd0 i)
        have : sc (E := E) v (ϖ ^ m) * c i = g := by
          have h1 : sc (E := E) v ϖ * (sc (E := E) v (ϖ ^ m) * c i) = sc (E := E) v ϖ * g := by
            rw [← mul_assoc, sc_mul, ← pow_succ']
            exact hge
          have h2 := congrArg (fun y => sc (E := E) v ϖ⁻¹ * y) h1
          simp only [← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul] at h2
          exact h2
        rw [this]
        exact hg
    obtain ⟨m, hm⟩ := exists_pow_mem v hϖ c
    exact key m c hc hm

end PI.OmVg
end
end

section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  PI.VolStabSW
open scoped TensorProduct

def CorOne {R : Type} [CommRing R] {a : ℕ} (T : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ i₀ : Fin a, (∀ j, T i₀ j = 0) ∧ (∀ j, T j i₀ = 0) ∧ IsUnit (T + Matrix.single i₀ i₀ 1).det

def FFInertB : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → CorOne T →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T ∧ LinearIndependent K X} : ℝ) =
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
        ∏ j ∈ Finset.Icc (M - a) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))

def FFSplitB : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → CorOne T →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T ∧ LinearIndependent (k × k) X} : ℝ) =
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
        ∏ j ∈ Finset.Icc (M - a) M, (1 - (1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def RedP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (J' : Matrix (Fin n) (Fin n) K) (T' : Matrix (Fin a) (Fin a) K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, σ' (T' j i) = T' i j) ∧ CorOne T' ∧
          Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → K // ffGram (σ' : K →+* K) J' X = T' ∧ LinearIndependent K X}) ∨
       (etaV (E := E) v = 1 ∧ ∃ (J' : Matrix (Fin n) (Fin n) (k × k)) (T' : Matrix (Fin a) (Fin a) (k × k)),
          (∀ i j, (J' j i).swap = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, (T' j i).swap = T' i j) ∧ CorOne T' ∧
          Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → k × k //
              ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J' X = T' ∧ LinearIndependent (k × k) X}))

theorem clsP_of (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedP σ J ψ v Λ a Y) (hI : FFInertB) (hS : FFSplitB) :
    ClsP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have ha : a ≤ n := hG.2.2.2.2.1
  obtain ⟨k, _, _, hk, h⟩ := hR hG ϖ hϖ
  rcases h with ⟨hη, K, _, _, σ', J', T', hσ, h2, hne, hJ, hJu, hT, hTu, hc⟩ |
    ⟨hη, J', T', hJ, hJu, hT, hTu, hc⟩
  · rw [hc, hI k K σ' hσ h2 hne n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEtaB qv
    rw [hη]
    push_cast
    rfl
  · rw [hc, hS k n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEtaB qv
    rw [hη]
    push_cast
    rfl

end Gen

end PI.OmVd
end
end
