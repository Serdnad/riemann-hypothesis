module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle002
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
public import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.evenVal :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), Dict.Unr L → ∀ v : Pl (Lp L), EvenVal (Ov v) (cv v P.Δ) := by
  intro L _ _ _ P hU v
  have hval : ∀ x : Lp L, Valued.v (cv v x) = v.valuation (Lp L) x := fun x =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hδ : P.e QuadraticAlgebra.omega * P.e QuadraticAlgebra.omega = algebraMap (Lp L) L P.Δ := by
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero,
      P.e_alg]
  have hδ0 : P.e QuadraticAlgebra.omega ≠ 0 := by
    intro h0
    have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = 0 := P.e.injective (by rw [h0, map_zero])
    have h2 := congrArg QuadraticAlgebra.im h1
    simp at h2
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hQl.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQm.isPrime, hQ0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hQl
  have hr : w.asIdeal.ramificationIdx (𝓞 (Lp L)) = 1 := by
    haveI := hU w
    haveI : w.asIdeal.IsPrime := w.isPrime
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 (Lp L)) (p := w.asIdeal)
  have hv := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v w P.Δ
  rw [hr, pow_one, ← hδ, map_mul] at hv
  have hw0 : w.valuation L (P.e QuadraticAlgebra.omega) ≠ 0 := by simpa using hδ0
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer (Lp L)
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  let t : Lp L := π ^ (-WithZero.log (w.valuation L (P.e QuadraticAlgebra.omega)))
  have ht0 : t ≠ 0 := zpow_ne_zero _ hπ0
  have ht : v.valuation (Lp L) t = w.valuation L (P.e QuadraticAlgebra.omega) := by
    simp only [t, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
    exact WithZero.exp_log hw0
  have hu1 : Valued.v (cv v (P.Δ / t ^ 2)) = 1 := by
    rw [hval, map_div₀, map_pow, ht, hv, sq]
    exact div_self (mul_ne_zero hw0 hw0)
  have hu2 : Valued.v (cv v (P.Δ / t ^ 2)⁻¹) = 1 := by
    rw [hval, map_inv₀, ← hval, hu1, inv_one]
  have hne : P.Δ / t ^ 2 ≠ 0 := div_ne_zero (by
      intro h0
      apply hδ0
      exact mul_self_eq_zero.mp (by rw [hδ, h0, map_zero])) (pow_ne_zero _ ht0)
  refine ⟨⟨⟨cv v (P.Δ / t ^ 2), le_of_eq hu1⟩, ⟨cv v (P.Δ / t ^ 2)⁻¹, le_of_eq hu2⟩, ?_, ?_⟩,
    cv v t, (map_ne_zero (cv v)).2 ht0, ?_⟩
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2) * cv v (P.Δ / t ^ 2)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2)⁻¹ * cv v (P.Δ / t ^ 2) = 1
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  · show cv v P.Δ = cv v (P.Δ / t ^ 2) * cv v t ^ 2
    rw [← map_pow, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ ht0)]
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoDiv :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (a : Kv v), P.φ v w h a ∈ w.adicCompletionIntegers L ↔ a ∈ v.adicCompletionIntegers (Lp L) := by
  intro L _ _ _ P v w h a
  subst h
  have hval : ∀ (F : Type) [Field F] [NumberField F] (u : Pl F) (x : F),
      Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x := fun F _ _ u x =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
  have he : (un w).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (un w).ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (un w).asIdeal w.asIdeal (un w).ne_bot] at he
  have key : ∀ x : Lp L, P.φ (un w) w rfl (cv (un w) x) ∈ w.adicCompletionIntegers L ↔
      cv (un w) x ∈ (un w).adicCompletionIntegers (Lp L) := by
    intro x
    have h1 := hval (Lp L) (un w) x
    have h2 := hval L w (algebraMap (Lp L) L x)
    rw [P.φ_alg, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, cv, h1, h2,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L (un w) w x]
    first
      | exact pow_le_one_iff he
      | exact pow_le_one_iff_of_nonneg zero_le' he
      | exact pow_le_one_iff_of_nonneg (zero_le' (a := _)) he
  have hd : DenseRange (cv (un w)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (Lp L) (un w)
  have hc := P.φ_cont (un w) w rfl
  have o1 : IsClopen ((P.φ (un w) w rfl) ⁻¹' (w.adicCompletionIntegers L : Set (Kw w))) :=
    (Valued.isClopen_integer (Kw w)).preimage hc
  have o2 : IsClopen ((un w).adicCompletionIntegers (Lp L) : Set (Kv (un w))) :=
    Valued.isClopen_integer (Kv (un w))
  constructor
  · intro ha
    by_contra hb
    obtain ⟨x, hx⟩ := hd.exists_mem_open (o1.isOpen.inter o2.compl.isOpen) ⟨a, ha, hb⟩
    exact hx.2 ((key x).1 hx.1)
  · intro ha
    by_contra hb
    obtain ⟨x, hx⟩ := hd.exists_mem_open (o2.isOpen.inter o1.compl.isOpen) ⟨a, ha, hb⟩
    exact hx.2 ((key x).2 hx.1)
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoGlob :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (x : Lsq (Lp L) P.Δ), P.rho v w h (lmap (cv v) P.Δ x) = algebraMap L (Kw w) (P.e x) := by
  intro L _ _ _ P v w h x
  have hx : x = algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.re
      + algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  have lhs : P.rho v w h (lmap (cv v) P.Δ x)
      = P.φ v w h (cv v x.re) + P.φ v w h (cv v x.im) * P.rt w := rfl
  rw [lhs, P.φ_alg, P.φ_alg, Pre.rt]
  conv_rhs => rw [hx]
  rw [map_add (f := _), map_mul, P.e_alg, P.e_alg, map_add (f := _), map_mul]
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)
open scoped TensorProduct
open GroundTheory.Global.SemiLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem lies {v : Pl (Lp L)} {w : Plc L} (h : un w = v) : w.asIdeal.LiesOver v.asIdeal := by
  subst h
  exact ⟨rfl⟩

private theorem unOf {v : Pl (Lp L)} {w : Plc L} (h : w.asIdeal.LiesOver v.asIdeal) : un w = v :=
  HeightOneSpectrum.ext h.over.symm

private theorem phi_eq (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v)
    [w.asIdeal.LiesOver v.asIdeal] (a : Kv v) : P.φ v w h a = completionMap v w a := by
  have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 (Lp L)) (Lp L) v
  have key : (P.φ v w h) ∘ algebraMap (Lp L) (Kv v) =
      (completionMap v w) ∘ algebraMap (Lp L) (Kv v) := by
    funext x
    simp only [Function.comp_apply]
    rw [completionMap_algebraMap]
    exact (P.φ_alg v w h x).trans (IsScalarTower.algebraMap_apply (Lp L) L _ x).symm
  exact congrFun (hd.equalizer (P.φ_cont v w h) (continuous_completionMap v w) key) a

private def bas (P : Pre L) : Module.Basis (Fin 2) (Lp L) L :=
  (QuadraticAlgebra.basis P.Δ 0).map (AlgEquiv.ofRingEquiv (f := P.e) P.e_alg).toLinearEquiv

private theorem bas_zero (P : Pre L) : bas P 0 = 1 := by
  have h0 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 0 = 1 := by
    ext <;> simp [QuadraticAlgebra.basis] <;> rfl
  rw [bas, Module.Basis.map_apply, h0]
  simp

private theorem bas_one (P : Pre L) : bas P 1 = P.e QuadraticAlgebra.omega := by
  have h1 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 1 = QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.basis]
  rw [bas, Module.Basis.map_apply, h1]
  rfl

private def tt (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) : Kv v ⊗[Lp L] L :=
  x.re ⊗ₜ 1 + x.im ⊗ₜ P.e QuadraticAlgebra.omega

private theorem tt_apply (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) (p : PlacesOver L v) :
    tensorEquiv L v (tt P v x) p = P.rho v p.1 (unOf p.2) x := by
  simp only [tt, map_add (f := _), tensorEquiv_tmul, map_one, mul_one, Pi.add_apply, Pi.mul_apply]
  haveI := p.2
  show completionMap v p.1 x.re + completionMap v p.1 x.im * algebraMap L _ (P.e QuadraticAlgebra.omega) =
    P.φ v p.1 (unOf p.2) x.re + P.φ v p.1 (unOf p.2) x.im * P.rt p.1
  rw [phi_eq P v p.1 (unOf p.2), phi_eq P v p.1 (unOf p.2)]
  rfl

private theorem tt_eq (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) :
    tt P v x = (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm ![x.re, x.im] := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  simp only [Algebra.TensorProduct.basis_apply, bas_zero, bas_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

private theorem tt_inj (P : Pre L) (v : Pl (Lp L)) : Function.Injective (tt P v) := by
  intro x y h
  rw [tt_eq, tt_eq] at h
  have h' := (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm.injective h
  refine QuadraticAlgebra.ext ?_ ?_
  · simpa using congrFun h' 0
  · simpa using congrFun h' 1

private theorem tt_surj (P : Pre L) (v : Pl (Lp L)) : Function.Surjective (tt P v) := by
  intro t
  set c := (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun t
  refine ⟨⟨c 0, c 1⟩, ?_⟩
  rw [tt_eq]
  have hc : (![c 0, c 1] : Fin 2 → Kv v) = c := by
    funext i
    fin_cases i <;> rfl
  simp only [QuadraticAlgebra.re, QuadraticAlgebra.im]
  rw [hc]
  exact (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm_apply_apply t

end UpperTheory.V.Z.Sym.Dict.Br

end

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoBij :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v : Pl (Lp L), Function.Bijective fun (x : Lsq (Kv v) (cv v P.Δ)) (w : {w : Plc L // un w = v}) => P.rho v w.1 w.2 x := by
  intro L _ _ _ P v
  constructor
  · intro x y hxy
    refine tt_inj P v ((tensorEquiv L v).injective (funext fun p => ?_))
    rw [tt_apply, tt_apply]
    exact congrFun hxy ⟨p.1, unOf p.2⟩
  · intro f
    obtain ⟨t, ht⟩ := (tensorEquiv L v).surjective (fun p => f ⟨p.1, unOf p.2⟩)
    obtain ⟨x, rfl⟩ := tt_surj P v t
    refine ⟨x, funext fun w => ?_⟩
    have := congrFun ht ⟨w.1, lies w.2⟩
    rw [tt_apply] at this
    exact this
end
