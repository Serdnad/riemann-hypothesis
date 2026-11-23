module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle286
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle242
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerEqZmOfParity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle002

@[expose] public section

section

open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM

theorem UpperTheory.V.Z.Kato.Joint.avgMF :
    UpperTheory.V.Z.Kato.Joint.AvgMF := by
  intro k l N m θ χ f t α B c hp hk hodd hN hlN hm hχ hf hα hE
  haveI : NeZero N := ⟨hN.ne'⟩
  have hsq : ∀ ν : DirichletCharacter ℂ N, ν (-1) * ν (-1) = 1 := fun ν => by rw [← map_mul]; simp
  have hform : ∀ ν : DirichletCharacter ℂ N, ν (-1) = -θ (-1) → MF k (N * l) (ch (θ⁻¹ * ν)) (frm l N m k θ ν f) :=
    fun ν hν => (GlobalTheory.iterU_level_val_stable k N l m (θ⁻¹ * ν) (fun _ => 0) α B c _ (by omega) hp hα
      (GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity k N l m (θ⁻¹ * ν) θ ν f hk hodd hN hp hm hlN rfl hν hf)).1
  have hsign : (θ * χ) (-1) = -θ (-1) := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hχ]; ring
  have hmain := hform (θ * χ) hsign
  rw [inv_mul_cancel_left] at hmain
  refine ⟨hmain, ?_⟩
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hN).ne'
  have htw : tw2 N (θ (-1)) =
      fun y => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ch ν y := by
    funext y
    rw [GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters N (θ (-1)) hN y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hmes : mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f =
      ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) *
        ((α ^ m)⁻¹ * lam B c (frm l N m k θ ν f)) := by
    unfold mesMu
    rw [htw, funext (measMu_zm_sum k l (hat θ) Finset.univ _ _ _), measMu_val_sum]
    rfl
  rw [hmes, Finset.sum_eq_single_of_mem (θ * χ) (Finset.mem_univ _)]
  · have h2 : (1 : ℂ) - θ (-1) * (θ * χ) (-1) = 2 := by
      rw [hsign]; linear_combination hsq θ
    rw [h2]
    field_simp
  · intro ν _ hne
    have h0 : (ν (-1) - θ (-1)) * (ν (-1) + θ (-1)) = 0 := by linear_combination hsq ν - hsq θ
    rcases mul_eq_zero.1 h0 with h | h
    · rw [sub_eq_zero.1 h, hsq θ]; ring
    · have hne' : θ⁻¹ * ν ≠ χ := fun h' => hne (by rw [← h', mul_inv_cancel_left])
      rw [hE.kill _ _ hne' (hform ν (eq_neg_of_add_eq_zero_left h))]
      ring
end

section

open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM GlobalTheory.KummerEisensteinGalois

private theorem pm_one {R : Type*} [CommRing R] {K : Type*} [Field K] (χ : MulChar R K) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul]; simp

private theorem ind_sum {N : ℕ} [NeZero N] (ν : DirichletCharacter ℂ N) (v : (ZMod N)ˣ) (B : ZMod N) :
    ∑ u : (ZMod N)ˣ, ν u * (if B = (u : ZMod N) * v then 1 else 0) = ν⁻¹ v * ν B := by
  by_cases hB : IsUnit B
  · obtain ⟨w, rfl⟩ := hB
    have h : ∀ u : (ZMod N)ˣ, ((w : ZMod N) = (u : ZMod N) * v) ↔ w * v⁻¹ = u := fun u => by
      rw [← Units.val_mul, Units.val_inj, mul_inv_eq_iff_eq_mul]
    simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Units.val_mul, map_mul]
    rw [mul_comm, MulChar.inv_apply_eq_inv']
    congr 1
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul]; simp
  · rw [MulChar.map_nonunit _ hB, mul_zero]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    exact hB (u * v).isUnit

private theorem twb_sum {N : ℕ} [NeZero N] (θ χ : DirichletCharacter ℂ N) (hχ : χ (-1) = -1) (b : ℤ) (hb : IsCoprime b N) (B : ℤ) :
    ∑ u : (ZMod N)ˣ, (θ * χ) u * twb N (θ (-1)) (((u : ZMod N).val : ℤ) * b) B =
      2 * (θ * χ)⁻¹ (b : ZMod N) * ch (θ * χ) B := by
  obtain ⟨v, hv⟩ : IsUnit (b : ZMod N) := (ZMod.coe_int_isUnit_iff_isCoprime b N).mpr hb.symm
  have h1 := ind_sum (θ * χ) v B
  have h2 := ind_sum (θ * χ) v (-B)
  have h3 : (θ * χ) (-(B : ZMod N)) = -θ (-1) * (θ * χ) B := by
    rw [← neg_one_mul (B : ZMod N), map_mul, MulChar.mul_apply θ χ (-1), hχ]; ring
  simp only [neg_eq_iff_eq_neg] at h2
  simp only [twb, ch, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, ← hv, mul_sub, Finset.sum_sub_distrib,
    mul_left_comm _ (θ (-1)), ← Finset.mul_sum]
  rw [h1, h2, h3]
  linear_combination ((θ * χ)⁻¹ v * (θ * χ) B) * pm_one θ

private theorem Zm_sum {ι : Type*} (S : Finset ι) (k l : ℕ) (u : ℤ → ℂ) (c : ι → ℂ) (v : ι → ℤ → ℂ) (e : ℂ) (w : ℤ → ℂ)
    (F : ℕ → ℕ → ℂ) (h : ∀ B, ∑ j ∈ S, c j * v j B = e * w B) (n : ℕ) :
    ∑ j ∈ S, c j * Zm k l u (v j) F n = e * Zm k l u w F n := by
  simp only [Zm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · calc _ = (x.1 : ℂ) ^ (k - 2) * u x.1 * F x.1 y.2 * ∑ j ∈ S, c j * v j y.1 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h]; ring

theorem UpperTheory.V.Z.Kato.Joint.avgEq :
    UpperTheory.V.Z.Kato.Joint.AvgEq := by
  intro l _ ι N _ θ χ m k ψ a b _ _ hk ho hχ ha hb
  refine ⟨fun hne => ?_, fun a' b' haa hbb => ?_, fun hs i => ?_⟩
  · funext i
    apply ι.injective
    have h1 : ι (ψ (-1)) * ι (ψ (-1)) = 1 := by rw [← map_mul, pm_one, map_one]
    have h2 := pm_one θ
    have h3 : ι (ψ (-1)) + θ (-1) = 0 := by
      refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
      linear_combination h1 - h2
    have h4 : 1 + ι (ψ (-1)) * θ (-1) = 0 := by linear_combination θ (-1) * h3 - h2
    rw [ser_eq_Zm ι N θ m k ψ a b hk ho ha, h4]
    simp
  · have e1 : (a : ZMod N) = a' := (ZMod.intCast_eq_intCast_iff _ _ _).mpr haa
    have e2 : (b : ZMod N) = b' := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hbb
    have ha' : IsCoprime a' N := by
      refine ((ZMod.coe_int_isUnit_iff_isCoprime a' N).mp ?_).symm
      rw [← e1]
      exact (ZMod.coe_int_isUnit_iff_isCoprime a N).mpr ha.symm
    have e3 : twb N (ι (ψ (-1))) b = twb N (ι (ψ (-1))) b' := by
      funext B; simp only [twb, e2]
    funext i
    apply ι.injective
    rw [ser_eq_Zm ι N θ m k ψ a b hk ho ha, ser_eq_Zm ι N θ m k ψ a' b' hk ho ha', e1, e3]
  · have hu : ∀ u : (ZMod N)ˣ, IsCoprime (((u : ZMod N).val : ℤ) * a) N := fun u =>
      IsCoprime.mul_left (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u)) ha
    have key := Zm_sum Finset.univ k l (hat θ) _ _ _ _
      (fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) (twb_sum θ χ hχ b hb) (l ^ m * i)
    simp only [ser_eq_Zm_of_parity ι N θ m k ψ _ _ hk ho (hu _) hs, frm, Uo_iterate]
    calc _ = θ (a : ZMod N) * ∑ u : (ZMod N)ˣ, (θ * χ) u * Zm k l (hat θ) (twb N (θ (-1)) (((u : ZMod N).val : ℤ) * b))
            (fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) (l ^ m * i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, map_mul θ, MulChar.mul_apply]
          ring
      _ = _ := by rw [key]; ring
end
