module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitOfPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TwoNeZeroV
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def QProd : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal),
      ∀ c, e (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = (c, c)

theorem sq_mem (h : IsCMExt F E σ) (x : QE (E := E) v) (hx : sigQ σ v x = x) :
    ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs : Ideal.Quotient.mk (IE (E := E) v) (sigO σ y) = Ideal.Quotient.mk _ y := by
    rw [← sigQ_mk]; exact hx
  have hss : sigO σ (sigO σ y) = y := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ h _)
  obtain ⟨b, hb⟩ := fix_int σ h (y * sigO σ y) (by rw [map_mul, hss, mul_comm])
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hb, map_mul, hs]

theorem idem_cases {k : Type} [Field k] {a : k} (ha : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, ha, mul_one, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

theorem qSplit_of (hP : QProd σ J ψ v) : QSplit σ J ψ v := by
  intro hstd hun hp
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨e, he⟩ := hP hstd hun hp
  refine ⟨e, ?_⟩
  set z : QE (E := E) v := e.symm (1, 0) with hz
  have hez : e z = (1, 0) := by rw [hz, RingEquiv.apply_symm_apply]
  have hinv : ∀ x, sigQ σ v (sigQ σ v x) = x := sigQ_sigQ σ v hstd.1
  have hw : e (sigQ σ v z) = (0, 1) := by
    have hzz : z * z = z := e.injective (by rw [map_mul, hez]; simp)
    have hid : e (sigQ σ v z) * e (sigQ σ v z) = e (sigQ σ v z) := by rw [← map_mul, ← map_mul, hzz]
    have h1 := idem_cases ((Prod.fst_mul _ _).symm.trans (congrArg Prod.fst hid))
    have h2 := idem_cases ((Prod.snd_mul _ _).symm.trans (congrArg Prod.snd hid))
    have h10 : ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).1 ≠ ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).2 :=
      one_ne_zero
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      have h0 : sigQ σ v z = 0 := (map_eq_zero_iff e e.injective).1 (Prod.ext h1 h2)
      have : e z = 0 := by rw [← hinv z, h0, map_zero, map_zero]
      rw [hez] at this
      exact one_ne_zero (congrArg Prod.fst this)
    · exact Prod.ext h1 h2
    · exfalso
      have hf : sigQ σ v z = z := e.injective (by rw [hez]; exact Prod.ext h1 h2)
      obtain ⟨c, hc⟩ := sq_mem σ v hstd.1 z hf
      rw [hzz] at hc
      have := he c
      rw [hc, hez] at this
      apply h10
      rw [this]
    · exfalso
      have h0 : sigQ σ v z = 1 := e.injective (by rw [map_one]; exact Prod.ext h1 h2)
      have : e z = 1 := by rw [← hinv z, h0, map_one, map_one]
      rw [hez] at this
      exact zero_ne_one (congrArg Prod.snd this)
  intro x
  have hx : x = algebraMap _ (QE (E := E) v) (e x).1 * z + algebraMap _ (QE (E := E) v) (e x).2 * (1 - z) := by
    apply e.injective
    rw [map_add (f := _), map_mul, map_mul, he, he, map_sub, map_one, hez]
    ext <;> simp
  have key : e (sigQ σ v x) = ((e x).2, (e x).1) := by
    conv_lhs => rw [hx]
    rw [map_add (f := _), map_mul, map_mul, sigQ_alg, sigQ_alg, map_sub, map_one, map_add (f := _), map_mul, map_mul, he, he,
      map_sub, map_one, hw]
    ext <;> simp
  rw [key]
  rfl

end PI.OmLocU.Red
end
end

section

noncomputable section

namespace PI.OmLocU.UnitaryOrbitCounting

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem orbAll_of_res (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.OrbAll σ J ψ v Λ a Y :=
  PI.OmLocU.Orb.orbAll_of_norm σ J ψ v Λ a Y (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN

theorem countU_of_res' (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.CountU σ J ψ v Λ a Y :=
  PI.OmLocU.Red.countU_of_res σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN hRes a Y

end PI.OmLocU.UnitaryOrbitCounting
end
end

section

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
  PI.OmLocU.Red
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem tr_nd_field {k K : Type} [Field k] [Field K] [Algebra k K] (σ' : K ≃ₐ[k] K) (hne : σ' ≠ AlgEquiv.refl)
    (z : K) (hz : z ≠ 0) : ∃ t : K, t * z + σ' (t * z) ≠ 0 := by
  have hu : ∃ u : K, u + σ' u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    have h1 : (1 : K) + 1 = 0 := by simpa using h 1
    ext u
    have h2 : σ' u = -u := eq_neg_of_add_eq_zero_right (h u)
    rw [h2]
    show -u = u
    have h3 : u + u = 0 := by rw [← mul_one u, ← mul_add, h1, mul_zero]
    exact (eq_neg_of_add_eq_zero_left h3).symm
  obtain ⟨u, hu⟩ := hu
  refine ⟨u * z⁻¹, ?_⟩
  rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
  exact hu

theorem tr_nd_prod {k : Type} [Field k] (z : k × k) (hz : z ≠ 0) :
    ∃ t : k × k, t * z + (RingEquiv.prodComm (R := k) (S := k)).toRingHom (t * z) ≠ 0 := by
  by_cases h1 : z.1 = 0
  · have h2 : z.2 ≠ 0 := by
      intro h2
      exact hz (Prod.ext h1 h2)
    refine ⟨(0, z.2⁻¹), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h2] at this
  · refine ⟨(z.1⁻¹, 0), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h1] at this

theorem trNd_of_res {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) (hcm : IsCMExt F E σ)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (hres : IsRes σ v ϖ τ π) (hnd : ∀ z : K, z ≠ 0 → ∃ t : K, t * z + τ (t * z) ≠ 0)
    (c : Fv F v ⊗[F] E) (hc : c ∈ OEv (E := E) v) (hcn : sc (E := E) v (ϖ⁻¹) * c ∉ OEv (E := E) v) :
    ∃ t ∈ OEv (E := E) v, IsU v (t * c + sigR (Fv F v) σ (t * c)) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨hsurj, hker, hsig⟩ := hres
  let cO : OR (E := E) v := ⟨c, hc⟩
  have hc0 : π cO ≠ 0 := by
    intro h
    obtain ⟨d, hd0, hd⟩ := (hker cO).1 h
    apply hcn
    have hd' : c = sc (E := E) v ϖ * d := hd
    rw [hd', ← mul_assoc, sc_eq, sc_eq, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_mul]
    exact hd0
  obtain ⟨tb, htb⟩ := hnd _ hc0
  obtain ⟨tO, htO⟩ := hsurj tb
  have ht0 : (tO : Fv F v ⊗[F] E) ∈ OEv (E := E) v := tO.2
  have htc0 : (tO : Fv F v ⊗[F] E) * c ∈ OEv (E := E) v := (tO * cO).2
  let yO : OR (E := E) v := ⟨sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c), sigR_mem σ v htc0⟩
  have hy : π yO = τ (π (tO * cO)) := hsig (tO * cO) yO rfl
  set s := (tO : Fv F v ⊗[F] E) * c + sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c) with hs
  have hsO : π (tO * cO + yO) ≠ 0 := by
    rw [map_add (f := _), hy, map_mul, htO]
    exact htb
  have hs0 : s ∈ OEv (E := E) v := (tO * cO + yO).2
  have hsf : sigR (Fv F v) σ s = s := by
    rw [hs, map_add (f := _), sigR_invol σ v hcm, add_comm]
  refine ⟨tO, ht0, ?_⟩
  obtain ⟨a, ha, hsa⟩ := fix_int σ v hcm hs0 hsf
  rw [← hs, hsa]
  by_cases hva : Valued.v a < 1
  · exfalso
    obtain ⟨d, hd⟩ := (mem_unifO_iff v hϖ ⟨a, ha⟩).2 hva
    apply hsO
    apply (hker _).2
    refine ⟨sc (E := E) v (d : Fv F v), sc_mem v d.2, ?_⟩
    show s = _
    rw [hsa, sc_eq, sc_eq, sc_eq, ← map_mul]
    exact congrArg _ hd
  · have ha1 : Valued.v a = 1 := le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 ha) (not_lt.1 hva)
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact zero_ne_one ha1
    have hai : a⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ha1, inv_one]
    refine ⟨sc (E := E) v (a⁻¹), sc_mem v hai, ?_⟩
    rw [sc_eq, sc_eq, ← map_mul, mul_inv_cancel₀ ha0, map_one]

theorem trNd_of (hR : ResAlg σ J ψ v) : TrNd σ J ψ v := by
  intro hstd hun ϖ hϖ c hc hcn
  obtain ⟨k, _, _, -, hcase⟩ := hR hstd hun ϖ hϖ
  rcases hcase with ⟨-, K, _, _, σ', π, -, -, hne, hres⟩ | ⟨-, π, hres⟩
  · exact trNd_of_res σ v (σ' : K →+* K) π hstd.1 hϖ hres (fun z hz => tr_nd_field σ' hne z hz) c hc hcn
  · exact trNd_of_res σ v _ π hstd.1 hϖ hres (fun z hz => tr_nd_prod z hz) c hc hcn

theorem unitNorm_of_res (hR : ResAlg σ J ψ v) : UnitNorm σ J ψ v Λ :=
  unitNorm_of σ J ψ v Λ (fixLoc_holds σ v) (trNd_of σ J ψ v hR) (primPerp_holds σ J ψ v Λ)

end PI.OmLocU.UnN
end
end
