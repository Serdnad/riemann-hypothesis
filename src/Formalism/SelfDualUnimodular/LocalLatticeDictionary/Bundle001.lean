module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle003
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.AlgebraMapNeZeroOfMemHcompl
public import Lemmata.Denominators.Denom
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.UnimodOfSelfDual
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.LF

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem vec_denom (M : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ m : ℕ, 0 < m ∧ (m : 𝓞 E) • v ∈ M := by
  first | exact Bl.DenominatorsAlt.goal1 .. | (apply Bl.DenominatorsAlt.goal1 <;> assumption) | (intros; apply Bl.DenominatorsAlt.goal1 <;> assumption)

theorem lat_denom (L M : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, (N : 𝓞 E) • x ∈ M := by
  classical
  obtain ⟨S, hS⟩ := hL
  choose f hf0 hfM using fun v : Fin n → E => vec_denom M hsp v
  refine ⟨∏ s ∈ S, f s, Finset.prod_pos (fun i _ => hf0 i), ?_⟩
  intro x hx
  rw [← hS] at hx
  have hle : Submodule.span (𝓞 E) (S : Set (Fin n → E)) ≤
      M.comap (((∏ s ∈ S, f s : ℕ) : 𝓞 E) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro s hs
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hs)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact M.smul_mem _ (hfM s)
  have h2 := hle hx
  rwa [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h2

theorem loc_le_of_denom {L M : Submodule (𝓞 E) (Fin n → E)} {N : ℕ} (hN : ∀ x ∈ L, (N : 𝓞 E) • x ∈ M)
    {p : Ideal (𝓞 E)} (hp : p.IsPrime) (hNp : (N : 𝓞 E) ∉ p) :
    Formalism.HermitianLatticesTheory.loc (K := E) p L ≤ Formalism.HermitianLatticesTheory.loc (K := E) p M := by
  rintro x ⟨t, ht, htx⟩
  have hNh : (N : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p := by
    rw [mem_hcompl_iff hp, mem_conjIdeal_iff, map_natCast]
    exact ⟨hNp, hNp⟩
  refine ⟨(N : 𝓞 E) * t, mul_mem hNh ht, ?_⟩
  rw [mul_smul]; exact hN _ htx

theorem lattice_locally_finite : LocFinite := by
  intro E _ _ _ n L M hLfg hMfg hLsp hMsp
  obtain ⟨N₁, hN₁, h1⟩ := lat_denom L M hLfg hMsp
  obtain ⟨N₂, hN₂, h2⟩ := lat_denom M L hMfg hLsp
  have h0 : ((N₁ * N₂ : ℕ) : 𝓞 E) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (Nat.mul_pos hN₁ hN₂).ne'
  refine (Ring.HasFiniteQuotients.finite_setOfPred_mem _ h0).subset ?_
  rintro p ⟨hp, hne⟩
  by_contra hNp
  apply hne
  have hp' := hp.isPrime
  simp only [Set.mem_ofPred_eq, Nat.cast_mul] at hNp
  have n1 : (N₁ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_right _ h)
  have n2 : (N₂ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_left _ h)
  exact le_antisymm (loc_le_of_denom h2 hp' n2) (loc_le_of_denom h1 hp' n1)

end Formalism.L2.SG.Pf.LatDictZ.Z0.LF
end
end

section

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem loc_iff_of_isom (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    {L M : Submodule (𝓞 E) (Fin n → E)} {p : Ideal (𝓞 E)}
    (hm : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ g x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M)
    (γ : GL (Fin n) E) (hγg : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (v : Fin n → E) :
    v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔ ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v := by
  constructor
  · intro hv
    refine ⟨g.symm v, (hm _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hv), ?_⟩
    rw [hγg, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    rw [hγg]; exact (hm w).1 hw

theorem semiGenus_of (hG : SemiGenusLoc) : SemiGenus := by
  intro E _ _ _ n J hK hJh hdet L M hLfg hMfg hLsp hMsp hLd hMd p hp
  obtain ⟨g, hg, hm⟩ := hG E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  exact ⟨γ, hγ, loc_iff_of_isom g hm γ hγg⟩

theorem algebraMap_ne_zero' {p : Ideal (𝓞 E)} (hp : p.IsPrime) {t : 𝓞 E}
    (ht : t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) : algebraMap (𝓞 E) E t ≠ 0 :=
  algebraMap_ne_zero_of_mem_hcompl hp ht

theorem smul_eq_alg (t : 𝓞 E) (v : Fin n → E) : t • v = (algebraMap (𝓞 E) E t) • v := by
  rw [algebraMap_smul]

theorem semiGenusZ_of (hZ : SemiGenusZLoc) : SemiGenusZ := by
  intro E _ _ _ n J hK hJh hdet r s z L M hLfg hMfg hLsp hMsp hLd hMd hsz hU hSL hSM hzL hzM hPL hPM p hp
  have hpP := hp.isPrime

  have hU' : ∀ w ∈ Submodule.span E (Set.range s),
      w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup ↔ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup := by
    intro w hw
    change w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M
    constructor
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).1 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).2 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
  have hsplit : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ w ∈ N, ∃ w₁ ∈ N, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      ∀ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup, ∃ w₁ ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup,
        w₁ ∈ Submodule.span E (Set.range s) ∧ ∀ a, hJ J (s a) (w - w₁) = 0 := by
    intro N hN w hw
    obtain ⟨t, ht, htw⟩ := hw
    obtain ⟨u, huN, hus, hu0⟩ := hN _ htw
    have ht0 := algebraMap_ne_zero' hpP ht
    refine ⟨(algebraMap (𝓞 E) E t)⁻¹ • u, ⟨t, ht, ?_⟩, Submodule.smul_mem _ _ hus, fun a => ?_⟩
    · rw [smul_eq_alg, smul_smul, mul_inv_cancel₀ ht0, one_smul]; exact huN
    · have e : w - (algebraMap (𝓞 E) E t)⁻¹ • u = (algebraMap (𝓞 E) E t)⁻¹ • (t • w - u) := by
        rw [smul_eq_alg, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [e, map_smul, smul_eq_mul, hJ_apply, hu0 a, mul_zero]
  have hprim : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ c : E, c • z ∈ N → c ∈ (algebraMap (𝓞 E) E).range) →
      ∀ c : E, c • z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup → c ∈ locRing p := by
    intro N hN c hc
    obtain ⟨t, ht, htc⟩ := hc
    rw [smul_eq_alg, smul_smul] at htc
    obtain ⟨r, hr⟩ := hN _ htc
    have ht0 := algebraMap_ne_zero' hpP ht
    rw [mem_locRing, mem_locR_iff hpP]
    refine ⟨r, t, ht, ?_⟩
    rw [hr]; field_simp
  have hzloc : ∀ N : Submodule (𝓞 E) (Fin n → E), z ∈ N → z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup :=
    fun N hz => ⟨1, one_mem _, by rw [one_smul]; exact hz⟩
  obtain ⟨g, hg, hgs, hgz, hm⟩ := hZ E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp s z
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
    hsz hU' (hsplit L hSL) (hsplit M hSM) (hzloc L hzL) (hzloc M hzM) (hprim L hPL) (hprim M hPM)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  refine ⟨γ, hγ, fun a => by rw [hγg, hgs a], by rw [hγg, hgz], loc_iff_of_isom g hm γ hγg⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
end
end
