module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFLeSpanK
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle011
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def phi {n : ℕ} (b : Fin n → V) (a : Fin n → 𝓞 F) : (Fin n → 𝓞 K) →ₗ[𝓞 K] V where
  toFun z := ∑ i, (jK (z i) / jK (ι (a i))) • b i
  map_add' z z' := by
    simp only [Pi.add_apply, map_add (f := _), add_div, add_smul, Finset.sum_add_distrib]
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K c, smul_smul, mul_div_assoc]

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {n : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F}

private theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : jK (ι a) = algebraMap F K (a : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  rw [coe_iota_eq_algebraMap_coe]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha

theorem h_phi (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
    (z : Fin n → 𝓞 K) (k : Fin n) : h (b k) (phi b a z) = jK (z k) := by
  show h (b k) (∑ i, (jK (z i) / jK (ι (a i))) • b i) = jK (z k)
  rw [map_sum, Finset.sum_eq_single k]
  · rw [LinearMap.map_smul, smul_eq_mul, hdiag k, ← coe_iota_eq_algebraMap_coe,
      div_mul_cancel₀ _ (jK_iota_ne_zero (ha k))]
  · intro i _ hik
    rw [LinearMap.map_smul, horth k i hik.symm, smul_zero]
  · simp

theorem phi_mem (hbX : ∀ i, b i ∈ X) (z : Fin n → 𝓞 K) : phi b a z ∈ X := by
  show (∑ i, (jK (z i) / jK (ι (a i))) • b i) ∈ X
  exact X.sum_mem fun i _ => X.smul_mem _ (hbX i)

theorem disc_equiv (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn X L) (hbX : ∀ i, b i ∈ X)
    (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
    (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0) :
    Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] ∀ i : Fin n, 𝓞 K ⧸ extP K 𝔭 ^ vF 𝔭 (a i)) := by
  classical
  haveI := h𝔭.isPrime
  have hA : ∀ z, phi b a z ∈ locF 𝔭 (dualIn h X L) := fun z =>
    (mem_locF_dualIn_iff hbX hloc horth hdiag ha hF h𝔭 hL _).mpr
      ⟨phi_mem hbX z, fun i => by rw [h_phi horth hdiag ha]; exact HU.jK_mem_SP _⟩
  let ψ₀ : (Fin n → 𝓞 K) →ₗ[𝓞 K] locF 𝔭 (dualIn h X L) := LinearMap.codRestrict _ (phi b a) hA
  let ψ := ((locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype).mkQ.comp ψ₀
  have hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun i => extP K 𝔭 ^ vF 𝔭 (a i)) := by
    ext z
    simp only [ψ, ψ₀, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      LinearMap.codRestrict_apply, Submodule.mem_pi, Set.mem_univ, forall_const]
    rw [mem_B_iff hbX hloc horth hdiag ha h𝔭.isPrime hL]
    simp only [h_phi horth hdiag ha, div_mem_SP_iff h𝔭 (ha _)]
    exact ⟨fun hz => hz.2, fun hz => ⟨phi_mem hbX z, hz⟩⟩
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ :=
      Submodule.Quotient.mk_surjective ((locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype) q
    have hx' := (mem_locF_dualIn_iff hbX hloc horth hdiag ha hF h𝔭 hL x).mp hx
    choose z hz using fun i => exists_sub_div_mem_SP h𝔭 (ha i) (hx'.2 i)
    refine ⟨z, ?_⟩
    simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [ψ₀, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub,
      LinearMap.codRestrict_apply]
    rw [mem_B_iff hbX hloc horth hdiag ha h𝔭.isPrime hL]
    refine ⟨X.sub_mem (phi_mem hbX z) hx'.1, fun i => ?_⟩
    rw [map_sub, h_phi horth hdiag ha]
    have := Subring.neg_mem _ (hz i)
    rwa [← neg_div, neg_sub] at this
  exact ⟨(LinearMap.quotKerEquivOfSurjective ψ hsurj).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ Submodule.quotientPi _⟩

end

end Formalism.L2.SG.Pf.G2
end
end

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

section

variable {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] {k : ℕ}

local notation "mk" => Ideal.Quotient.mk (extP K 𝔭 ^ k)

theorem exists_mk_iff {d : 𝓞 F} (hd : d ≠ 0) (hk : vF 𝔭 d ≤ k) (z : 𝓞 K) :
    (∃ w : 𝓞 K ⧸ extP K 𝔭 ^ k, mk z = w * mk (ι d)) ↔ jK z / jK (ι d) ∈ HU.SP K 𝔭 := by
  have hd0 : jK (ι d) ≠ 0 := by
    change algebraMap F K (d : F) ≠ 0
    exact (map_eq_zero_iff _ (algebraMap F K).injective).not.mpr (by exact_mod_cast hd)
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    have e : mk z = mk (w * ι d) := by rw [hw, map_mul]
    have hx := Ideal.pow_le_pow_right hk (Ideal.Quotient.eq.mp e)
    obtain ⟨t, ht, htx⟩ := exists_mul_mem_span h𝔭 hd
    have hle : Ideal.span {t} * 𝔭 ^ vF 𝔭 d ≤ Ideal.span {d} :=
      Ideal.span_singleton_mul_le_iff.mpr htx
    have hmap := Ideal.map_mono (f := ι) hle
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, Ideal.map_pow,
      Ideal.map_span, Set.image_singleton, ← extP] at hmap
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp
      (Ideal.span_singleton_mul_le_iff.mp hmap _ hx)
    have hdiv : jK (z - w * ι d) / jK (ι d) ∈ HU.SP K 𝔭 := by
      refine HU.mem_SP.mpr ⟨t, ht, q, ?_⟩
      rw [← mul_div_assoc]
      exact (eq_div_iff hd0).mpr (by simpa only [map_mul] using congrArg jK hq)
    have hsum : jK z / jK (ι d) = jK (z - w * ι d) / jK (ι d) + jK w := by
      rw [map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ hd0, sub_add_cancel]
    rw [hsum]
    exact add_mem hdiv (HU.jK_mem_SP w)
  · intro h
    obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.mp h
    obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht k
    have hmul : w * ι d = ι t * z := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_mul, map_mul, hw, mul_assoc, div_mul_cancel₀ _ hd0]
    have heq : z - (ι u * w) * ι d = ι (1 - t * u) * z := by
      rw [mul_assoc, hmul, map_sub, map_one, map_mul]
      ring
    have hmem : z - (ι u * w) * ι d ∈ extP K 𝔭 ^ k := by
      rw [heq]
      exact Ideal.mul_mem_right _ _ (localizedQuotients.ι_mem_pow hu)
    refine ⟨mk (ι u * w), ?_⟩
    have e : mk z = mk ((ι u * w) * ι d) := Ideal.Quotient.eq.mpr hmem
    rw [e, map_mul]

theorem exists_mk_mul_iff {d d' : 𝓞 F} (hd : d ≠ 0) (hd' : d' ≠ 0) (hk : vF 𝔭 d + vF 𝔭 d' ≤ k)
    (z : 𝓞 K) :
    (∃ w : 𝓞 K ⧸ extP K 𝔭 ^ k, mk z = mk (ι d) * w * mk (ι d')) ↔
      jK z / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by
  have hprime : Prime 𝔭 := Ideal.prime_of_isPrime
    (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)) h𝔭.isPrime
  have hfin {x : 𝓞 F} (hx : x ≠ 0) : FiniteMultiplicity 𝔭 (Ideal.span {x}) :=
    FiniteMultiplicity.of_prime_left hprime (by simpa using hx)
  have hv {x : 𝓞 F} (hx : x ≠ 0) : vF 𝔭 x = multiplicity 𝔭 (Ideal.span {x}) := by
    have hset : {n : ℕ | x ∈ 𝔭 ^ n} = Set.Iic (multiplicity 𝔭 (Ideal.span {x})) := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      rw [← (hfin hx).pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    rw [vF, hset, csSup_Iic]
  have hdd' := mul_ne_zero hd hd'
  have hval : vF 𝔭 (d * d') = vF 𝔭 d + vF 𝔭 d' := by
    rw [hv hdd', hv hd, hv hd', ← Ideal.span_singleton_mul_span_singleton]
    exact multiplicity_mul hprime (by simpa only [Ideal.span_singleton_mul_span_singleton] using hfin hdd')
  have hmk (w : 𝓞 K ⧸ extP K 𝔭 ^ k) :
      mk (ι d) * w * mk (ι d') = w * mk (ι (d * d')) := by
    simp only [map_mul]
    rw [mul_comm (mk (ι d)) w, mul_assoc]
  have hden : jK (ι (d * d')) = jK (ι d) * jK (ι d') := by rw [map_mul, map_mul]
  rw [← hden, ← exists_mk_iff hdd' (hval.symm ▸ hk) z]
  simp only [hmk]

variable {m : ℕ} (a : Fin m → 𝓞 F)

def gramO (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Yᴴ * diagonal (fun i => ι (a i)) * Y - diagonal (fun i => ι (a i))

variable {a}

theorem diagQ_eq : diagQ K 𝔭 k a = (diagonal fun i => ι (a i)).map mk := by
  unfold diagQ
  rw [Matrix.diagonal_map (map_zero _)]

theorem condP_iff_eqP (ha : ∀ i, a i ≠ 0) (hk : ∀ i, vF 𝔭 (a i) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ P, P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y.map mk) ↔
      ∀ i j, jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  unfold diagQ
  constructor
  · rintro ⟨P, hP⟩ i j
    refine (exists_mk_iff (ha j) (hk j) _).mp ⟨P i j, ?_⟩
    have := congrFun (congrFun hP i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at this
    rw [map_mul, this]
  · intro h
    choose P hP using fun i j => (exists_mk_iff (ha j) (hk j) (ι (a i) * Y i j)).mpr (h i j)
    refine ⟨Matrix.of P, ?_⟩
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.of_apply]
    rw [← hP i j, map_mul]

theorem form_eq_map (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a = (gramO a Y).map mk := by
  have hs : Function.Semiconj (Ideal.Quotient.mk (extP K 𝔭 ^ k)) star star :=
    fun x => (idealPowerSpanBounds.star_mk 𝔭 k x).symm
  have e : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K),
      M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = (Ideal.Quotient.mk (extP K 𝔭 ^ k)).mapMatrix M :=
    fun _ => rfl
  rw [e (gramO a Y)]
  unfold gramO
  rw [map_sub, map_mul, map_mul, ← e, ← e, ← e, diagQ_eq, Matrix.conjTranspose_map _ hs]

theorem condW_iff (ha : ∀ i, a i ≠ 0) (hk : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ W, (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a =
        diagQ K 𝔭 k a * W * diagQ K 𝔭 k a) ↔
      ∀ i j, jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭 := by
  rw [form_eq_map Y]
  unfold diagQ
  constructor
  · rintro ⟨W, hW⟩ i j
    refine (exists_mk_mul_iff (ha i) (ha j) (hk i j) _).mp ⟨W i j, ?_⟩
    have := congrFun (congrFun hW i) j
    simpa only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  · intro h
    choose W hW using fun i j => (exists_mk_mul_iff (ha i) (ha j) (hk i j) (gramO a Y i j)).mpr (h i j)
    refine ⟨Matrix.of W, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    exact hW i j

theorem condZ_iff (ha : ∀ i, a i ≠ 0) (hk : ∀ i, vF 𝔭 (a i) ≤ k)
    (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ Z, Y.map mk - Y'.map mk = Z * diagQ K 𝔭 k a) ↔
      ∀ i j, jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  unfold diagQ
  constructor
  · rintro ⟨Z, hZ⟩ i j
    refine (exists_mk_iff (ha j) (hk j) _).mp ⟨Z i j, ?_⟩
    have := congrFun (congrFun hZ i) j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal] at this
    rw [map_sub, this]
  · intro h
    choose Z hZ using fun i j => (exists_mk_iff (ha j) (hk j) (Y i j - Y' i j)).mpr (h i j)
    refine ⟨Matrix.of Z, ?_⟩
    ext i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal, Matrix.of_apply]
    rw [← hZ i j, map_sub]

end

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {v : V} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem form_ozmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (y v : V) : h y (c • v) = c • h y v := by
  rw [← algebraMap_smul K c v, LinearMap.map_smul, algebraMap_smul]

theorem form_ozmul_left_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) {y v : V}
    (hy : h y v ∈ (1 : Submodule (𝓞 K) K)) : h (c • y) v ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← algebraMap_smul K c y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨c0, hc0⟩ := Submodule.mem_one.mp (VecSplit.star_alg_mem_one c)
  obtain ⟨z0, hz0⟩ := Submodule.mem_one.mp hy
  exact Submodule.mem_one.mpr ⟨c0 * z0, by rw [map_mul, hc0, hz0]⟩

theorem mem_locF_dualIn {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    (hL : L.FG) (𝔭 : Ideal (𝓞 F)) {v : V} (hv : v ∈ X)
    (H : ∀ y ∈ L, h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) : v ∈ locF 𝔭 (dualIn h X L) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have H' : ∀ y ∈ s, ∃ t ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      t • h y v ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    exact H y (hs ▸ Submodule.subset_span hy)
  choose! t ht using H'
  refine ⟨∏ y ∈ s, t y, Submonoid.prod_mem _ fun y hy => (ht y hy).1, ?_⟩
  refine ⟨X.restrictScalars (𝓞 K) |>.smul_mem _ hv, ?_⟩
  show (∏ y ∈ s, t y) • v ∈ Formalism.HermitianLatticesTheory.dual h L
  rw [mem_dual_iff]
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [form_ozmul_right, ← Finset.prod_erase_mul s t hy, mul_smul]
    exact Submodule.smul_mem _ _ (ht y hy).2
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact form_ozmul_left_mem h c ha

theorem projection_into_holds : ProjInto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX x hx
  apply mem_locF_dualIn hL.1 𝔭 (Submodule.projection_apply_mem hc x)
  intro y hy
  have hyΛ : y ∈ Λ := by
    have : y ∈ locF 𝔭 L := LocalizedFibreSets.le_locF 𝔭 L hy
    rw [← hΛX] at this
    exact this.1
  have hyX : y ∈ X := le_of_isLatIn hL y hy
  have e := Submodule.projection_add_projection_eq_self hc x
  have h0 : h y (Y.projection X hc.symm x) = 0 := hXY y hyX _ (Submodule.projection_apply_mem _ x)
  have hx' : x ∈ dualF h 𝔭 Λ := by rw [hΛd]; exact hx
  have := hx' y hyΛ
  rw [← e, map_add (f := _), h0, add_zero] at this
  exact this

end Formalism.L2.SG.Pf.G6
end
end
