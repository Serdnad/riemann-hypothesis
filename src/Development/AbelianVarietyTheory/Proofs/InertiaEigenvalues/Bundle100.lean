module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem units_near_one_inverse_continuousAt (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)

theorem et_units_near_one_inverse_continuousAt :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  fun F _ _ _ _ _ A => units_near_one_inverse_continuousAt F A.K

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LatTop

theorem isLocallyConstant_indicator_one' {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem lattice_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)),
    IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧
      IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  intro F E _ _ _ _ hU A r j
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  set B : Set E := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set V : Set (Fin r → E) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hS : {y : A.L | ∀ i, ‖j y i‖ ≤ 1} = jF ⁻¹' V := by
    ext y
    simp [hV, hB, jF]
  have hS' : jF ⁻¹' V = jF.symm '' V := (jF.toEquiv.image_symm_eq_preimage V).symm
  have hSo : IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVo.preimage hc
  have hSc : IsClosed {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVc.preimage hc
  have hSk : IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := by
    rw [hS, hS']; exact hVk.image hcs
  exact ⟨hSo, hSk, isLocallyConstant_indicator_one' ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LatTop
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NotIntegral

theorem inv_small_not_integral : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  intro K B a ha m hint
  obtain ⟨ha0, hmax, -⟩ := ha
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let f : K.E →ₐ[K.O] (B.A ⧸ m.asIdeal) := IsScalarTower.toAlgHom K.O K.E (B.A ⧸ m.asIdeal)
  have hf : Function.Injective f := (algebraMap K.E (B.A ⧸ m.asIdeal)).injective
  have hE : IsIntegral K.O (algebraMap K.O K.E a)⁻¹ := (isIntegral_algHom_iff f hf).1 hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hE
  have hne : algebraMap K.O K.E a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]; exact ha0
  have hab : a * b = 1 := by
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  exact (IsLocalRing.mem_maximalIdeal a).1 hmax ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩

end GlobalTheory.NotIntegral
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem etale_norm_continuous_and_zero (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := by
  classical
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  let b0 := Module.finBasisOfFinrankEq F E h2
  let b : Module.Basis (Fin 2) A.K A.L := hb.basis b0
  have hN : ∀ y, A.NL y = (Algebra.leftMulMatrix b y).det := fun y => Algebra.norm_eq_matrix_det b y
  refine ⟨?_, ?_⟩
  · have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := funext hN
    rw [this]
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    let f : A.L →ₗ[F] A.K := ((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine hf.congr fun y => ?_
    simp [f, Algebra.leftMulMatrix_eq_repr_mul]
  · rw [hN, map_zero]
    simp

end GlobalTheory
end

section

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.TorusOrbitLat

section General

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) :
    t ∈ stabLat O L ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L := Iff.rfl

theorem mem_intUnits_iff (t : Aˣ) :
    t ∈ intUnits O A ↔ IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A) := Iff.rfl

theorem mem_mulLat_unit (u : Aˣ) (L : Submodule O A) (w : A) :
    w ∈ mulLat O (u : A) L ↔ ((u⁻¹ : Aˣ) : A) * w ∈ L := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_eq_iff (u v : Aˣ) (L : Submodule O A) :
    mulLat O (u : A) L = mulLat O (v : A) L ↔ u⁻¹ * v ∈ stabLat O L := by
  rw [mem_stabLat_iff]
  constructor
  · intro h y
    calc y ∈ L ↔ (v : A) * y ∈ mulLat O (v : A) L := by rw [mem_mulLat_unit]; simp
      _ ↔ (v : A) * y ∈ mulLat O (u : A) L := by rw [h]
      _ ↔ ((u⁻¹ * v : Aˣ) : A) * y ∈ L := by rw [mem_mulLat_unit, Units.val_mul, mul_assoc]
  · intro h
    ext w
    rw [mem_mulLat_unit, mem_mulLat_unit, h (((v⁻¹ : Aˣ) : A) * w)]
    simp [mul_assoc]

theorem isIntegral_inv_mul_iff (t u : Aˣ) (hu : u ∈ intUnits O A) (w : A) :
    IsIntegral O ((((t * u)⁻¹ : Aˣ) : A) * w) ↔ IsIntegral O (((t⁻¹ : Aˣ) : A) * w) := by
  rw [mem_intUnits_iff] at hu
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  constructor
  · intro h
    have := hu.1.mul h
    simpa using this
  · intro h
    exact hu.2.mul h

end General

section Main

variable {K : UQ} (B : InvAlg K)

theorem rho_cond_mk (t : B.T) (w : B.A) :
    IsIntegral K.O (((((Quotient.out (QuotientGroup.mk t : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T) : B.T) :
      B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) ↔ IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) t
  rw [hh, Subgroup.coe_mul]
  exact isIntegral_inv_mul_iff _ _ (Subgroup.mem_subgroupOf.mp h.2) w

theorem orbit_count : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  intro K B L hSle hidx a hrho m k hmk hin hout
  set w : B.A := algebraMap K.O B.A a with hw
  set H : Subgroup B.T := (stabLat K.O L).subgroupOf B.T with hH
  set Kc : Subgroup B.T := (intUnits K.O B.A).subgroupOf B.T with hKc
  have hHK : H ≤ Kc := by
    intro x hx
    rw [hH, Subgroup.mem_subgroupOf] at hx
    rw [hKc, Subgroup.mem_subgroupOf]
    exact hSle ⟨hx, x.2⟩
  have hidx_eq : (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) = (H.subgroupOf Kc).index := by
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : intUnits K.O B.A ⊓ B.T ≤ B.T),
      Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right]
    rfl
  have hQfin : Finite (Kc ⧸ H.subgroupOf Kc) := by
    rw [← Subgroup.index_ne_zero_iff_finite, ← hidx_eq]; exact hidx
  have hRfin : ∀ j, Finite {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => (Nat.card_pos_iff.mp (hrho j)).2
  have hrho_eq : ∀ j, B.rho (w ^ j) = Nat.card {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => rfl
  let e := Subgroup.quotientEquivProdOfLE hHK
  have he1 : ∀ g : B.T, (e (QuotientGroup.mk g)).1 = QuotientGroup.mk g := fun g => rfl

  let Y := {c : B.T ⧸ H // w ^ k ∈ mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L}
  let fY : Y → {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ w ^ k ∈ M} :=
    fun c => ⟨mulLat K.O (((Quotient.out c.1 : B.T) : B.Aˣ) : B.A) L, ⟨_, (Quotient.out c.1).2, rfl⟩, c.2⟩
  have hfY : Function.Bijective fY := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      have h' : mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L = mulLat K.O (((Quotient.out c' : B.T) : B.Aˣ) : B.A) L :=
        congrArg Subtype.val h
      rw [mulLat_eq_iff] at h'
      apply Subtype.ext
      change c = c'
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h')
    · rintro ⟨M, ⟨t, ht, rfl⟩, hM⟩
      have hc := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H))
      rw [hH, Subgroup.mem_subgroupOf] at hc
      have key : mulLat K.O (((Quotient.out (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H) : B.T) : B.Aˣ) : B.A) L =
          mulLat K.O (t : B.A) L := by
        rw [mulLat_eq_iff]; simpa using hc
      exact ⟨⟨_, key ▸ hM⟩, Subtype.ext key⟩
  have hcardXY := Nat.card_congr (Equiv.ofBijective fY hfY)

  have key1 : ∀ g : B.T, ((((g : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w ^ k ∈ L) →
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A) := by
    intro g hg
    rw [he1 g, rho_cond_mk]
    have := hout _ hg
    convert this using 1
    rw [pow_add]; ring
  let U : Y → {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) := fun c =>
    (⟨(e c.1).1, by
      have := key1 (Quotient.out c.1) (by rw [← mem_mulLat_unit]; exact c.2)
      rwa [QuotientGroup.out_eq'] at this⟩, (e c.1).2)
  have hU : Function.Injective U := by
    intro c c' h
    apply Subtype.ext
    apply e.injective
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 h2
  have hYfin : Finite Y := by
    haveI := hRfin (k + m)
    exact Finite.of_injective U hU

  have key2 : ∀ g : B.T,
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A) →
      w ^ k ∈ mulLat K.O ((g : B.Aˣ) : B.A) L := by
    intro g hg
    rw [he1 g, rho_cond_mk] at hg
    rw [mem_mulLat_unit]
    have := hin _ hg
    convert this using 1
    rw [← Nat.add_sub_cancel' hmk, pow_add, Nat.add_sub_cancel_left]; ring
  let D : {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) → Y := fun p =>
    ⟨e.symm (p.1.1, p.2), by
      have hc : e (e.symm (p.1.1, p.2)) = (p.1.1, p.2) := e.apply_symm_apply _
      apply key2
      rw [QuotientGroup.out_eq', hc]
      exact p.1.2⟩
  have hD : Function.Injective D := by
    intro p p' h
    have h' := e.symm.injective (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) h2
  refine ⟨?_, ?_, ?_⟩
  · exact Finite.of_equiv Y (Equiv.ofBijective fY hfY)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    exact (Nat.card_prod _ _).symm.trans_le (Nat.card_le_card_of_injective D hD)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    haveI := hRfin (k + m)
    exact (Nat.card_le_card_of_injective U hU).trans_eq (Nat.card_prod _ _)

end Main

end GlobalTheory.TorusOrbitLat
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def Hyp (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ) : Prop :=
  IsField A.K ∧ IsField A.L ∧ IsStdChar ψ ∧ SelfDual μ (A.kerL ψ x) ∧
    ∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)

def nOp (A : Et F E) (ψ : AddChar F ℂ) (x z : A.K) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => A.psiK ψ (z * x * A.NL y) * φ y

def mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)

def fOp (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (φ : A.L → ℂ) : A.L → ℂ :=
  fourB μ (A.kerL ψ x) φ

def gaussInt (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (S : Set A.L) : ℂ :=
  ∫ y in S, A.psiK ψ (u * x * A.NL y) ∂μ

def IsStableGauss (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (G : ℂ) : Prop :=
  ∃ Λ₀ : AddSubgroup A.L, IsOpen (Λ₀ : Set A.L) ∧ IsCompact (Λ₀ : Set A.L) ∧
    ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → Λ₀ ≤ Λ →
      gaussInt A ψ x μ u Λ = G

end GlobalTheory.JR.WeilQuad
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem norm_sub_notMem_of_not_norm :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ∀ (x : A.Kˣ) (a : A.K) (D : Set A.K), (∀ b ∈ D, ∃ s s' : A.K, s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse a * b) → IsUnit a → (¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ y : A.L, (x : A.K) * A.NL y - a ∉ D := by
  intro F E _ _ _ _ _ A ⟨h1, h2, _, h4, _⟩ x a D hD ha hn y hy
  obtain ⟨s, s', hss, hs⟩ := hD _ hy
  have hai : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel a ha
  have key : (x : A.K) * A.NL y = a * s ^ 2 := by
    rw [hs]
    linear_combination (-((x : A.K) * A.NL y - a)) * hai
  have hsu : IsUnit s := IsUnit.of_mul_eq_one s' hss
  have hs'u : IsUnit s' := IsUnit.of_mul_eq_one s (by rw [mul_comm]; exact hss)
  have hN : IsUnit (A.NL y) := by
    have : IsUnit ((x : A.K) * A.NL y) := by
      rw [key]; exact ha.mul (hsu.pow 2)
    exact isUnit_of_mul_isUnit_right this
  refine hn ⟨y * algebraMap A.K A.L s', (h4 y hN).mul (hs'u.map _), ?_⟩
  rw [h2, h1, ← mul_assoc, key]
  linear_combination (-a * (s * s' + 1)) * hss

end GlobalTheory.JR
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def cc (A : Et F E) (e : A.L) (p : A.K × A.K) : A.L :=
  algebraMap A.K A.L p.1 * e + algebraMap A.K A.L p.2 * (1 - e)

def ci (A : Et F E) (e : A.L) (y : A.L) : A.K × A.K :=
  (Algebra.trace A.K A.L (y * e), Algebra.trace A.K A.L (y * (1 - e)))

def kx (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (u b : A.K) : ℂ := A.psiK ψ (x * u * b)

def pt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  fourB ν (kx A ψ x) (fun b => Φ (p.1, b)) p.2

def rg (A : Et F E) (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  Φ (p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 0 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 0,
    p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 1 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 1)

def wHyp (A : Et F E) (e : A.L) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K)
    (g : SpecialLinearGroup (Fin 2) A.K) (φ : A.L → ℂ) (y : A.L) : ℂ :=
  pt A ν ψ x (pt A ν ψ x (pt A ν ψ x (rg A g (pt A ν ψ x (fun p => φ (cc A e p)))))) (ci A e y)

end GlobalTheory.JR.Hyp
end
end

section

open PowerSeries GlobalTheory.BK Filter Topology

theorem _root_.GlobalTheory.T.frobenius_mem_rigidFunctions_of_mem_invertEisenstein : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := by
  first | exact @GlobalTheory.BK.frob_mem_R_of_mem_invE_A | exact GlobalTheory.BK.frob_mem_R_of_mem_invE_A | (intros; apply GlobalTheory.BK.frob_mem_R_of_mem_invE_A <;> assumption)
end
