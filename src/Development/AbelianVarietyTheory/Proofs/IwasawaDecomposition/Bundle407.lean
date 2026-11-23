module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle391
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle174
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle168
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem mem_integralNormOne_of_normOneDetClass_eq_one (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (h : u1Dt H SQ x = 1) :
    x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H) := by
  obtain ⟨a, ha⟩ := exists_lift H x
  have e : (QuotientGroup.mk a : DtQ H SQ) = 1 := (normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha).symm.trans h
  have ha' : a ∈ KDq H SQ := (QuotientGroup.eq_one_iff a).1 e
  refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).2 fun w => ?_
  exact (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).1 (Subgroup.mem_sup_left (KDq_le_KD H SQ ha')) w (conjPrime₂ w)
    ((isConjPl_iff H w _).2 rfl)

theorem unitIdeleImage_eq_map_integralNormOne : UOQ H SQ = ((Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)).subgroupOf (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))).map (u1Dt H SQ) := by
  ext t
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := exists_of_idele H a
    refine ⟨x, ?_, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩
    refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a hx).2 fun w => ?_
    exact (ha w).trans (ha (conjPrime₂ w)).symm
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_lift H x
    rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, mk_mem_UOQ, KDq_sup_unitIdl]
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).2 fun w w' hw => ?_
    rw [(isConjPl_iff H w w').1 hw]
    exact (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).1 hx w

end Gen

section Main

open Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem detPt_of_reads (hI : I.Ok) (u : B.Word) (i : ℕ) {Ch : Type} {chOf : (I.stp u I.mu0 i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u I.mu0 i chOf Lb U chi y st k) (c : (I.stp u I.mu0 i).Cl)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det (y c)) :
    detPt B.host I.SQ ((I.stp u I.mu0 i).rep c).1.1 = u1Dt B.host I.SQ x := by
  obtain ⟨p, hp, hN⟩ := hR.k_std (chOf c)
  refine GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level B.R B.host _ _ _ _ I.SQ _ (y c) (k (chOf c)) x (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni
    (hN ▸ hp.lat) (fun P hP => ?_) hx
  refine hR.k_off _ _ (GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes B X I hI u P hP) ?_ (Or.inl rfl)
  rintro ⟨Q, hQ, -⟩
  rw [GlobalTheory.T.q_mu0_eq_empty B X I] at hQ
  exact absurd hQ (Finset.notMem_empty Q)

theorem det_reGL {a b : ℕ} (h : a = b) {A : Type} [CommRing A] (g : GL (Fin a) A) :
    Matrix.GeneralLinearGroup.det (reGL h A g) = Matrix.GeneralLinearGroup.det g := by
  subst h
  refine Units.ext ?_
  simp [reGL, Matrix.GeneralLinearGroup.det]

variable (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : ColsTiedSym (I.rec7 l Z))


include I in
theorem det_normOne_classStepZero_trueColumns (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (c : ((I.rec7 l Z).mem u).C.cls 0)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det ((C.herm.base.lev0 u).y c).1) :
    (I.rec7 l Z).detCls u 0 c = u1Dt B.host I.SQ x := by
  obtain ⟨k, hk⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  refine detPt_of_reads I hI u 0 hk c x ?_
  have e := (C.car0 u).y_eq c
  rw [hx]
  exact (e ▸ det_reGL _ _).symm


include I in
theorem detI_std (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ B.R.m)
    (c : ((I.rec7 l Z).mem u).C.cls i) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det
      ((C.herm.base.cls u i h1 hm (C.herm.base.chOf u i c)).y ⟨c, rfl⟩).1) :
    (I.rec7 l Z).detCls u i c = u1Dt B.host I.SQ x := by
  by_cases h2 : i + 1 ≤ B.R.m
  · obtain ⟨k, hk⟩ := (hS u).mid i h1 h2
    refine detPt_of_reads I hI u i hk c x ?_
    have e := (C.carC u i h1 h2 (C.herm.base.chOf u i c)).y_eq ⟨c, rfl⟩
    rw [hx]
    exact (e ▸ det_reGL _ _).symm
  · obtain rfl : i = B.R.m := by omega
    obtain ⟨k, hk⟩ := (hS u).ends B.R.m le_rfl (Or.inr rfl)
    refine detPt_of_reads I hI u _ hk c x ?_
    have e := (C.carM u).y_eq c
    have key : ∀ (β : C.herm.base.Ch u B.R.m) (hb : C.herm.base.chOf u B.R.m c = β),
        Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm β).y ⟨c, hb⟩).1 =
          Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm (C.herm.base.chOf u B.R.m c)).y ⟨c, rfl⟩).1 := by
      rintro _ rfl
      rfl
    rw [hx, ← key _ (chOf_m C.herm.base u c)]
    exact (e ▸ det_reGL _ _).symm

def hermS (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricHermitianColumns (I.rec7 l Z) :=
  { C.herm.base with
    dt := u1Dt B.host I.SQ
    dt_surj := normOneFiniteAdeleDetClass_surjective B.host I.SQ
    dt_ker := mem_integralNormOne_of_normOneDetClass_eq_one B.host I.SQ
    dt_open := GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass B.R B.host _ I.SQ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1
    dt_UO := unitIdeleImage_eq_map_integralNormOne B.host I.SQ
    dt_rat := fun z x h => GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class B.R B.host I.SQ z x h
    det0 := fun u c x h => det_normOne_classStepZero_trueColumns I l Z C hI hS u c x h
    detI := fun u i h1 hm c x h => detI_std I l Z C hI hS u i h1 hm c x h }

theorem relDet_std (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricRelativeDeterminant (I.rec7 l Z) (hermS I l Z C hI hS) := by
  intro N L L' g _ hg x hx
  obtain ⟨idl, hp⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by ext t; exact ⟨fun h => ⟨t, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩) (fun _ => rfl)
    (fun N L L' t h => h)
  exact GlobalTheory.Mem.NormOneIdeal.relDet_eq_of_pinned (I.rec7 l Z) idl hp _ (hermS I l Z C hI hS).dt (hermS I l Z C hI hS).dt_ker
    (hermS I l Z C hI hS).dt_UO (hermS I l Z C hI hS).dt_rat L L' g x hg hx

theorem exists_colsFullS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (C : ColsTiedSym (I.rec7 l Z)) (g : Formalism.L2.Herm.SymmetricGroupCompatibility (I.rec7 l Z) C.herm.base), I.StdC l Z C → Formalism.L2.Herm.VolumeCompatible (I.rec7 l Z) → ∃ Fu : ColsFullS C, HEq Fu.1.g g ∧ I.StdDt l Z Fu.1.base.dt := by
  intro B X I hI _ l Z C g hS hV
  let Fu : Formalism.L2.Herm.FullTiedS (I.rec7 l Z) :=
    { base := hermS I l Z C hI hS
      atT := C.herm.atT
      vol := hV
      levelZeroCompatibility := C.herm.levelZeroCompatibility
      g := g
      ad := C.herm.ad
      cof := C.herm.cof
      piG := C.herm.piG
      stabMap := C.herm.stabMap
      fvI := C.herm.fvI
      relDet := relDet_std I l Z C hI hS
      std := C.herm.std
      vpos := B.V_pos
      baseL := C.herm.baseL }
  refine ⟨⟨Fu, rfl⟩, HEq.rfl, ?_⟩
  intro x a ha
  exact normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x a ha

end Main

end GlobalTheory.Mem.Col2.FullDt

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem not_isUnit_natCast {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) : ¬ IsUnit (p : 𝓞 K) := by
  intro h
  have : IsLocalHom (algebraMap ℤ (𝓞 K)) := Algebra.IsIntegral.isLocalHom _ _
  rw [← map_natCast (algebraMap ℤ (𝓞 K))] at h
  exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ h)

theorem rayField_splitsIn_of_isRayPrime (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M)
    (hf : FiniteDimensional ℚ M) :
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  intro hM p hp
  obtain ⟨hpp, π, hπK, hπi, hπc, σ, hσ⟩ := hp
  have hc0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
    exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
  let φ : D.host.K →+* Qb := jE.comp (D.host.K.val : D.host.K →+* D.host.E)
  have hφ : Function.Injective φ := jE.injective.comp Subtype.val_injective
  have hint : ∀ z : D.host.K, IsIntegral ℤ (φ z) → IsIntegral ℤ z := fun z hz =>
    (isIntegral_algHom_iff φ.toIntAlgHom hφ).1 hz
  have hmem : ∀ w : Qb, w ∈ KQbar D jE → ∃ z : D.host.K, φ z = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map _).1 hw
    exact ⟨⟨z, hz⟩, rfl⟩
  have hp0 : (p : Qb) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hπ0 : π ≠ 0 := left_ne_zero_of_mul (hσ ▸ hp0)
  have hσπ : σ π = p / π := by rw [← hσ, mul_div_cancel_left₀ _ hπ0]
  have hσK : σ π ∈ KQbar D jE := hσπ ▸ div_mem (natCast_mem _ p) hπK
  obtain ⟨x, hx⟩ := hmem π hπK
  obtain ⟨y, hy⟩ := hmem (σ π) hσK
  let σZ : Qb →ₐ[ℤ] Qb := σ.toRingHom.toIntAlgHom
  let a : 𝓞 D.host.K := ⟨x, hint x (hx ▸ hπi)⟩
  let b : 𝓞 D.host.K := ⟨y, hint y (hy ▸ hπi.map σZ)⟩

  have hab : a * b = p := by
    apply RingOfIntegers.coe_injective
    apply hφ
    rw [map_mul, map_natCast, map_mul, map_natCast]
    show φ x * φ y = _
    rw [hx, hy, hσ]

  have hdvd : ∀ z : 𝓞 D.host.K,
      IsIntegral ℤ ((φ z - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) →
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.K) ∣ z - 1 := by
    intro z hz
    set c : ℕ := D.host.QS * D.host.q * D.host.d
    have hcK : (c : D.host.K) ≠ 0 := by exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
    have hφw : φ (((z : D.host.K) - 1) / c) = (φ z - 1) / c := by
      rw [map_div₀, map_sub, map_one, map_natCast]
    let w : 𝓞 D.host.K := ⟨((z : D.host.K) - 1) / c, hint _ (hφw ▸ hz)⟩
    refine ⟨w, RingOfIntegers.coe_injective ?_⟩
    show (z : D.host.K) - 1 = (c : D.host.K) * (((z : D.host.K) - 1) / c)
    rw [mul_div_cancel₀ _ hcK]
  have hca := hdvd a (by show IsIntegral ℤ ((φ x - 1) / _); rw [hx]; exact hπc)
  have hcb := hdvd b (by
    show IsIntegral ℤ ((φ y - 1) / _)
    have e : σZ ((π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) =
        (σ π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) := by
      show σ _ = _
      rw [map_div₀, map_sub, map_one, map_natCast]
    rw [hy, ← e]
    exact hπc.map σZ)

  have hpu : ¬ IsUnit (p : 𝓞 D.host.K) := not_isUnit_natCast hpp
  have hunit : ∀ (z : 𝓞 D.host.K), (z : D.host.K) ≠ 0 → IsIntegral ℤ (φ z)⁻¹ → IsUnit z := by
    intro z hz0 hz
    have hi : IsIntegral ℤ ((z : D.host.K)⁻¹) := hint _ (by rw [map_inv₀]; exact hz)
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝓞 D.host.K) (RingOfIntegers.coe_injective ?_)
    show (z : D.host.K) * (z : D.host.K)⁻¹ = 1
    exact mul_inv_cancel₀ hz0
  have hinv : ∀ (z : 𝓞 D.host.K), IsUnit z → IsIntegral ℤ (φ z)⁻¹ := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    have h1 : (algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K) =
        ((algebraMap (𝓞 D.host.K) D.host.K) (u : 𝓞 D.host.K))⁻¹ :=
      map_units_inv (algebraMap (𝓞 D.host.K) D.host.K) u
    have h2 : φ ((algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K)) =
        (φ ((u : 𝓞 D.host.K) : D.host.K))⁻¹ := by
      rw [h1, map_inv₀]
    rw [← h2]
    exact (RingOfIntegers.isIntegral_coe _).map φ.toIntAlgHom
  have hx0 : (x : D.host.K) ≠ 0 := fun h0 => hπ0 (by rw [← hx, h0, map_zero])
  have hy0 : (y : D.host.K) ≠ 0 := fun h0 => hp0 (by rw [← hσ, ← hy, h0, map_zero, mul_zero])
  have hu : ¬ IsUnit a := fun ha => hpu (by
    have h1 := (hinv a ha).map σZ
    have h2 : σZ (φ x)⁻¹ = (φ y)⁻¹ := by
      show σ (φ x)⁻¹ = _
      rw [map_inv₀, hx, hy]
    rw [← hab]
    exact ha.mul (hunit b hy0 (h2 ▸ h1)))
  have hu' : ¬ IsUnit b := fun hb => hpu (by
    haveI : Algebra.IsAlgebraic ℚ Qb := by
      unfold Qb; convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
    let τ : Qb ≃ₐ[ℚ] Qb := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
    let τZ : Qb →ₐ[ℤ] Qb := τ.symm.toRingEquiv.toRingHom.toIntAlgHom
    have h1 := (hinv b hb).map τZ
    have h2 : τZ (φ y)⁻¹ = (φ x)⁻¹ := by
      show τ.symm (φ y)⁻¹ = _
      rw [map_inv₀, hy, hx]
      congr 1
      exact τ.symm_apply_apply π
    rw [← hab]
    exact (hunit a hx0 (h2 ▸ h1)).mul hb)

  have hpc : ¬ p ∣ D.host.QS * D.host.q * D.host.d := fun hd => hpu (by
    have h1 : (p : 𝓞 D.host.K) ∣ a - 1 := (Nat.cast_dvd_cast hd).trans hca
    have h2 : (p : 𝓞 D.host.K) ∣ b - 1 := (Nat.cast_dvd_cast hd).trans hcb
    have h3 : (1 : 𝓞 D.host.K) = p - (a * (b - 1) + (a - 1)) := by rw [← hab]; ring
    exact isUnit_of_dvd_one (h3 ▸ dvd_sub dvd_rfl (dvd_add (h2.mul_left _) h1)))
  have hd : ¬ (p : ℤ) ∣ discr M := fun hd => hpc (GlobalTheory.Mem.RaySplit.unr_of_ray hM p hpp hd)
  exact (GlobalTheory.HostSplit.ncard_placesOver M hpp).trans
    (GlobalTheory.Mem.RaySplit.ncard_primesOver_eq hM (GlobalTheory.Mem.RaySplit.isEmpty_real D.host)
      (GlobalTheory.Mem.RaySplit.finrank_K D.host) hpp hd hab hu hu' hca hcb)

end GlobalTheory.ParRay

end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev

theorem lev_iffQ : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E},
    J' = 1 → J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad),
    S.Lb = Formalism.L2.Col.stdLat E n → ∀ {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n'), 0 < t → n = r + s * t →
    ∀ {SG Q : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (ξ : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    RdLevOn hc Set.univ S.U S.chi (parFam h t s P χ) emb Q (fun _ => blockTri (blk2 r))
      (fun P => (ξ P.1).comp (blkDet (blk2 r) 1)) →
    ∀ (P' : LevelP SG r ℂ) (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    (∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H) →
    (∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K)) →
    (∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K)) →
    ∀ (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
    (∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) →
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  intro F E K _ _ _ _ _ _ _ hc n n' e _ J' J hJ' hJ T f bad S hL r t s h h' ht hn SG Q P χ emb ξ hR P' cg hH hchi hcg g y hgy
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔
      g ∈ lev hc 1 1 (parDat h t s P χ) ∧ ∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4⟩, a5⟩
      exact ⟨⟨⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, fun w _ => (hH _).1 a5 w⟩, a4⟩
    · rintro ⟨⟨⟨a1, a2, a3, -⟩, a5⟩, a4⟩
      exact ⟨⟨a1, a2, a3, a4⟩, (hH _).2 fun w => a5 w (Set.mem_univ w)⟩
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ∧ (∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r)) ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, hq⟩
      exact (hR g (Set.mem_univ g) h2 h1).1.2 ⟨fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w), fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2⟩
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      obtain ⟨a, b⟩ := (hR g (Set.mem_univ g) h2 h1).1.1 hy
      refine ⟨⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩, fun PP hP => ?_⟩
      · have := a w
        rwa [← hred h2] at this
      · have := b ⟨PP, hP⟩
        rwa [← hred h2] at this
  refine ⟨by rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1], fun hy => ?_⟩
  obtain ⟨h1, h2⟩ := hU hy
  obtain ⟨h3, hq⟩ := e1.2 hy
  have h4 : g ∈ lev hc 1 1 (parDat h t s P χ) := levU_parFam_eq_lev hc h ht hn P χ ▸ h3
  have h5 := e0.2 ⟨h4, hq⟩
  obtain ⟨r1, r2⟩ := hR g (Set.mem_univ g) h2 h1
  have hq' : ∀ PP : Q, redAt 1 PP.1 ⟨g, h2⟩ ∈ blockTri (blk2 r) := fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2
  have hw' : ∀ w : SG, redAt 1 w.1 ⟨g, h2⟩ ∈ (parFam h t s P χ w).H := (r1.1 hy).1
  have a1 : ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) =
      emb ((levFn 1 (parDat h t s P χ) g : Kˣ) : K) *
        ∏ PP ∈ Q, ((((ξ PP)⁻¹ (dBlk (blk2 r) 1 (redFn 1 PP g))) : ℂˣ) : ℂ) := by
    have eQ : (parDat h t s P χ).Q = ∅ := rfl
    unfold levFn
    rw [extendOne_of_mem _ h5.2, extendOne_of_mem _ h4.2, eQ, Finset.prod_empty, mul_one]
    simp only [Units.val_mul, Units.coe_prod, map_mul, map_prod]
    congr 1
    congr 1
    · rw [hchi _ fun w => h4.2 w (Set.mem_univ w)]
      have := rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, h4.2⟩
      refine Eq.trans ?_ (congrArg (fun x : Kˣ => emb (x : K)) this).symm
      simp only [Units.coe_prod, map_prod]
      rfl
    · show ∏ PP ∈ SG, _ = ∏ PP ∈ SG, _
      refine Finset.prod_congr rfl fun w hw => ?_
      show ∏ c ∈ Finset.range s, _ = ∏ c ∈ Finset.range s, _
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [rld_parDat_cg h P χ c ⟨w, hw⟩]
      exact hcg c ⟨w, hw⟩ _
  have a2 := levChr_parFam_eq_levChar hc h ht hn P χ g h3 h4
  rw [levChar_apply] at a2
  rw [a1, ← a2, r2 hy hw' hq', star_mul']
  congr 1
  · show emb ((piChar (fun w => (parFam h t s P χ w).H) (fun w => (parFam h t s P χ w).lam) (levRed hc n' ∅ SG _ ⟨g, h3⟩) : Kˣ) : K) = _
    rw [piChar_apply, Units.coe_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
    have b1 := ((emb.toMonoidHom.comp ((Units.coeHom K).comp (parFam h t s P χ w).lam)).isOfFinOrder
      (isOfFinOrder_of_finite ⟨_, hw' w⟩)).norm_eq_one
    refine Eq.trans ?_ ((congrArg star (Complex.inv_eq_conj b1)).trans (Complex.conj_conj _)).symm
    exact congrArg (fun x => emb (((parFam h t s P χ w).lam x : Kˣ) : K))
      (Subtype.ext ((levRed_apply hc n' ∅ SG _ ⟨g, h3⟩ w).trans (hred h2 w.1)))
  · rw [star_prod, ← Finset.prod_coe_sort Q]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have : Finite (𝓞 E ⧸ PP.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    have ed : dBlk (blk2 r) 1 (redFn 1 PP.1 g) = blkDet (blk2 r) 1 ⟨_, hq' PP⟩ := by
      unfold dBlk
      rw [extendOne_of_mem _ (hq PP.1 PP.2)]
      exact congrArg _ (Subtype.ext (hred h2 PP.1))
    rw [ed, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have b1 := (((Units.coeHom ℂ).comp (ξ PP.1)).isOfFinOrder
      (isOfFinOrder_of_finite (blkDet (blk2 r) 1 ⟨_, hq' PP⟩))).norm_eq_one
    exact Complex.inv_eq_conj b1

end GlobalTheory.SeeSaw.TwLev

end
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem measurePreserving_coords_sorted (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ) :
    MeasurePreserving (coords X κ) volume volume := by
  let e : Fin (nd X) ≃ Tau × Low r :=
    ((Equiv.prodCongr κ (Equiv.refl (Low r))).trans (Fintype.equivFin (Ent X))).symm
  have h1 := GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))
  have h2 := volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℂ) (MeasurePreserving.id _)
  have h3 := GlobalTheory.FlagBase.PoissonV.measurePreserving_curry Tau (Low r)
  exact h3.comp (h2.comp h1)

end GlobalTheory.FlagFibre
end
