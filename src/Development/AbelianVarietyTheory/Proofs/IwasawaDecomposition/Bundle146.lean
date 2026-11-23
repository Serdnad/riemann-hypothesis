module

import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle088
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle087
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle406
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

namespace GlobalTheory.NatSmulMemLattice

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ (n : ℕ) (a : 𝓞 E), 0 < n ∧ (a : E) = (n : E) * c := by
  apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_nat_mul_integer <;> assumption

theorem exists_nat_smul_mem {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (L : Submodule (𝓞 E) W)
    (hL : Submodule.span E (L : Set W) = ⊤) (v : W) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 E) • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set W) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨n, e, hn, he⟩ := exists_nat_mul_integral c
    refine ⟨a * n, Nat.mul_pos ha hn, ?_⟩
    have key : ((a * n : ℕ) : 𝓞 E) • c • x = e • (a : 𝓞 E) • x := by
      rw [← algebraMap_smul E e, ← algebraMap_smul E (a : 𝓞 E),
        ← algebraMap_smul E ((a * n : ℕ) : 𝓞 E), smul_smul, smul_smul]
      congr 1
      have he' : algebraMap (𝓞 E) E e = (n : E) * c := he
      rw [he', map_natCast, map_natCast, Nat.cast_mul]
      ring
    rw [key]
    exact L.smul_mem _ hx

theorem exists_nat_smul_mem_lattice {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (v : Formalism.BasicNotions.HSpace.V V) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 (Formalism.BasicNotions.D7.host D).E) • v ∈ Formalism.BasicNotions.HSpace.L0 V :=
  by
    let E := (Formalism.BasicNotions.D7.host D).E
    let f := (V.hT v).restrictScalars (𝓞 E)
    obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 E)) (V.standardTuple_isLattice.fg.map f)
    have hd0 : (d : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
    obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_integral (d : E)⁻¹
    refine ⟨n, hn, ?_⟩
    rw [← V.baseLattice_isUnimodular]
    change (n : 𝓞 E) • v ∈ Formalism.E.hdual V.hT V.L0
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
    intro y hy
    obtain ⟨b, hb⟩ := hint (V.hT v y) ⟨y, hy, rfl⟩
    have hb' : (b : E) = (d : E) * V.hT v y := hb
    have hab : ((a * b : 𝓞 E) : E) = (n : E) * V.hT v y := by
      change (a : E) * (b : E) = _
      rw [ha, hb']
      field_simp
    have hs : IsIntegral ℤ (star ((n : E) * V.hT v y)) := by
      rw [← hab]
      exact (a * b).2.map (starRingEnd E).toIntAlgHom
    apply Submodule.mem_one.2
    refine ⟨⟨_, ?_⟩, rfl⟩
    change IsIntegral ℤ _
    have hh := V.herm.eq y v
    simp only [star_mul, star_natCast] at hs
    have hh' : star (V.hT v y) = V.hT y v := by
      rw [← hh]
      exact star_star _
    rw [hh'] at hs
    simpa [map_smul, Algebra.smul_def, mul_comm] using hs

end GlobalTheory.NatSmulMemLattice
end

section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.PsiFix

end GlobalTheory.Mem.An.PsiFix

namespace GlobalTheory.Mem.An

end GlobalTheory.Mem.An
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjWD

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.ConjWD

namespace GlobalTheory.ConjWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_weil_eq_on {g : G E Ω} (hg : g ∈ Dec (F := E) A) (L : IntermediateField E Ω)
    [FiniteDimensional E L] : ∃ τ : Weil h, ∀ x ∈ L, (τ : G E Ω) x = g x := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.decomposition_element_frobenius_power E Ω A w h L inferInstance g hg
  set φ : Weil h := frob h ^ k
  have hφ : ActsAs A (normV w) (φ : G E Ω) k 0 := actsAs_of_deg (by simp [φ])
  have hψ : ((φ : G E Ω) * g) ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem hφ.1 hg
  obtain ⟨ι, hι, hιL⟩ := GlobalTheory.T.inertia_lift_of_residual_trivial E Ω A w h L _ hψ fun x hx hxi => by
    have hx1 : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr (mem_of_isIntegral_int A hxi)
    have hgx : A.valuation (g x) ≤ 1 := val_apply_le_one hg hx1
    have h1 := hφ.2 _ hgx
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (hk x hx hxi)
  refine ⟨φ⁻¹ * ineIncl h ⟨ι, hι⟩, fun x hx => ?_⟩
  show (φ : G E Ω)⁻¹ (ι x) = g x
  rw [hιL x hx, AlgEquiv.mul_apply]
  show ((φ : G E Ω)⁻¹ * (φ : G E Ω)) (g x) = g x
  simp

end GlobalTheory.ConjWD
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.ULaws

variable {l : ℕ} [Fact l.Prime]

theorem alg_acris (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem ringHom_ext_Kur {R : Type} [CommRing R] (f g : ↥(MaximalUnramifiedExtension l) →+* R)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) =
      g (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])))
    (hr : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → f c = g c) (c : ↥(MaximalUnramifiedExtension l)) :
    f c = g c := by
  have hq : f.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = g.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext hz)
  obtain ⟨x, hx⟩ := c
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hxm⟩ := hx
    exact hr _ m hm hlm (Subtype.ext hxm)
  | algebraMap q => exact RingHom.congr_fun hq q
  | add x y hx hy a b =>
    exact (map_add f ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ (· + ·) a b).trans (map_add g ⟨x, hx⟩ ⟨y, hy⟩).symm)
  | inv x hx a => exact eq_on_inv₀ f g (a := ⟨x, hx⟩) a
  | mul x y hx hy a b =>
    exact (map_mul f ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ (· * ·) a b).trans (map_mul g ⟨x, hx⟩ ⟨y, hy⟩).symm)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem iota_injective (C : Core l) : Function.Injective C.ι := by
  obtain ⟨ι, h1, h2⟩ := GlobalTheory.T.exists_injective_bcris_to_bdR l C.j C.j_cris
  have e : C.ι = ι := GlobalTheory.RingIface.bcris_ext l fun x => (C.ι_j x).trans (h1 x).symm
  rw [e]
  exact h2

theorem iota_aB (C : Core l) (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have e : Per.aB l a = algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) a) := GlobalTheory.RingIface.aB_eq_alg l a
  rw [e, C.ι_j, alg_acris, C.j_cris.on0, Subalgebra.coe_algebraMap, aDp, RingHom.comp_apply]

theorem iota_sigma (C : Core l) (g : GQ l) (b : Per.Bcris l) :
    C.ι (Per.σB g b) = Per.σD g (C.ι b) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, -, hB, -⟩ := ActLaws.act_laws l
  have e : C.ι.comp (Per.σB g) = (Per.σD g).comp C.ι := by
    refine GlobalTheory.RingIface.bcris_ext l fun x => ?_
    simp only [RingHom.comp_apply]
    rw [hB, C.ι_j, C.ι_j, hD, (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris).2.1]
  exact RingHom.congr_fun e b

theorem iota_isCrisDR (C : Core l) : Per.IsCrisDR l C.ι := by
  obtain ⟨ι, hι⟩ := GlobalTheory.CrisIncl.exists_incl l
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hι
  have e : j = C.j := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris).1 j ⟨h2, h3⟩
  have e' : C.ι = ι := GlobalTheory.RingIface.bcris_ext l fun x => by rw [C.ι_j, h1, e]
  rwa [e']

theorem u_padicInt (C : Core l) (z : ℤ_[l]) :
    C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z := by
  apply iota_injective C
  have e : Per.zB l z = Per.aB l (Per.zA l z) := GlobalTheory.RingIface.zB_eq_aB_zA l z
  rw [e, iota_aB, C.ι_u, ← C.o_sec.z]
  rfl

theorem sigma_u (C : Core l) (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)) (h : g (c : Om l) = (c' : Om l)) :
    Per.σB g (C.u c) = C.u c' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, -⟩ := ActLaws.act_laws l
  apply iota_injective C
  rw [iota_sigma, C.ι_u, C.ι_u, hD, (GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec).2.2, h]

theorem phi_u (C : Core l) (c : ↥(MaximalUnramifiedExtension l)) : Per.φB l (C.u c) = C.u (C.σ c) := by
  obtain ⟨-, -, -, -, -, -, hφ, -, hz, -⟩ := ActLaws.act_laws l
  refine ringHom_ext_Kur ((Per.φB l).comp C.u) (C.u.comp (C.σ : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l)))
    (fun z => ?_) (fun c m hm hlm hc => ?_) c
  · have e : Per.zB l z = Per.aB l (Per.zA l z) := GlobalTheory.RingIface.zB_eq_aB_zA l z
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    rw [u_padicInt, e, hφ, hz]
  · obtain ⟨⟨xb, hxb⟩, h2⟩ := GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift l C.o C.o_sec (c : Om l) m hm hlm
      (congrArg Subtype.val hc)
    have hu : C.u c = Per.aB l (Per.tm xb) := by
      apply iota_injective C
      rw [iota_aB, C.ι_u, (h2 xb hxb).2.2]
    have h1 : Per.φA l (Per.tm xb) = Per.tm xb ^ l := by
      rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
        frobenius_def, map_pow]
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [C.σ_root c m hm hlm hc, map_pow, hu, hφ, h1, map_pow]

theorem u_laws (l : ℕ) [Fact l.Prime] (C : Core l) :
    (∀ c : ↥(MaximalUnramifiedExtension l), Per.φB l (C.u c) = C.u (C.σ c)) ∧
    (∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) → Per.σB g (C.u c) = C.u c') ∧
    (∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z) ∧
    Function.Injective C.ι ∧
    (∀ (g : GQ l) (b : Per.Bcris l), C.ι (Per.σB g b) = Per.σD g (C.ι b)) ∧
    Per.IsCrisDR l C.ι :=
  ⟨phi_u C, sigma_u C, u_padicInt C, iota_injective C, iota_sigma C, iota_isCrisDR C⟩

end GlobalTheory.MemLoc.ULaws
end

section

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem coreEx_alg_tower {l : ℕ} [Fact l.Prime] (a : _root_.Formalism.Per.Ainf l) :
    algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) a =
      algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] _root_.Formalism.Per.Acris _root_.Formalism.Per.Bcris

theorem coreEx_isUnit_l {l : ℕ} [Fact l.Prime] (e : _root_.Formalism.Per.Fl l) (h1 : e.untilt = 1) (h2 : e ≠ 1)
    (w : _root_.Formalism.Per.Acris0 l)
    (hw : (l : _root_.Formalism.Per.AinfP l) * (w : _root_.Formalism.Per.AinfP l) = algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (mu e) ^ (l - 1)) :
    IsUnit (l : _root_.Formalism.Per.Bcris l) := by
  have h0 : (l : _root_.Formalism.Per.Acris0 l) * w = algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hu : IsUnit (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)
      (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) (mu e))) := by
    exact GlobalTheory.CrisLoc.unit_of_root l e h1 h2
  have h3 := congrArg ((algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)).comp
    (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l))) h0
  rw [map_mul, map_natCast, map_pow] at h3
  have h4 : (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)).comp (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l))
      (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris0 l) (mu e)) =
      algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) (mu e)) := by
    rw [coreEx_alg_tower, RingHom.comp_apply]
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hu.pow (l - 1))

theorem nonempty_core : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Core l) := by
  intro l _
  obtain ⟨ζ, ε, z0, zs, z1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  obtain ⟨o, ho⟩ := GlobalTheory.T.exists_isBdRPlusSectionOfTheta l
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_canonical_acris_to_bdRPlus l
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.T.exists_injective_bcris_to_bdR l j hj
  have h1 : ε.untilt = 1 := by
    have h := hr 0
    rw [z0, map_one] at h
    exact Subtype.ext h
  have h2 : ε ≠ 1 := by
    intro h
    have h' := hr 1
    rw [h] at h'
    simp only [rootT, Function.iterate_one, map_one] at h'
    apply z1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h', map_one]
    rfl
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l ε h1
  have hA : ∀ a : _root_.Formalism.Per.Ainf l, ι (_root_.Formalism.Per.aB l a) = algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l a) := by
    intro a
    have h := hι (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) a)
    have h' : j (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) a) = aDp l a := by
      rw [coreEx_alg_tower, hj.on0]; rfl
    rw [h'] at h
    rw [GlobalTheory.RingIface.aB_apply]
    exact h
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_maxUnramified_embedding_into_Bcris l o ι ho hinj hA (coreEx_isUnit_l ε h1 h2 w hw)
  obtain ⟨t, -, ht, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l ε h1
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  exact ⟨⟨ζ, z0, zs, z1, ε, hr, o, ho, j, hj, ι, hι, u, hu, t, ht, σ, hσ, χ, hχ⟩⟩

end

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∧ C.j C.t ∈ Per.FilP l 1 ∧ C.j C.t ∉ Per.FilP l 2 ∧ IsUnit (l : Per.Bcris l) := by
  first | exact @GlobalTheory.MemLoc.core_t_unit_fil | exact GlobalTheory.MemLoc.core_t_unit_fil | (intros; apply GlobalTheory.MemLoc.core_t_unit_fil <;> assumption)
end

section

open NumberField

namespace GlobalTheory

theorem algWt_exists_invForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  intro L _ _ _ n a
  exact GlobalTheory.T.exists_invariant_hermitian_weight_form L n a

end GlobalTheory
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

def TwistConeVanishing {X : Scheme.{0}} (A N : LB X) (F : X.Modules) : Prop :=
  ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p →
    Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.conj_eq_add_kummer_torusTorsionPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ) (σ : F →ₐ[FractionRing R] F) (p p' : QkPt D F k), QkExt σ.toRingHom p p' →
    spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left →
    ∃ (τ : Multiplicative D.X →* Fˣ) (q : QkPt D F k), τ ^ k = 1 ∧ q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkAdd p q p' ∧
      ∀ (χ : D.X) (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D p.y χ x →
        ∃ s : F, s ≠ 0 ∧ O.valuation s ^ k = O.valuation (algebraMap (FractionRing R) F x) ∧
          σ s = (τ (Multiplicative.ofAdd χ) : F) * s := by
  first | exact @GlobalTheory.KummerConj.conj_eq_add_tor | exact GlobalTheory.KummerConj.conj_eq_add_tor | (intros; apply GlobalTheory.KummerConj.conj_eq_add_tor <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

theorem _root_.GlobalTheory.T.prod_idele_char_global_unit_eq_one : ∀ (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (B : Type) [CommGroup B] (ψ : Ideles F →* B), IsOpen (ψ.ker : Set (Ideles F)) → (∀ k : Fˣ, ψ (diagUnits F k) = 1) → ∀ (a : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ T, ψ (locUnit F v a) = 1) → ∏ v ∈ T, ψ (locUnit F v a) = 1 := by
  exact @GlobalTheory.ProdLocUnit.prod_locUnit_eq_one
end
