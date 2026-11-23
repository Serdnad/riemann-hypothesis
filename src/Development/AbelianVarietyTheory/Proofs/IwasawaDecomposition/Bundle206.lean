module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle201
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle199
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaWeightArithmeticAtPlace_proof : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.ArithAt D i τ := by
  first | exact @GlobalTheory.PairWeightArith.arithAt | exact GlobalTheory.PairWeightArith.arithAt | (intros; apply GlobalTheory.PairWeightArith.arithAt <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.PdEx

variable {l : ℕ} [Fact l.Prime]

def actOf {G k B : Type} [Group G] [CommRing k] [CommRing B] [Algebra k B] (s : G → B →+* B)
    (hmul : ∀ g h x, s (g * h) x = s g (s h x)) (hone : ∀ x, s 1 x = x)
    (hk : ∀ g c, s g (algebraMap k B c) = algebraMap k B c) : G →* (B ≃ₐ[k] B) where
  toFun g :=
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun x => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun x => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := map_mul (s g)
      map_add' := map_add (s g)
      commutes' := hk g }
  map_one' := AlgEquiv.ext fun x => hone x
  map_mul' g h := AlgEquiv.ext fun x => hmul g h x

def inc (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)

theorem inc_coe (K : FinExt l) (x : ↥(K0 K)) : ((inc K x : ↥(MaximalUnramifiedExtension l)) : Om l) = (x : Om l) := rfl

def sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (h : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) :=
  (((MaximalUnramifiedExtension l).val.comp σ).comp (inc K)).codRestrict (K0 K).toSubalgebra fun x =>
    ⟨h (inc K x) x.2.1, (σ (inc K x)).2⟩

theorem inc_sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (h) (x : ↥(K0 K)) :
    inc K (sigK K σ h x) = σ (inc K x) := Subtype.ext rfl

theorem finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

theorem fix (K : FinExt l) (g : ↥(GK K)) (x : Om l) (hx : x ∈ K.1) : (g : GQ l) x = x :=
  (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).1 g.2 x hx

theorem exists_abstract (R : LocRings l) (K : FinExt l)
    (sB : GQ l → R.B →+* R.B) (sD : GQ l → R.BdR →+* R.BdR) (φ : R.B →+* R.B) (ι : R.B →+* R.BdR)
    (F : ℤ → AddSubgroup R.BdR) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (χ : GQ l →* ℤ_[l]ˣ) (t : R.B)
    (hσ : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1)
    (sB_mul : ∀ g h x, sB (g * h) x = sB g (sB h x)) (sB_one : ∀ x, sB 1 x = x)
    (sD_mul : ∀ g h x, sD (g * h) x = sD g (sD h x)) (sD_one : ∀ x, sD 1 x = x)
    (sB_u : ∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) →
      sB g (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B c')
    (sD_o : ∀ (g : GQ l) (x : Om l), sD g (algebraMap (Om l) R.BdR x) = algebraMap (Om l) R.BdR (g x))
    (invB : ∀ b, (∀ g ∈ GK K, sB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ algebraMap ↥(MaximalUnramifiedExtension l) R.B c = b)
    (invD : ∀ b, (∀ g ∈ GK K, sD g b = b) → ∃ y ∈ K.1, algebraMap (Om l) R.BdR y = b)
    (φ_inj : Function.Injective φ)
    (φ_u : ∀ c, φ (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B (σ c))
    (φ_comm : ∀ g b, φ (sB g b) = sB g (φ b))
    (ι_u : ∀ c : ↥(MaximalUnramifiedExtension l), ι (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap (Om l) R.BdR (c : Om l))
    (ι_inj : Function.Injective ι) (ι_comm : ∀ g b, ι (sB g b) = sD g (ι b))
    (F_o : ∀ x : Om l, algebraMap (Om l) R.BdR x ∈ F 0)
    (F_anti : ∀ a, F (a + 1) ≤ F a)
    (F_mul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (F_exh : ∀ x, ∃ a, x ∈ F a) (F_sep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (F_G : ∀ g a x, x ∈ F a → sD g x ∈ F a)
    (t_unit : IsUnit t)
    (t_act : ∀ g, sB g t = algebraMap ℚ_[l] R.B ((χ g : ℤ_[l]) : ℚ_[l]) * t)
    (t_φ : φ t = (l : R.B) * t) (t1 : ι t ∈ F 1) (t2 : ι t ∉ F 2)
    (fund : ∀ b, φ b = b → ι b ∈ F 0 → ∃ c : ℚ_[l], algebraMap ℚ_[l] R.B c = b) :
    ∃ PD : WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 R.B R.BdR,
      PD.p = l ∧ (∀ g b, PD.actB g b = sB g b) ∧ (∀ g b, PD.actdR g b = sD g b) ∧ (∀ b, PD.φ b = φ b) ∧
      (∀ b, PD.ι b = ι b) ∧ PD.t = t ∧ (∀ g, ((PD.χ g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ (g : GQ l) : ℤ_[l]) : ℚ_[l])) ∧
      (∀ a x, x ∈ PD.Fil a ↔ x ∈ F a) ∧
      ∀ (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
        ((PD.σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have aB : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (inc K c) := fun _ => rfl
  have aD : ∀ c : ↥K.1, algebraMap ↥K.1 R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aD0 : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aQ : ∀ c : ℚ_[l], algebraMap ℚ_[l] R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) :=
    fun c => IsScalarTower.algebraMap_apply _ _ _ c
  haveI := finiteDimensional_maxUnramifiedSubfield K
  refine ⟨{
    p := l
    hp := Fact.out
    finK₀ := finiteDimensional_maxUnramifiedSubfield K
    finK := K.2
    σ := sigK K σ hσ
    σ_bij := AlgHom.bijective _
    actB := actOf (fun g : ↥(GK K) => sB g) (fun g h x => sB_mul g h x) (fun x => sB_one x)
      (fun g c => by rw [aB]; exact sB_u g _ _ (fix K g _ c.2.1))
    invB := fun b hb => by
      obtain ⟨c, hc, e⟩ := invB b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc, c.2⟩, e⟩
    φ := AlgHom.mk φ fun c => by
      change φ _ = _
      rw [aQ, φ_u, AlgHom.commutes]
    φ_inj := φ_inj
    φ_K₀ := fun c => by
      change φ _ = _
      rw [aB, aB, φ_u, inc_sigK]
    φ_comm := fun g b => φ_comm g b
    actdR := actOf (fun g : ↥(GK K) => sD g) (fun g h x => sD_mul g h x) (fun x => sD_one x)
      (fun g c => by rw [aD, sD_o, fix K g _ c.2])
    invdR := fun b hb => by
      obtain ⟨c, hc, e⟩ := invD b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc⟩, e⟩
    ι := AlgHom.mk ι fun c => by
      change ι _ = _
      rw [aB, aD0, ι_u, inc_coe]
    ι_inj := ι_inj
    ι_comm := fun g b => ι_comm g b
    Fil := fun a =>
      { carrier := F a
        add_mem' := fun hx hy => (F a).add_mem hx hy
        zero_mem' := (F a).zero_mem
        smul_mem' := fun c x hx => by
          have := F_mul 0 a _ _ (F_o (c : Om l)) hx
          rw [zero_add, ← aD, ← Algebra.smul_def] at this
          exact this }
    Fil_anti := fun a x hx => F_anti a hx
    one_mem := by
      have := F_o 1
      rw [map_one] at this
      exact this
    Fil_mul := F_mul
    Fil_exh := F_exh
    Fil_sep := F_sep
    Fil_G := fun g a x hx => F_G g a x hx
    χ := ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp χ).comp (GK K).subtype
    t := t
    t_unit := t_unit
    t_act := fun g => by
      rw [Algebra.smul_def]
      exact t_act g
    t_φ := by
      rw [Algebra.smul_def, map_natCast]
      exact t_φ
    mem_filtration_one := t1
    not_mem_filtration_two := t2
    fund := fund }, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl,
    fun _ _ => Iff.rfl, fun x c h => ?_⟩
  have : inc K x = c := Subtype.ext h.symm
  rw [← this]
  rfl

theorem exists_realPD : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l), ∃ PD, IsRealPD C K PD := by
  intro l _ C K
  obtain ⟨a1, a2, a3, a4, a5, -, -, -, -, a10, -, a12, a13⟩ := ActLaws.act_laws l
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := GlobalTheory.T.bdR_filtration_laws l
  obtain ⟨u1, u2, -, u4, u5, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  have hσ := (frob_laws l C.σ C.σ_root).2.1 K
  have so := (GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec).2.2
  have sD_o : ∀ (g : GQ l) (x : Om l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) (C.o x)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (g x)) := fun g x => by rw [a10, so]
  have F_o : ∀ x : Om l, algebraMap (Per.BdRp l) (Per.BdR l) (C.o x) ∈ Per.FilD l 0 := fun x => by
    have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (f7 0 1).1 (by rw [map_one]; exact f2)
    have h2 : C.o x * 1 ∈ Per.FilP l 0 := Ideal.mul_mem_left _ _ h1
    rw [mul_one] at h2
    exact (f7 0 _).2 h2
  have u_z : ∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) := fun z => by
    apply u4
    have e1 : ((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]) : ↥(MaximalUnramifiedExtension l)) : Om l) = algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) :=
      (IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) (Om l) (z : ℚ_[l])).symm
    rw [C.ι_u, C.ι_j, ULaws.alg_acris, C.j_cris.on0, e1, C.o_sec.z, Subalgebra.coe_algebraMap, aDp,
      RingHom.comp_apply]
  have t_act : ∀ g : GQ l, Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((C.χ g : ℤ_[l]) : ℚ_[l])) * algebraMap (Per.Acris l) (Per.Bcris l) C.t :=
    fun g => by
      rw [a12, GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C g, map_mul, u_z]
  have t_φ : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) C.t := by
    rw [a13, GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C, map_mul, map_natCast]
  have s1 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∈ Per.FilD l 1 := by
    rw [C.ι_j]
    exact (f7 1 _).2 t2
  have s2 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∉ Per.FilD l 2 := by
    rw [C.ι_j]
    exact fun h => t3 ((f7 2 _).1 h)
  obtain ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_abstract (ringsOf C) K
    (fun g => Per.σB g) (fun g => Per.σD g) (Per.φB l) C.ι (fun a => (Per.FilD l a).toAddSubgroup) C.σ C.χ
    (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hσ a1 a2 a3 a4 u2 sD_o
    (InvCris.invariants_Bcris l C K) (GlobalTheory.T.bdR_galois_invariants_eq_finExt l C K) (GlobalTheory.T.frobenius_period_ring_injective l) u1 (fun g b => a5 g b) C.ι_u u4 u5
    F_o f1 f3 f4 f5 f6 t1 t_act t_φ s1 s2 (GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp l C)
  exact ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end GlobalTheory.MemLoc.PdEx
end
end

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem colNorm_exists_im_ne_zero {K : Type} [Field K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h a)

theorem colNorm_normAt_column (D : D7) (u : D.what₂.Word) (x : (D.div.Nu u).V) :
    Formalism.HermitianLatticesTheory.normAt (D.div.Nu u).b (D.div.Nu u).X (InfinitePlace.mk D.what₂.embLL) x = ‖D.jN u x‖ := by
  rw [D.nuIn_norm, normAt_sq_eq_majAt_re, (D.fm u).emb_norm, ← D.nuIn_jN, norm_eq_sqrt_re_inner (𝕜 := ℂ), D.eMu_isom]
  rfl

theorem colNorm_of_nuTie : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), R.NuTie → M.ColNorm := by
  intro D Bs A X fc s R cr M h u
  obtain ⟨L, hL⟩ := h u
  refine ⟨1, one_pos, fun φ => ?_⟩
  rw [one_mul]
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a = cj s (D.what₂.embLL a) := by
    rw [← R.v0]; exact R.twist
  have := fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL s htw (colNorm_exists_im_ne_zero _) (D.div.Nu u) _ L _ (R.eNu u) hL
    (D.what₂.Mu u) (D.jN u) (M.cφ u) (colNorm_normAt_column D u) (M.cφ_eq u) φ
  rw [← R.v0] at this
  exact this

end GlobalTheory.Mem.SJ
end

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem exists_im_ne_zero_of_totallyComplex {K : Type} [Field K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  exact Complex.conj_eq_iff_im.2 (h a)

theorem lin_single_cpt {K : Type} [Field K] (σ : K →+* ℂ) {d : ℕ} {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (e : (Fin d → K) ≃ₗ[K] V) (j : V →ₛₗ[σ] W) (x : Fin d → K) :
    lin (fun k => j (e (Pi.single k 1))) (cpt σ x) = j (e x) := by
  rw [lin_apply]
  conv_rhs => rw [pi_eq_sum_univ' x]

  simp [map_sum, map_smulₛₗ, cpt]

theorem rows_eq_rows_level : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.RRTie cr → (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ ∀ F, ‖M.eR F‖ = Real.sqrt (X.nP true) * ‖F‖ := by
  intro D Bs A X fc s R cr M eV hX hT
  obtain ⟨L, hT⟩ := hT
  have hn : 0 < X.nP true := hX.pos.2.2 true
  let g := lin (fun k => D.jEE (R.eRR (Pi.single k 1)))
  have hg : ∀ x, g (cpt D.what₂.embLL x) = D.jEE (R.eRR x) := lin_single_cpt _ R.eRR D.jEE
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt D.what₂.embLL (R.eRR.symm (D.div.RR.b i)), by rw [hg, R.eRR.apply_symm_apply]⟩
  have key : ∀ z, M.eR (g z) = X.iC cr true Bs.μ0 (cjv s z) := by
    intro z

    rw [← lin_basis (X.iC cr true Bs.μ0), lin_apply, lin_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, M.eR_eq]
    congr 2
    funext i
    by_cases h : i = k <;> simp [cpt, h]
  have hcc : ∀ z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ, cjv s (cjv s z) = z := by
    intro z
    funext i
    cases s <;> simp [cjv, cj]
  refine ⟨fun F => ?_, fun e he => ?_, fun F => ?_⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key, ← hX.h2.2.2]
    exact ⟨_, rfl⟩
  · rw [← hX.h2.2.2] at he
    obtain ⟨z, rfl⟩ := he
    exact ⟨g (cjv s z), by rw [key, hcc]⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key]
    have hd : DenseRange (cpt D.what₂.embLL : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) → _) :=
      DenseRange.piMap (fun _ => denseRange_of_im_ne_zero D.what₂.embLL (exists_im_ne_zero_of_totallyComplex _))
    have hcj : Continuous (cj s) := by
      cases s
      · exact continuous_id
      · exact Complex.continuous_conj
    have hcv : Continuous fun z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ => cjv s z :=
      continuous_pi fun i => hcj.comp (continuous_apply i)
    have h1 : Continuous fun z => ‖X.iC cr true Bs.μ0 (cjv s z)‖ :=
      ((LinearMap.continuous_of_finiteDimensional (X.iC cr true Bs.μ0)).comp hcv).norm
    have h2 : Continuous fun z => Real.sqrt (X.nP true) * ‖g z‖ :=
      continuous_const.mul (LinearMap.continuous_of_finiteDimensional g).norm
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    have hv : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
      funext i
      simp [cjv, cpt, R.twist]
    have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) := by
      simp [CxData.XE, rowXE, rowFrame, spliceFrame]
    have hli : LinearIndependent ℂ fun i => X.iC cr true Bs.μ0 (Pi.single i 1) :=
      li_of_lin_injective (by rw [lin_basis]; exact hX.h2.1)
    have hm := majAt_gram_smul (X.XE cr true) Bs.v0 _ hli _ (inv_pos.2 hn) hXE x x
    rw [lin_basis] at hm
    rw [hv, hg, ← D.jEE_norm, ← R.v0, normAt_sq_eq_majAt_re, hT.metric, hm, inner_self_eq_norm_sq_to_K,
      ← Real.sqrt_mul hn.le]
    erw [show ((((X.nP true)⁻¹ : ℝ) : ℂ) * ((‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ : ℝ) : ℂ) ^ 2).re =
      (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ ^ 2 by norm_cast]
    rw [mul_inv_cancel_left₀ hn.ne', Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.Mem.SJ
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l), (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  first | exact @GlobalTheory.MemLoc.InvCris.invariants_Bcris | exact GlobalTheory.MemLoc.InvCris.invariants_Bcris | (intros; apply GlobalTheory.MemLoc.InvCris.invariants_Bcris <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar


theorem _root_.GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F) (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str → (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) → IsIso h := by
  first | exact @GlobalTheory.BijPointsIso.isIso_of_bijective_points | exact GlobalTheory.BijPointsIso.isIso_of_bijective_points | (intros; apply GlobalTheory.BijPointsIso.isIso_of_bijective_points <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z = 1 → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB → interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] := by
  first | exact @GlobalTheory.VB.interNum_one_eq_genRank_mul | exact GlobalTheory.VB.interNum_one_eq_genRank_mul | (intros; apply GlobalTheory.VB.interNum_one_eq_genRank_mul <;> assumption)
end

section

noncomputable section

open MvPolynomial Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.PointChern

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coordOf {H : Host E} {Dw : Datum H} {n : ℕ} (e : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ :=
  fun τ i j => w (e.symm (τ, i, j))

def InDom {H : Host E} {Dw : Datum H} (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) : Prop :=
  ∀ τ, (1 - (z τ)ᴴ * z τ).PosDef

theorem mult_of_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult τ = Dw.p := by
  simp [Datum.mult, h]

theorem mult_of_not_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    Dw.mult τ = Dw.q := by
  simp [Datum.mult, h]


open Classical in
def modelGram (H : Host E) (Dw : Datum H) (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) :
    GlobalTheory.FlagBundle.Mat Dw.mult ℂ := fun τ =>
  if h : τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
      (1 - (z ⟨τ, h⟩).map (starRingEnd ℂ) * (z ⟨τ, h⟩)ᵀ)⁻¹
  else if h' : conjEmb τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
      (1 - (z ⟨conjEmb τ, h'⟩)ᴴ * z ⟨conjEmb τ, h'⟩)⁻¹
  else 1

def relPoly {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)

end GlobalTheory.PointChern
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.satakeEigenvalue_inv_normalised_eq_esymm : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  first | exact @GlobalTheory.SatEigArith.satEig_inv_normalised | exact GlobalTheory.SatEigArith.satEig_inv_normalised | (intros; apply GlobalTheory.SatEigArith.satEig_inv_normalised <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (μ' : Measure (HA (AF F) σ J')), 2 ≤ M → StepData σ J x a B J' → μ'.IsHaarMeasure → (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure ∧ StepRel s σ J x a B J' μ μ') ∧ ∀ μ₁ μ₂ : Measure (HA (AF F) σ J), StepRel s σ J x a B J' μ₁ μ' → StepRel s σ J x a B J' μ₂ μ' → μ₁ = μ₂ := by
  first | exact @GlobalTheory.GaugeEx.exists_unique_stepRel | exact GlobalTheory.GaugeEx.exists_unique_stepRel | (intros; apply GlobalTheory.GaugeEx.exists_unique_stepRel <;> assumption)
end
