module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle189
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import GroundTheory.PAdicHodge.ACrisLog
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle190
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.cech_double_complex_map : ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R)
    (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type} (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)),
    ∃ φ : DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R),
      (∀ n (x : CH.H F n), φ.tot.mapH n ((CH.cechAugRow (idxπ U hU) F).edge.mapH n
          ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n x)) =
        (CH.cechAugRow (idxπ U' hU') F').edge.mapH n
          ((CH.Mor.restrict F' (CategoryOfElements.π ((Functor.const C').obj PUnit.{1}))).hom.mapH n (m.pull n x))) ∧
      ∀ p q (x : ((dbl U hU F).col p).H q) (i : Fin (p + 1) → ι'),
        (tupM U' hU' F' i).pull q ((φ.col p).mapH q x) =
          (morU m (U := capT U (τ ∘ i)) (U' := capT U' i) fun T hT k => hτ (i k) T (hT k)).pull q ((tupM U hU F (τ ∘ i)).pull q x) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.dbl_mor | exact GlobalTheory.CompanionTheory.CechSerre.dbl_mor | (intros; apply GlobalTheory.CompanionTheory.CechSerre.dbl_mor <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_class_zero_of_lead_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | exact GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | (intros; apply GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_map_lead_compat : ∀ {R : Type} [CommRing R] (K L : DCx.{1} R) (φ : DCx.Hom K L (RingHom.id R)) (a j : ℕ) (z : Zf K (a + j) j),
    ∃ z' : Zf L (a + j) j, clsZ L (a + j) j z' = φ.tot.mapH (a + j) (clsZ K (a + j) j z) ∧
      ∃ (y : (L.col j).H a) (hy : (colH L a).d j y = 0) (y₀ : (K.col j).H a) (hy₀ : (colH K a).d j y₀ = 0),
        leadE K j a z = (colH K a).cls y₀ hy₀ ∧ leadE L j a z' = (colH L a).cls y hy ∧ y = (φ.col j).mapH a y₀ := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_map | exact GlobalTheory.CompanionTheory.CechSerre.leadE_map | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_map <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.BaseAcris

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

def invS (h : IsBase l A) : A.A →+* Ob l := (RingEquiv.ofBijective A.s h).symm.toRingHom

theorem invS_comp (h : IsBase l A) : (invS A h).comp A.s = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).symm_apply_apply x

theorem comp_invS (h : IsBase l A) : A.s.comp (invS A h) = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).apply_symm_apply x

theorem map_xi_invS (h : IsBase l A) : WittVector.map (invS A h) A.xi = xi0 l := by
  rw [xi, sW, ← wmap_comp, invS_comp, wmap_id]

theorem awayW_left (h : IsBase l A) (y : WL l (Ob l)) : awayW (invS A h) (awayW A.s y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, invS_comp, awayW_id]; rfl

theorem awayW_right (h : IsBase l A) (y : WL l A.A) : awayW A.s (awayW (invS A h) y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, comp_invS, awayW_id]; rfl

theorem awayW_inv_mem (h : IsBase l A) {y : WL l A.A} (hy : y ∈ A.Acr0) :
    awayW (invS A h) y ∈ ACris.ACrisZero ℂ_[l] l := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have e := awayW_dpw (invS A h) k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    rw [map_xi_invS] at e
    exact Set.mem_of_eq_of_mem e (ACris.dpow_mem xi0_mem k)
  | algebraMap x => rw [awayW_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem acrisZero_bijective_of_isBase (h : IsBase l A) : Function.Bijective A.cris0 := by
  constructor
  · intro x y hxy
    have e : awayW A.s x.1 = awayW A.s y.1 := congrArg Subtype.val hxy
    have e' := congrArg (awayW (invS A h)) e
    rw [awayW_left, awayW_left] at e'
    exact Subtype.ext e'
  · intro y
    exact ⟨⟨awayW (invS A h) y.1, awayW_inv_mem A h y.2⟩, Subtype.ext (awayW_right A h y.1)⟩

theorem sW_bijective (h : IsBase l A) : Function.Bijective A.sW :=
  Function.bijective_iff_has_inverse.2 ⟨WittVector.map (invS A h),
    fun x => by
      change WittVector.map (invS A h) (WittVector.map A.s x) = x
      rw [← wmap_comp, invS_comp, wmap_id],
    fun x => by
      change WittVector.map A.s (WittVector.map (invS A h) x) = x
      rw [← wmap_comp, comp_invS, wmap_id]⟩

theorem oC_bijective (h : IsBase l A) : Function.Bijective A.oC := by
  have hs := sW_bijective A h
  have hth := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hth y
    rw [oC_theta0] at hy
    have hm : A.sW x ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := hs.2 c
    have e : x = c' * xi0 l := hs.1 (by rw [map_mul, ← hc]; rfl)
    have : x ∈ RingHom.ker (theta0 l) := by
      rw [e]; exact Ideal.mul_mem_left _ _ xi0_mem
    exact this
  · intro u
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨x, rfl⟩ := hs.2 w
    exact ⟨theta0 l x, A.oC_theta0 x⟩

theorem mem_map_of_evalₐ_eq_zero (B : Type) [CommRing B] (π : B) (n : ℕ)
    (a : AdicCompletion (Ideal.span {π}) B) (h : AdicCompletion.evalₐ (Ideal.span {π}) n a = 0) :
    a ∈ (Ideal.span {π} ^ n).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
  rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    ← AdicCompletion.factor_evalₐ_eq_eval _ a (by simp), h, map_zero]

theorem cris_surjective (h : IsBase l A) (n : ℕ) : Function.Surjective (A.cris n) := by
  intro u
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨y, rfl⟩ := (acrisZero_bijective_of_isBase A h).2 w
  exact ⟨AdicCompletion.of _ _ y, A.cris_of n y⟩

theorem cris_natCast_pow (n : ℕ) : A.cris n ((l : Acris l) ^ n) = 0 := by
  rw [map_pow, map_natCast, pow_l_acr]

theorem ker_cris (h : IsBase l A) (n : ℕ) :
    RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : Acris0 l)}) n a)
    have e : A.cris n a = A.mkAcr n (A.cris0 y) := by
      simp only [cris, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hy,
        Ideal.Quotient.lift_mk]
    rw [RingHom.mem_ker, e] at ha
    have hm : A.cris0 y ∈ Ideal.span {(l : A.Acr0) ^ n} := Ideal.Quotient.eq_zero_iff_mem.1 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := (acrisZero_bijective_of_isBase A h).2 c
    have e2 : y = c' * (l : Acris0 l) ^ n := (acrisZero_bijective_of_isBase A h).1 (by
      rw [map_mul, map_pow, map_natCast, hc])
    have hz : Ideal.Quotient.mk (Ideal.span {(l : Acris0 l)} ^ n) y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by
        rw [e2, Ideal.span_singleton_pow]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    rw [hz] at hy
    have hk : a ∈ (Ideal.span {(l : Acris0 l)} ^ n).map (algebraMap (Acris0 l) (Acris l)) := by
      exact mem_map_of_evalₐ_eq_zero _ _ n a hy.symm
    rw [ACris.map_span_p_pow, Ideal.span_singleton_pow] at hk
    exact hk
  · rw [Ideal.span_singleton_le_iff_mem]
    exact cris_natCast_pow A n

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A →
    (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧
      ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} :=
  fun A h => ⟨⟨acrisZero_bijective_of_isBase A h, oC_bijective A h⟩, fun n => ⟨cris_surjective A h n, ker_cris A h n⟩⟩

end GlobalTheory.CompanionTheory.BaseAcris
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CompanionTheory.OmBridge

open GlobalTheory.HodgeCoh GlobalTheory.CechDR

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem algebraMap_sec (W : X.Opens) (r : K) :
    letI := algΓ q
    algebraMap K (Sec q W) r = restrictTop W (algebraMap K Γ(X, ⊤) r) := by
  letI := algΓ q
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appLE ⊤ W le_top).hom r =
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop) ≫ X.presheaf.map (homOfLE le_top).op).hom r
  congr 2

theorem toOm_smul (a : ℕ) (W : X.Opens) (r : K) (x : OmU q W a) :
    letI := algΓ q
    CrystallineSemistableComparison.Om.Cech.toOm q a W (r • x) =
      (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom.app (op W)
        (CrystallineSemistableComparison.Om.Cech.toOm q a W x) := by
  letI := algΓ q
  rw [← algebraMap_smul (Sec q W) r x]
  have h := ((toOmega q a).app (op W)).hom.map_smul (algebraMap K (Sec q W) r) x
  refine h.trans ?_
  rw [algebraMap_sec q W r]
  rfl

variable {ι : Type} (U : ι → X.Opens) (a : ℕ)

theorem formCoch_smul (n : ℕ) (r : K) (c : (Glob.formCos q U a).X n) :
    letI := algΓ q
    formCoch q U a n (r • c) =
      GroundTheory.Arith.SchemeCoh.push U
        (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom n (formCoch q U a n c) := by
  letI := algΓ q
  funext i
  change res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (r • c i)) =
    (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom.app (op (inter U i))
      (res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (c i)))
  rw [toOm_smul]
  exact (ConcreteCategory.congr_hom
    ((smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom.naturality
      (homOfLE (inter_le_capO U i)).op) _).symm

theorem formToCO_smul (j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j) :
    formToCO q U a j (r • x) = r • formToCO q U a j x := by
  letI := algΓ q
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
  have hrc : (Glob.formCos q U a).cx.d j (r • c) = 0 := by rw [map_smul, hc', smul_zero]
  change formToCO q U a j ((Glob.formCos q U a).cx.cls (r • c) hrc) =
    r • formToCO q U a j ((Glob.formCos q U a).cx.cls c hc')
  rw [formToCO_cls, formToCO_cls]
  have hd : d (modulesAb (Omega q a)).obj U j (formCoch q U a j c) = 0 := by
    rw [← formCoch_d]
    exact (congrArg _ hc').trans (map_zero _)
  change _ = GroundTheory.Arith.SchemeCoh.cechHMap U (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom j
    (GroundTheory.Arith.SchemeCoh.cls (formCoch q U a j c) hd)
  rw [GroundTheory.Arith.SchemeCoh.cechHMap_cls]
  exact GroundTheory.Arith.SchemeCoh.cls_congr U (formCoch_smul q U a j r c) _ _

end GlobalTheory.CompanionTheory.OmBridge
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem res_bijective_of_le {T : TopCat.{0}} (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) {V W : Opens T}
    (h : V ≤ W) (h' : W ≤ V) : Function.Bijective (res P h) :=
  Function.bijective_iff_has_inverse.2
    ⟨res P h', fun x => by rw [res_res, res_refl], fun x => by rw [res_res, res_refl]⟩

theorem formCoch_bijective {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {ι : Type} (U : ι → X.Opens)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a n : ℕ) :
    Function.Bijective (formCoch q U a n) := by
  have hb : ∀ i : Fin (n + 1) → ι, Function.Bijective
      (fun x => res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i)
        (toOm q a (Pb.capO U i) x)) := fun i =>
    (res_bijective_of_le _ (inter_le_capO U i) (le_of_eq (inter_eq_iInf U i).symm)).comp
      (GlobalTheory.HodgeCoh.toOm_bijective q a (hUaff n i))
  refine ⟨fun c c' h => funext fun i => (hb i).1 (congrFun h i), fun σ => ?_⟩
  choose c hc using fun i => (hb i).2 (σ i)
  exact ⟨c, funext hc⟩

theorem formToCO_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j) := by
  intro K _ X q ι U hUaff a j
  have hB := formCoch_bijective q U hUaff a
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
    have hx' : formToCO q U a j ((Glob.formCos q U a).cx.cls c hc') = 0 := hx
    rw [formToCO_cls, GroundTheory.Arith.SchemeCoh.cls_eq_zero_iff] at hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change c ∈ (Glob.formCos q U a).cx.B j
    cases j with
    | zero =>
      rw [coboundaries_zero, AddSubgroup.mem_bot] at hx'
      exact (hB 0).1 (hx'.trans (map_zero _).symm)
    | succ n =>
      rw [coboundaries_succ] at hx'
      obtain ⟨τ, hτ⟩ := hx'
      obtain ⟨b, rfl⟩ := (hB n).2 τ
      exact ⟨b, (hB (n + 1)).1 ((formCoch_d q U a n b).trans hτ)⟩
  · intro y
    obtain ⟨σ, hσ, rfl⟩ := exists_cls (P := (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj) (U := U) (n := j) y
    obtain ⟨c, rfl⟩ := (hB j).2 σ
    have hc : (Glob.formCos q U a).cx.d j c = 0 :=
      (hB (j + 1)).1 (((formCoch_d q U a j c).trans hσ).trans (map_zero _).symm)
    exact ⟨(Glob.formCos q U a).cx.cls c hc, formToCO_cls q U a c hc⟩

end GlobalTheory.CompanionTheory.OmCech
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.integral_ring_adic_complete_prime_regular : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  first | exact @GlobalTheory.CompanionTheory.TiltCompl.complete_tf | exact GlobalTheory.CompanionTheory.TiltCompl.complete_tf | (intros; apply GlobalTheory.CompanionTheory.TiltCompl.complete_tf <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfLift

variable {l : ℕ} [Fact l.Prime] {R S : Type} [CommRing R] [CommRing S]

def powHom (hS : (l : S) = 0) (n : ℕ) : S →+* S where
  toFun x := x ^ l ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : l.Prime) x y n
    rw [hr, hS]; simp

theorem powHom_apply (hS : (l : S) = 0) (n : ℕ) (x : S) : powHom hS n x = x ^ l ^ n := rfl

def rootHom [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) : R ≃+* R :=
  RingEquiv.ofBijective (powHom hR n)
    (PerfectRing.bijective_frobenius : Function.Bijective fun x : R => x ^ l ^ n)

theorem rootHom_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (a : R) :
    ((rootHom hR n).symm a) ^ l ^ n = a :=
  (rootHom hR n).apply_symm_apply a

theorem rootHom_symm_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (b : R) :
    (rootHom hR n).symm (b ^ l ^ n) = b :=
  (rootHom hR n).symm_apply_apply b

def level [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) : R →+* S ⧸ Ideal.span {π} ^ l ^ n :=
  (Ideal.quotientMap (Ideal.span {π} ^ l ^ n) (powHom hS n)
    (fun _ hx => Ideal.mem_comap.2 (Ideal.pow_mem_pow hx _))).comp
      (g.comp ((rootHom hR n).symm : R →+* R))

theorem level_spec [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) (b : R) (x : S)
    (hx : Ideal.Quotient.mk _ x = g b) :
    level hR hS π g n (b ^ l ^ n) = Ideal.Quotient.mk _ (x ^ l ^ n) := by
  have h1 : ((rootHom hR n).symm : R →+* R) (b ^ l ^ n) = b := rootHom_symm_pow hR n b
  simp only [level, RingHom.comp_apply, h1, ← hx, Ideal.quotientMap_mk, powHom_apply]

theorem strictMono_pow : StrictMono fun n : ℕ => l ^ n :=
  strictMono_nat_of_lt_succ fun n => Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (Nat.lt_succ_self n)

theorem level_compat [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (m : ℕ) :
    (Ideal.Quotient.factorPow (Ideal.span {π}) ((strictMono_pow (l := l)).monotone m.le_succ)).comp
      (level hR hS π g (m + 1)) = level hR hS π g m := by
  ext a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ (m + 1) = a := ⟨_, rootHom_pow hR (m + 1) a⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g b)
  have hx' : Ideal.Quotient.mk (Ideal.span {π}) (x ^ l) = g (b ^ l) := by
    rw [map_pow, map_pow, hx]
  have e1 : b ^ l ^ (m + 1) = (b ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  have e2 : x ^ l ^ (m + 1) = (x ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  rw [RingHom.comp_apply, level_spec hR hS π g (m + 1) b x hx, e1, level_spec hR hS π g m _ _ hx', e2]
  rfl

theorem exists_lift [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsAdicComplete (Ideal.span {π}) S] (g : R →+* S ⧸ Ideal.span {π}) :
    ∃ f : R →+* S, (Ideal.Quotient.mk _).comp f = g := by
  refine ⟨IsAdicComplete.StrictMono.liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m), ?_⟩
  ext a
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g a)
  have h0 := IsAdicComplete.StrictMono.mk_liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m) (n := 0) a
  have h1 := level_spec hR hS π g 0 a x hx
  have ea : a ^ l ^ 0 = a := by simp
  have ex : x ^ l ^ 0 = x := by simp
  rw [ea, ex] at h1
  have h2 := Ideal.Quotient.eq.1 (h0.trans h1)
  have eI : Ideal.span {π} ^ l ^ 0 = Ideal.span {π} := by simp
  rw [eI] at h2
  rw [RingHom.comp_apply, ← hx]
  exact Ideal.Quotient.eq.2 h2

theorem lift_unique [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsHausdorff (Ideal.span {π}) S] (f f' : R →+* S)
    (h : (Ideal.Quotient.mk (Ideal.span {π})).comp f = (Ideal.Quotient.mk _).comp f') : f = f' := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' (Ideal.span {π}) (strictMono_pow (l := l))
  intro n a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ n = a := ⟨_, rootHom_pow hR n a⟩
  have hb : f b - f' b ∈ Ideal.span {π} :=
    Ideal.Quotient.eq.1 (RingHom.congr_fun h b)
  refine Ideal.Quotient.eq.2 ?_
  have e : f (b ^ l ^ n) - f' (b ^ l ^ n) = (f b - f' b) ^ l ^ n := by
    have := map_sub (powHom hS n) (f b) (f' b)
    simpa only [powHom_apply, map_pow] using this.symm
  rw [e]
  exact Ideal.pow_mem_pow hb _

theorem existsUnique_hom {l : ℕ} [Fact l.Prime] (A A' : PAlg l)
    (g : A.A →+* A'.A ⧸ Ideal.span {A'.pi})
    (hg : g.comp A.s = (Ideal.Quotient.mk _).comp A'.s) :
    ∃! φ : A ⟶ A', (Ideal.Quotient.mk _).comp (PAlg.Hom.f φ) = g := by
  have : IsAdicComplete (Ideal.span {A'.pi}) A'.A := A'.compl
  have hOb : ((l : ℕ) : Ob l) = 0 := CharP.cast_eq_zero _ l
  obtain ⟨f, hf⟩ := exists_lift A.natCast_l A'.natCast_l A'.pi g
  have hcomm : f.comp A.s = A'.s := by
    refine lift_unique hOb A'.natCast_l A'.pi _ _ ?_
    rw [← RingHom.comp_assoc, hf, hg]
  refine ⟨⟨f, hcomm⟩, hf, fun φ hφ => ?_⟩
  apply PAlg.Hom.ext
  exact lift_unique A.natCast_l A'.natCast_l A'.pi _ _ (hφ.trans hf.symm)

end GlobalTheory.CompanionTheory.PerfLift
end
end
