module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle474
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairPowerSumValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle477
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open ChangeOfRings in
theorem unit_eq_zero_dvd {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) (N : ModuleCat.{1} (ULift.{1} (ZMod Q))) (y : N)
    (h : ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app N).hom y = 0) :
    ∃ z : N, y = q • z := by
  change (1 : ULift.{1} (ZMod q)) ⊗ₜ[ULift.{1} (ZMod Q), uliftHom (ZMod.castHom hq (ZMod q))] y = 0 at h
  let K : AddSubgroup N := (DistribSMul.toAddMonoidHom N q).range
  let gZ : ℤ →+ (N →+ N ⧸ K) := zmultiplesHom _ (QuotientAddGroup.mk' K)
  have hgZ : gZ q = 0 := by
    ext m
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.zero_apply, AddMonoidHom.coe_smul, Pi.smul_apply,
      QuotientAddGroup.mk'_apply]
    rw [natCast_zsmul, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩
  let g : ZMod q →+ (N →+ N ⧸ K) := ZMod.lift q ⟨gZ, hgZ⟩
  let f : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q))))
      →+ (N →+ N ⧸ K) := g.comp (AddEquiv.ulift : ULift.{1} (ZMod q) ≃+ ZMod q).toAddMonoidHom
  have hf : ∀ (r : ULift.{1} (ZMod Q)) s (n : N), f (r • s) n = f s (r • n) := by
    intro r s n
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (ULift.down r)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (ULift.down (s : ULift.{1} (ZMod q)))
    have hr : r • n = a • n := by
      rw [show r = ((a : ℤ) : ULift.{1} (ZMod Q)) from ULift.ext (by simp [ha]), Int.cast_smul_eq_zsmul]
    change g (ZMod.castHom hq (ZMod q) (ULift.down r) * ULift.down (s : ULift.{1} (ZMod q))) n =
      g (ULift.down (s : ULift.{1} (ZMod q))) (r • n)
    rw [hr, ← ha, ← hb, map_intCast, ← Int.cast_mul, ZMod.lift_coe, ZMod.lift_coe]
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, QuotientAddGroup.mk'_apply,
      map_zsmul, mul_comm a b, mul_zsmul]
    exact smul_comm b a _
  let one : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))) :=
    (1 : ULift.{1} (ZMod q))
  have e : f one y = 0 :=
    (TensorProduct.liftAddHom_tmul f hf one y).symm.trans ((congrArg (TensorProduct.liftAddHom f hf) h).trans (map_zero _))
  have e1 : f one = QuotientAddGroup.mk' K := by
    change g ((1 : ZMod q)) = _
    rw [← Int.cast_one, ZMod.lift_coe]
    simp [gZ]
  rw [e1, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at e
  obtain ⟨z, hz⟩ := e
  exact ⟨z, hz.symm⟩

theorem extSh_sec_eq_zero_loc : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U),
    extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  intro Q q _ hq M U x hx
  have hloc := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).2.1 U
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app (M.obj.obj (op U))).hom x) hx
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ hloc ?_
  intro V g hg
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.naturality (M.obj.map g.op)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) x
  exact unit_eq_zero_dvd hq (M.obj.obj (op V)) (Sec.res g x) (h2.trans hg)

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped ChangeOfRings

namespace GlobalTheory.EtC.ExtOnto

theorem unit_surjective {R S : Type 1} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (N : ModuleCat.{1} R) (z : (ModuleCat.extendScalars.{1,1,1} f).obj N) :
    ∃ m : N, ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} f).unit.app N).hom m = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hf s
    refine ⟨r • m, ?_⟩
    erw [ModuleCat.ExtendRestrictScalarsAdj.unit_app, map_smul, ModuleCat.restrictScalars.smul_def]
    exact (ModuleCat.ExtendScalars.smul_tmul (M := N) f (f r) 1 m).trans
      (congrArg (fun t : S => t ⊗ₜ[R,f] m) (mul_one _))
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), ha, hb]; rfl⟩

theorem uliftHom_surjective {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) :
    Function.Surjective (uliftHom φ) := by
  intro s
  obtain ⟨r, hr⟩ := hφ s.down
  exact ⟨⟨r⟩, ULift.ext hr⟩

theorem ext_onto : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0})
    (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U),
    Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  intro Q q _ hq M U y
  have hs := uliftHom_surjective (ZMod.castHom hq (ZMod q)) (ZMod.ringHom_surjective _)
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q)
    (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).1 U y
  refine GlobalTheory.EtC.loc_calculus.2.1 _ _ _ h1 ?_
  rintro V g ⟨z, hz⟩
  obtain ⟨m, hm⟩ := unit_surjective _ hs (M.obj.obj (op V)) z
  refine ⟨m, ?_⟩
  subst hm
  exact hz

end GlobalTheory.EtC.ExtOnto
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (exact GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurentCechNerve_level_spec_tensorPower : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (GlobalTheory.EtC.GmStep.laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (exact GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (intros; apply GlobalTheory.EtC.GmStep.LevelIso.level_iso  <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.diagonal_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  first | (exact @GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (exact GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (intros; apply GlobalTheory.EZ.ev_map_dD_eq_diagCx_d <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  first | (exact @GlobalTheory.EZ.awO_comm_d) | (exact GlobalTheory.EZ.awO_comm_d) | (intros; apply GlobalTheory.EZ.awO_comm_d <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ

theorem _root_.GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero : ∀ a b c d : ℕ, c + d + 2 = a + b → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  first | (exact @GlobalTheory.EZ.TotSq.dT_sq) | (exact GlobalTheory.EZ.TotSq.dT_sq) | (intros; apply GlobalTheory.EZ.TotSq.dT_sq  <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.cone_contracting_homotopy : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ), (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b), ε a b (bop α β) = 1) ∧ (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧ ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)), cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  first | (exact @GlobalTheory.EZ.Cone.coneContraction) | (exact GlobalTheory.EZ.Cone.coneContraction) | (intros; apply GlobalTheory.EZ.Cone.coneContraction  <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.eilenberg_zilber_homotopy_equivalence : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  first | (exact @GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (exact GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (intros; apply GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem _root_.GlobalTheory.T.hasStrictFDerivAt_diagonalTorus_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r), HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  first | exact @GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero | exact GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero | (intros; apply GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

theorem _root_.GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) → u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  first | exact @GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | exact GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | (intros; apply GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

theorem _root_.GlobalTheory.T.unipotent_translation_measure_preserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) → ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧ ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  first | exact @GlobalTheory.WhitBump.exists_shear_measurePreserving | exact GlobalTheory.WhitBump.exists_shear_measurePreserving | (intros; apply GlobalTheory.WhitBump.exists_shear_measurePreserving <;> assumption)
end
