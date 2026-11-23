module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle807
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedExists

def constCx {R : Type} [CommRing R] (F : Shv R) : Cx R where
  X _ := F
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

theorem ext_map (Q q : ℕ) (hq : q ∣ Q) (F : Shv (ZMod Q)) (G : Shv (ZMod q))
    (f : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hf : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec F U), Sec.res g (f U a) = f V (Sec.res g a)) :
    ∃ α : (extSh (ZMod.castHom hq (ZMod q))).obj F ⟶ G, ∀ (U : Scheme.{0}) (a : Sec F U),
      Sec.map α (extSh.sec (ZMod.castHom hq (ZMod q)) F U a) = f U a := by
  let ρ : SemiMap (constCx F) (constCx G) :=
    { app := fun U _ => f U
      nat := fun g _ a => hf _ _ g a
      comm := fun U s t a => by
        show Sec.map (0 : G ⟶ G) (f U a) = f U (Sec.map (0 : F ⟶ F) a)
        simp [Sec.map]
        exact ((f U).map_zero).symm }
  exact ⟨FactorExt.term _ (FactorExt.intCast_surj Q) ρ 0,
    fun U a => FactorExt.term_sec _ (FactorExt.intCast_surj Q) ρ 0 U a⟩

def semiOfExt {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) : SemiMap I K where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom.comp ((extπ (ZMod.castHom hq (ZMod q)) I).app U s)
  nat g s a := by
    have h := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op))
      ((extπ (ZMod.castHom hq (ZMod q)) I).app _ s a)).symm
    refine h.trans ?_
    exact congrArg (fun x => ((m.f s).hom.app (op _)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).nat g s a)
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a))) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · exact congrArg (fun x => ((m.f t).hom.app (op U)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).comm U s t a)

theorem semiOfExt_app {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (semiOfExt hq m).app U s a = Sec.map (m.f s) (extSh.sec (ZMod.castHom hq (ZMod q)) (I.X s) U a) := rfl

def powPrim {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.EtC.PrimBasic.prim_basic Q A).2.2.2.2.2 q hq ζ
    rw [← h]
    exact ξ.2⟩

theorem powPrim_map {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (ζ : Prim Q A) : (powPrim hq ζ).map φ = powPrim hq (ζ.map φ) :=
  Subtype.ext (map_pow φ _ _)

theorem nsmul_mod_of {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) (n : ℕ) :
    n • x = (n % q) • x := by
  have hq : q • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (by simp)
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm q, mul_smul, hq, smul_zero, add_zero]

theorem twRed_sec : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ), ∃ f : ∀ U : Scheme.{0}, Sec (tw Q i) U →+ Sec (tw q i) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec (tw Q i) U), Sec.res g (f U a) = f V (Sec.res g a)) ∧
    ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → f U (twGen i ζ) = twGen i ξ := by
  intro Q q _ _ hq i
  let M : Shv (ZMod Q) := (GlobalTheory.EtC.restr (ZMod.castHom hq (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (powPrim hq ζ) : Sec (tw q i) U)
  have ts := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim Q Γ(U, ⊤)), Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have := ts.2.2.2.1 V U g (powPrim hq ζ)
    rw [powPrim_map] at this
    exact this
  have hcast : ∀ u : (ZMod Q)ˣ, ((ZMod.unitsMap hq u : (ZMod q)ˣ) : ZMod q).val = (u : ZMod Q).val % q := by
    intro u
    show (ZMod.castHom hq (ZMod q) (u : ZMod Q)).val = _
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a h
    have hq1 : (ζ.1 ^ (Q / q)) ^ q = 1 := (GlobalTheory.EtC.PrimBasic.prim_basic q _).1 (powPrim hq ζ)
    have hpw : (powPrim hq ξ).1 = (powPrim hq ζ).1 ^ ((ZMod.unitsMap hq a : (ZMod q)ˣ) : ZMod q).val := by
      rw [hcast]
      show ξ.1 ^ (Q / q) = (ζ.1 ^ (Q / q)) ^ ((a : ZMod Q).val % q)
      rw [h, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.mod_add_div (a : ZMod Q).val q]
      rw [pow_add, pow_mul, hq1, one_pow, mul_one]
    have h5 := ts.2.2.2.2.1 U (powPrim hq ζ) (powPrim hq ξ) (ZMod.unitsMap hq a) hpw
    show (twGen i (powPrim hq ξ) : Sec (tw q i) U) =
      ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • (twGen i (powPrim hq ζ) : Sec (tw q i) U)
    have hm : (((ZMod.unitsMap hq a) ^ i : (ZMod q)ˣ) : ZMod q).val % q = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val % q := by
      rw [show (ZMod.unitsMap hq a) ^ i = ZMod.unitsMap hq (a ^ i) from (map_zpow _ _ _).symm, hcast, Nat.mod_mod]
    rw [h5, nsmul_mod_of (q := q) (twGen i (powPrim hq ζ)), hm, ← nsmul_mod_of (q := q)]
  obtain ⟨β, hβ, -⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).2.2.2.2.2 M e he1 he2
  refine ⟨fun U => ⟨⟨fun a => ((β.hom.app (op U)).hom a : Sec (tw q i) U), (β.hom.app (op U)).hom.map_zero⟩,
    fun a b => (β.hom.app (op U)).hom.map_add a b⟩, ?_, ?_⟩
  · intro V U g a
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (β.hom.naturality g.op)) a).symm
  · intro U ζ ξ h
    have h1 := hβ U ζ
    have h2 : powPrim hq ζ = ξ := Subtype.ext h.symm
    exact h1.trans (congrArg (twGen i) h2)

theorem redMap_exists (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ) :
    ∃ ρ : SemiMap (res _ (tw Q i)) (res _ (tw q i)), ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)),
      ξ.1 = ζ.1 ^ (Q / q) → ρ.app U 0 (resGen i ζ) = resGen i ξ := by
  obtain ⟨f, hf, hfg⟩ := twRed_sec Q q hq i
  obtain ⟨α, hα⟩ := ext_map Q q hq (tw Q i) (tw q i) f hf
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  have hQ := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))
    (extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) (res _ (tw q i))
    (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).1
    ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i))
  refine ⟨semiOfExt hq m, fun U ζ ξ h => ?_⟩
  have hv : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 := by
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        m.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ m.f 0) hs').trans (Category.assoc _ _ _)
  have hw : ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        α ≫ resι _ (tw q i) := by
    rw [HomologicalComplex.comp_f, ← hι]
    change ((HomologicalComplex.single (Shv (ZMod q)) (ComplexShape.up ℤ) 0).map α).f 0 ≫ _ = _
    rw [HomologicalComplex.single_map_f_self]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ?_
    exact Category.assoc _ _ _
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 = α ≫ resι _ (tw q i) := by
    have e : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
        ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 := by rw [hm]
    rw [hv, hw] at e
    exact (cancel_epi _).1 e
  rw [semiOfExt_app]
  change Sec.map (m.f 0) (extSh.sec _ _ U (Sec.map (resι _ (tw Q i)) (twGen i ζ))) = Sec.map (resι _ (tw q i)) (twGen i ξ)
  rw [← extSh.sec_map, ← hfg U ζ ξ h, ← hα]
  have e2 := congrArg (fun k => Sec.map k (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) U (twGen i ζ))) key
  exact e2

theorem red_exists : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  intro Q q _ _ hq i U ζ ξ h
  exact pick_spec (redMap_exists Q q hq i) U ζ ξ h

end GlobalTheory.EtC.RedExists
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianVariety_cech_vanishing_above_degree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  first | exact @GlobalTheory.AmpleGen.not_NV_of_ge | exact GlobalTheory.AmpleGen.not_NV_of_ge | (intros; apply GlobalTheory.AmpleGen.not_NV_of_ge <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem isGen_oneGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen (Y := Y) L).IsGen := by
  intro i j
  have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
    by
    unfold LB.LinComb; simp
  simp only [LB.oneGen, hg, map_one, one_mul]

theorem exists_iso_mix_one_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left)
    (hL : L.IsLB) : ∃ w : LB.Iso L (mix A L 1 0), w.IsGen := by
  have hs : LB.SameSum (K := PEmpty) PEmpty.elim PEmpty.elim
      (Sum.elim (fun _ : Fin 1 => 𝟙 A.left) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left])
      (Sum.elim (fun _ => (1 : ℤ)) fun k => -(![1, 0] : Fin 2 → ℤ) k) := by
    intro ψ
    by_cases h : 𝟙 A.left = ψ <;> by_cases h' : (GrpObj.inv : A ⟶ A).left = ψ <;>
      simp [Fintype.sum_sum_type, Fin.sum_univ_two, h, h']
  obtain ⟨t, ht, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_transport hL hs (LB.oneGen L) (isGen_oneGen L)
  have key := (GlobalTheory.GermSectionCompare.isGen_divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]
    ((GlobalTheory.GermSectionCompare.divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]).symm t)).1
    (by rw [Equiv.apply_symm_apply]; exact ht)
  exact ⟨_, key⟩

theorem nv_mix_one_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB →
    ∀ j : ℕ, NV A L j → NV A (mix A L 1 0) j := by
  intro K _ A _ L hL j ⟨κ, lo, ft, W, hW, hcov, hne⟩
  obtain ⟨w, hw⟩ := exists_iso_mix_one_zero A L hL
  have hM : (mix A L 1 0).IsLB := LB.isLB_linComb hL _ _
  exact ⟨κ, lo, ft, W, hW, hcov, fun h => hne (h.of_iso (GlobalTheory.AbLaw.cechLBCongr A.hom W hL hM w hw).symm)⟩

end GlobalTheory.AmpleGen
end
end

section

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem L_actR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (i j : Ix P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab i j) (embR P Q R h k G) = embR P Q R h k (opR P Q R k i j G) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fock_action_upper_left_commutes_embedding P Q R h k a a' G
  · exact GlobalTheory.T.fock_action_commutes_with_embedding P Q R h k a b' G
  · exact GlobalTheory.T.fock_action_lower_left_commutes_embedding P Q R h k a' b G
  · exact GlobalTheory.T.fock_action_lower_right_commutes_embedding P Q R h k b b' G

theorem mat_eq_sum {P Q : ℕ} (Z : Mat P Q) : Z = ∑ i, ∑ j, Z i j • Eab i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp [Eab, Matrix.smul_single]

theorem actR_full (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (Z : Mat P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 Z (embR P Q R h k G) = embR P Q R h k (actR P Q R k Z G) := by
  conv_lhs => rw [mat_eq_sum Z]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actR, actR_apply]

end GlobalTheory.CharPair

end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_transportHermitianFrame_chartMeasure : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 → ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ → ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) = ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := by
  first | exact @GlobalTheory.FlagTransport.lintegral_trF_cpt | exact GlobalTheory.FlagTransport.lintegral_trF_cpt | (intros; apply GlobalTheory.FlagTransport.lintegral_trF_cpt <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_transportHermitianFrame_realUnitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 → ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ → ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := by
  first | exact @GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf | exact GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf | (intros; apply GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.cech_finite_generation_of_affine_base_change : ∀ (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1) (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) → CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  first | exact @GlobalTheory.CechTr.cechFG_of_baseChange_affine | exact GlobalTheory.CechTr.cechFG_of_baseChange_affine | (intros; apply GlobalTheory.CechTr.cechFG_of_baseChange_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover : ∀ (Z : Scheme.{0}) (J : Type) (W : J → Z.Opens) (S : Set J), (∀ i, W i ≤ ⨆ a ∈ S, W a) → ∀ d : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W d → ∀ h₀ : ∀ i, Γ(Z, W i), (∀ a ∈ S, ∀ b ∈ S, d a b = resG Z inf_le_left (h₀ a) - resG Z inf_le_right (h₀ b)) → ∃ h : ∀ i, Γ(Z, W i), ∀ i i', d i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechFin.isCob_of_isCob_subcover | exact GlobalTheory.CechFin.isCob_of_isCob_subcover | (intros; apply GlobalTheory.CechFin.isCob_of_isCob_subcover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.cechCocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  first | exact @GlobalTheory.CechFin.cocycle_of_finite_affine_subcover | exact GlobalTheory.CechFin.cocycle_of_finite_affine_subcover | (intros; apply GlobalTheory.CechFin.cocycle_of_finite_affine_subcover <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_of_isCob : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.toPos_mem_Z1_of_isCoc : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_toCech_sub_of_mem_Z1 : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf (toCech s U hU hinf f) - f := by
  first | exact @GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary | exact GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary | (intros; apply GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary <;> assumption)
end
