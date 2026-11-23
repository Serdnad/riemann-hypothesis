module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle852
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.WithTerminal.FinCategory
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wB_smul_transform : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), wB N x (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * wB N (vact N x γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) := by
  intro N _ x γ τ
  have h := congrFun (EisensteinSeries.G2_slash_action γ) τ
  rw [ModularForm.SL_slash_apply, Pi.sub_apply, EisensteinSeries.D2] at h
  have hj : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hd : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [ModularGroup.denom_apply]
  have hG : EisensteinSeries.G2 (γ • τ) = UpperHalfPlane.denom γ τ ^ 2 * EisensteinSeries.G2 τ
      - 2 * Real.pi * Complex.I * ((γ 1 0 : ℤ) : ℂ) * UpperHalfPlane.denom γ τ := by
    rw [zpow_neg, zpow_ofNat] at h
    field_simp at h
    linear_combination h
  have hwp := ((GlobalTheory.QFam.isFam_iff_values _ _ _ _).1 (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1) x γ τ
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [zpow_ofNat] at hwp
  rw [wB, wB, gN, gN, hwp, hG, hd]
  field_simp
  ring
end WpFam
end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCZero

noncomputable def clHom (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    Cocycle ((chains R).obj E) (res R F) 0 →+ H R E F 0 :=
  AddMonoidHom.mk' (fun c => CohomologyClass.mk c) (fun a b => CohomologyClass.mk_add a b)

theorem cochain_neg_one_eq_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (β : Cochain ((chains R).obj E) (res R F) (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · exact (GlobalTheory.EtC.HCElements.chains_X_isZero R E p hp).eq_of_src _ _
  · exact (GlobalTheory.EtC.HCElements.res_X_isZero R F q (by omega)).eq_of_tgt _ _

theorem clHom_bijective (R : Type) [CommRing R] (F : Shv R) (E : Spc) : Function.Bijective (clHom R F E) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : CohomologyClass.mk (a - b) = 0 := by
      rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 hab
    rw [CohomologyClass.mk_eq_zero_iff] at h0
    obtain ⟨m, hm, β, hβ⟩ := h0
    obtain rfl : m = -1 := by omega
    rw [cochain_neg_one_eq_zero R F E β, δ_zero] at hβ
    rw [← sub_eq_zero]
    exact Cocycle.ext (by simpa using hβ.symm)
  · obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c, rfl⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  intro R _ F
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  let cE : ∀ X : Scheme.{0}, Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 ≃+ H R (sch.obj X) F 0 :=
    fun X => AddEquiv.ofBijective (clHom R F (sch.obj X)) (clHom_bijective R F (sch.obj X))
  let φ : ∀ X : Scheme.{0}, Sec F X →+ Cochain ((chains R).obj (sch.obj X)) (res R F) 0 :=
    fun X => (AddMonoidHom.mk' (fun c : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 => c.1) (fun _ _ => rfl)).comp
      ((cE X).symm.toAddMonoidHom.comp (e X).toAddMonoidHom)
  have hφ : ∀ X s, φ X s = ((cE X).symm (e X s)).1 := fun _ _ => rfl
  refine ⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop), naturality := ?_ }, fun U => ⟨?_, fun z => ⟨?_, ?_⟩⟩⟩
  · intro U V f
    ext x
    change φ V.unop ((F.obj.map f).hom x) = ((HC R F).map (sch.map f.unop).op).f 0 (φ U.unop x)
    set c := (cE U.unop).symm (e U.unop x) with hc
    have key : (cE V.unop) (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) =
        e V.unop ((F.obj.map f).hom x) := by
      have h1 := he f.unop x
      have h2 : pull R (sch.map f.unop) F 0 (cE U.unop c) =
          CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) := rfl
      rw [hc, AddEquiv.apply_symm_apply] at h2
      rw [h2] at h1
      exact h1
    rw [hφ, hφ, ← key, AddEquiv.symm_apply_apply]
    rfl
  · intro a b hab
    change φ U.unop a = φ U.unop b at hab
    rw [hφ, hφ] at hab
    exact (e U.unop).injective ((cE U.unop).symm.injective (Subtype.ext hab))
  · intro hz
    refine ⟨(e U.unop).symm (cE U.unop (Cocycle.mk z (0 + 1) rfl hz)), ?_⟩
    change φ U.unop _ = z
    rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, rfl⟩
    change δ 0 (0 + 1) (φ U.unop x) = 0
    rw [hφ]
    exact ((cE U.unop).symm (e U.unop x)).2

end GlobalTheory.EtC.HCZero
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acycF_of_pi_sh : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type)
    [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) →
    AcycF R (sp B) F := by
  intro R _ F ι _ T _ B _ ⟨e⟩ hT n hn
  obtain ⟨hc⟩ := GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv ι T B e
  have hbij := GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective R F (Spec (CommRingCat.of B)) ι (fun i => Spec (CommRingCat.of (T i)))
    (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))) hc n
  have hsub : ∀ i, Subsingleton (H R (sch.obj (Spec (CommRingCat.of (T i)))) F n) :=
    fun i => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf R (T i) (hT i) F n hn
  refine ⟨fun x y => hbij.1 ?_⟩
  funext i
  exact Subsingleton.elim _ _

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.SmallEtaleCech

instance : PreservesLimitsOfSize.{0, 0} (disc : PSh ⥤ Spc) :=
  inferInstanceAs (PreservesLimitsOfSize.{0, 0} (Functor.const SimplexCategoryᵒᵖ : PSh ⥤ _))

instance : PreservesLimitsOfSize.{0, 0} sch := inferInstanceAs (PreservesLimitsOfSize.{0, 0} (yoneda ⋙ disc))

noncomputable def bcIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) :
    bc p ≅ Over.post sch ⋙ Over.pullback p ⋙ Over.forget E :=
  NatIso.ofComponents (fun U => pullbackSymmetry p (sch.map U.hom)) (fun {U V} g => by
    change pullback.map p (sch.map U.hom) p (sch.map V.hom) (𝟙 _) (sch.map g.left) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← sch.map_comp, Over.w g]) ≫ (pullbackSymmetry p (sch.map V.hom)).hom =
      (pullbackSymmetry p (sch.map U.hom)).hom ≫ pullback.lift (f := sch.map V.hom) (g := p)
        (pullback.fst (sch.map U.hom) p ≫ sch.map g.left) (pullback.snd (sch.map U.hom) p)
        (by rw [Category.assoc, ← sch.map_comp, Over.w g, pullback.condition])
    apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd])

theorem bc_preserves {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (J : Type) [SmallCategory J] [IsConnected J]
    [FinCategory J] : PreservesLimitsOfShape J (bc p) := by
  have : PreservesLimitsOfShape J (Over.post sch ⋙ Over.pullback p ⋙ Over.forget E : Over S ⥤ _) := inferInstance
  exact preservesLimitsOfShape_of_natIso (bcIso p).symm

theorem bc_isPullback {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {U V : Over S} (g : U ⟶ V) :
    IsPullback (pullback.snd p (sch.map U.hom)) ((bc p).map g) (sch.map g.left) (pullback.snd p (sch.map V.hom)) := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := pullback.fst p (sch.map V.hom)) (h₂₂ := sch.map V.hom) (v₁₃ := p) ?_ ?_
    (IsPullback.of_hasPullback p (sch.map V.hom)))
  · have h1 : (bc p).map g ≫ pullback.fst p (sch.map V.hom) = pullback.fst p (sch.map U.hom) := by
      simp [bc, pullback.map, pullback.lift_fst]
    have h2 : sch.map g.left ≫ sch.map V.hom = sch.map U.hom := by rw [← sch.map_comp, Over.w g]
    have h3 := IsPullback.of_hasPullback p (sch.map U.hom)
    rw [h2]
    exact h1 ▸ h3
  · simp [bc, pullback.map, pullback.lift_snd]

theorem hyp_coAug : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) [HasFiniteWidePushouts (S.Etale)ᵒᵖ] (U V : (S.Etale)ᵒᵖ) (g : U ⟶ V), Surjective g.unop.left → Hyp R ((Scheme.Etale.forget S ⋙ bc p).op) (coAug g) := by
  intro R _ S E p _ U V g hg k
  refine GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R _ _ (fun n => ?_) U V g ?_
  · have h1 := bc_preserves p (WidePullbackShape (Fin (n + 1)))
    have h2 : PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
        ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k) := inferInstance
    have h3 := preservesLimitsOfShape_of_equiv (widePushoutShapeOpEquiv (Fin (n + 1))).symm
        ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k)
    exact preservesColimitsOfShape_op _ ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k)
  · have he : Etale g.unop.left := by
      have h1 : Etale V.unop.hom := V.unop.prop
      have h2 : Etale U.unop.hom := U.unop.prop
      have h3 : Etale (g.unop.left ≫ U.unop.hom) := by
        rw [MorphismProperty.Over.w g.unop]; exact h1
      exact Etale.of_comp _ U.unop.hom
    exact isLocallySurjective_of_isPullback _ _ _ _
      ((bc_isPullback p ((Scheme.Etale.forget S).map g.unop)).map ((evaluation _ PSh).obj k))
      (yoneda_map_isLocallySurjective_of_etale_surjective _ _ g.unop.left he hg)

end GlobalTheory.EtC.SmallEtaleCech
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem preservesColimitsOfShape_spec_yoneda (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op) := by
  have h1 : PreservesColimitsOfShape J Scheme.Spec.{0}.rightOp := preservesColimitsOfShape_rightOp J _
  have h2 : PreservesColimitsOfShape J (yoneda (C := Scheme.{0})).op := preservesColimitsOfShape_op J _
  infer_instance

theorem hyp_spec_coAug_of_etFF : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  intro R _ A B g hg k
  obtain ⟨h1, h2⟩ := (etFF_basic.2.1 A B g).1 hg
  exact GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R CommRingCat.{0} (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op)
    (fun n => preservesColimitsOfShape_spec_yoneda _) A B g
    (locallySurjective_etale_section_baseChange.1 _ _ (Spec.map g) h1 h2)

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bij_of_subsingleton_pair {A B : Type*} [Subsingleton A] [Subsingleton B] (_b₀ : B) (a₀ : A) (φ : A → B) :
    Function.Bijective φ :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨a₀, Subsingleton.elim _ _⟩⟩

theorem eqv_of_gen_lc : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g →
    ∀ (U V : Scheme.{0}) (s : U ⟶ S) (f : V ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj V) F →
    Function.Bijective (fun φ : LocallyConstant U R ↦ φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  intro R _ F S g hg U V s f hU hV hb n
  obtain ⟨hneg, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  obtain ⟨eL, -, hE⟩ := GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant R F S g hg
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := hneg (sch.obj U) n hn
    have := hneg (sch.obj V) n hn
    exact bij_of_subsingleton_pair 0 0 _
  · have key : (fun x ↦ pull R (sch.map f) F 0 x) =
        (fun x ↦ e V (eL V (f ≫ s) (LocallyConstant.comap f.base.hom ((eL U s).symm ((e U).symm x))))) := by
      funext x
      conv_lhs => rw [← (e U).apply_symm_apply x, ← (eL U s).apply_symm_apply ((e U).symm x)]
      rw [he, hE]
    change Function.Bijective (fun x ↦ pull R (sch.map f) F 0 x)
    rw [key]
    exact (e V).bijective.comp ((eL V (f ≫ s)).bijective.comp
      (hb.comp ((eL U s).symm.bijective.comp (e U).symm.bijective)))
  · have := hU n hn
    have := hV n hn
    exact bij_of_subsingleton_pair 0 0 _

end GlobalTheory.EtC
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_isConn_of_isEt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : G.IsEt → G.dual.IsConn := by
  intro hG n χ hχ
  have : IsReduced (G.A n) := hG n
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p

  have roots : ∀ r : ℕ, ∀ a : G.A n, ∃ b : G.A n, a = b ^ p ^ r := by
    intro r
    induction r with
    | zero => exact fun a => ⟨a, by simp⟩
    | succ r ih =>
      intro a
      obtain ⟨c, rfl⟩ := ih a
      obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) c
      exact ⟨b, by rw [← pow_mul, pow_succ, mul_comm]⟩

  have h1 : χ 1 = 0 := by
    have hc := (RingHom.mem_ker).1 hχ
    exact hc
  refine ⟨p ^ n, ?_⟩
  apply CartierDual.ext_apply
  intro a
  obtain ⟨b, rfl⟩ := roots n a
  rw [GlobalTheory.T.cartierDual_convPow_primePow_apply_pow p k hp G n n χ b, PDivGroup.mulBy_pow_self, Algebra.algebraMap_eq_smul_one,
    map_smul, h1, smul_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  rfl

end GlobalTheory
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (h : (p : k) = 0)
      (G : PDivGroup p k), G.IsEt →
      Function.Bijective (G.rigToLie h) ∧ Function.Bijective G.dual.rigOfOmega := by
  intro p _ k _ _ _ h G hG
  obtain ⟨h1, h2⟩ := GlobalTheory.T.subsingleton_invariantDifferentials_of_etale p k G hG
  refine ⟨⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, G.rigToLie_surjective h⟩,
    ⟨G.dual.rigOfOmega_injective_of_eq_zero h, fun y => ?_⟩⟩
  · obtain ⟨w, rfl⟩ := (G.exact_rigOfOmega_rigToLie h x).1 hx
    rw [Subsingleton.elim w 0, map_zero]
  · refine (G.dual.exact_rigOfOmega_rigToLie h y).1 ?_
    exact LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, LinearMap.zero_apply]

end PDivGroup

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_zero_of_val_eq_zero_abelian : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  first | exact @GlobalTheory.ValInj.eq_zero_of_val_eq_zero | exact GlobalTheory.ValInj.eq_zero_of_val_eq_zero | (intros; apply GlobalTheory.ValInj.eq_zero_of_val_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pow_mul_eq_regularValue_basicOpen : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens), IsAffineOpen U → ∀ (r : Γ(A.left, U)) (k : (Fin g → ℂ) → ℂ), IsReg u.ex (A.left.basicOpen r) k → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, U), ∀ z ∈ pre u.ex (A.left.basicOpen r), val u.ex U b z = val u.ex U r z ^ N * k z := by
  first | exact @GlobalTheory.ClearDen.exists_pow_mul_eq_val | exact GlobalTheory.ClearDen.exists_pow_mul_eq_val | (intros; apply GlobalTheory.ClearDen.exists_pow_mul_eq_val <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), IsAffineOpen U → ∀ m : Ideal Γ(A.left, U), m.IsMaximal → ∃ z ∈ pre u.ex U, ∀ b, b ∈ m ↔ val u.ex U b z = 0 := by
  first | exact @GlobalTheory.MaxPoints.main | exact GlobalTheory.MaxPoints.main | (intros; apply GlobalTheory.MaxPoints.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechDeRhamPeriods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  first | exact @GlobalTheory.CechPer.periods_linear | exact GlobalTheory.CechPer.periods_linear | (intros; apply GlobalTheory.CechPer.periods_linear <;> assumption)
end
