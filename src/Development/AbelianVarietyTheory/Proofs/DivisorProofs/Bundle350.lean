module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle005
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle039
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle058
public import ReciprocityTheory.SemistableReduction.SJCoreA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle275
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem card_stabilizer_pair_eq (y : Y) (γ : ConjSelf Γ) :
    Nat.card (MulAction.stabilizer Γ (y, γ)) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer Γ y) γ) := by
  have hmap : (MulAction.stabilizer (MulAction.stabilizer Γ y) γ).map
      (MulAction.stabilizer Γ y).subtype = MulAction.stabilizer Γ (y, γ) := by
    ext η
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype, Prod.smul_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨η, h1⟩, h2, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

end GlobalTheory.OrbitUnfold

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem inner_sum_eq (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (y : Y)
    (hfin : (MulAction.stabilizer Γ y : Set Γ).Finite) (hsupp : (Function.support (F y)).Finite) :
    ∑ᶠ o' : MulAction.orbitRel.Quotient (MulAction.stabilizer Γ y) (ConjSelf Γ),
        pairTerm F (y, Quotient.out o') =
      ((Nat.card (MulAction.stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F y γ := by
  haveI : Finite (MulAction.stabilizer Γ y) := hfin.to_subtype
  have hinv : ∀ (k : MulAction.stabilizer Γ y) (z : ConjSelf Γ),
      F y (val (k • z)) = F y (val z) := by
    intro k z
    have hk : (k : Γ) • y = y := k.2
    have e1 : val (k • z) = (k : Γ) * val z * (k : Γ)⁻¹ := rfl
    have e2 := hF (k : Γ) y (val z)
    rw [hk] at e2
    rw [e1, e2]
  have hs : (Function.support (fun z : ConjSelf Γ => F y (val z))).Finite := hsupp
  have key := GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass (K := MulAction.stabilizer Γ y) (Z := ConjSelf Γ)
    (fun z => F y (val z)) hinv hs
  refine Eq.trans ?_ key
  refine finsum_congr fun o' => ?_
  unfold pairTerm
  rw [card_stabilizer_pair_eq]

theorem orbitSum_eq_pairSum (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (horb : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y,
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ =
      pairSum F := by
  have hg := GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp horb
  have hπ : ∀ (h : Γ) (x : Y × ConjSelf Γ), (h • x).1 = h • x.1 := fun _ _ => rfl
  have hinj : ∀ y : Y, Function.Injective (fun γ : ConjSelf Γ => (y, γ)) :=
    fun y a b hab => (Prod.mk.inj hab).2
  have hsurj : ∀ (y : Y) (x : Y × ConjSelf Γ), x.1 = y → ∃ e : ConjSelf Γ, (y, e) = x := by
    rintro y ⟨a, b⟩ rfl
    exact ⟨b, rfl⟩
  have hequi : ∀ (y : Y), ∀ h ∈ MulAction.stabilizer Γ y, ∀ e : ConjSelf Γ,
      ((y, h • e) : Y × ConjSelf Γ) = h • (y, e) := by
    intro y h hh e
    have hh' : h • y = y := hh
    rw [Prod.smul_mk, hh']
  have h := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := Y) (E := ConjSelf Γ) Prod.fst
    hπ (fun y => MulAction.stabilizer Γ y) (fun _ => le_rfl)
    (fun y γ => (y, γ)) hinj (fun _ _ => rfl) hsurj hequi
    Quotient.out (fun q => Quotient.out_eq q)
    (fun o => pairTerm F (Quotient.out o)) hg
  unfold pairSum
  rw [h]
  refine finsum_congr fun q => ?_
  rw [← inner_sum_eq F hF (Quotient.out q) (hstab _) (hsupp _)]
  refine finsum_congr fun o' => ?_
  exact (pairTerm_out F hF (Quotient.out q, Quotient.out o')).symm

end GlobalTheory.OrbitUnfold
end

section

open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

noncomputable section

namespace GlobalTheory.OrbitUnfold

def conjClassesEquivOrbits (Γ : Type) [Group Γ] :
    ConjClasses Γ ≃ MulAction.orbitRel.Quotient Γ (ConjSelf Γ) :=
  Quotient.congr (⟨of, val, fun _ => rfl, fun _ => rfl⟩ : Γ ≃ ConjSelf Γ) (by
    intro a b
    show IsConj a b ↔ of a ∈ MulAction.orbit Γ (of b)
    rw [isConj_comm, isConj_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg of hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg val hc⟩)

theorem conjClassesEquivOrbits_mk {Γ : Type} [Group Γ] (γ : Γ) :
    conjClassesEquivOrbits Γ (Quotient.mk (IsConj.setoid Γ) γ) =
      Quotient.mk (MulAction.orbitRel Γ (ConjSelf Γ)) (of γ) := rfl

theorem finsum_conjClasses_centralizer_orbits {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (_hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (hfin : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y,
      ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} :
        Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  set_option backward.isDefEq.respectTransparency false in
    set e := conjClassesEquivOrbits Γ
    have key := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := ConjSelf Γ) (E := Y)
      Prod.snd (fun _ _ => rfl) (fun b => Subgroup.centralizer {val b})
      (fun b => by rw [stabilizer_eq_centralizer])
      (fun b y => (y, b)) (fun b y y' h => congrArg Prod.fst h) (fun _ _ => rfl)
      (fun b x hx => ⟨x.1, Prod.ext rfl hx.symm⟩)
      (fun b h hh y => by
        have : h • b = b := by
          rw [← MulAction.mem_stabilizer_iff, stabilizer_eq_centralizer]; exact hh
        show (h • y, b) = (h • y, h • b)
        rw [this])
      (fun q => of (Quotient.out (e.symm q)))
      (fun q => by
        show Quotient.mk _ (of (Quotient.out (e.symm q))) = q
        have hout : ∀ c : ConjClasses Γ, (Quotient.mk (IsConj.setoid Γ) (Quotient.out c) : ConjClasses Γ) = c :=
          fun c => Quotient.out_eq c
        rw [← conjClassesEquivOrbits_mk, hout, Equiv.apply_symm_apply])
      (fun o => pairTerm F (Quotient.out o))
      (GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp hfin)
    unfold pairSum
    rw [key, ← finsum_comp_equiv e]
    refine finsum_congr (fun c => ?_)
    change Quotient (IsConj.setoid Γ) at c
    change ConjClasses Γ at c
    change (Quotient (IsConj.setoid Γ)) at c
    rw [e.symm_apply_apply]
    dsimp only [ConjSelf.val, ConjSelf.of]
    refine finsum_congr (fun o => ?_)
    rw [pairTerm_out F hF]
    unfold pairTerm
    rw [stabilizer_pair]
    rfl

end GlobalTheory.OrbitUnfold
end
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  first | exact @GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | exact GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | (intros; apply GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.hilbert_point_glue_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  first | (exact @GlobalTheory.HilbGlue.HPt.exists_glue) | (exact GlobalTheory.HilbGlue.HPt.exists_glue) | (intros; apply GlobalTheory.HilbGlue.HPt.exists_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_flat_ideal_extension (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X']
    (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X)
    (h : IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    (I : X'.IdealSheafData) : ∃ J : X.IdealSheafData, Flat (J.subschemeι ≫ p) ∧ J.comap b = I := by
  obtain ⟨J₀, hf, hJ⟩ := GlobalTheory.T.exists_flat_ideal_valuationRing_pullback V K X X' p p' b h (I.ideal ⟨⊤, isAffineOpen_top X'⟩)
  have e : (Scheme.IdealSheafData.ofIdealTop J₀).ideal ⟨⊤, isAffineOpen_top X⟩ = J₀ :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J₀
  refine ⟨Scheme.IdealSheafData.ofIdealTop J₀, GlobalTheory.T.flat_subscheme_of_quotient_flat_affine V X p _ (by rw [e]; exact hf), ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine, e, hJ]

theorem finrank_const_of_isLocalRing (V : Type) [CommRing V] [IsLocalRing V] (Z : Scheme.{0})
    (f : Z ⟶ Spec (CommRingCat.of V)) (h1 : IsFinite f) (h2 : Flat f) (x y : Spec (CommRingCat.of V)) :
    f.finrank x = f.finrank y := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ f)
  have ef : f = Z.isoSpec.hom ≫ Spec.map φ := by rw [hφ]; simp
  have hf1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hf2 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have hr1 := hf1
  have hr2 := hf2
  rw [IsFinite.SpecMap_iff] at hr1
  rw [Flat.SpecMap_iff] at hr2
  rw [ef, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hr1 hr2]
  algebraize [φ.hom]
  have : Module.Free V Γ(Z, ⊤) := Module.free_of_flat_of_isLocalRing
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]
  simp only [Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_good_extension (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (r : ℕ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g)).IdealSheafData)
    (hI : Good A B r _ I) :
    ∃ J, Good A B r g J ∧ J.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  obtain ⟨J, hJf, hJ⟩ := exists_flat_ideal_extension V K _ _ (pullback.snd (str A B) g) (pullback.snd _ _) _
    (isPullback_bc A B g _) I
  have : IsFinite (str A B) := by
    rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.mpr inferInstance
  have h1 : IsFinite (J.subschemeι ≫ pullback.snd (str A B) g) := inferInstance
  refine ⟨J, ⟨h1, hJf, fun y => ?_⟩, hJ⟩
  obtain ⟨_, _, h3⟩ := hI
  subst hJ
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  rw [finrank_const_of_isLocalRing V _ _ h1 hJf y (a pt)]
  have H : IsPullback (pullback.snd (bc A B g a) J.subschemeι)
      (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))
      (J.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) J.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (J.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (J.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) J.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H hJf
  have := h3 pt
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H pt]
    at this
  exact this

theorem valuativeExistence (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H) :
    ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  intro S
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), (R.homEquiv f).1 = f ≫ (R.homEquiv (𝟙 H)).1 := by
    intro T f
    have h := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at h
    rw [h]; rfl
  set ι := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) with hι
  have gen : ∀ x : (functor A B r).obj (op (Spec (CommRingCat.of S.K))), x.1 = ι ≫ S.i₂ →
      ∃ y : (functor A B r).obj (op (Spec (CommRingCat.of S.R))),
        y.1 = S.i₂ ∧ (functor A B r).map ι.op y = x := by
    rintro ⟨g', I, hI⟩ hx
    dsimp only at hx
    subst hx
    obtain ⟨J, hJ, hJI⟩ := exists_good_extension A B r S.R S.K S.i₂ I hI
    subst hJI
    exact ⟨⟨S.i₂, J, hJ⟩, rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := gen (R.homEquiv S.i₁) ((key S.i₁).trans S.commSq.w)
  refine ⟨⟨{ l := R.homEquiv.symm y, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply R.homEquiv.injective
    rw [R.homEquiv_comp, Equiv.apply_symm_apply, hy2]
  · rw [← key, Equiv.apply_symm_apply, hy1]

end GlobalTheory.HilbAff
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.PowerMultiple

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

theorem res_pow_mul_mem_gen
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {D W V : X.Opens} (hD : IsAffineOpen D) (hDW : D ≤ W) (hDV : D ≤ V)
    (T : Set (F.obj (op V))) (f : Γ(X, W)) (a : F.obj (op W))
    (ha : ∀ (W' : X.Opens), IsAffineOpen W' → ∀ (h1 : W' ≤ X.basicOpen f) (h2 : W' ≤ V),
      (F.map (homOfLE h1).op).hom ((F.map (homOfLE (X.basicOpen_le f)).op).hom a) ∈
        gen F α h2 T) :
    ∃ m : ℕ, (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f ^ m * a) ∈ gen F α hDV T := by
  set fD : Γ(X, D) := (X.presheaf.map (homOfLE hDW).op).hom f with hfD
  have hbo : X.basicOpen fD = D ⊓ X.basicOpen f := Scheme.basicOpen_res X f (homOfLE hDW).op
  have hD'D : X.basicOpen fD ≤ D := X.basicOpen_le fD
  have hD'f : X.basicOpen fD ≤ X.basicOpen f := hbo.le.trans inf_le_right
  have hD'V : X.basicOpen fD ≤ V := hD'D.trans hDV
  have hD' : IsAffineOpen (X.basicOpen fD) := hD.basicOpen fD
  letI iRA : Algebra Γ(X, D) (F.obj (op D)) := (α.app (op D)).hom.toAlgebra
  letI iRR' : Algebra Γ(X, D) Γ(X, X.basicOpen fD) :=
    (X.presheaf.map (homOfLE hD'D).op).hom.toAlgebra
  letI iR'A' : Algebra Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) :=
    (α.app (op (X.basicOpen fD))).hom.toAlgebra
  letI iAA' : Algebra (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    (F.map (homOfLE hD'D).op).hom.toAlgebra
  letI iRA' : Algebra Γ(X, D) (F.obj (op (X.basicOpen fD))) :=
    ((F.map (homOfLE hD'D).op).hom.comp (α.app (op D)).hom).toAlgebra
  haveI : IsScalarTower Γ(X, D) (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(X, D) Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have := congr($(α.naturality (homOfLE hD'D).op).hom r)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  haveI : IsLocalization.Away fD Γ(X, X.basicOpen fD) := hD.isLocalization_basicOpen fD
  haveI : IsLocalization.Away (algebraMap Γ(X, D) (F.obj (op D)) fD)
      (F.obj (op (X.basicOpen fD))) := isLocalizationAway F α hα hD fD
  have hres : ∀ {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom y) =
        (F.map (homOfLE (h₂.trans h₁)).op).hom y := by
    intro U₁ U₂ U₃ h₁ h₂ y
    rw [← CommRingCat.comp_apply, ← F.map_comp]
    rfl
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway (R := Γ(X, D)) (A := F.obj (op D))
    (R' := Γ(X, X.basicOpen fD)) (A' := F.obj (op (X.basicOpen fD))) fD
    ((F.map (homOfLE hDV).op).hom '' T) ((F.map (homOfLE hDW).op).hom a) (by
      have h0 := ha _ hD' hD'f hD'V
      rw [hres, gen_eq_adjoin] at h0
      change (F.map (homOfLE hD'D).op).hom ((F.map (homOfLE hDW).op).hom a) ∈ _
      rw [hres, Set.image_image]
      have hfun : (fun x => (algebraMap (F.obj (op D)) (F.obj (op (X.basicOpen fD))))
          ((F.map (homOfLE hDV).op).hom x)) = ⇑(F.map (homOfLE hD'V).op).hom :=
        funext fun x => hres _ _ x
      rw [hfun]
      exact h0)
  refine ⟨m, ?_⟩
  have hnat : (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f) = (α.app (op D)).hom fD := by
    have := congr($(α.naturality (homOfLE hDW).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  rw [map_mul, map_pow, hnat, gen_eq_adjoin]
  exact hm

end GlobalTheory.QcSub.PowerMultiple

theorem GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  intro X hX F α hα ι _ V hV T W hW f a ha
  classical
  haveI := Fintype.ofFinite ι
  rw [mem_sub] at ha
  choose s hs1 hs2 using fun j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX W (V j) hW (hV j)
  have hle : ∀ j, ∀ h ∈ s j, X.basicOpen h ≤ V j := by
    intro j h hh
    obtain ⟨r, hr⟩ := hs1 j h hh
    rw [hr]
    exact X.basicOpen_le r
  choose m hm using fun j (h : s j) =>
    GlobalTheory.QcSub.PowerMultiple.res_pow_mul_mem_gen F α hα (hW.basicOpen h.1) (X.basicOpen_le h.1)
      (hle j h.1 h.2) (T j) f a (fun W' hW' h1 h2 => ha j W' hW' h1 h2)
  refine ⟨∑ j, ∑ h : s j, m j h, ?_⟩
  rw [mem_sub]
  intro j W' hW' hWW' hWV
  refine GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) W (T j) _ ?_ W' hW' hWW' hWV
  intro x hx
  have hx' := hs2 j hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx'
  obtain ⟨h, hh, hxh⟩ := hx'
  refine ⟨X.basicOpen h, hW.basicOpen h, hxh, X.basicOpen_le h, hle j h hh, ?_⟩
  have hmle : m j ⟨h, hh⟩ ≤ ∑ j, ∑ h : s j, m j h :=
    le_trans (Finset.single_le_sum (f := fun h' => m j h') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨h, hh⟩ : s j)))
      (Finset.single_le_sum (f := fun j' => ∑ h' : s j', m j' h') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  rw [show ∑ j, ∑ h : s j, m j h = (∑ j, ∑ h : s j, m j h - m j ⟨h, hh⟩) + m j ⟨h, hh⟩ by omega,
    pow_add, mul_assoc, map_mul]
  refine mul_mem ?_ (hm j ⟨h, hh⟩)
  rw [map_pow]
  refine pow_mem ?_ _
  have := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom f)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem _root_.GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral) → ∀ {ι : Type} (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → (∀ x : X, ∃ j, x ∈ V j) → ∀ (T : ∀ j, Set (F.obj (op (V j)))), (∀ j, (T j).Finite) → ∀ W : X.Opens, IsAffineOpen W → (subMap F α V T W).Finite := by
  first | exact @GlobalTheory.QcSub.subMap_finite | exact GlobalTheory.QcSub.subMap_finite | (intros; apply GlobalTheory.QcSub.subMap_finite <;> assumption)
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem _root_.GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  first | exact @GlobalTheory.RealWeil.Osc.exists_isOsc | exact GlobalTheory.RealWeil.Osc.exists_isOsc | (intros; apply GlobalTheory.RealWeil.Osc.exists_isOsc <;> assumption)
end

section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem _root_.GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | exact GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | (intros; apply GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound <;> assumption)
end

section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

theorem _root_.GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧ Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧ ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
  first | exact @GlobalTheory.SphereMeanDrop.radProb_log_mean | exact GlobalTheory.SphereMeanDrop.radProb_log_mean | (intros; apply GlobalTheory.SphereMeanDrop.radProb_log_mean <;> assumption)
end
