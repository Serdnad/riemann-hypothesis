module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle663
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit



theorem res_resGen_of_pow (q : ℕ) [NeZero q] {W V : Scheme.{0}} (k : W ⟶ V) (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : k.appTop.hom ξ.1 = k.appTop.hom ζ.1 ^ (a : ZMod q).val) :
    Sec.res k (resGen 1 ξ) = (a : ZMod q).val • resGen 1 (ζ.map k.appTop.hom) := by
  have e1 : Sec.res k (resGen 1 ξ) = resGen 1 (ξ.map k.appTop.hom) := by
    unfold resGen
    rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
  rw [e1]
  have e2 := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.2.1 W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) a h
  simp only [zpow_one] at e2
  unfold resGen
  rw [e2]
  exact map_nsmul ((resι (ZMod q) (tw q 1)).hom.app (op W)).hom _ _

end GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit



theorem relation_kernel (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (hc : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  classical
  set d : unitsP.obj (op V) →₀ ULift.{1} (ZMod q) :=
    c.sum fun x r => Finsupp.single (unitsP.mk (tripP.get x).tgt) r - Finsupp.single (unitsP.mk (tripP.get x).src) r
    with hd_def
  have hd : (d.sum fun u r => r • freeGen (ZMod q) unitsP V u) = 0 := by
    rw [← Finsupp.linearCombination_apply, hd_def, map_finsuppSum, ← hc]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
  have hloc := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) unitsP V).2 d hd
  by_cases hc0 : c = 0
  · simp [hc0]
  obtain ⟨x₀, -⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hroots : ∀ x : ↥c.support, Loc V fun _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val :=
    fun x => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (tripP.get x₀).root (tripP.get x.1).root
  have hall := loc_calculus.2.2.2.2.2.1 V (↥c.support) (fun x _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val) hroots
  have hboth := loc_calculus.2.2.1 V _ _ hloc hall
  apply sec_eq_zero_of_loc
  refine loc_calculus.2.1 V _ _ hboth ?_
  rintro W k ⟨hkd, hka⟩
  rw [res_sum]
  by_cases hW : IsEmpty W
  · exact sec_eq_zero_of_loc _ _ (loc_calculus.2.2.2.2.2.2 W _)
  rw [not_isEmpty_iff] at hW
  haveI : Nontrivial Γ(W, ⊤) := @Scheme.component_nontrivial W ⊤ ⟨⟨hW.some, trivial⟩⟩
  choose a ha using hka
  let a' : (tripP q).obj (op V) → ℕ := fun x =>
    if h : x ∈ c.support then ((a ⟨x, h⟩ : (ZMod q)ˣ) : ZMod q).val else 0
  have hax : ∀ x (hx : x ∈ c.support), a' x = ((a ⟨x, hx⟩ : (ZMod q)ˣ) : ZMod q).val := fun x hx => dif_pos hx
  have hsum : (c.sum fun x r => r • Sec.res k (resGen 1 (tripP.get x).root)) =
      (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) •
        resGen 1 ((tripP.get x₀).root.map k.appTop.hom) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [res_resGen_of_pow q k (tripP.get x₀).root _ (a ⟨x, hx⟩) (ha ⟨x, hx⟩), ← hax x hx, mul_smul,
      Nat.cast_smul_eq_nsmul]
  have halg := GlobalTheory.T.primitiveRoot_free_action_finsupp_sum q Γ(W, ⊤) ((tripP.get x₀).root.map k.appTop.hom) ((tripP q).obj (op V)) c.support
    (fun x => c x) a'
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).src)
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).tgt) ?_ ?_
  · rw [hsum]
    suffices h0 : (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) = 0 by rw [h0, zero_smul]
    apply ULift.ext
    rw [Finsupp.sum]
    refine Eq.trans ?_ halg
    induction c.support using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ULift.add_down, ih]; simp
  · intro x hx
    rw [hax x hx]
    change k.appTop.hom ((tripP.get x).tgt : Γ(V, ⊤)) =
      k.appTop.hom (tripP.get x₀).root.1 ^ _ * k.appTop.hom ((tripP.get x).src : Γ(V, ⊤))
    rw [(tripP.get x).tgt_eq, map_mul, ha ⟨x, hx⟩]
  · rw [hd_def, Finsupp.sum, Finsupp.mapDomain_finsetSum] at hkd
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, unitsP.map_mk] at hkd
    exact hkd

end GlobalTheory.EtC.KummerSplit
end

section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem closureEtaleAt_comap_baseChange_atPrime : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) := by
  intro A R R₁ DA _ _ _ _ _ _ κ P₁ _ h
  letI := closureAlg A R DA
  letI iRS : Algebra R (Localization.AtPrime P₁) :=
    ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
  have hunit : ∀ y : (P₁.comap κ).primeCompl,
      IsUnit (algebraMap R (Localization.AtPrime P₁) y) := by
    intro y
    exact IsLocalization.map_units (Localization.AtPrime P₁)
      (⟨κ y, y.2⟩ : P₁.primeCompl)
  letI : Algebra (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    (IsLocalization.lift (M := (P₁.comap κ).primeCompl) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.lift_eq (M := (P₁.comap κ).primeCompl) hunit x).symm)
  haveI : Algebra.Etale (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA) := h
  haveI : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[Localization.AtPrime (P₁.comap κ)]
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA)) :=
    Algebra.Etale.baseChange _ _ _
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime P₁) (Localization.AtPrime P₁) (closure A R DA))

end GlobalTheory.KeyOriginEnlarge
end
end

section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology

namespace GlobalTheory.EZ
universe u v

theorem ez_nat {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    (Y : SimplicialObject (SimplicialObject C)) :
    ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  obtain ⟨G, h0, hG⟩ := GlobalTheory.T.exists_bisimplicial_shuffle_operators
  obtain ⟨H, hH⟩ := GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id G h0 hG
  obtain ⟨K, hK⟩ := GlobalTheory.T.alexander_whitney_homotopy_formula G h0 hG
  exact GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv Y G H K h0 hG hH hK

variable (R : Type) [CommRing R]

theorem ez (X : SimplicialObject GlobalTheory.EtC.Spc) :
    ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X),
      ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n :=
  GlobalTheory.T.eilenberg_zilber_homotopy_equivalence R X (ez_nat _)

def ezEquiv (X : SimplicialObject GlobalTheory.EtC.Spc) :
    HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X) := (ez R X).choose

def awChains (X : SimplicialObject GlobalTheory.EtC.Spc) : (GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X) ⟶ totChains R X :=
  (ezEquiv R X).hom

theorem awChains_f (X : SimplicialObject GlobalTheory.EtC.Spc) (n : ℕ) : (awChains R X).f (-(n : ℤ)) = awZ R X n :=
  (ez R X).choose_spec n

theorem pull_awChains_bijective (X : SimplicialObject GlobalTheory.EtC.Spc) (I : GlobalTheory.EtC.Cx R) (k : ℤ) :
    Function.Bijective (GlobalTheory.EtC.cpull (awChains R X) I k) :=
  GlobalTheory.EtC.LevelCmp.cpull_bij_of_heq (ezEquiv R X) I k

end GlobalTheory.EZ
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.exists_affineSpace_morphism_of_coordinates : ∀ (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg) (x : Fin n → Γ(T, ⊤)), ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  first | (exact @GlobalTheory.HomFixPoint.exists_affine_hom) | (exact GlobalTheory.HomFixPoint.exists_affine_hom) | (intros; apply GlobalTheory.HomFixPoint.exists_affine_hom  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat


theorem _root_.GlobalTheory.T.isMatrixIdentity_germ_pullback_chart : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.isMat_germ) | (exact GlobalTheory.HomFixMat.isMat_germ) | (intros; apply GlobalTheory.HomFixMat.isMat_germ  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem epi_of_isPullback_galois {X Y P Q : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (hc : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {a : P ⟶ X} {b : P ⟶ Q} {c : Q ⟶ Y} (h : IsPullback a b π c) : Epi b := by
  have e := h.flip.isoPullback_hom_fst
  have := GlobalTheory.GaloisCartDesc.epi_pullback_fst hc c
  rw [← e]
  exact epi_comp _ _

variable {S : Scheme.{0}}

theorem isPullback_whiskerRight_fst {A A' : Over S} (ψ : A ⟶ A') (B : Over S) :
    IsPullback (pullback.fst A.hom B.hom) (ψ ▷ B).left ψ.left (pullback.fst A'.hom B.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd A'.hom B.hom) (v₂₂ := A'.hom) (h₃₁ := B.hom) ?_
    (Over.whiskerRight_left_fst ψ).symm (IsPullback.of_hasPullback A'.hom B.hom)
  rw [Over.whiskerRight_left_snd, Over.w]
  exact IsPullback.of_hasPullback A.hom B.hom

theorem isPullback_whiskerLeft_snd {A A' : Over S} (ψ : A ⟶ A') (B : Over S) :
    IsPullback (pullback.snd B.hom A.hom) (B ◁ ψ).left ψ.left (pullback.snd B.hom A'.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.fst B.hom A'.hom) (v₂₂ := A'.hom) (h₃₁ := B.hom) ?_
    (Over.whiskerLeft_left_snd ψ).symm (IsPullback.of_hasPullback B.hom A'.hom).flip
  rw [Over.whiskerLeft_left_fst, Over.w]
  exact (IsPullback.of_hasPullback B.hom A.hom).flip

theorem exists_desc_endo (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A') (hψ : IsMonHom ψ)
    (hc : GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left)
    (f : A ⟶ A) (hf : IsMonHom f) (hH : ∀ h ∈ H, h ≫ f ∈ H) :
    ∃ f' : A' ⟶ A', IsMonHom f' ∧ ψ ≫ f' = f ≫ ψ := by

  have kill : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hc.inv ⟨h, hh⟩)
  have inv : ∀ a : H, (transl a.1).left ≫ f.left ≫ ψ.left = f.left ≫ ψ.left := by
    intro a
    have e : transl a.1 ≫ f ≫ ψ = f ≫ ψ := by
      have k1 : toUnit A ≫ a.1 ≫ f ≫ ψ = 1 := by
        rw [← Category.assoc a.1, kill _ (hH _ a.2), comp_one]
      rw [transl, MonObj.mul_comp, Category.id_comp, Category.assoc, k1, _root_.mul_one]
    simpa using congrArg Over.Hom.left e
  obtain ⟨g, hg, -⟩ := hc.existsUnique_desc (f.left ≫ ψ.left) inv
  have hepi := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hc
  have gw : g ≫ A'.hom = A'.hom := by
    rw [← cancel_epi ψ.left, reassoc_of% hg, Over.w, Over.w]
  let f' : A' ⟶ A' := Over.homMk g gw
  have hf' : ψ ≫ f' = f ≫ ψ := Over.OverMorphism.ext (by simpa [f'] using hg)
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · rw [← IsMonHom.one_hom ψ, Category.assoc, hf', ← Category.assoc, IsMonHom.one_hom f]
  · have e1 : Epi (ψ ▷ A).left := epi_of_isPullback_galois hc (isPullback_whiskerRight_fst ψ A)
    have e2 : Epi (A' ◁ ψ).left := epi_of_isPullback_galois hc (isPullback_whiskerLeft_snd ψ A')
    have : Epi (ψ ⊗ₘ ψ) := by
      rw [MonoidalCategory.tensorHom_def]
      have := Over.epi_of_epi_left (ψ ▷ A)
      have := Over.epi_of_epi_left (A' ◁ ψ)
      exact epi_comp _ _
    rw [← cancel_epi (ψ ⊗ₘ ψ), ← reassoc_of% (IsMonHom.mul_hom ψ), hf', ← Category.assoc,
      IsMonHom.mul_hom f, Category.assoc, IsMonHom.mul_hom ψ]
    simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hf']

end GlobalTheory.UPel.HT.Hecke
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HomDescent

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft' (A : Over S) {Y Z : Over S} (q : Y ⟶ Z) :
    IsPullback (A ◁ q).left (snd A Y).left (snd A Z).left q.left := by
  have h1 : IsPullback (fst A Z).left (snd A Z).left A.hom Z.hom := IsPullback.of_hasPullback A.hom Z.hom
  have h2 : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback A.hom Y.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight' {A A' : Over S} (q : A ⟶ A') (Y : Over S) :
    IsPullback (q ▷ Y).left (fst A Y).left (fst A' Y).left q.left := by
  have h1 : IsPullback (snd A' Y).left (fst A' Y).left Y.hom A'.hom :=
    (IsPullback.of_hasPullback A'.hom Y.hom).flip
  have h2 : IsPullback (snd A Y).left (fst A Y).left Y.hom A.hom := (IsPullback.of_hasPullback A.hom Y.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem epi_of_isPullback {X Y P Q : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {u : P ⟶ Q} {v : P ⟶ X} {t : Q ⟶ Y} (hp : IsPullback u v t π) : Epi u := by
  have := GlobalTheory.GaloisCartDesc.epi_pullback_fst h t
  rw [← hp.isoPullback_hom_fst]
  infer_instance

theorem exists_desc : ∀ (S : Scheme.{0}) (A A' B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj B] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ B, IsMonHom f → (∀ h ∈ H, h ≫ f = 1) → ∃ f' : A' ⟶ B, IsMonHom f' ∧ ψ ≫ f' = f := by
  intro S A A' B _ _ _ _ _ H ψ hψ hG f hf hH
  have inv : ∀ a : H, (GlobalTheory.UPel.HT.Hecke.transl a.1).left ≫ f.left = f.left := by
    intro a
    rw [← Over.comp_left]
    congr 1
    rw [GlobalTheory.UPel.HT.Hecke.transl, mul_comp, Category.id_comp, Category.assoc, hH a.1 a.2, comp_one, _root_.mul_one]
  obtain ⟨g, hg, -⟩ := hG.existsUnique_desc f.left inv
  have eψ : Epi ψ.left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG
  have w : g ≫ B.hom = A'.hom := by
    rw [← cancel_epi ψ.left, reassoc_of% hg, Over.w, Over.w]
  let f' : A' ⟶ B := Over.homMk g w
  have hf' : ψ ≫ f' = f := Over.OverMorphism.ext hg
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · rw [← IsMonHom.one_hom ψ, Category.assoc, hf', IsMonHom.one_hom]
  · have e1 : Epi (ψ ▷ A).left := epi_of_isPullback hG (isPullback_whiskerRight' ψ A)
    have e2 : Epi (A' ◁ ψ).left := epi_of_isPullback hG (isPullback_whiskerLeft' A' ψ)
    have e : Epi (ψ ⊗ₘ ψ).left := by
      rw [MonoidalCategory.tensorHom_def, Over.comp_left]; infer_instance
    apply Over.OverMorphism.ext
    rw [← cancel_epi (ψ ⊗ₘ ψ).left, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← Category.assoc, ← IsMonHom.mul_hom ψ, Category.assoc, hf', IsMonHom.mul_hom, ← hf',
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]

end GlobalTheory.HomDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.geometric_fibre_mulK_torsor_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK) | (exact GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK) | (intros; apply GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open Matrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem exists_ideal_rank_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B),
    ∃ K₂ : Ideal B, ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f) := by
  intro p _ D R _ b B _ βB n M
  set J := lieIdeal b βB M with hJdef
  let P : Fin D.a → Matrix (Fin n) (Fin n) (B ⧸ J) := fun i => (projMat b βB M i).map (Ideal.Quotient.mk J)
  have hJmk : J ≤ RingHom.ker (Ideal.Quotient.mk J) := fun a ha => by
    rw [RingHom.mem_ker]; exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hrange : ∀ (K : Type) [CommRing K] (g : B →+* K), J ≤ RingHom.ker g → ∀ i : Fin D.a,
      (eigSub (matAct M g) ((g.comp βB).comp (b.t i)) : Set (Fin n → K)) =
        LinearMap.range ((projMat b βB M i).map g).mulVecLin := by
    intro K _ g hg i
    ext v
    simp only [SetLike.mem_coe, mem_eigSub, matAct_apply, LinearMap.mem_range, Matrix.mulVecLin_apply,
      RingHom.coe_comp, Function.comp_apply]
    constructor
    · intro hv
      exact ⟨v, GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector p D R b B βB n M K g i v hv⟩
    · rintro ⟨w, rfl⟩ c
      rw [Matrix.mulVec_mulVec, GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar p D R b B βB n M K g hg i c, Matrix.smul_mulVec]
  have hidem : ∀ i, P i * P i = P i := by
    intro i
    apply (Matrix.toLin' (R := B ⧸ J) (m := Fin n) (n := Fin n)).injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec]
    apply GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector p D R b B βB n M _ (Ideal.Quotient.mk J) i
    intro c
    rw [Matrix.mulVec_mulVec, GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar p D R b B βB n M _ _ hJmk i c, Matrix.smul_mulVec]
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_rank_ideal_of_idempotent' (B ⧸ J) (Fin D.a) n P hidem D.m
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.span {x'}, fun T _ f hf => ?_⟩
  have hfa : ∀ a ∈ J, f a = 0 := fun a ha => RingHom.mem_ker.1 (hf ha)
  let fb : B ⧸ J →+* T := Ideal.Quotient.lift J f hfa
  have hfb : fb.comp (Ideal.Quotient.mk J) = f := Ideal.Quotient.lift_comp_mk _ _ _
  rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  have hx' := hx T fb
  rw [show fb (Ideal.Quotient.mk J x') = f x' from Ideal.Quotient.lift_mk _ _ _] at hx'
  rw [← hx']
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun h => forall_congr' fun i => ?_
  have e1 : eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i)) =
      LinearMap.range ((P i).map (h.comp fb)).mulVecLin := by
    apply SetLike.coe_injective
    show (eigSub (matAct M (h.comp f)) (((h.comp f).comp βB).comp (b.t i)) : Set (Fin n → k)) = _
    rw [hrange k (h.comp f) (fun a ha => by simp [hfa a ha]) i]
    congr 3
  rw [e1, GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk (B ⧸ J) n (P i) (hidem i) k (h.comp fb)]

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_deformedLatticeEisensteinSummand_weight_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) → ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E → (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)), x = (a : E) + (b : E) * θ) → ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S → HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  first | exact @GlobalTheory.WeightTwoCompare.hasSum_defTerm | exact GlobalTheory.WeightTwoCompare.hasSum_defTerm | (intros; apply GlobalTheory.WeightTwoCompare.hasSum_defTerm <;> assumption)
end
