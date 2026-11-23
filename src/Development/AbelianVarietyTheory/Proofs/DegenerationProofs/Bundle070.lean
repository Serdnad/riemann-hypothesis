module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem exists_splitExt_of_galois_invariant :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  intro k K _ _ _ _ _ G₀ B₀ _ _ _ hB₀ G B _ _ X _ _ _ φG φ hG hB q i hq hfl hsu hqc hi H hinv
  have spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
      spMap (g.comp f) = spMap g ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl

  have spMap_surjective' {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
      ∃ f : A →+* B, spMap f = y :=
    ⟨(Spec.preimage y).hom, by simp [spMap]⟩

  have spMap_inj_lemma_3 {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
      f = g := by
    have h' := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom h'

  have hc : GlobalTheory.ZM.IsGaloisCover (K ≃ₐ[k] K) (fun σ => spMap (σ : K →+* K)) (spMap (algebraMap k K)) := by
    refine
      { finite := inferInstance
        one := ?_
        mul := ?_
        inv := ?_
        fin := ?_
        etale := ?_
        onto := ?_
        fibre := ?_ }
    · show Spec.map _ = _
      convert Spec.map_id (CommRingCat.of K)
      rfl
    · intro a c
      show spMap (((a * c : K ≃ₐ[k] K) : K →+* K)) = _
      rw [← spMap_comp_moduli_spaces]
      rfl
    · intro a
      rw [← spMap_comp_moduli_spaces]
      congr 1
      ext r
      exact a.commutes r
    · show IsFinite (Spec.map _)
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    · show Etale (Spec.map _)
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      show (algebraMap k K).Etale
      rw [RingHom.etale_algebraMap]
      exact ⟨Algebra.FormallyEtale.of_isSeparable k K, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    · exact ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    · intro k' _ _ y y' h
      obtain ⟨f, rfl⟩ := spMap_surjective' y
      obtain ⟨f', rfl⟩ := spMap_surjective' y'
      rw [← spMap_comp_moduli_spaces, ← spMap_comp_moduli_spaces] at h
      have hfa := spMap_inj_lemma_3 h
      let _ : Algebra k k' := (f.comp (algebraMap k K)).toAlgebra
      let φ : K →ₐ[k] k' := { f with commutes' := fun _ => rfl }
      let φ' : K →ₐ[k] k' :=
        { f' with commutes' := fun r => (RingHom.congr_fun hfa r).symm }
      let Φ : (K ≃ₐ[k] K) → (K →ₐ[k] k') := fun a => φ.comp a.toAlgHom
      have hinj : Function.Injective Φ := by
        intro a b hab
        ext x
        exact f.injective (AlgHom.congr_fun hab x)
      have hcard : Nat.card (K →ₐ[k] k') ≤ Nat.card (K ≃ₐ[k] K) := by
        rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, AlgHom.card]
      obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hcard).2 φ'
      refine ⟨a, ?_, fun b hb => ?_⟩
      · show spMap f ≫ spMap (a : K →+* K) = spMap f'
        rw [← spMap_comp_moduli_spaces]
        congr 1
        ext x
        exact AlgHom.congr_fun ha x
      · have hb' : f.comp (b : K →+* K) = f' := by
          have hb0 : spMap f ≫ spMap (b : K →+* K) = spMap f' := hb
          rw [← spMap_comp_moduli_spaces] at hb0
          exact spMap_inj_lemma_3 hb0
        apply hinj
        ext x
        exact (RingHom.congr_fun hb' x).trans (AlgHom.congr_fun ha x).symm
  have coverPull {A B A' B' : Scheme} {p : A ⟶ B} {p' : A' ⟶ B'}
      {Γ : Type} [Group Γ] {ρ : Γ → (A ⟶ A)} {ρ' : Γ → (A' ⟶ A')}
      {u : A' ⟶ A} {v : B' ⟶ B} (h : GlobalTheory.ZM.IsGaloisCover Γ ρ p)
      (hp : IsPullback u p' p v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
      (hin : ∀ a, ρ' a ≫ p' = p') : GlobalTheory.ZM.IsGaloisCover Γ ρ' p' :=
    ((GlobalTheory.ZM.galoisCover_descent A B p Γ ρ h).2.2 A' B' p' ρ' u v hu hp.w).2 hp hin
  have coverDesc {A B : Scheme} {p : A ⟶ B} {Γ : Type} [Group Γ]
      {ρ : Γ → (A ⟶ A)} (h : GlobalTheory.ZM.IsGaloisCover Γ ρ p)
      {Z : Scheme} (f : A ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
      ∃! f' : B ⟶ Z, p ≫ f' = f :=
    (GlobalTheory.ZM.galoisCover_descent A B p Γ ρ h).1 Z f hf
  let s : (K ≃ₐ[k] K) → (G.left ⟶ G.left) := fun τ =>
    hG.1.lift φG (G.hom ≫ spMap (τ : K →+* K)) (by rw [Category.assoc, hc.inv, hG.1.w])
  have hs₁ : ∀ τ, s τ ≫ φG = φG := fun τ => hG.1.lift_fst _ _ _
  have hs₂ : ∀ τ, s τ ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) := fun τ => hG.1.lift_snd _ _ _
  have hcG := coverPull hc (ρ' := s) hG.1.flip hs₂ hs₁
  have bcFst {S S' : Scheme} (f : S' ⟶ S) :
      SplitTorus.bcMap f X ≫ Rosenlicht.torusFst S X = Rosenlicht.torusFst S' X :=
    pullback.lift_fst _ _ _
  have hT := SplitTorus.isPullback_bcMap (spMap (algebraMap k K)) X
  have hcT := coverPull hc
    (ρ' := fun τ : K ≃ₐ[k] K => SplitTorus.bcMap (spMap (τ : K →+* K)) X) hT.flip
    (fun τ => SplitTorus.bcMap_hom _ X) (fun τ => pullback.hom_ext
      (by
        have e := bcFst (spMap (algebraMap k K))
        exact (Category.assoc _ _ _).trans ((congrArg _ e).trans
          ((bcFst _).trans e.symm)))
      (by
        have e := SplitTorus.bcMap_hom (spMap (algebraMap k K)) X
        refine (Category.assoc _ _ _).trans ((congrArg _ e).trans (Eq.trans ?_ e.symm))
        rw [SplitTorus.bcMap_hom_assoc, hc.inv]))
  obtain ⟨q', hq', -⟩ := coverDesc hcG (q.left ≫ φ) fun τ => (hinv τ _ (hs₁ τ) (hs₂ τ)).1
  obtain ⟨i', hi', -⟩ := coverDesc hcT (i.left ≫ φG) fun τ => by
    rw [← Category.assoc, (hinv τ _ (hs₁ τ) (hs₂ τ)).2, Category.assoc, hs₁]
  have wq : q' ≫ B₀.hom = G₀.hom :=
    (coverDesc hcG (φG ≫ G₀.hom) fun τ => by rw [← Category.assoc, hs₁]).unique
      (by rw [← Category.assoc, hq', Category.assoc, hB.1.w, ← Category.assoc, Over.w, hG.1.w]) rfl
  have wi : i' ≫ G₀.hom = (splitTorus (Sp k) X).hom :=
    (coverDesc hcT (SplitTorus.bcMap (spMap (algebraMap k K)) X ≫ (splitTorus (Sp k) X).hom)
      fun τ => by rw [← Category.assoc, hcT.inv]).unique
      (by rw [← Category.assoc, hi', Category.assoc, hG.1.w, ← Category.assoc, Over.w, hT.w]) rfl
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := splitTorus_extension_descends k K (algebraMap k K) G B G₀ B₀ X
    φG φ hG hB q i (Over.homMk q' wq) (Over.homMk i' wi) hq' hi' hq hfl hsu hqc hi H
  obtain ⟨O, a, b, c, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X G₀ B₀ hB₀ _ _
    h₁ h₅ h₂ h₃ h₄ h₆
  obtain ⟨d, -⟩ := h hB₀
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory

end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionFrame_pow_eq_integral_generator : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (M : RigLB G) (B : Scheme.{0}) (P : PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (t : Sp (FractionRing V) ⟶ B) (ψ : pullback G.hom (jK V) ⟶ P.A.left), IsGrpPullback ((Over.pullback (jK V)).obj G) P.A t ψ → ∀ (w : LB.Iso (M.L.pull (pullback.fst G.hom (jK V))) (P.L.pull ψ)), w.IsGen → ∀ n : ℕ, ∃ lam : FractionRing V, lam ≠ 0 ∧ ∀ (z : baseOver B ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver B).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))), IsTorsFrame P rig n z τ → ∀ (h : baseOver (Sp V) ⟶ G) (x : Sp (FractionRing V) ⟶ pullback G.hom (jK V)), x ≫ pullback.fst G.hom (jK V) = jK V ≫ h.left → x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → x ≫ ψ = t ≫ z.left → ∀ (i : M.L.ι) (k : P.L.ι), ⊤ ≤ h.left ⁻¹ᵁ M.L.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ P.L.U k → ∃ v : Vˣ, valR (X := (baseOver B).left) t _ (τ.s (fun _ => k)).val ^ (n ^ 2) = (lam * valR x _ (w.s (fun _ => k, fun _ => i)).val) ^ (n ^ 2) * algebraMap V (FractionRing V) v := by
  first | exact @GlobalTheory.TorsFrameInt.torsFrame_pow_eq | exact GlobalTheory.TorsFrameInt.torsFrame_pow_eq | (intros; apply GlobalTheory.TorsFrameInt.torsFrame_pow_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.exists_gtDatum_baseChange_maps' : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G), ∃ (E' : SplitExt S') (xe : E'.X ≃+ E.X) (d' : E'.GtDatum ((Over.pullback f).obj G)) (π : E'.B.left ⟶ E.B.left), IsGrpPullback E'.B E.B f π ∧ d'.q.left ≫ π = pullback.fst G.hom f ≫ d.q.left ∧ (∀ χ, LBIso (E'.O χ).L ((E.O (xe χ)).L.pull π)) ∧ ∀ (Z : Over S') (τ : Z ⟶ splitTorus S' E'.X), ∃ τ₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S E.X, (τ₀ ≫ d.i).left = (τ ≫ d'.i).left ≫ pullback.fst G.hom f ∧ ∀ (χ : E'.X) (z : Z.left), gm (Y := Z.left) τ₀.left z ⊤ (charUnit S E.X (xe χ)) = gm τ.left z ⊤ (charUnit S' E'.X χ) := by
  first | exact @GlobalTheory.exists_gtDatum_baseChange_maps | exact GlobalTheory.exists_gtDatum_baseChange_maps | (intros; apply GlobalTheory.exists_gtDatum_baseChange_maps <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGen_one_of_g_eq_one {X : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) :
    (⟨fun _ => 1⟩ : LB.Gen L).IsGen := fun i j =>
  (map_one _).trans ((congrArg₂ (· * ·) (h i j) (map_one _)).trans (_root_.mul_one _)).symm

theorem div_g_eq_one {X : Scheme.{0}} (M L : LB X) (hM : ∀ i j, M.g i j = 1) (hL : ∀ i j, L.g i j = 1)
    (i j : (LB.div M L).ι) : (LB.div M L).g i j = 1 := by
  simp only [LB.div, hM, hL, map_one, inv_one, _root_.mul_one]
  rfl

theorem isGen_one_linComb_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.LinComb (Out.Inh.trivLB X) φ ε)).IsGen :=
  isGen_one_of_g_eq_one _ (Out.Inh.linComb_triv_g φ ε)

def splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) : SplitExt S where
  B := B
  isAbelian := h
  X := PUnit
  O := fun _ => ⟨Out.Inh.trivLB _, ⟨fun _ => 1⟩, Out.Inh.trivLB_isLB _, isGen_one_linComb_triv _ _⟩
  addIso := fun _ _ => ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _
    (div_g_eq_one _ _ (div_g_eq_one _ _ (fun _ _ => rfl) fun _ _ => rfl) fun _ _ => rfl)⟩
  zeroTriv := ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _ fun _ _ => rfl⟩
  primitive := fun _ => ⟨⟨fun _ => 1⟩, isGen_one_linComb_triv _ _⟩

theorem isGt_splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) :
    (splitExtOfAbelian B h).IsGt B := by
  have := h.comm
  have := isIso_toUnit_splitTorus_punit S
  have hk : IsPullback (toUnit (splitTorus S PUnit) ≫ η[B]) (toUnit _) (𝟙 B) η[B] :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  refine CoordToExt.isGt_of_units (splitExtOfAbelian B h) (𝟙 B) (toUnit _ ≫ η[B])
    (inferInstanceAs (IsMonHom (𝟙 B)))
    (inferInstanceAs (IsMonHom (toUnit (splitTorus S PUnit) ≫ η[B])))
    (inferInstanceAs (Flat (𝟙 B.left))) (inferInstanceAs (Surjective (𝟙 B.left)))
    (inferInstanceAs (IsAffineHom (𝟙 B.left))) hk (fun _ _ => 1) ?_ ?_ ?_
  · intro χ Z r z a a' _ _
    exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · intro χ a Z t g z _
    have e : charUnit S PUnit χ = 1 := by
      have e₀ : Multiplicative.ofAdd (α := PUnit) χ = 1 := rfl
      unfold charUnit
      rw [e₀]
      simp only [map_one]
      exact (congrArg _ (map_one _)).trans (map_one _)
    exact (map_one _).trans ((congrArg₂ (· * ·) ((congrArg _ e).trans (map_one _)) (map_one _)).trans
      (_root_.mul_one _)).symm
  · intro χ a y _
    exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)

section

variable {T V Z G H : Scheme.{0}} {f : H ⟶ G} {s : H ⟶ V} {t : G ⟶ Z} {y₀ : V ⟶ Z}

end

section

variable (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated π] (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (A : Over Z) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom)

end

end GlobalTheory.ZJ

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.exists_symLift_of_pow_eq_one : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k → IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  first | exact @GlobalTheory.exists_symLift_global | exact GlobalTheory.exists_symLift_global | (intros; apply GlobalTheory.exists_symLift_global <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.exists_normalised_mulPull_iso_origin : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  first | exact @GlobalTheory.ThetaReal.exists_normalised_mulPull | exact GlobalTheory.ThetaReal.exists_normalised_mulPull | (intros; apply GlobalTheory.ThetaReal.exists_normalised_mulPull <;> assumption)
end
