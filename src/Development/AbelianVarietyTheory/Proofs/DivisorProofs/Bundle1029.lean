module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle912
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
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
import Mathlib.Data.Finset.Functor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.IntAcyc

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def finDiag : Finset B ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin A (t : Set B))
  map {t u} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def finCocone : Cocone (finDiag A B) where
  pt := CommRingCat.of B
  ι := { app := fun t => CommRingCat.ofHom (Algebra.adjoin A (t : Set B)).val.toRingHom
         naturality := fun _ _ _ => by ext; rfl }

def finCoconeIsColimit : IsColimit (finCocone A B) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset B) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (finCocone A B)) ?_ ?_)
  · intro x
    exact ⟨{x}, ⟨x, Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, ?_⟩
    apply Subtype.ext
    exact h

theorem finite_finDiag [Algebra.IsIntegral A B] (t : Finset B) :
    Module.Finite A (Algebra.adjoin A (t : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

end GlobalTheory.EtC.IntAcyc
end

namespace GlobalTheory.EtC.IntAcyc

theorem acycF_of_isIntegral : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      SH A → AcycF R (sp B) F := by
  classical
  intro R _ F hF A B _ _ _ _ hA
  obtain ⟨hHens, hSep⟩ := hA
  intro n hn
  suffices h : ∀ x : H R (sp B) F n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF (Finset B) (finDiag A B) (finCocone A B)
    (finCoconeIsColimit A B) n).1 x
  haveI := finite_finDiag A B j
  obtain ⟨ι, hι, T, hT, hAl, e, hH, hS⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A (Algebra.adjoin A (j : Set B))
  have hac : AcycF R (sp ((finDiag A B).obj j)) F :=
    GlobalTheory.T.acycF_of_pi_sh' R F ι T ((finDiag A B).obj j) ⟨e.toRingEquiv⟩ (fun i => ⟨hH i, (hS i).1⟩)
  haveI := hac n hn
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [← hy, hy0]
  exact map_zero _

end GlobalTheory.EtC.IntAcyc
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

section Corner

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem comp_proj_eq_of_comp_eq_zero {X Y Y₀ Y₁ : PDivGroup p k} (f : X ⟶ Y) (r₀ : Y ⟶ Y₀)
    (j₀ : Y₀ ⟶ Y) (r₁ : Y ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (hY : r₀ ≫ j₀ + r₁ ≫ j₁ = 𝟙 Y)
    (h : f ≫ r₁ = 0) : f ≫ r₀ ≫ j₀ = f := by
  have h' : f ≫ r₁ ≫ j₁ = 0 := by rw [← Category.assoc, h, Limits.zero_comp]
  calc f ≫ r₀ ≫ j₀ = f ≫ r₀ ≫ j₀ + f ≫ r₁ ≫ j₁ := by rw [h', add_zero]
    _ = f ≫ 𝟙 Y := by rw [← hY, Preadditive.comp_add]
    _ = f := Category.comp_id f

theorem proj_comp_eq_of_comp_eq_zero {X X₀ X₁ Y : PDivGroup p k} (f : X ⟶ Y) (π₀ : X ⟶ X₀)
    (i₀ : X₀ ⟶ X) (π₁ : X ⟶ X₁) (i₁ : X₁ ⟶ X) (hX : π₀ ≫ i₀ + π₁ ≫ i₁ = 𝟙 X)
    (h : i₀ ≫ f = 0) : π₁ ≫ i₁ ≫ f = f := by
  have h' : π₀ ≫ i₀ ≫ f = 0 := by rw [h, Limits.comp_zero]
  calc π₁ ≫ i₁ ≫ f = π₀ ≫ i₀ ≫ f + π₁ ≫ i₁ ≫ f := by rw [h', zero_add]
    _ = 𝟙 X ≫ f := by rw [← hX, Preadditive.add_comp, Category.assoc, Category.assoc]
    _ = f := Category.id_comp f

theorem isIsog_corner {G H G' H' : PDivGroup p k} (q : G ⟶ H) (hq : IsIsog q) (i : G' ⟶ G)
    (π : G ⟶ G') (j : H' ⟶ H) (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hjr : j ≫ r = 𝟙 H')
    (hq' : i ≫ q ≫ r ≫ j = i ≫ q) (hg : ∀ g : H ⟶ G, j ≫ g ≫ π ≫ i = j ≫ g) :
    IsIsog (i ≫ q ≫ r) := by
  unfold IsIsog at hq ⊢
  obtain ⟨n, g, h1, h2⟩ := hq
  refine ⟨n, j ≫ g ≫ π, ?_, ?_⟩
  · calc (i ≫ q ≫ r) ≫ j ≫ g ≫ π = (i ≫ q ≫ r ≫ j) ≫ g ≫ π := by
          simp only [Category.assoc]
      _ = i ≫ (q ≫ g) ≫ π := by rw [hq']; simp only [Category.assoc]
      _ = _ := by rw [h1, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hiπ]
  · calc (j ≫ g ≫ π) ≫ i ≫ q ≫ r = (j ≫ g ≫ π ≫ i) ≫ q ≫ r := by
          simp only [Category.assoc]
      _ = j ≫ (g ≫ q) ≫ r := by rw [hg g]; simp only [Category.assoc]
      _ = _ := by rw [h2, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hjr]

theorem omegaMap_corner_surjective {G H G' H' : PDivGroup p k} (q : G ⟶ H)
    (hs : Function.Surjective (omegaMap G H q)) (i : G' ⟶ G) (π : G ⟶ G') (j : H' ⟶ H)
    (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hq' : i ≫ q ≫ r ≫ j = i ≫ q) :
    Function.Surjective (omegaMap G' H' (i ≫ q ≫ r)) := by
  intro w
  obtain ⟨v, hv⟩ := hs (omegaMap G G' π w)
  refine ⟨omegaMap H' H j v, ?_⟩
  have e1 : omegaMap G' H' (i ≫ q ≫ r) (omegaMap H' H j v) = omegaMap G' H (i ≫ q) v := by
    rw [← LinearMap.comp_apply, ← omegaMap_comp]
    simp only [Category.assoc]
    rw [hq']
  rw [e1, omegaMap_comp, LinearMap.comp_apply, hv, ← LinearMap.comp_apply, ← omegaMap_comp, hiπ,
    omegaMap_id, LinearMap.id_apply]

theorem isIsog_dualHom_of_isIsog {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    IsIsog (dualHom G H f) := by
  unfold IsIsog at hf ⊢
  obtain ⟨n, g, h1, h2⟩ := hf
  refine ⟨n, dualHom H G g, ?_, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]

theorem isIso_of_isIso_dualHom {G H : PDivGroup p k} (f : G ⟶ H) (h : IsIso (dualHom G H f)) :
    IsIso f := by
  obtain ⟨d, hd⟩ := (dualHom_bijective (G := H) (H := G)).2 (inv (dualHom G H f))
  refine ⟨⟨d, ?_, ?_⟩⟩
  · apply (dualHom_bijective (G := G) (H := G)).1
    rw [dualHom_comp, hd, IsIso.inv_hom_id, dualHom_id]
  · apply (dualHom_bijective (G := H) (H := H)).1
    rw [dualHom_comp, hd, IsIso.hom_inv_id, dualHom_id]

theorem isIso_of_isConn_of_omegaMap_surjective [CharP k p] {G H : PDivGroup p k} (f : G ⟶ H)
    (hG : G.IsConn) (hf : IsIsog f) (hs : Function.Surjective (omegaMap G H f)) : IsIso f := by
  have hsurj := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G H f hG hs
  apply ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.2 H f hf).1
  unfold HasLogDeg
  refine ⟨0, fun n _ => ?_⟩
  rw [pow_zero]
  exact (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k _ _ _).1 (hsurj n)

end Corner

theorem isIso_of_isIsog_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q →
    Function.Surjective (omegaMap G H q) →
    Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  intro p _ k _ _ _ G H q hq hs hsd
  obtain ⟨G₀, G₁, i₀, π₀, i₁, π₁, hG₀, hG₁, hi₀, hi₁, hG⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, hj₀, hj₁, hH⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k H
  have z : ∀ {X Y : PDivGroup p k}, X.IsConn → Y.IsEt → (∀ f : X ⟶ Y, f = 0) ∧ ∀ f : Y ⟶ X, f = 0 :=
    fun {X Y} hX hY => GlobalTheory.T.hom_eq_zero_of_isConn_of_isEt' p k X Y hX hY

  have c₀ : i₀ ≫ q ≫ r₀ ≫ j₀ = i₀ ≫ q := by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₀ ≫ q) r₀ j₀ r₁ j₁ hH ((z hG₀ hH₁).1 _)
  have c₁ : i₁ ≫ q ≫ r₁ ≫ j₁ = i₁ ≫ q := by
    have hH' : r₁ ≫ j₁ + r₀ ≫ j₀ = 𝟙 H := by rw [add_comm, hH]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₁ ≫ q) r₁ j₁ r₀ j₀ hH' ((z hH₀ hG₁).2 _)
  have g₀ : ∀ g : H ⟶ G, j₀ ≫ g ≫ π₀ ≫ i₀ = j₀ ≫ g := fun g => by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₀ ≫ g) π₀ i₀ π₁ i₁ hG ((z hH₀ hG₁).1 _)
  have g₁ : ∀ g : H ⟶ G, j₁ ≫ g ≫ π₁ ≫ i₁ = j₁ ≫ g := fun g => by
    have hG' : π₁ ≫ i₁ + π₀ ≫ i₀ = 𝟙 G := by rw [add_comm, hG]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₁ ≫ g) π₁ i₁ π₀ i₀ hG' ((z hG₀ hH₁).2 _)

  have ha : IsIso (i₀ ≫ q ≫ r₀) :=
    isIso_of_isConn_of_omegaMap_surjective _ hG₀ (isIsog_corner q hq i₀ π₀ j₀ r₀ hi₀ hj₀ c₀ g₀)
      (omegaMap_corner_surjective q hs i₀ π₀ j₀ r₀ hi₀ c₀)

  have hb : IsIso (i₁ ≫ q ≫ r₁) := by
    apply isIso_of_isIso_dualHom
    have hdb : dualHom G₁ H₁ (i₁ ≫ q ≫ r₁) =
        dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ := by
      rw [dualHom_comp, dualHom_comp, Category.assoc]
    have hrj : dualHom H H₁ r₁ ≫ dualHom H₁ H j₁ = 𝟙 H₁.dual := by
      rw [← dualHom_comp, hj₁, dualHom_id]
    have hq'd : dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ ≫ dualHom G G₁ π₁ =
        dualHom H H₁ r₁ ≫ dualHom G H q := by
      have e : π₁ ≫ i₁ ≫ q ≫ r₁ = q ≫ r₁ :=
        proj_comp_eq_of_comp_eq_zero (q ≫ r₁) π₀ i₀ π₁ i₁ hG
          (by rw [← Category.assoc]; exact (z hG₀ hH₁).1 _)
      have e' := congrArg (dualHom G H₁) e
      simp only [dualHom_comp, Category.assoc] at e'
      exact e'
    have hs' : Function.Surjective (omegaMap H₁.dual G₁.dual (dualHom G₁ H₁ (i₁ ≫ q ≫ r₁))) := by
      rw [hdb]
      exact omegaMap_corner_surjective (dualHom G H q) hsd (dualHom H H₁ r₁) (dualHom H₁ H j₁)
        (dualHom G G₁ π₁) (dualHom G₁ G i₁) hrj hq'd
    exact isIso_of_isConn_of_omegaMap_surjective _ (GlobalTheory.T.dual_isConn_of_isEt_pDivGroup p k H₁ hH₁)
      (isIsog_dualHom_of_isIsog _ (isIsog_corner q hq i₁ π₁ j₁ r₁ hi₁ hj₁ c₁ g₁)) hs'

  have hqd : q = π₀ ≫ (i₀ ≫ q ≫ r₀) ≫ j₀ + π₁ ≫ (i₁ ≫ q ≫ r₁) ≫ j₁ := by
    simp only [Category.assoc, c₀, c₁]
    rw [← Category.assoc π₀, ← Category.assoc π₁, ← Preadditive.add_comp, hG, Category.id_comp]
  have hj01 : j₀ ≫ r₁ = 0 := (z hH₀ hH₁).1 _
  have hj10 : j₁ ≫ r₀ = 0 := (z hH₀ hH₁).2 _
  have hi01 : i₀ ≫ π₁ = 0 := (z hG₀ hG₁).1 _
  have hi10 : i₁ ≫ π₀ = 0 := (z hG₀ hG₁).2 _
  generalize i₀ ≫ q ≫ r₀ = a at ha hqd
  generalize i₁ ≫ q ≫ r₁ = b at hb hqd
  subst hqd
  refine ⟨⟨r₀ ≫ inv a ≫ i₀ + r₁ ≫ inv b ≫ i₁, ?_, ?_⟩⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hj₀,
      reassoc_of% hj₁, reassoc_of% hj01, reassoc_of% hj10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.hom_inv_id_assoc]
    exact hG
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hi₀,
      reassoc_of% hi₁, reassoc_of% hi01, reassoc_of% hi10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.inv_hom_id_assoc]
    exact hH

end GlobalTheory.Dieu
end
end

section

open GlobalTheory GlobalTheory.LogDR


theorem _root_.GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  first | exact @GlobalTheory.LogDR.round_coeff_mem | exact GlobalTheory.LogDR.round_coeff_mem | (intros; apply GlobalTheory.LogDR.round_coeff_mem <;> assumption)
end

section

open GlobalTheory GlobalTheory.LogDR


theorem _root_.GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x → LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  first | exact @GlobalTheory.LogDR.logWedge_basis | exact GlobalTheory.LogDR.logWedge_basis | (intros; apply GlobalTheory.LogDR.logWedge_basis <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

theorem _root_.GlobalTheory.T.roundedTwist_localEquation_chart : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  first | exact @GlobalTheory.roundedTwist_isEqn | exact GlobalTheory.roundedTwist_isEqn | (intros; apply GlobalTheory.roundedTwist_isEqn <;> assumption)
end

section

open GlobalTheory GlobalTheory.LogDR


theorem _root_.GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K), IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  first | exact @GlobalTheory.cartierMap_smul_logWedge | exact GlobalTheory.cartierMap_smul_logWedge | (intros; apply GlobalTheory.cartierMap_smul_logWedge <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hasRepAF_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  intro S A _ g Y Y' e h
  obtain ⟨B, b, P, hR, hG, hF⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, ?_⟩, ?_, hF⟩
  · intro T t N hN
    obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨?_, hx2⟩, fun y hy => hu y ⟨?_, hy.2⟩⟩
    · rw [← Category.assoc, hx1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← hy.1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Over.comp_left]
    obtain ⟨hp, hs, hc⟩ := hG
    have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩⟩
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine ⟨inferInstance, ?_, MorphismProperty.RespectsIso.postcomp (@GeometricallyConnected : MorphismProperty Scheme.{0}) e.hom.left b.left hc⟩
    have := smoothOfRelativeDimension_comp (n := g) (m := 0) b.left e.hom.left
    simpa using this

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualCon

theorem Rep.baseChange (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S'') (hR : Rep A b P)
    (hpb : IsPullback k b'' b h) : Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  have hP : P.IsLB := hR.fam.isLB
  have hP' : (ev P (fst A B'') (snd A B'' ≫ k)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (y : Y ⟶ B''), evc hP' a y = evc hP a (y ≫ k) := by
    intro Y a y
    rw [evc_ev hP, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (N : LB (A ⊗ T).left) (hN : N.IsLB) (y : T ⟶ B''),
      LBIso N (ev (ev P (fst A B'') (snd A B'' ≫ k)) (fst A T) (snd A T ≫ y)) ↔
        LBIso N (ev P (fst A T) (snd A T ≫ y ≫ k)) := by
    intro T N hN y
    rw [← cls_eq_iff hN (pull_isLB hP' _), ← cls_eq_iff hN (pull_isLB hP _), cls_ev hP', cls_ev hP, key,
      Category.assoc]
  refine ⟨⟨hP', (isAdditive_iff hP').2 fun Y a a' t ↦ ?_⟩, fun T t N hN ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff hP).1 hR.fam.add Y a a' (t ≫ k)
  · obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ h) N hN
    refine ⟨hpb.lift x t hx1, ⟨hpb.lift_snd _ _ _, (iso T N hN.isLB _).2 ?_⟩, fun y ⟨hy1, hy2⟩ ↦ ?_⟩
    · rw [hpb.lift_fst]
      exact hx2
    · have e : y ≫ k = x := hu (y ≫ k) ⟨by rw [Category.assoc, hpb.w, ← Category.assoc, hy1],
        (iso T N hN.isLB y).1 hy2⟩
      exact hpb.hom_ext (by rw [e, hpb.lift_fst]) (by rw [hy1, hpb.lift_snd])

end GlobalTheory.DualCon
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem finAff_sigma : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  intro κ _ B hB F
  classical
  have hfin : ∀ i, {y : B i | Sigma.ι B i y ∈ F}.Finite := fun i =>
    (F.finite_toSet).preimage (Sigma.ι B i).isOpenEmbedding.injective.injOn
  choose V hV hFV using fun i => hB i (hfin i).toFinset
  refine ⟨⨆ i, Sigma.ι B i ''ᵁ V i, IsAffineOpen.iSup_of_disjoint
    (fun i => (hV i).image_of_isOpenImmersion _) fun i j hij => ?_, fun x hx => ?_⟩
  · exact (disjoint_opensRange_sigmaι B i j hij).mono (Scheme.Hom.image_le_opensRange _ _)
      (Scheme.Hom.image_le_opensRange _ _)
  · obtain ⟨i, y, rfl⟩ := (sigmaOpenCover B).exists_eq x
    have hy : y ∈ V i := hFV i y ((Set.Finite.mem_toFinset _).2 hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨y, hy, rfl⟩⟩

end GlobalTheory.DualCon
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lbIso_of_isEmpty {X : Scheme.{0}} [IsEmpty X] (L M : LB X) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have hU : (LB.div M L).U i ⊓ (LB.div M L).U j = ⊥ := by ext x; exact (IsEmpty.false x).elim
  have : Subsingleton Γ(X, (LB.div M L).U i ⊓ (LB.div M L).U j) := by rw [hU]; infer_instance
  exact Subsingleton.elim _ _

theorem hasRepAF_of_isEmpty : ∀ (S : Scheme.{0}) (A S' : Over S) [GrpObj A] (g : ℕ), IsEmpty S'.left →
    HasRepAF A g S' := by
  intro S A S' _ g hS
  have emp : ∀ {Y : Over S} (_ : Y ⟶ S'), IsEmpty Y.left := fun y => ⟨fun p => hS.false (y.left p)⟩
  refine ⟨S', 𝟙 S', LB.triv _, ⟨⟨LB.isLB_triv _, fun Y a a' t => ?_⟩, fun T t N _ => ?_⟩, ?_, ?_⟩
  · have := emp t; exact lbIso_of_isEmpty _ _
  · have := emp (snd A T ≫ t)
    exact ⟨t, ⟨Category.comp_id _, lbIso_of_isEmpty _ _⟩, fun x hx => (Category.comp_id x).symm.trans hx.1⟩
  · rw [Over.id_left]
    refine ⟨inferInstance, ⟨fun x => isEmptyElim x⟩, ⟨?_⟩⟩
    intro K _ y Z fst snd h
    exact isEmptyElim (y (IsLocalRing.closedPoint K))
  · intro F; exact ⟨⊥, isAffineOpen_bot _, fun x _ => isEmptyElim x⟩

end GlobalTheory.DualCon
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

def LiftsAlong {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {U : Over (Sp R)} (M : LB (A ⊗ U).left)
    (B : Type) [CommRing B] (I : Ideal B) : Prop :=
  ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left)
    (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U),
    Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) :
      Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ →
    ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u

end GlobalTheory.DualCon
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

theorem GlobalTheory.EtC.pairingProperties : GlobalTheory.EtC.B1 := by
  intro q J _ _ D c hc n i
  have h := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) J D c hc n
  exact ⟨fun x _ => h.1 x, fun j y _ hy => h.2 j y hy⟩
end
