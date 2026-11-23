module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Sc Integ IsTrans)
open UpperTheory.Gal.LocalSmoothExtension (qAt al leg cW CxFin StdC)

namespace UpperTheory.Gal.FixZ

private theorem lev_eq {G : Type} [Group G] (K : Subgroup G) (h : G) :
    GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ = G3.lev K h := by
  ext x
  simp only [GlobalTheory.HeckeCorr.heckeLevel, G3.lev, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨hx, ?_⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · rintro ⟨hx, hy⟩
    refine ⟨hx, _, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem ind_eq {G : Type} [Group G] (K : Subgroup G) (g : G) :
    Formalism.UG.dosetInd ℂ K g = G3.ind ℂ K g := by
  rfl

private theorem smooth_iso {A B C : Scheme.{0}} (e : A ≅ B) (s : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n s) : SmoothOfRelativeDimension n (e.hom ≫ s) := by
  haveI := h
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) e.hom s
  rwa [Nat.zero_add] at this

end UpperTheory.Gal.FixZ

open UpperTheory.Gal UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.bridge_of :
    UpperTheory.Gal.FixZ.TrFEt → UpperTheory.Gal.FixZ.AlFEt → UpperTheory.Gal.FixZ.LegOf → UpperTheory.Gal.FixZ.WtEq → UpperTheory.Gal.FixZ.TanIso → UpperTheory.Gal.FixZ.DimUniq → UpperTheory.Gal.FixZ.CxFinOf → UpperTheory.Gal.FixZ.Bridge := by
  intro hTr hAl hLeg hWt hTan hDim hCx h0 hZ p _ D G L hSc gb hStd i₀ v hv k T N' N hdvd d hsm h a b hreg α hα
  have hτ : ∀ i, D.tau i = D.tau i₀ := fun i => by
    have : Subsingleton (Fin D.a) := by rw [hSc.a1]; infer_instance
    rw [Subsingleton.elim i i₀]
  have hAdm : ∀ u ∈ L.KN N'.1, h * u * h⁻¹ ∈ L.KN N.1 := fun u hu => by
    have := b.2 u (by rw [T.K_eq]; exact hu)
    rwa [T.K_eq] at this
  have hLe : L.KN N'.1 ≤ L.KN N.1 := fun u hu => by
    have := a.2 u (by rw [T.K_eq]; exact hu)
    rw [T.K_eq] at this
    simpa using this
  have hLev : W2.LevOk L N.1 N'.1 h := ⟨N.2.1, N.2.2, N'.2.1, N'.2.2, hdvd, hAdm⟩
  obtain ⟨c₁, hc₁, -⟩ := hLeg p D G L gb k T N' N 1 a
  obtain ⟨c₂, -, hc₂'⟩ := hLeg p D G L gb k T N' N h b
  have hc₂ := hc₂' α
  have hregZ : ∀ g, h * g ∈ L.KN N.1 → GlobalTheory.LKCx.RegAf G g := fun g hg => hreg g (by
    have hm : g ∈ DoubleCoset.doubleCoset h⁻¹ (L.KN N.1 : Set G.GAf) (L.KN N.1) :=
      DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, h * g, hg, by simp⟩
    rw [G3.ind, Set.indicator_of_mem hm]
    exact one_ne_zero)
  have heq : ∀ M : Lv p, (T.e M).hom ≫ W2.sZ (T.M M) k = qAt T M := T.e_q
  have hpw : c₁.pw k = (T.e N').inv ≫ T.X.tr _ _ 1 a.1 a.2 ≫ (T.e N).hom := by
    rw [hc₁, Iso.inv_hom_id_assoc]
  have htw : c₂.tw α = (T.e N').inv ≫ leg T N' N h b α ≫ (T.e N).hom := by
    rw [hc₂, Iso.inv_hom_id_assoc]
  have hEt : Etale (c₁.pw k) := by
    haveI := T.X.etale (T.lev N') (T.lev N) a.1 a.2
    rw [hpw]
    infer_instance
  have h₁ : c₁.pw k ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [hpw, Category.assoc, Category.assoc, heq N, T.X.tr_q, Iso.inv_comp_eq]
    exact (heq N').symm
  have h₂ : c₂.tw α ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [htw, Category.assoc, Category.assoc, heq N, LocalSmoothExtension.leg_q, Iso.inv_comp_eq]
    exact (heq N').symm
  obtain ⟨-, -, -, -, -, hfin, hone, -⟩ := h0 p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  obtain ⟨hsm₀, Fx, At, hFx, hAt, hSum⟩ := hZ p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  have hRHS : ∀ y : ℂ, ∑ x ∈ Fx, W2.lefTerm (At x) y =
      (((L.KN N'.1).relIndex (G3.lev (L.KN N.1) h) : ℕ) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (G3.ind ℂ (L.KN N.1) h⁻¹) (LocalSmoothExtension.Kp G) (LocalSmoothExtension.oneP G) := by
    intro y
    rw [hSum y, hWt p D G L hSc.a1 i₀ v hv k α y, lev_eq, ind_eq]
    rfl
  have hFT := hTr p D G L gb k T N' N h b.1 b.2
  have hFA := hAl p D G L gb k T N α (fun s => (hα s).1)
  have hlegF : IsFinite (leg T N' N h b α) := by
    haveI := hFT.1
    haveI := hFA.1
    unfold leg
    infer_instance
  have hlegE : Etale (leg T N' N h b α) := by
    haveI := hFT.2
    haveI := hFA.2
    unfold leg
    infer_instance
  refine ⟨hCx p G v (L.KN N.1) (L.KN N'.1) h hLe hAdm hfin hone, hlegF, hlegE, ?_⟩
  by_cases hne : Nonempty (T.X.Z (T.lev N))
  · have hsm₁ : SmoothOfRelativeDimension (D.n - 1 + k * D.g) (qAt T N) := by
      rw [← heq N]
      exact smooth_iso _ _ _ hsm₀
    have hd : d = D.n - 1 + k * D.g := hDim _ (qAt T N) _ _ hsm hsm₁ hne
    subst hd
    obtain ⟨E, -, hE2, hE3⟩ := hTan _ _ _ _ (qAt T N) (qAt T N') (W2.sZ (T.M N) k) (W2.sZ (T.M N') k) (T.e N) (T.e N')
      (heq N) (heq N') (D.n - 1 + k * D.g) (T.X.tr _ _ 1 a.1 a.2) (leg T N' N h b α) (c₁.pw k) (c₂.tw α)
      (T.X.tr_q _ _ 1 a.1 a.2) (LocalSmoothExtension.leg_q T N' N h b α) h₁ h₂ hc₁ hc₂
    have hmem : ∀ x, x ∈ Fx.map E.symm.toEmbedding ↔ E x ∈ Fx := fun x => by
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
    refine ⟨Fx.map E.symm.toEmbedding, fun x => At (E x), fun x => ?_, fun x hx => ?_, fun y => ?_⟩
    · rw [hmem, hFx, hE2]
    · have := hAt _ ((hmem x).1 hx)
      exact ⟨hE3 x _ this.1, this.2⟩
    · rw [← hRHS y, Finset.sum_map]
      simp
  · have hpt : ∀ _ : Sp ℂ ⟶ T.X.Z (T.lev N'), False := fun x =>
      hne ⟨(x ≫ T.X.tr _ _ 1 a.1 a.2) (IsLocalRing.closedPoint ℂ)⟩
    have hFx0 : Fx = ∅ := Finset.eq_empty_of_forall_notMem fun x _ => hpt (x.1 ≫ (T.e N').inv)
    refine ⟨∅, fun _ => 0, fun x => (hpt x.1).elim, fun x => (hpt x.1).elim, fun y => ?_⟩
    rw [← hRHS y, hFx0, Finset.sum_empty, Finset.sum_empty]

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace UpperTheory.Gal.FixZ

private def secEquiv {Y Y' : Scheme.{0}} {t : Y ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (e : Y ≅ Y')
    (ht : e.hom ≫ t' = t) (V : Y'.Opens) : Sec t' V ≃ₐ[ℂ] Sec t (e.hom ⁻¹ᵁ V) :=
  AlgEquiv.ofBijective
    { appSec t' t e.hom V with
      commutes' := fun r => (semiHom_appSec ht V).map_algebraMap r }
    (ConcreteCategory.bijective_of_isIso (e.hom.app V))

private theorem eq_self_of_fix_D_of_linear_kaehler {A : Type} [CommRing A] [Algebra ℂ A] (g : Ω[A⁄ℂ] →ₗ[ℂ] Ω[A⁄ℂ])
    (hD : ∀ a, g (D ℂ A a) = D ℂ A a) (hs : ∀ (a : A) (ω : Ω[A⁄ℂ]), g (a • ω) = a • g ω)
    (ω : Ω[A⁄ℂ]) : g ω = ω := by
  have hω : ω ∈ Submodule.span A (Set.range (D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hD a
  | zero => exact map_zero g
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [hs, hx]

private theorem exists_kaehler_map_D_of_algHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] →ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : SMulCommClass ℂ A B := ⟨fun r a b => by
    change r • (f a * b) = f a * (r • b)
    rw [mul_smul_comm]⟩
  refine ⟨(KaehlerDifferential.map ℂ ℂ A B).restrictScalars ℂ, fun a => ?_, fun a ω => ?_⟩
  · exact KaehlerDifferential.map_D ℂ ℂ A B a
  · rw [LinearMap.restrictScalars_apply, LinearMap.map_smul, ← algebraMap_smul (A := B) a]
    rfl

private theorem exists_kaehler_equiv_D_of_algEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A ≃ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] ≃ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  obtain ⟨Ψ, h1, h2⟩ := exists_kaehler_map_D_of_algHom (f : A →ₐ[ℂ] B)
  obtain ⟨Φ, g1, g2⟩ := exists_kaehler_map_D_of_algHom (f.symm : B →ₐ[ℂ] A)
  have l : ∀ ω, Φ (Ψ ω) = ω := eq_self_of_fix_D_of_linear_kaehler (Φ ∘ₗ Ψ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  have r : ∀ η, Ψ (Φ η) = η := eq_self_of_fix_D_of_linear_kaehler (Ψ ∘ₗ Φ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  exact ⟨LinearEquiv.ofLinear Ψ Φ (LinearMap.ext r) (LinearMap.ext l), h1, h2⟩

private theorem valR_comp_eq_valR_app {X W : Scheme} (x : Sp ℂ ⟶ X) (f : X ⟶ W) (V : W.Opens)
    (g : Γ(W, V)) :
    valR (x ≫ f) V g = valR x (f ⁻¹ᵁ V) (f.app V g) := by
  unfold valR
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dite_eq_left h', dite_eq_left h]
    simp [Scheme.Hom.comp_appLE]
  · have h' : ¬ ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dite_eq_right h', dite_eq_right h]

private theorem preimage_le_preimage_preimage_of_comm_iso {Y Y' Z Z' : Scheme} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z)
    (c' : Y' ⟶ Z') (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens)
    (h : V' ≤ c' ⁻¹ᵁ U') : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U' := by
  rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage]
  exact fun p hp => h hp

private theorem appSec_res_appSec_eq_of_comm_iso {Y Y' Z Z' : Scheme} {s : Z ⟶ Sp ℂ} {t : Y ⟶ Sp ℂ}
    {s' : Z' ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z) (c' : Y' ⟶ Z')
    (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens) (hV' : V' ≤ c' ⁻¹ᵁ U')
    (hV : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U') (τ : Sec s' U') :
    appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) := by
  have key : ∀ (g₁ g₂ : Y ⟶ Z') (_ : g₁ = g₂) (W : Y.Opens) (e₁ : W ≤ g₁ ⁻¹ᵁ U')
      (e₂ : W ≤ g₂ ⁻¹ᵁ U'), g₁.appLE U' W e₁ = g₂.appLE U' W e₂ := by
    rintro _ _ rfl _ _ _; rfl
  have e1 : eY.hom ⁻¹ᵁ V' ≤ (eY.hom ≫ c') ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact fun p hp => hV' hp
  have e2 : eY.hom ⁻¹ᵁ V' ≤ (c ≫ eZ.hom) ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact hV
  have L : appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      (eY.hom ≫ c').appLE U' _ e1 τ := by
    change eY.hom.app V' (Y'.presheaf.map (homOfLE hV').op (c'.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE]
    simp only [CommRingCat.comp_apply]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have R : Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) =
      (c ≫ eZ.hom).appLE U' _ e2 τ := by
    change Y.presheaf.map (homOfLE hV).op (c.app _ (eZ.hom.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [L, R, key _ _ hc.symm]

theorem tanIso_of :
    UpperTheory.Gal.FixZ.TanIso := by
  intro Z Y Z' Y' s t s' t' eZ eY hs ht d c₁ c₂ c₁' c₂' h₁ h₂ h₁' h₂' hc₁ hc₂
  refine ⟨?E, ?_⟩
  case E =>
    unfold CxPts Points.PtsOver
    exact
      { toFun := fun x => ⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩
        invFun := fun y => ⟨y.1 ≫ eY.inv, by rw [Category.assoc, ← ht, eY.inv_hom_id_assoc]; exact y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  refine ⟨fun x => rfl, fun x => ?_, fun x A hT => ?_⟩
  · change x.1 ≫ c₁ = x.1 ≫ c₂ ↔ (x.1 ≫ eY.hom) ≫ c₁' = (x.1 ≫ eY.hom) ≫ c₂'
    rw [Category.assoc, Category.assoc, ← hc₁, ← hc₂, ← Category.assoc, ← Category.assoc x.1,
      cancel_mono]
  · obtain ⟨U', V', hV1', hV2', τ, hx, hU', hV', φ', hsm, hd1, hd2, hker⟩ := hT
    set σ := secEquiv eY ht V' with hσ
    have hσa : ∀ g, σ g = appSec t' t eY.hom V' g := fun g => rfl
    have EV : ∀ g : Sec t' V', CxPts.ev t' (RingHom.id ℂ) V' g
        (⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩ : CxPts t' (RingHom.id ℂ)) =
        CxPts.ev t (RingHom.id ℂ) (eY.hom ⁻¹ᵁ V') (σ g) x := fun g =>
      valR_comp_eq_valR_app x.1 eY.hom V' g
    obtain ⟨Ψ, hΨD, hΨs⟩ := exists_kaehler_equiv_D_of_algEquiv σ.symm
    have hW1 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1'
    have hW2 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2'
    have q1 : ∀ l, σ.symm (Sec.res t hW1 (appSec s t c₁ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV1' (appSec s' t' c₁' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1' hW1 (τ l)])
    have q2 : ∀ l, σ.symm (Sec.res t hW2 (appSec s t c₂ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV2' (appSec s' t' c₂' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2' hW2 (τ l)])
    refine ⟨eZ.hom ⁻¹ᵁ U', eY.hom ⁻¹ᵁ V', hW1, hW2, fun l => appSec s' s eZ.hom U' (τ l), hx,
      hU'.preimage_of_isIso eZ.hom, hV'.preimage_of_isIso eY.hom, φ' ∘ₗ Ψ.toLinearMap,
      ?_, ?_, ?_, ?_⟩
    · intro b ω
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨs, hsm]
      erw [EV]
      rw [AlgEquiv.apply_symm_apply]
    · intro l
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q1]
      exact hd1 l
    · intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q2]
      exact hd2 j
    · intro ω hω
      obtain ⟨m, b, ω', hb, hsum⟩ := hker (Ψ ω) hω
      refine ⟨m, fun i => σ (b i), fun i => Ψ.symm (ω' i), fun i => ?_, ?_⟩
      · rw [← EV]; exact hb i
      · apply Ψ.injective

        rw [hsum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hΨs, AlgEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

end UpperTheory.Gal.FixZ

end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace UpperTheory.Gal.FixZ

private theorem act_nat {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) (n : ℕ) :
    act.act (n : O) = (𝟙 A) ^ n := by
  induction n with
  | zero => simp [KS.Model.act_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, _root_.pow_succ]

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hf _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [hf 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i (fun j hj => hf _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  change (Pi.lift (fun i => (List.ofFn fun j => GlobalTheory.KS.pr A j ≫
    act.act (if i = j then d i else 0)).prod)) ≫ GlobalTheory.KS.pr A i = _
  rw [Pi.lift_comp_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Ne.symm hj, KS.Model.act_zero, comp_one]

end UpperTheory.Gal.FixZ

open UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.alFEt_of :
    UpperTheory.Gal.G3.IsogFEt → UpperTheory.Gal.FixZ.PowFEt → UpperTheory.Gal.FixZ.AlFEt := by
  intro hIsog hPow p _ D G L gb k T N α hα
  have hc : ∀ a : 𝓞 D.toG.F, a ≠ 0 → ∃ b : 𝓞 D.toG.F, ∃ d : ℕ, 0 < d ∧ a * b = (d : 𝓞 D.toG.F) := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨b, Ideal.absNorm (Ideal.span {a}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ha
    · rw [← hb, mul_comm]
  set U := (T.M N).univ with hU
  letI := U.grp
  letI := U.comm
  have key : ∀ x y : 𝓞 D.toG.F, ∀ d : ℕ, x * y = d →
      U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O y) ≫ U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O x)
        = 𝟙 U.A ^ d := by
    intro x y d h
    rw [← U.act.mul, ← map_mul, h, map_natCast, act_nat]
  have hf : ∀ s : Fin k, IsFinite (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Etale (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Surjective (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) := by
    intro s
    obtain ⟨b, d, hd, hab⟩ := hc (α s) (hα s)
    have e1 := key b (α s) d ((mul_comm b (α s)).trans hab)
    have e2 := key (α s) b d hab
    exact hIsog ℂ (T.M N).X (T.M N).s U.A U.A U.ab U.ab _ _ d hd (U.act.hom _) (U.act.hom _) e1 e2
  have hg := hPow _ U.A k (fun s => U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s))) hf
    (KS.matEnd U.act (LocalSmoothExtension.diagO D α)) (fun i => matEnd_diagonal_pr U.act _ i)
  obtain ⟨h1, h2, -⟩ := hg
  show IsFinite ((T.e N).hom ≫ _ ≫ (T.e N).inv) ∧ Etale ((T.e N).hom ≫ _ ≫ (T.e N).inv)
  exact ⟨inferInstance, inferInstance⟩

end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Sc Integ IsTrans)

namespace UpperTheory.Gal.FixZ

private theorem powMap_scal {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (d k : ℕ) (Φ : A.left ⟶ A.left)
    (hw : Φ ≫ A.hom = A.hom ≫ 𝟙 S) (h : Φ = ((𝟙 A) ^ d).left) :
    GlobalTheory.KS.powMap (𝟙 S) Φ hw k = (Limits.Pi.map (fun _ : Fin k => (𝟙 A) ^ d)).left := by
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [GlobalTheory.KS.PowPB.powMap_w, Over.w, Category.comp_id]
  · intro i
    rw [GlobalTheory.KS.PowPB.powMap_pr, h, ← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold KS.pr
    simp

end UpperTheory.Gal.FixZ

theorem UpperTheory.Gal.FixZ.trScal_of :
    UpperTheory.Gal.G3.WitUniq → UpperTheory.Gal.G3.IsogFEt → UpperTheory.Gal.FixZ.WitScal → UpperTheory.Gal.FixZ.PowFEt → UpperTheory.Gal.FixZ.TrScal := by
  intro hWU hIso hWS hPow p _ D G L gb k T N d z hd hdp hsc a b
  obtain ⟨π, o, ψ, φ, hw, hπ, htr, heq⟩ := T.tr_eq N N z a b
  have hI : Integ L z := (T.Δ_eq z).1 a
  have hA : UpperTheory.Gal.G3.AdmK L N.1 N.1 z := by
    intro u hu
    have hb := b u (by rw [T.K_eq]; exact hu)
    rwa [T.K_eq] at hb
  obtain ⟨rfl, hΦ⟩ := hWU p D G L ℂ gb N N (T.M N) (T.M N) z hI hA π (Over.Hom.left ψ ≫ φ.φ) (𝟙 _)
    (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ⟨hπ, o, ψ, φ, htr, rfl⟩ (hWS p D G L gb N (T.M N) d z hd hdp hsc)
  have hpm := GlobalTheory.DrinLev.HT.MulModel.isMonHom_id_pow (T.M N).univ.A d
  have hS := powMap_scal (T.M N).univ.A d k _ hw hΦ
  rw [hS] at heq
  have hfe : IsFinite (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ∧ Etale (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ∧
      Surjective (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) := by
    refine hIso ℂ _ (T.M N).s _ _ (T.M N).univ.ab (T.M N).univ.ab (𝟙 _ ^ d) (𝟙 _ ^ d) (d * d)
      (Nat.mul_pos hd hd) hpm hpm ?_ ?_
    · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
    · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  obtain ⟨hf1, hf2, -⟩ := hPow _ (T.M N).univ.A k (fun _ => 𝟙 _ ^ d) (fun _ => hfe)
    (Limits.Pi.map (fun _ : Fin k => 𝟙 (T.M N).univ.A ^ d)) (fun i => by unfold KS.pr; simp)
  have htr' : T.X.tr (T.lev N) (T.lev N) z a b =
      (T.e N).hom ≫ Over.Hom.left (Limits.Pi.map (fun _ : Fin k => 𝟙 (T.M N).univ.A ^ d)) ≫ (T.e N).inv := by
    rw [← Category.assoc, ← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [htr']
  constructor
  · infer_instance
  · infer_instance
end
end
