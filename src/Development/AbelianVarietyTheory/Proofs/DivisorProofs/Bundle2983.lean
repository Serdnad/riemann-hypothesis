module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle779
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertSpan

open GlobalTheory.Points (le_preimage_mono)

theorem exists_epsPt : ∀ (Z : Scheme.{0}) (W : Z.Opens) (e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W e → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ Z), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ w : Sp (DualNumber S) ⟶ Z, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ ∧ ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (O : Z.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(Z, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := GlobalTheory.T.exists_dualNumberPoint_of_vectorField

theorem exists_coeffs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := GlobalTheory.T.exists_coeffs_tangentVector_translatedBasis

theorem coeffs_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left) (W : t.G.left.Opens), W ≤ t.G.hom ⁻¹ᵁ U.1 → ⊤ ≤ g₀ ⁻¹ᵁ W → ∀ c : Fin n → S, (∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), ∑ a, ρ (c a) * (valR (wt a) O f).snd = 0) → c = 0 := GlobalTheory.T.tangent_basis_translate_coefficients_zero

theorem vert_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (W : t.G.left.Opens) (hW : W ≤ t.G.hom ⁻¹ᵁ U.1) (e : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), IsField W e → (∀ r : Γ(X, U.1), e W ((t.G.hom.appLE U.1 W hW).hom r) = 0) → ∃! c : Fin n → Γ(t.G.left, W), ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)), e O f = ∑ a, resG t.G.left hO (c a) * δ a O f := by
  intro E _ _ _ H X t U n v hv hb δ hδF hδ0 hδv W hW e he he0
  classical
  have hφ : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ W →
      ∃ φ : Γ(X, U.1) →+* S, g ≫ t.G.hom = spMap φ ≫ chart U := fun S _ g hg =>
    ⟨_, (GlobalTheory.Points.specMap_valMap_fromSpec U.2 (g ≫ t.G.hom) (le_preimage_mono g hW hg)).symm⟩
  have hE : ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ c : Fin n → S,
      ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S')
        (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)),
        (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) →
        ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O),
          valR (spMap ρ ≫ g₀) O (e O f) = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
    intro S _ g₀ hg
    obtain ⟨φ, hφg⟩ := hφ S g₀ hg
    obtain ⟨w, hred, hw⟩ := exists_epsPt t.G.left W e he S g₀ hg
    have hwW : ⊤ ≤ w ⁻¹ᵁ W := GlobalTheory.CechKS.le_preimage_of_red hred hg
    have hid : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
    have hid' : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
      have : dualMap (RingHom.id S) = RingHom.id _ := by
        refine RingHom.ext fun z => ?_
        ext <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have hover : w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom := by
      have hU1 : ⊤ ≤ (w ≫ t.G.hom) ⁻¹ᵁ U.1 := le_preimage_mono w hW hwW
      have hU0 : ⊤ ≤ (g₀ ≫ t.G.hom) ⁻¹ᵁ U.1 := le_preimage_mono g₀ hW hg
      have hU2 : ⊤ ≤ (spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom) ⁻¹ᵁ U.1 :=
        fun p _ => hU0 (Set.mem_univ (spMap (algebraMap S (DualNumber S)) p))
      refine GlobalTheory.Points.ext_of_valR U.2 hU1 hU2 fun r => ?_
      rw [← GlobalTheory.Points.valR_appLE w t.G.hom hW hwW r, GlobalTheory.Points.valR_spMap_comp _ _ _ hU0,
        ← GlobalTheory.Points.valR_appLE g₀ t.G.hom hW hg r]
      have h₁ := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom S S S).toRingHom w W hwW
        ((t.G.hom.appLE U.1 W hW).hom r)
      rw [hred] at h₁
      have h₂ := hw S (RingHom.id S) W le_rfl (by rw [hid, Category.id_comp]; exact hg)
        ((t.G.hom.appLE U.1 W hW).hom r)
      rw [hid, hid', Category.id_comp, Category.id_comp, he0, GlobalTheory.Points.valR_zero _ _ hg] at h₂
      ext
      · rw [h₁]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [h₂]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
    obtain ⟨c, hc⟩ := exists_coeffs E H X t U n v hv hb S φ g₀ w hφg hred hover
    exact ⟨c, fun S' _ ρ φ' wt h₁ h₂ O hO hgO f => by
      rw [← hw S' ρ O hO hgO f, hc S' ρ φ' wt h₁ h₂ O hgO f]⟩
  let F : ∀ (S : Type) [CommRing S], (Sp S ⟶ t.G.left) → Fin n → S := fun S _ g =>
    if h : ⊤ ≤ g ⁻¹ᵁ W then (hE S g h).choose else 0
  have hF : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (h : ⊤ ≤ g ⁻¹ᵁ W), F S g = (hE S g h).choose :=
    fun S _ g h => dif_pos h
  have hrel : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W) (φ : Γ(X, U.1) →+* S)
      (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g ≫ t.G.hom = spMap φ ≫ chart U →
      (∀ a, IsTranslate t φ g (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ g ⁻¹ᵁ O →
      ∀ f : Γ(t.G.left, O), valR g O (e O f) = ∑ a, F S g a * (valR (wt a) O f).snd := by
    intro S _ g hg φ wt h₁ h₂ O hO hgO f
    have hid : spMap (RingHom.id S) ≫ g = g := by
      rw [show spMap (RingHom.id S) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    have := (hE S g hg).choose_spec S (RingHom.id S) φ wt (by rw [hid]; exact h₁) (by rw [hid]; exact h₂) O hO
      (by rw [hid]; exact hgO) f
    rw [hid] at this
    rw [this, hF S g hg]
    rfl
  have hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ρ : S →+* S') (g : Sp S ⟶ t.G.left),
      ⊤ ≤ g ⁻¹ᵁ W → F S' (spMap ρ ≫ g) = fun a => ρ (F S g a) := by
    intro S S' _ _ ρ g hg
    have hg' : ⊤ ≤ (spMap ρ ≫ g) ⁻¹ᵁ W := fun p _ => hg (Set.mem_univ (spMap ρ p))
    have hz := coeffs_eq_zero E H X t U n v hv hb S' (spMap ρ ≫ g) W hW hg'
      (fun a => F S' (spMap ρ ≫ g) a - ρ (F S g a)) (fun S'' _ ρ' φ' wt h₁ h₂ O hO hgO f => by
        have hc : spMap (ρ'.comp ρ) ≫ g = spMap ρ' ≫ spMap ρ ≫ g := by
          rw [← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
        have e₁ := (hE S' (spMap ρ ≫ g) hg').choose_spec S'' ρ' φ' wt h₁ h₂ O hO hgO f
        have e₂ := (hE S g hg).choose_spec S'' (ρ'.comp ρ) φ' wt (by rw [hc]; exact h₁) (by rw [hc]; exact h₂) O hO
          (by rw [hc]; exact hgO) f
        rw [hc, ← hF S g hg] at e₂
        rw [← hF S' (spMap ρ ≫ g) hg'] at e₁
        simp only [RingHom.comp_apply] at e₂
        simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
        rw [← e₁, ← e₂, sub_self])
    funext a
    exact sub_eq_zero.1 (congrFun hz a)
  choose cs hcs using fun a => GlobalTheory.LogKSLin.exists_sec W (fun S _ g => F S g a)
    (fun S S' _ _ ρ g hg => congrFun (hnat S S' ρ g hg) a)
  have hval : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (φ : Γ(X, U.1) →+* S)
      (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g ≫ t.G.hom = spMap φ ≫ chart U →
      (∀ a, IsTranslate t φ g (v a) (wt a)) → ∀ (O : t.G.left.Opens) (hO : O ≤ W), ⊤ ≤ g ⁻¹ᵁ O →
      ∀ (c : Fin n → Γ(t.G.left, W)) (f : Γ(t.G.left, O)),
        valR g O (∑ a, resG t.G.left hO (c a) * δ a O f) = ∑ a, valR g W (c a) * (valR (wt a) O f).snd := by
    intro S _ g φ wt hφg hwt O hO hgO c f

    rw [GlobalTheory.Points.valR_eq _ _ hgO, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← GlobalTheory.Points.valR_eq _ _ hgO, GlobalTheory.Points.valR_mul _ _ hgO, GlobalTheory.Points.valR_res _ hO hgO,
      hδv a O (hO.trans hW) f S φ g (wt a) hφg hgO (hwt a)]
  have hex : ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)),
      e O f = ∑ a, resG t.G.left hO (cs a) * δ a O f := by
    intro O hO f
    refine GlobalTheory.CechInv.ext_of_valR O _ _ fun S _ g hg => ?_
    have hgW := le_preimage_mono g hO hg
    obtain ⟨φ, hφg⟩ := hφ S g hgW
    choose wt hwt using fun a => (existsUnique_isTranslate t φ hφg (hv a)).exists
    rw [hrel S g hgW φ wt hφg hwt O hO hg f, hval S g φ wt hφg hwt O hO hg cs f]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcs a S g hgW]
  refine ⟨cs, hex, fun c' hc' => ?_⟩
  have key : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ W →
      (fun a => valR g W (c' a) - valR g W (cs a)) = 0 := by
    intro S _ g hg
    refine coeffs_eq_zero E H X t U n v hv hb S g W hW hg _ fun S' _ ρ φ' wt h₁ h₂ O hO hgO f => ?_
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← GlobalTheory.Points.valR_spMap_comp ρ g W hg]
    rw [← hval S' (spMap ρ ≫ g) φ' wt h₁ h₂ O hO hgO c' f, ← hval S' (spMap ρ ≫ g) φ' wt h₁ h₂ O hO hgO cs f,
      ← hc' O hO f, ← hex O hO f, sub_self]
  funext a
  exact GlobalTheory.CechInv.ext_of_valR W _ _ fun S _ g hg => sub_eq_zero.1 (congrFun (key S g hg) a)

end GlobalTheory.VertSpan
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldBC

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : IsField W₀ d) (h : W₁ ≤ W₀) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h),
    fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

def derivOf {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (V : Z.Opens) (hV : V ≤ W₀) : Derivation ℤ Γ(Z, V) Γ(Z, V) :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' (d V) (hd.1 V hV)))
    (fun a b => by simp [hd.2.1 V hV a b, smul_eq_mul])

theorem exists_field_of_deriv {Z : Scheme.{0}} (V : Z.Opens) (hV : IsAffineOpen V)
    (δ : Derivation ℤ Γ(Z, V) Γ(Z, V)) :
    ∃ e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField V e ∧ ∀ a, e V a = δ a := by
  let σ : Γ(Z, V) →+* DualNumber Γ(Z, V) :=
    { toFun := fun a => TrivSqZeroExt.inl a + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext
        · simp
        · simp [δ.leibniz, smul_eq_mul]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  obtain ⟨d', hd', hd'v⟩ := GlobalTheory.SpecField.exists_isField Γ(Z, V) σ (fun a => by simp [σ])
  exact GlobalTheory.FieldTransport.exists_isField_transport Z V hV (fun a => δ a) d' hd'
    (fun a => by
      refine (hd'v a).trans ?_
      simp only [σ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rfl)

theorem sec_ext {Z : Scheme.{0}} (V : Z.Opens) (s t : Γ(Z, V))
    (h : ∀ x ∈ V, ∃ V' : Z.Opens, ∃ hV' : V' ≤ V, x ∈ V' ∧ resG Z hV' s = resG Z hV' t) : s = t := by
  refine TopCat.Presheaf.section_ext Z.sheaf V s t fun x hx => ?_
  obtain ⟨V', hV', hx', e⟩ := h x hx
  have := congrArg (Z.presheaf.germ V' x hx').hom e
  simp only [resG, TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem appLE_res {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (h : V' ≤ V) (r : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom r) = (f.appLE U V' (h.trans e)).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U U' : Y.Opens) (V : X.Opens) (h : U' ≤ U)
    (e : V ≤ f ⁻¹ᵁ U') (r : Γ(Y, U)) :
    (f.appLE U' V e).hom (resG Y h r) = (f.appLE U V (e.trans (f.preimage_mono h))).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem deriv_eq_zero_of_closure {B : Type} [CommRing B] (Δ : Derivation ℤ B B) (S : Set B)
    (hS : Subring.closure S = ⊤) (h : ∀ x ∈ S, Δ x = 0) (x : B) : Δ x = 0 := by
  have hx : x ∈ Subring.closure S := hS ▸ Subring.mem_top x
  induction hx using Subring.closure_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]
  | mul x y _ _ hx hy => simp [Derivation.leibniz, hx, hy]

theorem exists_field_pullback : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (W : Z.Opens) (hW : W ≤ p ⁻¹ᵁ U.1) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W d → (∀ r, d W ((p.appLE U.1 W hW).hom r) = (p.appLE U.1 W hW).hom (D r)) → ∃ d' : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O), IsField (φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1) d' ∧ (∀ (O' : Z'.Opens) (h' : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ φ ⁻¹ᵁ W → ∀ r, d' O' ((p'.appLE U'.1 O' h').hom r) = (p'.appLE U'.1 O' h').hom (D' r)) ∧ ∀ (O : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O), O ≤ W → O' ≤ p' ⁻¹ᵁ U'.1 → ∀ f, d' O' ((φ.appLE O O' h).hom f) = (φ.appLE O O' h).hom (d O f) := by
  intro Z Z' X X' p p' φ g hpb U U' hU D D' hD' W hW d hd hdD
  classical
  let A := {O : Z.affineOpens // O.1 ≤ W}
  have hOp : ∀ O : A, O.1.1 ≤ p ⁻¹ᵁ U.1 := fun O => O.2.trans hW
  let O' : A → Z'.Opens := fun O => φ ⁻¹ᵁ O.1.1 ⊓ p' ⁻¹ᵁ U'.1
  have hO'aff : ∀ O : A, IsAffineOpen (O' O) := fun O =>
    (GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).1
  have hgen : ∀ O : A, Subring.closure (Set.range (φ.appLE O.1.1 (O' O) inf_le_left).hom ∪
      Set.range (p'.appLE U'.1 (O' O) inf_le_right).hom) = ⊤ := fun O =>
    (GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).2
  let δ : ∀ O : A, Derivation ℤ Γ(Z, O.1.1) Γ(Z, O.1.1) := fun O => derivOf hd O.1.1 O.2
  have hδ : ∀ (O : A) r, δ O ((p.appLE U.1 O.1.1 (hOp O)).hom r) =
      (p.appLE U.1 O.1.1 (hOp O)).hom (D r) := by
    intro O r
    show d O.1.1 _ = _
    rw [← appLE_res p U.1 W O.1.1 hW O.2, hd.2.2 W O.1.1 O.2 le_rfl, hdD, appLE_res]
  choose δ' hδ'1 hδ'2 using fun O : A =>
    GlobalTheory.T.exists_derivation_fibreProduct_affine_compatible Z Z' X X' p p' φ g hpb U U' hU D D' hD' O.1 (hOp O) (δ O) (hδ O)
  choose e he1 he2 using fun O : A => exists_field_of_deriv (O' O) (hO'aff O) (δ' O)

  have hT : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (b : Γ(Z, O.1.1)),
      e O V ((φ.appLE O.1.1 V (hV.trans inf_le_left)).hom b) =
        (φ.appLE O.1.1 V (hV.trans inf_le_left)).hom (d O.1.1 b) := by
    intro O V hV b
    rw [← appLE_res φ O.1.1 (O' O) V inf_le_left hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'2,
      appLE_res]
    rfl
  have hP : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (r : Γ(X', U'.1)),
      e O V ((p'.appLE U'.1 V (hV.trans inf_le_right)).hom r) =
        (p'.appLE U'.1 V (hV.trans inf_le_right)).hom (D' r) := by
    intro O V hV r
    rw [← appLE_res p' U'.1 (O' O) V inf_le_right hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'1,
      appLE_res]

  let bas : (O : A) → Γ(Z, O.1.1) → A := fun O s =>
    ⟨⟨Z.basicOpen s, O.1.2.basicOpen s⟩, (Z.basicOpen_le s).trans O.2⟩
  have hKB : ∀ (O : A) (s : Γ(Z, O.1.1)) (V : Z'.Opens), V ≤ O' (bas O s) → ∀ f,
      e O V f = e (bas O s) V f := by
    intro O s
    have hle : O' (bas O s) ≤ O' O := inf_le_inf_right _ (φ.preimage_mono (Z.basicOpen_le s))
    refine GlobalTheory.T.vectorFields_eq_on_subopens_of_eq_affine Z' (O' (bas O s)) (hO'aff (bas O s)) (e O) (e (bas O s))
      (isField_mono (he1 O) hle) (he1 (bas O s)) ?_
    intro a
    rw [he2 (bas O s)]
    let Δ := derivOf (he1 O) (O' (bas O s)) hle - δ' (bas O s)
    have hΔ : ∀ x, Δ x = e O (O' (bas O s)) x - δ' (bas O s) x := fun x => rfl
    suffices key : ∀ x, Δ x = 0 by
      have := key a
      rwa [hΔ, sub_eq_zero] at this
    refine deriv_eq_zero_of_closure Δ _ (hgen (bas O s)) ?_
    rintro x (⟨c, rfl⟩ | ⟨r, rfl⟩)
    · let ψ := (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
      have hres : ∀ b : Γ(Z, O.1.1), Δ (ψ (resG Z (Z.basicOpen_le s) b)) = 0 := by
        intro b
        rw [hΔ, sub_eq_zero]
        show e O (O' (bas O s)) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b)) = δ' (bas O s) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b))
        rw [hδ'2 (bas O s)]
        show _ = (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom (d (Z.basicOpen s) (resG Z (Z.basicOpen_le s) b))
        rw [res_appLE, hT O _ hle, hd.2.2 O.1.1 (Z.basicOpen s) (Z.basicOpen_le s) O.2, res_appLE]
      haveI := O.1.2.isLocalization_basicOpen s
      obtain ⟨⟨a₀, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) c
      change c * resG Z (Z.basicOpen_le s) m = resG Z (Z.basicOpen_le s) a₀ at hm
      have hunit : IsUnit (ψ (resG Z (Z.basicOpen_le s) m)) := by
        obtain ⟨n, hn⟩ := m.2
        rw [← hn, map_pow]
        exact ((RingedSpace.isUnit_res_basicOpen Z.toRingedSpace s).pow n).map ψ
      have h1 := congrArg (fun y => Δ (ψ y)) hm
      simp only [map_mul, Derivation.leibniz, hres, smul_zero, zero_add, smul_eq_mul, mul_zero] at h1
      exact (hunit.mul_right_eq_zero).1 h1
    · rw [hΔ, sub_eq_zero, hP O _ hle, hδ'1]
  have hcomp : ∀ (O₁ O₂ : A) (V : Z'.Opens), V ≤ O' O₁ → V ≤ O' O₂ → ∀ f, e O₁ V f = e O₂ V f := by
    intro O₁ O₂ V h1 h2 f
    apply sec_ext V
    intro x hx
    have hx1 : φ.base x ∈ O₁.1.1 ⊓ O₂.1.1 := ⟨(h1 hx).1, (h2 hx).1⟩
    obtain ⟨f₁, f₂, hf, hxf⟩ := exists_basicOpen_le_affine_inter O₁.1.2 O₂.1.2 _ hx1
    have hA : bas O₁ f₁ = bas O₂ f₂ := Subtype.ext (Subtype.ext hf)
    have hV1 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₁ f₁) := inf_le_right
    have hV2 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₂ f₂) := le_of_le_of_eq inf_le_right (congrArg O' hA)
    refine ⟨V ⊓ O' (bas O₁ f₁), inf_le_left, ⟨hx, hxf, (h1 hx).2⟩, ?_⟩
    rw [← (he1 O₁).2.2 V _ inf_le_left h1, ← (he1 O₂).2.2 V _ inf_le_left h2,
      hKB O₁ f₁ _ hV1, hKB O₂ f₂ _ hV2]
    exact congrArg (fun B => e B (V ⊓ O' (bas O₁ f₁)) (resG Z' inf_le_left f)) hA
  obtain ⟨d', hd'1, hd'2⟩ := GlobalTheory.T.exists_vectorField_glued_openCover Z' A O' e he1 hcomp
  have hcov : φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1 ≤ ⨆ O : A, O' O := by
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hx.1)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨O₀, hO₀⟩, hle⟩, hx0, hx.2⟩
  refine ⟨d', isField_mono hd'1 hcov, ?_, ?_⟩
  · intro V hV hVW r
    have hVc : V ≤ ⨆ O : A, O' O := (le_inf hVW hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hVW hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      hP B _ inf_le_right]
  · intro O V h hOW hV f
    have hVc : V ≤ ⨆ O : A, O' O :=
      (le_inf (h.trans (φ.preimage_mono hOW)) hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ O from h hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle.trans hOW⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      ← res_appLE φ O O₀ (V ⊓ O' B) hle (inf_le_right.trans inf_le_left) f,
      hT B _ inf_le_right, hd.2.2 O O₀ hle hOW, res_appLE]

end GlobalTheory.FieldBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.relatively_ample_closed_immersion : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  first | (exact @GlobalTheory.KernelRepFinite.isFinite_restrict) | (exact GlobalTheory.KernelRepFinite.isFinite_restrict) | (intros; apply GlobalTheory.KernelRepFinite.isFinite_restrict  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical


theorem _root_.GlobalTheory.T.genericFibre_pulled_semiAbelian_eq_abelianVariety : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (e : Ω →+* FractionRing R₁) (M' : Modif R₁) (h : M'.S ⟶ M.Z), M'.gp ≫ h = spMap e ≫ M.pt → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ α : A₁.A.left ⟶ ((Over.pullback h).obj Z.G).left, IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α ∧ LBIso A₁.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) := by
  first | exact @GlobalTheory.MumGen.genFibre_pullback | exact GlobalTheory.MumGen.genFibre_pullback | (intros; apply GlobalTheory.MumGen.genFibre_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.semiAbelianExtension_abelian_over_open_part : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  first | exact @GlobalTheory.ZH.abLocus_of_over₀ | exact GlobalTheory.ZH.abLocus_of_over₀ | (intros; apply GlobalTheory.ZH.abLocus_of_over₀ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.genericFibre_polarisation_eq_eighthPower_pullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  first | exact @GlobalTheory.Poinc.GenPull.lbIso_gen_pull | exact GlobalTheory.Poinc.GenPull.lbIso_gen_pull | (intros; apply GlobalTheory.Poinc.GenPull.lbIso_gen_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_admissible_projective_theta_model_over_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ∀ M₁ : RatModel o Ω, IsProjOver M₁.s → ∀ (K : Type) [Finite K] (Jk : K → Type) [∀ k, Finite (Jk k)] (t : ∀ k, Jk k → Ω), (∀ k j, t k j ≠ 0) → ∃ (Y : RatModel o Ω) (πY : Y.Z ⟶ M₁.Z) (U₀ : Y.Z.Opens) (EE : Y.Lat S.J) (_ : ZHOut ρ Y U₀ EE), M₁.IsHom Y (AlgHom.id o Ω) πY ∧ IsProper πY ∧ S.admitted Y U₀ ∧ S.IsEE Y U₀ EE ∧ ∀ k, Nonempty (Jk k) → Y.HasDiv (t k) := by
  first | exact @GlobalTheory.Poinc.exists_admissible_projective_theta_model | exact GlobalTheory.Poinc.exists_admissible_projective_theta_model | (intros; apply GlobalTheory.Poinc.exists_admissible_projective_theta_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.genericFibre_uniformisedModelPoint_groupPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  first | exact @GlobalTheory.GenPb.genfib_grpPullback | exact GlobalTheory.GenPb.genfib_grpPullback | (intros; apply GlobalTheory.GenPb.genfib_grpPullback <;> assumption)
end
