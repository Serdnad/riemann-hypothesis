module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamData
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle009
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

open Formalism.L2.Pj

section Induce

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

end Induce

theorem vLa_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (p : K) := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hp
  have h2 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) ≠ 0 := by
    rw [Ne, map_eq_zero, map_natCast]
    exact_mod_cast hp0
  have hlog := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at hlog
  unfold vLa
  rw [show ((p : K)) = algebraMap (𝓞 K) K (p : 𝓞 K) from (map_natCast _ _).symm]
  omega

section Host

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

end Host

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB Pf.ERam

theorem dual_int {E : Type} [Field E] [NumberField E] (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) :
    ∀ i : Fin (nI E), IsIntegral ℤ ((δ : E) * omDF (E := E) i) := by
  set ω := RingOfIntegers.basis E
  set bq := integralBasis E
  have hbqω : ∀ i, bq i = algebraMap (𝓞 E) E (ω i) := fun i => integralBasis_apply E i
  have h := _root_.dual_difference E _ bq (fun i => by rw [hbqω]; exact RingOfIntegers.isIntegral_coe _) (fun x => by
      refine ⟨fun i => ω.repr x i, ?_⟩
      have h1 := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)

      rw [map_sum] at h1
      show algebraMap (𝓞 E) E x = _
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbqω, map_zsmul, Int.cast_smul_eq_zsmul]) _ hδ
  intro i
  exact h _

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace Pf.EigA

theorem idem_data {E : Type} [Field E] [NumberField E] {k V : Type} [Field k] [CommRing V] [Algebra V k]
    (ψ : E →+* k) (hint : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (algebraMap (𝓞 E) E x)) (w : V)
    (hw : algebraMap V k w * (((discr E).natAbs : ℕ) : k) = 1) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (c : Fin n → V),
      (∑ i, algebraMap V k (c i) * ψ (algebraMap (𝓞 E) E (b i)) = 1) ∧
      ∀ a : 𝓞 E, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap V k (c i) = ψ (algebraMap (𝓞 E) E a) * algebraMap V k (c j) := by
  classical
  obtain ⟨b, c, h1, h2⟩ := idem_data_basis ψ hint w hw
  set eq := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  refine ⟨_, fun i => b (eq.symm i), fun i => c (eq.symm i), ?_, fun a => ?_⟩
  · rw [Equiv.sum_comp eq.symm (fun x => algebraMap V k (c x) * ψ (algebraMap (𝓞 E) E (b x)))]
    exact h1
  · obtain ⟨m, hm1, hm2⟩ := h2 a
    refine ⟨fun i j => m (eq.symm i) (eq.symm j), fun i => ?_, fun j => ?_⟩
    · rw [hm1, ← Equiv.sum_comp eq.symm (fun x => m (eq.symm i) x • b x)]
    · rw [Equiv.sum_comp eq.symm (fun x => (m x (eq.symm j) : k) * algebraMap V k (c x))]
      exact hm2 _

end Pf.EigA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section LC

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

private lemma valprod_lemma {R : Type} [CommRing R] (φ : R →+* ℂ) (u : K → Rˣ) (ε : K → ℤ) :
    φ ↑(∏ k, u k ^ ε k) = ∏ k, φ ↑(u k) ^ ε k := by
  have key : ∀ x : Rˣ, φ ↑x = ((Units.map φ.toMonoidHom x : ℂˣ) : ℂ) := fun _ => rfl
  rw [key, map_prod, Units.coe_prod]
  simp only [map_zpow, Units.val_zpow_eq_zpow_val, key]

theorem vtf_val_prodU (p : Sp ℂ ⟶ Y) {V : Y.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : K → Γ(Y, V)ˣ) (ε : K → ℤ) :
    valAt' p V (∏ k, u k ^ ε k).val = ∏ k, valAt' p V (u k).val ^ ε k := by
  simp only [valAt', dif_pos h]
  unfold valAt
  simp only [← RingHom.comp_apply]
  exact valprod_lemma _ u ε

theorem vtf_val_lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  calc valAt' p _ ((LB.LinComb L φ ε).g j j').val
      = valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))) ^ ε k).val := rfl
    _ = ∏ k, valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))).val ^ ε k := vtf_val_prodU p h _ ε
    _ = _ := Finset.prod_congr rfl fun k _ => by
        exact congrArg (· ^ ε k) ((vtf_val_res (U := φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) p _ h _).trans
          (vtf_val_pullU p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))))

theorem vtf_isGen_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Sp ℂ ⟶ Y) (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ (t.s j).val =
      (∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' p _ (t.s j').val := by
  have h' : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') := h
  calc valAt' p _ (t.s j).val
      = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          (res (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j)).val :=
        (vtf_val_res p _ h' _).symm
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          ((LB.LinComb L φ ε).g j j' *
            res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [ht j j']
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') ((LB.LinComb L φ ε).g j j').val *
          valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
            (res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [Units.val_mul, valAt'_mul]
    _ = _ := by rw [vtf_val_lcg L φ ε p j j' h, vtf_val_res p _ h']

end LC

section Liou

variable {g : ℕ}

end Liou

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem valAt'_eqToHom_lemma {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {U U' : Y.Opens} (h : U = U')
    (f : Γ(Y, U')) : valAt' x U (Y.presheaf.map (eqToHom h).op f) = valAt' x U' f := by
  subst h
  simp

theorem valAt'_fromSpec {Y : Scheme.{0}} {Vo : Y.Opens} (hV : IsAffineOpen Vo) (l : Sp ℂ ⟶ Spec Γ(Y, Vo))
    (a : Γ(Y, Vo)) : valAt' (l ≫ hV.fromSpec) Vo a = valAt' l ⊤ ((Scheme.ΓSpecIso Γ(Y, Vo)).inv a) := by
  rw [← valAt'_comp, IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
  exact valAt'_eqToHom_lemma l hV.fromSpec_preimage_self _

private theorem pt_lemma_2 (a b : PrimeSpectrum ℂ) : a = b := by
  have h : ∀ c : PrimeSpectrum ℂ, c.asIdeal = ⊥ := fun c =>
    (Ideal.eq_bot_or_top c.asIdeal).resolve_right c.2.ne_top
  exact PrimeSpectrum.ext (by rw [h a, h b])

private theorem top_le_lemma_3 {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (W : Y.Opens) (q : Sp ℂ)
    (h : x q ∈ W) : ⊤ ≤ x ⁻¹ᵁ W := by
  intro q' _
  have hq : q' = q := pt_lemma_2 q' q
  rw [hq]
  exact h

theorem holPair (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (n : ℕ) (B : Set (Fin n → ℂ))
    (e₁ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₂)) (he : ∀ b, e₁ b ≫ p₁ = e₂ b ≫ p₂) :
    IsOpen B → IsHolTo B e₁ → IsHolTo B e₂ → IsHolTo B (fun b => pullback.lift (e₁ b) (e₂ b) (he b)) := by
  classical
  intro _ h₁ h₂
  apply isHolTo_of_local
  intro U f b₀ hb₀ hU
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ

  obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X))
    (show (e₁ b₀ ≫ p₁) q ∈ (⊤ : X.Opens) from trivial)
  have hxW₂ : (e₂ b₀ ≫ p₂) q ∈ W := by rw [← he b₀]; exact hxW
  rw [Scheme.Hom.comp_apply] at hxW hxW₂
  obtain ⟨W₁, hW₁, hx₁, hW₁le⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y₁))
    (show e₁ b₀ q ∈ p₁ ⁻¹ᵁ W from hxW)
  obtain ⟨W₂, hW₂, hx₂, hW₂le⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y₂))
    (show e₂ b₀ q ∈ p₂ ⁻¹ᵁ W from hxW₂)
  have hW' : IsAffineOpen W := hW
  have hW₁' : IsAffineOpen W₁ := hW₁
  have hW₂' : IsAffineOpen W₂ := hW₂
  let N : Set (Fin n → ℂ) := {b ∈ B | ⊤ ≤ e₁ b ⁻¹ᵁ W₁} ∩ {b ∈ B | ⊤ ≤ e₂ b ⁻¹ᵁ W₂}
  have hN : IsOpen N := (h₁ W₁ 0).1.inter (h₂ W₂ 0).1
  have hb₀N : b₀ ∈ N := ⟨⟨hb₀, top_le_lemma_3 _ _ q hx₁⟩, ⟨hb₀, top_le_lemma_3 _ _ q hx₂⟩⟩

  have hr₁ : ∀ b ∈ N, Set.range (e₁ b) ⊆ Set.range hW₁'.fromSpec := by
    intro b hb
    rw [hW₁'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    exact hb.1.2 (show q' ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hr₂ : ∀ b ∈ N, Set.range (e₂ b) ⊆ Set.range hW₂'.fromSpec := by
    intro b hb
    rw [hW₂'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    exact hb.2.2 (show q' ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  let l₁ : ∀ b ∈ N, Sp ℂ ⟶ Spec Γ(Y₁, W₁) := fun b hb => IsOpenImmersion.lift hW₁'.fromSpec (e₁ b) (hr₁ b hb)
  let l₂ : ∀ b ∈ N, Sp ℂ ⟶ Spec Γ(Y₂, W₂) := fun b hb => IsOpenImmersion.lift hW₂'.fromSpec (e₂ b) (hr₂ b hb)
  have hl₁ : ∀ b (hb : b ∈ N), l₁ b hb ≫ hW₁'.fromSpec = e₁ b := fun b hb => IsOpenImmersion.lift_fac _ _ _
  have hl₂ : ∀ b (hb : b ∈ N), l₂ b hb ≫ hW₂'.fromSpec = e₂ b := fun b hb => IsOpenImmersion.lift_fac _ _ _
  letI : Algebra Γ(X, W) Γ(Y₁, W₁) := (p₁.appLE W W₁ hW₁le).hom.toAlgebra
  letI : Algebra Γ(X, W) Γ(Y₂, W₂) := (p₂.appLE W W₂ hW₂le).hom.toAlgebra
  have c₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))) ≫ hW'.fromSpec = hW₁'.fromSpec ≫ p₁ :=
    IsAffineOpen.SpecMap_appLE_fromSpec p₁ hW' hW₁' hW₁le
  have c₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂))) ≫ hW'.fromSpec = hW₂'.fromSpec ≫ p₂ :=
    IsAffineOpen.SpecMap_appLE_fromSpec p₂ hW' hW₂' hW₂le
  have hc : ∀ b (hb : b ∈ N), l₁ b hb ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))) =
      l₂ b hb ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂))) := by
    intro b hb
    rw [← cancel_mono hW'.fromSpec, Category.assoc, Category.assoc, c₁, c₂, ← Category.assoc, ← Category.assoc, hl₁ b hb, hl₂ b hb, he]
  let φ := pullback.map _ _ p₁ p₂ hW₁'.fromSpec hW₂'.fromSpec hW'.fromSpec c₁ c₂
  let wN : ∀ b ∈ N, Sp ℂ ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂)))) :=
    fun b hb => pullback.lift (l₁ b hb) (l₂ b hb) (hc b hb)
  let w := fun b => if hb : b ∈ N then wN b hb else wN b₀ hb₀N
  have hw : ∀ b (hb : b ∈ N), w b = wN b hb := fun b hb => dif_pos hb
  have hwφ : ∀ b ∈ N, w b ≫ φ = pullback.lift (e₁ b) (e₂ b) (he b) := by
    intro b hb
    rw [hw b hb]
    apply pullback.hom_ext
    · simp only [φ, wN, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
      exact hl₁ b hb
    · simp only [φ, wN, Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc]
      exact hl₂ b hb
  have hwhol : IsHolTo N w := by
    refine isHolTo_pullbackSpec hN w (fun a => ?_) (fun c => ?_)
    · refine ((h₁ W₁ a).2.mono (fun b (hb : b ∈ N) => hb.1)).congr (fun b hb => ?_)
      have h := valAt'_fromSpec hW₁' (l₁ b hb) a
      rw [hl₁ b hb] at h
      rw [hw b hb]
      simp only [wN, pullback.lift_fst]
      exact h.symm
    · refine ((h₂ W₂ c).2.mono (fun b (hb : b ∈ N) => hb.2)).congr (fun b hb => ?_)
      have h := valAt'_fromSpec hW₂' (l₂ b hb) c
      rw [hl₂ b hb] at h
      rw [hw b hb]
      simp only [wN, pullback.lift_snd]
      exact h.symm
  obtain ⟨ho, hdf⟩ := isHolTo_comp hwhol φ U f
  refine ⟨{b ∈ N | ⊤ ≤ (w b ≫ φ) ⁻¹ᵁ U}, ho.mem_nhds ⟨hb₀N, by show ⊤ ≤ (w b₀ ≫ φ) ⁻¹ᵁ U; rw [hwφ b₀ hb₀N]; exact hU⟩,
    fun b hb => ⟨hb.1.1.1, by rw [← hwφ b hb.1]; exact hb.2⟩, hdf.congr fun b hb => ?_⟩
  simp only [hwφ b hb.1]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

namespace ThetaHol

theorem isHolTo_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) :
    IsHolTo (Set.univ : Set V) (fun _ => y) := by
  intro Uo f
  by_cases h : ⊤ ≤ y ⁻¹ᵁ Uo
  · simp only [Set.mem_univ, true_and, h, Set.ofPred_true]
    exact ⟨isOpen_univ, differentiableOn_const _⟩
  · simp only [Set.mem_univ, true_and, h, Set.ofPred_false]
    exact ⟨isOpen_empty, differentiableOn_empty⟩

end ThetaHol

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem rig_pmaps {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ))
    (h : RigIso m w) :
    PMaps w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  (maps_iff w _ _ _ t'.PP.rig t.PP.rig m.cm.e (m.cm.rigPull t.PP.L t.PP.rig)
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 h.2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma neg_log_epStar (M f w k0 : ℝ) (hM : 0 < M) (hfw : 0 < f * w + 2) (hk0 : 0 < k0) (hk0' : k0 ≤ 2) :
    -Real.log (epStar M f w k0) ≤ max 0 (Real.log M + Real.log (f * w + 2) + Real.log 2) := by
  unfold epStar
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < M * (f * w + 2) * k0 * Real.log 2 := by positivity
  rcases le_total 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2)) with hq | hq
  · rw [min_eq_left hq, Real.log_one]; simp
  · rw [min_eq_right hq, Real.log_div Real.pi_pos.ne' hden.ne', Real.log_mul (by positivity) hl2.ne',
      Real.log_mul (by positivity) hk0.ne', Real.log_mul hM.ne' hfw.ne']
    have h1 : Real.log k0 ≤ Real.log 2 := Real.log_le_log hk0 hk0'
    have h2 : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hl2.le (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith)
    have h3 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have h4 := le_max_right 0 (Real.log M + Real.log (f * w + 2) + Real.log 2)
    linarith

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row
end
end
