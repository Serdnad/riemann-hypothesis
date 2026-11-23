module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle144
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

theorem unit_of_val {K S : Type} [Field K] [CommRing S] [Nontrivial S] (f : K →+* S) {u v : Sˣ} {c : K}
    (h : u.val = v.val * f c) : ∃ m : Kˣ, (m : K) = c ∧ u = v * Units.map f.toMonoidHom m := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at h
    exact u.ne_zero h
  exact ⟨Units.mk0 c hc, rfl, Units.ext (by rw [h, Units.val_mul]; rfl)⟩

theorem toStk_surj' {K : Type} [Field K] (z : Sp K) : Function.Surjective (toStk z) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp K).presheaf.germ_exist s
  exact ⟨_, (toStk_valF_gs (𝟙 _) U z hU a).trans (gs_eq _ _ _ hU _)⟩

theorem units_identity {U : Type} [CommGroup U] (gO gB gP gC gCn R M2 M3 M4 M5 : U) :
    (gO⁻¹ * gB * M2) ^ 2 * (gP * gC⁻¹ * gB⁻¹ * gO * M3) ^ 2 * (gCn⁻¹ * gC * M4) *
        (gO * gC⁻¹ * gCn⁻¹ * gO * M5)⁻¹ * (R ^ 2)⁻¹ =
      gP ^ 2 * (gO⁻¹ ^ 2 * (R ^ 2)⁻¹) * (M2 ^ 2 * M3 ^ 2 * M4 * M5⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem sq_cancel {S : Type} [CommRing S] (a b c d f : S) (h : a * c = 1) :
    (a * b) ^ 2 * (c ^ 2 * d * f) = b ^ 2 * (d * f) := by
  linear_combination (a * c + 1) * b ^ 2 * d * f * h

theorem c_zero_eta {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) : D.c 0 = η[D.P.A] := by
  rw [GlobalTheory.Poinc.ThetaOne.c_zero]
  rfl

theorem ev_values : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X)
    (τ₀ : GlobalTheory.UChart.Gens D) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)), (∀ c, b c ^ N₁ = 1) →
    ∀ (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))),
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) →
    ∀ (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)),
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) →
    ∀ (G : X → C → V₁),
      (∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) →
    ∃ Λ : K, ∀ mu c, ∃ r ∈ k₀, ev (G mu c) = Λ * r := by
  intro N₁ hN V₁ _ _ _ hV hunit D X C _ e τ₀ θ hθ b hb t ht χt hχt G hG K _ _ ev k₀ hk₀ W₀ _ ib hB hib
  obtain ⟨B₀, iG, M₀, c₀, τ₁, β, w, hFB⟩ := (fromBase_iff D τ₀ ib).1 hB
  have hM₀ : M₀.IsLB := hFB.2.1
  let z : Sp K := IsLocalRing.closedPoint K
  choose J hJ using fun ψ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J₀ hJ₀ using fun ψ : Sp K ⟶ B₀.left => exists_chart hM₀ (ψ z)
  have gJ : Good D.P.L z J := hJ
  have gJ₀ : Good M₀ z J₀ := hJ₀
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.thetaGenerator_values_scalar_mul_localUnit V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ θ hθ
  set r : Sp K ⟶ Sp V₁ := spMap ev with hr
  set U0 : ((Sp K).presheaf.stalk z)ˣ := (gwx w z J J₀ (r ≫ (D.c 0).left))⁻¹ ^ 2 * (rigV D r z J ^ 2)⁻¹ with hU0
  have hO : r ≫ (η[D.P.A]).left = r ≫ (D.c 0).left := by rw [c_zero_eta]
  have key : ∀ mu c, ∃ q ∈ k₀, toStk z (ev (G mu c)) = toStk z (κ ^ 2 * q) * U0.val := by
    intro mu c
    obtain ⟨hBd, -, hPd, -⟩ := GlobalTheory.T.torsionPoints_projections_defined_over_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib N₁ (by omega)
      (b c) (hb c) (e mu)
    obtain ⟨c1, hc1, e1⟩ := hκ (b c * D.c (e mu)) hPd
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.torsionFrame_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (b c) (hb c) hBd (t c) (ht c)
    obtain ⟨c3, hc3, e3⟩ := GlobalTheory.T.characterValue_mem_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (e mu) (b c) (hb c) hBd (χt mu c) (hχt mu c)
    obtain ⟨c4, hc4, e4⟩ := GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ (e mu)
    obtain ⟨c5, hc5, e5⟩ := GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀
      (e mu) (-e mu)
    have hPP : r ≫ (D.c (e mu) * b c).left = r ≫ (b c * D.c (e mu)).left := by rw [mul_comm]
    have h00 : r ≫ (D.c (e mu + -e mu)).left = r ≫ (D.c 0).left := by rw [add_neg_cancel]
    rw [hO] at e2 e3
    rw [hPP] at e3
    rw [h00] at e5
    obtain ⟨m2, rfl, u2⟩ := unit_of_val (toStk z) e2
    obtain ⟨m3, rfl, u3⟩ := unit_of_val (toStk z) e3
    obtain ⟨m4, rfl, u4⟩ := unit_of_val (toStk z) e4
    obtain ⟨m5, rfl, u5⟩ := unit_of_val (toStk z) e5
    have h1 := hG mu c (Sp K) r z J gJ
    rw [u2, u3, u4, u5, e1, units_identity, ← hU0] at h1
    have hL : gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) = toStk z (ev (G mu c)) := by
      have := GlobalTheory.RatioVal.gs_specMap ev z ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c))
      rw [Iso.inv_hom_id_apply] at this
      exact this
    refine ⟨c1 ^ 2 * ((m2 : K) ^ 2 * (m3 : K) ^ 2 * (m4 : K) * (m5 : K)⁻¹),
      k₀.mul_mem (k₀.pow_mem hc1 2) (k₀.mul_mem (k₀.mul_mem (k₀.mul_mem (k₀.pow_mem hc2 2) (k₀.pow_mem hc3 2)) hc4)
        (k₀.inv_mem hc5)), ?_⟩
    rw [← hL, h1, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
      sq_cancel _ _ _ _ _ (Units.inv_mul _)]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← map_inv, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Units.val_inv_eq_inv_val, map_mul, map_pow]
    ring
  obtain ⟨lam, hlam⟩ := toStk_surj' z U0.val
  refine ⟨κ ^ 2 * lam, fun mu c => ?_⟩
  obtain ⟨q, hq, eq⟩ := key mu c
  refine ⟨q, hq, (toStk z).injective ?_⟩
  rw [eq, ← hlam, ← map_mul]
  congr 1
  ring

end GlobalTheory.USep.EvG
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

set_option autoImplicit false
noncomputable section

def GlobalTheory.HeatSym.derOfFun {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) : Derivation ℤ F F :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' d hadd)) fun x y => by
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
    exact hmul x y

theorem GlobalTheory.HeatSym.derOfFun_apply {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) (x : F) : GlobalTheory.HeatSym.derOfFun d hadd hmul x = d x := rfl

theorem GlobalTheory.HeatSym.vertical_symbol_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Λᵀ = Λ → (∀ r, δ₀ ((algebraMap Ω (FractionRing Ω)) (φ r)) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ b c : FractionRing Ω, GlobalTheory.HeatSym.VS φ t.PP.L x' g k b → GlobalTheory.HeatSym.VS φ t.PP.L x' g k c → GlobalTheory.HeatSym.VS φ t.PP.L x' g (3 * k) ((k : FractionRing Ω) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b))) → Λ = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hloc n v' D Ω _ _ _ φ x' δ dd' hcomp hx' hinv hδ hval
    hsep g hg δL hδL δ₀ Λ hΛ hδ₀ hbr

  obtain ⟨ψ, ξ, hψ, hξ, hξ', hξsep⟩ := GlobalTheory.T.exists_genericPoint_abelianVariety_through_formalPoint E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL
  obtain ⟨v, dd, hinv₂, hval₂⟩ := GlobalTheory.T.generic_fibre_invariant_vectorFields_at_generic_point E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep
  obtain ⟨j₀, q, hj₀, hq, hVS⟩ := GlobalTheory.T.polarisation_value_spaces_generic_point_dictionary E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep

  have hker : ∀ D' : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (∀ r, D' (algebraMap Ω (FractionRing Ω) (φ r)) = 0) → ∀ s, D' (ψ s) = 0 := by
    intro D' hD' s
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective R s
    rw [map_div₀, hψ, hψ, Derivation.leibniz_div, hD', hD']
    simp
  have hδL₀ : ∀ a r, δL a (algebraMap Ω (FractionRing Ω) (φ r)) = 0 := by
    intro a r
    rw [hδL, hδ, map_zero]

  have hadd : ∀ x y : FractionRing Ω,
      (δ₀ (x + y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y)) =
        (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) + (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y) =
        ∑ a, ∑ e, Λ a e * δL a q / q * δL e x + ∑ a, ∑ e, Λ a e * δL a q / q * δL e y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_add (f := _), mul_add]
    rw [map_add (f := _), this]
    ring
  have hmul : ∀ x y : FractionRing Ω,
      (δ₀ (x * y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y)) =
        x * (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) + y * (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y) =
        x * ∑ a, ∑ e, Λ a e * δL a q / q * δL e y + y * ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, this]
    ring
  let δ₁ := GlobalTheory.HeatSym.derOfFun (fun x => δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) hadd hmul
  have hδ₁ : ∀ x, δ₁ x = δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := fun x =>
    GlobalTheory.HeatSym.derOfFun_apply _ hadd hmul x
  have hδ₁ψ : ∀ r, δ₁ (ψ r) = 0 := by
    intro r
    rw [hδ₁, hker δ₀ hδ₀ r]
    simp [hker (δL _) (hδL₀ _) r]
  have : CharZero R := algebraRat.charZero R
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))

  let δL' := fun a : Fin n =>
    GlobalTheory.HeatSym.derOfFun (δL a) (fun x y => map_add _ x y)
      (fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
  have hδL' : ∀ a x, δL' a x = δL a x := fun a x => GlobalTheory.HeatSym.derOfFun_apply _ _ _ x
  have hval₃ : ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL' a (valR ξ O f) := by
    intro a O f h
    rw [hδL']
    exact hval₂ a O f h

  refine GlobalTheory.T.verticalSecondOrderSymbol_vanishes_of_polarisation (FractionRing R) P.A n v dd hinv₂ (FractionRing Ω) ψ ξ hξ hξsep δL' hval₃ j₀ hj₀ δ₁ Λ hΛ
    hδ₁ψ ?_
  intro k hk σ τ
  have hb := (hVS k _ hk).2 ⟨σ, rfl⟩
  have hc := (hVS k _ hk).2 ⟨τ, rfl⟩
  have h3 := hbr k hk _ _ hb hc
  rw [GlobalTheory.T.secondOrderSymbol_bracket_rescale_by_unit_pow Ω n δ₀ δL Λ q _ _ k hq] at h3
  obtain ⟨ρ, hρ⟩ := (hVS (3 * k) _ (by omega)).1 h3
  refine ⟨ρ, ?_⟩
  rintro b c rfl rfl
  simp only [hδ₁, hδL']
  exact mul_left_cancel₀ (pow_ne_zero _ hq) hρ
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensAct

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) [Module O D'.X]
    (o : D'.OAct O) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (i : Fin r) :
    TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) i = ∏ j, TensTor.cmp T ν ν' b j ^ ρ x i j := by
  letI := D.P.isAb.comm
  simp only [TensTor.cmp, GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x i]
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := by simp [Hom.one_def]
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have := map_prod (ν.eA.symm.toMonoidHom.comp P) (fun j => T.pr j ^ ρ x i j) Finset.univ
  simp only [map_zpow] at this
  exact this

end GlobalTheory.Mum.TensAct
namespace GlobalTheory.Mum.TensAct

section V
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem rel_one (hF : TensFacts W φ e wv) : GtRelV W φ e wv 1 1 := by
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W φ e wv hF 1
  have h2 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hF u u 1 1 hu hu
  rw [_root_.mul_one] at h2
  have h3 : u * u = u := GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv hF _ _ _ h2 hu
  rw [_root_.mul_eq_left] at h3
  exact h3 ▸ hu

theorem rel_pow (hF : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) :
    ∀ m : ℕ, GtRelV W φ e wv (v' ^ m) (vs ^ m)
  | 0 => by simpa using rel_one hF
  | m + 1 => by
    rw [_root_.pow_succ, _root_.pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hF _ _ _ _ (rel_pow hF h m) h

end V

theorem io_sum {O : Type} [CommRing O] (N : NumD O) {κ : Type} (s : Finset κ) (m : κ → ℤ) (y : κ → N.X) :
    N.io (∑ j ∈ s, m j • y j) = ∏ j ∈ s, N.io (y j) ^ m j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, N.io_add, ih]
    congr 1
    have := N.ioHom.map_zpow (Multiplicative.ofAdd (y k)) (m k)
    simpa [NumD.ioHom, ← ofAdd_zsmul] using this

def qTH {O : Type} [CommRing O] (N : NumD O) (k : ℕ) : Multiplicative N.X →* N.QT k :=
  MonoidHom.mk' (fun z => N.qTriv k z.toAdd) fun a b => Subtype.ext (Prod.ext
    (by simp [NumD.qTriv, smul_add, ofAdd_add]) (by simp [NumD.qTriv, N.io_add]))

theorem qEq_iff_mk {O : Type} [CommRing O] (N : NumD O) {k : ℕ} (p p' : N.QT k) :
    N.QEq p p' ↔ (p : N.QT k ⧸ (qTH N k).range) = p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [qTH]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    have : N.qTriv k z.toAdd = p⁻¹ * p' := hz
    rw [this, mul_inv_cancel_left]

end GlobalTheory.Mum.TensAct

open GlobalTheory.Mum.TensAct in
theorem GlobalTheory.Mum.TensAct.qkAct_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact g ev hadd hker n hn x a p' q' hp hq
  letI := H.starRing
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  have hB := GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have hB' := GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  beta_reduce at hB hB'
  obtain ⟨q0, qs, hq0, hqs, hrel0⟩ := hp
  obtain ⟨q1, qs1, hq1, hqs1, hrel1⟩ := hq
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).1 o.onB x
  let us : Fin r → N.QT n := fun i => ∏ j, qs j ^ ρ x i j
  let ts : Fin r → N.Gt := fun i => ∏ j, (qs j).1.2 ^ ρ x i j
  have hts : ∀ i, (us i).1.2 = ts i := fun i => by
    show ((MonoidHom.snd _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j) = ∏ j, (qs j).1.2 ^ ρ x i j
    rw [map_prod]
    simp only [map_zpow]
    rfl
  have husy : ∀ i, (us i).1.1.toAdd = ∑ j, ρ x i j • (qs j).1.1.toAdd := fun i => by
    show Multiplicative.toAdd (((MonoidHom.fst _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j)) = _
    rw [map_prod, toAdd_prod]
    simp only [map_zpow, toAdd_zpow]
    rfl
  obtain ⟨w', hw'⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W _ _ _ hF ts
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x q0.1.2.b := by
    apply hF.2.1.1
    funext i
    rw [cmp_actV T ν ν' ρ o hact x _ i, hw'.1 i]
    simp only [ts]
    rw [← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, NumD.projB_apply, hrel0.2.1 j]
  have hros := GlobalTheory.T.rosati_values_tensor_data_matrix_action R hR D D' W T F N N' ν ν' E H ρ hρ o hact x ρ' hρ' q0.1.2 w' (fun j => (qs j).1.2) hrel0.2 hw'

  set y'' : N'.X := ν'.eX.symm (x • p'.y) with hy''
  have hey : ∀ i, TensTor.chi T ν ν' y'' i = (us i).1.1.toAdd := fun i => by
    rw [husy i]
    have h1 : ν'.eX y'' = x • p'.y := by rw [hy'', AddEquiv.apply_symm_apply]

    simp only [TensTor.chi, h1, hact.1 x p'.y i, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hrel0.1 j, ← hq0.1]
    rfl
  have hwn : w' ^ n = N'.io y'' := by
    have hpow := rel_pow hF hw' n
    have hio := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W _ _ _ hF y''
    have e1 : ts ^ n = fun j => N.io (TensTor.chi T ν ν' y'' j) := funext fun i => by
      rw [hey i, husy i, io_sum]
      simp only [Pi.pow_apply, ts, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← (qs j).2]
      rw [← zpow_natCast, ← zpow_natCast ((qs j).1.2), ← zpow_mul, ← zpow_mul, mul_comm]
    rw [e1] at hpow
    exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W _ _ _ hF _ _ _ hpow hio
  let tv : N'.QT n := ⟨(Multiplicative.ofAdd y'', w'), by rw [NumD.mem_QT]; exact hwn⟩
  obtain ⟨t', ht'⟩ := (hB'.2.2.2.2 n).2.1 tv

  have hex : ∀ b, ∃ c, ν.QPt (ev n b) c := fun b => ((hB.2.2.2.2 n).1 (ev n b)).exists
  choose qv hqv using hex
  have huniq : ∀ b c, ν.QPt (ev n b) c → c = qv b := fun b c h =>
    ((hB.2.2.2.2 n).1 (ev n b)).unique h (hqv b)
  have haddv : ∀ b c, N.QEq (qv b * qv c) (qv (b + c)) := fun b c => by
    obtain ⟨q, hqy, hqadd, hqeq⟩ := hadd n hn b c
    obtain ⟨cq, hcq⟩ := ((hB.2.2.2.2 n).1 q).exists
    have e1 : cq = qv b * qv c := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        change ν.eX cq.1.1.toAdd = ν.eX ((qv b).1.1.toAdd + (qv c).1.1.toAdd)
        rw [map_add (f := _), (hqv b).1, (hqv c).1, hcq.1, hqy]
      · exact (hB.2.2.1 _ _ _ _ _ _ (hqv b).2 (hqv c).2 hcq.2).1 hqadd
    rw [← e1]
    exact ((hB.2.2.2.2 n).2.2 q (ev n (b + c)) cq (qv (b + c)) hcq (hqv _)).1 hqeq
  let f : Multiplicative ((Fin g → ℤ) × (Fin g → ℤ)) →* N.QT n ⧸ (qTH N n).range :=
    MonoidHom.mk' (fun b => ((qv b.toAdd : N.QT n) : N.QT n ⧸ (qTH N n).range)) fun b c => by
      rw [toAdd_mul, ← (qEq_iff_mk N _ _).1 (haddv _ _), QuotientGroup.mk_mul]
  have hQi : ∀ i, N.QEq (us i) (qs1 i) := fun i => by
    rw [qEq_iff_mk, huniq _ _ (hqs1 i)]
    have h1 : ((qv (∑ j, ρ x i j • a j) : N.QT n) : N.QT n ⧸ (qTH N n).range) =
        f (Multiplicative.ofAdd (∑ j, ρ x i j • a j)) := rfl
    rw [h1, ofAdd_sum, map_prod]
    simp only [us, QuotientGroup.mk_prod, QuotientGroup.mk_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ofAdd_zsmul, map_zpow, huniq _ _ (hqs j)]
    rfl
  choose z hz1 hz2 using hQi
  obtain ⟨z', hz'⟩ := hF.2.2.2.1.2 z
  let eH : N'.X →+ (Fin r → N.X) := AddMonoidHom.mk' (TensTor.chi T ν ν') fun a b => funext (hF.2.2.1 a b)
  have hQ : N'.QEq tv q1 := by
    refine ⟨z', ?_, ?_⟩
    · apply hF.2.2.2.1.1
      have hs : TensTor.chi T ν ν' (y'' + n • z') = TensTor.chi T ν ν' y'' + n • TensTor.chi T ν ν' z' :=
        (map_add eH _ _).trans (congrArg _ (map_nsmul eH n z'))
      change TensTor.chi T ν ν' q1.1.1.toAdd = TensTor.chi T ν ν' (y'' + n • z')
      rw [hs]
      funext i
      rw [Pi.add_apply, Pi.smul_apply]
      rw [hrel1.1 i, hz1 i, hey i, hz']
    · have hm := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W _ _ _ hF _ _ _ _ hw' (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W _ _ _ hF z')
      have e2 : ts * (fun j => N.io (TensTor.chi T ν ν' z' j)) = fun j => (qs1 j).1.2 := funext fun i => by
        rw [Pi.mul_apply, hz2 i, hts i, hz']
      rw [e2] at hm
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W _ _ _ hF _ _ _ hrel1.2 hm
  refine ⟨t', ?_, ?_, ((hB'.2.2.2.2 n).2.2 t' q' tv q1 ht' hq1).2 hQ⟩
  · rw [← ht'.1]
    exact AddEquiv.apply_symm_apply _ _
  · exact ((GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).2 o x ρ' hρ' p'.g t'.g q0.1.2 w'
      hq0.2 ht'.2).2 ⟨hb, hros⟩
end
end
