module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle311
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KummerLoc

noncomputable abbrev gU (R : Type) [CommRing R] : Rˣ →* (Γ(Spec (CommRingCat.of R), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom

theorem pull_spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    {q : ℕ} {n i : ℤ} (x : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp φ)) _ _ x = pull _ (spMap ψ) _ _ (pull _ (spMap φ) _ _ x) := by
  rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp]; rfl

theorem pull_kum_gU (hnat : DivisorNaturality) (q : ℕ) [NeZero q] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hq : IsUnit (q : R)) (v : Rˣ) :
    pull _ (spMap φ) _ _ (kum q (gU R v)) = kum q (gU S (Units.map φ.toMonoidHom v)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rw [(hnat q).2.2.2 _ _ hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom (v : R)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simpa using h2.symm



theorem exists_kummer_on_finer_nbhd : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  intro q _ k B _ _ _ _ _ _ hq f _ A' _ _ hA' w
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hqA : IsUnit (q : A') := by simpa using hqB.map (algebraMap B A')
  haveI : Algebra.Etale B A' := hA'.1
  set SB : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
    (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hSB
  set M : Submonoid A' := Algebra.algebraMapSubmonoid A' SB with hM
  have hfM : (algebraMap B A' f) ∈ M := ⟨f, Submonoid.mem_sup_right (Submonoid.mem_powers f), rfl⟩
  let φf : Localization.Away (algebraMap B A' f) →+* Localization M :=
    IsLocalization.Away.lift (algebraMap B A' f) (IsLocalization.map_units (Localization M) (⟨(algebraMap B A' f), hfM⟩ : M))
  have hφf : φf.comp (algebraMap A' _) = algebraMap A' (Localization M) := IsLocalization.Away.lift_comp _ _
  haveI := GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo B f A'
  have hqL : IsUnit (q : Localization M) := by simpa using hqA.map (algebraMap A' (Localization M))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (Localization M) hqL (fun c _ => Subsingleton.elim _ _) (pull _ (spMap φf) _ _ w)
  let u₀ : (Localization M)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization M))).hom.hom.toMonoidHom u
  have hu₀ : gU _ u₀ = u := by ext; simp [u₀]
  obtain ⟨m₀, hm₀, v, hv⟩ := GlobalTheory.T.exists_away_unit_map_eq A' M u₀
  have hm₁ : (algebraMap B A' f) * m₀ ∈ M := M.mul_mem hfM hm₀
  have hunit1 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀)) ((algebraMap B A' f) * m₀)) := IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (algebraMap B A' f) →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift (algebraMap B A' f) (isUnit_of_mul_isUnit_left (by simpa using hunit1))
  let β : Localization.Away m₀ →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift m₀ (isUnit_of_mul_isUnit_right (by simpa using hunit1))
  let φ₁ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization M :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (IsLocalization.map_units (Localization M) (⟨_, hm₁⟩ : M))
  have hα : α.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hβ : β.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hφ₁ : φ₁.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₀ : IsUnit (q : Localization.Away m₀) := by simpa using hqA.map (algebraMap A' _)
  have hqm₁ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀)) := by simpa using hqA.map (algebraMap A' _)
  have hnat := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  set y := pull _ (spMap α) _ _ w - kum q (gU _ (Units.map β.toMonoidHom v)) with hy
  have hy0 : pull _ (spMap φ₁) _ _ y = 0 := by
    rw [hy, map_sub, ← pull_spMap_comp, pull_kum_gU hnat q _ hqm₁]
    have e1 : φ₁.comp α = φf := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) (by rw [RingHom.comp_assoc, hα, hφ₁, hφf])
    have e2 : Units.map φ₁.toMonoidHom (Units.map β.toMonoidHom v) = u₀ := by
      rw [← hv (φ₁.comp β) (by rw [RingHom.comp_assoc, hβ, hφ₁])]; ext; rfl
    rw [e1, e2, hu₀, hu, sub_self]
  obtain ⟨m', hm', hψ⟩ := GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q A' M 1 1 hqA ((algebraMap B A' f) * m₀) hm₁ y φ₁ hφ₁ hy0
  obtain ⟨b, hb, hbm⟩ := M.mul_mem hm₁ hm'
  obtain ⟨s, hs, t, ht, rfl⟩ := Submonoid.mem_sup.1 hb
  obtain ⟨n, rfl⟩ := ht
  have hs' : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) := hs
  refine ⟨Localization.Away (algebraMap B A' s), inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' B A' f s hA' hs', ?_⟩
  set A₂ := Localization.Away (algebraMap B A' s)
  set g : A' →+* Localization.Away (algebraMap B A₂ f) := (algebraMap A₂ _).comp (algebraMap A' A₂) with hg
  have hgu : IsUnit (g ((algebraMap B A' f) * m₀ * m')) := by
    rw [← hbm]
    simp only [map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · exact (IsLocalization.Away.algebraMap_isUnit (algebraMap B A' s)).map (algebraMap A₂ _)
    · have : g (algebraMap B A' f) = algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) := by
        rw [hg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂ f]
      rw [this]
      exact IsLocalization.Away.algebraMap_isUnit _
  let χ : Localization.Away ((algebraMap B A' f) * m₀ * m') →+* Localization.Away (algebraMap B A₂ f) :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀ * m') hgu
  have hχ : χ.comp (algebraMap A' _) = g := IsLocalization.Away.lift_comp _ _
  have hunit2 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀ * m')) ((algebraMap B A' f) * m₀ * m')) :=
    IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization.Away ((algebraMap B A' f) * m₀ * m') :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (isUnit_of_mul_isUnit_left (by simpa using hunit2))
  have hψc : ψ.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₂ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀ * m')) := by simpa using hqA.map (algebraMap A' _)
  clear_value χ ψ β α
  refine ⟨gU _ (Units.map (χ.comp (ψ.comp β)).toMonoidHom v), fun φ hφ => ?_⟩
  have e3 : φ = χ.comp (ψ.comp α) := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f))
    (by rw [hφ, RingHom.comp_assoc, RingHom.comp_assoc, hα, hψc, hχ])
  have hw : pull _ (spMap α) _ _ w = y + kum q (gU _ (Units.map β.toMonoidHom v)) := by
    rw [hy, sub_add_cancel]
  subst e3
  rw [pull_spMap_comp, pull_spMap_comp, hw]
  have hψy := hψ ψ hψc
  rw [map_add (pull _ (spMap ψ) _ _)]
  rw [hψy, zero_add]
  rw [pull_kum_gU hnat q ψ hqm₁]
  have key : pull _ (spMap χ) _ _ (kum q (gU _ (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) =
      kum q (gU _ (Units.map χ.toMonoidHom (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) :=
    pull_kum_gU hnat q χ hqm₂ _
  refine key.trans ?_
  exact congrArg (kum q) (congrArg (gU _) (Units.ext rfl))

end GlobalTheory.EtC.KummerLoc

end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TrivAbove

variable {E : Type} [Field E] [NumberField E]

theorem one_coord' (w : HeightOneSpectrum (𝓞 E)) : (1 : Af E) w = 1 := rfl

theorem mul_coord' (x y : Af E) (w : HeightOneSpectrum (𝓞 E)) : (x * y) w = x w * y w := rfl

theorem inv_coord' (z : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : (↑z⁻¹ : Af E) w = ((z : Af E) w)⁻¹ := by
  show (((coord w z)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
  rw [Units.val_inv_eq_inv_val, coe_coord]


open Classical in
theorem prod_single_coord (S : Finset (HeightOneSpectrum (𝓞 E)))
    (x : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w' : HeightOneSpectrum (𝓞 E)) :
    ((∏ w ∈ S, single w (x w) : (Af E)ˣ) : Af E) w' = if w' ∈ S then (x w' : w'.adicCompletion E) else 1 := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, one_coord']; simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul, mul_coord', ih]
    by_cases h : w' = a
    · subst h; simp [ha, single_self]
    · rw [suppAt_single a (x a) w' h]; simp [h]

theorem mem_hatOUnits [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) (z : (Af E)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((z : Af E) w - 1) <
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) :
    z ∈ hatOUnits c := by
  have key : ∀ z : Af E, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w - 1) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) → z ∈ hatO c :=
    fun z h => (GlobalTheory.T.mem_completedOrder_iff_placewise E c hc z).2 ⟨1, one_mem _, fun w => by rw [one_coord', map_one], h⟩
  refine ⟨key _ fun w => (hz w).le, key _ fun w => ?_⟩
  have h1 : Valued.v ((z : Af E) w - 1) < Valued.v (1 : w.adicCompletion E) := by
    rw [map_one]
    exact (hz w).trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hv : Valued.v ((z : Af E) w) = 1 := by
    have := Valuation.map_eq_of_sub_lt _ h1
    rwa [map_one] at this
  have hz0 : (z : Af E) w ≠ 0 := by rw [← coe_coord]; exact (coord w z).ne_zero
  show Valued.v ((↑z⁻¹ : Af E) w - 1) ≤ _
  rw [inv_coord']
  have he : ((z : Af E) w)⁻¹ - 1 = -(((z : Af E) w - 1) * ((z : Af E) w)⁻¹) := by
    field_simp; ring
  rw [he, Valuation.map_neg, map_mul, map_inv₀, hv, inv_one, mul_one]
  exact (hz w).le

theorem exists_rep_trivial_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (l : ℕ),
    c ≠ ⊥ → l.Prime → ∀ q : PicO c, ∃ y : (Af E)ˣ, (QuotientGroup.mk y : PicO c) = q ∧
      ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1 := by
  intro E _ _ _ c l hc hl q
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hl0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
    exact (Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units hfin.toFinset (fun w => (coord w y0)⁻¹)
    (fun w => (multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))
  set A : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom a with hAdef
  set y1 : (Af E)ˣ := A * y0 with hy1
  set u : (Af E)ˣ := ∏ w ∈ hfin.toFinset, single w (coord w y1) with hudef
  have hA : A ∈ princ ⊔ hatOUnits c := Subgroup.mem_sup_left ⟨a, rfl⟩
  have hu : u ∈ princ ⊔ hatOUnits c := by
    refine Subgroup.mem_sup_right (mem_hatOUnits hc u fun w => ?_)
    rw [hudef, prod_single_coord]
    split_ifs with hw
    · rw [coe_coord, hy1, Units.val_mul, mul_coord']
      have hAw : (A : Af E) w = algebraMap E (w.adicCompletion E) (a : E) := rfl
      have := ha w hw
      rw [hAw]
      simpa [Units.val_inv_eq_inv_val, coe_coord] using this
    · rw [sub_self, map_zero]; exact WithZero.exp_pos.bot_lt
  refine ⟨y1 * u⁻¹, ?_, fun w hw => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff A).2 hA, (QuotientGroup.eq_one_iff u).2 hu, one_mul, inv_one, mul_one]
  · have hwT : w ∈ hfin.toFinset := hfin.mem_toFinset.2 hw
    rw [Units.val_mul, mul_coord', inv_coord', hudef, prod_single_coord, if_pos hwT, coe_coord]
    exact mul_inv_cancel₀ (by rw [← coe_coord]; exact (coord w y1).ne_zero)

end GlobalTheory.CMVal.TrivAbove
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.lift_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c)
    (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (φ ψ : G.A n →ₐ[R] D) :
    Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) =
      d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f (G.A n) D (toConv φ * toConv ψ).ofConv (t.y n) +
            (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f (G.A n) D φ (t.y n) + φ (d.h n)) -
          (fv d.f (G.A n) D ψ (t.y n) + ψ (d.h n))) := by
  set l : G.A n ⊗[R] G.A n →ₐ[R] D := Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) with hl
  have hc := (fv_isCoc_and_ev_eq R A d.f).1
  have e1 : l.comp Algebra.TensorProduct.includeLeft = φ := by
    simpa only [hl] using Algebra.TensorProduct.lift_comp_includeLeft φ ψ (fun _ _ ↦ Commute.all _ _)
  have e2 : l.comp Algebra.TensorProduct.includeRight = ψ := by
    simpa only [hl] using Algebra.TensorProduct.lift_comp_includeRight' φ ψ (fun _ _ ↦ Commute.all _ _)
  have e3 : l.comp (Bialgebra.comulAlgHom R (G.A n)) = (toConv φ * toConv ψ).ofConv := by
    apply AlgHom.ext
    intro a
    change l (Coalgebra.comul a) = (toConv φ * toConv ψ) a
    rw [AlgHom.convMul_apply, ofConv_toConv, ofConv_toConv, hl]
  have e4 : (toConv (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) *
      toConv Algebra.TensorProduct.includeRight).ofConv = Bialgebra.comulAlgHom R (G.A n) := by
    apply AlgHom.ext
    intro a
    simpa only [ofConv_toConv, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply,
      Bialgebra.comulAlgHom_apply]
      using AlgHom.convMul_apply
        (toConv (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n))
        (toConv Algebra.TensorProduct.includeRight) a
  have m := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
    (toConv Algebra.TensorProduct.includeRight)
  rw [e4] at m
  have a := d.add (G.A n ⊗[R] G.A n) D l (spOver Algebra.TensorProduct.includeLeft ≫ t.y n)
    (spOver Algebra.TensorProduct.includeRight ≫ t.y n)
  have c1 := hc _ _ _ Algebra.TensorProduct.includeLeft l (t.y n) (sm_whole _)
  have c2 := hc _ _ _ Algebra.TensorProduct.includeRight l (t.y n) (sm_whole _)
  have c3 := hc _ _ _ (Bialgebra.comulAlgHom R (G.A n)) l (t.y n) (sm_whole _)
  rw [← m, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e1, e2] at a
  rw [e1] at c1
  rw [e2] at c2
  rw [e3] at c3
  have h3 : l (Coalgebra.comul (d.h n)) = (toConv φ * toConv ψ).ofConv (d.h n) := by
    rw [← e3]; rfl
  have h1 : l (d.h n ⊗ₜ 1) = φ (d.h n) := by simp [hl]
  have h2 : l (1 ⊗ₜ d.h n) = ψ (d.h n) := by simp [hl]
  simp only [Dat.coc, cobOne_apply, map_sub, h1, h2, h3]
  rw [c1, c2, c3]
  linear_combination -a

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
theorem _root_.GlobalTheory.T.crystallineCocycleCotangentValue_baseChange_natural
    (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R')
    (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ)
    (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D']
    (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D')
    (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (ha : ∀ r : D, (a.φ r : D') = s r) :
    cotVal (m.coef.pullbackOneCocycle f) y' =
      (SemiBialgHom.cot s) (cotVal f y) + dUnit (R := R') (A := D') (ev f a) :=
  cotVal_pull R R' σ X X' φ m D D' s y y' a f ha
end

section

alias GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq :=
  GlobalTheory.PtExt.fv_isCoc_and_ev_eq
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR A → ∃ g : Fn2 A, IsAdd (fv f) g := by
  first | exact @GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | exact GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | (intros; apply GlobalTheory.PtExt.exists_isAdd_of_mem_primDR <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_basicOpen_cover_algebraPoint_liesInCover :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a,
          Sm (X := X) W (D := Localization.Away (s a))
            (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) :=
  GlobalTheory.PtExt.exists_away_cover_sm
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial : ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∃ j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι, IsChoice P j := by
  first | exact @GlobalTheory.PtExt.exists_isChoice | exact GlobalTheory.PtExt.exists_isChoice | (intros; apply GlobalTheory.PtExt.exists_isChoice <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

theorem isCob_whole_of_isCob_cover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc (whole X) u → ∀ k : Fn0 X, IsCob W u k → ∃ k' : Fn0 X, IsCob (whole X) u k' := by
  intro R _ X K W hW u hu k hk
  have ex : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃! d : D,
      ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (D := E) (spOver ψ ≫ x) →
        k E (spOver ψ ≫ x) - u D E ψ x = ψ d := by
    intro D _ _ x
    refine natFamily_existsUnique R X K W hW D x (fun E _ _ ψ ↦ k E (spOver ψ ≫ x) - u D E ψ x) ?_
    intro E _ _ E' _ _ ψ θ hψ
    have c := hu D E E' ψ θ x (sm_whole x)
    have b := hk E E' θ (spOver ψ ≫ x) hψ
    have e : spOver (θ.comp ψ) ≫ x = spOver θ ≫ spOver ψ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    show k E' (spOver (θ.comp ψ) ≫ x) - u D E' (θ.comp ψ) x = θ (k E (spOver ψ ≫ x) - u D E ψ x)
    rw [e, c, b, map_sub]
    ring
  let k' : Fn0 X := fun D _ _ x ↦ (ex D x).exists.choose
  have hk' : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (E : Type) [CommRing E] [Algebra R E]
      (ψ : D →ₐ[R] E), Sm W (D := E) (spOver ψ ≫ x) → k E (spOver ψ ≫ x) - u D E ψ x = ψ (k' D x) :=
    fun D _ _ x ↦ (ex D x).exists.choose_spec
  refine ⟨k', fun D _ _ D' _ _ φ x _ ↦ ?_⟩
  have huniq : k' D' (spOver φ ≫ x) = u D D' φ x + φ (k' D x) := by
    refine (ex D' (spOver φ ≫ x)).unique (hk' D' (spOver φ ≫ x)) ?_
    intro E _ _ ψ hψ
    have e : spOver (ψ.comp φ) ≫ x = spOver ψ ≫ spOver φ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    have h1 := hk' D x E (ψ.comp φ) (by rw [e]; exact hψ)
    have c := hu D D' E φ ψ x (sm_whole x)
    rw [e, c, AlgHom.comp_apply] at h1
    rw [map_add (f := _), ← h1]
    ring
  rw [huniq]
  ring

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product :
    ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (v : epsR R ⟶ B), IsTangent v →
    (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let y : Pt A D' := spOver φ ≫ x
      ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
        (s' : trivAt (pt0 B y) ⟶ thickAt B y) (i' : trivAt (ptV v y) ⟶ thickAt B y)
        (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B y)) (b : trivAt (ptV v x) ⟶ trivAt (ptV v y))
        (τ : thickAt B x ⟶ thickAt B y),
        (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧
        (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧
        (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧
    ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ :=
  GlobalTheory.PtExt.ContrMor.exists_contr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

theorem _root_.GlobalTheory.T.length_stalk_reducedClosed_genericPoint_eq_rank : ∀ (X : Scheme.{0}) (Z : Closeds X) [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme] (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G], Module.length (X.presheaf.stalk (redι Z (genericPoint _))) (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) = (GlobalTheory.VB.genRank G : ℕ∞) := by
  first | exact @GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint | exact GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint | (intros; apply GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint <;> assumption)
end
