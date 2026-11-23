module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
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
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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

open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology

noncomputable section

namespace GlobalTheory

def latticeCurve (L : PeriodPair) : WeierstrassCurve ℂ := ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩

lemma latticeCurve_Δ (L : PeriodPair) : (latticeCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [latticeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma latticeCurve_c₄ (L : PeriodPair) : (latticeCurve L).c₄ = 12 * L.g₂ := by
  simp only [latticeCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp [τ.im_ne_zero] at h1
    simp [h1] at h2
    exact ⟨h1, h2⟩

lemma mem_lattice_periodPairOfTau (τ : ℍ) (x : ℂ) :
    x ∈ (periodPairOfTau τ).lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by
  simp [PeriodPair.mem_lattice, periodPairOfTau]

theorem exists_lattice_eq_mul_tau (L : PeriodPair) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  have hi := LinearIndependent.pair_iff.mp L.indep
  have h2 : L.ω₂ ≠ 0 := fun h ↦ by simpa using (hi 0 1 (by simp [h])).2
  have him : (L.ω₁ / L.ω₂).im ≠ 0 := fun h ↦ by
    have h3 : L.ω₁ / L.ω₂ = ((L.ω₁ / L.ω₂).re : ℂ) := Complex.ext (by simp) (by simpa using h)
    have := (hi 1 (-(L.ω₁ / L.ω₂).re) (by
      simp only [Complex.real_smul, Complex.ofReal_neg, ← h3]
      field_simp
      simp)).1
    simp at this
  rcases lt_or_gt_of_ne him with h | h
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by simpa using h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩

section

variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

theorem latticeG_eq_E {k : ℕ} (hk : 3 ≤ k) :
    L.G k = 2 * riemannZeta k * E hk τ / a ^ k := by
  let e : (Fin 2 → ℤ) → L.lattice := fun v ↦ ⟨a * (v 0 * (τ : ℂ) + v 1), (h _).mpr ⟨_, _, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro v w hvw
      have h0 : (v 0 * (τ : ℂ) + v 1) = w 0 * (τ : ℂ) + w 1 :=
        mul_left_cancel₀ ha (congrArg Subtype.val hvw)
      have h1 := congrArg Complex.im h0
      simp [τ.im_ne_zero] at h1
      rw [h1, add_right_inj] at h0
      ext i
      fin_cases i
      · exact h1
      · exact_mod_cast h0
    · rintro ⟨x, hx⟩
      obtain ⟨m, n, rfl⟩ := (h x).mp hx
      exact ⟨![m, n], rfl⟩
  have h1 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h2 : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [PeriodPair.G, ← (Equiv.ofBijective e he).tsum_eq, h2]
  have h3 : ∀ v, (((Equiv.ofBijective e he v : L.lattice) : ℂ) ^ k)⁻¹ =
      (a ^ k)⁻¹ * eisSummand k v τ := fun v ↦ by
    simp [e, eisSummand, mul_pow, mul_comm]
  simp_rw [h3]
  rw [tsum_mul_left, h1]
  field_simp

theorem g₂_eq_E₄ : L.g₂ = 4 * π ^ 4 / 3 * E₄ τ / a ^ 4 := by
  have := latticeG_eq_E ha h (k := 4) (by norm_num)
  rw [PeriodPair.g₂, this, Nat.cast_ofNat, riemannZeta_four]
  ring

theorem g₃_eq_E₆ : L.g₃ = 8 * π ^ 6 / 27 * E₆ τ / a ^ 6 := by
  have := latticeG_eq_E ha h (k := 6) (by norm_num)
  have h6 : riemannZeta 6 = π ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [PeriodPair.g₃, this, Nat.cast_ofNat, h6]
  ring

theorem latticeCurve_Δ_eq_discriminant :
    (latticeCurve L).Δ = (2 * π / a) ^ 12 * discriminant τ := by
  rw [latticeCurve_Δ, g₂_eq_E₄ ha h, g₃_eq_E₆ ha h, discriminant_eq_E₄_cube_sub_E₆_sq]
  field_simp
  ring

end

theorem latticeCurve_Δ_ne_zero (L : PeriodPair) : (latticeCurve L).Δ ≠ 0 := by
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [latticeCurve_Δ_eq_discriminant ha h]
  have := discriminant_ne_zero τ
  have := Real.pi_ne_zero
  simp [*]

instance latticeCurve_isElliptic (L : PeriodPair) : (latticeCurve L).IsElliptic :=
  ⟨(latticeCurve_Δ_ne_zero L).isUnit⟩

theorem latticeCurve_j {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    (latticeCurve L).j = E₄ τ ^ 3 / discriminant τ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    latticeCurve_Δ_eq_discriminant ha h, latticeCurve_c₄, g₂_eq_E₄ ha h]
  have := discriminant_ne_zero τ
  have : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  field_simp
  ring

lemma tendsto_E₄_atImInfty : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty E₄ = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL)]
    exact E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (E₄)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

theorem exists_E₄_cube_div_discriminant_eq (c : ℂ) :
    ∃ τ : ℍ, E₄ τ ^ 3 / discriminant τ = c := by
  by_contra! hc
  let g : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) -
    c • (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  have hg : ∀ τ, g τ = E₄ τ ^ 3 - c * discriminant τ := fun τ ↦ by
    simp [g]
    rfl
  have hg0 : ∀ τ, g τ ≠ 0 := fun τ h ↦ hc τ (by
    rw [hg] at h
    rw [div_eq_iff (discriminant_ne_zero τ)]
    linear_combination h)
  have hlim : Tendsto (g : ℍ → ℂ) atImInfty (𝓝 1) := by
    have := (tendsto_E₄_atImInfty.pow 3).sub
      ((show Tendsto discriminant atImInfty (𝓝 0) from discriminant_isZeroAtImInfty).const_mul c)
    simpa [funext hg] using this
  have hsl : ∀ γ : SL(2, ℤ),
      ((1 : ℍ → ℂ) / g) ∣[(0 : ℤ) - 12] γ = (1 : ℍ → ℂ) / g := fun γ ↦ by
    have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
    rw [div_slash_SL2, is_invariant_one, SL_slash, SlashInvariantForm.slash_action_eqn _ _ hγ]
  let f : ModularForm 𝒮ℒ ((0 : ℤ) - 12) :=
    { toFun := (1 : ℍ → ℂ) / g
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hsl γ
      holo' := mdifferentiable_const.div g.holo' hg0
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hsl γ]
        exact ((tendsto_const_nhds (x := (1 : ℂ))).div hlim one_ne_zero).isBigO_one ℝ }
  have := congrFun (ModularFormClass.levelOne_neg_weight_eq_zero (by norm_num) f) UpperHalfPlane.I
  have h3 : (1 : ℂ) / g UpperHalfPlane.I = 0 := this
  simp [hg0] at h3

theorem exists_variableChange_eq_latticeCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • W = latticeCurve L := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq W.j
  refine ⟨periodPairOfTau τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [latticeCurve_j one_ne_zero (mem_lattice_periodPairOfTau τ), hτ]

end GlobalTheory
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory

namespace FlatDescent

universe u

variable {X Y Z : Scheme.{u}}

theorem injective_appTop_of_epi (p : Y ⟶ X) [Epi p] : Function.Injective p.appTop := by
  have : Epi (Scheme.Γ.rightOp.map p) :=
    have := ΓSpec.adjunction.isLeftAdjoint
    inferInstance
  have : Mono p.appTop := inferInstanceAs (Mono (Scheme.Γ.rightOp.map p).unop)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback p.appTop

theorem exists_appTop_eq_of_effectiveEpi (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) (hs : f.appTop s = g.appTop s) :
    ∃ a : Γ(X, ⊤), p.appTop a = s := by
  let E := RingHom.eqLocus f.appTop.hom g.appTop.hom
  let ι : CommRingCat.of E ⟶ Γ(Y, ⊤) := CommRingCat.ofHom E.subtype
  have hι : ι ≫ f.appTop = ι ≫ g.appTop := by
    ext x
    exact x.2
  have : HasPullback p p := inferInstance
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair p h (Y.toSpecΓ ≫ Spec.map ι) (by
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hι])
  refine ⟨u.appTop ((Scheme.ΓSpecIso (.of E)).inv ⟨s, hs⟩), ?_⟩
  have h1 : (Scheme.ΓSpecIso (.of E)).inv ≫ u.appTop ≫ p.appTop = ι := by
    rw [← Scheme.Hom.comp_appTop, hu, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  exact congr($h1 ⟨s, hs⟩)

theorem appTop_appTop_eq {p : Y ⟶ X} {f g : Z ⟶ Y} (h : f ≫ p = g ≫ p) (a : Γ(X, ⊤)) :
    f.appTop (p.appTop a) = g.appTop (p.appTop a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, h]

theorem existsUnique_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) :
    (∃! a : Γ(X, ⊤), p.appTop a = s) ↔ f.appTop s = g.appTop s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact appTop_appTop_eq h.w a
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s hs
    exact ⟨a, ha, fun b hb => injective_appTop_of_epi p (hb.trans ha.symm)⟩

theorem isUnit_appTop_iff (p : Y ⟶ X) [EffectiveEpi p] (a : Γ(X, ⊤)) :
    IsUnit (p.appTop a) ↔ IsUnit a := by
  refine ⟨fun ha => ?_, fun ha => ha.map p.appTop.hom⟩
  obtain ⟨t, ht⟩ := ha.exists_right_inv
  have h := IsPullback.of_hasPullback p p
  obtain ⟨b, rfl⟩ := exists_appTop_eq_of_effectiveEpi p h t (by
    have h1 := congrArg (pullback.fst p p).appTop.hom ht
    have h2 := congrArg (pullback.snd p p).appTop.hom ht
    rw [map_mul, map_one] at h1 h2
    rw [appTop_appTop_eq h.w a] at h1
    exact left_inv_eq_right_inv ((mul_comm _ _).trans h1) h2)
  exact IsUnit.of_mul_eq_one b (injective_appTop_of_epi p (by rw [map_mul, ht, map_one]))

theorem existsUnique_units_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)ˣ) :
    (∃! a : Γ(X, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom a = s) ↔
      Units.map f.appTop.hom.toMonoidHom s = Units.map g.appTop.hom.toMonoidHom s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact Units.ext (appTop_appTop_eq h.w a)
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s (congrArg Units.val hs)
    obtain ⟨a, rfl⟩ := (isUnit_appTop_iff p a).1 (ha ▸ s.isUnit)
    exact ⟨a, Units.ext ha, fun b hb => Units.ext <|
      injective_appTop_of_epi p ((congrArg Units.val hb).trans ha.symm)⟩

section Opens

theorem isPullback_resLE {p : Y ⟶ X} {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens)
    (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) :
    IsPullback (f.resLE _ W hf) (g.resLE _ W hg) (p ∣_ U) (p ∣_ U) := by
  subst hW
  have hc : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      (s.fst ≫ (p ⁻¹ᵁ U).ι) ≫ p = (s.snd ≫ (p ⁻¹ᵁ U).ι) ≫ p := fun s => by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, s.condition_assoc]
  have hr : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      Set.range (h.lift _ _ (hc s)) ⊆ Set.range (f ⁻¹ᵁ p ⁻¹ᵁ U).ι := fun s => by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (h.lift _ _ _ x) ∈ p ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_apply, h.lift_fst, Scheme.Hom.comp_apply]
    exact (s.fst x).2
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => IsOpenImmersion.lift (f ⁻¹ᵁ p ⁻¹ᵁ U).ι
    (h.lift _ _ (hc s)) (hr s)) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, h.w]
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (f ⁻¹ᵁ p ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
    refine h.hom_ext ?_ ?_
    · simp [← h₁]
    · simp [← h₂]

theorem appTop_resLE_apply (f : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : (f.resLE V W e).appTop (V.topIso.inv s) = W.topIso.inv (f.appLE V W e s) := by
  have : V.topIso.inv ≫ (f.resLE V W e).appTop = f.appLE V W e ≫ W.topIso.inv := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]
  exact congr($this s)

theorem appTop_morphismRestrict_apply (p : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (p ∣_ U).appTop (U.topIso.inv a) = (p ⁻¹ᵁ U).topIso.inv (p.app U a) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, appTop_resLE_apply, Scheme.Hom.appLE_eq_app]

theorem effectiveEpi_morphismRestrict (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : EffectiveEpi (p ∣_ U) := by
  have : Flat (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : Surjective (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : QuasiCompact (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  infer_instance

theorem existsUnique_app_eq_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens) (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U)
    (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) (s : Γ(Y, p ⁻¹ᵁ U)) :
    (∃! a : Γ(X, U), p.app U a = s) ↔ f.appLE _ W hf s = g.appLE _ W hg s := by
  have := effectiveEpi_morphismRestrict p U
  have hb : ∀ {T : Scheme.{u}} (V : T.Opens), Function.Bijective V.topIso.inv := fun V =>
    ConcreteCategory.bijective_of_isIso _
  rw [← (hb W).1.eq_iff, ← appTop_resLE_apply, ← appTop_resLE_apply,
    ← existsUnique_appTop_eq_iff (p ∣_ U) (isPullback_resLE h U W hW hf hg),
    ← (Equiv.ofBijective _ (hb U)).existsUnique_congr_right]
  simp only [Equiv.ofBijective_apply, appTop_morphismRestrict_apply, (hb _).1.eq_iff]

theorem isUnit_app_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p] (U : X.Opens)
    (a : Γ(X, U)) : IsUnit (p.app U a) ↔ IsUnit a := by
  have := effectiveEpi_morphismRestrict p U
  rw [← isUnit_map_iff (p ⁻¹ᵁ U).topIso.inv.hom, ← appTop_morphismRestrict_apply,
    isUnit_appTop_iff, isUnit_map_iff]

end Opens

end FlatDescent

end GlobalTheory
end

section

universe u_1

namespace GlobalTheory.IrreducibleGeneralizations

open AlgebraicGeometry Topology

theorem isIrreducible_generalizations {X : Scheme.{u_1}} (x : X) [IsDomain (X.presheaf.stalk x)] :
    IsIrreducible {y : X | y ⤳ x} := by

  have hSpec : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ _
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact hSpec.image _ (X.fromSpecStalk x).continuous.continuousOn

theorem component_eq_closure {X : Scheme.{u_1}} {x : X} [IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) :
    Z = closure {y : X | y ⤳ x} := by

  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hsub : Z ⊆ closure {y : X | y ⤳ x} := fun z hz =>
    closure_mono (Set.singleton_subset_iff.mpr (hη.specializes hx)) (hη.specializes hz).mem_closure
  exact hsub.antisymm (hZ.2 (isIrreducible_generalizations x).closure hsub)

theorem main : ∀ {X : AlgebraicGeometry.Scheme} {x : ↥X} [IsDomain (↑(TopCat.Presheaf.stalk (AlgebraicGeometry.PresheafedSpace.presheaf (AlgebraicGeometry.SheafedSpace.toPresheafedSpace (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) x) : Type u_1)] {Z W : Set ↥X}, Z ∈ irreducibleComponents ↥X → W ∈ irreducibleComponents ↥X → x ∈ Z → x ∈ W → Z = W := by
  intro X x _ Z W hZ hW hxZ hxW
  rw [component_eq_closure hZ hxZ, component_eq_closure hW hxW]

end GlobalTheory.IrreducibleGeneralizations
end
