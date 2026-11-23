module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle235
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_cancel_tensor {R O A T : Type} [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] :
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  haveI : SMulCommClass R O T := IsScalarTower.to_smulCommClass
  refine ⟨(TensorProduct.comm R A T).toAddEquiv.trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R O O T A).symm.toAddEquiv).trans
      (TensorProduct.comm O T (O ⊗[R] A)).toAddEquiv), fun w t => ?_⟩
  simp

theorem exists_cancel_tensor_compHom (R O A T : Type) [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] :
    letI : Module R T := Module.compHom T (algebraMap R O)
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  letI : Module R T := Module.compHom T (algebraMap R O)
  haveI : IsScalarTower R O T := IsScalarTower.of_compHom R O T
  exact exists_cancel_tensor

theorem exists_kappa : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  intro l _ K LL T
  exact exists_cancel_tensor_compHom ℤ_[l] ↥(OL LL) (WCb l) ↥T.L.T

end GlobalTheory.HWL
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Filter Topology

namespace GlobalTheory

theorem continuous_adicModule_span_iff {R M G : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace G] (a : R) (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g₀ : G) (n : ℕ), ∀ᶠ g in 𝓝 g₀, ∃ y : M, f g = f g₀ + a ^ n • y := by
  letI : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hmem : ∀ (n : ℕ) (x : M), x ∈ ((Ideal.span {a}) ^ n • (⊤ : Submodule R M)) ↔
      ∃ y : M, a ^ n • y = x := by
    intro n x
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hb := fun x₀ : M => (@ModuleFilterBasis.toAddGroupFilterBasis R M _
    (Ideal.span {a}).adic_basis.topology _ _
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M))).nhds_hasBasis x₀
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g₀ => ?_
  refine ((hb (f g₀)).tendsto_right_iff).trans ?_
  constructor
  · intro h n
    filter_upwards [h _ ⟨n, rfl⟩] with g hg
    obtain ⟨y, hy, hy'⟩ := hg
    obtain ⟨z, rfl⟩ := (hmem n y).1 hy
    exact ⟨z, hy'.symm⟩
  · rintro h _ ⟨n, rfl⟩
    filter_upwards [h n] with g hg
    obtain ⟨z, hz⟩ := hg
    exact ⟨a ^ n • z, (hmem n _).2 ⟨z, rfl⟩, hz.symm⟩

theorem torsionExponent_devissage_commRing {R G X X' X'' : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X'] [AddCommGroup X''] [Module R X'']
    (a : R) (htf : ∀ (n : ℕ) (z : X''), a ^ n • z = 0 → z = 0)
    (ρ : Representation R G X) (ρ' : Representation R G X') (ρ'' : Representation R G X'')
    (i : X' →ₗ[R] X) (p : X →ₗ[R] X'') (r' r'' : R)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hiρ : ∀ g x, i (ρ' g x) = ρ g (i x)) (hpρ : ∀ g x, p (ρ g x) = ρ'' g (p x))
    (hc : ∀ x, @Continuous G X _ ((Ideal.span {a}).adicModuleTopology X) fun g => ρ g x)
    (h0 : ∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = a ^ k • z)
    (h' : @TorsKilledBy R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' a r')
    (h'' : @TorsKilledBy R G X'' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X'') ρ'' a r'') :
    @TorsKilledBy R G X _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X) ρ a (r' * r'') := by
  rintro f ⟨hfc, hf⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_span_iff] at hfc
  simp only [Pi.smul_apply] at hx

  obtain ⟨z'', hz''⟩ := h'' (fun g => p (f g)) ⟨by
      rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n] with g hg
      obtain ⟨y, hy⟩ := hg
      exact ⟨p y, by rw [hy, map_add (f := _), map_smul]⟩,
    fun g h => by simp only [hf, map_add (f := _), hpρ]⟩
    ⟨k, p x, fun g => by rw [Pi.smul_apply, ← map_smul, hx, map_sub, hpρ]⟩
  obtain ⟨z, rfl⟩ := hp z''
  simp only [Pi.smul_apply] at hz''
  have hex' : ∀ g, ∃ y, i y = r'' • f g - (ρ g z - z) := fun g =>
    (hex _).1 (by rw [map_sub, map_smul, hz'', map_sub, hpρ, sub_self])
  choose f' hf' using hex'
  have hcoc : @IsCoc R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' f' := by
    refine ⟨?_, fun g h => hi ?_⟩
    · rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n, (continuous_adicModule_span_iff a _).1 (hc z) g₀ n] with g hg hg'
      obtain ⟨y, hy⟩ := hg
      obtain ⟨w, hw⟩ := hg'
      have h1 : i (f' g) = i (f' g₀) + a ^ n • (r'' • y - w) := by
        rw [hf', hf', hy, hw]; module
      have h2 : p (r'' • y - w) = 0 := by
        apply htf n
        have := congrArg p h1
        rwa [map_add, hex.apply_apply_eq_zero, hex.apply_apply_eq_zero, zero_add, map_smul,
          eq_comm] at this
      obtain ⟨u, hu⟩ := (hex _).1 h2
      exact ⟨u, hi (by rw [h1, map_add (f := _), map_smul, hu])⟩
    · rw [map_add (f := _), hiρ, hf', hf', hf', hf, map_mul]
      simp only [Module.End.mul_apply, map_sub, map_smul]
      module

  have hw : ∀ g, i (a ^ k • f' g) = ρ g (r'' • x - a ^ k • z) - (r'' • x - a ^ k • z) := by
    intro g
    rw [map_smul, hf', smul_sub, smul_comm, hx]
    simp only [map_sub, map_smul]
    module
  obtain ⟨k', x₀, hx₀, hpx₀⟩ := h0 (p (r'' • x - a ^ k • z)) (fun g => by
    rw [← hpρ, ← sub_eq_zero, ← map_sub, ← hw, hex.apply_apply_eq_zero])
  obtain ⟨w', hw'⟩ := (hex (a ^ k' • (r'' • x - a ^ k • z) - x₀)).1
    (by rw [map_sub, map_smul, hpx₀, sub_self])
  obtain ⟨u, hu⟩ := h' f' hcoc ⟨k' + k, w', fun g => hi (by
    rw [Pi.smul_apply, pow_add, mul_smul, map_smul, hw, map_sub i, hiρ, hw', map_sub (ρ g) _ x₀,
      hx₀, map_smul (ρ g) (a ^ k')]
    module)⟩
  refine ⟨i u + r' • z, fun g => ?_⟩
  have := congrArg i (hu g)
  rw [Pi.smul_apply, map_smul, hf', map_sub, hiρ] at this
  rw [Pi.smul_apply, map_add (f := _), map_smul]
  linear_combination (norm := module) this

theorem torsKilledBy_devissage : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [NoZeroSMulDivisors ℤ_[l] X] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X] (X' : Type) [AddCommGroup X'] [Module ℤ_[l] X'] [NoZeroSMulDivisors ℤ_[l] X'] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X'] (X'' : Type) [AddCommGroup X''] [Module ℤ_[l] X''] [NoZeroSMulDivisors ℤ_[l] X''] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X''] (ρ : Representation ℤ_[l] G X) (ρ' : Representation ℤ_[l] G X') (ρ'' : Representation ℤ_[l] G X'') (i : X' →ₗ[ℤ_[l]] X) (p : X →ₗ[ℤ_[l]] X'') (c' c'' : ℕ), letI : TopologicalSpace X := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X; letI : TopologicalSpace X' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X'; letI : TopologicalSpace X'' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X''; Function.Injective i → Function.Surjective p → Function.Exact i p → (∀ g x, i (ρ' g x) = ρ g (i x)) → (∀ g x, p (ρ g x) = ρ'' g (p x)) → (∀ x, Continuous fun g => ρ g x) → (∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = (l : ℤ_[l]) ^ k • z) → TorsKilledBy ρ' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c') → TorsKilledBy ρ'' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c'') → TorsKilledBy ρ (l : ℤ_[l]) ((l : ℤ_[l]) ^ (c' + c'')) := by
  intro l _ G _ _ _ _ _ X _ _ _ _ X' _ _ _ _ X'' _ _ _ _ ρ ρ' ρ'' i p c' c''
  intro hi hp hex hiρ hpρ hc h0 h' h''
  rw [pow_add]
  refine torsionExponent_devissage_commRing (l : ℤ_[l]) ?_ ρ ρ' ρ'' i p _ _ hi hp hex hiρ hpρ hc h0 h' h''
  intro n z hz
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left hl

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TorsionLevel

theorem exists_cocycle_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', c ∉ BD LA' → ∀ r : ℕ, (∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T) → ∀ n : ℕ, r ≤ n → ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T), ∃ c' ∈ quotientCocycles LA' _ hI', c' ∉ BQ LA' _ hI' ∧ ∀ h, ∃ t ∈ LA'.T, Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) = (algebraMap O LL ϖ) ^ n • liftD LA' (c h) + (algebraMap O LL ϖ) ^ n • t := by
  intro l _ K LL _ _ _ O _ _ hgood A' LA' ϖ hϖ c hc hcB r hr n hn hI'
  classical
  obtain ⟨⟨_, _, _⟩, -⟩ := hgood
  set p0 : LL := algebraMap O LL ϖ with hp0
  have hp0ne : p0 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr hϖ.ne_zero
  have memI : ∀ x : ↥LA'.T, x ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T) ↔
      ∃ y : ↥LA'.T, ϖ ^ n • y = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp
  have smulp : ∀ (j : ℕ) (w : A'.V), p0 ^ j • w = ϖ ^ j • w := by
    intro j w; rw [hp0, ← map_pow, algebraMap_smul]
  have hmem : ∀ g, p0 ^ n • liftD LA' (c g) ∈ LA'.T := by
    intro g
    have : p0 ^ n • liftD LA' (c g) = ϖ ^ (n - r) • (p0 ^ r • liftD LA' (c g)) := by
      rw [← smulp, smul_smul, ← pow_add, Nat.sub_add_cancel hn]
    rw [this]; exact LA'.T.smul_mem _ (hr g)
  have hlift : ∀ v : A'.V ⧸ LA'.T, Submodule.Quotient.mk (p := LA'.T) (liftD LA' v) = v :=
    fun v => (Submodule.Quotient.mk_surjective _ v).choose_spec
  let F : A'.V ⧸ LA'.T → ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T) := fun v =>
    if h : p0 ^ n • liftD LA' v ∈ LA'.T then Submodule.Quotient.mk ⟨_, h⟩ else 0
  have hc' : ∀ g, (F ∘ c) g = Submodule.Quotient.mk ⟨_, hmem g⟩ := by
    intro g; simp only [F, Function.comp_apply, dif_pos (hmem g)]
  refine ⟨fun g => Submodule.Quotient.mk ⟨_, hmem g⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have : (fun g => (Submodule.Quotient.mk ⟨_, hmem g⟩ :
        ↥LA'.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T))) = F ∘ c :=
      funext fun g => (hc' g).symm
    rw [this]; exact hc.1.comp F
  · intro g h
    simp only
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memI]
    have hd : liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h)) ∈ LA'.T := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub,
        hlift, hlift, hc.2 g h]
      have : Submodule.Quotient.mk (p := LA'.T) (A'.ρ g (liftD LA' (c h))) = actD LA' g (c h) := by
        conv_rhs => rw [← hlift (c h)]
        rfl
      rw [this]; abel
    refine ⟨⟨_, hd⟩, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, ← smulp]
    show p0 ^ n • (liftD LA' (c (g * h)) - liftD LA' (c g) - A'.ρ g (liftD LA' (c h))) =
      p0 ^ n • liftD LA' (c (g * h)) - (p0 ^ n • liftD LA' (c g) + A'.ρ g (p0 ^ n • liftD LA' (c h)))
    rw [map_smul, smul_sub, smul_sub]; abel
  · rintro ⟨x, hx⟩
    apply hcB
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨Submodule.Quotient.mk ((p0 ^ n)⁻¹ • (t : A'.V)), funext fun g => ?_⟩
    have hxg := congrFun hx g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hxg ⊢
    change Submodule.Quotient.mk (actT LA' g t) - Submodule.Quotient.mk t = _ at hxg
    rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq, memI] at hxg
    obtain ⟨s, hs⟩ := hxg
    have key : A'.ρ g (t : A'.V) - t - p0 ^ n • liftD LA' (c g) = p0 ^ n • (s : A'.V) := by
      rw [smulp n (s : A'.V)]
      have := congrArg Subtype.val hs
      rw [Submodule.coe_smul] at this
      rw [this]; rfl
    conv_rhs => rw [← hlift (c g)]
    change Submodule.Quotient.mk (p := LA'.T) (A'.ρ g ((p0 ^ n)⁻¹ • (t : A'.V))) - _ = _
    rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
    have : (A'.ρ g) ((p0 ^ n)⁻¹ • (t : A'.V)) - (p0 ^ n)⁻¹ • (t : A'.V) - liftD LA' (c g) = s := by
      apply smul_right_injective A'.V (pow_ne_zero n hp0ne)
      simp only [map_smul, ← smul_sub]
      rw [smul_sub, smul_inv_smul₀ (pow_ne_zero n hp0ne), key]
    rw [this]; exact s.2
  · intro h
    have key : ∀ x q : ↥LA'.T,
        Submodule.Quotient.mk (p := (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T)) q =
          Submodule.Quotient.mk x → ∃ t ∈ LA'.T, (q : A'.V) = (x : A'.V) + p0 ^ n • t := by
      intro x q hq
      rw [Submodule.Quotient.eq, memI] at hq
      obtain ⟨y, hy⟩ := hq
      refine ⟨y, y.2, ?_⟩
      rw [smulp n (y : A'.V), ← Submodule.coe_smul, hy, Submodule.coe_sub]; abel
    exact key _ _ (Submodule.Quotient.mk_surjective _ _).choose_spec

end GlobalTheory.TorsionLevel
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DivLift

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mk_inv_smul_liftQ (L : Lattice (O := O) ρ) (a : O) (ha : algebraMap O LL a ≠ 0)
    (y : ↥L.T) :
    (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y)) : V ⧸ L.T) =
      Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • (y : V)) := by
  obtain ⟨y0, hy0, hs⟩ : ∃ y0 : ↥L.T, (y0 : V) = Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y) ∧
      (Submodule.Quotient.mk y0 : ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) =
        Submodule.Quotient.mk y :=
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk y)).choose_spec⟩
  rw [← hy0]
  have hmem := (Submodule.Quotient.eq _).1 hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨t, -, ht⟩ := hmem
  have ht' : a • (t : V) = (y0 : V) - (y : V) := congrArg Subtype.val ht
  rw [Submodule.Quotient.eq, ← smul_sub, ← ht', ← algebraMap_smul LL a, smul_smul,
    inv_mul_cancel₀ ha, one_smul]
  exact t.2

theorem inv_smul_liftQ_mem_Z1D [TopologicalSpace G] (L : Lattice (O := O) ρ) (a : O)
    (ha : algebraMap O LL a ≠ 0) (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T))
    (c : G → ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (hc : c ∈ quotientCocycles L _ hI) :
    (fun g => (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) :
      V ⧸ L.T)) ∈ divisibleCocycles L := by
  refine ⟨hc.1.comp (fun x => (Submodule.Quotient.mk
    ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ x) : V ⧸ L.T)), fun g h => ?_⟩
  have hgh := hc.2 g h
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (c g)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (c h)
  have h1 : c (g * h) = Submodule.Quotient.mk (x + actT L g y) := by
    rw [hgh, ← hx, ← hy]; rfl
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + actD L g (Submodule.Quotient.mk _)
  rw [h1, ← hx, ← hy, mk_inv_smul_liftQ L a ha, mk_inv_smul_liftQ L a ha,
    mk_inv_smul_liftQ L a ha]
  show _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk (ρ g ((algebraMap O LL a)⁻¹ • (y : V)))
  rw [← Submodule.Quotient.mk_add, map_smul, ← smul_add]
  rfl

end Gen

theorem pow_inv_smul_liftQ_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  intro l _ K LL _ _ _ O _ _ _ A' LA' r hI' c'
  have he : algebraMap O LL (((l : ℕ) : O) ^ r) = ((l : ℕ) : LL) ^ r := by
    rw [map_pow, map_natCast]
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have := inv_smul_liftQ_mem_Z1D LA' (((l : ℕ) : O) ^ r) (by rw [he]; exact pow_ne_zero _ hl)
    hI' c'.1 c'.2
  rwa [he] at this

end GlobalTheory.DivLift
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def ioL (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) →ₗ[O] (V ⧸ L.T) :=
  (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T).liftQ
    (L.T.mkQ ∘ₗ (((algebraMap O LL ϖ)⁻¹ ^ r • (LinearMap.id : V →ₗ[LL] V)).restrictScalars O) ∘ₗ
      L.T.subtype) (by
    intro x hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.coe_smul,
      LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [← algebraMap_smul LL (ϖ ^ r) (y : V), smul_smul, map_pow, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simpa using y.2
      · rw [h, inv_zero, zero_mul, zero_pow hr.ne', zero_smul]; exact L.T.zero_mem
    · rw [inv_mul_cancel₀ h, one_pow, one_smul]; exact y.2)

theorem ioL_mk (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (y : ↥L.T) :
    ioL L ϖ r (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • (y : V)) := rfl

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def cupQ (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O)
    (r : ℕ) (c : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (c' : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T)) (x : G × G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (c x.1)) (ρ' x.1 (Formalism.MainNotions.LocalSituation.liftQ L' _ (c' x.2)))

end GlobalTheory.BKFinLevel
end
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPoly

theorem aeval_mem_of_stable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (p : L[X]) : ∀ x ∈ D, Polynomial.aeval f p x ∈ D := by
  induction p using Polynomial.induction_on with
  | C a => intro x hx; simpa [Module.algebraMap_end_apply] using D.smul_mem a hx
  | add p q hp hq => intro x hx; simpa using D.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    have := ih _ (hD x hx)
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact this

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ (g * h) x = actVB PC.PD ρ g (actVB PC.PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_one' (x : V ⊗[Qp] B) : actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_resH (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_Dpcris_iff (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ g ∈ PC.H, actVB PC.PD ρ g x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, actVB_resH, Subtype.forall]

theorem Dpcris_stable (g : G) : ∀ x ∈ PC.Dpcris ρ, actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  intro x hx
  rw [mem_Dpcris_iff] at hx ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ PC.H := by simpa using PC.normal.conj_mem h hh g⁻¹
  rw [← actVB_mul', show h * g = g * (g⁻¹ * h * g) by group, actVB_mul', hx _ h1]

end

end GlobalTheory.PassPoly

end
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.exists_pow_p_smul_mem_one_fractionRing : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    PadicCoeff p O → ∀ y : FractionRing O,
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := by
  first | exact @GlobalTheory.padicCoeff_exists_pow_smul_mem_one | exact GlobalTheory.padicCoeff_exists_pow_smul_mem_one | (intros; apply GlobalTheory.padicCoeff_exists_pow_smul_mem_one <;> assumption)
end
