module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle611
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.CoefDescent

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {E E' : Type} [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
    {O O' : Type} [CommRing O] [Algebra O E] [CommRing O'] [Algebra O' E']

theorem blochKatoCocycle_comp_equivariant_map
    {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
    [Module O V] [IsScalarTower O E V] {ρ : Representation E G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul E V]
    {V' : Type} [AddCommGroup V'] [Module E' V'] [Module Qp V'] [IsScalarTower Qp E' V']
    [Module O' V'] [IsScalarTower O' E' V'] {ρ' : Representation E' G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul E' V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O') ρ') (φ : V →ₗ[Qp] V')
    (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (hc : Continuous φ) (hT : ∀ x ∈ L.T, φ x ∈ L'.T)
    (c : G → V) (h : c ∈ latticeFiniteCocycles PD L) : (fun g => φ (c g)) ∈ latticeFiniteCocycles PD L' := by
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, -, x, hx⟩ := h
  have hz : (fun g => φ (c g)) ∈ continuousCocycles ρ' := by
    refine ⟨hc.comp hc1, fun g h => ?_⟩
    change φ (c (g * h)) = φ (c g) + ρ' g (φ (c h))
    rw [hc2, map_add (f := _), he]
  refine ⟨⟨hz, fun g _ => hT _ (hc3 g (Set.mem_univ g))⟩, hz, LinearMap.rTensor B φ x, fun g => ?_⟩
  have key : ∀ y : V ⊗[Qp] B, LinearMap.rTensor B φ (actVB PD ρ g y) =
      actVB PD ρ' g (LinearMap.rTensor B φ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← key, ← map_sub, ← hx, LinearMap.rTensor_tmul]

theorem liftF_of_retract
    {V₁ : Type} [AddCommGroup V₁] [Module E V₁] [Module Qp V₁] [IsScalarTower Qp E V₁]
    [Module O V₁] [IsScalarTower O E V₁] {ρ₁ : Representation E G V₁}
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul E V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module E V₂] [Module Qp V₂] [IsScalarTower Qp E V₂]
    [Module O V₂] [IsScalarTower O E V₂] {ρ₂ : Representation E G V₂}
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul E V₂]
    {W₁ : Type} [AddCommGroup W₁] [Module E' W₁] [Module Qp W₁] [IsScalarTower Qp E' W₁]
    [Module O' W₁] [IsScalarTower O' E' W₁] {σ₁ : Representation E' G W₁}
    [TopologicalSpace W₁] [ContinuousAdd W₁] [ContinuousConstSMul E' W₁]
    {W₂ : Type} [AddCommGroup W₂] [Module E' W₂] [Module Qp W₂] [IsScalarTower Qp E' W₂]
    [Module O' W₂] [IsScalarTower O' E' W₂] {σ₂ : Representation E' G W₂}
    [TopologicalSpace W₂] [ContinuousAdd W₂] [ContinuousConstSMul E' W₂]
    {L₁ : Lattice (O := O) ρ₁} {L₂ : Lattice (O := O) ρ₂}
    {M₁ : Lattice (O := O') σ₁} {M₂ : Lattice (O := O') σ₂}
    (F : LatHom L₁ L₂) (F' : LatHom M₁ M₂)
    (ι : V₂ →ₗ[Qp] W₂) (R₁ : W₁ →ₗ[Qp] V₁) (R₂ : W₂ →ₗ[Qp] V₂)
    (ιe : ∀ g x, ι (ρ₂ g x) = σ₂ g (ι x)) (ιc : Continuous ι) (ιT : ∀ x ∈ L₂.T, ι x ∈ M₂.T)
    (R₁e : ∀ g x, R₁ (σ₁ g x) = ρ₁ g (R₁ x)) (R₁c : Continuous R₁) (R₁T : ∀ x ∈ M₁.T, R₁ x ∈ L₁.T)
    (R₂e : ∀ g x, R₂ (σ₂ g x) = ρ₂ g (R₂ x)) (R₂T : ∀ x ∈ M₂.T, R₂ x ∈ L₂.T)
    (hret : ∀ x, R₂ (ι x) = x) (hF : ∀ x, R₂ (F'.f x) = F.f (R₁ x))
    (e : ℕ) (h : F'.LiftF PD e) : F.LiftF PD e := by
  intro c hc
  have h1 := h _ (blochKatoCocycle_comp_equivariant_map PD L₂ M₂ ι ιe ιc ιT c hc)
  obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨y, hy, rfl⟩, hsum⟩ := Submodule.mem_sup.1 h1
  refine Submodule.mem_sup.2 ⟨_, ⟨_, blochKatoCocycle_comp_equivariant_map PD M₁ L₁ R₁ R₁e R₁c R₁T d hd, rfl⟩, _,
    ⟨R₂ y, R₂T y hy, rfl⟩, ?_⟩
  funext g
  have h2 := congrArg R₂ (congrFun hsum g)
  change R₂ (F'.f (d g) + (σ₂ g y - y)) = R₂ (((PD.p : O') ^ e) • ι (c g)) at h2
  change F.f (R₁ (d g)) + (ρ₂ g (R₂ y) - R₂ y) = ((PD.p : O) ^ e) • c g
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, hret, map_add (f := _), map_sub, hF, R₂e] at h2
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, h2]

end General

section Maps
variable {Qp E E' : Type} [Field Qp] [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
  {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module Qp V'] [IsScalarTower Qp E V']
  {k k' : ℕ}

def emb (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) : V →ₗ[Qp] (Fin k → E') :=
  LinearMap.pi fun i => j.toLinearMap ∘ₗ (b.coord i).restrictScalars Qp

theorem emb_apply (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (v : V) (i : Fin k) :
    emb j b v i = j (b.repr v i) := rfl

def ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) : (Fin k → E') →ₗ[Qp] V :=
  (b.equivFun.symm.toLinearMap.restrictScalars Qp) ∘ₗ LinearMap.compLeft r (Fin k)

theorem ret_apply (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') :
    ret r b w = ∑ i, r (w i) • b i := by
  simp [ret, Module.Basis.equivFun_symm_apply]

theorem repr_ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') (i : Fin k) :
    b.repr (ret r b w) i = r (w i) := by
  rw [ret_apply]; simp [Finsupp.single_apply]

theorem ret_emb (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x) (h1 : r 1 = 1)
    (b : Module.Basis (Fin k) E V) (v : V) : ret r b (emb j b v) = v := by
  refine b.ext_elem fun i => ?_
  have := hr (b.repr v i) 1
  rw [mul_one, h1, mul_one] at this
  rw [repr_ret, emb_apply, this]

theorem emb_map (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (v : V) :
    emb j b' (f v) = ((LinearMap.toMatrix b b' f).map j).mulVec (emb j b v) := by
  funext i
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f v) i
  rw [emb_apply, ← this]
  simp [Matrix.mulVec, dotProduct, emb_apply]

theorem ret_map (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x)
    (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (w : Fin k → E') :
    ret r b' (((LinearMap.toMatrix b b' f).map j).mulVec w) = f (ret r b w) := by
  refine b'.ext_elem fun i => ?_
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f (ret r b w)) i
  rw [repr_ret, ← this]
  simp [Matrix.mulVec, dotProduct, repr_ret, hr]

end Maps




theorem liftF_descends : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {K₀ K B BdR : Type} [Field K₀] [Field K] [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B] [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR] (PD : PeriodData G ℚ_[l] K₀ K B BdR) (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1), (∀ a x, r (incl hL a * x) = a * r x) → r 1 = 1 → (∀ x ∈ OL LL', r x ∈ OL LL) → Continuous r → ∀ e : ℕ, (extHom hL hb₁ hb₂ F).LiftF PD e → F.LiftF PD e := by
  intro l _ G _ _ K₀ K B BdR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PD LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr h1
    hint hrc e h
  have hincl : Continuous (incl hL) := continuous_subtype_val.subtype_mk _
  have retT : ∀ {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ} {b : Module.Basis (Fin k) ↥LL.1 T.V},
      IsLatBasis T b → ∀ x ∈ intVec LL' k, ret r b x ∈ T.L.T := by
    intro T k b hb x hx
    rw [ret_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := T.L.T.smul_mem (⟨r (x i), hint _ (hx i)⟩ : ↥(OL LL)) (hb.1 i)
    rwa [← algebraMap_smul ↥LL.1] at this
  refine liftF_of_retract PD F (extHom hL hb₁ hb₂ F) (emb (incl hL) b₂) (ret r b₁) (ret r b₂)
    (fun g x => emb_map (incl hL) b₂ b₂ (T₂.ρ g) x) ?_ ?_
    (fun g x => ret_map (incl hL) r hr b₁ b₁ (T₁.ρ g) x) ?_ (retT hb₁)
    (fun g x => ret_map (incl hL) r hr b₂ b₂ (T₂.ρ g) x) (retT hb₂)
    (ret_emb (incl hL) r hr h1 b₂) (fun x => ret_map (incl hL) r hr b₁ b₂ F.f x) e h
  · exact continuous_pi fun i => hincl.comp (IsModuleTopology.continuous_of_linearMap (b₂.coord i))
  · intro x hx i
    exact incl_integral hL (hb₂.2 x hx i)
  · have hc : Continuous (b₁.equivFun.symm.toLinearMap) := IsModuleTopology.continuous_of_linearMap _
    exact hc.comp (continuous_pi fun i => hrc.comp (continuous_apply i))

end GlobalTheory.CoefDescent
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.CoefRetraction

theorem exists_retraction (A K L : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral A x → ∃ a : A, algebraMap A K a = r x := by
  classical
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.Free A (integralClosure A L) :=
    IsIntegralClosure.module_free A K L (integralClosure A L)
  have : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.finite A K L (integralClosure A L)
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L (integralClosure A L)

  let b := Module.Free.chooseBasis A (integralClosure A L)
  let bL := b.localizationLocalization K (nonZeroDivisors A) L
  have hrepr : ∀ (z : integralClosure A L) i,
      bL.repr (algebraMap (integralClosure A L) L z) i = algebraMap A K (b.repr z i) :=
    fun z i => b.localizationLocalization_repr_algebraMap K (nonZeroDivisors A) L z i

  have hspan : (1 : A) ∈ Ideal.span (Set.range fun i => b.repr 1 i) := by
    obtain ⟨d, hd⟩ : ∃ d : A, Ideal.span (Set.range fun i => b.repr 1 i) = Ideal.span {d} :=
      ⟨Submodule.IsPrincipal.generator (Ideal.span (Set.range fun i => b.repr 1 i)),
        (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
    have hdiv : ∀ i, ∃ e : A, e * d = b.repr 1 i := fun i => by
      have hi : b.repr 1 i ∈ Ideal.span (Set.range fun i => b.repr 1 i) :=
        Ideal.subset_span ⟨i, rfl⟩
      rw [hd] at hi
      exact Ideal.mem_span_singleton'.mp hi
    choose e he using hdiv
    set β : integralClosure A L := ∑ i, e i • b i with hβ
    have hdβ : d • β = 1 := by
      rw [hβ, Finset.smul_sum]
      conv_rhs => rw [← b.sum_repr 1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm, he i]
    have hL : algebraMap A L d * (β : L) = 1 := by
      have := congrArg (fun z : integralClosure A L => (z : L)) hdβ
      simpa [Algebra.smul_def] using this
    have hK : algebraMap K L (algebraMap A K d) * (β : L) = 1 := by
      rw [← IsScalarTower.algebraMap_apply]; exact hL
    have hd0 : algebraMap A K d ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hK; exact zero_ne_one hK
    have hint : IsIntegral A (algebraMap K L (algebraMap A K d)⁻¹) := by
      rw [map_inv₀, inv_eq_of_mul_eq_one_right hK]
      exact β.2
    have hint' : IsIntegral A (algebraMap A K d)⁻¹ :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp hint
    obtain ⟨u, hu⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
    have hud : u * d = 1 := by
      apply IsFractionRing.injective A K
      rw [map_mul, hu, map_one, inv_mul_cancel₀ hd0]
    rw [hd, ← hud]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self d)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan
  refine ⟨∑ i, algebraMap A K (a i) • bL.coord i, ?_, ?_⟩
  · have h1 : (1 : L) = algebraMap (integralClosure A L) L 1 := (map_one _).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [h1]
    simp only [hrepr]

    rw [← map_one (algebraMap A K), ← ha, map_sum]
    simp only [map_mul]
  · intro x hx
    set z : integralClosure A L := ⟨x, show x ∈ integralClosure A L from hx⟩ with hz
    have hx' : x = algebraMap (integralClosure A L) L z := rfl
    refine ⟨∑ i, a i * b.repr z i, ?_⟩
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [hx']
    simp only [hrepr]

    rw [map_sum]
    simp only [map_mul]

theorem exists_retraction_closure (R F K L : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [FiniteDimensional F K]
    [IsPrincipalIdealRing (integralClosure R K)]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral R x → IsIntegral R (r x) := by
  have : IsScalarTower (integralClosure R K) K L := inferInstance
  have : IsFractionRing (integralClosure R K) K :=
    integralClosure.isFractionRing_of_finite_extension F K
  have : IsScalarTower R (integralClosure R K) L := IsScalarTower.of_algebraMap_eq fun y => by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply (integralClosure R K) K L]
    rfl
  obtain ⟨r, hr1, hr⟩ := exists_retraction (integralClosure R K) K L
  refine ⟨r, hr1, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hr x (hx.tower_top)
  rw [← ha]
  exact a.2

theorem exists_integral_retraction : ∀ (l : ℕ) [Fact l.Prime] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1),
    ∃ r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ a x, r (incl hL a * x) = a * r x) ∧ r 1 = 1 ∧
      (∀ x ∈ OL LL', r x ∈ OL LL) := by
  intro l _ LL LL' hL
  letI : Algebra ↥LL.1 ↥LL'.1 := (incl hL).toRingHom.toAlgebra
  have hmap : ∀ y : ↥LL.1, algebraMap ↥LL.1 ↥LL'.1 y = incl hL y := fun _ => rfl
  have : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun q => by
    rw [hmap, AlgHom.commutes]
  have : IsScalarTower ℤ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun z => by
    rw [hmap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, AlgHom.commutes]
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  have : FiniteDimensional ↥LL.1 ↥LL'.1 := FiniteDimensional.right ℚ_[l] ↥LL.1 ↥LL'.1
  have : IsPrincipalIdealRing (integralClosure ℤ_[l] ↥LL.1) := by
    obtain ⟨h, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact h.toIsPrincipalIdealRing
  obtain ⟨r, hr1, hr⟩ := exists_retraction_closure ℤ_[l] ℚ_[l] ↥LL.1 ↥LL'.1
  refine ⟨r.restrictScalars ℚ_[l], fun a x => ?_, hr1, fun x hx => hr x hx⟩
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, ← hmap, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.CoefRetraction
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.TameInertiaCyclic GlobalTheory.MemLoc.FrobLaws

noncomputable section
namespace GlobalTheory.NearRoot

variable {l : ℕ} [hl : Fact l.Prime]

theorem ratio_one (g : GQ l) : GlobalTheory.TameInertiaCyclic.ratio g 1 = 1 :=
  Subtype.ext (by show g 1 / 1 = 1; simp)

theorem ratio_pow (g : GQ l) (x : Om l) (n : ℕ) :
    GlobalTheory.TameInertiaCyclic.ratio g (x ^ n) = GlobalTheory.TameInertiaCyclic.ratio g x ^ n := by
  induction n with
  | zero => simpa using ratio_one g
  | succ n ih => rw [pow_succ, GlobalTheory.TameInertiaCyclic.ratio_mul, ih, pow_succ]

theorem norm_natCast_lt_one : ‖(l : Om l)‖ < 1 := by
  have h : ‖((l : ℚ_[l]) : Om l)‖ < 1 := by
    rw [PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
  simpa using h

theorem natCast_ne_zero : (l : Om l) ≠ 0 := by
  have h : ((l : ℚ_[l]) : Om l) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] (Om l)).injective]
    exact_mod_cast hl.out.ne_zero
  simpa using h

theorem exists_unif (F : FinExt l) :
    ∃ ϖ ∈ F.1, ϖ ≠ 0 ∧ (∀ x ∈ F.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖ϖ ^ k‖) ∧
      ∃ E : ℕ, 0 < E ∧ ‖ϖ‖ ^ E = ‖(l : Om l)‖ := by
  obtain ⟨π, hπ, hπ0, hgen⟩ := GlobalTheory.TameInertiaCyclic.exists_gen F
  have hlF : (l : Om l) ∈ F.1 := natCast_mem _ l
  obtain ⟨k0, hk0⟩ := hgen _ hlF natCast_ne_zero
  have hk0' : k0 ≠ 0 := by
    rintro rfl
    have := norm_natCast_lt_one (l := l)
    rw [hk0] at this
    simp at this
  rcases lt_or_gt_of_ne hk0' with hneg | hpos
  · refine ⟨π⁻¹, inv_mem hπ, inv_ne_zero hπ0, fun x hx hx0 => ?_, (-k0).toNat, by omega, ?_⟩
    · obtain ⟨k, hk⟩ := hgen x hx hx0
      exact ⟨-k, by rw [hk, _root_.inv_zpow', neg_neg]⟩
    · rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), _root_.inv_zpow', neg_neg]
  · refine ⟨π, hπ, hπ0, hgen, k0.toNat, by omega, ?_⟩
    rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

theorem near_root : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ := by
  intro l _ F
  obtain ⟨ϖ, hϖ, hϖ0, hgen, E, hE, hEn⟩ := exists_unif F
  obtain ⟨s, M, hlM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hE.ne' l (Fact.out : l.Prime).ne_one
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hlM)
  refine ⟨M, hM, hlM, fun ρ hρ g hg hgρ x hx hx0 => ?_⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne', eq_comm, neg_eq_zero] at hρ
    exact natCast_ne_zero hρ
  have hq0 : ϖ ^ (l ^ s) ≠ 0 := pow_ne_zero _ hϖ0
  have hnq : ‖ϖ ^ (l ^ s)‖ = ‖ρ‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 ?_
    rw [← norm_pow, ← pow_mul, norm_pow, hEn, ← norm_pow, hρ, norm_neg]
  set u := ϖ ^ (l ^ s) / ρ with hu
  have hu0 : u ≠ 0 := div_ne_zero hq0 hρ0
  have hnu : ‖u‖ = 1 := by rw [hu, norm_div, hnq, div_self (norm_ne_zero_iff.2 hρ0)]
  have h1 : res (GlobalTheory.TameInertiaCyclic.ratio g u) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hu0, hnu]; exact hg u hnu.le
  have h2 : res (GlobalTheory.TameInertiaCyclic.ratio g ρ) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hρ0, hgρ, sub_self, norm_zero]
    exact norm_pos_iff.2 hρ0
  have h3 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) ^ (l ^ s) = 1 := by
    rw [← map_pow, ← ratio_pow, ← div_mul_cancel₀ (ϖ ^ (l ^ s)) hρ0, ← hu,
      GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h1, h2, one_mul]
  have h4 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) = 1 := by
    have h5 : (res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) - 1) ^ (l ^ s) = 0 := by
      rw [sub_pow_char_pow, h3, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h5)
  obtain ⟨k, hk⟩ := hgen x hx hx0
  have hp : ϖ ^ k ≠ 0 := zpow_ne_zero k hϖ0
  have hv : ‖x / ϖ ^ k‖ = 1 := by rw [norm_div, hk, div_self (norm_ne_zero_iff.2 hp)]
  have h6 : res (GlobalTheory.TameInertiaCyclic.ratio g (x / ϖ ^ k)) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff _ (div_ne_zero hx0 hp), hv]
    exact hg _ hv.le
  rw [← GlobalTheory.TameInertiaCyclic.res_ratio_iff _ hx0, ← div_mul_cancel₀ x hp,
    GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h6,
    GlobalTheory.TameInertiaCyclic.res_ratio_zpow _ hϖ0 h4, one_mul]

end GlobalTheory.NearRoot
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.exists_unitary_supported_at_split_place_lift : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N : ℕ), IsBaseFrame S βS Λ N → ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), ∃ κ : GA D S, SuppAt e S κ ∧ κ ∈ GfC S ∧ finE S κ ∈ St βS ∧ (redFn βS PP (finE S κ)).val.map ι = h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) ∧ (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T κ 1 x) = h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * rdAdj S T βS βT φ x := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_supp_lift_adj | exact GlobalTheory.DownLift.SplitCoef.exists_supp_lift_adj | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_supp_lift_adj <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.galoisRepTuple_relation_mem_pow_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (c N : ℕ) (cs : Fin m → Om l), (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∀ G : Γ →₀ ℤ_[l], (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = 0 → ∃ f' : Γ →₀ ℤ_[l], (G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ N • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) := by
  first | (exact @GlobalTheory.CovKer.kerB) | (exact GlobalTheory.CovKer.kerB) | (intros; apply GlobalTheory.CovKer.kerB  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.trace_estimate_scaledProductSpanLattice : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (c N n : ℕ) (cs : Fin m → Om l), n ≤ N → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t M → ‖(F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  first | (exact @GlobalTheory.trace_estimate_latL) | (exact GlobalTheory.trace_estimate_latL) | (intros; apply GlobalTheory.trace_estimate_latL  <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.frobeniusSolution_expansion_mod_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.Expand.expand | exact GlobalTheory.ExpImage.Expand.expand | (intros; apply GlobalTheory.ExpImage.Expand.expand <;> assumption)
end
