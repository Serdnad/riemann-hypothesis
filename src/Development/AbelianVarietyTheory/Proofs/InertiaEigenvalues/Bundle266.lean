module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.BasicDefinitions.ExistsUnique
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.TopSteps

theorem mem_cob_of_repr_mem_herrB : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (z : G → Fin A.m → k)
    (b g : ZMod n → Vc k A.m), Repr F A z b g → (b, g) ∈ herrB (F.D A) → z ∈ cob A := by
  intro k G _ _ l n _ _ _ R F A z b g hR hB
  obtain ⟨E, a, p, e, ε, hE, ha, hp, hinj, hex, hpe, hρe, hε⟩ := hR
  unfold GlobalTheory.Models.herrB at hB
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hB

  have hbx : ∀ i, b i = (F.D A).φ i (x (i - 1)) - x i := fun i => by
    have h := congrArg (fun q => q.1 i) hx
    simp at h
    exact h.symm
  have hgx : ∀ i, g i = (F.D A).γ i (x i) - x i := fun i => by
    have h := congrArg (fun q => q.2 i) hx
    simp at h
    exact h.symm
  have hA : F.Obj A := F.obj_sub A E a ha hinj hE
  have h1 : F.Obj (GlobalTheory.Models.chr (1 : G →* kˣ)) := F.obj_one

  set η : ZMod n → Vc k E.m := fun i => ε i - F.map A E a i (x i) with hη
  have hηφ : ∀ i, (F.D E).φ i (η (i - 1)) = η i := by
    intro i
    have h2 := (hε i).2.1
    rw [hbx i, map_sub, F.map_φ A E a hA hE ha] at h2
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2.symm
  have hηγ : ∀ i, (F.D E).γ i (η i) = η i := by
    intro i
    have h3 := (hε i).2.2
    rw [hgx i, map_sub, F.map_γ A E a hA hE ha] at h3
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h3.symm
  obtain ⟨f, hf, hfη⟩ := F.fix E hE η hηφ hηγ

  have hmap0 : ∀ i y, F.map A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 i y = 0 := by
    intro i y
    have h := F.map_smul A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 0 hA h1 (fun _ _ => by simp) i y
    simpa using h
  have hpa : p ∘ₗ a = 0 := LinearMap.ext fun y => hex.apply_apply_eq_zero y
  have hpa_map : ∀ i y, F.map E (GlobalTheory.Models.chr (1 : G →* kˣ)) p i (F.map A E a i y) = 0 := by
    intro i y
    have h := F.map_comp A E (GlobalTheory.Models.chr (1 : G →* kˣ)) a p hA hE h1 ha hp i
    rw [hpa] at h
    have h' := LinearMap.congr_fun h y
    simpa [hmap0] using h'.symm

  set one : Fin 1 → k := fun _ => 1 with hone
  set c : k := p (f one) 0 with hc
  have hqc : ∀ v : Fin 1 → k, p (f v) = c • v := by
    intro v
    have hv : v = v 0 • one := funext fun j => by
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [hone]
    rw [hv, map_smul, map_smul]
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [hc, hone, mul_comm]
  have hq : p ∘ₗ f = c • LinearMap.id := LinearMap.ext fun v => by simp [hqc]
  have hidH : GlobalTheory.Models.IsHom (GlobalTheory.Models.chr (1 : G →* kˣ)) (GlobalTheory.Models.chr (1 : G →* kˣ)) LinearMap.id :=
    fun _ _ => rfl

  have hcu : c • F.unit 0 = F.unit 0 := by
    have hcomp := F.map_comp _ E _ f p h1 hE h1 hf hp 0
    have hval := LinearMap.congr_fun hcomp (F.unit 0)
    rw [LinearMap.comp_apply, hfη 0, hη, map_sub, (hε 0).1, hpa_map, sub_zero, hq,
      F.map_smul _ _ _ c h1 h1 hidH, F.map_id _ h1] at hval
    simpa using hval
  have hc1 : c = 1 := by
    by_contra hne
    have hu : (c - 1) • F.unit 0 = 0 := by rw [sub_smul, one_smul, hcu, sub_self]
    apply F.unit_ne 0
    have h := inv_smul_smul₀ (sub_ne_zero.mpr hne) (F.unit 0)
    rw [hu, smul_zero] at h
    exact h.symm

  have hpw : p (f one) = one := by rw [hqc, hc1, one_smul]
  have hρ1 : ∀ σ (v : Fin 1 → k), (GlobalTheory.Models.chr (1 : G →* kˣ)).ρ σ v = v := fun σ v => by
    change ((1 : G →* kˣ) σ : k) • LinearMap.id v = v
    simp
  have hw : ∀ σ, E.ρ σ (f one) = f one := fun σ => by
    rw [← hf σ one, hρ1]

  have hker : p (e - f one) = 0 := by rw [map_sub, hpe, hpw, sub_self]
  obtain ⟨y, hy⟩ := (hex (e - f one)).1 hker
  have hkey : ∀ σ, A.ρ σ y = y + z σ := fun σ => by
    apply hinj
    rw [ha σ y, hy, map_sub, hρe σ, hw σ, map_add (f := _), hy]
    abel
  unfold GlobalTheory.Models.cob
  refine LinearMap.mem_range.mpr ⟨y, funext fun σ => ?_⟩
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [hkey σ]
  abel

end GlobalTheory.TopSteps
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem GlobalTheory.admissible_eventually_iff_mem_cls : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0) →
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) →
    ∀ z : ↥(Z1 (twCoef W S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea W S.Γ.χ₁ ha z)) ↔
        Submodule.Quotient.mk z ∈ S.cls W X) := by
  intro l _ P S M _ _ W X _ _ _ hX hlev z
  constructor
  · rintro ⟨a₀, h⟩
    obtain ⟨a₁, h1⟩ := hX
    have hle1 : a₁ ≤ max a₀ (max a₁ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
    have ha : ∀ x : X, S.Γ.lam ^ (max a₀ (max a₁ 1)) • x = 0 := by
      intro x
      rw [← Nat.sub_add_cancel hle1, pow_add, mul_smul, h1, smul_zero]
    have hA := h (max a₀ (max a₁ 1)) (le_max_left _ _) ha
    have hone : 1 ≤ max a₀ (max a₁ 1) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hlev _ ha hone]
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mpr hA
  · intro h
    refine ⟨1, fun a ha1 ha => ?_⟩
    rw [hlev a ha ha1] at h
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mp h
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.Cut.Coc

theorem KOG_torsion {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (t : KOG O k) :
    ∃ d : O, d ≠ 0 ∧ d • t = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) v
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  choose u hu using hb
  exact ⟨u, funext fun j => hu j⟩

theorem smul_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k : ℕ} (t : KOG O k) :
    Continuous fun a : O => a • t := by
  obtain ⟨d, hd, hdt⟩ := KOG_torsion t
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.mp hO).1 n
  have hk : ∀ a ∈ (IsLocalRing.maximalIdeal O ^ n : Ideal O), a • t = 0 := by
    intro a ha
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have : c * ϖ ^ n = (c * ((u⁻¹ : Oˣ) : O)) * (u * ϖ ^ n) := by
      rw [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, mul_smul, hdt, smul_zero]
  refine continuous_of_continuousAt_zero (LinearMap.toSpanSingleton O (KOG O k) t) ?_
  refine (continuousAt_const (y := (0 : KOG O k))).congr ?_
  filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
  exact (hk a ha).symm

theorem lin_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k n : ℕ} {X : Type} [Fintype X]
    [DecidableEq X] (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] KOG O k) : Continuous φ := by
  have h : ∀ y : X → Matrix (Fin n) (Fin n) O,
      φ y = ∑ x, ∑ p, ∑ q, y x p q • φ (Pi.single x (Matrix.single p q 1)) := by
    intro y

    simp only [← map_smul, ← map_sum]
    apply congrArg φ
    funext x
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp only [Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single (y x)
    · intro b _ hb
      simp [Pi.smul_apply, Pi.single_eq_of_ne hb.symm]
    · simp
  rw [show (φ : _ → _) = _ from funext h]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_
  exact (smul_cont hO _).comp (by fun_prop : Continuous fun y : X → Matrix (Fin n) (Fin n) O => y x p q)

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

def tw (g : GE D.nd) : S.X' → MatN D.nd i :=
  fun x' => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rO D.nd i r (S.p x') g

theorem tw_mem (g : GE D.nd) : InR' D.nd r S (tw i r S g) := by
  refine ⟨1, fun _ _ => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => g,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  rw [Fin.sum_univ_one]
  rfl

theorem yg_mem (g : GE D.nd) : InY D.nd r S (yg D.nd r S g) := by
  refine ⟨1, fun _ => tw i r S 1, fun _ => g, fun _ => tw_mem i r S 1, ?_⟩
  rw [Fin.sum_univ_one]
  funext x'
  simp [tw]

theorem yg_mul (g h : GE D.nd) :
    yg D.nd r S (g * h) = yg D.nd r S g + tw i r S g * yg D.nd r S h := by
  funext x'
  simp only [yg, tw, Pi.add_apply, Pi.mul_apply, map_mul, mul_inv, Units.val_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, mul_smul, mul_assoc]
  rw [smul_comm]
  abel

theorem yg_cont (hr : GoodR D.nd i r) : Continuous fun g => yg D.nd r S g := by
  refine continuous_pi fun x' => ?_
  have hc : Continuous fun g => rO D.nd i r (S.p x') g := (hr (S.p x')).1
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine ((h1.smul (hc.mul (continuous_const (y := Eel D.nd S x')))).sub
    (continuous_const (y := Eel D.nd S x'))).congr fun g => ?_
  simp [yg]

theorem cocW_le (hr : GoodR D.nd i r) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hψ : ∀ g, ψ (tw i r S g) = M g) :
    cocW i r S Xs ψ ≤ Z1 (WKG M) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, hφ, -, rfl⟩
  refine ⟨(lin_cont (D.nd.O_adic i) φ).comp (yg_cont i r S hr), fun g h => ?_⟩
  show φ _ = φ _ + WKG M g (φ _)
  rw [yg_mul, map_add (f := _), hφ _ (tw_mem i r S g) _ (yg_mem i r S h), hψ]
  rfl

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : GoodCongruenceObjects D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [tw, hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.Coc

end
end

section

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem cutVal_exists_single {O X : Type} [CommRing O] [IsDomain O] [Fintype X]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g ∈ T, g x ≠ 0 ∧ ∀ y, y ≠ x → g y = 0 := by
  classical
  have key : ∀ y : X, ∃ f ∈ T, f x ≠ 0 ∧ (y ≠ x → f y = 0) := by
    intro y
    by_cases hy : y = x
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hy h⟩
    · obtain ⟨f, hf, hne⟩ := hsep y x hy
      refine ⟨f - algebraMap _ _ (f y), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  refine ⟨∏ y, f y, prod_mem fun y _ => hf y, ?_, fun y hy => ?_⟩
  · rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.2 fun y _ => h1 y
  · rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (h2 y hy)

theorem cutVal_coord_eq_zero {O X X' ι : Type} [CommRing O] [IsDomain O] [Fintype X] [Fintype ι]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (p : X' → X) (b : ι → X' → O)
    (huniq : ∀ cf : ι → T, (0 : X' → O) = ∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k →
      cf = 0)
    (cf : ι → T) (x : X)
    (h0 : ∀ x', p x' = x → (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' = 0)
    (k : ι) : (cf k : X → O) x = 0 := by
  obtain ⟨g, hg, hx, hy⟩ := cutVal_exists_single T hsep x
  have h := huniq (fun k => ⟨g, hg⟩ * cf k) (by
    funext x'
    have : (∑ k, ((fun x' => (((⟨g, hg⟩ : T) * cf k : T) : X → O) (p x')) : X' → O) * b k) x' =
        g (p x') * (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' := by
      simp [Finset.sum_apply, Finset.mul_sum, mul_assoc]
    rw [this]
    by_cases hp : p x' = x
    · rw [h0 x' hp]; simp
    · rw [hy _ hp]; simp)
  have h2 : g x * (cf k : X → O) x = 0 := by
    have := congrArg (fun c : ι → T => (c k : X → O) x) h
    simpa using this
  exact (mul_eq_zero.1 h2).resolve_left hx

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

end GlobalTheory.Cut
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Peel

theorem length_eq_inf_ker_add_map {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (C : Submodule R M) :
    Module.length R ↥C = Module.length R ↥(C ⊓ LinearMap.ker f) + Module.length R ↥(C.map f) := by
  refine Module.length_eq_add_of_exact (Submodule.inclusion (inf_le_left : C ⊓ LinearMap.ker f ≤ C))
    (f.submoduleMap C) (Submodule.inclusion_injective _) (f.submoduleMap_surjective C) ?_
  intro y
  constructor
  · intro hy
    have hy' : f y = 0 := by
      simpa [LinearMap.submoduleMap_coe_apply] using congrArg Subtype.val hy
    exact ⟨⟨y.1, y.2, hy'⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    ext
    simpa [LinearMap.submoduleMap_coe_apply] using z.2.2

theorem exists_le_map_eq_bot {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N : ι → Type*} [∀ q, AddCommGroup (N q)] [∀ q, Module R (N q)] (f : ∀ q, M →ₗ[R] N q)
    (C : Submodule R M) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C'.map (f q) = ⊥) ∧
      Module.length R ↥C ≤ Module.length R ↥C' + ∑ q ∈ Q, Module.length R ↥(C.map (f q)) := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert q Q hq ih =>
    obtain ⟨C₀, hC₀, hmap, hlen⟩ := ih
    refine ⟨C₀ ⊓ LinearMap.ker (f q), inf_le_left.trans hC₀, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · rw [eq_bot_iff, ← hmap p hp]
        exact Submodule.map_mono inf_le_left
    · have hsplit := length_eq_inf_ker_add_map (f q) C₀
      have hle : Module.length R ↥(C₀.map (f q)) ≤ Module.length R ↥(C.map (f q)) :=
        Module.length_le_of_injective _ (Submodule.inclusion_injective (Submodule.map_mono hC₀))
      rw [Finset.sum_insert hq]
      calc Module.length R ↥C ≤ Module.length R ↥C₀ + ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := hlen
        _ = Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C₀.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by rw [← hsplit]
        _ ≤ Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by gcongr
        _ = _ := by rw [add_assoc]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : ℕ) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ q ∈ Q, resIne i C' q = ⊥) ∧ Module.length (D.nd.O i) ↥C ≤ Module.length (D.nd.O i) ↥C' + ∑ q ∈ Q, Module.length (D.nd.O i) ↥(resIne i C q) := by
  intro D i k C Q
  exact exists_le_map_eq_bot
    (fun q => LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) k)
      (Subtype.val : ↥(Ine (F := D.host.E) (D.nd.plOm.1 q)) → GE D.nd)) C Q

end GlobalTheory.Cut.Peel
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.ResidualSelmer

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → NoChiOff i r Xs → ∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → ∃ η : Fin D.R.nV → KK D.nd i, ∃ γ : GE D.nd, ((yg D.nd r S γ x').map (toK D.nd i)).mulVec η ≠ 0 := by
  intro D i r ρ π Xs S _ hG _ hN x' hx hZ
  have hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1 := hG.2.2.2.2.2.2.2.2.2.2.1.1 x'
  by_contra hcon
  push Not at hcon
  have h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0 := by
    intro η
    apply hN _ hx hZ
    intro g
    have h := hcon η g
    have hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x' := by
      unfold yg
      rw [← Matrix.smul_mul]
      rfl
    rw [hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0 := LinearMap.ext h0
  simp only [← Matrix.finrank_range_mulVecLin] at hrank
  rw [hz, LinearMap.range_zero, finrank_bot] at hrank
  exact zero_ne_one hrank

end GlobalTheory.Cut.ResidualSelmer
end
