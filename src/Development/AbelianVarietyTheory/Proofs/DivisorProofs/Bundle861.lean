module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Formalism.PieriBlockIdeals.PieriColumnMinors.DepthNonnegative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010

@[expose] public section

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame

theorem map_mk_smul_sum {O A : Type} [CommRing O] [Ring A] [Algebra O A] {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W] (U : Submodule A V)
    (ψ : U →ₗ[A] W) {κ : Type} (S : Finset κ) (c : O) (v : κ → V) (hv : ∀ s, v s ∈ U) (x : V) (hx : x ∈ U)
    (e : x = c • ∑ s ∈ S, v s) : c • ∑ s ∈ S, ψ ⟨v s, hv s⟩ = ψ ⟨x, hx⟩ := by
  have e' : (⟨x, hx⟩ : U) = c • ∑ s ∈ S, (⟨v s, hv s⟩ : U) := by
    apply Subtype.ext
    simpa using e

  rw [e', LinearMap.map_smul_of_tower, map_sum]

section
variable {O A G I : Type} [CommRing O] [Ring A] [Algebra O A] [Group G] (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A)
  (tr : I → Finset G) (cst : I → O)

theorem hecke_values_mem {V : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule A V) (t : MvPolynomial I O) :
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ U) →
      ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f hf g
    rw [hV.1 c f]
    exact U.smul_of_tower_mem c (hf g)
  | add p q hp hq =>
    intro f hf g
    rw [add_smul]
    exact U.add_mem (hp f hf g) (hq f hf g)
  | mul_X p i hp =>
    intro f hf g
    rw [mul_smul]
    apply hp
    intro g'
    rw [hV.2 i f g']
    exact U.smul_of_tower_mem _ (U.sum_mem fun s _ => hf _)

theorem hecke_values_map {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s))
    (U : Submodule A V)
    (ψ : U →ₗ[A] W) (t : MvPolynomial I O) :
    ∀ (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
      (hf : ∀ g, (f : G → V) g ∈ U), (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
      ∀ g (h : ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
        ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨_, h⟩ := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f φ hf hφ g h
    have e : (⟨_, h⟩ : U) = c • ⟨(f : G → V) g, hf g⟩ := by
      apply Subtype.ext
      simp only [hV.1 c f]
      rfl
    rw [e, LinearMap.map_smul_of_tower, ← hφ g, hW.1 c φ]
    rfl
  | add p q hp hq =>
    intro f φ hf hφ g h
    have hp' := hecke_values_mem Γ jK tr cst hV U p f hf g
    have hq' := hecke_values_mem Γ jK tr cst hV U q f hf g
    have e : (⟨_, h⟩ : U) = ⟨_, hp'⟩ + ⟨_, hq'⟩ := by
      apply Subtype.ext
      simp only [add_smul]
      rfl
    rw [e, map_add (f := _), ← hp f φ hf hφ g hp', ← hq f φ hf hφ g hq', add_smul]
    rfl
  | mul_X p i hp =>
    intro f φ hf hφ g h
    have hX := hecke_values_mem Γ jK tr cst hV U (X i) f hf
    have hφX : ∀ g', (((X i : MvPolynomial I O) • φ : Forms O Γ jK W) : G → W) g' = ψ ⟨_, hX g'⟩ := by
      intro g'
      refine (hW.2 i φ g').trans (Eq.trans ?_ (map_mk_smul_sum U ψ (tr i) (cst i) (fun s => (f : G → V) (g' * s))
        (fun s => hf _) _ (hX g') (hV.2 i f g')))
      exact congrArg (fun z => cst i • z) (Finset.sum_congr rfl fun s _ => hφ (g' * s))
    have h2 : ((p • ((X i : MvPolynomial I O) • f) : Forms O Γ jK V) : G → V) g ∈ U := by
      rw [← mul_smul]
      exact h
    have e : (⟨_, h⟩ : U) = ⟨_, h2⟩ := by
      apply Subtype.ext
      simp only [mul_smul]
    rw [e, mul_smul]
    exact hp _ _ hX hφX g h2

theorem hecke_stable_nat (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s)) :
    HeckeStable O Γ jK (MvPolynomial I O) V ∧ HeckeNat O Γ jK (MvPolynomial I O) V W :=
  ⟨fun U t f hf => hecke_values_mem Γ jK tr cst hV U t f hf,
    fun U ψ t f φ hf hf' hφ g => hecke_values_map Γ jK tr cst hV hW U ψ t f φ hf hφ g (hf' g)⟩

end



theorem heckeStable_heckeNat_of_isHecke : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  intro l _ ι _ _ N F lam jK i1 W i2 i3 i4 i5 i6 hV hW
  refine @hecke_stable_nat F.O (alg F.O N lam) F.G F.I _ _ _ _ F.Γ F.K jK F.tr F.cst (NablaT F.O N lam) W _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · exact hV
  · exact hW

end GlobalTheory.ExpFrame
end

section

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.ExpFrame Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

section Galois

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

def ofOL (LL : FinExt l) : ↥(OL LL) →+* PadicAlgCl l :=
  (LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)

def IntegralBlock (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ) : Prop :=
  ∃ (LL : FinExt l) (r : G E Ω →* GL (Fin n) ↥(OL LL)) (ψ : Fin t → G E Ω →* (↥(OL LL))ˣ) (ϖ : ↥(OL LL))
    (R : ℕ) (M : Fin (R + 1) → Submodule ↥(OL LL) (Fin n → ↥(OL LL))) (rs : Fin t → Fin R),
    (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧
    CrysWith ((Matrix.GeneralLinearGroup.map (ofOL l LL)).comp r) (fun τ => Finset.univ.val.map (J τ)) ∧
    (∀ s, CrysWith (GlobalTheory.TripleGal.rk1 ((Units.map (ofOL l LL).toMonoidHom).comp (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
    Irreducible ϖ ∧ (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → ↥(OL LL), x = fun a => ϖ * y a) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧
    (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x ∈ M k) ∧
    Function.Injective rs ∧
    ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧
      M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span ↥(OL LL) {x} ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x - (fun a => ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) * x a) ∈
        M (rs s).castSucc

end Galois

section Reduced

variable {F : Type} [Field F] {n : ℕ}

def lau (y : Fin n → F⟦X⟧) : Fin n → LaurentSeries F := fun a => ((y a : F⟦X⟧) : LaurentSeries F)

def phiV (l : ℕ) (P : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  P.mulVec fun a => frob0 l (y a)

def gamV (un : F⟦X⟧) (D : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  (1 + (X : F⟦X⟧) • D).mulVec fun a => gam0 0 un (y a)

def RedFilt {ι : Type} (σ : Equiv.Perm ι) (l : ℕ) {t : ℕ} (un : F⟦X⟧) (P D : ι → Matrix (Fin n) (Fin n) F⟦X⟧)
    (Pψ Dψ : Fin t → ι → F⟦X⟧) : Prop :=
  ∃ (R : ℕ) (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (rs : Fin t → Fin R)
    (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
    Function.Injective rs ∧
    (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
    (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
    (∀ i k y, lau y ∈ V (σ i) k → lau (phiV l (P i) y) ∈ V i k) ∧
    (∀ i k y, lau y ∈ V i k → lau (gamV un (D i) y) ∈ V i k) ∧
    (∀ i s, lau (e i s) ∉ V i (rs s).castSucc ∧
      V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {lau (e i s)}) ∧
    (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (phiV l (P i) (e (σ i) s)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : LaurentSeries F)) •
          lau (e i s) ∈ V i (rs s).castSucc) ∧
    ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (gamV un (D i) (e i s)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i : F⟦X⟧) : LaurentSeries F)) • lau (e i s) ∈ V i (rs s).castSucc

end Reduced

end GlobalTheory.WachBlock

end
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.BaseChangeIndep

theorem indep_pi {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {L : Type} [Field L] (emb : O →+* L)
    (hemb : Function.Injective emb) {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module L V]
    (b : M →ₛₗ[emb] V) (hbinj : Function.Injective b)
    (hb : ∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent L fun a => b (x a))
    {T : Type} [Finite T] (n : ℕ) (y : Fin n → T → M) (hy : LinearIndependent O y) :
    LinearIndependent L fun a t => b (y a t) := by
  classical
  haveI : Fintype T := Fintype.ofFinite T

  haveI : Module.IsTorsionFree O M := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m h
    have h1 : emb r • b m = 0 := by rw [← LinearMap.map_smulₛₗ, h, map_zero]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (hemb (by rw [h2, map_zero]))
    · exact Or.inr (hbinj (by rw [h2, map_zero]))

  let P : Submodule O M := Submodule.span O (Set.range fun p : Fin n × T => y p.1 p.2)
  haveI : Module.Finite O P := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))
  haveI : Module.Free O P := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O P
  let k := Module.finrank O P
  have hmem : ∀ a t, y a t ∈ P := fun a t => Submodule.subset_span ⟨(a, t), rfl⟩
  have he : LinearIndependent O fun i => ((e i : P) : M) :=
    e.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hbe : LinearIndependent L fun i => b (e i : M) := by
    have := hb k (fun i => (e i : M)) he
    exact this

  let Y : Fin n → T × Fin k → O := fun a p => e.repr ⟨y a p.1, hmem a p.1⟩ p.2
  let Φ : (T × Fin k → O) →ₗ[O] (T → M) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • ((e i : P) : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΦ : ∀ a, Φ (Y a) = y a := by
    intro a; funext t
    have h2 : ((∑ i, e.repr ⟨y a t, hmem a t⟩ i • e i : P) : M) = y a t := by rw [e.sum_repr]
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    change ∑ i, Y a (t, i) • ((e i : P) : M) = y a t
    exact h2
  have hY : LinearIndependent O Y := by
    apply LinearIndependent.of_comp Φ
    have : (Φ ∘ Y) = y := funext hΦ
    rw [this]; exact hy
  letI : Algebra O L := emb.toAlgebra
  haveI : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 hemb
  have hY' : LinearIndependent L fun a => algebraMap O L ∘ Y a :=
    linearIndependent_algebraMap_comp_iff.2 hY
  let Ψ : (T × Fin k → L) →ₗ[L] (T → V) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • b (e i : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro Z hZ
    funext p
    have h1 : ∑ i, Z (p.1, i) • b (e i : M) = 0 := congrFun hZ p.1
    have := (Fintype.linearIndependent_iff.1 hbe) (fun i => Z (p.1, i)) h1 p.2
    simpa using this
  have key := hY'.map' Ψ hΨ
  have hfam : (Ψ ∘ fun a => algebraMap O L ∘ Y a) = fun a t => b (y a t) := by
    funext a t
    change ∑ i, (algebraMap O L (Y a (t, i))) • b (e i : M) = b (y a t)
    rw [← hΦ a]

    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.map_smulₛₗ]
    rfl
  rw [hfam] at key
  exact key

end GlobalTheory.BaseChangeIndep

namespace GlobalTheory.BaseChangeIndep

theorem forms_indep : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok →
    (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) →
    ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x →
      LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  intro l _ ι _ _ N F mu jK b hbinj hOk hb n x hx
  obtain ⟨S, hS⟩ := hOk.classes
  let R : Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu) →ₗ[F.O] (S → NablaT F.O N mu) :=
    { toFun := fun f s => (f : F.G → NablaT F.O N mu) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf0
    apply Subtype.ext
    funext g
    obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
    have hf : ∀ (γ : F.Γ) (g : F.G) (κ : F.K), (f : F.G → NablaT F.O N mu) ((γ : F.G) * g * κ) =
        repOf F.O (A := alg F.O N mu) jK (NablaT F.O N mu) κ⁻¹ ((f : F.G → NablaT F.O N mu) g) := f.2
    have h0 : (f : F.G → NablaT F.O N mu) s = 0 := congrFun hf0 ⟨s, hs⟩
    have h1 := hf ⟨γ, hγ⟩ s ⟨κ, hκ⟩
    rw [h1, h0, map_zero]
    rfl
  have hx' : LinearIndependent F.O (R ∘ x) := hx.map' R hR
  have hOk1 := hOk.ring.1
  have key := indep_pi F.emb hOk1 b hbinj hb n (R ∘ x) hx'
  let R' : (F.G → NablaT (PadicAlgCl l) N mu) →ₗ[PadicAlgCl l] (S → NablaT (PadicAlgCl l) N mu) :=
    { toFun := fun f s => f s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp R'
  exact key

end GlobalTheory.BaseChangeIndep
end
end

section

open GlobalTheory.ExpFrame Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.FrameQuot

theorem finite_quot_prime (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N) (hF : F.Ok) :
    Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  obtain ⟨hinj, L, hL, hrange⟩ := hF.ring
  haveI := hL
  have hmem : ∀ x : F.O, F.emb x ∈ L ∧ ‖F.emb x‖ ≤ 1 := fun x => by
    have hx : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at hx
    exact hx
  let f : F.O →+* integralClosure ℤ_[l] L :=
    { toFun := fun x => ⟨⟨F.emb x, (hmem x).1⟩,
        (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨F.emb x, (hmem x).1⟩).2 (hmem x).2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one F.emb))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul F.emb x y))
      map_zero' := Subtype.ext (Subtype.ext (map_zero F.emb))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add F.emb x y)) }
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨y, hyL⟩, hy⟩
    have hn := (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨y, hyL⟩).1 hy
    have hy' : y ∈ Set.range F.emb := by
      rw [hrange]
      exact ⟨hyL, hn⟩
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, rfl⟩
  have hbij : Function.Bijective f :=
    ⟨fun x y h => hinj (congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : PadicAlgCl l)) h), hsurj⟩
  let e := RingEquiv.ofBijective f hbij
  have hfin : Finite (integralClosure ℤ_[l] L ⧸
      Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1}) :=
    GlobalTheory.LocalIntegers.finite_quotient_pow l (integralClosure ℤ_[l] L) 1
  have hIJ : Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1} =
      (Ideal.span {((l : ℕ) : F.O)}).map (e : F.O →+* integralClosure ℤ_[l] L) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, pow_one]
  exact Finite.of_equiv _ (Ideal.quotientEquiv _ _ e hIJ).symm.toEquiv

end GlobalTheory.FrameQuot
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.UG

namespace GlobalTheory.ExpFrame

def rowProj (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (w : Fin N → ℕ) :
    dualWeyl O N N ν →ₗ[O] dualWeyl O N N ν :=
  (weightedHomogeneousComponent (rowW N N) w).restrict
    (fun x hx => dualWeylModuleRowGraded O N N ν w x hx)

theorem exists_unique_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι)
    (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  intro O _ N ι _ _ lam τ w
  have hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w)) := by
    intro x y hy
    unfold atFactor
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp only [Function.update_self, LinearMap.restrict_apply, rowProj]
      exact Subtype.ext hy.symm
    · simp [Function.update_of_ne h]
  refine ⟨_, hP, fun a' ha' => ?_⟩
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  exact (ha' x y rfl).trans (hP x y rfl).symm

end GlobalTheory.ExpFrame

end
end

section

set_option autoImplicit false

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.UG Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame

theorem finite_forms_of_classes {O : Type} [CommRing O] {W : Type} [AddCommGroup W] [Module O W] [IsNoetherian O W]
    {G : Type} [Group G] (Γ K : Subgroup G) (ρ : Representation O K W)
    (h : ∃ S : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ κ ∈ K, g = γ * s * κ) : Module.Finite O (AMFK O Γ K ρ) := by
  obtain ⟨S, hS⟩ := h
  let ev : AMFK O Γ K ρ →ₗ[O] (S → W) :=
    (LinearMap.funLeft O W (Subtype.val : S → G)).comp (AMFK O Γ K ρ).subtype
  refine Module.Finite.of_injective ev ?_
  intro f f' hff
  ext g
  obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
  have h1 := f.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h2 := f'.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h3 : (f : G → W) s = (f' : G → W) s := congrFun hff ⟨s, hs⟩
  exact h1.trans ((congrArg _ h3).trans h2.symm)

theorem Frame.finite_latticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  intro l _ ι _ _ N F mu jK hF
  have : ∀ τ : ι, Module.Finite F.O (dualWeyl F.O N N (res N (mu τ))) :=
    fun τ => dualWeyl_module_finite F.O N N _
  have : IsNoetherian F.O (NablaT F.O N mu) := inferInstance
  exact finite_forms_of_classes F.Γ F.K _ hF.classes

end GlobalTheory.ExpFrame
end
