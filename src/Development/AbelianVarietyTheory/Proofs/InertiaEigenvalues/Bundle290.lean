module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
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

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.AdmClosure

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
variable {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def between [IsDomain O] [IsPrincipalIdealRing O] (L₁ L₂ : Lattice (O := O) ρ) (N : Submodule O V)
    (h₁ : N ≤ L₁.T) (h₂ : L₂.T ≤ N) (hs : ∀ g, ∀ x ∈ N, ρ g x ∈ N) : Lattice (O := O) ρ where
  T := N
  stable := hs
  fg := L₁.fg.of_le h₁
  free := by
    haveI := L₁.free
    haveI : Module.Finite O L₁.T := Module.Finite.iff_fg.mpr L₁.fg
    haveI : Module.Finite O (N.comap L₁.T.subtype) := inferInstance
    haveI : Module.Free O (N.comap L₁.T.subtype) := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe h₁)
  span := by
    rw [eq_top_iff, ← L₂.span]
    exact Submodule.span_mono h₂

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def prodEquiv (A : Submodule O V) (B : Submodule O V') : ↥(A.prod B) ≃ₗ[O] (↥A × ↥B) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def prodLattice (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') : Lattice (O := O) (ρ.prod ρ') where
  T := L.T.prod L'.T
  stable := fun g x hx => ⟨L.stable g _ hx.1, L'.stable g _ hx.2⟩
  fg := L.fg.prod L'.fg
  free := by
    haveI := L.free
    haveI := L'.free
    exact Module.Free.of_equiv (prodEquiv L.T L'.T).symm
  span := by
    have h := Submodule.span_prod_eq (R := LL) (s := (L.T : Set V)) (t := (L'.T : Set V')) L.T.zero_mem L'.T.zero_mem
    rw [L.span, L'.span, Submodule.prod_top] at h
    exact h

end Lat

section Bundled

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def prodLoc (T T' : LocLat G Qp LL O) : LocLat G Qp LL O where
  V := T.V × T'.V
  ρ := T.ρ.prod T'.ρ
  cont := fun x => (T.cont x.1).prodMk (T'.cont x.2)
  L := prodLattice T.L T'.L

end Bundled

def appendEquiv {R : Type} [CommRing R] {A : Type 1} (W : A → Type) [∀ x, AddCommGroup (W x)] [∀ x, Module R (W x)]
    {ι κ : Type} (F : ι → A) (F' : κ → A) :
    ((∀ j, W (F j)) × (∀ j, W (F' j))) ≃ₗ[R] (∀ j : ι ⊕ κ, W (Sum.elim F F' j)) where
  toFun x j := match j with
    | .inl a => x.1 a
    | .inr b => x.2 b
  invFun y := (fun a => y (.inl a), fun b => y (.inr b))
  map_add' _ _ := by funext j; cases j <;> rfl
  map_smul' _ _ := by funext j; cases j <;> rfl
  left_inv _ := rfl
  right_inv _ := by funext j; cases j <;> rfl

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {t : ℕ} {Ut : ZMod n → Multiset ℤ}

theorem sumFull_prod [IsTopologicalRing LL] {μ μ' : ℕ} {T T' : LocLat G Qp LL O} (h : SumFull PD emb Γ t Ut μ T)
    (h' : SumFull PD emb Γ t Ut μ' T') : SumFull PD emb Γ t Ut (μ + μ') (prodLoc T T') := by
  obtain ⟨F, hF, e, he⟩ := h
  obtain ⟨F', hF', e', he'⟩ := h'
  let s : Fin (μ + μ') ≃ Fin μ ⊕ Fin μ' := finSumFinEquiv.symm
  have key : ∀ (g : G) (x : T.V × T'.V) (j : Fin μ ⊕ Fin μ'),
      appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e (T.ρ g x.1), e' (T'.ρ g x.2)) j =
        (Sum.elim F F' j).ρ g (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e x.1, e' x.2) j) := by
    intro g x j
    cases j with
    | inl a => exact he g x.1 a
    | inr b => exact he' g x.2 b
  refine ⟨fun j => Sum.elim F F' (s j), fun j => ?_,
    ((e.prodCongr e').trans (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F')).trans
      (LinearEquiv.piCongrLeft LL (fun j => (Sum.elim F F' j).V) s).symm, fun g x j => key g x (s j)⟩
  beta_reduce
  cases s j with
  | inl a => exact hF a
  | inr b => exact hF' b

variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'}

theorem admissible_prod [IsTopologicalRing LL] (h : Admissible PD emb Γ t Ut π) (h' : Admissible PD emb Γ t Ut π') :
    Admissible PD emb Γ t Ut (π.prod π') := by
  obtain ⟨hf, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  obtain ⟨hf', μ', T', hT', L₂', p', hle', hp', hg', hk'⟩ := h'
  refine ⟨inferInstance, μ + μ', prodLoc T T', sumFull_prod hT hT', prodLattice L₂ L₂',
    (p.prodMap p') ∘ₗ (prodEquiv T.L.T T'.L.T).toLinearMap, Submodule.prod_mono hle hle',
    (hp.prodMap hp').comp (prodEquiv T.L.T T'.L.T).surjective, fun g x => ?_, fun x => ?_⟩
  · exact Prod.ext (hg g (prodEquiv T.L.T T'.L.T x).1) (hg' g (prodEquiv T.L.T T'.L.T x).2)
  · exact Prod.ext_iff.trans (and_congr (hk (prodEquiv T.L.T T'.L.T x).1) (hk' (prodEquiv T.L.T T'.L.T x).2))

variable [IsDomain O] [IsPrincipalIdealRing O]

theorem admissible_of_surjective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hs : Function.Surjective f) (h : Admissible PD emb Γ t Ut π) : Admissible PD emb Γ t Ut π' := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := (LinearMap.ker (f ∘ₗ p)).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ f (p x) = 0 := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  refine ⟨Finite.of_surjective f hs, μ, T, hT, between T.L L₂ N h₁ (fun x hx => ?_) (fun g x hx => ?_),
    f ∘ₗ p, h₁, hs.comp hp, fun g x => ?_, fun x => (hN x).symm⟩
  · refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx, map_zero]
  · refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    rw [hg, hf, (hN ⟨x, h₁ hx⟩).mp hx, map_zero]
  · simp only [LinearMap.comp_apply, hg, hf]

theorem admissible_of_injective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hi : Function.Injective f) (h : Admissible PD emb Γ t Ut π') : Admissible PD emb Γ t Ut π := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := ((LinearMap.range f).comap p).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ p x ∈ LinearMap.range f := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  have h₂ : L₂.T ≤ N := fun x hx => by
    refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx]
    exact zero_mem _
  have hs : ∀ g, ∀ x ∈ N, T.ρ g x ∈ N := fun g x hx => by
    refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    obtain ⟨y, hy⟩ := (hN ⟨x, h₁ hx⟩).mp hx
    exact ⟨π g y, by rw [hg, hf, hy]⟩
  let q : N →ₗ[O] M := (LinearEquiv.ofInjective f hi).symm.toLinearMap ∘ₗ
    (p ∘ₗ Submodule.inclusion h₁).codRestrict (LinearMap.range f) (fun x => (hN ⟨x, h₁ x.2⟩).mp x.2)
  have hq : ∀ x : N, f (q x) = p ⟨x, h₁ x.2⟩ := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective f hi).apply_symm_apply ⟨_, (hN ⟨x, h₁ x.2⟩).mp x.2⟩)
  refine ⟨Finite.of_injective f hi, μ, withLat T (between T.L L₂ N h₁ h₂ hs), hT.withLat _, L₂, q, h₂,
    fun y => ?_, fun g x => hi ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := hp (f y)
    exact ⟨⟨x.1, (hN x).mpr ⟨y, hx.symm⟩⟩, hi ((hq _).trans hx)⟩
  · exact (hq _).trans ((hg g ⟨x.1, h₁ x.2⟩).trans ((congrArg (π' g) (hq x).symm).trans (hf g _).symm))
  · refine Iff.trans ?_ (hk ⟨x.1, h₁ x.2⟩)
    rw [← hq x, ← map_zero f]
    exact hi.eq_iff.symm

end Per

theorem admissible_closed : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Closed := by
  intro l _ P S M M' _ _ _ _ π π'
  obtain ⟨⟨hD, hDV, -⟩, -, -, hT, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  exact ⟨fun f hf => ⟨admissible_of_injective f hf, admissible_of_surjective f hf⟩, admissible_prod⟩

end GlobalTheory.AdmClosure
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  first | exact @GlobalTheory.Cyc.htBasis_of_isDec | exact GlobalTheory.Cyc.htBasis_of_isDec | (intros; apply GlobalTheory.Cyc.htBasis_of_isDec <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  first | exact @GlobalTheory.GLq.ZOrth.zorth | exact GlobalTheory.GLq.ZOrth.zorth | (intros; apply GlobalTheory.GLq.ZOrth.zorth <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.complexFieldAut_acts_harishChandra_characters : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  first | exact @GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters | exact GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters | (intros; apply GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.exists_fontaineTheta_on_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ∃ θ : Ainf l →+* OC l, IsTheta AI θ := by
  first | exact @GlobalTheory.Cyc.exists_isTheta | exact GlobalTheory.Cyc.exists_isTheta | (intros; apply GlobalTheory.Cyc.exists_isTheta <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  first | exact @GlobalTheory.Cyc.isMat_exists_and_props | exact GlobalTheory.Cyc.isMat_exists_and_props | (intros; apply GlobalTheory.Cyc.isMat_exists_and_props <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem vecMul_repr_rows {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul v (Matrix.of fun k j => b.repr (Pi.single k 1) j) = b.repr v := by
  ext j
  conv_rhs => rw [← Finset.univ_sum_single v]

  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (v k) : n → E) = v k • Pi.single k 1 by
    ext i; by_cases h : i = k <;> simp [h]]
  simp

theorem vecMul_rows_repr {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul (b.repr v) (Matrix.of fun i j => b i j) = v := by
  ext j
  conv_rhs => rw [← b.sum_repr v]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem splits_of_stable_rat_subspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  classical
  intro l _ n _ _ K r ρ hρ W hWE hWsm hWst hW0 hWtop
  let E : Subfield ↥(MaximalUnramifiedExtension l) := RingHom.eqLocusField (fr l r) (RingHom.id _)
  let ι : E →+* ↥(MaximalUnramifiedExtension l) := E.subtype
  have hE : ∀ x : E, fr l r (x : ↥(MaximalUnramifiedExtension l)) = x := fun x => x.2
  let cv : (n → E) → (n → ↥(MaximalUnramifiedExtension l)) := fun c i => (c i : ↥(MaximalUnramifiedExtension l))
  let W' : Submodule E (n → E) :=
    { carrier := {c | cv c ∈ W}
      add_mem' := fun {c d} hc hd => by
        show cv (c + d) ∈ W
        rw [show cv (c + d) = cv c + cv d from funext fun i => by simp [cv]]
        exact W.add_mem hc hd
      zero_mem' := by
        show cv 0 ∈ W
        rw [show cv 0 = 0 from funext fun i => by simp [cv]]
        exact W.zero_mem
      smul_mem' := fun e c hc => by
        show cv (e • c) ∈ W
        rw [show cv (e • c) = (e : ↥(MaximalUnramifiedExtension l)) • cv c from funext fun i => by simp [cv, smul_eq_mul]]
        exact hWsm (e : ↥(MaximalUnramifiedExtension l)) (hE e) _ hc }
  have memW' : ∀ c, c ∈ W' ↔ cv c ∈ W := fun c => Iff.rfl
  have lift : ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∃ c' : n → E, cv c' = c :=
    fun c hc => ⟨fun i => ⟨c i, hc i⟩, rfl⟩
  have hW'0 : W' ≠ ⊥ := by
    obtain ⟨c, hcW, hc0⟩ : ∃ c ∈ W, c ≠ 0 := by
      by_contra h
      push_neg at h
      exact hW0 ((AddSubgroup.eq_bot_iff_forall W).2 h)
    obtain ⟨c', rfl⟩ := lift c (hWE c hcW)
    intro h
    have : c' ∈ W' := hcW
    rw [h, Submodule.mem_bot] at this
    exact hc0 (by subst this; rfl)
  have hW'top : W' ≠ ⊤ := by
    obtain ⟨c, hcE, hcW⟩ := hWtop
    obtain ⟨c', rfl⟩ := lift c hcE
    intro h
    exact hcW ((memW' c').1 (h ▸ Submodule.mem_top))
  obtain ⟨S, hSW, hSspan, hSli⟩ := exists_linearIndependent E (W' : Set (n → E))
  have hSli' : LinearIndepOn E id S := hSli
  let B := Module.Basis.extend hSli'
  let e := B.indexEquiv (Pi.basisFun E n)
  let b : Module.Basis n E (n → E) := B.reindex e
  have hb : ∀ i, b i = ((e.symm i : _) : n → E) := fun i => by
    rw [Module.Basis.reindex_apply]; exact Module.Basis.extend_apply_self hSli' _
  have hbS : ∀ x ∈ S, ∃ i, b i = x := fun x hx =>
    ⟨e ⟨x, Module.Basis.subset_extend hSli' hx⟩, by simp [hb]⟩
  let s : Finset n := Finset.univ.filter fun i => b i ∉ S
  have hs : ∀ i, i ∉ s ↔ b i ∈ S := fun i => by simp [s]
  have hWspan : W' ≤ Submodule.span E (b '' ((s : Set n)ᶜ)) := by
    conv_lhs => rw [← Submodule.span_eq W', ← hSspan]
    apply Submodule.span_mono
    intro x hx
    obtain ⟨i, rfl⟩ := hbS x hx
    exact ⟨i, by simpa [hs] using hx, rfl⟩
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hW'top
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hSW ((hs i).1 (by simp [h]))
  have hsuniv : s ≠ Finset.univ := by
    intro h
    apply hW'0
    have hS0 : S = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨i, rfl⟩ := hbS x hx
      exact (hs i).2 hx (by simp [h])
    rw [← Submodule.span_eq W', ← hSspan, hS0, Submodule.span_empty]
  let M : Matrix n n E := Matrix.of fun i j => b i j
  let N : Matrix n n E := Matrix.of fun k j => b.repr (Pi.single k 1) j
  have hNM : N * M = 1 := by
    refine Matrix.ext fun k j => ?_
    show Matrix.vecMul (b.repr (Pi.single k 1)) M j = _
    rw [vecMul_rows_repr]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hMN : M * N = 1 := mul_eq_one_comm.2 hNM
  let qE : GL n E := ⟨M, N, hMN, hNM⟩
  let p : GL n ↥(MaximalUnramifiedExtension l) := (Matrix.GeneralLinearGroup.map ι qE)⁻¹
  have hp : (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = N.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [← map_inv]
    rfl
  have hpinv : ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = M.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [inv_inv]
    rfl
  let R : ↥(GK K) → Matrix n n E := fun g => Matrix.of fun i j => (⟨(ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j, hρ.rat g i j⟩ : E)
  have hR : ∀ g, ((ρ g : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = (R g).map ι := fun g => by
    ext i j; rfl
  refine ⟨s, p, hsne, hsuniv, fun i j => ?_, fun g i j hi hj => ?_⟩
  · rw [hp]
    exact hE (N i j)
  · rw [Units.val_mul, Units.val_mul, hpinv, hR, hp, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    suffices h : (M * R g * N) i j = 0 by rw [h, map_zero]
    show Matrix.vecMul (Matrix.vecMul (b i) (R g)) N j = 0
    rw [vecMul_repr_rows]
    have hw : Matrix.vecMul (b i) (R g) ∈ W' := by
      rw [memW']
      have h1 : cv (b i) ∈ W := hSW ((hs i).1 hi)
      have h2 := hWst g _ h1
      convert h2 using 1
      funext k
      show ι (Matrix.vecMul (b i) (R g) k) = Matrix.vecMul (cv (b i)) (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, map_sum, map_mul]
      rfl
    have := (Module.Basis.mem_span_image b).1 (hWspan hw)
    by_contra hne
    exact this ((Finsupp.mem_support_iff).2 hne) (by simpa using hj)

end GlobalTheory.PMon
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.cocycle_rat_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  intro l _ n _ _ K r σ ρ₀ p c c₀ hint hc0 hc g h
  set f : ℚ_[l] →+* ↥(MaximalUnramifiedExtension l) := algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) with hf
  set P : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hP

  have hC : (fun x : n × Fin r => fr l x.2 (c (g * h) x.1)) =
      (fun x : n × Fin r => fr l x.2 (c g x.1)) +
        (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).mulVec
          (fun x : n × Fin r => fr l x.2 (c h x.1)) := by
    funext ⟨i, m⟩

    simp only [hc, Pi.add_apply, map_add (f := _), Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, Matrix.map_apply, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  have key : P.mulVec (fun x => f (c₀ (g * h) x)) =
      P.mulVec (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    rw [hc0, hC, ← hc0 g, ← hc0 h, Matrix.mulVec_mulVec, ← hint g]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    congr 1
    congr 1
    funext x
    simp only [Pi.add_apply, map_add, RingHom.map_mulVec, Function.comp_def]
  have inj : (fun x => f (c₀ (g * h) x)) =
      (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    have := congrArg (fun v => ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec v) key
    simp only [hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
    exact this
  funext x
  exact f.injective (congrFun inj x)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem firstAdmissibilityAt_of_parts : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  intro D bkP i s h1 h2 h3 h4
  exact ⟨h1, h2, fun v => (h3 v).1, fun v => (h3 v).2, h4⟩

end GlobalTheory.TripleGal
end
