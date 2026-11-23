module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle001
public import Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle002
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

open AlgebraicGeometry CategoryTheory Limits NumberField in
private theorem wedgeForm_update_eq_zero_of_mem_span_others {S N : Type} [CommRing S]
    [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S) (v : Fin k → N) (i : Fin k)
    {x : N} (hx : x ∈ Submodule.span S (v '' {j | j ≠ i})) :
    F (Function.update v i x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j ≠ i := hj
    exact F.map_eq_zero_of_eq (Function.update v i (v j)) (i := i) (j := j)
      (by simp [Function.update_of_ne hj']) (Ne.symm hj')
  | zero => exact F.map_update_zero v i
  | add y z _ _ hy hz => rw [F.map_update_add, hy, hz, add_zero]
  | smul a y _ hy => rw [F.map_update_smul, hy, smul_zero]

open AlgebraicGeometry CategoryTheory Limits NumberField in
private theorem wedgeForm_eq_prod_mul_of_triangular_change {T : Type} {m : T → ℕ} {S N : Type}
    [CommRing S] [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S)
    (c c' : _root_.GlobalTheory.FlagEmb.Let m → N) (d : _root_.GlobalTheory.FlagEmb.Let m → S)
    (ht : ∀ z : _root_.GlobalTheory.FlagEmb.Let m, c' z - d z • c z ∈
      Submodule.span S ((fun j => c ⟨z.fst, j⟩) '' {j | j < z.snd}))
    (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    F (fun l => c' (e l)) = (∏ l, d (e l)) * F (fun l => c (e l)) := by
  classical
  obtain ⟨_, hdown⟩ := he
  let w : Finset (Fin k) → Fin k → N := fun s l => if l ∈ s then c' (e l) else c (e l)
  have key : ∀ s : Finset (Fin k), F (w s) = (∏ l ∈ s, d (e l)) * F (w ∅) := by
    intro s
    refine Finset.induction_on_min_value (fun l => ((e l).snd : ℕ)) s ?_ ?_
    · simp
    · intro a s ha hmin ih
      have hw : w (insert a s) = Function.update (w s) a
          (d (e a) • w s a + (c' (e a) - d (e a) • c (e a))) := by
        funext l
        by_cases hl : l = a
        · subst hl
          simp [w, ha]
        · simp [w, hl, Function.update_of_ne hl]
      have hzero : F (Function.update (w s) a (c' (e a) - d (e a) • c (e a))) = 0 := by
        refine wedgeForm_update_eq_zero_of_mem_span_others F (w s) a ?_
        refine Submodule.span_mono ?_ (ht (e a))
        rintro _ ⟨j, hj, rfl⟩
        have hj' : (j : ℕ) < ((e a).snd : ℕ) := hj
        obtain ⟨l', hl'⟩ := hdown a j hj
        have hsnd : ((e l').snd : ℕ) = j := by
          have := congrArg (fun z : _root_.GlobalTheory.FlagEmb.Let m => (z.snd : ℕ)) hl'
          simpa using this
        have hne : l' ≠ a := by
          rintro rfl
          omega
        have hns : l' ∉ s := by
          intro h
          have := hmin l' h
          omega
        refine ⟨l', hne, ?_⟩
        simp [w, hns, hl']
      rw [hw, F.map_update_add, F.map_update_smul, Function.update_eq_self, hzero,
        Finset.prod_insert ha, ih, smul_eq_mul, add_zero, mul_assoc]
  have h1 : w Finset.univ = fun l => c' (e l) := by
    funext l
    simp [w]
  have h2 : w ∅ = fun l => c (e l) := by
    funext l
    simp [w]
  have := key Finset.univ
  rwa [h1, h2] at this


open AlgebraicGeometry CategoryTheory Limits NumberField in
theorem _root_.GlobalTheory.FlagEmb.plk_tri (T : Type) (m : T → ℕ) (S : Type) [CommRing S]
    (M : ℕ) (c c' : _root_.GlobalTheory.FlagEmb.Let m → Fin (M + 1) → S)
    (d : _root_.GlobalTheory.FlagEmb.Let m → S) (k : ℕ) (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m)
    (ht : _root_.GlobalTheory.FlagEmb.Tri c c' d) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    _root_.GlobalTheory.FlagEmb.plk c' e = (∏ l, d (e l)) • _root_.GlobalTheory.FlagEmb.plk c e := by
  funext q
  have := wedgeForm_eq_prod_mul_of_triangular_change
    ((Matrix.detRowAlternating (n := Fin k) (R := S)).compLinearMap
      (LinearMap.funLeft S S (_root_.GlobalTheory.FlagEmb.plE M k q))) c c' d ht e he
  unfold _root_.GlobalTheory.FlagEmb.plk
  simp only [Pi.smul_apply, smul_eq_mul]
  exact this

end GlobalTheory.FlagEmb
end

section

noncomputable section

namespace GlobalTheory.FlagEmb

theorem adjugate_mul_eq_plk {K : Type} [Field K] {M k : ℕ} (D : Fin k → Fin (M + 1) → K) (r : Fin k → Fin (M + 1))
    (i : Fin k) (s : Fin (M + 1)) :
    ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      plk D id ((plE M k).symm (Function.update r i s)) := by
  have h1 : ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      ((Matrix.of fun l l' => D l (r l')).adjugate.mulVec fun j => D j s) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  simp only [plk, Equiv.apply_symm_apply, id]
  congr 1
  ext l l'
  by_cases h : l' = i
  · subst h
    simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply, Function.update_of_ne h, h]

theorem mem_span_of_plk_eq_smul (K : Type) [Field K] (M k : ℕ) (c c' : Fin k → Fin (M + 1) → K) (a : K)
    (h0 : plk c' id ≠ 0) (h : plk c' id = a • plk c id) (l : Fin k) :
    c' l ∈ Submodule.span K (Set.range c) := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h0
  set r := plE M k q with hr
  set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c l (r l') with hA
  set A' : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c' l (r l') with hA'
  have hdet : A'.det ≠ 0 := hq
  have hadj : A'.adjugate * Matrix.of c' = a • (A.adjugate * Matrix.of c) := by
    ext i s
    rw [hA, hA', adjugate_mul_eq_plk, Matrix.smul_apply, adjugate_mul_eq_plk, h]
    rfl
  have hC : A'.det • (Matrix.of c' : Matrix (Fin k) (Fin (M + 1)) K) = a • (A' * A.adjugate * Matrix.of c) := by
    have := congrArg (fun X => A' * X) hadj
    simp only [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul] at this
    simpa [Matrix.smul_mul] using this
  have hrow : c' l = ∑ j, ((A'.det)⁻¹ * (a * (A' * A.adjugate) l j)) • c j := by
    funext s
    have h2 := congrFun (congrFun hC l) s
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mul_apply (M := A' * A.adjugate)] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [eq_inv_mul_iff_mul_eq₀ hdet |>.2 h2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrow]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.FlagEmb
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open ReciprocityTheory.ChartRestriction.G.PullbackSections (IsEigV)

namespace GlobalTheory.FlagEmb.EigSpread

section Alg

theorem existsUnique_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (v : ι → M) :
    (∀ w, ∃! a : ι → R, ∑ j, a j • v j = w) ↔ LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  exact (Function.bijective_iff_existsUnique (Fintype.linearCombination R v)).symm

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] (χ : ι → O →+* K)

def Splits : Prop :=
  ∀ (S M : Type) [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M] (ρ : O →+* Module.End S M),
    (∀ m, ∃ mm : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) ∧ ∑ τ, mm τ = m) ∧
    ∀ mm mm' : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) → (∀ τ, IsEigV ρ (χ τ) (mm' τ)) → ∑ τ, mm τ = ∑ τ, mm' τ → mm = mm'

variable {χ} {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}

omit [Fintype ι] in
theorem eig_single [DecidableEq ι] {τ : ι} {w : M} (hw : IsEigV ρ (χ τ) w) (τ' : ι) :
    IsEigV ρ (χ τ') (Pi.single (M := fun _ => M) τ w τ') := by
  by_cases h : τ' = τ
  · subst h; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]; intro a; simp

theorem eig_comb {κ : Type} [Fintype κ] {ψ : O →+* K} {u : κ → M} (hu : ∀ i, IsEigV ρ ψ (u i)) (a : κ → R) :
    IsEigV ρ ψ (∑ i, a i • u i) := fun o => by

  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu, smul_comm]

theorem block_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ w, ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w) (τ : ι) (w : M) (hw : IsEigV ρ (χ τ) w) :
    ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w := by
  classical
  obtain ⟨a, ha, -⟩ := hb w
  have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) (Pi.single τ w)
    (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) (eig_single hw)
    (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← ha, Fintype.sum_sigma])
  have e' := congrFun e τ
  rw [Pi.single_eq_same] at e'
  refine ⟨_, e', fun b hb' => ?_⟩
  have li : LinearIndependent R fun i => u ⟨τ, i⟩ :=
    ((existsUnique_iff u).1 hb).1.comp (Sigma.mk τ) sigma_mk_injective
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 li (hb'.trans e'.symm)

theorem global_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ τ w, IsEigV ρ (χ τ) w → ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w) (w : M) :
    ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w := by
  obtain ⟨mm, h1, h2⟩ := (hs R M ρ).1 w
  choose c hc hc' using fun τ => hb τ _ (h1 τ)
  refine ⟨fun z => c z.1 z.2, ?_, fun a ha => ?_⟩
  · show ∑ z : Σ τ, Fin (m τ), c z.1 z.2 • u z = w
    rw [Fintype.sum_sigma, ← h2]
    exact Finset.sum_congr rfl fun τ _ => hc τ
  · have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) mm
      (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) h1 (by rw [h2, ← ha, Fintype.sum_sigma])
    funext z
    exact congrFun (hc' z.1 (fun i => a ⟨z.1, i⟩) (congrFun e z.1)) z.2

variable {S N : Type} [CommRing S] [Algebra K S] [AddCommGroup N] [Module S N] {ρ' : O →+* Module.End S N}
  {φ : R →+* S} (f : M →ₛₗ[φ] N)


end Alg

section Lift

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] {χ : ι → O →+* K}
  {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}
  {k N : Type} [Field k] [Algebra K k] [AddCommGroup N] [Module k N] {ρ' : O →+* Module.End k N}
  {φ : R →+* k} (f : M →ₛₗ[φ] N)

end Lift

section Geo

open GlobalTheory.FrameTangent MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {x' : Sp S ⟶ X}

theorem splits {l : Level H} (c : Coeff l) : Splits (embK c) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c)
    (fun τ a => embK_coe c τ a)
  intro S M _ _ _ _ ρ
  refine ⟨fun m => ⟨fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ m, fun τ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m), ?_⟩,
    fun mm mm' h h' e => funext fun τ => ?_⟩
  · rw [← LinearMap.sum_apply, ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj ρ _ α hinj]
    rfl
  · rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm h, e, ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm' h']

def lf (m : TanM x t.G) : Tn t R := (tv m).left

theorem lf_inj {m m' : TanM x t.G} (h : lf m = lf m') : m = m' := tv_injective (Over.OverMorphism.ext h)

theorem exists_lf {w : Tn t R} (hw : IsTanAtG t x w) : ∃ m : TanM x t.G, lf m = w :=
  ⟨mkT (FrameTangent.ovT (t := t) hw) (FrameTangent.smT_zero_ovT hw), rfl⟩

theorem comb_lf {n : ℕ} (v : Fin n → TanM x t.G) (a : Fin n → R) (w : TanM x t.G) :
    IsCombAtG t x (fun j => lf (v j)) a (lf w) ↔ ∑ j, a j • v j = w := by
  refine (FrameTangent.isCombAtG_iff t x (fun j => tv (v j)) a (lf w)).trans ⟨fun h => lf_inj ?_, fun h => ?_⟩
  · rw [lf, tv_comb]
    exact h
  · rw [← h, lf, tv_comb]
    rfl


variable {Dw : Datum H} {l : Level H} {c : Coeff l}

end Geo

end GlobalTheory.FlagEmb.EigSpread
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem exists_integral_cell : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (A : ValuationSubring K) (M : ℕ)
    (c u : Let m → Fin (M + 1) → K), InBlock c u → (∀ τ, LinearIndependent K fun j : Fin (m τ) => u ⟨τ, j⟩) →
    ∃ (w : Pm m) (x : CellVar m → K) (d : Let m → K), (∀ v, x v ∈ A) ∧ (∀ z, d z ≠ 0) ∧
      Tri (cellVec c w x) u d := by
  intro T m K _ A M c u hin hli
  have hg : ∀ z : Let m, ∃ a : Fin (m z.1) → K, ∑ i, a i • c ⟨z.1, i⟩ = u z := fun z =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hin z)
  choose a ha using hg
  let g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) K := fun τ i j => a ⟨τ, j⟩ i
  have hu : ∀ τ j, u ⟨τ, j⟩ = ∑ i, g τ i j • c ⟨τ, i⟩ := fun τ j => (ha ⟨τ, j⟩).symm
  have hgli : ∀ τ, LinearIndependent K (g τ).transpose := by
    intro τ
    refine Fintype.linearIndependent_iff.2 fun s hs => ?_
    have hs' : ∀ i, ∑ j, s j * g τ i j = 0 := fun i => by
      have := congrFun hs i
      simpa [Finset.sum_apply, Matrix.transpose_apply] using this
    have h0 : ∑ j, s j • u ⟨τ, j⟩ = 0 := by
      simp_rw [hu, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      simp [hs']
    exact Fintype.linearIndependent_iff.1 (hli τ) s h0
  have hdec := fun τ => GlobalTheory.exists_integral_pivot_decomposition K A _ _ (g τ) (hgli τ)
  choose ι u0 b huA hu0 hu1 hbt hbd hgub using hdec
  have hbij : ∀ τ, Function.Bijective (ι τ) := fun τ => Finite.injective_iff_bijective.1 (ι τ).injective
  let w : Pm m := fun τ => Equiv.ofBijective _ (hbij τ)
  let x : CellVar m → K := fun v => u0 v.1 (ι v.1 v.2.1.1) v.2.1.2
  refine ⟨w, x, fun z => b z.1 z.2 z.2, fun v => huA _ _ _, fun z => hbd _ _, ?_⟩
  have hcell : ∀ τ i j, cell x τ i j = u0 τ (ι τ i) j := by
    intro τ i j
    unfold cell
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hu1 τ i).symm
    · have : i < j := lt_of_le_of_ne (not_lt.1 h1) h2
      exact (hu0 τ i j this).symm
  have hv : ∀ τ j, cellVec c w x ⟨τ, j⟩ = ∑ k, u0 τ k j • c ⟨τ, k⟩ := by
    intro τ j
    simp only [cellVec, hcell]
    exact Equiv.sum_comp (w τ) (fun k => u0 τ k j • c ⟨τ, k⟩)
  have hexp : ∀ τ j, u ⟨τ, j⟩ = ∑ l, b τ l j • cellVec c w x ⟨τ, l⟩ := by
    intro τ j
    rw [hu]
    simp_rw [hv, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [show g τ i j = (u0 τ * b τ) i j from by rw [← hgub τ], Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rintro ⟨τ, j⟩
  show u ⟨τ, j⟩ - b τ j j • cellVec c w x ⟨τ, j⟩ ∈ _
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun l hl => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, h, rfl⟩)
  · rw [hbt τ h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam

def shimXOfPkg {D : D7} {G : DV.Geo D.what₂.LL} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {N j : ℕ} {Comp : Type} [Fintype Comp] [Nonempty Comp] (cx : CxPkg D.what₂.Tau N j Comp)
    (alg : AlgPkg G D.what₂.Tau N Comp) (pad : PadPkg D N j Comp jC ng) (h : 1 ≤ j ∧ j < N) (lev : Finset ℕ)
    (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h.1
  j_lt := h.2
  lev := lev
  lev_prime := hlev
  Comp := Comp
  vol := cx.vol
  chern := cx.chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N cx.vol P d hd hP
  arDeg := pad.arDeg
  arDeg_homog := pad.arDeg_homog
  arMix := pad.arMix
  arMix_HT := pad.arMix_HT
  arMix_DR := pad.arMix_DR
  CurveHT := pad.CurveHT
  degHT := pad.degHT
  CurveDR := pad.CurveDR
  degDR := pad.degDR
  FibComp := pad.FibComp
  fibInBd := pad.fibInBd
  Pt := pad.Pt
  phiDR := pad.phiDR
  phiMod := pad.phiMod
  phiFr := pad.phiFr
  XC := cx.XC
  rfn := cx.rfn
  rfn_ge := cx.rfn_ge
  hLo := cx.hLo
  hUp := cx.hUp
  hLo_le := cx.hLo_le
  connN := cx.connN
  curvN := cx.curvN
  compOf := cx.compOf
  normDetInf := cx.normDetInf
  compPt := pad.compPt
  normDetT := pad.normDetT
  normDetH := pad.normDetH
  htDetT := pad.htDetT
  ALB := alg.ALB
  arSelf := fun L => ∑ c, alg.arSelfC L c
  arSelfC := alg.arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, alg.geoC L c
  geoC := alg.geoC
  geo_sum := fun _ => rfl
  arVol := alg.arVol
  semipos := alg.semipos
  nefFib := alg.nefFib
  arNef := alg.arNef
  Mbar := alg.Mbar

section
variable {D : D7} {A : Amb D} {F : SrcFam A} {L : CmList A} {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C)
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (k : Kits F L C jC ng)

end

end GlobalTheory.ShFam
end
end
