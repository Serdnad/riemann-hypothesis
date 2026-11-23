module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfAMemAdjoinLow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle280
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle100
import Formalism.RealPlaceAnalysis.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.ZFin


open Polynomial in
theorem commute_aeval {M : Type} [AddCommGroup M] [Module ℂ M] {T S : Module.End ℂ M} (h : Commute S T) (q : ℂ[X]) :
    Commute S (aeval T q) := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _


open Polynomial in
theorem aeval_modByMonic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} {w : M}
    (hw : aeval T p w = 0) (q : ℂ[X]) : aeval T q w = aeval T (q %ₘ p) w := by
  conv_lhs => rw [← Polynomial.modByMonic_add_div q p]
  rw [map_add (f := _), LinearMap.add_apply, mul_comm, map_mul, Module.End.mul_apply, hw, map_zero, add_zero]


open Polynomial in
theorem exists_step {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} (hp : p.Monic)
    {W : Submodule ℂ M} (hF : W.FG) (hW : ∀ w ∈ W, aeval T p w = 0) :
    ∃ W' : Submodule ℂ M, W'.FG ∧ W ≤ W' ∧ (∀ w ∈ W', T w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w ∈ W) → ∀ w ∈ W', S w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w = 0) → ∀ w ∈ W', S w = 0) := by
  let B : ℂ[X] →ₗ[ℂ] M →ₗ[ℂ] M := (aeval T).toLinearMap
  have hB : ∀ q w, B q w = aeval T q w := fun _ _ => rfl
  have hdeg : ∀ q : ℂ[X], q %ₘ p ∈ degreeLT ℂ p.natDegree := fun q => by
    rw [Polynomial.mem_degreeLT, ← Polynomial.degree_eq_natDegree hp.ne_zero]
    exact Polynomial.degree_modByMonic_lt q hp
  have hmem : ∀ q, ∀ w ∈ W, aeval T q w ∈ Submodule.map₂ B (degreeLT ℂ p.natDegree) W := fun q w hw => by
    rw [aeval_modByMonic T (hW w hw) q]
    exact Submodule.apply_mem_map₂ B (hdeg q) hw
  have hfg : (degreeLT ℂ p.natDegree).FG := by
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ p.natDegree).symm
  refine ⟨Submodule.map₂ B (degreeLT ℂ p.natDegree) W, Submodule.FG.map₂ _ hfg hF, fun w hw => ?_, ?_, ?_, ?_⟩
  · simpa using hmem 1 w hw
  · have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap T :=
      Submodule.map₂_le.2 fun q _ w hw => by
        have e : T * aeval T q = aeval T (X * q) := by rw [map_mul, Polynomial.aeval_X]
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, e]
        exact hmem _ w hw
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply]
        exact hmem _ _ (hSW w hw)
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤ LinearMap.ker S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [LinearMap.mem_ker, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply,
          hSW w hw, map_zero]
    exact fun w hw => this hw


open Polynomial in
theorem exists_fg_stable {M ι : Type} [AddCommGroup M] [Module ℂ M] [Fintype ι] (T : ι → Module.End ℂ M)
    (p : ι → ℂ[X]) (hp : ∀ i, (p i).Monic) (hc : ∀ i j, Commute (T i) (T j)) (v : M)
    (hv : ∀ i, aeval (T i) (p i) v = 0) :
    ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ ∀ i, ∀ w ∈ W, T i w ∈ W := by
  classical
  have key : ∀ s : Finset ι, ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ (∀ i ∈ s, ∀ w ∈ W, T i w ∈ W) ∧
      ∀ i, ∀ w ∈ W, aeval (T i) (p i) w = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {v}, Submodule.fg_span_singleton v, Submodule.mem_span_singleton_self v,
        by simp, fun i w hw => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, hv, smul_zero]
    | insert j s _ ih =>
      obtain ⟨W, hF, hvW, hs, hk⟩ := ih
      obtain ⟨W', hF', hle, hT, hS, hZ⟩ := exists_step (T j) (hp j) hF (hk j)
      refine ⟨W', hF', hle hvW, fun i hi => ?_, fun i => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hT
        · exact hS _ (hc i j) (hs i hi)
      · exact hZ _ ((commute_aeval (hc j i) (p i)).symm) (hk i)
  obtain ⟨W, hF, hvW, hs, _⟩ := key Finset.univ
  exact ⟨W, hF, hvW, fun i => hs i (Finset.mem_univ i)⟩

section Main

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

abbrev unitOp (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : Fin V.rank → Fin V.rank → Module.End ℂ (SmFun θ V) :=
  fun a b => derEnd hθ τ (Matrix.single a b 1)

theorem commute_derEnd_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ℕ) :
    Commute (derEnd hθ τ Z) (gelfA (unitOp hθ V τ') k) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have e1 : ∀ g : SmFun θ V, (gelfA (unitOp hθ V τ') k g).1 = gelf θ V τ' k g.1 := fun g => (gelf_eq hθ τ' k g).symm
  have L := linOnSm_gelf (θ := θ) (V := V) τ' k
  refine LinearMap.ext fun f => Subtype.ext ?_
  change RderC θ V τ Z (gelfA (unitOp hθ V τ') k f).1 = (gelfA (unitOp hθ V τ') k (derEnd hθ τ Z f)).1
  rw [e1, e1]
  change _ = gelf θ V τ' k (RderC θ V τ Z f.1)
  simp only [RderC]
  rw [L.add _ (Rder_mem f.2 h1) _ (Submodule.smul_mem _ _ (Rder_mem f.2 h2)), L.smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 f.2, GlobalTheory.CuspLie.gelf_Rder hθ h2 f.2]

theorem commute_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k k' : ℕ) :
    Commute (gelfA (unitOp hθ V τ) k) (gelfA (unitOp hθ V τ') k') := by
  refine Commute.sum_left _ _ _ fun idx _ => Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
  exact commute_derEnd_gelfA hθ τ τ' _ k'


open Polynomial in
theorem foldr_gelf_eq (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) (φ : SmFun θ V) (L : List ℂ) :
    L.foldr (fun a f => gelf θ V τ k f - a • f) φ.1 =
      (aeval (gelfA (unitOp hθ V τ) k) ((L.map fun a => (X - C a : ℂ[X])).prod) φ).1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, gelf_eq hθ τ k, map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    rfl

open Polynomial in
theorem monic_prod_roots (L : List ℂ) : ((L.map fun a => (X - C a : ℂ[X])).prod).Monic := by
  induction L with
  | nil => simp
  | cons a L ih => simpa using (monic_X_sub_C a).mul ih

end Main

end GlobalTheory.CompanionTheory.ZFin


open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms GlobalTheory.CompanionTheory.ZFin in
open Polynomial in
theorem GlobalTheory.CompanionTheory.ZFin.isAutFunSm_of_gelf_roots : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) → (∀ τ k, ∃ L : List ℂ, L.foldr (fun a f => gelf θ V τ k f - a • f) φ = 0) → IsAutFunSm θ V φ := by
  intro D θ hθ V φ hA hs hg hz
  choose L hL using hz
  have hsm : φ ∈ SmFun θ V := hs
  obtain ⟨W, hF, hv, hS⟩ := exists_fg_stable (ι := D.what₂.Tau × Fin V.rank)
    (fun i => gelfA (unitOp hθ V i.1) i.2.val)
    (fun i => ((L i.1 i.2.val).map fun a => (X - C a : ℂ[X])).prod)
    (fun i => monic_prod_roots _) (fun i j => commute_gelfA hθ _ _ _ _) ⟨φ, hsm⟩
    (fun i => Subtype.ext ((foldr_gelf_eq hθ i.1 i.2.val ⟨φ, hsm⟩ _).symm.trans (hL _ _)))
  refine { toIsAutFun := hA, smooth := hs, growth := hg,
           zfin := ⟨W.map (SmFun θ V).subtype, Module.Finite.iff_fg.2 (hF.map _), ⟨⟨φ, hsm⟩, hv, rfl⟩, ?_⟩ }
  rintro τ k _ ⟨f, hf, rfl⟩
  have hstab : ∀ x ∈ Algebra.adjoin ℂ (Set.range fun k : Fin V.rank => gelfA (unitOp hθ V τ) k.val),
      ∀ w ∈ W, x w ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hS (τ, j)
    | algebraMap r =>
      intro w hw
      simpa using W.smul_mem r hw
    | add x y _ _ hx hy => exact fun w hw => add_mem (hx w hw) (hy w hw)
    | mul x y _ _ hx hy => exact fun w hw => hx _ (hy w hw)
  exact ⟨_, hstab _ (gelfA_mem_adjoin_low _ _ _ (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) k) f hf, (gelf_eq hθ τ k f).symm⟩

end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.CoreGL.CapScalar

def linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun Z := ∑ a, ∑ b, Z a b • E a b
  map_add' Z W := by simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c Z := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem linOf_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin n) :
    linOf E (Matrix.single a b 1) = E a b := by
  classical
  change ∑ i, ∑ j, (Matrix.single a b (1 : ℂ)) i j • E i j = E a b
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj; simp [Matrix.single_apply, Ne.symm hj]
  · simp
  · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [Matrix.single_apply, Ne.symm hi]
  · simp

theorem glRel_linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M) :
    Formalism.REAL.GlRel fun i j => linOf E (M i j) := by
  have h : Formalism.REAL.GlRel (fun i j => linOf E (Matrix.single i j 1)) := by
    simpa only [linOf_single] using hE
  intro a b c d
  simp only
  rw [GlobalTheory.CapelliLowest.lie_of_glRel (linOf E) h, hM a b c d, map_sub, apply_ite (linOf E), apply_ite (linOf E), map_zero]

theorem qdet_commute {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M)
    (hs : Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) = ⊤) (v : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    linOf E Z * Formalism.REAL.qdet (fun i j => linOf E (M i j)) v = Formalism.REAL.qdet (fun i j => linOf E (M i j)) v * linOf E Z := by
  have hZ : Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) := hs ▸ Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact (Formalism.REAL.qDetCentral A n _ (glRel_linOf hE hM) v p.1 p.2).symm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), add_mul, mul_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]

end GlobalTheory.CompanionTheory.CoreGL.CapScalar

namespace GlobalTheory.CompanionTheory.CoreGL

open GlobalTheory.CompanionTheory.CoreGL.CapScalar GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

attribute [local instance 100] LieRing.ofAssociativeRing

theorem qdet_scalar_of_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Submodule.span ℂ (Set.range fun p : Fin V.rank × Fin V.rank => M p.1 p.2) = ⊤ → ∀ (c : ℕ → ℂ) (v : ℂ), ∃ s : ℂ,
      ∀ f : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ k, gelf θ V τ k f.1 = c k • f.1) →
        Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v f = s • f := by
  intro D θ hθ V τ M hM hsp c v
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨P, Q, hPQ, h⟩ := GlobalTheory.T.unitary_lie_generators_rep _ _ (R.1 τ).1 (R.1 τ).2
  obtain ⟨h1, h2⟩ := h (EnvAt V τ) (fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add (f := _)])
    (fun c X => by
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul])
  set E : Fin V.rank → Fin V.rank → EnvAt V τ := fun a b =>
    UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] P a b) + Complex.I • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Q a b) with hEdef

  have hcomm := qdet_commute h1 hM hsp v
  set z : EnvAt V τ := Formalism.REAL.qdet (fun i j => linOf E (M i j)) v with hz
  have hι : ∀ X : LieAt V τ, UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * z = z * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
    intro X
    have hX := h2 X
    generalize UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) = y at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      have := hcomm (Matrix.single p.1 p.2 1)
      rwa [linOf_single] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  obtain ⟨cg, hc, hg⟩ := exists_gelf R τ
  have hcen : z ∈ Subalgebra.center ℂ (EnvAt V τ) := by
    rw [Subalgebra.mem_center_iff]
    intro u
    have : u ∈ Subalgebra.centralizer ℂ ({z} : Set (EnvAt V τ)) := by
      obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
      refine Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun x hx => ?_) _
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (hι X).symm
    rw [Subalgebra.mem_centralizer_iff] at this
    exact (this z rfl).symm

  have key : ∀ y ∈ Algebra.adjoin ℂ (Set.range cg), ∃ s : ℂ, ∀ ψ : SmF θ V,
      (∀ k, gelf θ V τ k ψ.1 = c k • ψ.1) → envRep R τ y ψ = s • ψ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨c k, fun ψ e => Subtype.ext ((hg k ψ).symm.trans (e k))⟩
    | algebraMap r => exact ⟨r, fun ψ _ => by rw [AlgHom.commutes]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s + t, fun ψ e => by rw [map_add (f := _), LinearMap.add_apply, hs ψ e, ht ψ e, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s * t, fun ψ e => by
        rw [map_mul, Module.End.mul_apply, ht ψ e, map_smul, hs ψ e, smul_smul, mul_comm]⟩
  rw [hc] at hcen
  obtain ⟨s, hs⟩ := key z hcen

  have e : GlobalTheory.Mem.AutSpace.SmFun θ V = SmF θ V := Submodule.ext fun φ => smooth_iff R φ
  let T := (LinearEquiv.ofEq _ _ e).conjAlgEquiv ℂ
  have k0 : ∀ a b, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1)) = envRep R τ (E a b) := by
    intro a b
    rw [hEdef]
    simp only [map_add (f := _), map_smul, envRep_ι]
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change RderC θ V τ (Matrix.single a b 1) φ.1 = _
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]
    rfl
  have k1 : ∀ Z, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ Z) = envRep R τ (linOf E Z) := by
    intro Z
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    change _ = envRep R τ (∑ a, ∑ b, Z a b • E a b)

    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, k0]
  have k2 : T (Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v) = envRep R τ z := by
    have a1 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet T.toAlgHom (fun i j => GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (M i j)) v
    have a2 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet (envRep R τ) (fun i j => linOf E (M i j)) v
    change T _ = _ at a1
    rw [a1, hz, a2]
    congr 1
    funext i j
    exact k1 (M i j)
  refine ⟨s, fun f hf => ?_⟩
  have k3 := congrArg (fun S : Module.End ℂ (SmF θ V) => (S (LinearEquiv.ofEq _ _ e f)).1) k2
  have k4 := hs (LinearEquiv.ofEq _ _ e f) hf
  exact Subtype.ext (k3.trans (congrArg Subtype.val k4))

end GlobalTheory.CompanionTheory.CoreGL

end
end
