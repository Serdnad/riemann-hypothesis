module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Mathlib.RingTheory.Flat.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import ReciprocityTheory.BasicDefinitions.AdRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle232
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Mathlib.RingTheory.Flat.Stability
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

theorem isOpen_of_fg_of_span_eq_top {LL O V : Type} [Field LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (hO : IsOpen (Set.range (algebraMap O LL))) (M : Submodule O V) (hfg : M.FG)
    (hspan : Submodule.span LL (M : Set V) = ⊤) : IsOpen (M : Set V) := by
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hbM : ∀ i, b i ∈ M := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hsurj : Function.Surjective (Fintype.linearCombination LL b) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← hspan, ← hb,
      Submodule.span_span_of_tower]
  have hopen : IsOpenMap (Fintype.linearCombination LL b) :=
    IsModuleTopology.isOpenMap_of_surjective hsurj
  haveI := IsModuleTopology.topologicalAddGroup LL V
  have hU : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.range (algebraMap O LL)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hO
  refine M.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset ((hopen _ hU).mem_nhds ⟨0, fun _ _ => ⟨0, by simp⟩, map_zero _⟩) ?_)
  rintro _ ⟨x, hx, rfl⟩
  rw [Fintype.linearCombination_apply]
  refine M.sum_mem fun i _ => ?_
  obtain ⟨a, ha⟩ := hx i (Set.mem_univ i)
  rw [← ha, algebraMap_smul]
  exact M.smul_mem a (hbM i)

theorem locLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ T : LocLat G Qp LL O, IsOpen (T.L.T : Set T.V) := by
  intro G _ _ Qp _ _ LL _ _ _ O _ _ h T
  haveI := h.2.2.2.1
  exact isOpen_of_fg_of_span_eq_top h.2.2.2.2 T.L.T T.L.fg T.L.span

end GlobalTheory.Cyc
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamDescent

theorem finrank_fixed {R G M K L : Type} [Field R] [Group G] [AddCommGroup M] [Module R M]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : G →* Module.End R M) (m : L →+* Module.End R M) (ε : G →* (L ≃ₐ[K] L))
    (hs : Function.Surjective ε) (hε : ∀ g a x, A g (m a x) = m (ε g a) (A g x))
    (D D' : Submodule R M) (hD : ∀ x, x ∈ D ↔ ∀ g, A g x = x)
    (hD' : ∀ x, x ∈ D' ↔ ∀ g, ε g = 1 → A g x = x) :
    Module.finrank R D' = Module.finrank K L * Module.finrank R D := by
  classical
  have hc : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank K L
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hc).symm
  let μ : Module.Basis (L ≃ₐ[K] L) K L := b.traceDual
  let Pm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ i => σ (b i)
  let Qm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun j σ => σ (μ j)
  have hQP : Qm * Pm = 1 := by
    ext j i
    simp only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, ← map_mul]
    rw [← trace_eq_sum_automorphisms, Module.Basis.trace_traceDual_mul, Matrix.one_apply]
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.1 hQP
  have h1 : ∀ j i, ∑ σ : L ≃ₐ[K] L, σ (μ j) * σ (b i) = if j = i then 1 else 0 := fun j i => by
    have := congrFun (congrFun hQP j) i
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply] using this
  have h2 : ∀ σ : L ≃ₐ[K] L, ∑ i, b i * σ (μ i) = if 1 = σ then 1 else 0 := fun σ => by
    have := congrFun (congrFun hPQ 1) σ
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply,
      AlgEquiv.one_apply] using this
  choose s hs' using hs
  have hm : ∀ a, ∀ x ∈ D', m a x ∈ D' := fun a x hx => by
    rw [hD'] at hx ⊢
    intro g hg
    rw [hε, hg, hx g hg, AlgEquiv.one_apply]
  have hDD : D ≤ D' := fun x hx => (hD' x).2 fun g _ => (hD x).1 hx g
  have hA : ∀ x ∈ D', ∀ g g', ε g = ε g' → A g x = A g' x := fun x hx g g' h => by
    have := (hD' x).1 hx (g'⁻¹ * g) (by rw [map_mul, map_inv, h, inv_mul_cancel])
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  let Φ₀ : ((L ≃ₐ[K] L) → D) →ₗ[R] M :=
    ∑ i, (m (b i)) ∘ₗ D.subtype ∘ₗ LinearMap.proj i
  have hΦ : ∀ x, Φ₀ x = ∑ i, m (b i) (x i) := fun x => by
    simp [Φ₀]
  have hinj : Function.Injective Φ₀ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h3 : ∀ σ : L ≃ₐ[K] L, ∑ i, m (σ (b i)) (x i) = 0 := fun σ => by
      have := congrArg (A (s σ)) hx

      rw [hΦ, map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hε, hs', (hD _).1 (x i).2]
    funext j
    apply Subtype.ext
    have h4 : ∑ σ : L ≃ₐ[K] L, m (σ (μ j)) (∑ i, m (σ (b i)) (x i)) = 0 := by
      simp only [h3, map_zero, Finset.sum_const_zero]

    simp only [map_sum, ← Module.End.mul_apply, ← map_mul m] at h4
    rw [Finset.sum_comm] at h4

    simp only [← LinearMap.sum_apply, ← map_sum m, h1] at h4
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)] at h4
    simpa using h4
  have hr : LinearMap.range Φ₀ = D' := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hΦ]
      exact D'.sum_mem fun i _ => hm _ _ (hDD (x i).2)
    · intro x hx
      refine ⟨fun i => ⟨∑ σ, A (s σ) (m (μ i) x), (hD _).2 fun g => ?_⟩, ?_⟩
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (ε g))
          (fun σ => A (s σ) (m (μ i) x))]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Module.End.mul_apply, ← map_mul]
        exact hA _ (hm _ _ hx) _ _ (by simp [hs'])
      · rw [hΦ]
        have hmm : ∀ a a' y, m a (m a' y) = m (a * a') y := fun a a' y => by
          rw [map_mul, Module.End.mul_apply]

        simp only [hε, hs', map_sum, hmm]
        rw [Finset.sum_comm]

        simp only [← LinearMap.sum_apply, ← map_sum m, h2]
        rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
        simpa using (hD' x).1 hx _ (hs' 1)
  rw [← hr, LinearMap.finrank_range_of_inj hinj]
  by_cases hf : Module.Finite R D
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
  · rw [Module.finrank_of_not_finite hf, mul_zero, Module.finrank_of_not_finite]
    intro h
    exact hf (Module.Finite.of_surjective
      (LinearMap.proj (R := R) (φ := fun _ : L ≃ₐ[K] L => D) (1 : L ≃ₐ[K] L))
      (fun y => ⟨fun _ => y, rfl⟩))


open GlobalTheory.JumpDescent TensorProduct in
theorem isDR_of_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l)
    (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) →
    ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  intro l _ P K K' LL hle h hst V _ _ _ _ ρ hρ
  unfold IsDR at hρ ⊢
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  let L : IntermediateField ↥K.1 (Om l) := IntermediateField.extendScalars h
  haveI : FiniteDimensional ℚ_[l] ↥L := K'.2
  haveI : FiniteDimensional ↥K.1 ↥L := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  haveI : Normal ↥K.1 (Om l) := Normal.tower_top_of_normal ℚ_[l] _ _
  let e : ↥(GK K) ≃* (Om l ≃ₐ[↥K.1] Om l) := IntermediateField.fixingSubgroupEquiv K.1
  have he : ∀ (g : ↥(GK K)) (x : Om l), e g x = (g : GQ l) x := fun _ _ => rfl
  haveI : Normal ↥K.1 ↥L := IntermediateField.normal_iff_forall_map_le'.2 fun σ => by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := e.surjective σ
    exact hst g.1 g.2 x hx
  haveI : IsGalois ↥K.1 ↥L := {}
  let ε : ↥(GK K) →* (↥L ≃ₐ[↥K.1] ↥L) := (AlgEquiv.restrictNormalHom ↥L).comp e.toMonoidHom
  have hεa : ∀ (g : ↥(GK K)) (x : ↥L), ((ε g x : ↥L) : Om l) = (g : GQ l) x := fun g x =>
    AlgEquiv.restrictNormalHom_apply L (e g) x
  let A : ↥(GK K) →* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := actVdR (P.PD K) ρ
      map_one' := by ext v b; simp [actVdR_tmul]
      map_mul' := fun g g' => by ext v b; simp [actVdR_tmul] }
  let m : ↥L →+* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun c => mulOm P (c : Om l)
      map_one' := by ext v b; simp [mulOm_tmul]
      map_mul' := fun g g' => by ext v b; simp [mulOm_tmul, mul_assoc]
      map_zero' := by ext v b; simp [mulOm_tmul]
      map_add' := fun g g' => by ext v b; simp [mulOm_tmul, add_mul, tmul_add] }
  have key := finrank_fixed A m ε
    ((AlgEquiv.restrictNormalHom_surjective (F := ↥K.1) (K₁ := ↥L) (Om l)).comp e.surjective)
    (fun g c x => by
      change actVdR (P.PD K) ρ g (mulOm (LL := ↥LL.1) P (c : Om l) x) =
        mulOm (LL := ↥LL.1) P ((ε g c : ↥L) : Om l) (actVdR (P.PD K) ρ g x)
      rw [hεa]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v b => simp [mulOm_tmul, actVdR_tmul, P.PD_actdR, P.actQdR_Om]
      | add y z hy hz => simp only [map_add (f := _), hy, hz])
    (DdR (P.PD K) ρ) (DdR (P.PD K') (ρ.comp (Subgroup.inclusion hle)))
    (fun x => mem_DdR P K ρ x)
    (fun x => by
      rw [mem_DdR]
      constructor
      · intro hx g hg
        have hg' : g.1 ∈ GK K' := fun a => by
          have := hεa g ⟨a.1, a.2⟩
          rw [hg] at this
          exact this.symm
        have := hx ⟨g.1, hg'⟩
        rw [actVdR_comp P h] at this
        exact this
      · intro hx g
        rw [actVdR_comp P h]
        apply hx
        ext a
        rw [hεa]
        exact g.2 ⟨a.1, a.2⟩)
  have hfin : Module.finrank ℚ_[l] ↥K'.1 = Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥K.1 ↥L :=
    (Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥L).symm
  have hpos : 0 < Module.finrank ↥K.1 ↥L := Module.finrank_pos
  rw [key, hfin] at hρ
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hρ]
  ring

end GlobalTheory.DeRhamDescent
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.FlatLocCompl

theorem mem_pow_smul_top_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (r : R) (k : ℕ) (z : S) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R S) ↔ z ∈ Ideal.span {(algebraMap R S r) ^ k} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨e, -, rfl⟩
    exact ⟨e, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, Submodule.mem_top, by rw [Algebra.smul_def, map_pow]⟩

theorem mem_pow_smul_top_self_iff {R : Type} [CommRing R] (r : R) (k : ℕ) (z : R) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R R) ↔ z ∈ Ideal.span {r ^ k} := by
  rw [mem_pow_smul_top_iff]; rfl

theorem flat_of_levels {B E : Type} [CommRing B] [IsNoetherianRing B] [CommRing E] [Algebra B E] (p : B)
    (hc : IsAdicComplete (Ideal.span {algebraMap B E p}) E)
    (hinj : ∀ (b : B) (k : ℕ), algebraMap B E b ∈ Ideal.span {(algebraMap B E p) ^ k} →
      b ∈ Ideal.span {p ^ k})
    (hden : ∀ (y : E) (k : ℕ), ∃ b : B, algebraMap B E b - y ∈ Ideal.span {(algebraMap B E p) ^ k}) :
    Module.Flat B E := by
  set I : Ideal B := Ideal.span {p} with hI
  haveI : IsAdicComplete I E := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := E)]
    rwa [hI, Ideal.map_span, Set.image_singleton]
  let f : B →ₗ[B] E := Algebra.linearMap B E
  have hle : ∀ k, (I ^ k • ⊤ : Submodule B B) ≤ (I ^ k • ⊤ : Submodule B E).comap f := by
    intro k z hz
    rw [Submodule.mem_comap, mem_pow_smul_top_iff]
    rw [mem_pow_smul_top_self_iff, Ideal.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    exact Ideal.mem_span_singleton.2 ⟨algebraMap B E c, by simp [f, map_pow]⟩
  let fk : ∀ k : ℕ, AdicCompletion I B →ₗ[B] E ⧸ (I ^ k • ⊤ : Submodule B E) := fun k =>
    (Submodule.mapQ _ _ f (hle k)) ∘ₗ AdicCompletion.eval I B k
  have hfk : ∀ {m n : ℕ} (hmn : m ≤ n), Submodule.factorPow I E hmn ∘ₗ fk n = fk m := by
    intro m n hmn
    refine LinearMap.ext fun x => ?_
    simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply]
    rw [← AdicCompletion.transitionMap_comp_eval_apply I B hmn x]
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [← hb]
    rfl
  let G : AdicCompletion I B →ₗ[B] E := IsAdicComplete.lift I fk hfk
  have hG : ∀ k x, Submodule.Quotient.mk (p := (I ^ k • ⊤ : Submodule B E)) (G x) = fk k x :=
    fun k x => IsAdicComplete.mk_lift I hfk k x
  have hbij : Function.Bijective G := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      ext k
      have h1 := hG k x
      rw [hx, Submodule.Quotient.mk_zero] at h1
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val k)
      have h2 : fk k x = Submodule.Quotient.mk (f b) := by
        simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply, ← hb]; rfl
      rw [h2, eq_comm, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff] at h1
      rw [← hb, AdicCompletion.val_zero_apply, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_self_iff]
      exact hinj b k h1
    · intro y
      choose b hb using fun k => hden y k
      have hcau : ∀ k, b k ≡ b (k + 1) [SMOD (I ^ k • ⊤ : Submodule B B)] := by
        intro k
        rw [SModEq.sub_mem, mem_pow_smul_top_self_iff]
        apply hinj
        have h3 : algebraMap B E (b k - b (k + 1)) =
            (algebraMap B E (b k) - y) - (algebraMap B E (b (k + 1)) - y) := by rw [map_sub]; ring
        rw [h3]
        refine Ideal.sub_mem _ (hb k) ?_
        refine Ideal.span_singleton_le_span_singleton.2 ?_ (hb (k + 1))
        exact pow_dvd_pow _ (Nat.le_succ k)
      refine ⟨AdicCompletion.mk I B (AdicCompletion.AdicCauchySequence.mk I B b hcau), ?_⟩
      rw [IsHausdorff.eq_iff_smodEq (I := I)]
      intro k
      rw [SModEq, hG]
      change Submodule.Quotient.mk (f (b k)) = Submodule.Quotient.mk y
      rw [← SModEq, SModEq.sub_mem, mem_pow_smul_top_iff]
      exact hb k
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective G hbij).symm

end GlobalTheory.FlatLocCompl

namespace GlobalTheory.FlatLocCompl

theorem flat_letA (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E]
    [Algebra (LetA O n) E] (p : ℕ) (hπ : IsUnit (algebraMap (LetA O n) E letπ))
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hden : ∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) -
      algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k})
    (hsat : ∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) :
    Module.Flat (LetA O n) E := by
  let B := Localization.Away (letπ : LetA O n)
  let g : B →+* E := IsLocalization.Away.lift (S := B) (letπ : LetA O n) hπ
  letI : Algebra B E := g.toAlgebra
  have hg : ∀ a : LetA O n, algebraMap B E (algebraMap (LetA O n) B a) = algebraMap (LetA O n) E a :=
    fun a => IsLocalization.Away.lift_eq (S := B) (letπ : LetA O n) hπ a
  haveI : IsScalarTower (LetA O n) B E := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have hp : algebraMap B E (p : B) = (p : E) := map_natCast _ _
  haveI : Module.Flat B E := by
    refine flat_of_levels (p : B) (by rwa [hp]) ?_ ?_
    · intro b k hb
      rw [hp] at hb
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (letπ : LetA O n)) b
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B s = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} := by
        rw [← hg, ← h1, map_mul]
        exact Ideal.mul_mem_right _ _ hb
      obtain ⟨c, rfl⟩ := hsat a k h2
      refine Ideal.mem_span_singleton.2 ⟨IsLocalization.mk' B c s, ?_⟩
      show IsLocalization.mk' B ((p : LetA O n) ^ k * c) s = (p : B) ^ k * IsLocalization.mk' B c s
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    · intro y k
      obtain ⟨a, m, h⟩ := hden y k
      let s : Submonoid.powers (letπ : LetA O n) := ⟨letπ ^ m, m, rfl⟩
      refine ⟨IsLocalization.mk' B a s, ?_⟩
      rw [hp]
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B (letπ ^ m) = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap B E (IsLocalization.mk' B a s) * algebraMap (LetA O n) E (letπ ^ m) =
          algebraMap (LetA O n) E a := by rw [← hg, ← hg, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hπ.pow m
      rw [← map_pow] at hv
      have h3 : algebraMap B E (IsLocalization.mk' B a s) - y =
          -((y * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a) * ↑v⁻¹) := by
        rw [← h2, ← hv, neg_mul_eq_neg_mul, neg_sub, ← sub_mul, mul_assoc, Units.mul_inv, mul_one]
      rw [h3]
      exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ h)
  exact Module.Flat.trans (LetA O n) B E

end GlobalTheory.FlatLocCompl
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HalfTwist

theorem eta_char (D : D7) (w : PlE D.host) :
    D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
  have hu := D.naut.etaT_unr w
  have hinv := D.naut.etaTinv_def w
  have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hcard : Multiset.card (D.naut.frobEig (D.naut.locG D.naut.etaT w)) = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    have h0 := D.naut.frobEig_ne_zero _ hu
    rw [hb] at h0
    intro hb'
    exact h0 (by simp [hb'])
  have hinvb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {b⁻¹} := by
    rw [hinv.2, hb, Multiset.map_singleton]
  have hunr := D.naut.unr_char _ _ hd1 hu hinv.1
  have hf := D.naut.frobEig_char _ _ b⁻¹ hu hinv.1 hd1 hinvb
  rw [D.naut.unr_eq_lpUnr _ hunr, hf, hb, Multiset.map_singleton, mul_inv_cancel₀ hb0]

theorem eta_inf (D : D7) (hA : SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) :
    ∃ h : ℂ, D.naut.infG D.naut.etaT τ = {h} ∧ D.naut.infG D.naut.etaTinv τ = {-h} ∧
      (h = 1 / 2 ∨ h = -(1 / 2)) := by
  obtain ⟨h1, h2⟩ := hA.2.1 τ
  rcases h1 with h1 | h1
  · exact ⟨1 / 2, h1, by rw [h2, h1, Multiset.map_singleton], Or.inl rfl⟩
  · exact ⟨-(1 / 2), h1, by rw [h2, h1, Multiset.map_singleton], Or.inr rfl⟩

end GlobalTheory.HalfTwist

end

section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_continuous_cocycle_lift_of_subsingleton_H2 : ∀ (O G T M : Type) [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M] (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M), IsAdicComplete (Ideal.span {lam}) T → (∀ t : T, lam • t = 0 → t = 0) → Function.Surjective q → (∀ t, q t = 0 ↔ ∃ y, t = lam • y) → (∀ g t, q (π g t) = π' g (q t)) → (∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y) → Subsingleton (ReciprocityTheory.Def.H2 π' ⊤) → ∀ z ∈ ReciprocityTheory.Def.Z1 π' ⊤, ∃ c : G → T, (∀ g h, c (g * h) = c g + π g (c h)) ∧ (∀ g, q (c g) = z g) ∧ ∀ (a : ℕ) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, c g - c g₀ = lam ^ a • y := by
  first | exact @GlobalTheory.CocycleLift.exists_lift | exact GlobalTheory.CocycleLift.exists_lift | (intros; apply GlobalTheory.CocycleLift.exists_lift <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.natCard_H2_comp_equiv : ∀ {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (i : G ≃ₜ* Γ) (rho : Representation R Γ M), Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) := by
  first | exact @GlobalTheory.TransportH2.natCard_H2_comp | exact GlobalTheory.TransportH2.natCard_H2_comp | (intros; apply GlobalTheory.TransportH2.natCard_H2_comp <;> assumption)
end

section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_pow_smul_nhds_zero_basis : ∀ (LL O V : Type) [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V] (T : Submodule O V) (lam : O), T.FG → Submodule.span LL (T : Set V) = ⊤ → IsOpen (Set.range (algebraMap O LL)) → algebraMap O LL lam ≠ 0 → (∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (lam ^ a * x) ∈ U) → (∀ a : ℕ, {v : V | ∃ t ∈ T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ T, lam ^ a • t ∈ U := by
  first | exact @GlobalTheory.lattice_multiples_nhds_basis | exact GlobalTheory.lattice_multiples_nhds_basis | (intros; apply GlobalTheory.lattice_multiples_nhds_basis <;> assumption)
end
