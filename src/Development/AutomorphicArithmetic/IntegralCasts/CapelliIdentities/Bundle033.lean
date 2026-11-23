module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Submodule
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.SimpleModule.Isotypic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Basic.Complex.BigOperators
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

theorem UpperTheory.ae_translate_eq :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace X]
        (μ : MeasureTheory.Measure G) [μ.IsMulRightInvariant] (ν : MeasureTheory.Measure X) (q : G → X) (ρ : X → X) (g : G)
        (v v' : X → ℂ) (φ : G → ℂ), MeasureTheory.Measure.QuasiMeasurePreserving q μ ν → (∀ y, ρ (q y) = q (y * g)) →
        (v' =ᵐ[ν] fun x => v (ρ x)) → (∀ᵐ y ∂μ, v (q y) = φ y) → ∀ᵐ y ∂μ, v' (q y) = φ (y * g) := by
  intro G X _ _ _ _ μ _ ν q ρ g v v' φ hq hρ hv hφ
  have h1 : ∀ᵐ y ∂μ, v' (q y) = v (ρ (q y)) := MeasureTheory.Measure.QuasiMeasurePreserving.ae hq hv
  have h2 : ∀ᵐ y ∂μ, v (q (y * g)) = φ (y * g) :=
    (MeasureTheory.measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hφ
  filter_upwards [h1, h2] with y a b
  rw [a, hρ, b]
end

section

theorem UpperTheory.trace_eq_sum_re_cm_type :
    ∀ {E : Type} [Field E] [NumberField E] {Ψ : Type} [Fintype Ψ] (φ : Ψ → (E →+* ℂ)),
        Function.Injective φ →
        (∀ s : E →+* ℂ, (∃ τ, φ τ = s) ↔ ¬ ∃ τ, φ τ = (starRingEnd ℂ).comp s) →
        ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ, 2 * (φ τ x).re := by
  intro E _ _ Ψ _ φ hinj h x
  classical
  have hcc : ∀ s : E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext y
    simp
  let g : Ψ ⊕ Ψ → (E →+* ℂ) := Sum.elim φ (fun τ => (starRingEnd ℂ).comp (φ τ))
  have hg : Function.Bijective g := by
    constructor
    · rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (hinj hab)
      · exact absurd ⟨a, hab⟩ ((h (φ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, hab.symm⟩ ((h (φ a)).1 ⟨a, rfl⟩)
      · have h2 := congrArg (fun s => (starRingEnd ℂ).comp s) hab
        simp only [g, Sum.elim_inr, hcc] at h2
        exact congrArg Sum.inr (hinj h2)
    · intro s
      by_cases hs : ∃ τ, φ τ = s
      · obtain ⟨τ, hτ⟩ := hs
        exact ⟨Sum.inl τ, hτ⟩
      · obtain ⟨τ, hτ⟩ := not_not.1 (fun hn => hs ((h s).2 hn))
        refine ⟨Sum.inr τ, ?_⟩
        simp only [g, Sum.elim_inr, hτ, hcc]
  have h1 : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ s : E →+* ℂ, s x := by
    have h0 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := x)
    rw [eq_ratCast] at h0
    rw [h0]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun s => rfl)).symm
  rw [← Fintype.sum_bijective g hg (fun t => g t x) (fun s => s x) (fun _ => rfl),
    Fintype.sum_sum_type, ← Finset.sum_add_distrib] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.ratCast_re, Complex.re_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [g, two_mul]
end

section

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.Qk58.agree_of_adjoin :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] (φ ψ : E →+* ℂ) {a b : E},
    (φ : E → ℂ) a = (ψ : E → ℂ) a → b ∈ ℚ⟮a⟯ → (φ : E → ℂ) b = (ψ : E → ℂ) b := by
  intro E _ _ φ ψ a b ha hb
  induction hb using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ha
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
end

section

theorem UpperTheory.Reformulated.B.Qe21.emb_two :
    ∀ {K M : Type} [inst : Field K] [NumberField K]
    [inst_2 : Field M] [NumberField M] [inst_4 : Algebra K M] [IsGalois K M],
    Module.finrank K M = (2 : ℕ) →
      ∀ (σ : Gal(M/K)),
        σ ≠ (1 : Gal(M/K)) →
          ∀ (τ τ' : M →+* ℂ),
            τ ≠ τ' →
              τ.comp (Algebra.algebraMap K M) = τ'.comp (Algebra.algebraMap K M) →
                τ.comp σ.toRingEquiv.toRingHom = τ' := by
  intro K M _ _ _ _ _ _ h2 σ hσ τ τ' hne hc
  obtain ⟨ρ, hρ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq τ τ' hc
  have hcard : Nat.card Gal(M/K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Gal(M/K))).1 hcard
  have h1 : ρ.symm ≠ 1 := by
    intro h
    apply hne
    rw [← hρ, h]
    ext x
    rfl
  have h3 : σ = ρ.symm := (hy σ hσ).trans (hy _ h1).symm
  rw [← hρ, h3]
  ext x
  rfl
end

section

private lemma sepCore {R S N ι : Type} [Ring R] [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [AddCommGroup N] [Module R N] (f : ι → S →ₗ[R] N)
    (h : ⨆ i, LinearMap.range (f i) = ⊤) {x : N} (hx : x ≠ 0) :
    ∃ p : N →ₗ[R] S, p x ≠ 0 := by
  have hss : ∀ i, IsSemisimpleModule R (LinearMap.range (f i)) := fun i => .range (f i)
  have : IsSemisimpleModule R N := isSemisimpleModule_of_isSemisimpleModule_submodule' hss h
  have hiso : IsIsotypicOfType R N S := by
    apply IsIsotypicOfType.of_isotypicComponent_eq_top
    rw [eq_top_iff, ← h]
    refine iSup_le fun i => ?_
    rcases (f i).injective_or_eq_zero with hi | hi
    · exact le_sSup ⟨(LinearEquiv.ofInjective (f i) hi).symm⟩
    · rw [hi, LinearMap.range_zero]
      exact bot_le
  obtain ⟨κ, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  have hne : e x ≠ 0 := (LinearEquiv.map_ne_zero_iff e).mpr hx
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  exact ⟨(Finsupp.lapply i) ∘ₗ e.toLinearMap, by simpa using hi⟩

theorem UpperTheory.irreducible_projection_exists :
    ∀ {H V M : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
        (σ : Representation ℂ H V) (ρ : Representation ℂ H M), σ.IsIrreducible →
        ∀ (Y : Submodule ℂ M),
          Y ≤ ⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
            LinearMap.range f.1 →
          ∀ {F : M}, F ∈ Y → F ≠ 0 →
            ∃ p : M →ₗ[ℂ] V, (∀ (g : H), ∀ y ∈ Y, p (ρ g y) = σ g (p y)) ∧ p F ≠ 0 := by
  intro H V M _ _ _ _ _ σ ρ hσ Y hY F hF hF0
  have hinv : ∀ (g : H) {y : M}, y ∈ Y → ρ g y ∈ Y := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => ρ g y ∈ Y) (hY hy) ?_ ?_ ?_
    · rintro ⟨f, hf, hr⟩ x ⟨v, rfl⟩
      rw [← hf g v]
      exact hr ⟨_, rfl⟩
    · simp
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Y.add_mem ha hb
  let Ys : Subrepresentation ρ := ⟨Y, hinv⟩
  let τ : Representation ℂ H Y := Ys.toRepresentation
  let φ : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y } →
      Representation.IntertwiningMap σ τ := fun f =>
    (f.1.codRestrict Y (fun v => f.2.2 ⟨v, rfl⟩)).intertwiningMap_of_isIntertwiningMap σ τ
      (fun g v => Subtype.ext (f.2.1 g v))
  let ψ := fun i => Representation.IntertwiningMap.equivLinearMapAsModule σ τ (φ i)
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have hall : ∀ y ∈ (⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
      LinearMap.range f.1), ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i) := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i)) hy ?_ ?_ ?_
    · rintro f x ⟨v, rfl⟩
      exact ⟨f.2.2 ⟨v, rfl⟩, Submodule.mem_iSup_of_mem f ⟨v, rfl⟩⟩
    · exact ⟨Y.zero_mem, Submodule.zero_mem _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨Y.add_mem ha hb, Submodule.add_mem _ ha' hb'⟩
  have htop : ⨆ i, LinearMap.range (ψ i) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨_, hx⟩ := hall (x : Y).1 (hY (x : Y).2)
    exact hx
  obtain ⟨p, hp⟩ := sepCore ψ htop (x := (show τ.asModule from (⟨F, hF⟩ : Y)))
    (fun h => hF0 (congrArg Subtype.val (show (⟨F, hF⟩ : Y) = 0 from h)))
  let p' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm p
  obtain ⟨q, hq⟩ := LinearMap.exists_extend p'.toLinearMap
  have hqy : ∀ (y : M) (hy : y ∈ Y), q y = p' ⟨y, hy⟩ := fun y hy =>
    congrArg (fun l => l (⟨y, hy⟩ : Y)) hq
  refine ⟨q, fun g y hy => ?_, ?_⟩
  · rw [hqy _ (hinv g hy), hqy _ hy]
    exact Representation.IntertwiningMap.isIntertwining τ σ p' g ⟨y, hy⟩
  · rw [hqy _ hF]
    exact hp
end

section

noncomputable def UpperTheory.Reformulated.B.SubgroupFixed.HasFixed :
    {Γ V : Type} →
      [inst : Group Γ] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ Γ V → Subgroup Γ → Prop :=
    fun {Γ V : Type} [Group Γ] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ Γ V) (U : Subgroup Γ) ↦
      ∃ (v : V), v ≠ (0 : V) ∧ ∀ u ∈ U, ((ρ : Γ → V →ₗ[ℂ] V) u : V → V) v = v

private lemma UpperTheory.Reformulated.B.SubgroupFixed.core {R M N : Type*} [Ring R] [AddCommGroup M] [_root_.Module R M]
    [AddCommGroup N] [_root_.Module R N] [IsSimpleModule R M]
    (hsup : ∀ S : Submodule R N, (∀ f : M →ₗ[R] N, LinearMap.range f ≤ S) → S = ⊤)
    (W : Submodule R N) (hW : W ≠ ⊥) :
    ∃ g : M →ₗ[R] N, Function.Injective g ∧ LinearMap.range g ≤ W := by
  have hss : IsSemisimpleModule R N := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun f : M →ₗ[R] N => LinearMap.range f) (fun f => IsSemisimpleModule.range f) ?_
    exact hsup _ (fun f => le_iSup (fun f : M →ₗ[R] N => LinearMap.range f) f)
  obtain ⟨C, hC⟩ := exists_isCompl W
  let p : N →ₗ[R] W := W.linearProjOfIsCompl C hC
  have hex : ∃ f : M →ₗ[R] N, p ∘ₗ f ≠ 0 := by
    by_contra hno
    push Not at hno
    have htop : LinearMap.ker p = ⊤ := hsup _ (fun f => by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (hno f) x)
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have h1 : p w = 0 := by
      have : w ∈ LinearMap.ker p := htop ▸ Submodule.mem_top
      exact this
    have h2 : p w = ⟨w, hw⟩ := Submodule.linearProjOfIsCompl_apply_left hC ⟨w, hw⟩
    have h3 : (⟨w, hw⟩ : W) = 0 := h2.symm.trans h1
    simpa using congrArg Subtype.val h3
  obtain ⟨f, hf⟩ := hex
  have hinj := (LinearMap.injective_or_eq_zero (p ∘ₗ f)).resolve_right hf
  refine ⟨W.subtype ∘ₗ p ∘ₗ f, W.injective_subtype.comp hinj, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (p (f x)).2

theorem UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed :
    ∀ {Γ X V : Type} [inst : Group Γ] [inst_1 : AddCommGroup X] [inst_2 : _root_.Module ℂ X] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (σ : Representation ℂ Γ X),
      σ.IsIrreducible →
        ∀ (τ : Representation ℂ Γ V),
          ⨆ (f :
                { f : X →ₗ[ℂ] V //
                  ∀ (g : Γ) (v : X),
                    (f : X → V) (((σ : Γ → X →ₗ[ℂ] X) g : X → X) v) = ((τ : Γ → V →ₗ[ℂ] V) g : V → V) ((f : X → V) v) }),
                (↑f : X →ₗ[ℂ] V).range =
              ⊤ →
            ∀ (W : Submodule ℂ V),
              (∀ (g : Γ), ∀ v ∈ W, ((τ : Γ → V →ₗ[ℂ] V) g : V → V) v ∈ W) →
                W ≠ ⊥ →
                  ∀ (K : Subgroup Γ),
                    UpperTheory.Reformulated.B.SubgroupFixed.HasFixed σ K → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ u ∈ K, ((τ : Γ → V →ₗ[ℂ] V) u : V → V) v = v := by
  intro Γ X V _ _ _ _ _ σ hσ τ h W hWinv hW K hK
  obtain ⟨x0, hx0, hfix⟩ := hK
  haveI : IsSimpleModule (MonoidAlgebra ℂ Γ) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let W' : Submodule (MonoidAlgebra ℂ Γ) τ.asModule :=
    { carrier := {x | τ.asModuleEquiv x ∈ W}
      add_mem' := fun {a b} ha hb => by
        show τ.asModuleEquiv (a + b) ∈ W
        rw [map_add (f := _)]
        exact W.add_mem ha hb
      zero_mem' := by
        show τ.asModuleEquiv 0 ∈ W
        rw [map_zero]
        exact W.zero_mem
      smul_mem' := fun r x hx => by
        show τ.asModuleEquiv (r • x) ∈ W
        rw [Representation.asModuleEquiv_map_smul]
        exact τ.asAlgebraHom_mem_of_forall_mem W hWinv _ hx r }
  have hW' : W' ≠ ⊥ := by
    intro hbot
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have hmem : τ.asModuleEquiv.symm w ∈ W' := by
      show τ.asModuleEquiv (τ.asModuleEquiv.symm w) ∈ W
      simpa using hw
    rw [hbot, Submodule.mem_bot] at hmem
    simpa using hmem
  have hsup : ∀ S : Submodule (MonoidAlgebra ℂ Γ) τ.asModule,
      (∀ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule, LinearMap.range f ≤ S) → S = ⊤ := by
    intro S hS
    let S0 : Submodule ℂ V :=
      (S.restrictScalars ℂ).comap (τ.asModuleEquiv.symm : V →ₗ[ℂ] τ.asModule)
    have hS0 : S0 = ⊤ := by
      rw [eq_top_iff, ← h]
      refine iSup_le fun f => ?_
      rintro _ ⟨x, rfl⟩
      let F : Representation.IntertwiningMap σ τ :=
        f.1.intertwiningMap_of_isIntertwiningMap σ τ f.2
      exact hS (Representation.IntertwiningMap.equivLinearMapAsModule σ τ F)
        ⟨σ.asModuleEquiv.symm x, rfl⟩
    rw [eq_top_iff]
    intro y _
    have hy : τ.asModuleEquiv y ∈ S0 := hS0 ▸ Submodule.mem_top
    simpa [S0] using hy
  obtain ⟨g, hg, hgW⟩ := UpperTheory.Reformulated.B.SubgroupFixed.core hsup W' hW'
  refine ⟨τ.asModuleEquiv (g (σ.asModuleEquiv.symm x0)), hgW ⟨_, rfl⟩, ?_, ?_⟩
  · intro h0
    have h1 : g (σ.asModuleEquiv.symm x0) = 0 := by simpa using h0
    have h2 : σ.asModuleEquiv.symm x0 = 0 := hg (h1.trans (map_zero g).symm)
    exact hx0 (by simpa using h2)
  · intro u hu
    apply τ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply, ← map_smul,
      ← Representation.asModuleEquiv_symm_map_rho, hfix u hu]
end

section

noncomputable def UpperTheory.Reformulated.B.Yoa6.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.Yoa6.Helpers

private noncomputable def herm {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v))
    (by intro v v' w; simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)
    (by intro v w w'; simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)

private lemma herm_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) (v w : V) :
    herm B c v w = c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.Yoa6.Helpers

open UpperTheory.Reformulated.B.Yoa6.Helpers in
theorem UpperTheory.Reformulated.B.Yoa6.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.Yoa6.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ h
  obtain ⟨B, hB0, hBinv⟩ := h
  have hherm : ∀ (c : ℂ) (v w : V), herm B c w v = starRingEnd ℂ (herm B c v w) := by
    intro c v w
    simp only [herm_apply, map_add (f := _), map_mul, Complex.conj_conj]
    ring
  have hinv : ∀ (c : ℂ) (g : G) (v w : V), herm B c (ρ g v) (ρ g w) = herm B c v w := by
    intro c g v w
    simp only [herm_apply, hBinv]
  by_cases h1 : herm B 1 = 0
  · refine ⟨herm B Complex.I, ?_, hherm Complex.I, hinv Complex.I⟩
    intro hI
    apply hB0
    ext v w
    have e1 := congrArg (fun f => f v w) h1
    have e2 := congrArg (fun f => f v w) hI
    simp only [herm_apply, LinearMap.zero_apply, map_one, one_mul, Complex.conj_I] at e1 e2
    simp only [LinearMap.zero_apply]
    have : (2 * Complex.I) * B v w = 0 := by
      linear_combination Complex.I * e1 + e2
    rcases mul_eq_zero.mp this with h | h
    · exfalso; simp [Complex.ext_iff] at h
    · exact h
  · exact ⟨herm B 1, h1, hherm 1, hinv 1⟩
end

section

noncomputable def UpperTheory.Reformulated.B.EvaluationMap.coeffSpan :
    {K W : Type} →
      [inst : Group K] →
        [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module ℂ W] → Representation ℂ K W → Submodule ℂ (K → ℂ) :=
    fun {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W] (ρ : Representation ℂ K W) ↦
      Submodule.span ℂ
        {f : K → ℂ | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun (k : K) ↦ (ℓ : W → ℂ) (((ρ : K → W →ₗ[ℂ] W) k : W → W) w)}

namespace UpperTheory.Reformulated.B.EvaluationMap.Helpers

private noncomputable def Φ {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W]
    (ρ : Representation ℂ K W) : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (K → ℂ) where
  toFun φ := fun k => φ (ρ k)
  map_add' φ ψ := by funext k; simp
  map_smul' c φ := by funext k; simp

private noncomputable def evw {W : Type} [AddCommGroup W] [_root_.Module ℂ W]
    (ℓ : Module.Dual ℂ W) (w : W) : Module.Dual ℂ (W →ₗ[ℂ] W) where
  toFun A := ℓ (A w)
  map_add' A B := by simp
  map_smul' c A := by simp

end UpperTheory.Reformulated.B.EvaluationMap.Helpers

open UpperTheory.Reformulated.B.EvaluationMap.Helpers in
theorem UpperTheory.Reformulated.B.EvaluationMap.main :
    ∀ {K W : Type} [inst : Group K] [inst_1 : AddCommGroup W] [inst_2 : _root_.Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ K W), FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ) := by
  intro K W _ _ _ _ ρ
  have hle : UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ ≤ LinearMap.range (Φ ρ) := by
    unfold UpperTheory.Reformulated.B.EvaluationMap.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨evw ℓ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
end

section

noncomputable def UpperTheory.Reformulated.B.StabilizerSubgroup.stabG :
    {G V : Type} →
      [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G _V} _ _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha => by
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
end
