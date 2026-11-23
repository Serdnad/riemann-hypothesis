module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

section

private theorem UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ s ∈ S, ∀ v ∈ N, s v ∈ N) → N = ⊥ ∨ N = ⊤) : S = ⊤ := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [eq_top_iff]
    intro f _
    rw [Subsingleton.elim f 0]
    exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun s hs v hv => N.smul_mem (⟨s, hs⟩ : S) hv) with h1 | h1
    · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).1 h1)
    · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).1 h1)
  rw [eq_top_iff]
  intro f _
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K
          (A := S) (V := V)).2 φ
        exact f.map_smul c v }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) :=
    b.ext fun i => hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem UpperTheory.Reformulated.B.Qe4.irrIffSpan :
    ∀ {K G ι : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : Group G]
    [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (ρ : G →* Matrix ι ι K),
    (∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, ((ρ : G → Matrix ι ι K) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔
      Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) = ⊤ := by
  intro K G ι _ _ _ _ _ ρ
  constructor
  · intro h
    have hmul : ∀ x y : Matrix ι ι K, x ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        x * y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
      exact ⟨a * c, map_mul ρ a c⟩
    let A : Subalgebra K (Matrix ι ι K) :=
      (Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K))).toSubalgebra
        (Submodule.subset_span ⟨1, map_one ρ⟩) hmul
    let e : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K) := Matrix.toLinAlgEquiv'
    have hS : A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) = ⊤ := by
      refine UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top _ fun N hN => h N fun g v hv => ?_
      exact hN (e (ρ g)) ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩ v hv
    rw [eq_top_iff]
    intro M _
    have hM : e M ∈ A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) := by
      rw [hS]; exact Algebra.mem_top
    obtain ⟨x, hx, hxe⟩ := hM
    have : x = M := e.injective hxe
    rw [← this]
    exact hx
  · intro h N hN
    have hall : ∀ M : Matrix ι ι K, ∀ v ∈ N, M.mulVec v ∈ N := by
      intro M v hv
      have hM : M ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
        rw [h]; exact Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g v hv
      | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
      | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
      | smul c x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem c hx
    by_cases hb : N = ⊥
    · exact Or.inl hb
    right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hb
    rw [eq_top_iff]
    intro w _
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv0
    have := hall (LinearMap.toMatrix' (φ.smulRight w)) v hv
    rw [LinearMap.toMatrix'_mulVec] at this
    simpa [hφ] using this
end

section

theorem UpperTheory.Reformulated.B.Qj3.burnside_end.{u_3, u_4} :
    ∀ {K : Type u_3} {V : Type u_4} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V)),
    (∀ (N : Submodule K V), (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤) → ∀ (f : Module.End K V), f ∈ S := by
  intro K V _ _ _ _ _ S h f
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : f = 0 := by ext v; exact Subsingleton.elim _ _
    rw [this]; exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun g hg v hv => N.smul_mem (⟨g, hg⟩ : S) hv) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff _ _ _).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff _ _ _).1 h1
  have hs := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := S) (V := V)).2
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := hs φ
        simp [Module.End.smul_def, Module.algebraMap_end_apply] }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) := by
    refine b.ext fun i => ?_
    exact hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]; exact r.2
end

section

noncomputable def UpperTheory.Reformulated.B.H13.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.H13.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.H13.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.H13.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.H13.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.H13.aux5 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (1 : Γ)) *
          (r : Γ → GL (Fin n) k) (1 : Γ) =
        (1 : GL (Fin n) k) := by
  intro Γ k _ _ n r χ
  simp

theorem UpperTheory.Reformulated.B.H13.aux6 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s t : Γ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (s * t)) *
          (r : Γ → GL (Fin n) k) (s * t) =
        (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s *
          ((Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) t) * (r : Γ → GL (Fin n) k) t) := by
  intro Γ k _ _ n r χ s t
  have hc : ∀ (c : kˣ) (A : GL (Fin n) k),
      A * Matrix.GeneralLinearGroup.scalar (Fin n) c = Matrix.GeneralLinearGroup.scalar (Fin n) c * A := by
    intro c A
    apply Units.ext
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute (c : k) (fun x => Commute.all _ _) (A : Matrix (Fin n) (Fin n) k)).eq.symm
  rw [map_mul, map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (r s), hc, mul_assoc]

noncomputable def UpperTheory.Reformulated.B.H13.tw :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* kˣ) → Γ →* GL (Fin n) k :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) ↦
      {
        toFun := fun (s : Γ) ↦
          (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s,
        map_one' := UpperTheory.Reformulated.B.H13.aux5 r χ, map_mul' := UpperTheory.Reformulated.B.H13.aux6 r χ : Γ →* GL (Fin n) k }

noncomputable def UpperTheory.Reformulated.B.H13.SchurTw :
    Prop :=
    ∀ (Γ Γ' k : Type) [inst : Group Γ] [inst_1 : Group Γ'] [inst_2 : Field k] [IsAlgClosed k] (n : ℕ)
      (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
      UpperTheory.Reformulated.B.H13.IsIrr (r.comp φ) →
        δ.comp φ = (1 : Γ' →* kˣ) → UpperTheory.Reformulated.B.H13.RepIso r (UpperTheory.Reformulated.B.H13.tw r δ) → δ = (1 : Γ →* kˣ)

theorem UpperTheory.Reformulated.B.H13.schur_twist_holds :
    UpperTheory.Reformulated.B.H13.SchurTw := by
  intro Γ Γ' k _ _ _ _ n r φ δ hirr hδ hiso
  obtain ⟨hne, -, hmin⟩ := hirr
  obtain ⟨g, hg⟩ := hiso
  have hg' : ∀ s : Γ, Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s * g = g * r s := by
    intro s
    have h : Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s = g * r s * g⁻¹ := hg s
    rw [h, inv_mul_cancel_right]
  have hcomm : ∀ t : Γ', r (φ t) * g = g * r (φ t) := by
    intro t
    have h1 : δ (φ t) = 1 := DFunLike.congr_fun hδ t
    have h := hg' (φ t)
    rwa [h1, map_one, one_mul] at h
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v : Fin n → k,
      v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c ↔
        (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have htop : Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c = ⊤ := by
    refine (hmin _ le_top ?_).resolve_left hc
    intro t v hv
    rw [hmem] at hv ⊢
    have h : (r (φ t) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k)
        = (g : Matrix (Fin n) (Fin n) k) * (r (φ t) : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    change (g : Matrix (Fin n) (Fin n) k).mulVec ((r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v)
      = c • (r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hgv : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [← hmem, htop]
    exact Submodule.mem_top
  have hcent : ∀ A : GL (Fin n) k, g * A = A * g := by
    intro A
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgv, hgv, Matrix.mulVec_smul]
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton (Fin n → k) inferInstance
  obtain ⟨i⟩ := hn
  refine MonoidHom.ext fun s => ?_
  have h := hg' s
  rw [hcent, mul_left_inj, mul_eq_right] at h
  have h2 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) i i) h
  apply Units.ext
  simpa using h2
end

section

noncomputable def UpperTheory.Reformulated.B.Qi17.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qi17.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qi17.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qi17.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.Qi17.schur_scalar :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qi17.IsIrr r →
        ∀ (g : GL (Fin n) k),
          (∀ (s : Γ), (r : Γ → GL (Fin n) k) s * g = g * (r : Γ → GL (Fin n) k) s) →
            ∃ (c : kˣ), (↑g : Matrix (Fin n) (Fin n) k) = (↑c : k) • (1 : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n r hr g hg
  obtain ⟨hne, -, hmin⟩ := hr
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hinv : UpperTheory.Reformulated.B.Qi17.IsInv r
      (Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c) := by
    intro s v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    have h : (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
        = (r s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hg s]
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have htop := (hmin _ le_top hinv).resolve_left hc
  have hgc : (g : Matrix (Fin n) (Fin n) k) = c • (1 : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c := by
      rw [htop]; exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hgc
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
    apply hv
    have h1 : (1 : Matrix (Fin n) (Fin n) k) = 0 := by
      rw [← g.mul_inv, hgc, zero_mul]
    rw [← Matrix.one_mulVec v, h1, Matrix.zero_mulVec]
  exact ⟨Units.mk0 c hc0, hgc⟩
end

section

theorem UpperTheory.Reformulated.B.CommonEigenvectorOfCommutingSet.common_eig :
    ∀ {k : Type} [inst : Field k] [IsAlgClosed k]
    {V : Type} [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V] [FiniteDimensional k V] (S : Set (Module.End k V)),
    (∀ f ∈ S, ∀ f' ∈ S, f * f' = f' * f) →
      ∀ (d : ℕ) (W : Submodule k V),
        Module.finrank k ↥W = d →
          W ≠ ⊥ →
            (∀ f ∈ S, ∀ x ∈ W, (f : V → V) x ∈ W) → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ f ∈ S, ∃ (c : k), (f : V → V) v = c • v := by
  intro k _ _ V _ _ _ S hS d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro W hd hW hinv
    by_cases h : ∀ f ∈ S, ∀ x ∈ W, ∃ c : k, f x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨v, hv, hv0, fun f hf => h f hf v hv⟩
    · push Not at h
      obtain ⟨f, hf, x, hx, hfx⟩ := h
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict (hinv f hf) : Module.End k W)
      obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
      have hwe : f (w : V) = μ • (w : V) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : W ⊓ f.eigenspace μ < W := by
        refine lt_of_le_of_ne inf_le_left fun he => ?_
        have hx' : x ∈ W ⊓ f.eigenspace μ := he.symm ▸ hx
        exact hfx μ (Module.End.mem_eigenspace_iff.mp hx'.2)
      have hne : W ⊓ f.eigenspace μ ≠ ⊥ := by
        intro hb
        have hm : (w : V) ∈ W ⊓ f.eigenspace μ :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hwe⟩
        rw [hb] at hm
        exact hw0 ((Submodule.mem_bot k).mp hm)
      have hinv' : ∀ g ∈ S, ∀ y ∈ W ⊓ f.eigenspace μ, g y ∈ W ⊓ f.eigenspace μ := by
        intro g hg y hy
        refine ⟨hinv g hg y hy.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 : f y = μ • y := Module.End.mem_eigenspace_iff.mp hy.2
        have h2 : f (g y) = g (f y) := LinearMap.congr_fun (hS f hf g hg) y
        rw [h2, h1, map_smul]
      obtain ⟨v, hv, hv0, hv'⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hinv'
      exact ⟨v, hv.1, hv0, hv'⟩
end

section

theorem UpperTheory.Reformulated.B.SimultaneousEigenvectorInvariantSubspace.simEig :
    ∀ {K M : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup M]
    [inst_3 : _root_.Module K M] [FiniteDimensional K M] {J : Type} (T : J → Module.End K M),
    (∀ (i j : J), T i * T j = T j * T i) →
      ∀ (d : ℕ) (U : Submodule K M),
        Module.finrank K ↥U = d →
          U ≠ ⊥ →
            (∀ (j : J), ∀ x ∈ U, (T j : M → M) x ∈ U) →
              ∃ v ∈ U, v ≠ (0 : M) ∧ ∀ (j : J), ∃ (c : K), (T j : M → M) v = c • v := by
  intro K M _ _ _ _ _ J T hT d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hU hinv
    by_cases h : ∀ j, ∃ c : K, ∀ x ∈ U, T j x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨v, hv, hv0, fun j => ?_⟩
      obtain ⟨c, hc⟩ := h j
      exact ⟨c, hc v hv⟩
    · rw [not_forall] at h
      obtain ⟨i, hi⟩ := h
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hinv i) : Module.End K U)
      obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
      have hw1 : T i (w : M) = c • (w : M) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : M) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : U ⊓ (T i).eigenspace c < U := by
        refine lt_of_le_of_ne inf_le_left fun heq => hi ⟨c, fun x hx => ?_⟩
        rw [← heq] at hx
        exact Module.End.mem_eigenspace_iff.mp hx.2
      have hne : U ⊓ (T i).eigenspace c ≠ ⊥ := by
        intro h0
        have hm : (w : M) ∈ U ⊓ (T i).eigenspace c :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩
        rw [h0] at hm
        exact hw0 ((Submodule.mem_bot K).mp hm)
      have hst : ∀ j, ∀ x ∈ U ⊓ (T i).eigenspace c, T j x ∈ U ⊓ (T i).eigenspace c := by
        intro j x hx
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h2 : T i x = c • x := Module.End.mem_eigenspace_iff.mp hx.2
        have h3 := LinearMap.congr_fun (hT i j) x
        simp only [Module.End.mul_apply] at h3
        rw [h3, h2, map_smul]
      obtain ⟨v, hv, hv0, hvj⟩ :=
        ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hst
      exact ⟨v, hv.1, hv0, hvj⟩
end

section

theorem UpperTheory.Reformulated.B.Qk69.res_algClosed :
    ∀ {Ω : Type} [inst : Field Ω] [IsAlgClosed Ω]
    (A : ValuationSubring Ω), IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  intro Ω _ _ A
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hq, hdeg, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : q.degree ≠ 0 := by
    rw [hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  have hinj : Function.Injective (algebraMap A Ω) := Subtype.val_injective
  have hd' : (q.map (algebraMap A Ω)).degree ≠ 0 := by
    rwa [hm.degree_map]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd'
  have hx' : Polynomial.eval₂ (algebraMap A Ω) x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral A x := ⟨q, hm, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    apply hinj
    rw [Polynomial.eval₂_at_apply] at hx'
    rw [hx', map_zero]
  refine ⟨IsLocalRing.residue A y, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end
