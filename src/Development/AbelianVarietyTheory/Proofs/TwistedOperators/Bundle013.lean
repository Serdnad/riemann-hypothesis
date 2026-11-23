module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory

open Submodule

theorem exists_finiteDimensional_orbit_of_generated :
    ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  intro V ι K _ _ U G P D m L T a hG hDL hGP hDP hmin hTG ha hTD f hf
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → Submodule ℂ V, Q 0 = span ℂ G ∧
      ∀ n, Q (n + 1) = Q n ⊔ span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) :=
    ⟨fun n => Nat.rec (span ℂ G) (fun _ R => R ⊔ span ℂ (⋃ u ∈ U, (D u) '' (R : Set V))) n,
      rfl, fun _ => rfl⟩
  have hmono : Monotone Q := monotone_nat_of_le_succ fun n => by
    rw [hQs]; exact le_sup_left
  have hDQ : ∀ n, ∀ u ∈ U, ∀ x ∈ Q n, D u x ∈ Q (n + 1) := by
    intro n u hu x hx
    rw [hQs]
    exact mem_sup_right (subset_span (Set.mem_iUnion₂.2 ⟨u, hu, x, hx, rfl⟩))
  have hfin : ∀ n : ℕ, FiniteDimensional ℂ (Q n) := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact hG
    | succ n ih =>
      rw [hQs]
      have hle : span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) ≤ ⨆ i, (Q n).map (L i) := by
        refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
        rintro _ ⟨x, hx, rfl⟩
        refine (span_le.2 ?_) (hDL u hu x)
        rintro _ ⟨i, rfl⟩
        exact mem_iSup_of_mem i (mem_map_of_mem hx)
      haveI : FiniteDimensional ℂ (span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V))) :=
        Submodule.finiteDimensional_of_le hle
      exact Submodule.finiteDimensional_sup _ _
  have hQP : ∀ n, Q n ≤ P := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact span_le.2 hGP
    | succ n ih =>
      rw [hQs]
      refine sup_le ih (span_le.2 (Set.iUnion₂_subset fun u hu => ?_))
      rintro _ ⟨y, hy, rfl⟩
      exact hDP u hu y (ih hy)
  have hT : ∀ n k, Q n ≤ (Q n).comap (T k) := by
    intro n k
    induction n with
    | zero => rw [hQ0]; exact span_le.2 fun g hg => hTG k g hg
    | succ n ih =>
      rw [hQs]
      refine sup_le (ih.trans (comap_mono le_sup_left)) ?_
      refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
      rintro _ ⟨x, hx, rfl⟩
      have hxP : x ∈ P := hQP n hx
      rw [SetLike.mem_coe, mem_comap, ← hQs, hTD k u hu x hxP]
      exact hDQ n (a k u) (ha k u hu) (T k x) (ih hx)
  have hGN : G ⊆ (⨆ n, Q n : Submodule ℂ V) := fun g hg =>
    mem_iSup_of_mem 0 (hQ0 ▸ subset_span hg)
  have hDN : ∀ u ∈ U, ∀ x ∈ (⨆ n, Q n : Submodule ℂ V), D u x ∈ (⨆ n, Q n : Submodule ℂ V) := by
    intro u hu x hx
    obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 hx
    exact mem_iSup_of_mem (n + 1) (hDQ n u hu x hn)
  obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 (hmin _ hGN hDN hf)
  exact ⟨Q n, hfin n, fun k => hT n k hn⟩

end GlobalTheory
end

section

namespace GlobalTheory.FinsetKernelTrivial

open scoped BigOperators

noncomputable def restr {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X) :
    W →ₗ[ℂ] (P → ℂ) :=
  LinearMap.pi (fun x : P => (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x.1).comp (V.subtype.comp W.subtype))

lemma restr_apply {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X)
    (w : W) (x : P) : restr V W P w x = ((w : V) : X → ℂ) x := rfl

lemma exists_finset_ker_eq_bot {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] : ∃ P : Finset X, LinearMap.ker (restr V W P) = ⊥ := by
  classical
  have hex : ∃ n, ∃ P : Finset X, Module.finrank ℂ (LinearMap.ker (restr V W P)) = n :=
    ⟨_, ∅, rfl⟩
  obtain ⟨P, hP⟩ := Nat.find_spec hex
  refine ⟨P, ?_⟩
  by_contra hne
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hf : ((w : V) : X → ℂ) ≠ 0 := by
    intro h
    apply hw0
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have hle : LinearMap.ker (restr V W (insert x P)) < LinearMap.ker (restr V W P) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      funext y
      have := congrFun hv ⟨y.1, Finset.mem_insert_of_mem y.2⟩
      simpa [restr_apply] using this
    · intro heq
      have : w ∈ LinearMap.ker (restr V W (insert x P)) := heq ▸ hwK
      rw [LinearMap.mem_ker] at this
      have := congrFun this ⟨x, Finset.mem_insert_self x P⟩
      exact hx (by simpa [restr_apply] using this)
  have hlt := Submodule.finrank_lt_finrank_of_lt hle
  have hmin := Nat.find_min hex (hP ▸ hlt)
  exact hmin ⟨insert x P, rfl⟩

theorem main : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ ↥V) [FiniteDimensional ℂ ↥W],
    ∃ (P : Finset X) (e : X → ↥V), ∀ w ∈ W, w = ∑ x ∈ P, (↑w : X → ℂ) x • e x := by
  intro X V W _
  classical
  obtain ⟨P, hP⟩ := exists_finset_ker_eq_bot V W
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (restr V W P) hP
  refine ⟨P, fun x => if h : x ∈ P then ((L (Pi.single ⟨x, h⟩ 1) : W) : V) else 0, ?_⟩
  intro w hw
  have h1 : (⟨w, hw⟩ : W) = L (restr V W P ⟨w, hw⟩) := by
    have := congrArg (fun g => g ⟨w, hw⟩) hL
    simpa using this.symm
  have h2 : restr V W P ⟨w, hw⟩ = ∑ x : P, ((w : X → ℂ) x.1) • (Pi.single x (1 : ℂ)) := by
    funext y
    simp [restr_apply, Finset.sum_apply, Pi.single_apply]
  have h3 : w = ∑ x : P, ((w : X → ℂ) x.1) • ((L (Pi.single x 1) : W) : V) := by
    have := congrArg (fun u : W => (u : V)) h1
    simp only at this

    conv_lhs => rw [this, h2, map_sum]
    simp [map_smul]
  conv_lhs => rw [h3]
  rw [← Finset.sum_attach P]
  refine Finset.sum_congr rfl ?_
  intro x _
  simp [x.2]

end GlobalTheory.FinsetKernelTrivial
end

section

namespace GlobalTheory.Chain.RealIt

open MvPolynomial

theorem totalDegree_mulLeft_add {σ : Type} (Q : MvPolynomial σ ℂ)
    (L : Module.End ℂ (MvPolynomial σ ℂ)) (hQ : Q ≠ 0) (hh : Q.IsHomogeneous 2)
    (hL : ∀ P, (L P).totalDegree ≤ P.totalDegree) (φ : MvPolynomial σ ℂ) (hφ : φ ≠ 0) :
    ((LinearMap.mulLeft ℂ Q + L) φ).totalDegree = φ.totalDegree + 2 := by
  have h1 : (Q * φ).totalDegree = φ.totalDegree + 2 := by
    rw [totalDegree_mul_of_isDomain hQ hφ, hh.totalDegree hQ, add_comm]
  have h2 : (L φ).totalDegree < (Q * φ).totalDegree := by
    have := hL φ
    omega
  rw [LinearMap.add_apply, LinearMap.mulLeft_apply, totalDegree_add_eq_left_of_totalDegree_lt h2, h1]

theorem exists_totalDegree_le_of_finiteDimensional {σ : Type} (F : Submodule ℂ (MvPolynomial σ ℂ))
    (hF : FiniteDimensional ℂ F) : ∃ N : ℕ, ∀ P ∈ F, P.totalDegree ≤ N := by
  obtain ⟨s, hs⟩ : F.FG := (Submodule.fg_iff_finiteDimensional F).2 hF
  refine ⟨s.sup totalDegree, fun P hP => ?_⟩
  have hle : F ≤ restrictTotalDegree σ ℂ (s.sup totalDegree) := by
    rw [← hs, Submodule.span_le]
    intro x hx
    exact (mem_restrictTotalDegree σ _ x).2 (Finset.le_sup (f := totalDegree) hx)
  exact (mem_restrictTotalDegree σ _ P).1 (hle hP)

theorem not_locallyFinite_mulLeft_add :
    ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)),
      Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) →
      ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ),
        FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by
  intro σ _ Q L hQ hh hL φ hφ F hF hall
  obtain ⟨N, hN⟩ := exists_totalDegree_le_of_finiteDimensional F hF
  have key : ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ≠ 0 ∧
      (((LinearMap.mulLeft ℂ Q + L) ^ n) φ).totalDegree = φ.totalDegree + 2 * n := by
    intro n
    induction n with
    | zero => simpa using hφ
    | succ n ih =>
      have h := totalDegree_mulLeft_add Q L hQ hh hL _ ih.1
      rw [pow_succ', Module.End.mul_apply]
      refine ⟨fun h0 => ?_, by rw [h, ih.2]; ring⟩
      rw [h0, totalDegree_zero] at h
      omega
  have h1 := hN _ (hall (N + 1))
  rw [(key (N + 1)).2] at h1
  omega

end GlobalTheory.Chain.RealIt
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead

def Stab {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (N : Submodule ℂ V) : Prop :=
  ∀ g ∈ G, ∀ x ∈ N, g x ∈ N

def SimpleOver {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Prop :=
  ∀ N : Submodule ℂ V, Stab G N → K ≤ N → N = K ∨ N = ⊤

def piOp {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (⨂[ℂ] j, M j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)

def piOps {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) :
    Set (Module.End ℂ (⨂[ℂ] j, M j)) :=
  {f | ∃ i, ∃ g ∈ Op i, f = piOp i g}

def tensOps {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) : Set (Module.End ℂ (V₀ ⊗[ℂ] V₁)) :=
  {f | ∃ g ∈ A, f = TensorProduct.map g LinearMap.id} ∪
    {f | ∃ h ∈ B, f = TensorProduct.map LinearMap.id h}

def piKer {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (K : ∀ i, Submodule ℂ (M i)) : Submodule ℂ (⨂[ℂ] j, M j) :=
  Submodule.span ℂ {t | ∃ y : ∀ i, M i, (∃ i, y i ∈ K i) ∧ t = PiTensorProduct.tprod ℂ y}

def tensKer {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) : Submodule ℂ (V₀ ⊗[ℂ] V₁) :=
  Submodule.span ℂ {t | ∃ (x : V₀) (y : V₁), (x ∈ K₀ ∨ y ∈ K₁) ∧ t = x ⊗ₜ[ℂ] y}

end GlobalTheory.TensHead
end

section

namespace GlobalTheory

theorem trace_eq_zero_of_coord_move {X W : Type} [Fintype X] [DecidableEq X] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (π : X → X) (hπ : ∀ c, π c ≠ c)
    (φ : X → Module.End ℂ W) (M : Module.End ℂ (X → W)) (hM : ∀ f c, M f c = φ c (f (π c))) :
    LinearMap.trace ℂ (X → W) M = 0 := by
  classical

  let b := Pi.basis (fun _ : X => Module.finBasis ℂ W)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hM,
    Pi.single_eq_of_ne (hπ i.1), map_zero, map_zero, Finsupp.zero_apply]

theorem finrank_eq_card_mul_and_trace_eq_zero_of_free_values :
    ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  intro Y X B W _ _ _ _ _ _ cls ev S hcls hinj hcls_eq hfree
  classical
  haveI : Fintype X := Fintype.ofFinite X

  obtain ⟨s, hs⟩ : ∃ s : X → Y, ∀ x, cls (s x) = x :=
    ⟨fun x => (hcls x).choose, fun x => (hcls x).choose_spec⟩

  let Φ : S →ₗ[ℂ] (X → W) := LinearMap.pi (fun x => (ev (s x)).comp S.subtype)
  have hΦ : ∀ (T : S) x, Φ T x = ev (s x) T := fun _ _ => rfl
  have hzero : ∀ T ∈ S, (∀ x, ev (s x) T = 0) → T = 0 := by
    intro T hT h0
    apply hinj
    intro h
    obtain ⟨φ, hφ⟩ := hcls_eq (s (cls h)) h (hs _)
    rw [hφ T hT, h0, map_zero]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    refine Subtype.ext (hzero T T.2 (fun x => ?_))
    have hx := congrFun hT x
    rw [hΦ] at hx
    exact hx
  have hΦsurj : Function.Surjective Φ := by
    intro g
    choose T hTS hTg hT0 using fun x => hfree (s x) (g x)
    refine ⟨⟨∑ x, T x, Submodule.sum_mem _ (fun x _ => hTS x)⟩, ?_⟩
    funext y
    show ev (s y) (∑ x, T x) = g y

    rw [map_sum, Finset.sum_eq_single y]
    · exact hTg y
    · intro x _ hxy
      apply hT0
      rw [hs, hs]
      exact Ne.symm hxy
    · intro h
      exact absurd (Finset.mem_univ y) h
  let Ψ : S ≃ₗ[ℂ] (X → W) := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hfd : FiniteDimensional ℂ S := LinearEquiv.finiteDimensional Ψ.symm
  refine ⟨hfd, ?_, ?_⟩
  · rw [Ψ.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  · intro H _ _ e he hrange A t hA ht

    let eS : H ≃ₗ[ℂ] S := (LinearEquiv.ofInjective e he).trans (LinearEquiv.ofEq _ _ hrange)
    let Θ : H ≃ₗ[ℂ] (X → W) := eS.trans Ψ
    have hΘ : ∀ x c, Θ x c = ev (s c) (e x) := fun _ _ => rfl
    haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional Θ.symm
    rw [← LinearMap.trace_conj' A Θ]
    choose φ hφ using fun c => hcls_eq (s (cls (t (s c)))) (t (s c)) (hs _)
    refine trace_eq_zero_of_coord_move (fun c => cls (t (s c)))
      (fun c => by have h := ht (s c); rwa [hs] at h) φ _ ?_
    intro g c
    obtain ⟨x, rfl⟩ := Θ.surjective g
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, hA]
    have hmem : e x ∈ S := by
      rw [← hrange]
      exact LinearMap.mem_range_self e x
    exact hφ c (e x) hmem

end GlobalTheory
end

section

namespace GlobalTheory

theorem hermite_reduction_column {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R → R) (hb : ∀ i j, j < i → b i j = 0) (hr : ∀ i y, b i i ∣ y - r i y)
    (j : Fin n) (m : ℕ) :
    ∃ x : Fin n → R, x j = 1 ∧ (∀ l, j < l → x l = 0) ∧
      ∀ i : Fin n, i < j → (j : ℕ) ≤ i + m → ∃ y, b.mulVec x i = r i y := by
  induction m with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [hl.ne'], fun i hi hj => ?_⟩
    exact absurd (Fin.lt_def.1 hi) (by omega)
  | succ m ih =>
    obtain ⟨x, hx1, hx0, hx⟩ := ih
    by_cases h : ∃ k : Fin n, (j : ℕ) = k + m + 1
    · obtain ⟨k, hk⟩ := h
      obtain ⟨z, hz⟩ := hr k (b.mulVec x k)
      have hkj : k < j := Fin.lt_def.2 (by omega)
      have key : ∀ i, b.mulVec (x - Pi.single k z) i = b.mulVec x i - b i k * z := by
        intro i
        rw [Matrix.mulVec_sub, Pi.sub_apply]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      refine ⟨x - Pi.single k z, ?_, fun l hl => ?_, fun i hi hj => ?_⟩
      · simp [hx1, hkj.ne']
      · simp [hx0 l hl, (hkj.trans hl).ne']
      · rw [key]
        by_cases hik : i = k
        · subst hik
          exact ⟨b.mulVec x i, by rw [← hz]; ring⟩
        · have hne : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
          have hki : k < i := Fin.lt_def.2 (by omega)
          rw [hb i k hki, zero_mul, sub_zero]
          exact hx i hi (by omega)
    · refine ⟨x, hx1, hx0, fun i hi hj => hx i hi ?_⟩
      by_contra hc
      exact h ⟨i, by omega⟩

theorem hermite_reduction_unipotent :
    ∀ (R : Type) [CommRing R] (n : ℕ) (b : Matrix (Fin n) (Fin n) R) (r : Fin n → R → R),
      (∀ i j, j < i → b i j = 0) → (∀ i y, b i i ∣ y - r i y) →
      ∃ u : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        ∀ i j, i < j → ∃ y, (b * u) i j = r i y := by
  intro R _ n b r hb hr
  choose x hx1 hx0 hx using fun j : Fin n => hermite_reduction_column b r hb hr j n
  refine ⟨Matrix.of fun i j => x j i, fun i j h => hx0 j i h, fun i => hx1 i, fun i j h => ?_⟩
  obtain ⟨y, hy⟩ := hx j i h (by have := j.2; omega)
  exact ⟨y, by rw [← hy]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]⟩

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem eichlerTransvection_unitary_inverse_conj :
    ∀ (A : Type) [CommRing A] [StarRing A] [Invertible (2 : A)] (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι A) (_ : Gᴴ = G) (h : (ι → A) → (ι → A) → A) (_ : ∀ x y, h x y = star y ⬝ᵥ G.mulVec x) (E : (ι → A) → (ι → A) → (ι → A) → (ι → A)) (_ : ∀ w v y, E w v y = y + h y v • w - h y w • v - (⅟(2 : A) * h v v * h y w) • w), (∀ w v, h w w = 0 → h w v = 0 → ∀ x y, h (E w v x) (E w v y) = h x y) ∧ (∀ w v, h w w = 0 → h w v = 0 → ∀ y, E w (-v) (E w v y) = y) ∧ ∀ (g : Matrix ι ι A), (∀ x y, h (g.mulVec x) (g.mulVec y) = h x y) → ∀ w v y, g.mulVec (E w v y) = E (g.mulVec w) (g.mulVec v) (g.mulVec y) := by
  intro A _ _ _ ι _ _ G hG h hh E hE
  have addl : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y; simp only [hh, mulVec_add, dotProduct_add]
  have subl : ∀ x x' y, h (x - x') y = h x y - h x' y := by
    intro x x' y; simp only [hh, mulVec_sub, dotProduct_sub]
  have negl : ∀ x y, h (-x) y = - h x y := by
    intro x y; simp only [hh, mulVec_neg, dotProduct_neg]
  have smull : ∀ (a : A) x y, h (a • x) y = a * h x y := by
    intro a x y; simp only [hh, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have addr : ∀ x y y', h x (y + y') = h x y + h x y' := by
    intro x y y'; simp only [hh, star_add, add_dotProduct]
  have subr : ∀ x y y', h x (y - y') = h x y - h x y' := by
    intro x y y'; simp only [hh, star_sub, sub_dotProduct]
  have negr : ∀ x y, h x (-y) = - h x y := by
    intro x y; simp only [hh, star_neg, neg_dotProduct]
  have smulr : ∀ (a : A) x y, h x (a • y) = star a * h x y := by
    intro a x y; simp only [hh, star_smul, smul_dotProduct, smul_eq_mul]
  have symm : ∀ x y, star (h x y) = h y x := by
    intro x y
    rw [hh, hh, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self _
  have s2 : star (⅟(2 : A)) = ⅟(2 : A) := by
    have := congrArg star h2
    rw [star_mul', star_one, star_ofNat] at this
    linear_combination (⅟(2 : A)) * this - (star (⅟(2 : A))) * h2
  refine ⟨?_, ?_, ?_⟩
  · intro w v hww hwv x y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE, hE]
    simp only [addl, subl, smull, addr, subr, smulr, star_mul', symm, s2, hww, hwv, hvw]
    linear_combination (-(h v v * h x w * h w y)) * h2
  · intro w v hww hwv y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE w (-v), hE w v]
    simp only [addl, subl, smull, negl, negr, hww, hwv, hvw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (-(h v v * h y w * w i)) * h2
  · intro g hg w v y
    rw [hE, hE]
    simp only [hg, mulVec_add, mulVec_sub, mulVec_smul]

end GlobalTheory
end
