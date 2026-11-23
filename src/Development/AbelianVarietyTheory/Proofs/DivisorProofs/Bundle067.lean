module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

open Module

namespace GlobalTheory.CommutingHecke

theorem fixed_mem_of_stable {ι : Type} [Finite ι] {H : ι → Type} [∀ c, Monoid (H c)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (E : Submodule ℂ V) (hE : E ≠ ⊥) (hst : ∀ c g, ∀ v ∈ E, e c (a c g v) ∈ E)
    (v : V) (hv : ∀ c, e c v = v) : v ∈ E := by
  classical
  haveI := Fintype.ofFinite ι
  let Y : Finset ι → Submodule ℂ V := fun s =>
    sInf {Y | E ≤ Y ∧ ∀ c ∈ s, ∀ g, ∀ v ∈ Y, a c g v ∈ Y}
  have hEY : ∀ s, E ≤ Y s := fun s => le_sInf fun _ h => h.1
  have hYst : ∀ s, ∀ c ∈ s, ∀ g, ∀ v ∈ Y s, a c g v ∈ Y s := by
    intro s c hc g v hv
    simp only [Y, Submodule.mem_sInf] at hv ⊢
    exact fun p hp => hp.2 c hc g v (hv p hp)
  have hind : ∀ s, v ∈ Y s → v ∈ E := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      have : Y ∅ ≤ E := sInf_le ⟨le_rfl, by simp⟩
      exact this h
    | insert c s hc ih =>
      intro h
      apply ih
      let Z : Submodule ℂ V := ⨅ g, (Y s).comap (e c * a c g)
      have hZ : ∀ w, w ∈ Z ↔ ∀ g, e c (a c g w) ∈ Y s := by
        intro w
        simp [Z, Submodule.mem_iInf]
      have hle : Y (insert c s) ≤ Z := by
        refine sInf_le ⟨fun w hw => (hZ w).2 fun g => hEY s (hst c g w hw), ?_⟩
        intro c' hc' g w hw
        rw [hZ] at hw ⊢
        intro g'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · have := hw (g' * g)
          rwa [map_mul, Module.End.mul_apply] at this
        · have hne : c ≠ c' := fun h => hc (h ▸ hc')
          have h1 : a c g' (a c' g w) = a c' g (a c g' w) :=
            LinearMap.congr_fun (haa c c' hne g' g).eq w
          have h2 : e c (a c' g (a c g' w)) = a c' g (e c (a c g' w)) :=
            LinearMap.congr_fun (hea c c' hne g).eq _
          rw [h1, h2]
          exact hYst s c' hc' g _ (hw g')
      have := (hZ v).1 (hle h) 1
      rwa [map_one, Module.End.one_apply, hv] at this
  apply hind Finset.univ
  rcases hirr (Y Finset.univ) (fun c => hYst _ c (Finset.mem_univ c)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ hEY _)) hE
  · rw [h]; trivial

theorem finrank_fixed_le_one (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hee : ∀ c, e c * e c = e c)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (hec : ∀ c c', c ≠ c' → Commute (e c) (e c'))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hhk : ∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c)
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (W : Submodule ℂ V) (hW : ∀ v ∈ W, ∀ c, e c v = v) : finrank ℂ W ≤ 1 := by
  classical
  let W0 : Submodule ℂ V := ⨅ c, LinearMap.eqLocus (e c) LinearMap.id
  have hW0 : ∀ v, v ∈ W0 ↔ ∀ c, e c v = v := by
    intro v
    simp [W0, Submodule.mem_iInf]
  have hpres : ∀ c g, ∀ v ∈ W0, e c (a c g v) ∈ W0 := by
    intro c g v hv
    rw [hW0] at hv ⊢
    intro c'
    by_cases h : c' = c
    · subst h
      exact LinearMap.congr_fun (hee c') _
    · have h1 : e c' (e c (a c g v)) = e c (e c' (a c g v)) :=
        LinearMap.congr_fun (hec c' c h).eq _
      have h2 : e c' (a c g v) = a c g (e c' v) := LinearMap.congr_fun (hea c' c h g).eq _
      rw [h1, h2, hv]
  have hcomm : ∀ c g c' h, ∀ v ∈ W0,
      e c (a c g (e c' (a c' h v))) = e c' (a c' h (e c (a c g v))) := by
    intro c g c' h v hv
    rw [hW0] at hv
    by_cases hc : c = c'
    · subst hc
      have := LinearMap.congr_fun (hhk c g h) v
      simpa only [Module.End.mul_apply, hv] using this
    · have : Commute (e c * a c g) (e c' * a c' h) :=
        Commute.mul_left ((hec c c' hc).mul_right (hea c c' hc h))
          ((hea c' c (Ne.symm hc) g).symm.mul_right (haa c c' hc g h))
      exact LinearMap.congr_fun this.eq v
  have hWle : W ≤ W0 := fun v hv => (hW0 v).2 (hW v hv)
  refine le_trans (Submodule.finrank_mono hWle) ?_
  by_cases hbot : W0 = ⊥
  · rw [hbot]; simp
  haveI : Nontrivial W0 := Submodule.nontrivial_iff_ne_bot.2 hbot
  have hscal : ∀ c g, ∃ μ : ℂ, ∀ v ∈ W0, e c (a c g v) = μ • v := by
    intro c g
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue
      ((e c * a c g).restrict (p := W0) (q := W0) (hpres c g))
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : e c (a c g w) = μ • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨μ, fun v hv => ?_⟩
    have := fixed_mem_of_stable a e hea haa hirr (W0 ⊓ Module.End.eigenspace (e c * a c g) μ)
      ?_ ?_ v ((hW0 v).1 hv)
    · exact Module.End.mem_eigenspace_iff.1 this.2
    · rw [Submodule.ne_bot_iff]
      exact ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, fun h => hw.2 (Subtype.ext h)⟩
    · intro c' h u hu
      refine ⟨hpres c' h u hu.1, Module.End.mem_eigenspace_iff.2 ?_⟩
      have hu2 : e c (a c g u) = μ • u := Module.End.mem_eigenspace_iff.1 hu.2
      rw [Module.End.mul_apply, hcomm c g c' h u hu.1, hu2, map_smul, map_smul]
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hbot
  have hle : W0 ≤ ℂ ∙ w := by
    intro v hv
    refine fixed_mem_of_stable a e hea haa hirr (ℂ ∙ w) (by simpa using hw0) ?_ v ((hW0 v).1 hv)
    intro c g u hu
    obtain ⟨μ, hμ⟩ := hscal c g
    rw [hμ u ((Submodule.span_singleton_le_iff_mem _ _).2 hw hu)]
    exact Submodule.smul_mem _ _ hu
  exact le_trans (Submodule.finrank_mono hle) (finrank_span_singleton hw0).le

end GlobalTheory.CommutingHecke
end

section

namespace GlobalTheory

theorem iSupIndep_of_joint_eigen {E I : Type} [AddCommGroup E] [Module ℂ E]
    (h : I → Module.End ℂ E) (V : (I → ℂ) → Submodule ℂ E)
    (hV : ∀ x, ∀ v ∈ V x, ∀ i, h i v = x i • v) : iSupIndep V := by
  classical
  have stab : ∀ (s : Finset (I → ℂ)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y := by
    intro s i
    have : (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i) := by
      refine iSup₂_le fun y hy v hv => ?_
      rw [Submodule.mem_comap, hV y v hv i]
      exact Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)
    exact fun u hu => this hu
  have key : ∀ (x : I → ℂ) (s : Finset (I → ℂ)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0 := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _ v _ hv; simpa using hv
    | insert y s hy ih =>
      intro hx v hvx hv
      rw [Finset.mem_insert, not_or] at hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hv
      obtain ⟨w, hw, u, hu, hsum⟩ := hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx.1
      have e : (x i - y i) • v = h i u - y i • u := by
        rw [sub_smul, ← hV x v hvx i, ← hsum, map_add (f := _), hV y w hw i, smul_add]; abel
      have h0 := ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx)
        (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)
  intro x
  rw [Submodule.disjoint_def]
  intro v hvx hv
  replace hv : v ∈ ⨆ y : {y : I → ℂ // y ≠ x}, V y.1 := by rwa [iSup_subtype]
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
  refine key x (s.image Subtype.val) ?_ v hvx ?_
  · intro hx
    obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.mem_image.mp hx
    exact hy e
  · refine (iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs
    exact le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1
      (Finset.mem_image_of_mem _ hy) le_rfl

theorem finrank_iSup_eq_of_iSupIndep {E W X : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (V : X → Submodule ℂ E) (V' : X → Submodule ℂ W) (hV : iSupIndep V) (hV' : iSupIndep V')
    (hd : ∀ x, Module.finrank ℂ (V x) = Module.finrank ℂ (V' x)) :
    Module.finrank ℂ (⨆ x, V x : Submodule ℂ E) = Module.finrank ℂ (⨆ x, V' x : Submodule ℂ W) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, Submodule.iSup_eq_range_dfinsupp_lsum]
  have e : ∀ x, V x ≃ₗ[ℂ] V' x := fun x => LinearEquiv.ofFinrankEq _ _ (hd x)
  exact (((LinearEquiv.ofInjective _ hV.dfinsupp_lsum_injective).symm.trans
    (DFinsupp.mapRange.linearEquiv e)).trans
      (LinearEquiv.ofInjective _ hV'.dfinsupp_lsum_injective)).finrank_eq

theorem finrank_iSup_joint_eigen_eq : ∀ {E W I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (h : I → Module.End ℂ E) (h' : I → Module.End ℂ W) (U : C → Submodule ℂ E) (U' : C → Submodule ℂ W) (lab : C → I → ℂ), (∀ c, ∀ x ∈ U c, ∀ i, h i x = lab c i • x) → (∀ c, ∀ x ∈ U' c, ∀ i, h' i x = lab c i • x) → (∀ c c', lab c = lab c' → U c = U c' ∧ U' c = U' c') → (∀ c, Module.finrank ℂ (U c) = Module.finrank ℂ (U' c)) → ∀ S : C → Prop, Module.finrank ℂ (⨆ (c : C) (_ : S c), U c : Submodule ℂ E) = Module.finrank ℂ (⨆ (c : C) (_ : S c), U' c : Submodule ℂ W) := by
  intro E W I C _ _ _ _ _ _ h h' U U' lab hU hU' hlab hd S
  have re : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (⨆ (c : C) (_ : S c), A c) = ⨆ (x : I → ℂ), ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ A
    apply le_antisymm
    · refine iSup₂_le fun c hc => le_iSup_of_le (lab c) ?_
      exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
    · exact iSup_le fun x => iSup₂_le fun c hc =>
        le_iSup₂_of_le (f := fun c' (_ : S c') => A c') c hc.1 le_rfl
  have one : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (∀ c c', lab c = lab c' → A c = A c') → ∀ c, S c →
      (⨆ (c' : C) (_ : S c' ∧ lab c' = lab c), A c') = A c := by
    intro F _ _ A hA c hc
    apply le_antisymm
    · exact iSup₂_le fun c' hc' => (hA c' c hc'.2).le
    · exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
  have none : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F) (x : I → ℂ),
      (¬ ∃ c, S c ∧ lab c = x) → (⨆ (c' : C) (_ : S c' ∧ lab c' = x), A c') = ⊥ := by
    intro F _ _ A x hx
    exact le_bot_iff.mp (iSup₂_le fun c hc => (hx ⟨c, hc⟩).elim)
  have ind : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (g : I → Module.End ℂ F)
      (A : C → Submodule ℂ F), (∀ c c', lab c = lab c' → A c = A c') →
      (∀ c, ∀ x ∈ A c, ∀ i, g i x = lab c i • x) →
      iSupIndep fun x : I → ℂ => ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ g A hA hg
    refine iSupIndep_of_joint_eigen g _ fun x v hv i => ?_
    by_cases hx : ∃ c, S c ∧ lab c = x
    · obtain ⟨c, hc, rfl⟩ := hx
      rw [one A hA c hc] at hv
      exact hg c v hv i
    · rw [none A x hx, Submodule.mem_bot] at hv
      simp [hv]
  rw [re U, re U']
  refine finrank_iSup_eq_of_iSupIndep _ _ (ind h U (fun c c' e => (hlab c c' e).1) hU)
    (ind h' U' (fun c c' e => (hlab c c' e).2) hU') fun x => ?_
  by_cases hx : ∃ c, S c ∧ lab c = x
  · obtain ⟨c, hc, rfl⟩ := hx
    rw [one U (fun c c' e => (hlab c c' e).1) c hc, one U' (fun c c' e => (hlab c c' e).2) c hc]
    exact hd c
  · rw [none U x hx, none U' x hx]
    simp

end GlobalTheory
end

section

open scoped ComplexOrder

namespace GlobalTheory

theorem isotropic_unipotent_column_relations : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  intro n r J X hX l d h u A X₁ Xb X₂ h1 hb hperp
  classical

  have hext : ∀ (m : ℕ) (hm : m ≤ r) (a : Fin m → ℂ),
      Matrix.mulVec X (fun i : Fin r => if hi : i.val < m then a ⟨i.val, hi⟩ else 0) =
        Matrix.mulVec (X.submatrix id fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) a := by
    intro m hm a
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
    symm
    refine Fintype.sum_of_injective (fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) ?_ _ _ ?_ ?_
    · intro x y hxy
      exact Fin.ext (by simpa using congrArg Fin.val hxy)
    · intro i hi
      have : ¬ i.val < m := by
        intro hlt
        exact hi ⟨⟨i.val, hlt⟩, rfl⟩
      simp [this]
    · intro j
      simp
  have he1 : ∀ a : Fin l → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₁ a := fun a => hext l (by omega) a
  have he2 : ∀ a : Fin (l + d) → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l + d then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₂ a := fun a => hext (l + d) h a
  have hcol : ∀ (v : Fin n → ℂ) (i : Fin (l + d)),
      Matrix.mulVec (X₂.conjTranspose * J) v i =
        Matrix.mulVec (X.conjTranspose * J) v ⟨i.val, by omega⟩ := by
    intro v i
    rfl
  have hXc : ∀ (i j : Fin r), Matrix.mulVec (X.conjTranspose * J) (fun k => X k j) i = 0 := by
    intro i j
    exact congrFun (congrFun hX i) j
  have key : ∀ j : Fin r, ∃ c : Fin r → ℂ,
      (∀ i, c i ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
      Matrix.mulVec u (fun k => X k j) = (fun k => X k j) + Matrix.mulVec X c := by
    intro j
    by_cases hj1 : j.val < l
    · refine ⟨0, fun i hi => absurd rfl hi, ?_⟩
      funext k
      have := congrFun (congrFun h1 k) ⟨j.val, hj1⟩
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, X₁] using this
    by_cases hj2 : j.val < l + d
    · refine ⟨fun i => if hi : i.val < l then A ⟨i.val, hi⟩ ⟨j.val - l, by omega⟩ else 0, ?_, ?_⟩
      · intro i hi
        left
        by_cases hil : i.val < l
        · exact ⟨hil, by omega⟩
        · exact absurd (by simp [hil]) hi
      · have he1' := he1 (fun i => A i ⟨j.val - l, by omega⟩)
        beta_reduce at he1'
        rw [he1']
        funext k
        have := congrFun (congrFun hb k) ⟨j.val - l, by omega⟩
        have hjj : (⟨l + (j.val - l), by omega⟩ : Fin r) = j := Fin.ext (by simp; omega)
        simp only [Matrix.mul_apply, Matrix.add_apply, Xb, X₁, Matrix.submatrix_apply, id, hjj] at this
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, X₁] using this
    · have hz : Matrix.mulVec (X₂.conjTranspose * J) (fun k => X k j) = 0 := by
        funext i
        rw [hcol]
        exact hXc _ _
      obtain ⟨w, a, hwa⟩ := hperp _ hz
      refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
          (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
      · intro i hi
        right
        refine ⟨?_, by omega⟩
        by_contra hc
        have hc' : ¬ i.val < l := by omega
        exact hi (by simp [hc, hc'])
      · rw [Matrix.mulVec_add, he1, he2, ← hwa]
        abel
  choose c hc hc' using key
  refine ⟨Matrix.of fun i j => c j i, ?_, ?_, ?_⟩
  · ext k j
    have := congrFun (hc' j) k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · intro i j hij
    exact hc j i (by simpa using hij)
  · intro v hv
    have hz : Matrix.mulVec (X₂.conjTranspose * J) v = 0 := by
      funext i
      rw [hcol]
      exact hv _ (by simp)
    obtain ⟨w, a, hwa⟩ := hperp v hz
    refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
        (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
    · intro i hi
      by_contra hc
      have hc' : ¬ i.val < l := by omega
      exact hi (by simp [hc, hc'])
    · rw [hwa, Matrix.mulVec_add, he1, he2]

end GlobalTheory
end

section

open scoped ComplexOrder
open Matrix

namespace GlobalTheory


open scoped ComplexOrder in
open Matrix in
theorem _root_.GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj :
    ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  intro n d J P X Y y₀ hJ hP hXX hYY hXY hPX hPY k hk m G
  have hki : (k⁻¹).1 = k.1ᴴ := by
    calc (k⁻¹).1 = (k.1ᴴ * k.1) * (k⁻¹).1 := by rw [hk, Matrix.one_mul]
      _ = k.1ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hm : m.1 = y₀.1 * k.1 * (y₀⁻¹).1 := by simp [m]
  have hmi : (m⁻¹).1 = y₀.1 * k.1ᴴ * (y₀⁻¹).1 := by
    simp only [m, _root_.mul_inv_rev, inv_inv, Units.val_mul, hki, Matrix.mul_assoc]
  have hab : y₀.1ᴴ * (y₀⁻¹).1ᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have hAm : m.1ᴴ * ((y₀⁻¹).1ᴴ * (y₀⁻¹).1) * m.1 = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [hm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y₀.1ᴴ, hab, Matrix.one_mul, ← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hBm : (m⁻¹).1 * (y₀.1 * y₀.1ᴴ) * (m⁻¹).1ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [hmi]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc y₀.1ᴴ, hab,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hAh : ((y₀⁻¹).1ᴴ * (y₀⁻¹).1)ᴴ = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hBh : (y₀.1 * y₀.1ᴴ)ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [G]
  generalize (y₀⁻¹).1ᴴ * (y₀⁻¹).1 = A at hPX hAm hAh
  generalize y₀.1 * y₀.1ᴴ = B at hPY hBm hBh
  generalize m.1 = m₁ at hAm
  generalize (m⁻¹).1 = m₂ at hBm
  have hYX : Yᴴ * J * X = 1 := by
    have h := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using h
  have hXP : Xᴴ * P = A * (Yᴴ * J) := by
    have h := congrArg conjTranspose hPX
    simpa [conjTranspose_mul, hJ, hP, hAh, Matrix.mul_assoc] using h
  have hYP : Yᴴ * P = B * (Xᴴ * J) := by
    have h := congrArg conjTranspose hPY
    simpa [conjTranspose_mul, hJ, hP, hBh, Matrix.mul_assoc] using h
  have r1 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (X * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have r2 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (Y * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have r3 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (Y * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have r4 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (X * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have r5 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (X * Z) = J * (Y * (A * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPX]
  have r6 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (Y * Z) = J * (X * (B * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPY]
  have r7 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Xᴴ * (P * Z) = A * (Yᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hXP]
  have r8 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Yᴴ * (P * Z) = B * (Xᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hYP]
  have r9 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₁ᴴ * (A * (m₁ * Z)) = A * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hAm]
  have r10 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₂ * (B * (m₂ᴴ * Z)) = B * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hBm]
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_conjTranspose, hJ, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hXP, hYP,
    Matrix.mul_zero, Matrix.zero_mul, sub_zero, add_zero, zero_add]
  abel

end GlobalTheory
end
