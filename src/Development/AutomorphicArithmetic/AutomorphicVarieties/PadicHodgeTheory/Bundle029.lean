module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle017
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
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
import Mathlib.NumberTheory.Padics.LocalField
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {E : Type} [Field E] [Algebra ℚ_[l] E]
  {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]

private noncomputable def spanT (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E]
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    (W : Submodule E V) : Submodule E (V ⊗[ℚ_[l]] Bdr l) :=
  Submodule.span E {y | ∃ v ∈ W, ∃ b ∈ ((PP l).PD (botExt l)).Fil 0, y = v ⊗ₜ[ℚ_[l]] b}

private theorem filT_le_spanT : FilT (l := l) E V 0 ≤ spanT l (⊤ : Submodule E V) := by
  rintro _ ⟨z, rfl⟩
  induction z with
  | tmul v b => exact Submodule.subset_span ⟨v, trivial, b.1, b.2, by simp⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

private theorem spanT_le_filT (W : Submodule E V) : spanT l W ≤ FilT (l := l) E V 0 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, -, b, hb, rfl⟩
  exact ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

private theorem spanT_bot : spanT l (⊥ : Submodule E V) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨v, hv, b, -, rfl⟩
  rw [Submodule.mem_bot] at hv
  simp [hv]

private theorem map_spanT {V' : Type} [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] E V'] (f : V →ₗ[E] V') (W : Submodule E V) (W' : Submodule E V')
    (hf : ∀ v ∈ W, f v ∈ W') (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W) :
    AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) y ∈ spanT l W' := by
  have : spanT l W ≤ (spanT l W').comap
      (AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, b, hb, rfl⟩
    exact Submodule.subset_span ⟨f v, hf v hv, b, hb, by simp⟩
  exact this hy

private theorem step (φ : G →* GQ l) (ρ : Representation E G V) (κ : G →* Eˣ)
    (hκ : FilD φ (chRep κ) 0 = ⊥) (W W' : Submodule E V) (x : V) (lam : V →ₗ[E] E)
    (hp : ∀ v ∈ W', v - lam v • x ∈ W)
    (heq : ∀ g, ∀ v ∈ W', lam (ρ g v) = (κ g : E) * lam v)
    (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W') (hD : y ∈ Ddr φ ρ) : y ∈ spanT l W := by
  set L := AlgebraTensorModule.map lam (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) with hL
  have hcomm : ∀ g, ∀ z ∈ spanT l W', L (actD φ ρ g z) = actD φ (chRep κ) g (L z) := by
    intro g z hz
    have : spanT l W' ≤ LinearMap.eqLocus (L ∘ₗ actD φ ρ g) (actD φ (chRep κ) g ∘ₗ L) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, b, hb, rfl⟩
      simp [LinearMap.mem_eqLocus, hL, actD, chRep, heq g v hv]
    exact this hz
  have h0 : L y = 0 := by
    have : L y ∈ FilD φ (chRep κ) 0 := by
      refine ⟨?_, spanT_le_filT ⊤ (map_spanT lam W' ⊤ (fun _ _ => trivial) y hy)⟩
      simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hD ⊢
      intro g
      rw [← hcomm g y hy, hD g]
    rwa [hκ, Submodule.mem_bot] at this
  have h1 := map_spanT (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam) W' W
    (fun v hv => by simpa using hp v hv) y hy
  have h2 : ∀ z : V ⊗[ℚ_[l]] Bdr l,
      AlgebraTensorModule.map (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) z =
      z - AlgebraTensorModule.map (LinearMap.toSpanSingleton E V x)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) (L z) := by
    intro z
    induction z with
    | tmul v b => simp [hL, sub_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
  rwa [h2, h0, map_zero, sub_zero] at h1

private theorem H0_eq_bot_of_filD_zero_eq_bot (φ : G →* GQ l) (ρ : Representation E G V) [TopologicalSpace G]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
    (h : FilD φ ρ 0 = ⊥) : H0 ρ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_riemannRochSpace_iff_regularAt_everywhere] at hv
  haveI : Nontrivial (Bdr l) := nontrivial_of_ne 1 0 fun h1 =>
    ((PP l).PD (botExt l)).not_mem_filtration_two (by
      have : (((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t : Bdr l) = 0 := by
        rw [← mul_one (((PP l).PD (botExt l)).ι _), h1, mul_zero]
      rw [this]; exact zero_mem _)
  have hm : v ⊗ₜ[ℚ_[l]] (1 : Bdr l) ∈ FilD φ ρ 0 := by
    refine ⟨?_, v ⊗ₜ ⟨1, ((PP l).PD (botExt l)).one_mem⟩, by simp⟩
    simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    simp [actD, hv g]
  rw [h, Submodule.mem_bot] at hm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ_[l] (one_ne_zero : (1 : Bdr l) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid ℚ_[l] V (TensorProduct.map LinearMap.id f z)) hm
  simpa [hf] using this

end SlopeTestRemainingChoices

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.posBasic :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0 ρ = ⊥ ∧ FilD φ ρ 0 = ⊥ ∧ Module.Finite E ↥(finiteCohomology φ ρ) ∧ finrank E ↥(finiteCohomology φ ρ) = φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos
  obtain ⟨hdr, n, F, hF0, hFn, hF⟩ := hpos
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have key : ∀ i ≤ n, (∀ g, ∀ v ∈ F i, ρ g v ∈ F i) ∧ ∀ y ∈ spanT l (F i), y ∈ Ddr φ ρ → y = 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hF0, spanT_bot]
      refine ⟨fun g v hv => ?_, fun y hy _ => hy⟩
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ i ih =>
      intro hi
      obtain ⟨hst, hz⟩ := ih (by omega)
      obtain ⟨hle, κ, ⟨w, hw, hκ⟩, x, hsup, hx⟩ := hF i (by omega)
      by_cases hxi : x ∈ F i
      · have : F (i + 1) = F i := by
          rw [hsup, sup_eq_left, Submodule.span_singleton_le_iff_mem]; exact hxi
        rw [this]; exact ⟨hst, hz⟩
      obtain ⟨lam, hl1, hl0⟩ : ∃ lam : V →ₗ[E] E, lam x = 1 ∧ ∀ v ∈ F i, lam v = 0 := by
        have hne : (F i).mkQ x ≠ 0 := by simpa using hxi
        obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one E hne
        refine ⟨f ∘ₗ (F i).mkQ, hf, fun v hv => ?_⟩
        have : (F i).mkQ v = 0 := by simpa using hv
        rw [LinearMap.comp_apply, this, map_zero]
      have hdec : ∀ v ∈ F (i + 1), ∃ u ∈ F i, ∃ c : E, v = u + c • x := by
        intro v hv
        rw [hsup, Submodule.mem_sup] at hv
        obtain ⟨u, hu, z, hz, rfl⟩ := hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        exact ⟨u, hu, c, rfl⟩
      have hx1 : x ∈ F (i + 1) := by
        rw [hsup]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
      have hlx : ∀ g, lam (ρ g x) = (κ g : E) := by
        intro g
        have := hl0 _ (hx g)
        rwa [map_sub, map_smul, hl1, smul_eq_mul, mul_one, sub_eq_zero] at this
      have hcont : Continuous (fun g => (κ g : E)) := by
        have h1 : Continuous (lam.restrictScalars ℚ_[l]) :=
          IsModuleTopology.continuous_of_linearMap _
        have h2 : Continuous (fun g => ρ g x) := hρ.comp (Continuous.prodMk_left x)
        have := h1.comp h2
        convert this using 1
        funext g
        exact (hlx g).symm
      have hfil := ((charFil φ hφ κ hcont w hκ).2 0).2 (by omega)
      refine ⟨fun g v hv => ?_, fun y hy hD => hz y (step φ ρ κ hfil (F i) (F (i + 1)) x lam ?_ ?_ y hy hD) hD⟩
      · obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        rw [map_add (f := _), map_smul]
        refine add_mem (hle (hst g u hu)) (Submodule.smul_mem _ _ ?_)
        have := add_mem (hle (hx g)) (Submodule.smul_mem _ (κ g : E) hx1)
        rwa [sub_add_cancel] at this
      · intro v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simpa [hl0 u hu, hl1] using hu
      · intro g v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simp [hl0 u hu, hl1, hl0 _ (hst g u hu), hlx, mul_comm]
  have hfil : FilD φ ρ 0 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact (key n le_rfl).2 y (hFn ▸ filT_le_spanT hy.2) hy.1
  have hH0 := H0_eq_bot_of_filD_zero_eq_bot φ ρ hfil
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ ρ hρ hdr
  refine ⟨hH0, hfil, hfin, ?_⟩
  rw [hfil, hH0] at hdim
  simpa using hdim
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem sandwich {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B S Z : Submodule E M)
    (hBS : B ≤ S) (hSZ : S ≤ Z) [Module.Finite E B]
    [hQ : Module.Finite E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ)] :
    Module.Finite E S ∧
      finrank E S = finrank E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) + finrank E B := by
  let f : S →ₗ[E] (Z ⧸ B.comap Z.subtype) := (B.comap Z.subtype).mkQ ∘ₗ Submodule.inclusion hSZ
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    simp [f]
  have eB := Submodule.comapSubtypeEquivOfLe hBS
  have hkf : Module.Finite E ↥(LinearMap.ker f) := by
    rw [hk]; exact Module.Finite.equiv eB.symm
  have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
  have hS : Module.Finite E S := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
    · rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf
    · rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf
  refine ⟨hS, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]

private theorem exists_ne_one {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] ℚ_[l] E] (κ : G →* Eˣ) (w : ℤ) (hw : w ≠ 0) (h : HasWeight φ κ w) :
    ∃ g, κ g ≠ 1 := by
  obtain ⟨U, hU, h⟩ := h
  obtain ⟨-, s, ⟨⟨g, hg, rfl⟩, hs⟩, hfin⟩ := (cycInertia l).2 (U.map φ) (hφ.isOpenMap _ hU)
  refine ⟨g, fun h1 => hfin ?_⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have h2 := h g hg hs
  rw [h1] at h2
  have h3 : cyc l l (φ g) ^ w = 1 := by
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
    rw [map_zpow, map_one]
    exact h2.symm
  exact isOfFinOrder_iff_zpow_eq_one.2 ⟨w, hw, h3⟩

private theorem finrank_ddr {l : ℕ} [Fact l.Prime] {G : Type} [Group G]
    (φ : G →* GQ l) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (ρ : Representation E G E) (h : IsDr φ ρ) : finrank E ↥(Ddr φ ρ) = φ.range.index := by
  have he : Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
    ext x
    simp only [Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have h1 : finrank ℚ_[l] ↥(Ddr φ ρ) = φ.range.index * finrank ℚ_[l] E := by
    unfold IsDr at h
    rw [he] at h
    exact h
  rw [← Module.finrank_mul_finrank ℚ_[l] E, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

theorem UpperTheory.V.Loc.z1fChar :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (κ : G →* Eˣ), Continuous (fun g => (κ g : E)) → ∀ w : ℤ, HasWeight φ κ w → (w < 0 → UpperTheory.V.Loc.finiteCocycles φ (chRep κ) = ReciprocityTheory.Gal.B1 (chRep κ) ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1) ∧ (0 < w → Module.Finite E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) ∧ finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) = φ.range.index + 1) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ w hw
  have hc : ReciprocityTheory.Gal.ContAction (chRep κ) := by
    have : (fun p : G × E => chRep κ p.1 p.2) = fun p => (κ p.1 : E) * p.2 := by
      funext p; simp [chRep]
    unfold ReciprocityTheory.Gal.ContAction
    rw [this]
    exact (hκ.comp continuous_fst).mul continuous_snd
  obtain ⟨hdr, hfil⟩ := charFil φ hφ κ hκ w hw
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ (chRep κ) hc hdr
  have hBS := (z1fMap φ (chRep κ) (chRep κ)).1 hc
  have hSZ : UpperTheory.V.Loc.finiteCocycles φ (chRep κ) ≤ ReciprocityTheory.Gal.Z1 (chRep κ) := fun c h => h.1
  have hBf : Module.Finite E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := by
    unfold ReciprocityTheory.Gal.B1; infer_instance
  obtain ⟨hS, hSd⟩ := sandwich _ _ _ hBS hSZ (hQ := hfin)
  replace hSd : finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) =
    finrank E ↥(finiteCohomology φ (chRep κ)) + finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := hSd
  have key : w ≠ 0 → ReciprocityTheory.Gal.H0 (chRep κ) = ⊥ ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1 := by
    intro h0
    obtain ⟨g, hg⟩ := exists_ne_one φ hφ κ w h0 hw
    have hz : ∀ m : E, chRep κ g m - m = 0 → m = 0 := by
      intro m hm
      have h1 : ((κ g : E) - 1) * m = 0 := by
        rw [sub_mul, one_mul]; simpa [chRep] using hm
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h)) hg
      · exact h
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro m hm
      exact hz m (sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm g))
    · unfold ReciprocityTheory.Gal.B1
      rw [LinearMap.finrank_range_of_inj, finrank_self]
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro m hm
      exact hz m (congrFun hm g)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h0, hB⟩ := key h.ne
    rw [h0, (hfil 0).1 (by omega), finrank_ddr φ _ hdr, finrank_bot, finrank_self] at hdim
    refine ⟨(Submodule.eq_of_le_of_finrank_eq hBS (by omega)).symm, hB⟩
  · obtain ⟨h0, hB⟩ := key h.ne'
    rw [h0, (hfil 0).2 (by omega), finrank_bot, finrank_bot, finrank_self] at hdim
    exact ⟨hS, by omega⟩
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private noncomputable def filS {l : ℕ} [Fact l.Prime] (K : FinExt l) : Subring (Bcr l) where
  carrier := {x | ∀ k : ℕ, (PP l).ιB (((PP l).φB ^ k) x) ∈ ((PP l).PD K).Fil 0}
  mul_mem' := fun {a b} ha hb k => by
    rw [map_mul, map_mul]
    simpa using ((PP l).PD K).Fil_mul 0 0 _ _ (ha k) (hb k)
  one_mem' := fun k => by
    rw [map_one, map_one]; exact ((PP l).PD K).one_mem
  add_mem' := fun {a b} ha hb k => by
    rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ (ha k) (hb k)
  zero_mem' := fun k => by
    rw [map_zero, map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha k => by
    rw [map_neg, map_neg]; exact Submodule.neg_mem _ (ha k)

private theorem frobenius_iterate_unramified {l : ℕ} [Fact l.Prime] (K : FinExt l) (k : ℕ) (c : ↥(K0 K)) :
    ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← (PP l).PD_φ K,
      ((PP l).PD K).φ_K₀]

private theorem K0_mem {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(K0 K)) :
    algebraMap ↥(K0 K) (Bcr l) c ∈ filS K := by
  intro k
  rw [AlgHom.coe_pow, frobenius_iterate_unramified, ← (PP l).PD_ι K, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul ↥K.1]
  exact Submodule.smul_mem _ _ ((PP l).PD K).one_mem

private theorem fil_iff {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (x : Bdr l) :
    x ∈ ((PP l).PD K).Fil 0 ↔ x ∈ ((PP l).PD K').Fil 0 := by
  obtain ⟨T⟩ := tiedP l
  rw [T.fil, T.fil]

theorem UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (F : Matrix (Fin d) (Fin d) ↥(K0 K)), M' * M = 1 → (∀ (k : ℕ) i j, (PP l).ιB (((PP l).φB)^[k] (M i j)) ∈ ((PP l).PD (botExt l)).Fil 0) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖a‖ ≤ 1 := by
  intro l _ K f hf hσ d M M' F hM hFil hφ a ha
  obtain ⟨T⟩ := tiedP l
  haveI : IsDomain (Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hdet⟩ := UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum (K0 K) F a ha
  set j : ↥(K0 K) →+* Bcr l := algebraMap ↥(K0 K) (Bcr l) with hj
  let ψ : Bcr l →+* Bcr l := (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
  have hψ : (ψ : Bcr l → Bcr l) = ((PP l).φB)^[f] := AlgHom.coe_pow _ _
  obtain ⟨X, hXd⟩ : ∃ X : Matrix (Fin d) (Fin r) (Bcr l), X = M * Y.map j := ⟨_, rfl⟩
  have hZX : (Z.map j * M') * X = 1 := by
    rw [hXd]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M', hM, Matrix.one_mul, ← Matrix.map_mul, hZY,
      Matrix.map_one _ (map_zero j) (map_one j)]
  have hYψ : (Y.map j).map ψ = Y.map j := by
    ext i k
    simp only [Matrix.map_apply]
    rw [hψ, hj, frobenius_iterate_unramified, hσ]
  have hX : X.map ψ = X * F'.map j := by
    rw [hXd]
    rw [Matrix.map_mul, hYψ, hψ, hφ, Matrix.mul_assoc, ← Matrix.map_mul, hFY, Matrix.map_mul,
      Matrix.mul_assoc]
  obtain ⟨s, hs⟩ := UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse X _ hZX
  have hXS : ∀ i k, X i k ∈ filS K := by
    intro i k
    simp only [hXd, Matrix.mul_apply, Matrix.map_apply]
    refine Subring.sum_mem _ fun c _ => Subring.mul_mem _ (fun n => ?_) (K0_mem K _)
    rw [AlgHom.coe_pow]
    exact (fil_iff _ _ _).1 (hFil n i c)
  have hbS : (X.submatrix s id).det ∈ filS K := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hXS _ _)
  have hb : ((PP l).φB)^[f] (X.submatrix s id).det = j F'.det * (X.submatrix s id).det := by
    have h1 : (X.submatrix s id).map ψ = X.submatrix s id * F'.map j := by
      ext i k
      have := congrFun (congrFun hX (s i)) k
      simpa [Matrix.mul_apply] using this
    rw [← hψ, RingHom.map_det, RingHom.mapMatrix_apply, h1, Matrix.det_mul, mul_comm,
      RingHom.map_det, RingHom.mapMatrix_apply]
  have hle := UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero K f hf hσ _ F'.det hs hb fun i => by
    have := hbS i
    rw [AlgHom.coe_pow] at this
    exact (fil_iff _ _ _).1 this
  rw [hdet] at hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg a) hr.ne').1 hle
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → ∀ hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h, IsCr φ (ext2 (κ 0) (κ 1) x hx) → IsCr φ (chRep (κ 2)) → (IsCr φ (colRep ρ) ↔ (fun g => (z g, y g)) ∈ UpperTheory.V.Loc.finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ κ hκ x y z ρ cx cy cz hρ hx h1 h2
  have hc : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact continuous_triM (t := fun g i => κ i g) hκ cx cy cz
  let f : (B × B) →ₗ[B] (Fin 3 → B) :=
    { toFun := fun v => ![v.1, v.2, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp }
  have hf : ∀ v, f v = ![v.1, v.2, 0] := fun _ => rfl
  rw [← crOn_top]
  refine crExt φ hφ (ext2 (κ 0) (κ 1) x hx) (colRep ρ) (contAction_charExtension_of_continuous_cocycle (hκ 0) (hκ 1) hx cx)
    (contAction_colRep hc) (κ 2) f (LinearMap.proj 2) ![0, 0, 1] (fun g => (z g, y g)) ?_ ?_ ?_ ?_ ?_ ⊤
    (by simp) ((crOn_top _ _).2 h1) ((crOn_top _ _).2 h2)
  · intro v w h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · intro v
    constructor
    · intro h
      refine ⟨(v 0, v 1), ?_⟩
      have h' : v 2 = 0 := h
      ext i
      fin_cases i <;> simp [hf, h']
    · rintro ⟨w, rfl⟩
      rfl
  · rfl
  · intro g v
    rw [colRep_apply, hρ, characterExtensionRep_apply]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro g
    rw [colRep_apply, hρ]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
end
