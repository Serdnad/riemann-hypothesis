module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import GroundTheory.LocalFields.PadicLogSeries
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi.ACA

section
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]

private lemma lift_commute_of {X : Type} (u : X → Module.End ℂ Y) (z : Module.End ℂ Y)
    (h : ∀ x, Commute (u x) z) (p : FreeAlgebra ℂ X) : Commute (FreeAlgebra.lift ℂ u p) z := by
  induction p using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact Algebra.commutes r z
  | grade1 x => simpa using h x
  | mul p q hp hq => rw [map_mul]; exact hp.mul_left hq
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq

private lemma lift_commute {X X' : Type} (u : X → Module.End ℂ Y) (v : X' → Module.End ℂ Y)
    (h : ∀ x y, Commute (u x) (v y)) (p : FreeAlgebra ℂ X) (q : FreeAlgebra ℂ X') :
    Commute (FreeAlgebra.lift ℂ u p) (FreeAlgebra.lift ℂ v q) :=
  lift_commute_of u _ (fun x => (lift_commute_of v (u x) (fun y => (h x y).symm) q).symm) p

private lemma lift_intertwine {X : Type} (u v : X → Module.End ℂ Y) (A : Module.End ℂ Y)
    (h : ∀ x, A * u x = v x * A) (p : FreeAlgebra ℂ X) :
    A * FreeAlgebra.lift ℂ u p = FreeAlgebra.lift ℂ v p * A := by
  induction p using FreeAlgebra.induction with
  | grade0 r => simpa using (Algebra.commutes r A).symm
  | grade1 x => simpa using h x
  | mul p q hp hq => rw [map_mul, map_mul, ← mul_assoc, hp, mul_assoc, hq, mul_assoc]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), mul_add, add_mul, hp, hq]

private lemma lift_lift {X : Type} (u : X → Module.End ℂ Y) (p : FreeAlgebra ℂ (FreeAlgebra ℂ X)) :
    FreeAlgebra.lift ℂ (fun q => FreeAlgebra.lift ℂ u q) p =
      FreeAlgebra.lift ℂ u (FreeAlgebra.lift ℂ (fun q : FreeAlgebra ℂ X => q) p) := by
  have h : FreeAlgebra.lift ℂ (fun q => FreeAlgebra.lift ℂ u q) =
      (FreeAlgebra.lift ℂ u).comp (FreeAlgebra.lift ℂ (fun q : FreeAlgebra ℂ X => q)) :=
    FreeAlgebra.hom_ext (by funext q; simp)
  exact DFunLike.congr_fun h p

private lemma mem_adjoin_iff {X : Type} (u : X → Module.End ℂ Y) (x : Module.End ℂ Y) :
    x ∈ Algebra.adjoin ℂ (Set.range u) ↔ ∃ q, FreeAlgebra.lift ℂ u q = x := by
  constructor
  · intro hx
    have hle : Algebra.adjoin ℂ (Set.range u) ≤ (FreeAlgebra.lift ℂ u).range :=
      Algebra.adjoin_le (by
        rintro _ ⟨t, rfl⟩
        exact ⟨FreeAlgebra.ι ℂ t, by simp⟩)
    obtain ⟨q, hq⟩ := hle hx
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    induction q using FreeAlgebra.induction with
    | grade0 r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
    | grade1 t =>
      simpa using (Algebra.subset_adjoin (Set.mem_range_self t) : u t ∈ Algebra.adjoin ℂ (Set.range u))
    | mul p q hp hq => rw [map_mul]; exact Subalgebra.mul_mem _ hp hq
    | add p q hp hq => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hp hq

private lemma conj_mul (A x y : Module.End ℂ Y) (hAA : A * A = 1) :
    A * x * A * (A * y * A) = A * (x * y) * A := by
  calc A * x * A * (A * y * A) = A * x * (A * A) * y * A := by simp only [mul_assoc]
    _ = A * (x * y) * A := by rw [hAA, mul_one]; simp only [mul_assoc]

end

end UpperTheory.V.Z.Mult.Pi.ACA

open UpperTheory.V.Z.Mult.Pi.ACA in
theorem UpperTheory.V.Z.Mult.Pi.absCoreA_pf :
    AbsCore → RankOne → Corner → MinIdem → AbsCoreA := by
  intro hC hR hK hI I _ J M _ _ _ Y _ _ _ _ α a b A hM hrel haa hab hAA hAb hY
  classical
  obtain ⟨d, hd0, hd⟩ := hC I (fun i => FreeAlgebra ℂ (J i)) M Y
    (fun i q => FreeAlgebra.lift ℂ (α i) q) (fun i q => FreeAlgebra.lift ℂ (a i) q)
    (fun i q => FreeAlgebra.lift ℂ (b i) q) A
    (fun i W hW => hM i W fun f x hx => by simpa using hW (FreeAlgebra.ι ℂ f) x hx)
    (fun i p h => by
      rw [lift_lift] at h ⊢
      exact hrel i _ h)
    (fun i k h f g => lift_commute _ _ (haa i k h) f g)
    (fun i k f g => lift_commute _ _ (hab i k) f g)
    hAA
    (fun i q => lift_intertwine _ _ A (hAb i) q)
    (fun W hW => hY W fun i f x hx => by simpa using hW i (FreeAlgebra.ι ℂ f) x hx)
  have hd' : ∀ x y : ∀ i, FreeAlgebra ℂ (J i),
      LinearMap.trace ℂ Y (((Finset.univ : Finset I).toList.map fun i =>
        FreeAlgebra.lift ℂ (a i) (x i) * FreeAlgebra.lift ℂ (b i) (y i)).prod * A) =
      d * ∏ i, LinearMap.trace ℂ (M i)
        (FreeAlgebra.lift ℂ (α i) (x i) * FreeAlgebra.lift ℂ (α i) (y i)) := hd
  have hnt : ∀ i, Nontrivial (M i) := by
    intro i
    by_contra hn
    have hs : Subsingleton (M i) := not_nontrivial_iff_subsingleton.1 hn
    have h0 : FreeAlgebra.lift ℂ (α i) (1 : FreeAlgebra ℂ (J i)) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have h1 := hrel i 1 h0
    rw [map_one] at h1
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    exact hy (by simpa using LinearMap.congr_fun h1 y)
  have hex : ∀ i, ∃ p : FreeAlgebra ℂ (J i),
      LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) p * FreeAlgebra.lift ℂ (α i) p) = 1 ∧
      FreeAlgebra.lift ℂ (a i) p * FreeAlgebra.lift ℂ (a i) p = FreeAlgebra.lift ℂ (a i) p ∧
      ∀ q, ∃ c : ℂ, FreeAlgebra.lift ℂ (a i) p * FreeAlgebra.lift ℂ (a i) q *
        FreeAlgebra.lift ℂ (a i) p = c • FreeAlgebra.lift ℂ (a i) p := fun i => by
    haveI := hnt i
    exact hI (J i) (M i) Y (α i) (a i) (hM i) (hrel i)
  choose p hp1 hp2 hp3 using hex
  have hAq : ∀ i q, A * FreeAlgebra.lift ℂ (a i) q = FreeAlgebra.lift ℂ (b i) q * A :=
    fun i q => lift_intertwine _ _ A (hAb i) q
  have hbq : ∀ i q, FreeAlgebra.lift ℂ (b i) q = A * FreeAlgebra.lift ℂ (a i) q * A :=
    fun i q => by rw [hAq, mul_assoc, hAA, mul_one]
  have hbf : ∀ i f, b i f = A * a i f * A := fun i f => by rw [hAb, mul_assoc, hAA, mul_one]
  have hbb : ∀ i k, i ≠ k → ∀ f g, Commute (b i f) (b k g) := by
    intro i k h f g
    show b i f * b k g = b k g * b i f
    rw [hbf i f, hbf k g, conj_mul A _ _ hAA, conj_mul A _ _ hAA, (haa i k h f g).eq]
  obtain ⟨e, he⟩ : ∃ e : I → Module.End ℂ Y, ∀ i, e i = FreeAlgebra.lift ℂ (a i) (p i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : I → Module.End ℂ Y, ∀ i, e' i = FreeAlgebra.lift ℂ (b i) (p i) :=
    ⟨_, fun _ => rfl⟩
  have hee' : ∀ i, e' i = A * e i * A := fun i => by rw [he, he', hbq]
  have hidem : ∀ i, e i * e i = e i := fun i => by rw [he]; exact hp2 i
  have hcorner := hK I J Y a b e e' haa hab hbb hY
    (fun i => ⟨(mem_adjoin_iff _ _).2 ⟨p i, (he i).symm⟩, hidem i, fun x hx => by
      obtain ⟨q, rfl⟩ := (mem_adjoin_iff _ _).1 hx
      rw [he]
      exact hp3 i q⟩)
    (fun i => ⟨(mem_adjoin_iff _ _).2 ⟨p i, (he' i).symm⟩, by
        rw [hee', conj_mul A _ _ hAA, hidem], fun x hx => by
      obtain ⟨q, rfl⟩ := (mem_adjoin_iff _ _).1 hx
      obtain ⟨c, hc⟩ := hp3 i q
      refine ⟨c, ?_⟩
      rw [hee', hbq, conj_mul A _ _ hAA, conj_mul A _ _ hAA, he, hc, mul_smul_comm, smul_mul_assoc]⟩)
    _ rfl
  obtain ⟨hff, hsc⟩ := hcorner
  have hfac : ∀ i, Commute A (e i * e' i) := by
    intro i
    have hce : Commute (e i) (e' i) := by
      rw [he, he']
      exact lift_commute _ _ (hab i i) _ _
    have h1 : A * e i = e' i * A := by rw [he, he']; exact hAq i (p i)
    have h2 : A * e' i = e i * A := by
      rw [hee', ← mul_assoc, ← mul_assoc, hAA, one_mul]
    show A * (e i * e' i) = e i * e' i * A
    calc A * (e i * e' i) = A * e i * e' i := by rw [mul_assoc]
      _ = e' i * (A * e' i) := by rw [h1, mul_assoc]
      _ = e' i * e i * A := by rw [h2, mul_assoc]
      _ = e i * e' i * A := by rw [hce.eq]
  have hAF : Commute A ((Finset.univ : Finset I).toList.map fun i => e i * e' i).prod :=
    Commute.list_prod_right _ _ (by
      intro z hz
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hz
      exact hfac k)
  have htr : LinearMap.trace ℂ Y
      (((Finset.univ : Finset I).toList.map fun i => e i * e' i).prod * A) = d := by
    have h := hd' p p
    simp only [hp1, Finset.prod_const_one, mul_one] at h
    simpa only [he, he'] using h
  have hn : ‖d‖ = 1 := by
    rcases hR Y _ A hff hAA hAF.eq hsc with h | h
    · rw [htr] at h
      exact absurd h hd0
    · rwa [htr] at h
  refine ⟨d, hn, fun f g => ?_⟩
  simpa using hd' (fun i => FreeAlgebra.ι ℂ (f i)) (fun i => FreeAlgebra.ι ℂ (g i))
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem lv_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) (hv : v ∈ fixed ρ K) :
    Lv ρ K ((K : Set G).indicator 1) v = v := by
  have hc : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := by
    have h : (QuotientGroup.mk (QuotientGroup.mk 1 : G ⧸ K).out : G ⧸ K) = QuotientGroup.mk 1 :=
      QuotientGroup.out_eq' _
    simpa using QuotientGroup.eq.1 h
  have hq : ∀ q : G ⧸ K, q ≠ QuotientGroup.mk 1 → q.out ∉ K := by
    intro q hne hmem
    apply hne
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using hmem)
  unfold Lv levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)
    (fun q hne => by rw [Set.indicator_of_notMem (hq q hne), zero_smul]),
    Set.indicator_of_mem (show _ ∈ (K : Set G) from hc)]
  simpa using hv ⟨_, hc⟩

private theorem trOn_of_id {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    [FiniteDimensional ℂ M] (L : V →ₗ[ℂ] V) (hL : ∀ v ∈ M, L v = v) :
    trOn M L = (Module.finrank ℂ M : ℂ) := by
  have h : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [hL v hv]; exact hv
  have hid : L.restrict h = LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, hL v.1 v.2]
  unfold trOn
  rw [dite_eq_left h, hid]
  exact LinearMap.trace_id ℂ _

private theorem finFn_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w) : (fun g => finFn S φ₁ φ₂ (g, 1)) = pf S (two φ₁ φ₂) := by
  funext g
  have h1 : ∀ w : Pl E, atW w ((g, 1) : Gf E n 0) = (qw n w false g, 1) :=
    fun w => Prod.ext rfl (map_one (GeneralLinearGroup.map (pLoc E w)))
  have h2 : ∀ w : Pl E, atW w (thP E n 0 (g, 1)) = (qw n w true g, 1) := by
    intro w
    refine Prod.ext rfl ?_
    simp [atW, thP]
  unfold finFn pf
  simp only [h1, h2]
  rfl

private theorem ind_hecke {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (M N' : Subgroup (GLw n w)) (ho : IsOpen (M : Set (GLw n w))) (hM : M ≤ KGL w (n := n)) (hN : N' ≤ M) :
    IsHecke N' ((M : Set (GLw n w)).indicator 1) := by
  have hcl : IsClosed (M : Set (GLw n w)) := M.isClosed_of_isOpen ho
  have hcomp : IsCompact (M : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2.of_isClosed_subset hcl hM
  refine ⟨hcomp.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal Set.support_indicator_subset hcl), fun k hk x => ?_⟩
  have a1 : k * x ∈ M ↔ x ∈ M := M.mul_mem_cancel_left (hN hk)
  have a2 : x * k ∈ M ↔ x ∈ M := M.mul_mem_cancel_right (hN hk)
  simp only [Set.indicator, SetLike.mem_coe, a1, a2, Pi.one_apply, and_self]

theorem _root_.UpperTheory.V.Z.Mult.Pi.levelTrA : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Mult.Pi.ZTrA → UpperTheory.V.Z.Mult.Pi.SeenTrA → TTr → UpperTheory.V.Z.Mult.Pi.LevelTrA := by
  intro hAdm hZ hSeen hT E _ _ _ n S Z N hSec hSp hG π y B τ hB hτ
  obtain ⟨hne, d₀, hd₀, hd⟩ := hZ E n S Z N hSec hSp hG π y τ hτ
  let c : Pl E → ℂ := fun w => (((N w).relIndex (KGL w (n := n)) : ℕ) : ℂ) ^ 2
  have hc : ∀ w ∈ Z, ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (two φ₁ φ₂ w false) * Lv (τ w).ρ (N w) (two φ₁ φ₂ w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) :=
    fun w hw => hSeen E n w (hSp w hw).2 (τ w) (N w) (hG w).1 (hG w).2.1
  refine ⟨?_, d₀ * ∏ w ∈ Z, c w, by simp [hd₀, c], ?_⟩
  · let φ₀ : ∀ w : Pl E, LF n 0 w := fun w p => (N w : Set (GLw n w)).indicator 1 p.1
    have h2 : ∀ w b, two φ₀ φ₀ w b = (N w : Set (GLw n w)).indicator 1 := by
      intro w b
      cases b <;> rfl
    refine ⟨φ₀, fun w _ N' hN' b => ?_, Finset.prod_ne_zero_iff.2 fun w hw h0 => ?_⟩
    · rw [h2]
      exact ind_hecke w (N w) N' (hG w).1 (hG w).2.1 hN'
    · haveI : FiniteDimensional ℂ (fixed (τ w).ρ (N w)) := hAdm E n w (τ w) (N w) (hG w).1
      have e := hc w hw φ₀ φ₀ fun b => by
        rw [h2]
        exact ind_hecke w (N w) (N w) (hG w).1 (hG w).2.1 le_rfl
      rw [h0, mul_zero, h2, h2, trOn_of_id _ _ fun v hv => by
        rw [Module.End.mul_apply, lv_unit _ _ v hv, lv_unit _ _ v hv]] at e
      exact hne w hw (Submodule.finrank_eq_zero.1 (Nat.cast_eq_zero.1 e))
  · intro φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    obtain ⟨h1, h2, h3⟩ := hT E n S Z N hSec hSp hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    have hF : ∀ w ∈ Z, ∀ b, two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w b = two φ₁ φ₂ w b := by
      intro w hw b
      cases b <;> simp [two, intersection_update_fsHerm_neg_one, hw]
    have hP : ∀ w ∈ Z, GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w))
        (Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w false) *
          Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) := by
      intro w hw
      rw [hF w hw, hF w hw]
      exact hc w hw φ₁ φ₂ (hφ w hw)
    rw [finFn_one S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)]
    refine ⟨h1, ?_⟩
    rw [h3, smul_mul_assoc, map_smul, hd _ h2, smul_eq_mul, Finset.prod_congr rfl hP, Finset.prod_mul_distrib]
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

namespace UpperTheory.V.Z.Mult.Pi

theorem minIdem_pf : MinIdem := by
  intro J M Y _ _ _ _ _ _ α a hs hk
  have surj : Function.Surjective (FreeAlgebra.lift ℂ α) :=
    DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by
      simpa using hW (FreeAlgebra.ι ℂ f) x hx
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  obtain ⟨p, hp⟩ := surj (LinearMap.smulRight l v)
  have same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' →
      FreeAlgebra.lift ℂ a r = FreeAlgebra.lift ℂ a r' := by
    intro r r' h
    have h0 : FreeAlgebra.lift ℂ a (r - r') = 0 := hk _ (by rw [map_sub, h, sub_self])
    rw [map_sub] at h0
    exact sub_eq_zero.1 h0
  have idem : LinearMap.smulRight l v * LinearMap.smulRight l v = LinearMap.smulRight l v := by
    ext x
    simp [hl]
  refine ⟨p, ?_, ?_, fun q => ⟨l (FreeAlgebra.lift ℂ α q v), ?_⟩⟩
  · rw [hp, idem, LinearMap.trace_smulRight, hl]
  · rw [← map_mul]
    exact same _ _ (by rw [map_mul, hp, idem])
  · rw [← map_mul, ← map_mul, ← map_smul]
    refine same _ _ ?_
    rw [map_mul, map_mul, map_smul, hp]
    ext x
    simp [smul_smul, mul_comm]

end UpperTheory.V.Z.Mult.Pi
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi.Cn

variable {R : Type} [Ring R] [Algebra ℂ R]

private def Good (s : Set R) (e : R) : Prop :=
  e ∈ Algebra.adjoin ℂ s ∧ e * e = e ∧ ∀ x ∈ Algebra.adjoin ℂ s, ∃ c : ℂ, e * x * e = c • e

private lemma adj_comm {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {x y : R}
    (hx : x ∈ Algebra.adjoin ℂ s) (hy : y ∈ Algebra.adjoin ℂ t) : Commute x y :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun _ hb =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => (h a ha _ hb).symm).symm

private lemma mem_span {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {z : R}
    (hz : z ∈ Algebra.adjoin ℂ (s ∪ t)) :
    z ∈ Submodule.span ℂ {w : R | ∃ x ∈ Algebra.adjoin ℂ s, ∃ y ∈ Algebra.adjoin ℂ t, w = x * y} := by
  induction hz using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · exact Submodule.subset_span ⟨g, Algebra.subset_adjoin hg, 1, one_mem _, (mul_one _).symm⟩
    · exact Submodule.subset_span ⟨1, one_mem _, g, Algebra.subset_adjoin hg, (one_mul _).symm⟩
  | algebraMap r =>
    exact Submodule.subset_span ⟨_, Subalgebra.algebraMap_mem _ r, 1, one_mem _, (mul_one _).symm⟩
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv =>
    have hm := Submodule.mul_mem_mul hu hv
    rw [Submodule.span_mul_span] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, _, ⟨x', hx', y', hy', rfl⟩, rfl⟩
    refine ⟨x * x', mul_mem hx hx', y * y', mul_mem hy hy', ?_⟩
    exact ((adj_comm h hx' hy).mul_mul_mul_comm x y').symm

private lemma good_two {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {e e' : R}
    (he : Good s e) (he' : Good t e') : Good (s ∪ t) (e * e') := by
  obtain ⟨m, i, c⟩ := he
  obtain ⟨m', i', c'⟩ := he'
  refine ⟨mul_mem (Algebra.adjoin_mono Set.subset_union_left m)
    (Algebra.adjoin_mono Set.subset_union_right m'), ?_, fun z hz => ?_⟩
  · rw [(adj_comm h m m').symm.mul_mul_mul_comm, i, i']
  · have hz' := mem_span h hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      obtain ⟨p, hp⟩ := c x hx
      obtain ⟨q, hq⟩ := c' y hy
      refine ⟨p * q, ?_⟩
      rw [(adj_comm h hx m').symm.mul_mul_mul_comm,
        (adj_comm h m (mul_mem m' hy)).symm.mul_mul_mul_comm, hp, hq, smul_mul_smul_comm]
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨p, hp⟩ := hu
      obtain ⟨q, hq⟩ := hv
      exact ⟨p + q, by rw [mul_add, add_mul, hp, hq, add_smul]⟩
    | smul r u _ hu =>
      obtain ⟨p, hp⟩ := hu
      exact ⟨r * p, by rw [mul_smul_comm, smul_mul_assoc, hp, smul_smul]⟩

private lemma good_list {I : Type} (s : I → Set R) (e : I → R)
    (h : ∀ i k, i ≠ k → ∀ x ∈ s i, ∀ y ∈ s k, Commute x y) (he : ∀ i, Good (s i) (e i))
    (l : List I) (hl : l.Nodup) : Good {x | ∃ i ∈ l, x ∈ s i} (l.map e).prod := by
  induction l with
  | nil =>
    refine ⟨by simpa using one_mem _, by simp, fun x hx => ?_⟩
    have h0 : {x | ∃ i ∈ ([] : List I), x ∈ s i} = ∅ := by simp
    rw [h0, Algebra.adjoin_empty, Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    exact ⟨r, by simp [Algebra.algebraMap_eq_smul_one]⟩
  | cons i l ih =>
    have hn := List.nodup_cons.1 hl
    have h0 : {x | ∃ k ∈ i :: l, x ∈ s k} = s i ∪ {x | ∃ k ∈ l, x ∈ s k} := by
      ext x; simp
    rw [h0, List.map_cons, List.prod_cons]
    refine good_two ?_ (he i) (ih hn.2)
    rintro x hx y ⟨k, hk, hy⟩
    exact h i k (fun e => hn.1 (e ▸ hk)) x hx y hy

end UpperTheory.V.Z.Mult.Pi.Cn

open UpperTheory.V.Z.Mult.Pi.Cn in
theorem UpperTheory.V.Z.Mult.Pi.corner_pf :
    Corner := by
  intro I _ J Y _ _ _ _ a b e e' haa hab hbb hY he he' f hf
  have hg := good_list (fun i => Set.range (a i) ∪ Set.range (b i)) (fun i => e i * e' i)
    (by
      rintro i k hik x (⟨p, rfl⟩ | ⟨p, rfl⟩) y (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · exact haa i k hik p q
      · exact hab i k p q
      · exact (hab k i q p).symm
      · exact hbb i k hik p q)
    (fun i => good_two (by
      rintro x ⟨p, rfl⟩ y ⟨q, rfl⟩
      exact hab i i p q) (he i) (he' i))
    (Finset.univ : Finset I).toList (Finset.nodup_toList _)
  rw [← hf] at hg
  obtain ⟨-, h1, h2⟩ := hg
  refine ⟨h1, fun x => ?_⟩
  have hsurj := DiscreteGroups.T1.Desc.Swap3.burnside (Algebra.adjoin ℂ
    {x | ∃ i ∈ (Finset.univ : Finset I).toList, x ∈ Set.range (a i) ∪ Set.range (b i)}).val (by
    intro W hW
    refine hY W fun i p x hx => ⟨?_, ?_⟩
    · exact hW ⟨a i p, Algebra.subset_adjoin ⟨i, by simp, Or.inl ⟨p, rfl⟩⟩⟩ x hx
    · exact hW ⟨b i p, Algebra.subset_adjoin ⟨i, by simp, Or.inr ⟨p, rfl⟩⟩⟩ x hx)
  obtain ⟨⟨z, hz⟩, rfl⟩ := hsurj x
  exact h2 z hz
end
