module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsSum

theorem ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {α β γ : Type*} (s : Finset α) (A : Finset β) (A' : Finset γ) (w : α → ℝ≥0∞)
    (T : α → β → γ → ℝ≥0∞) (c : β → γ → ℝ≥0∞) :
    ∑ a ∈ s, w a * ∑ x ∈ A, ∑ x' ∈ A', T a x x' * c x x' =
      ∑ x ∈ A, ∑ x' ∈ A', c x x' * ∑ a ∈ s, w a * T a x x' := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem pairs_sum_le : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → CompatC → PerRowC →
    RowsMeanC → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (M : Submodule (𝓞 D.host.E) W) (x x' : ℕ),
      (GlobalTheory.DegCnt.Trip HW (gS D) (s • M) D.R.rS x x').encard = (GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard) →
    ∀ B : ℕ → ℕ → ℝ, (∀ x x', 0 ≤ B x x') →
    (∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) * B x x')) →
    ∀ (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ENNReal.ofReal (∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) ≤
      ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
        ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x') *
        ENNReal.ofReal (massC Y u * B x x') := by
  intro D large₂ X Y u hStd hCompat hPerRow hMean W HW hEmb hInv B hB hOrb j' j'' δ' δ'' S hS
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => inv_nonneg.2 (Nat.cast_nonneg _)

  have hterm : ∀ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2) =
      wRow D (X.Fu u) p.1.lam * (wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) := by
    intro p hp
    have hall : p ∈ (Y.tO u u).allPairs Set.univ := by
      have h1 := (hS p hp).1
      simp only [Formalism.FourierDecayAlt.PB.Terms.allPairs, Set.mem_ofPred_eq] at h1 ⊢
      exact ⟨Set.mem_univ _, Set.mem_univ _, h1.2.2⟩
    obtain ⟨hl, hl', -⟩ := hCompat D X Y u p hall
    unfold Formalism.L2.SG.TermOp.wt
    rw [← hl, ← hl', Real.mul_self_sqrt, mul_assoc]
    exacts [rfl, mul_nonneg (hw _) (hw _)]

  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_fiberwise_of_maps_to (g := fun p => p.1.lam) (t := Y.what₂ u) (fun p _ => p.1.mem)]
  refine (ofReal_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun Λ _ => ?_).trans ((le_of_eq (matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero (Y.what₂ u) (Finset.Icc 1 ⌊k2Del D j' δ'⌋₊) (Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊)
    (fun Λ => ENNReal.ofReal (wRow D (X.Fu u) Λ))
    (fun Λ x x' => (((GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x x').encard : ℕ∞) : ℝ≥0∞))
    (fun x x' => ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x')))).trans ?_)
  ·
    beta_reduce
    have hrw : ∑ p ∈ S with p.1.lam = Λ, wRow D (X.Fu u) p.1.lam * (wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) =
        wRow D (X.Fu u) Λ * ∑ p ∈ S with p.1.lam = Λ, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.1 hp).2]
    rw [hrw, ENNReal.ofReal_mul (hw Λ)]
    refine mul_le_mul' le_rfl (hPerRow D large₂ X Y u hStd W HW hEmb Λ j' j'' δ' δ'' _ fun p hp => ?_)
    obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hpS
    exact ⟨h1, hpΛ, h2, h3, h4, h5⟩
  ·
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x' hx' => mul_le_mul' le_rfl ?_
    exact hMean D large₂ X Y u hStd W HW hEmb
      (fun M => (((GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) (B x x') (hB x x')
      (fun s M => by simp only [hInv s M x x'])
      (fun Λ hΛ => hOrb Λ hΛ x x' (Finset.mem_Icc.1 hx).1 (Finset.mem_Icc.1 hx').1)

end GlobalTheory.TypeAsm.PairsSum
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaGraph

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem mem_gmap_iff (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap ψ Λ ↔ ψ.symm x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_map_iff (ψ : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (x : S.V) :
    x ∈ U.map (ψ : S.V →ₗ[E] S.V) ↔ ψ.symm x ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_orth_iff (U : Submodule E S.V) (x : S.V) :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  unfold orth
  simp [Submodule.mem_iInf]

theorem mem_orth_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U : Submodule E S.V)
    (x : S.V) : x ∈ orth S (U.map (ψ : S.V →ₗ[E] S.V)) ↔ ψ.symm x ∈ orth S U := by
  have hi : ∀ a b, S.hT (ψ a) (ψ b) = S.hT a b := hψ
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro h y hy
    have := h (ψ y) ⟨y, hy, rfl⟩
    rw [← hi y (ψ.symm x)]
    simpa using this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [← hi y (ψ.symm x)] at this
    simpa using this

variable {T T' : E}

theorem mem_Lrep_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) (x : S.V) :
    x ∈ Lrep (Formalism.HermitianLatticesTheory.gmap ψ Λ) G ↔ ψ.symm x ∈ Lrep Λ F := by
  unfold Lrep
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_orth_map ψ hψ]

theorem gmap_eq (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap ψ Λ = Λ.map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [mem_gmap_iff, Submodule.mem_map_equiv]
  rfl

theorem XLam_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) :
    XLam (Formalism.HermitianLatticesTheory.gmap ψ Λ) G = (XLam Λ F).map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [Submodule.mem_map_equiv]
  unfold XLam
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_map_iff]
  rfl

theorem mem_NgX_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F G : LFlag S r T) (F' G' : LFlag S r T') (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G)
    (hF' : (Xsp F').map (ψ : S.V →ₗ[E] S.V) = Xsp G') (x : S.V) :
    x ∈ NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' ↔ ψ.symm x ∈ NgX Λ g F F' := by
  have h : NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' =
      (NgX Λ g F F').map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
    unfold NgX
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', XLam_map ψ Λ F G hF,
      XLam_map ψ Λ F' G' hF', gmap_eq]
  rw [h, Submodule.mem_map_equiv]
  rfl

end Gen

end GlobalTheory.IotaGraph

namespace GlobalTheory.IotaGraph

section Dv

variable {D : D7} {T T' : D.host.E}

theorem mem_graph_iff (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D)
    {x' l : (VS D).V} (hx' : x' ∈ Lrep Λ F') (hl : l ∈ Lrep Λ F) :
    (x', l) ∈ (gdat F F' Λ).2.2 ↔ l - x' ∈ NgX Λ (gS D) F F' := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l₀, hl₀, h1, h2, h3⟩
    have hx'Λ : x' ∈ Λ := (Submodule.mem_inf.1 hx').1
    have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
    have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
    have hl₀Λ : l₀ ∈ Λ := (Submodule.mem_inf.1 hl₀).1
    have a1 : x' - l' ∈ XLam Λ F' := Submodule.mem_inf.2 ⟨Λ.sub_mem hx'Λ hl'Λ, h1⟩
    have a2 : l - l₀ ∈ XLam Λ F := Submodule.mem_inf.2 ⟨Λ.sub_mem hlΛ hl₀Λ, h2⟩
    have b1 : x' - l' ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_right a1
    have b2 : l - l₀ ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_left (Submodule.mem_sup_right a2)
    have e : l - x' = (l - l₀) + (l₀ - l') - (x' - l') := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ b2 h3) b1
  · intro h
    exact ⟨x', hx', l, hl, by simp, by simp, h⟩

theorem mem_graph_of_sub (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F)
    (hp : p ∈ (gdat F F' Λ).2.2) : q ∈ (gdat F F' Λ).2.2 := by
  simp only [gdat, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨l', hl', l, hl, k1, k2, k3⟩ := hp
  refine ⟨l', hl', l, hl, ?_, ?_, k3⟩
  · have e : q.1 - l' = (q.1 - p.1) + (p.1 - l') := by abel
    rw [e]; exact Submodule.add_mem _ h1 k1
  · have e : q.2 - l = (q.2 - p.2) + (p.2 - l) := by abel
    rw [e]; exact Submodule.add_mem _ h2 k2

theorem mem_graph_congr (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F) :
    p ∈ (gdat F F' Λ).2.2 ↔ q ∈ (gdat F F' Λ).2.2 := by
  refine ⟨mem_graph_of_sub F F' Λ h1 h2, mem_graph_of_sub F F' Λ ?_ ?_⟩
  · rw [← neg_sub]; exact Submodule.neg_mem _ h1
  · rw [← neg_sub]; exact Submodule.neg_mem _ h2

theorem mem_graph_map (ψ : GV D) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T')
    (hF : (Xsp F).map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G)
    (hF' : (Xsp F').map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G') (Λ : LV D) (x y : (VS D).V) :
    (x, y) ∈ (gdat F F' Λ).2.2 ↔ (ψ x, ψ y) ∈ (gdat G G' (Formalism.HermitianLatticesTheory.gmap ψ Λ)).2.2 := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ l', ?_, ψ l, ?_, ?_, ?_, ?_⟩
    · rw [mem_Lrep_map ψ hψ Λ F' G' hF']; simpa using hl'
    · rw [mem_Lrep_map ψ hψ Λ F G hF]; simpa using hl
    · rw [← hF', mem_map_iff]; simpa using h1
    · rw [← hF, mem_map_iff]; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF']; simpa using h3
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ.symm l', (mem_Lrep_map ψ hψ Λ F' G' hF' l').1 hl', ψ.symm l,
      (mem_Lrep_map ψ hψ Λ F G hF l).1 hl, ?_, ?_, ?_⟩
    · rw [← hF', mem_map_iff] at h1; simpa using h1
    · rw [← hF, mem_map_iff] at h2; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF'] at h3; simpa using h3

end Dv

end GlobalTheory.IotaGraph

namespace GlobalTheory

open GlobalTheory.IotaGraph

theorem iotaCompat_of_graph_eq : ∀ (D : D7) (T T' : D.host.E) (F₀ B : LFlag (D.sp.Y 0) D.R.rS T) (P₁ P₂ B' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D) (ψ₀ ψ₁ β : GV D), ψ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ψ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (Xsp F₀).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp F₀).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp P₁).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (Xsp P₂).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₀ Λ)).2.2 = (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2 → β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (Xsp P₁).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp P₂ → (∀ l ∈ Lrep Λ F₀, (ψ₁⁻¹ * ψ₀) l - l ∈ Xsp F₀) → (∀ x' ∈ Lrep Λ P₁, (ψ₁⁻¹ * ψ₀) x' - β x' ∈ Xsp P₂) → IotaCompat Λ F₀ P₁ P₂ β (gS D) := by
  intro D T T' F₀ B P₁ P₂ B' Λ ψ₀ ψ₁ β h0 h1 hF0 hF1 hP1 hP2 hgr hβ hβΛ hβP hml hmx x' hx' l hl
  have hc : ∀ y, ψ₁ ((ψ₁⁻¹ * ψ₀) y) = ψ₀ y := fun y => ψ₁.apply_symm_apply (ψ₀ y)

  have hβx : β x' ∈ Lrep Λ P₂ := by
    have := (mem_Lrep_map (S := VS D) β hβ Λ P₁ P₂ hβP (β x')).2 (by simpa using hx')
    rwa [hβΛ] at this
  have e1 := mem_graph_iff F₀ P₁ Λ hx' hl
  have e2 := mem_graph_map ψ₀ h0 F₀ B P₁ B' hF0 hP1 Λ x' l
  have e3 := mem_graph_map ψ₁ h1 F₀ B P₂ B' hF1 hP2 Λ ((ψ₁⁻¹ * ψ₀) x') ((ψ₁⁻¹ * ψ₀) l)
  rw [hc, hc] at e3
  have e4 := mem_graph_congr F₀ P₂ Λ (p := ((ψ₁⁻¹ * ψ₀) x', (ψ₁⁻¹ * ψ₀) l)) (q := (β x', l))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hmx x' hx'))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hml l hl))
  have e5 := mem_graph_iff F₀ P₂ Λ hβx hl
  rw [← e1, ← e5, e2, hgr, ← e3, e4]

end GlobalTheory
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

private theorem orth_map_isom_eq_map_orth (D : D7) (φ : GV D) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (U : Submodule D.host.E (VS D).V) :
    Formalism.MainNotions.S.Lat.orth (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) =
      (Formalism.MainNotions.S.Lat.orth (VS D) U).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have hi : ∀ x y, (VS D).hT (φ x) (φ y) = (VS D).hT x y := hφ
  ext v
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv
    refine (Submodule.mem_map).2 ⟨φ.symm v, ?_, by simp⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have h1 := hv (φ x) (Submodule.mem_map_of_mem hx)
    rw [← hi x (φ.symm v)]
    simpa using h1
  · intro hv x hx
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_map).1 hv
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_map).1 hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hw
    simp only [LinearEquiv.coe_coe]
    rw [hi]
    exact hw y hy

private theorem toO_map_eq_toO_map (D : D7) (φ : GV D) (U : Submodule D.host.E (VS D).V) :
    (Formalism.MainNotions.S.Lat.toO (VS D) U).map
              ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      Formalism.MainNotions.S.Lat.toO (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext v
  simp only [Formalism.MainNotions.S.Lat.toO, Submodule.mem_map, Submodule.restrictScalars_mem,
    LinearMap.coe_restrictScalars]

theorem lsub_gmap_of_map_Xsp_eq :
    ∀ (D : D7) (T : D.host.E) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T) (φ : GV D) (M : LV D),
      φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (Xsp F₁).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F₂ →
      Lsub (Formalism.HermitianLatticesTheory.gmap φ M) F₂ = Formalism.HermitianLatticesTheory.gmap φ (Lsub M F₁) := by
  intro D T F₁ F₂ φ M hφ hX
  have hinj : Function.Injective
      ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := φ.injective
  unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj,
    toO_map_eq_toO_map, toO_map_eq_toO_map, ← orth_map_isom_eq_map_orth D φ hφ, hX]

end GlobalTheory
end

section

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termAmplitudeFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Cs C : ℝ) (hC : 0 ≤ C) (j : ℕ) (δ : ℕ → D.host.E) :
    0 ≤ k2a large₂ CH Cs C j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hS : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := le_trans zero_le_one (one_le_sigma_product _ j δ)
  unfold k2a
  refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _)
    (Real.rpow_nonneg (minor_norm_nonneg j δ) _)) (Real.rpow_nonneg ?_ _)) (Real.rpow_nonneg hS _)
  unfold Formalism.MainNotions.S.Cnt.Hb
  exact Real.rpow_nonneg hb.le _

theorem typeBound_of_amplitude_pairs : AmpP → PairsP → TypeP := by
  intro hAmp hPairs Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hA⟩ := hAmp Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Ch, Cp, hCh, hCp, C'₁, Cl₁, hP⟩ := hPairs Cg cb Cw cT CT C0 CH hCH
  refine ⟨CH, Ch, Cp, hCH, hCh, hCp, fun Cs hCs => ?_⟩
  obtain ⟨C₀, hC₀, hA2⟩ := hA Cs (by linarith)
  refine ⟨C₀, fun C hC => ?_⟩
  obtain ⟨C'₂, Cl₂, hA3⟩ := hA2 C hC
  refine ⟨max C'₁ C'₂, max Cl₁ Cl₂, fun C' Cl hC' hCl D large₂ X Y u hTies hK hConc => ?_⟩
  have amp := hA3 C' Cl (le_of_max_le_right hC') (le_of_max_le_right hCl) D large₂ X Y u hTies hK hConc
  have pairs := hP C' Cl (le_of_max_le_left hC') (le_of_max_le_left hCl) D large₂ X Y u hK hConc
  intro j' hj' j'' hj'' δ' δ'' S hS
  have hC0 : 0 ≤ C := le_trans hC₀ hC
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hsq : Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u) = dpiC X u := Real.mul_self_sqrt hdpi
  have ha' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j' δ'
  have ha'' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j'' δ''
  have hK0 : 0 ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') :=
    mul_nonneg hdpi (mul_nonneg ha' ha'')
  have hterm : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
    intro p hp
    obtain ⟨hmem, hj1, hj2, hl1, hl2⟩ := hS p hp
    have h1 := amp p.1 hmem.1
    have h2 := amp p.2 hmem.2.1
    rw [hj1, hl1] at h1
    rw [hj2, hl2] at h2
    calc ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
        ≤ (Formalism.L2.SG.TermOp.wt p.1 * Real.sqrt (dpiC X u) * (omT p.1 * k2a large₂ CH Cs C j' δ')) *
          (Formalism.L2.SG.TermOp.wt p.2 * Real.sqrt (dpiC X u) * (omT p.2 * k2a large₂ CH Cs C j'' δ'')) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = (Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u)) * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
          ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by ring
      _ = _ := by rw [hsq]
  calc ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
      ≤ ∑ p ∈ S, dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := Finset.sum_le_sum hterm
    _ = dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ∑ p ∈ S, ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
      rw [Finset.mul_sum]
    _ ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        (massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')) :=
      mul_le_mul_of_nonneg_left (pairs j' hj' j'' hj'' δ' δ'' S hS) hK0
    _ = _ := by ring

end GlobalTheory.TypeAsm
end
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsLab

theorem norms_of_relevant : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  intro Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost hNF hLab hTerm hH t ht
  have hS : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := hHost D large₂ hS
  obtain ⟨N, hN, hNj, hNT⟩ := hNF D large₂ X Y u hS t ht
  have hT : N.IsTerm (gS D) t.lam := hTerm D large₂ X Y u hS t N hN
  obtain ⟨-, -, hDel, hDb, -⟩ := hLab D large₂ X Y u hS t N hN
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal D.host.E (VS D).V (HV D) hK D.R.rS N (gS D)
    t.lam (by omega) hT
  have hPF : PFHost D := PFHost_of_data D hH.1.2.1
  have hC : 2 * (CH + 1) ≤ 2 * (CH + 1) := le_rfl
  have hup := (delta_pos_le_height_sq hPF large₂ hCH hC t ht).2
  have hb := two_le_scale_b D large₂
  have hHb : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := by
    unfold Hb
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hS1 := one_le_sigma_product (D := D) (H1C large₂ CH) (jT t) (labT t)
  have hA : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hHb (one_le_pow₀ hS1)
  refine ⟨hDel ▸ hDel1, hDb ▸ hDb1, hup, ?_⟩
  have hcard : (k2ends D (jT t) (labT t)).card ≤ D.R.rS := by
    unfold k2ends
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    unfold jT
    omega
  calc DbL D (jT t) (labT t)
      ≤ ∏ _l ∈ k2ends D (jT t) (labT t),
          Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
        unfold DbL
        refine Finset.prod_le_prod₀ (fun l _ => ?_) (fun l hl => localNorm_le_height_sq hPF large₂ hCH hC t l hl)
        unfold Nloc
        exact_mod_cast FractionalIdeal.absNorm_nonneg _
    _ = _ ^ (k2ends D (jT t) (labT t)).card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_right₀ hA hcard

end GlobalTheory.TypeAsm.PairsLab
end
