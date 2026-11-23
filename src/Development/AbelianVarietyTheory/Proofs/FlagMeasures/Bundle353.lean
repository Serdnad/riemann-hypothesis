module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle341
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NRatInv

variable {D : D7}

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {j k : ℕ} (h : j ≤ k) :
    Xflag F j ≤ Xflag F k :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => lt_of_lt_of_le hi h)

theorem xsp_eq {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F = Xflag F D.R.rS := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x; simp

theorem mem_orth_iff {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (y : (VS D).V) :
    y ∈ orth (VS D) (Xsp F) ↔ ∀ x ∈ Xsp F, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem inv_mem_of_map_le (n : GV D) (W : Submodule D.host.E (VS D).V) [FiniteDimensional D.host.E W]
    (h : ∀ x ∈ W, n x ∈ W) : ∀ x ∈ W, n⁻¹ x ∈ W := by
  have hle : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ W := by
    rintro _ ⟨y, hy, rfl⟩; exact h y hy
  have heq : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = W :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n W)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : n⁻¹ (n y) = y := n.symm_apply_apply y
  simpa [this] using hy

end GlobalTheory.NRatInv

namespace GlobalTheory.NRatInv

variable {D : D7}

theorem xflag_fd {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    FiniteDimensional D.host.E (Xflag F j) :=
  FiniteDimensional.span_of_finite _ (Set.toFinite _)

theorem map_xflag {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) (k : ℕ) :
    ∀ x ∈ Xflag F k, n x ∈ Xflag F k := by
  intro x hx
  cases k with
  | zero =>
    have : Xflag F 0 = ⊥ := by
      show Submodule.span _ _ = ⊥
      simp
    rw [this, Submodule.mem_bot] at hx
    subst hx; simp
  | succ j =>
    have h1 := hn.2.1 j x hx
    have h2 := xflag_mono F (Nat.le_succ j) h1
    simpa using add_mem h2 hx

theorem adapt_and_inv_mem : ∀ (D : D7) (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : GV D),
    n ∈ NRat F → Adapt n F F ∧ n⁻¹ ∈ NRat F := by
  intro D T F n hn
  obtain ⟨hiso, hfl, hor⟩ := hn
  have hn' : n ∈ NRat F := ⟨hiso, hfl, hor⟩
  refine ⟨⟨hiso, ?_⟩, ?_⟩
  · intro a
    induction a using Fin.lastCases with
    | last =>
      have hz : frame F (Fin.last D.R.rS) = F.fl.z := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [hz]
      have : F.fl.z ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff]
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact F.fl.z_orth i
        | zero => simp
        | add a b _ _ ha hb => simp [ha, hb]
        | smul c a _ ha => simp [ha]
      have := hor _ this
      simpa [xsp_eq] using this
    | cast i =>
      have he : frame F (Fin.castSucc i) = F.fl.e i := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [he]
      have hmem : F.fl.e i ∈ Xflag F (i.val + 1) :=
        Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
      simpa using hfl i.val _ hmem
  · refine ⟨inv_mem hiso, ?_, ?_⟩
    · intro j x hx
      haveI := xflag_fd F (j + 1)
      have hy := inv_mem_of_map_le n _ (map_xflag hn' (j + 1)) x hx
      have key := hfl j _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this
    · intro x hx
      haveI := xflag_fd F D.R.rS
      have hsp : ∀ y ∈ Xsp F, n⁻¹ y ∈ Xsp F := by
        rw [xsp_eq]; exact inv_mem_of_map_le n _ (map_xflag hn' D.R.rS)
      have hspn : ∀ y ∈ Xsp F, n y ∈ Xsp F := by
        rw [xsp_eq]; exact map_xflag hn' D.R.rS
      have hy : n⁻¹ x ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff] at hx ⊢
        intro e he
        have h1 : n⁻¹ (n e) = e := n.symm_apply_apply e
        have h2 := (inv_mem hiso) (n e) x
        rw [h1] at h2
        rw [h2]; exact hx _ (hspn e he)
      have key := hor _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this

end GlobalTheory.NRatInv
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgTr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def Hom {T T' : E} (φ : S.V ≃ₗ[E] S.V) (A : LFlag S r T) (B : LFlag S r T') : Prop :=
  ∀ a : Fin (r + 1), φ (frame A a) - frame B a ∈ Xflag B a.val

theorem frame_castSucc {T : E} (A : LFlag S r T) (i : Fin r) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec, Fin.snoc_castSucc]

theorem frame_last {T : E} (A : LFlag S r T) : frame A (Fin.last r) = A.fl.z := by
  simp [frame, FlagG.fvec, Fin.snoc_last]

theorem xflag_mono {T : E} (A : LFlag S r T) {i j : ℕ} (h : i ≤ j) : Xflag A i ≤ Xflag A j := by
  exact Submodule.span_mono (Set.image_mono (fun k hk => lt_of_lt_of_le hk h))

theorem e_mem_xflag {T : E} (A : LFlag S r T) (i : Fin r) {j : ℕ} (h : i.1 < j) : A.fl.e i ∈ Xflag A j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem Hom.map_mem {T T' : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} (h : Hom φ A B)
    (j : ℕ) {x : S.V} (hx : x ∈ Xflag A j) : φ x ∈ Xflag B j := by
  have hle : Xflag A j ≤ (Xflag B j).comap (φ : S.V →ₗ[E] S.V) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    have h1 := h i.castSucc
    rw [frame_castSucc, frame_castSucc] at h1
    have h2 : φ (A.fl.e i) = (φ (A.fl.e i) - B.fl.e i) + B.fl.e i := by abel
    show φ (A.fl.e i) ∈ Xflag B j
    rw [h2]
    refine Submodule.add_mem _ ?_ (e_mem_xflag B i hi)
    exact xflag_mono B (le_of_lt hi) h1
  exact hle hx

theorem Hom.comp {T T' T'' : E} {φ ψ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} {C : LFlag S r T''}
    (hφ : Hom φ B C) (hψ : Hom ψ A B) : Hom (φ * ψ) A C := by
  intro a
  have e1 : (φ * ψ) (frame A a) - frame C a = φ (ψ (frame A a) - frame B a) + (φ (frame B a) - frame C a) := by
    rw [LinearEquiv.mul_apply, map_sub]; abel
  rw [e1]
  exact Submodule.add_mem _ (hφ.map_mem _ (hψ a)) (hφ a)

theorem Hom.inv {T : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} (h : Hom φ A A) : Hom φ⁻¹ A A := by
  have hW : ∀ j : ℕ, ∀ x ∈ Xflag A j, φ⁻¹ x ∈ Xflag A j := by
    intro j x hx
    set W := Xflag A j
    have : FiniteDimensional E W := FiniteDimensional.span_of_finite E ((Set.toFinite _).image _)
    have hle : W.map (φ : S.V →ₗ[E] S.V) ≤ W := by
      rintro y ⟨w, hw, rfl⟩
      exact h.map_mem j hw
    have heq : W.map (φ : S.V →ₗ[E] S.V) = W :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq φ W)
    rw [← heq] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have : φ⁻¹ (φ w) = w := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    simpa [this] using hw
  intro a
  have e1 : φ⁻¹ (frame A a) - frame A a = -(φ⁻¹ (φ (frame A a) - frame A a)) := by
    have : φ⁻¹ (φ (frame A a)) = frame A a := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    rw [map_sub, this]; abel
  rw [e1]
  exact Submodule.neg_mem _ (hW _ _ (h a))

theorem xflag_r {T : E} (A : LFlag S r T) : Xflag A r = Xsp A := by
  show Submodule.span E (A.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range A.fl.e)
  congr 1
  rw [← Set.image_univ]
  congr 1
  ext i; simp

theorem z_mem_orth {T : E} (A : LFlag S r T) : A.fl.z ∈ orth S (Xsp A) := by
  have hle : Xsp A ≤ LinearMap.ker (S.hT.flip A.fl.z) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    show S.hT.flip A.fl.z (A.fl.e i) = 0
    rw [LinearMap.flip_apply]; exact A.fl.z_orth i
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem Hom.of_nlam {T : E} {Λ : Submodule (𝓞 E) S.V} {n : S.V ≃ₗ[E] S.V} {A : LFlag S r T}
    (h : n ∈ NLam Λ A) : Hom n A A := by
  obtain ⟨-, h2, h3⟩ := h
  intro a
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_r]
    exact h3 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.val_castSucc]
    exact h2 i.1 _ (e_mem_xflag A i (Nat.lt_succ_self _))

theorem frame_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ A) a = γ (frame A a) := by
  induction a using Fin.lastCases with
  | last => simp [mapLF, hγ, frame_last, mapFlag]
  | cast i => simp [mapLF, hγ, frame_castSucc, mapFlag]

theorem Hom.of_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) :
    Hom γ A (mapLF γ A) := by
  intro a
  rw [frame_mapLF hγ, sub_self]
  exact Submodule.zero_mem _

theorem gmap_mul (φ ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (φ * ψ) Λ = Formalism.HermitianLatticesTheory.gmap φ (Formalism.HermitianLatticesTheory.gmap ψ Λ) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ψ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_inv {φ : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap φ Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap φ⁻¹ Λ = Λ := by
  conv_lhs => rw [← h]
  rw [← gmap_mul, inv_mul_cancel]
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.Unfold.TgTr

namespace GlobalTheory.Unfold


open GlobalTheory.Unfold.TgTr in
theorem tg_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ s : TauC Y u u') (Λ₀ : LV D) (a a' n n' : GV D), TG F F' t₀ Λ₀ → a ∈ Aut0 (lf D (X.Fu u)) t₀.lam → a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam' → n ∈ NLam t₀.lam (lf D (X.Fu u)) → n' ∈ NLam t₀.lam' (lf D (X.Fu u')) → s.lam = t₀.lam → s.lin = n * (a * t₀.lin * a'⁻¹) * n' → TG F F' s Λ₀ := by
  intro D X Y u u' F F' t₀ s Λ₀ a a' n n' hTG ha ha' hn hn' hsl hsg
  obtain ⟨g, hgL, hgt, hΛ⟩ := hTG
  obtain ⟨⟨haI, haH⟩, haΛ⟩ := ha
  obtain ⟨⟨ha'I, ha'H⟩, -⟩ := ha'
  have hnH : Hom n _ _ := Hom.of_nlam hn
  have hn'H : Hom n' _ _ := Hom.of_nlam hn'
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1.1
  have hnΛ : Formalism.HermitianLatticesTheory.gmap n t₀.lam = t₀.lam := hn.1.2
  have ht₀I : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hsI : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  refine ⟨g * a⁻¹ * n⁻¹, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · exact Hom.comp (Hom.comp (φ := g) hgL.2 (Hom.inv haH)) (Hom.inv hnH)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · have hK : Hom (g * t₀.lin * a'⁻¹ * n') (lf D (X.Fu u')) F' :=
      Hom.comp (Hom.comp (Hom.comp (φ := g) hgt.2 (Hom.of_mapLF ht₀I _)) (Hom.inv ha'H)) hn'H
    have heq : g * a⁻¹ * n⁻¹ * s.lin = g * t₀.lin * a'⁻¹ * n' := by
      rw [hsg]; group
    intro c
    have hf : frame s.frame c = s.lin (frame (lf D (X.Fu u')) c) := frame_mapLF hsI _ c
    rw [hf, ← LinearEquiv.mul_apply, heq]
    exact hK c
  · rw [hsl, gmap_mul, gmap_mul, gmap_inv hnΛ, gmap_inv haΛ, hΛ]

end GlobalTheory.Unfold
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem adapt_map_flag (D : D7) (T : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D) (hg : Adapt g F G) :
    (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧
      (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  have hmono : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) {a b : ℕ}, a ≤ b → Xflag H a ≤ Xflag H b := by
    intro H a b hab
    exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi hab : i.1 < b))
  have hmem : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) {j : ℕ}, i.1 < j → H.fl.e i ∈ Xflag H j := by
    intro H i j hij
    exact Submodule.subset_span ⟨i, hij, rfl⟩
  have hX : ∀ H : LFlag (D.sp.Y 0) D.R.rS T, Xsp H = Xflag H D.R.rS := by
    intro H
    show Submodule.span _ (Set.range H.fl.e) = Submodule.span _ (H.fl.e '' {i | i.1 < D.R.rS})
    congr 1
    ext x
    simp
  have hstep : ∀ i : Fin D.R.rS, g (F.fl.e i) - G.fl.e i ∈ Xflag G i.1 := by
    intro i
    have := hg.2 i.castSucc
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have hle : ∀ j, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
    intro j
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    show g (F.fl.e i) ∈ Xflag G j
    have h1 := hmono G (le_of_lt hi) (hstep i)
    have h2 := hmem G i hi
    simpa using add_mem h1 h2
  have hge : ∀ j, Xflag G j ≤ (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    induction j with
    | zero =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hmap : (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.map_mono (hmono F (Nat.le_succ j))
      have h1 : g (F.fl.e i) - G.fl.e i ∈ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        hmap (ih (hmono G hi' (hstep i)))
      have h2 : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) ∈
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.mem_map_of_mem (hmem F i hi)
      have h3 := sub_mem h2 h1
      simp only [LinearEquiv.coe_coe, sub_sub_cancel] at h3
      exact h3
  refine ⟨fun j => le_antisymm (hle j) (hge j), ?_⟩
  rw [hX F, hX G]
  exact le_antisymm (hle _) (hge _)

end GlobalTheory
end
end

section

open NumberField

namespace GlobalTheory.NatSmulMemOfSpan

theorem exists_nat_mul_eq_coe {K : Type*} [Field K] [NumberField K] (c : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (m : K) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y.natAbs : K) * c) := by
    have hc : (y.natAbs : K) = ((y.natAbs : ℤ) : K) := (Int.cast_natCast _).symm
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · rw [hc, ← h]; exact hint
    · have h2 : ((y.natAbs : ℤ) : K) = -(y : K) := by
        have : (y.natAbs : ℤ) = -y := by omega
        rw [this, Int.cast_neg]
      rw [hc, h2, neg_mul]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, ⟨_, hint'⟩, rfl⟩

theorem exists_nat_smul_mem_of_mem_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span K (Λ : Set V)) : ∃ n : ℕ, 0 < n ∧ (n : K) • v ∈ Λ := by
  have key : ∀ (a : 𝓞 K) (w : V), w ∈ Λ → algebraMap (𝓞 K) K a • w ∈ Λ := fun a w hw => by
    rw [algebraMap_smul]; exact Λ.smul_mem a hw
  have keyN : ∀ (m : ℕ) (w : V), w ∈ Λ → (m : K) • w ∈ Λ := fun m w hw => by
    simpa using key (m : 𝓞 K) w hw
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (x + y) = (n : K) • ((m : K) • x) + (m : K) • ((n : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (n : K)]
    rw [this]
    exact Λ.add_mem (keyN n _ hx) (keyN m _ hy)
  | smul c x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_coe c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (c • x) = algebraMap (𝓞 K) K a • ((n : K) • x) := by
      rw [ha, smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact key a _ hx

theorem exists_nat_smul_mem {D : Formalism.BasicNotions.D7} (Λ : GlobalTheory.Unfold.LV D)
    (hΛ : Submodule.IsFullLattice ((Formalism.BasicNotions.D7.host D).E) Λ)
    (v : Formalism.BasicNotions.HSpace.V (Formalism.MainNotions.S.VS D)) :
    ∃ n : ℕ, 0 < n ∧ (n : (Formalism.BasicNotions.D7.host D).E) • v ∈ Λ :=
  exists_nat_smul_mem_of_mem_span Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end GlobalTheory.NatSmulMemOfSpan
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitriangularFrameChange_from_linearAut : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) → (∃ N : G.GLV, ∀ b, N (G.f b) = ∑ a, B a b • G.f a) ∧ (∃ N : G.GLV, ∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) := by
  first | exact @GlobalTheory.HL.UniExt.main | exact GlobalTheory.HL.UniExt.main | (intros; apply GlobalTheory.HL.UniExt.main <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (N : G.GLV), ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f a.succ) i * G.Hm i j * sig (G.es a j)) = Formalism.L2.SG.PairVal.sgUp B) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) = Formalism.L2.SG.PairVal.sgUp B) := by
  first | exact @GlobalTheory.SlocCoef.main | exact GlobalTheory.SlocCoef.main | (intros; apply GlobalTheory.SlocCoef.main <;> assumption)
end
