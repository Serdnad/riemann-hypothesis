module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FrameAct

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

abbrev Xs (h : Fin (r + 1) → S.V) : Submodule E S.V :=
  Submodule.span E (Set.range fun a : Fin r => h a.castSucc)

theorem frameAct_castSucc_mem (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hξ : ∀ a b, b < a → ξ a b = 0) (a : Fin r) : frameAct h ξ a.castSucc ∈ Xs h := by
  show ∑ c, ((ξ c a.castSucc : 𝓞 E) : E) • h c ∈ _
  have h0 : ((ξ (Fin.last r) a.castSucc : 𝓞 E) : E) = 0 := by
    rw [hξ _ _ (Fin.castSucc_lt_last a)]
    rfl
  rw [Fin.sum_univ_castSucc, h0, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_last_sub (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hl : ξ (Fin.last r) (Fin.last r) = 1) : frameAct h ξ (Fin.last r) - h (Fin.last r) ∈ Xs h := by
  show ∑ c, ((ξ c (Fin.last r) : 𝓞 E) : E) • h c - h (Fin.last r) ∈ _
  have h1 : ((ξ (Fin.last r) (Fin.last r) : 𝓞 E) : E) = 1 := by
    rw [hl]
    rfl
  rw [Fin.sum_univ_castSucc, h1, one_smul, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_mem_span (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : frameAct h ξ b ∈ Submodule.span E (Set.range h) :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem frameAct_frameAct (h : Fin (r + 1) → S.V) (ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    frameAct (frameAct h ξ) ξ' = frameAct h (ξ * ξ') := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem frameAct_one (h : Fin (r + 1) → S.V) : frameAct h 1 = h := by
  funext b
  simp only [frameAct, Matrix.one_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [hc]
  · intro hb; exact absurd (Finset.mem_univ b) hb

theorem det_unitri {n : ℕ} {R : Type*} [CommRing R] (ξ : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : ξ.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
  simp [h2]

theorem frameAct_inv_back (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : frameAct (frameAct h ξ⁻¹) ξ = h := by
  rw [frameAct_frameAct, Matrix.nonsing_inv_mul _ (by rw [det_unitri ξ h1 h2]; exact isUnit_one),
    frameAct_one]

theorem Xs_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : Xs (frameAct h ξ⁻¹) = Xs h := by
  have hi := inv_unitri ξ h1 h2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_castSucc_mem h _ hi.1 a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_castSucc_mem (frameAct h ξ⁻¹) ξ h1 a
    rwa [frameAct_inv_back h ξ h1 h2] at this

theorem span_frameAct_inv (h : Fin (r + 1) → S.V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span E (Set.range (frameAct h ξ⁻¹)) = Submodule.span E (Set.range h) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact frameAct_mem_span h _ a
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := frameAct_mem_span (frameAct h ξ⁻¹) ξ a
    rwa [frameAct_inv_back h ξ h1 h2] at this

end FrameAct

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GZ

variable {D : D7}

theorem unitri_map (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    (∀ a b, b < a → η.map (fun x => (x : D.host.E)) a b = 0) ∧ (∀ a, η.map (fun x => (x : D.host.E)) a a = 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.map_apply, h1 a b hab]; rfl
  · rw [Matrix.map_apply, h2 a]; rfl

theorem GZ_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V) (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    GZ u (frameAct h η) = GZ u h * η.map (fun x => (x : D.host.E)) := by
  ext a b

  simp only [GZ, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, frameAct, brS, map_sum, map_smul,
  smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem GDl_frameAct_top (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) (D.R.rS + 1) = GDl u h (D.R.rS + 1) := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dite_eq_left le_rfl, dite_eq_left le_rfl]
  have e : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      M.submatrix (Fin.castLE (le_refl _)) (Fin.castLE (le_refl _)) = M := fun M => by ext i j; rfl
  rw [e, e, GZ_frameAct, Matrix.det_mul, det_unitri _ hm.1 hm.2, mul_one]

theorem GDl_frameAct_r (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    GDl u (frameAct h η) D.R.rS = GDl u h D.R.rS := by
  have hm := unitri_map η h1 h2
  unfold GDl
  rw [dite_eq_left (Nat.le_succ _), dite_eq_left (Nat.le_succ _), GZ_frameAct]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]
  have e : (GZ u h * η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc =
      (GZ u h).submatrix Fin.castSucc Fin.castSucc *
      (η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      hm.1 _ _ (Fin.castSucc_lt_last j), mul_zero, add_zero]
    rfl
  rw [e, Matrix.det_mul, det_unitri ((η.map (fun x => (x : D.host.E))).submatrix Fin.castSucc Fin.castSucc)
    (fun a b hab => hm.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab)) (fun a => hm.2 _), mul_one]

theorem Gom'_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom' u (frameAct h η) = Gom' u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hkey : ηE * (ηE.adjugate * (GZ u h).adjugate) = (GZ u h).adjugate := by
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, det_unitri _ hm.1 hm.2, one_smul, Matrix.one_mul]
  unfold Gom'
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  simp only [frameAct, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrFun (congrFun hkey c) (Fin.last _)
  rw [Matrix.mul_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem Gom_frameAct (u h : Fin (D.R.rS + 1) → (VS D).V)
    (η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → η a b = 0) (h2 : ∀ a, η a a = 1) :
    Gom u (frameAct h η) = Gom u h := by
  have hm := unitri_map η h1 h2
  set ηE := η.map (fun x => (x : D.host.E)) with hηE
  have hadj : ηE.adjugate = ηE⁻¹ := by
    rw [Matrix.inv_def, det_unitri _ hm.1 hm.2, Ring.inverse_one, one_smul]
  have hinv := inv_unitri ηE hm.1 hm.2
  unfold Gom
  rw [GZ_frameAct, Matrix.adjugate_mul_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last _), hadj, hinv.2, one_mul]
  · intro k _ hk
    rw [hadj, hinv.1 _ _ (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end GZ

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : D7} (Z : LocDat D) (p : PlF D)

def lt (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g : Fin (D.R.rS + 1) → (VS D).V) (Tn T'n : ℕ) :
    Loc.Term (Vp D p) (Z.M p) D.R.rS where
  abelian₂ := lattice₂ D Z.M p Λ
  f a := sF Z p a • baseChange₂ D p (f a)
  f' b := sF' Z p b • baseChange₂ D p (g b)
  T := (Tn : (D.s.atP p).Fp)
  T' := (T'n : (D.s.atP p).Fp)

structure GFacts (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop where
  iso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y
  lam : ∀ v ∈ Λ, β v ∈ Λ
  lam' : ∀ v ∈ Λ, β.symm v ∈ Λ
  xmap : ∀ a : Fin D.R.rS, β (g1 a.castSucc) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  xmap' : ∀ a : Fin D.R.rS, β.symm (g2 a.castSucc) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g1 b.castSucc)
  zmap : β (g1 (Fin.last _)) - g2 (Fin.last _) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  fiso : ∀ a b : Fin D.R.rS, (VS D).hT (f a.castSucc) (f b.castSucc) = 0
  g2iso : ∀ a b : Fin D.R.rS, (VS D).hT (g2 a.castSucc) (g2 b.castSucc) = 0
  proj : ∀ y, ∃ u ∈ Submodule.span D.host.E (Set.range (Sum.elim f g1)),
    ∀ i, (VS D).hT (Sum.elim f g1 i) (y - u) = 0
  gram : (Matrix.of fun i k => brS (VS D) (Sum.elim f g1 i) (Sum.elim f g1 k)).det ≠ 0
  theta : ∀ x1, (∀ i, (VS D).hT (Sum.elim f g1 i) x1 = 0) → ∃ x2, (∀ i, (VS D).hT (Sum.elim f g2 i) x2 = 0) ∧
    x1 - x2 ∈ Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc) ∧
    β x1 - x2 ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  ratio : GDl f g1 D.R.rS * GDl f g2 (D.R.rS + 1) = GDl f g2 D.R.rS * GDl f g1 (D.R.rS + 1)
  omp : GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2 ∈
    Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc)
  om : star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) - star (GDl f g1 (D.R.rS + 1)) • Gom f g2 ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)

theorem hermitian_base_change_smul (a : (D.s.atP p).Ep) (x y : (VS D).V) :
    (locH Z p).h (a • baseChange₂ D p x) (baseChange₂ D p y) = a * (D.s.atP p).ιE (brS (VS D) x y) := by
  have := h_bcP Z p a 1 x y
  rwa [one_smul, map_one, mul_one] at this

theorem h_zero_of_smul {c : (D.s.atP p).Ep} (hc : IsUnit c) {w y : Vp D p}
    (h : (locH Z p).h w (c • y) = 0) : (locH Z p).h w y = 0 := by
  rw [h_smul_right] at h
  exact (hc.map (Z.M p).L.cj).mul_right_eq_zero.1 h

theorem baseChange_mem_span {ι : Type} (v : ι → (VS D).V) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range v)) :
    baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range fun i => baseChange₂ D p (v i)) := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul e x _ hx => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem mem_orthogonal_frame_iff (u v : Fin (D.R.rS + 1) → Vp D p) (w : Vp D p) :
    w ∈ (locH Z p).W0 u v ↔ (∀ a, (locH Z p).h w (u a) = 0) ∧ ∀ b, (locH Z p).h w (v b) = 0 := by
  unfold Loc.HermSp.W0 Loc.HermSp.Xp
  rw [← Submodule.span_union, mem_perp_span]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), fun b => h _ (Or.inr ⟨b, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact h1 a
    · exact h2 b

theorem scalar_frame_w_zero_exists (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hG : GFacts Λ f g1 g2 β) {w : Vp D p}
    (hw : w ∈ (locH Z p).W0 (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g1 b))) :
    ∃ w₂ ∈ (locH Z p).W0 (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g2 b)),
      w - w₂ ∈ (locH Z p).X (fun a => sF Z p a • baseChange₂ D p (f a)) ∧
      betaP p β w - w₂ ∈ (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2 b)) := by
  rw [mem_orthogonal_frame_iff] at hw
  have hperp : ∀ i, (locH Z p).h w (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    rintro (a | b)
    · exact h_zero_of_smul Z p (isUnit_sF Z p a) (hw.1 a)
    · exact h_zero_of_smul Z p (isUnit_sF' Z p b) (hw.2 b)
  choose u hu hpu using fun j => hG.proj ((VS D).frame j)

  set U : Vp D p := ∑ j, w j • baseChange₂ D p (u j) with hU
  set Hh : Vp D p := ∑ j, w j • baseChange₂ D p ((VS D).frame j - u j) with hHh
  have hw_eq : w = U + Hh := by
    conv_lhs => rw [vp_eq_sum p w]
    rw [hU, hHh, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add, ← map_add (f := _), add_sub_cancel]
  have hHperp : ∀ i, (locH Z p).h Hh (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    intro i
    rw [hHh, h_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hermitian_base_change_smul, brS, hpu j i, map_zero, mul_zero]
  have hUperp : ∀ i, (locH Z p).h U (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    intro i
    have e : U = w - Hh := by rw [hw_eq]; abel
    rw [e, h_sub_left, hperp i, hHperp i, sub_zero]
  have hUspan : U ∈ Submodule.span (D.s.atP p).Ep (Set.range fun i => baseChange₂ D p (Sum.elim f g1 i)) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (baseChange_mem_span p _ (hu j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hUspan
  have hU0 : U = 0 := by
    set G0 := Matrix.of fun i k => brS (VS D) (Sum.elim f g1 i) (Sum.elim f g1 k) with hG0
    have hvm : Matrix.vecMul c ((D.s.atP p).ιE.mapMatrix G0) = 0 := by
      funext k
      have := hUperp k
      rw [← hc, h_sum_left] at this
      simp only [hermitian_base_change_smul] at this
      simpa [Matrix.vecMul, dotProduct, hG0] using this
    have hdet : IsUnit ((D.s.atP p).ιE.mapMatrix G0).det := by
      rw [← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 hG.gram).map _
    have hc0 : c = 0 := by
      have h1 := congrArg (fun v => Matrix.vecMul v ((D.s.atP p).ιE.mapMatrix G0)⁻¹) hvm
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] at h1
      exact h1
    rw [← hc, hc0]
    simp
  have hw' : w = Hh := by rw [hw_eq, hU0, zero_add]
  have hperp1 : ∀ j, ∀ i, (VS D).hT (Sum.elim f g1 i) ((VS D).frame j - u j) = 0 := fun j i => hpu j i
  choose x2 hx2 using fun j => hG.theta ((VS D).frame j - u j) (hperp1 j)
  refine ⟨∑ j, w j • baseChange₂ D p (x2 j), ?_, ?_, ?_⟩
  · rw [mem_orthogonal_frame_iff]
    constructor
    · intro a
      rw [h_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h_bcP, brS, show (VS D).hT (f a) (x2 j) = 0 from (hx2 j).1 (Sum.inl a), map_zero, mul_zero]
    · intro b
      rw [h_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h_bcP, brS, show (VS D).hT (g2 b) (x2 j) = 0 from (hx2 j).1 (Sum.inr b), map_zero, mul_zero]
  · have e : w - ∑ j, w j • baseChange₂ D p (x2 j) = ∑ j, w j • baseChange₂ D p ((VS D).frame j - u j - x2 j) := by
      nth_rewrite 1 [hw']
      rw [hHh, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_sub, ← map_sub]
    rw [e]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bcP_mem_X Z p f (sF Z p) (isUnit_sF Z p) (hx2 j).2.1)
  · have e : betaP p β w - ∑ j, w j • baseChange₂ D p (x2 j) =
        ∑ j, w j • baseChange₂ D p (β ((VS D).frame j - u j) - x2 j) := by
      nth_rewrite 1 [hw']

      rw [hHh, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, betaP_bc, ← smul_sub, ← map_sub]
    rw [e]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) (hx2 j).2.2)

end Assembly

end Formalism.L2.SG.Pf.ScalarFramePf
end
end
