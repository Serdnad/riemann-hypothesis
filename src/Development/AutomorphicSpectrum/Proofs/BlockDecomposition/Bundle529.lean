module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle503
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

@[expose] public section

section

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisJ

section Ring

variable {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_entry (d : Sˣ) (g : GL (ι ⊕ ι) S) (r c : ι ⊕ ι) :
    (((dg ι d)⁻¹ * g * dg ι d : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c =
      Sum.elim (fun _ => (1 : S)) (fun _ => ((d⁻¹ : Sˣ) : S)) r * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c *
        Sum.elim (fun _ => (1 : S)) (fun _ => (d : S)) c := by
  have h1 : (((dg ι d)⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) =
      Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => ((d⁻¹ : Sˣ) : S)) := rfl
  have h2 : ((dg ι d : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) =
      Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => (d : S)) := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_stab_line {i : ι} (hi : ∀ x, x = i) (s : Set (ι ⊕ ι)) (hs : s = {Sum.inl i}) (g : GL (ι ⊕ ι) S) :
    g ∈ stab S s ↔ (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (Sum.inr i) (Sum.inl i) = 0 ∧
      ((g⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (Sum.inr i) (Sum.inl i) = 0 := by
  subst hs
  have e : g ∈ stab S ({Sum.inl i} : Set (ι ⊕ ι)) ↔ ∀ r ∉ ({Sum.inl i} : Set (ι ⊕ ι)), ∀ c ∈ ({Sum.inl i} : Set (ι ⊕ ι)),
      (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c = 0 ∧ ((g⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c = 0 := Iff.rfl
  rw [e]
  constructor
  · intro h
    exact h _ (by simp) _ rfl
  · rintro h r hr c hc
    obtain rfl : c = Sum.inl i := hc
    rcases r with y | y
    · exact absurd (by rw [hi y]; rfl) hr
    · rw [hi y]; exact h

theorem det_tri {i : ι} (hi : ∀ x, x = i) (h : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (h0 : h (Sum.inr i) (Sum.inl i) = 0) :
    h.det = h (Sum.inl i) (Sum.inl i) * h (Sum.inr i) (Sum.inr i) := by
  haveI : Unique ι := ⟨⟨i⟩, hi⟩
  have e : h = Matrix.fromBlocks h.toBlocks₁₁ h.toBlocks₁₂ 0 h.toBlocks₂₂ := by
    ext r c
    rcases r with y | y <;> rcases c with z | z
    · rfl
    · rfl
    · rw [hi y, hi z]; simpa using h0
    · rfl
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_unique]
  have hd : (default : ι) = i := hi _
  simp [hd, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem bdet_val {κ : Type} [Fintype κ] [DecidableEq κ] (s : Set κ) (c : κ) (hs : s = {c}) (g : GL κ S)
    (hu : IsUnit ((g : Matrix κ κ S) c c)) : ((bdet s g : Sˣ) : S) = (g : Matrix κ κ S) c c := by
  subst hs
  have e : ∀ (f : Fintype ↥({c} : Set κ)) (dq : DecidableEq ↥({c} : Set κ)),
      @Matrix.det _ dq f S _ ((g : Matrix κ κ S).submatrix (Subtype.val : ({c} : Set κ) → κ) Subtype.val) =
        (g : Matrix κ κ S) c c := by
    intro f dq
    exact Matrix.det_eq_elem_of_subsingleton _ (⟨c, rfl⟩ : ({c} : Set κ))
  unfold bdet
  split_ifs with h
  · exact h.unit_spec.trans (e _ _)
  · exact absurd (by rw [e]; exact hu) h

end Ring

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R]
  {A : Ad E R} {ν : 𝔸[F] →+* R} {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ℤˣ}

theorem j_entry {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (x : cover A ν ι) (r c : ι ⊕ ι) :
    (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) r c = (x.1.1 : R) *
      (Sum.elim (fun _ => (1 : R)) (fun _ => (((Units.map A.i.toMonoidHom δ)⁻¹ : Rˣ) : R)) r *
        ν ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) r c) *
        Sum.elim (fun _ => (1 : R)) (fun _ => ((Units.map A.i.toMonoidHom δ : Rˣ) : R)) c) := by
  rw [hJ x, Matrix.smul_apply, smul_eq_mul, conj_entry]
  rfl

theorem j_low {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (hν : Function.Injective ν) (x : cover A ν ι)
    (i : ι) : (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl i) = 0 ↔
      (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inr i) (Sum.inl i) = 0 := by
  rw [j_entry hJ x, Sum.elim_inr, Sum.elim_inl, mul_one, Units.mul_right_eq_zero, Units.mul_right_eq_zero,
    map_eq_zero_iff ν hν]

theorem image_univ {i : ι} (hi : ∀ x, x = i) : (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) = {Sum.inl i} := by
  ext y
  constructor
  · rintro ⟨z, -, rfl⟩
    rw [hi z]; rfl
  · intro h
    obtain rfl : y = Sum.inl i := h
    exact ⟨i, trivial, rfl⟩

theorem compl_inr {i : ι} (hi : ∀ x, x = i) : ({Sum.inr i}ᶜ : Set (ι ⊕ ι)) = {Sum.inl i} := by
  ext y
  rcases y with y | y
  · rw [hi y]; simp
  · rw [hi y]; simp

theorem comap_uQ {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (hν : Function.Injective ν) {i : ι}
    (hi : ∀ x, x = i) :
    (A.uQ ε Set.univ).comap j = (stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι) := by
  ext x
  have e1 : x ∈ (A.uQ ε Set.univ).comap j ↔ (j x).1 ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := Iff.rfl
  have e2 : x ∈ (stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι) ↔ x.1.2 ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι)) := Iff.rfl
  have e3 : ((j x).1)⁻¹ = (j x⁻¹).1 := by rw [map_inv]; rfl
  have e4 : (x.1.2)⁻¹ = (x⁻¹).1.2 := rfl
  rw [e1, e2, mem_stab_line hi _ (image_univ hi), mem_stab_line hi _ rfl, e3, e4, j_low hJ hν, j_low hJ hν]

theorem blocks {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) {i : ι} (hi : ∀ x, x = i) (x : cover A ν ι)
    (hx : prj A ν ι x ∈ stab 𝔸[F] {Sum.inl i}) :
    bdet (Sum.inl '' (Set.univ : Set ι)) (j x).1 = x.1.1 * Units.map ν.toMonoidHom (bdet {Sum.inl i} (prj A ν ι x)) ∧
    Matrix.GeneralLinearGroup.det (prj A ν ι x) = bdet {Sum.inl i} (prj A ν ι x) * bdet {Sum.inr i} (prj A ν ι x) := by
  have hp : ((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = x.1.2 := rfl
  have h0 := ((mem_stab_line hi _ rfl _).1 hx).1
  have hdet := det_tri hi _ h0
  have hu : IsUnit (((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inl i) (Sum.inl i) *
      ((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inr i) (Sum.inr i)) := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (prj A ν ι x).isUnit
  have h1 := isUnit_of_mul_isUnit_left hu
  have h2 := isUnit_of_mul_isUnit_right hu
  have b1 := bdet_val _ _ rfl _ h1
  have b2 := bdet_val _ _ rfl _ h2
  have he := j_entry hJ x (Sum.inl i) (Sum.inl i)
  rw [Sum.elim_inl, Sum.elim_inl, one_mul, mul_one] at he
  have hju : IsUnit ((((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)) := by
    rw [he]
    exact x.1.1.isUnit.mul (h1.map ν)
  refine ⟨Units.ext ?_, Units.ext ?_⟩
  · rw [bdet_val _ (Sum.inl i) (image_univ hi) _ hju, he, Units.val_mul]
    congr 1
    exact (congrArg ν b1).symm
  · rw [Units.val_mul, b1, b2, ← hdet]
    rfl

theorem jPar : JPar := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j _ hB hi hJ
  exact ⟨by rw [compl_inr hi], comap_uQ hJ hB.inj hi, fun x hx => blocks hJ hi x hx⟩

end GlobalTheory.CompanionTheory.EisJ
end
end

section

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo.JIwaAd

section Dg

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem dg_mem_stab (s : Set (ι ⊕ ι)) (x : Rˣ) : dg ι x ∈ stab R s := by
  intro r hr c hc
  have hne : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hne⟩

theorem det_dg {i : ι} (hi : ∀ y, y = i) (x : Rˣ) : Matrix.GeneralLinearGroup.det (dg ι x) = x := by
  haveI : Unique ι := ⟨⟨i⟩, hi⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal _).det = _
  rw [Matrix.det_diagonal, Fintype.prod_sum_type]
  simp

theorem map_dg {S : Type} [CommRing S] (f : R →+* S) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (dg ι x) = dg ι (Units.map f.toMonoidHom x) := by
  apply Units.ext
  show (Matrix.diagonal _).map f = Matrix.diagonal _
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext a
  cases a <;> simp

theorem dg_mul (x y : Rˣ) : dg ι (x * y) = dg ι x * dg ι y := by
  apply Units.ext
  show Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  cases a <;> simp

end Dg

section Ad

variable {E R : Type} [Field E] [CommRing R] (A : Ad E R)

theorem dg_mem_kGL {ι : Type} [Fintype ι] [DecidableEq ι] (x : Rˣ) (h1 : (x : R) ∈ A.O)
    (h2 : ((x⁻¹ : Rˣ) : R) ∈ A.O) (h3 : ∀ w, ‖A.φ w x‖ = 1) : dg ι x ∈ A.kGL (ι ⊕ ι) := by
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · show Matrix.diagonal _ r c ∈ A.O
    by_cases h : r = c
    · subst h
      rw [Matrix.diagonal_apply_eq]
      cases r <;> simp [h1, A.O.one_mem]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact A.O.zero_mem
  · show Matrix.diagonal _ r c ∈ A.O
    by_cases h : r = c
    · subst h
      rw [Matrix.diagonal_apply_eq]
      cases r <;> simp [h2, A.O.one_mem]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact A.O.zero_mem
  · show (Matrix.diagonal _).map (A.φ w) ∈ Matrix.unitaryGroup _ ℂ
    rw [Matrix.diagonal_map (map_zero _), Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    cases a with
    | inl a => simp
    | inr a =>
      simp only [Function.comp, Sum.elim_inr, Pi.star_apply, RCLike.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, h3 w]
      simp

variable {n : Type} [Fintype n] [DecidableEq n]

theorem det_mem_O {M : Matrix n n R} (h : ∀ r c, M r c ∈ A.O) : M.det ∈ A.O := by
  rw [Matrix.det_apply']
  exact A.O.sum_mem fun s _ => A.O.mul_mem (intCast_mem _ _) (A.O.prod_mem fun m _ => h _ _)

theorem det_kGL {k : GL n R} (hk : k ∈ A.kGL n) :
    ((Matrix.GeneralLinearGroup.det k : Rˣ) : R) ∈ A.O ∧
      (((Matrix.GeneralLinearGroup.det k)⁻¹ : Rˣ) : R) ∈ A.O ∧
      ∀ w, ‖A.φ w (Matrix.GeneralLinearGroup.det k : Rˣ)‖ = 1 := by
  refine ⟨?_, ?_, fun w => ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_O A fun r c => (hk.1 r c).1
  · rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_O A fun r c => (hk.1 r c).2
  · have h := Matrix.det_of_mem_unitary (hk.2 w)
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    have h' : star (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det * (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det = 1 :=
      Unitary.star_mul_self_of_mem h
    have h2 : ‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ ^ 2 = 1 := by
      have := congrArg norm h'
      simpa [sq] using this
    nlinarith [norm_nonneg (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det, sq_nonneg (‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ - 1)]

end Ad

section Main

open GroundTheory.Global

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R] [TopologicalSpace R]

theorem map_mem_kGL {A : Ad E R} {ε : ℤˣ} {ν : 𝔸[F] →+* R} {r : R → 𝔸[F]} {δ : Eˣ} {α : IdeleGroup F}
    {ω : HeckeCharacter F} (hB : Base A ε ν r δ α ω) {n : Type} [Fintype n] [DecidableEq n]
    {k : GL n 𝔸[F]} (hk : k ∈ (adStd F).kGL n) : Matrix.GeneralLinearGroup.map ν k ∈ A.kGL n := by
  refine ⟨fun a b => ⟨(hB.int _).2 (hk.1 a b).1, ?_⟩, fun w => ?_⟩
  · rw [← map_inv]
    exact (hB.int _).2 (hk.1 a b).2
  · obtain ⟨v, hv⟩ := hB.inf w
    have e : ((Matrix.GeneralLinearGroup.map ν k : GL n R) : Matrix n n R).map (A.φ w) =
        (k : Matrix n n 𝔸[F]).map ((adStd F).φ v) := by
      ext a b
      simp [hv]
    rw [e]
    exact hk.2 v

theorem jiwa : StdGood → JIwa := by
  intro hS F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hB hi hJ x
  obtain ⟨b, hb, κ, hκ, hbk⟩ := (hS F).iwa (ι ⊕ ι) {Sum.inl i} ((dg ι α)⁻¹ * x.1.2 * dg ι α)
  obtain ⟨c1, c2, c3⟩ := det_kGL (adStd F) hκ
  set c := Matrix.GeneralLinearGroup.det κ with hc
  have ht : dg ι c ∈ (adStd F).kGL (ι ⊕ ι) := dg_mem_kGL _ c c1 c2 c3
  set κ' : GL (ι ⊕ ι) 𝔸[F] := (dg ι c)⁻¹ * κ with hκ'
  have hκ'K : κ' ∈ (adStd F).kGL (ι ⊕ ι) := mul_mem (inv_mem ht) hκ
  have hdet : Matrix.GeneralLinearGroup.det κ' = 1 := by
    rw [hκ', map_mul, map_inv, det_dg hi, ← hc, inv_mul_cancel]
  set d : GL (ι ⊕ ι) 𝔸[F] := dg ι α with hd
  have hdet2 : Matrix.GeneralLinearGroup.det (d * κ' * d⁻¹) = 1 := by
    simp [map_mul, hdet, mul_comm]
  have hkc : ((1 : Rˣ), d * κ' * d⁻¹) ∈ cover A ν ι := by
    simp [cover, MonoidHom.mem_ker, hdet2]
  let k : cover A ν ι := ⟨_, hkc⟩
  have hjk : (j k).1 ∈ A.kGL (ι ⊕ ι) := by
    obtain ⟨u, hu, u1, u2, u3⟩ := hB.δα
    have hδ : Units.map A.i.toMonoidHom δ = Units.map ν.toMonoidHom α * u := Units.ext hu
    have e : (j k).1 = (dg ι (Units.map A.i.toMonoidHom δ))⁻¹ * Matrix.GeneralLinearGroup.map ν k.1.2 *
        dg ι (Units.map A.i.toMonoidHom δ) := by
      apply Units.ext
      rw [hJ k]
      show ((1 : Rˣ) : R) • _ = _
      rw [Units.val_one, one_smul]
    have e2 : (j k).1 = (dg ι u)⁻¹ * Matrix.GeneralLinearGroup.map ν κ' * dg ι u := by
      have hD : dg ι (Units.map ν.toMonoidHom α) = Matrix.GeneralLinearGroup.map ν d := (map_dg ν α).symm
      have hk2 : Matrix.GeneralLinearGroup.map ν k.1.2 = Matrix.GeneralLinearGroup.map ν d *
          Matrix.GeneralLinearGroup.map ν κ' * (Matrix.GeneralLinearGroup.map ν d)⁻¹ := by
        show Matrix.GeneralLinearGroup.map ν (d * κ' * d⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [e, hδ, dg_mul, hD, hk2]
      generalize Matrix.GeneralLinearGroup.map ν d = P
      generalize Matrix.GeneralLinearGroup.map ν κ' = Q
      generalize dg ι u = T
      group
    rw [e2]
    have hU : dg ι u ∈ A.kGL (ι ⊕ ι) := dg_mem_kGL A u u1 u2 u3
    exact mul_mem (mul_mem (inv_mem hU) (map_mem_kGL hB hκ'K)) hU
  have hkK : k ∈ cK α j := by
    refine ⟨hjk, ?_⟩
    exact ⟨κ', hκ'K, rfl⟩
  refine ⟨x * k⁻¹, ?_, k, hkK, by simp⟩
  have hx : x.1.2 = d * (b * κ) * d⁻¹ := by
    rw [← hbk]
    group
  have hp : prj A ν ι (x * k⁻¹) = d * (b * dg ι c) * d⁻¹ := by
    rw [map_mul, map_inv]
    show x.1.2 * (d * κ' * d⁻¹)⁻¹ = _
    rw [hx, hκ']
    group
  show prj A ν ι (x * k⁻¹) ∈ stab 𝔸[F] {Sum.inl i}
  rw [hp]
  have hdS : d ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι)) := dg_mem_stab _ _
  exact mul_mem (mul_mem hdS (mul_mem hb (dg_mem_stab _ _))) (inv_mem hdS)

end Main

end GlobalTheory.CompanionTheory.RgEisSo.JIwaAd
end
end

section

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.RgEisBInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_below_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : HeightOneSpectrum (𝓞 E), below F w = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (hker.le.trans bot_le)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact hker
  exact ⟨⟨Q, hQ, hne⟩, HeightOneSpectrum.ext hQv⟩

theorem adeleMap_mem_intAd_iff (x : 𝔸[F]) : adeleMap F E x ∈ intAd E ↔ x ∈ intAd F := by
  have key : ∀ w : HeightOneSpectrum (𝓞 E),
      finEval w (adeleMap F E x) ∈ w.adicCompletionIntegers E ↔
        finEval (below F w) x ∈ (below F w).adicCompletionIntegers F := by
    intro w
    haveI := liesOver_below (K := F) w
    haveI := w.isPrime
    have h1 : finEval w (adeleMap F E x) =
        SemiLocal.completionMap (below F w) w (finEval (below F w) x) :=
      finiteAdeleMap_apply x.2 w
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      SemiLocal.valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  constructor
  · intro h v
    obtain ⟨w, rfl⟩ := exists_below_eq (E := E) v
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 (h _)

theorem nuCM_eqv (x : 𝔸[F]) : eqv F E (nuCM F E x) = adeleMap F E x := by
  have h := (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).commutes x
  exact h

theorem bInt : BInt := by
  unfold BInt ForCM
  intro F E _ _ _ _ _ σ χ c _ _ _ _ x
  simp only [adCM, Subring.mem_comap]
  change eqv F E (nuCM F E x) ∈ intAd E ↔ _
  rw [nuCM_eqv, adeleMap_mem_intAd_iff]

end GlobalTheory.CompanionTheory.RgEisBInt
end

section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.SgOneBase

theorem baseCM : CMGood → BFix → BRat → BInt → BInf → BLg → BDel → BaseCM := by
  intro _ hFix hRat hInt hInf hLg hDel F E _ _ _ _ _ σ χ c hCM hUn hHk hRes ε
  obtain ⟨hνc, hνi, hνfix, r, hrc, hrfix⟩ := hFix F E σ χ c hCM hUn hHk hRes
  obtain ⟨hrat, hrat'⟩ := hRat F E σ χ c hCM hUn hHk hRes
  have hint := hInt F E σ χ c hCM hUn hHk hRes
  obtain ⟨hinf, hinf'⟩ := hInf F E σ χ c hCM hUn hHk hRes
  obtain ⟨hlg, hlgσ⟩ := hLg F E σ χ c hCM hUn hHk hRes
  obtain ⟨δ0, α0, u0, hσδ, hδα, huO, huiO, hun⟩ := hDel F E σ χ c hCM hUn hHk hRes
  have hσi : ∀ x : E, (adCM σ χ).σ ((adCM σ χ).i x) = (adCM σ χ).i (σ x) := by
    intro x
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x)
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  let f : IdeleGroup F →* Circle := χ.comp (Units.map (nuCM F E).toMonoidHom)
  have hker : (IdeleGroup.diagonal F).range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    have e : Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a) =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* TensorProduct F (AF F) E) (Units.map (algebraMap F E : F →* E) a) :=
      Units.ext (hrat a)
    show χ (Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a)) = 1
    rw [e]
    exact hHk.2 _
  have hfc : Continuous f := hHk.1.comp (Continuous.units_map _ hνc)
  let ω : HeckeCharacter F :=
    ⟨QuotientGroup.lift _ f hker, (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hfc⟩
  have hω : ∀ x : IdeleGroup F, ω.toIdele x = (adCM σ χ).χ (Units.map (nuCM F E).toMonoidHom x) := fun x => rfl
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨r, δ0, α0, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨u0, hδα, huO, huiO, hun⟩, hω⟩⟩
    rw [hσi, hσδ, map_neg]
    simp
  · refine ⟨r, 1, 1, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨1, ?_, ?_, ?_, ?_⟩, hω⟩⟩
    · simp
    · simp
    · simpa using (adCM σ χ).O.one_mem
    · simpa using (adCM σ χ).O.one_mem
    · intro w
      simp

end GlobalTheory.CompanionTheory.SgOneBase
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.fourier_jacobi_coefficient_of_bound : PcBound → CfFJ := by
  first | exact @GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | exact GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | (intros; apply GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound <;> assumption)
end
