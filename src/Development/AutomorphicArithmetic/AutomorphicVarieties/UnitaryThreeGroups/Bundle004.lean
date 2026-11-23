module

public import Aesop.BuiltinRules
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Std.Tactic.BVDecide.Normalize.Bool
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle002
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

def form6 (O : Type) [CommRing O] : FormData O wt6 where
  J := Matrix.fromBlocks 0 (Jmat O 3) (Jmat O 3) 0
  unit := IsUnit.of_mul_eq_one (Matrix.fromBlocks 0 (Jmat O 3) (Jmat O 3) 0) (by
    simp [Matrix.fromBlocks_multiply, Jmat_mul_Jmat])
  sym := Or.inl (by simp [Matrix.fromBlocks_transpose, Jmat_transpose])
  κ := Bool
  blk := Sum.isLeft
  σ := not
  invol := Bool.not_not
  hblk a b h := by
    rcases a with a | a <;> rcases b with b | b <;> simp at h ⊢
  c := 0
  hw a b h := by
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [Jmat] at h <;> first | rfl | exact absurd rfl h

theorem blockPairingForm_JR (O R : Type) [CommRing O] [CommRing R] [Algebra O R] :
    (form6 O).JR R = Matrix.fromBlocks 0 (Jmat R 3) (Jmat R 3) 0 := by
  simp [FormData.JR, form6, Matrix.fromBlocks_map, Jmat_map]

theorem emb_apply {m : ℕ} {R : Type*} [CommRing R] (x : GG (m := m) (R := R)) :
    emb x = if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : GL (Fin m) R)
      else Matrix.fromBlocks 0 x.mat (theta x.left : GL (Fin m) R) 0 := rfl

theorem emb_map' {m : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : GG (m := m) (R := R)) :
    emb (GG.map f x) = (emb x).map f := by
  have h : (theta (GG.map f x).left : Matrix (Fin m) (Fin m) S) = (theta x.left : Matrix (Fin m) (Fin m) R).map f :=
    (congrArg Units.val (map_theta f x.left)).symm
  rw [emb_apply, emb_apply, h, GG.map_mat, GG.map_right]
  split_ifs <;> simp [Matrix.fromBlocks_map]

theorem mat_eq_emb' {m : ℕ} {R : Type*} [CommRing R] (x : GG (m := m) (R := R)) (a b : Fin m) :
    x.mat a b = emb x (.inl a) (.inl b) + emb x (.inl a) (.inr b) := by
  rw [emb_apply]
  split_ifs <;> simp

theorem eq_of_emb {m : ℕ} {R : Type*} [CommRing R] {x y : GG (m := m) (R := R)}
    (h : x.right = y.right) (e : emb x = emb y) :
    x = y := by
  refine SemidirectProduct.ext (Units.ext ?_) h
  ext a b
  exact (mat_eq_emb' x a b).trans (e ▸ (mat_eq_emb' y a b).symm)

theorem emb_form (O : Type) [CommRing O] {R : Type} [CommRing R] [Algebra O R] (x : GG (m := 3) (R := R)) :
    (emb x)ᵀ * (form6 O).JR R * emb x = (form6 O).JR R := by
  have h1 : x.matᵀ * Jmat R 3 * (theta x.left : GL (Fin 3) R) = Jmat R 3 := by
    rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R 3) (Jmat R 3), Jmat_mul_Jmat,
      Matrix.mul_one, GG.mat, ← Matrix.transpose_mul]
    simp
  have h2 : ((theta x.left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 * x.mat = Jmat R 3 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Jmat_transpose,
      ← Matrix.mul_assoc] at this
  rw [blockPairingForm_JR, emb_apply]
  split_ifs <;> simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h1, h2]

theorem emb_blk {m : ℕ} {R : Type*} [CommRing R] (x : GG (m := m) (R := R)) (a b : Fin m ⊕ Fin m)
    (h : emb x a b ≠ 0) :
    a.isLeft = if x.right = 1 then b.isLeft else !b.isLeft := by
  rw [emb_apply] at h
  split_ifs at h ⊢ <;> rcases a with a | a <;> rcases b with b | b <;> simp at h ⊢

theorem unitaryGroupEmbedding_baseLift_eq_zero_of_wt_ne {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) (h : wt6 a ≠ wt6 b) : emb (r0 η Ψ g) a b = 0 := by
  rw [emb_apply, GG.mat, unitaryThreeReflection_left, theta_tor, tor_val]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | rfl
    | exact Matrix.diagonal_apply_ne (i := a) (j := b) (fun i => ((Ψ g ^ wt1 i : Rˣ) : R)) (by rintro rfl; exact h rfl)

def sgnPerm : ℤˣ →* Equiv.Perm Bool where
  toFun s := if s = 1 then 1 else Function.Involutive.toPerm not Bool.not_not
  map_one' := if_pos rfl
  map_mul' s t := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;> decide

theorem blockPairingForm_normalises_baseLift (O : Type) [CommRing O] {G R : Type} [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (form6 O).Normalises (emb.comp (r0 η Ψ)) := by
  refine ⟨fun g => ⟨1, by rw [one_smul]; exact emb_form O _⟩, ⟨sgnPerm.comp η, fun g a b h => ?_⟩,
    fun g a b h => unitaryGroupEmbedding_baseLift_eq_zero_of_wt_ne η Ψ g a b h⟩
  have := emb_blk _ a b h
  show a.isLeft = (if η g = 1 then 1 else Function.Involutive.toPerm not Bool.not_not : Equiv.Perm Bool) b.isLeft
  rw [this, unitaryThreeReflection_right]
  split_ifs <;> rfl

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ}
  {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

theorem baseLift_map_residue {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (g : G) :
    GG.map (residue O) (r0 η Ψ g) = rbar O η Ψ g := by
  refine SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (residue O) = tor _ (barChar O Ψ g)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

theorem GLift.locConst (hη : IsLocallyConstant η) (r : GLift O η Ψ R) (n : ℕ) :
    IsLocallyConstant fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (r.hom g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 := (IsLocallyConstant.iff_eventually_eq _).1 hη x
  have h2 : ∀ᶠ y in nhds x, ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ n) ((r.hom y).mat a b) =
      Ideal.Quotient.mk (maximalIdeal R ^ n) ((r.hom x).mat a b) :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
      (IsLocallyConstant.iff_eventually_eq _).1 (r.cont a b n) x
  filter_upwards [h1, h2] with y e1 e2
  refine SemidirectProduct.ext (Units.ext ?_) ((r.hasMult y).trans (e1.trans (r.hasMult x).symm))
  ext a b
  exact e2 a b

def GLift.toLift (hη : IsLocallyConstant η) (r : GLift O η Ψ R) : Lift O (emb.comp (rbar O η Ψ)) R where
  hom := emb.comp r.hom
  cont a b n := by
    have := (r.locConst hη n).comp fun x => emb x a b
    simpa only [Function.comp_def, emb_map', Matrix.map_apply, MonoidHom.comp_apply] using this
  red g a b := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← r.red g, emb_map']
    rfl

abbrev unitFrame {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (π : G →* Γ)
    (hπ : Continuous π) (ι : H →* G) (hι : Continuous ι) {Q : Type} [Fintype Q] (D : Q → Subgroup G)
    (N : Q → Subgroup G) : Frame Γ where
  T := Unit
  v0 := ()
  Gv _ := H
  φ _ := π.comp ι
  hφ _ := hπ.comp hι
  Q := Q
  Gq q := D q
  ψ q := π.comp (D q).subtype
  hψ _ := hπ.comp continuous_subtype_val
  N q := (N q).subgroupOf (D q)

abbrev adBar (O : Type) [CommRing O] [IsLocalRing O] {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (j : ℤ) :
    Representation (ResidueField O) G ((form6 O).gw (ResidueField O) j) :=
  FormData.adRep (ρ := emb.comp (rbar O η Ψ)) (blockPairingForm_normalises_baseLift O η (barChar O Ψ)) j

end UpperTheory.V.U3
end
end

section

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Coord

variable {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
  (r : G →* GG (m := 3) (R := R)) (W : WPres O ℤ R)

def IsCoord (s : W.σ) : Prop :=
  ∃ g a b, W.wt s = wt6 a - wt6 b ∧ W.z s = emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)

def EntHomog : Prop := ∀ g a b, emb (r g) a b ∈ W.part (wt6 a - wt6 b)

end Coord

def boxDef (j : ℤ) : ℕ := if |j| ≤ 1 then 1 else 0

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H]

def IsLocPres {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (WB : WPres O ℤ (U.R ⧸ I)) :
    Prop :=
  (∀ s, IsCoord η Ψ (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB s) ∧ EntHomog (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB

variable {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R}

def BoxPres (B : Univ (BoxCond N ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) : Prop :=
  ∃ (W : WPres O ℤ B.R) (i : (U.R ⧸ I) →ₐ[O] B.R) (τ κ : Type) (_ : Fintype τ) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ)
    (f : κ → MvPowerSeries W.σ O) (wf : κ → ℤ),
    IsRelPres WB i W e f wf ∧ push (i.comp (Ideal.Quotient.mkₐ O I)) U.r.hom = B.r.hom.comp ι ∧
    (∀ t, IsCoord η Ψ B.r.hom W (e (.inr t))) ∧ EntHomog B.r.hom W ∧
    ∀ j, Nat.card {u // wf u = j} = Nat.card {t // W.wt (e (.inr t)) = j} + boxDef j

end UpperTheory.V.U3
end
end

section

open Matrix UpperTheory.V.U3

private theorem offdiag_zero {κ : Type} [Field κ] (M : Matrix (Fin 3) (Fin 3) κ) (z z' : κ)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hne : z' ≠ -z)
    (h : M * Matrix.diagonal ![z, 0, -z] = Matrix.diagonal ![z', 0, -z'] * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  intro i j hij
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] at e
  by_contra hM
  have e' := mul_right_cancel₀ hM e
  have hne' : z ≠ -z' := fun h => hne (by rw [h, neg_neg])
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator {κ ι : Type} [Field κ] [IsAlgClosed κ] (m : Fin 3 → κ) (hm : ∀ i, m i ≠ 0)
    (a a' : ι → Matrix (Fin 3) (Fin 3) κ)
    (h1 : ∀ g i j, m i * a g i j = a' g i j * m j)
    (h2 : ∀ g i j, m j.rev * a g i j = a' g i j * m i.rev) :
    ∃ t : κˣ, ∀ g i j, a' g i j = ((t ^ wt i j : κˣ) : κ) * a g i j := by
  have h0 := hm 0
  have h1' := hm 1
  have h2' := hm 2
  have ha : ∀ g i j, a' g i j = m i / m j * a g i j := by
    intro g i j
    have := hm j
    field_simp
    linear_combination -h1 g i j
  by_cases hd : m 0 * m 2 = m 1 * m 1
  · refine ⟨Units.mk0 (m 0 / m 1) (div_ne_zero h0 h1'), fun g i j => ?_⟩
    rw [ha]
    congr 1
    have e2 : m 2 = m 1 * m 1 / m 0 := by field_simp; linear_combination hd
    fin_cases i <;> fin_cases j <;> simp [wt, wt1, e2, zpow_ofNat, h0, h1'] <;> field_simp
  · obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (m 0 / m 2)
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact div_ne_zero h0 h2' (by simpa using hs)
    have hz : ∀ g i j, (m i * m i.rev - m j * m j.rev) * a g i j = 0 := by
      intro g i j
      linear_combination m i.rev * h1 g i j - m j * h2 g i j
    have hd1 : m 0 * m 2 - m 1 * m 1 ≠ 0 := sub_ne_zero.2 hd
    have hd2 : m 2 * m 0 - m 1 * m 1 ≠ 0 := by rwa [mul_comm (m 2)]
    have hd3 : m 1 * m 1 - m 0 * m 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hd)
    have hd4 : m 1 * m 1 - m 2 * m 0 ≠ 0 := by rwa [mul_comm (m 2)]
    refine ⟨Units.mk0 s hs0, fun g i j => ?_⟩
    have z01 : a g 0 1 = 0 := (mul_eq_zero.1 (hz g 0 1)).resolve_left hd1
    have z21 : a g 2 1 = 0 := (mul_eq_zero.1 (hz g 2 1)).resolve_left hd2
    have z10 : a g 1 0 = 0 := (mul_eq_zero.1 (hz g 1 0)).resolve_left hd3
    have z12 : a g 1 2 = 0 := (mul_eq_zero.1 (hz g 1 2)).resolve_left hd4
    have e0 : m 0 = s * s * m 2 := by rw [← hs]; field_simp
    rw [ha]
    fin_cases i <;> fin_cases j <;>
      simp [wt, wt1, z01, z21, z10, z12, e0, zpow_ofNat, h1', h2', hs0] <;> left <;> field_simp

theorem UpperTheory.V.U3.conjBy_tor_of_iso :
    ∀ {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] (η : G →* ℤˣ) (r r' : G →* GG (m := 3) (R := κ)) (c g₁ : G), (2 : κ) ≠ 0 → HasMult η r → HasMult η r' →
      η c = -1 → η g₁ = 1 → Normalised c g₁ r → Normalised c g₁ r' → zeta c g₁ r ≠ 0 → zeta c g₁ r' ≠ 0 → zeta c g₁ r' ≠ -zeta c g₁ r →
      (TypeI η r ∨ TypeII η r) → MatIso η.ker (mats r) (mats r') → ∃ t : κˣ, r' = conjBy (tor κ t) r := by
  intro G κ _ _ _ η r r' c g₁ h2 hr hr' hc hg hN hN' hz hz' hne _ hiso
  obtain ⟨M, hM⟩ := hiso
  have hstar : ∀ g, η g = 1 → η (gstar c g) = 1 := by
    intro g h
    simp [gstar, hc, h]
  have hZ : (M : Matrix (Fin 3) (Fin 3) κ) * zmat c g₁ r = zmat c g₁ r' * M := by
    have e1 := hM g₁ hg
    have e2 := hM (gstar c g₁) (hstar g₁ hg)
    unfold mats at e1 e2
    rw [zmat, zmat, Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [zmat_diag r c g₁ h2.isUnit ((hr c).trans hc) ((hr g₁).trans hg) hN,
    zmat_diag r' c g₁ h2.isUnit ((hr' c).trans hc) ((hr' g₁).trans hg) hN'] at hZ
  have hoff := offdiag_zero _ _ _ hz hz' hne hZ
  have hdiag : (M : Matrix (Fin 3) (Fin 3) κ) = Matrix.diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hm : ∀ i, (M : Matrix (Fin 3) (Fin 3) κ) i i ≠ 0 := by
    have hdet : (M : Matrix (Fin 3) (Fin 3) κ).det ≠ 0 := M.det_ne_zero
    rw [hdiag, Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdet
    exact fun i => hdet i (Finset.mem_univ i)
  have h1 : ∀ g, η g = 1 → ∀ i j, M i i * (r g).mat i j = (r' g).mat i j * M j j := by
    intro g h i j
    have e := hM g h
    rw [hdiag] at e
    have e' := congrFun (congrFun e i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at e'
  have hJ : ∀ (X : Matrix (Fin 3) (Fin 3) κ) (i j : Fin 3),
      (Jmat (R := κ) 3 * Xᵀ * Jmat (R := κ) 3) j.rev i.rev = X i j := by
    intro X i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have h2' : ∀ g, η g = 1 → ∀ i j : Fin 3,
      M j.rev j.rev * (r g).mat i j = (r' g).mat i j * M i.rev i.rev := by
    intro g h i j
    have e := h1 _ (hstar g h) j.rev i.rev
    rwa [(mat_gstar r c g hN.atc ((hr c).trans hc) ((hr g).trans h)).1,
      (mat_gstar r' c g hN'.atc ((hr' c).trans hc) ((hr' g).trans h)).1, hJ, hJ] at e
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator (ι := η.ker) (fun i => M i i) hm (fun g => (r g).mat)
    (fun g => (r' g).mat) (fun g => h1 g g.2) (fun g => h2' g g.2)
  have htor_val (u : κˣ) : (tor κ u : Matrix (Fin 3) (Fin 3) κ) =
      Matrix.diagonal (fun i => ((u ^ wt1 i : κˣ) : κ)) := rfl
  have htheta : theta (tor κ t) = tor κ t := by
    apply Units.ext
    rw [theta_val, ← map_inv, htor_val, htor_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, wt1, Matrix.diagonal, Fin.rev]
  have hact (s : ℤˣ) : sgnAct (m := 3) (R := κ) s (tor κ t) = tor κ t := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp [htheta]
  have hleft (g : G) : (conjBy (tor κ t) r g).left = tor κ t * (r g).left * tor κ t⁻¹ := by
    simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, hact, map_inv]
  have hright (g : G) : (conjBy (tor κ t) r g).right = (r g).right := by
    simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_right, SemidirectProduct.inv_right]
  have hmat (g : G) (i j : Fin 3) :
      (conjBy (tor κ t) r g).mat i j = ((t ^ wt i j : κˣ) : κ) * (r g).mat i j := by
    show (((conjBy (tor κ t) r g).left : GL (Fin 3) κ) : Matrix (Fin 3) (Fin 3) κ) i j = _
    rw [hleft, Units.val_mul, Units.val_mul, htor_val, htor_val, mul_diagonal, diagonal_mul]
    have hweight : ((t ^ wt1 i : κˣ) : κ) * ((t⁻¹ ^ wt1 j : κˣ) : κ) = ((t ^ wt i j : κˣ) : κ) := by
      rw [← Units.val_mul, wt, _root_.zpow_sub, _root_.inv_zpow]
    rw [← hweight, GG.mat]
    ring
  refine ⟨t, ?_⟩
  have hker : ∀ g, η g = 1 → r' g = conjBy (tor κ t) r g := by
    intro g h
    refine SemidirectProduct.ext (Units.ext ?_) (by rw [hright, hr g, hr' g])
    ext i j
    exact (ht ⟨g, h⟩ i j).trans (hmat g i j).symm
  have hconj_c : (conjBy (tor κ t) r c).mat = 1 := by
    ext i j
    rw [hmat, hN.atc]
    by_cases hij : i = j
    · subst j
      simp [wt]
    · simp [Matrix.one_apply_ne hij]
  have hcc : r' c = conjBy (tor κ t) r c :=
    SemidirectProduct.ext (Units.ext (hN'.atc.trans hconj_c.symm))
      (by rw [hright, hr c, hr' c])
  refine MonoidHom.ext fun g => ?_
  rcases Int.units_eq_one_or (η g) with h | h
  · exact hker g h
  · have e : g = g * c⁻¹ * c := by simp
    rw [e, map_mul r' _ c, map_mul _ _ c, hcc, hker (g * c⁻¹) (by simp [h, hc])]
end
