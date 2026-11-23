module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam.SpanFam

def colL (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (quat d)ᵀ 0 ((d : ℤ) • 1)

def colR (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 0 (quat d) 1

theorem colL_mul_transpose {d : ℕ} (hd : 0 < d) : colL d * (colL d)ᵀ = (d : ℤ) • form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colL, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]
  congr 1
  · rw [transpose_transpose, quat_transpose_mul, h1]; simp [sub_smul, smul_smul]
  · simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, transpose_zero, transpose_smul, transpose_one]
  · simp
  · simp [smul_smul]

theorem colR_mul_transpose {d : ℕ} (hd : 0 < d) : colR d * (colR d)ᵀ = form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colR, form, fromBlocks_transpose, fromBlocks_multiply]
  congr 1
  · simp
  · simp
  · simp
  · rw [quat_mul_transpose, h1]; simp [sub_smul]

def col (d : ℕ) (q : Fin 4 ⊕ Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Sum.elim (fun _ => colL d) (fun _ => colR d) q

def famM (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  col d t.2 * single t.1 t.2 1

theorem famM_apply (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) (p q : Fin 4 ⊕ Fin 4) :
    famM d t p q = if q = t.2 then col d t.2 p t.1 else 0 := by
  unfold famM
  split_ifs with h
  · subst h; simp
  · exact mul_single_apply_of_ne _ _ _ _ _ h _

theorem famM_mem (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : famM d t ∈ ord d := by
  intro i j
  rw [famM_apply]
  obtain ⟨k, q⟩ := t
  split_ifs with h
  · simp only at h
    subst h
    rcases k with k | k
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₁, Matrix.zero_apply]; exact dvd_zero _
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
  · exact dvd_zero _

theorem famM_form_transpose {d : ℕ} (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) :
    famM d t * form d * (famM d t)ᵀ = col d t.2 * single t.1 t.1 (form d t.2 t.2) * (col d t.2)ᵀ := by
  calc famM d t * form d * (famM d t)ᵀ
      = col d t.2 * (single t.1 t.2 1 * form d * single t.2 t.1 1) * (col d t.2)ᵀ := by
        simp only [famM, transpose_mul, transpose_single, Matrix.mul_assoc]
    _ = _ := by rw [single_mul_mul_single, _root_.one_mul, _root_.mul_one]

theorem sum_single_diag' (c : ℤ) : ∑ k : Fin 4 ⊕ Fin 4, single k k c = c • (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases h : a = b
  · subst h; simp [single_apply]
  · rw [Finset.sum_eq_zero (fun k _ => by rw [single_apply]; exact if_neg (fun hk => h (hk.1.symm.trans hk.2)))]
    simp [Matrix.one_apply, h]

theorem sum_famM {d : ℕ} (hd : 0 < d) :
    ∑ t, famM d t * form d * (famM d t)ᵀ = ((8 * d : ℕ) : ℤ) • form d := by
  simp_rw [famM_form_transpose]
  rw [Fintype.sum_prod_type_right]
  have hq : ∀ q : Fin 4 ⊕ Fin 4, ∑ k : Fin 4 ⊕ Fin 4, col d q * single k k (form d q q) * (col d q)ᵀ
      = form d q q • (col d q * (col d q)ᵀ) := by
    intro q
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_diag', Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  simp_rw [hq]
  rw [Fintype.sum_sum_type]
  simp only [col, Sum.elim_inl, Sum.elim_inr, colL_mul_transpose hd, colR_mul_transpose hd, smul_smul]
  have e1 : ∀ j : Fin 4, form d (Sum.inl j) (Sum.inl j) = 1 := fun j => by simp [form]
  have e2 : ∀ j : Fin 4, form d (Sum.inr j) (Sum.inr j) = d := fun j => by
    simp only [form, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one]
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← add_smul, smul_smul]
  rw [_root_.one_mul, ← add_nsmul, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
  congr 1

def fam (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : ord d := ⟨famM d t, famM_mem d t⟩

def coef (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : (Fin 4 ⊕ Fin 4) → (Fin 4 ⊕ Fin 4) → ℤ
  | Sum.inr m, Sum.inl j => N (Sum.inr m) (Sum.inl j) / d
  | Sum.inl m, Sum.inl j => N (Sum.inl m) (Sum.inl j) - ∑ s, quat d s m * (N (Sum.inr s) (Sum.inl j) / d)
  | Sum.inl m, Sum.inr j => N (Sum.inl m) (Sum.inr j)
  | Sum.inr m, Sum.inr j => N (Sum.inr m) (Sum.inr j) - ∑ s, quat d m s * N (Sum.inl s) (Sum.inr j)

theorem sum_coef_famM {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ} (hN : N ∈ ord d) (p q : Fin 4 ⊕ Fin 4) :
    ∑ t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4), coef d N t.1 t.2 * famM d t p q = N p q := by
  simp only [famM_apply, mul_ite, mul_zero]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hdiv : ∀ m j, (d : ℤ) * (N (Sum.inr m) (Sum.inl j) / d) = N (Sum.inr m) (Sum.inl j) :=
    fun m j => Int.mul_ediv_cancel' (hN m j)
  rcases q with j | j <;> rcases p with m | m <;>
    simp [Fintype.sum_sum_type, col, colL, colR, coef, Matrix.one_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, hdiv, mul_comm]
  all_goals done

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam.SpanFam

theorem span_fam_eq_top {d : ℕ} : Submodule.span ℤ (Set.range (fam d)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  rintro ⟨N, hN⟩
  have hx : (⟨N, hN⟩ : ord d) = ∑ t, coef d N t.1 t.2 • fam d t := by
    apply Subtype.ext
    ext p q
    change N p q = ((∑ t, coef d N t.1 t.2 • fam d t : ord d) : Matrix _ _ ℤ) p q
    rw [← sum_coef_famM hN p q]
    simp only [fam, AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [AddSubgroupClass.coe_zsmul, Matrix.smul_apply, smul_eq_mul]
  rw [hx]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem sum_fam_mul_bar {d : ℕ} (hd : 0 < d) :
    ∑ t, fam d t * bar d (fam d t) = ((8 * d : ℕ) : ord d) := by
  apply Subtype.ext
  have h : ∑ t, famM d t * form d * (famM d t)ᵀ * formInv d = ((8 * d : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) := by
    rw [← Finset.sum_mul, sum_famM hd, Matrix.smul_mul, form_mul_formInv hd]
  simp only [fam, bar_coe, Subring.coe_mul, Matrix.mul_assoc] at h ⊢
  simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, bar_coe, Matrix.mul_assoc]
  rw [h]
  simp only [Subring.coe_natCast]
  rw [Nat.cast_smul_eq_nsmul ℤ, nsmul_one]

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam

theorem exists_spanning_family_posDef :
    ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  intro d hd
  let e := Fintype.equivFin ((Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4))
  refine ⟨_, fun i => SpanFam.fam d (e.symm i), 1, 8 * d, ?_, ?_, by omega, ?_⟩
  · have hc : (fun i => SpanFam.fam d (e.symm i)) = SpanFam.fam d ∘ e.symm := rfl
    rw [hc, e.symm.surjective.range_comp]
    exact SpanFam.span_fam_eq_top
  · rw [transpose_one, Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one]
    exact Matrix.PosDef.one.add Matrix.PosDef.one
  · simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← SpanFam.sum_fam_mul_bar hd]
    exact Equiv.sum_comp e.symm (fun t => SpanFam.fam d t * bar d (SpanFam.fam d t))

end GlobalTheory.ZarhinFam
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole.CellNear

theorem vecAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (k : TF.X.F.J) {S : Type}
    [CommRing S] {z₁ z₂ : Sp S ⟶ TF.X.YY} (h : z₁ = z₂) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ TF.X.F.U k) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ TF.X.F.U k)
    {x : Sp S ⟶ TF.Y.X} (hx₁ : z₁ ≫ TF.X.π = x) (hx₂ : z₂ ≫ TF.X.π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TF.X.F.vecAt k z₁ h₁ hx₁ σ i = TF.X.F.vecAt k z₂ h₂ hx₂ σ i := by
  subst h; rfl

theorem exists_frameMat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c)
    (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (hv : IsEigBasis TF U e v) (k : TF.X.F.J)
    {W₀ : (Y₀ TF.X Z).Opens} (hW₀ : IsAffineOpen W₀) (hW₀U : W₀ ≤ toBase TF Z ⁻¹ᵁ U.1)
    (hW₀k : W₀ ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W₀),
      (∀ σ, IsUnit (C σ).det) ∧ IsFrameMat TF Z U e v W₀ k C := by
  have hU0 : ⊤ ≤ (FlagMod.tau hW₀ ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun q hq => FlagMod.tau_le hW₀ hW₀U hq
  have hk0 : ⊤ ≤ (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun q hq => FlagMod.tau_le hW₀ hW₀k hq
  have hx0 : (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ≫ TF.X.π = FlagMod.tau hW₀ ≫ toBase TF Z := Category.assoc _ _ _
  obtain ⟨C, hC⟩ := GlobalTheory.T.frameVector_isCombination_eigenbasis_flagSpace_point E H Dw l Xo c TF Z U n e v hv k _ (FlagMod.tau hW₀) hU0 hk0 hx0
  refine ⟨C, fun σ => GlobalTheory.T.isUnit_det_frame_eigenbasis_block_at_point E H Dw l Xo c TF Z U n e v hv k _ (FlagMod.tau hW₀) hU0 hk0 hx0 σ (C σ)
    (hC σ), ?_⟩
  intro S _ z hz hU hk hx σ i
  have hzφ : spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ = z := FlagMod.spMap_ev z hW₀ hz
  have eb : spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ toBase TF Z = z ≫ toBase TF Z := by
    rw [← Category.assoc, hzφ]
  have hb := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H TF.Y.X TF.Y.t _ S (ev z W₀ hz)
    (FlagMod.tau hW₀ ≫ toBase TF Z) (z ≫ toBase TF Z) eb).2 _
    (fun j => spMap (dualMap (ev (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0)) ≫ v (e ⟨σ, j⟩)) (C σ i) _ (hC σ i)
  have e1 : ∀ j, spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v j =
      spMap (dualMap (ev z W₀ hz)) ≫ spMap (dualMap (ev (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0)) ≫ v j := by
    intro j
    rw [← Category.assoc (spMap (dualMap (ev z W₀ hz))), TanBaseChange.spMap_comp_spMap', ← FlagMod.dualMap_comp,
      ← FlagMod.ev_spMap (ev z W₀ hz) (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0 (FlagMod.le_preimage_comp _ hU0),
      FlagMod.ev_congr eb U.1 (FlagMod.le_preimage_comp _ hU0) hU]
  have hz' : ⊤ ≤ (spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k :=
    FlagMod.le_preimage_comp _ hk0
  have hx' : (spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z := by
    rw [← eb]; simp only [toBase, Category.assoc]
  have e2 : (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left =
      spMap (dualMap (ev z W₀ hz)) ≫ (tv (TF.X.F.vecAt k (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) hk0 hx0 σ i)).left := by
    rw [← FlagMod.tanPull_left (ev z W₀ hz) eb, FlagMod.Frames.tanPull_vecAt TF.X.F k (ev z W₀ hz) _ hk0 hz' hx0 hx' eb,
      vecAt_congr TF k (by rw [← Category.assoc, hzφ]) hz' hk hx' hx]
  rw [funext fun j => e1 (e ⟨σ, j⟩), e2]
  exact hb

theorem isUnit_prod_univ {R ι : Type} [CommRing R] [Fintype ι] (f : ι → R) (h : ∀ i, IsUnit (f i)) :
    IsUnit (∏ i, f i) :=
  Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => h i

theorem isUnit_of_isUnit_prod_univ {R ι : Type} [CommRing R] [Fintype ι] (f : ι → R) (h : IsUnit (∏ i, f i))
    (i : ι) : IsUnit (f i) :=
  isUnit_of_dvd_unit (Finset.dvd_prod_of_mem f (Finset.mem_univ i)) h

end GlobalTheory.LogPole.CellNear


open GlobalTheory.LogPole.CellNear in
theorem GlobalTheory.LogPole.exists_isCell_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (y : Y₀ TF.X Z), toBase TF Z y ∈ U.1 → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∃ (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsEigBasis TF U e' v ∧ y ∈ W ∧ W ≤ V ∧ IsCell TF Z U e' v W k L N := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv y hyU V hyV
  obtain ⟨k, hk⟩ : ∃ k, inc₀ TF.X Z y ∈ TF.X.F.U k := by
    have : inc₀ TF.X Z y ∈ ⨆ k, TF.X.F.U k := by rw [TF.X.F.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW₀, hW₀le⟩ := (Y₀ TF.X Z).isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((V ⊓ toBase TF Z ⁻¹ᵁ U.1 ⊓ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k : (Y₀ TF.X Z).Opens) : Set (Y₀ TF.X Z)) from
      ⟨⟨hyV, hyU⟩, hk⟩) (V ⊓ toBase TF Z ⁻¹ᵁ U.1 ⊓ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k).isOpen
  have hW₀V : W₀ ≤ V := fun q hq => (hW₀le hq).1.1
  have hW₀U : W₀ ≤ toBase TF Z ⁻¹ᵁ U.1 := fun q hq => (hW₀le hq).1.2
  have hW₀k : W₀ ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k := fun q hq => (hW₀le hq).2
  obtain ⟨C, hCu, hC⟩ := exists_frameMat TF Z U e v hv k hW₀ hW₀U hW₀k
  let g := ((Y₀ TF.X Z).presheaf.germ W₀ y hyW₀).hom
  have hperm : ∀ σ : E →+* ℂ, ∃ w : Equiv.Perm (Fin (Dw.mult σ)), ∀ (m : ℕ) (hm : m ≤ Dw.mult σ),
      IsUnit ((((C σ).map g).submatrix id w).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := fun σ =>
    GlobalTheory.exists_perm_isUnit_leading_minors_localRing _ (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (hCu σ).map g)
  choose p hp using hperm
  let mn : (σ : E →+* ℂ) → Fin (Dw.mult σ + 1) → Γ(Y₀ TF.X Z, W₀) := fun σ m =>
    (((C σ).submatrix id (p σ)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2))
      (Fin.castLE (Nat.lt_succ_iff.mp m.2))).det
  have hmap : ∀ {R' : Type} [CommRing R'] (φ : Γ(Y₀ TF.X Z, W₀) →+* R') (σ : E →+* ℂ) (m : Fin (Dw.mult σ + 1)),
      φ (mn σ m) = ((((C σ).map φ).submatrix id (p σ)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2))
        (Fin.castLE (Nat.lt_succ_iff.mp m.2))).det := by
    intro R' _ φ σ m
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, ← Matrix.submatrix_map]
  let f := ∏ σ, ∏ m, mn σ m
  have hyf : y ∈ (Y₀ TF.X Z).basicOpen f := by
    rw [Scheme.mem_basicOpen _ f y hyW₀]
    show IsUnit (g f)
    rw [map_prod]
    refine isUnit_prod_univ _ fun σ => ?_
    rw [map_prod]
    refine isUnit_prod_univ _ fun m => ?_
    rw [hmap]
    exact hp σ m (Nat.lt_succ_iff.mp m.2)
  have hWW₀ : (Y₀ TF.X Z).basicOpen f ≤ W₀ := (Y₀ TF.X Z).basicOpen_le f
  have hWa : IsAffineOpen ((Y₀ TF.X Z).basicOpen f) := hW₀.basicOpen f
  have hrf : IsUnit (resG (Y₀ TF.X Z) hWW₀ f) := (Y₀ TF.X Z).toRingedSpace.isUnit_res_basicOpen f
  have hrm : ∀ σ m, IsUnit (resG (Y₀ TF.X Z) hWW₀ (mn σ m)) := by
    intro σ m
    rw [map_prod] at hrf
    have h1 := isUnit_of_isUnit_prod_univ _ hrf σ
    rw [map_prod] at h1
    exact isUnit_of_isUnit_prod_univ _ h1 m
  have hLU : ∀ σ : E →+* ℂ, ∃ L N : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, (Y₀ TF.X Z).basicOpen f),
      GlobalTheory.ShFam.Cell.IsLowInv L ∧ (∀ i j, j < i → N i j = 0) ∧ (∀ i, N i i = 1) ∧
        ((C σ).map (resG (Y₀ TF.X Z) hWW₀)).submatrix id (p σ) = L * N := fun σ =>
    GlobalTheory.ShFam.Cell.exists_lowInv_mul_upperUni_of_leadingMinors _ _ fun m hm => by
      have := hrm σ ⟨m, Nat.lt_succ_of_le hm⟩
      rw [hmap] at this
      exact this
  choose L N hL hN hNd hLN using hLU
  refine ⟨permE e p, (Y₀ TF.X Z).basicOpen f, k, L, N, isEigBasis_permE p hv, hyf, hWW₀.trans hW₀V,
    isCell_of_isFrameMat hWa (hWW₀.trans hW₀U) (hWW₀.trans hW₀k) (fun σ => (hL σ).1) (fun σ => (hL σ).2) hN hNd ?_⟩
  have h1 := isFrameMat_mono hWW₀ (isFrameMat_permE p hC)
  have e1 : (fun σ => ((C σ).submatrix id (p σ)).map (resG (Y₀ TF.X Z) hWW₀)) = fun σ => L σ * N σ :=
    funext fun σ => (Matrix.submatrix_map _ _ _ _).symm.trans (hLN σ)
  rw [e1] at h1
  exact h1
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.GenKSProof

theorem embK_conj_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c ((starRingEnd ℂ).comp τ) (H.bar x) = embK c τ x := by
  apply Subtype.ext
  show ((starRingEnd ℂ).comp τ) ((H.bar x : 𝓞 E) : E) = τ (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem embK_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c ((starRingEnd ℂ).comp τ) x := by
  apply Subtype.ext
  show τ ((H.bar x : 𝓞 E) : E) = ((starRingEnd ℂ).comp τ) (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem card_pairIx {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) : Fintype.card (GlobalTheory.LogKSDiv.PairIx H Dw) = Dw.dim := by
  have h := FlagTan.isHalf_psiSet H
  have hc : Fintype.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
    rw [← h.card, FlagTan.psiSet, Fintype.card_subtype]
  have hm : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      Dw.mult τ.1 * Dw.mult ((starRingEnd ℂ).comp τ.1) = Dw.p * Dw.q := fun τ => by
    rcases FlagTan.mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b]
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b, mul_comm]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, hm, Finset.sum_const, Finset.card_univ, hc,
    smul_eq_mul, Datum.dim, mul_assoc]

theorem symPair_mem_balanced {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (R : Type) [CommRing R] (κ : c.F → R) (n : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P ∈
      LogKS.balanced H.bar (fun a => Matrix.diagonal fun j => κ (embK c (e.symm j).1 a)) := by
  refine (LogKS.mem_balanced_diagonal H.bar (fun j a => κ (embK c (e.symm j).1 a)) _).2 ⟨?_, fun a i k => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    rw [add_comm]
    congr 1 <;> congr 1 <;> exact propext and_comm
  · simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    by_cases h1 : i = e ⟨P.1.1, P.2.1⟩ ∧ k = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [Equiv.symm_apply_apply, embK_conj_bar', sub_self, zero_mul]
    by_cases h2 : i = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ k = e ⟨P.1.1, P.2.1⟩
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Equiv.symm_apply_apply, embK_bar', sub_self, zero_mul]
    · rw [if_neg h1, if_neg h2, add_zero, mul_zero]

theorem exists_ext (k R K : Type) [CommRing k] [CommRing R] [Field K] (ρ : R →+* K) (α : k →+* K) (κ : k → R)
    (hfr : letI := ρ.toAlgebra; IsFractionRing R K) (hκ : ∀ a, ρ (κ a) = α a) (d : Derivation ℤ R R)
    (hd : ∀ a, d (κ a) = 0) :
    ∃ D : (letI := α.toAlgebra; Derivation k K K), ∀ r, D (ρ r) = ρ (d r) := by
  letI := ρ.toAlgebra
  obtain ⟨δ, hδ, hδρ⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (A := R) (B := K) (nonZeroDivisors R) (fun r => ρ (d r))
    (fun x y => by rw [map_add (f := _), map_add (f := _)]) (fun x y => by
      rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul]; rfl)
  have hα : ∀ a, δ (α a) = 0 := fun a => by
    rw [← hκ a]
    exact (hδρ (κ a)).trans (by rw [hd, map_zero])
  letI := α.toAlgebra
  have hs : ∀ (a : k) (x : K), δ (a • x) = a • δ x := fun a x => by
    show δ (α a * x) = α a * δ x
    rw [hδ.mul, hα, mul_zero, add_zero]
  let D0 : K →ₗ[k] K := { toFun := δ, map_add' := hδ.add, map_smul' := hs }
  exact ⟨{ toLinearMap := D0, map_one_eq_zero' := hδ.der_one, leibniz' := (fun x y => hδ.mul x y) },
    fun r => hδρ r⟩

theorem exists_genKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ φ₀ f₀ hφ₀
  obtain ⟨U, hU, ρ, n, e, v, hch, htan, huq, hf, heig⟩ := GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen E H Dw l Xo c TF Z φ₀ f₀ hφ₀
  obtain ⟨hfr, hconst⟩ := GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart E H Dw l Xo c TF Z U hU ρ hch
  obtain ⟨e', he'⟩ := TF.logKS U n v _ htan huq heig
  let ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw := (Fintype.equivFinOfCardEq (card_pairIx H Dw)).symm
  let Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U :=
    fun j => e'.symm ⟨GlobalTheory.LogKSDiv.symPair e (ε j), symPair_mem_balanced H Dw l c _ _ n e (ε j)⟩
  have hD := fun j => exists_ext c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField ρ (GlobalTheory.Cartier.constFn (s₀ TF.Y Z))
    (constFn TF.Y.s U.1) hfr hconst (Dl j).1 (Dl j).2.1
  choose D hD using hD
  refine ⟨D, U, hU, ρ, n, e, v, ε, Dl, hch, htan, huq, fun τ i => hf τ i, fun j => ?_, hD⟩
  refine (he' (Dl j) _).2 ?_
  simp only [Dl, LinearEquiv.apply_symm_apply]

end GlobalTheory.LogKSDiv.GenKSProof
end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ Z) (x : Sp S ⟶ Y.X) (hx : z ≫ π = x) (hx' : z' ≫ π = x), (∀ σ i, (cellFrames hZ ht).step z hx σ i = (cellFrames hZ ht).step z' hx' σ i) → z = z' := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cell_sep | exact GlobalTheory.FlagMod.FieldFlag.cell_sep | (intros; apply GlobalTheory.FlagMod.FieldFlag.cell_sep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.flagCellFrameChangeTriangular_of_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), FlagCellFrameChangeTriangular hZ := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular | exact GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular | (intros; apply GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular <;> assumption)
end
