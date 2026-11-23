module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle038
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle322
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.FlatColLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_iota (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem iota_mul (p : Place D k) (x : k) (m : AE D) : p.ι x * m = p.ι (x * p.π m) := by
  have h2 := p.ι_π (p.ι x * m)
  rw [map_mul, p.π_ι] at h2
  rw [h2, ← mul_assoc, e_iota]

theorem xi_ne (p : Place D k) : p.xi ≠ 0 := by
  have h : p.xi * p.pr D.host.xi0⁻¹ = 1 := by
    rw [Place.xi, Place.pr, Place.pr, ← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one,
      map_one]
  exact left_ne_zero_of_mul_eq_one h

theorem map_iota_mul (p : Place D k) {a b c : ℕ} (zk : Matrix (Fin a) (Fin b) k) (x : Mx D b c) :
    (zk.map p.ι : Mx D a b) ⬝ x = (zk * x.map p.π).map p.ι := by
  ext i j

  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iota_mul]

theorem trace_map_iota (p : Place D k) {a : ℕ} (x : Matrix (Fin a) (Fin a) k) :
    (x.map p.ι : Mx D a a).trace = p.ι x.trace := by

  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem map_iota_pi (p : Place D k) {a b : ℕ} (x : Matrix (Fin a) (Fin b) k) : (x.map p.ι).map p.π = x := by
  ext i j
  exact p.π_ι _

theorem hO_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (w : WO S T) (a : Mx D T.rank ρ) :
    hO S T w (d.extY T a) = pairS T (w ⬝ d.jX) a := by
  rw [d.hO_coordS]
  simp only [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, HypDec.pY_j0, HypDec.pY_jX, Matrix.mul_one,
    Matrix.mul_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.zero_mul, trace_zero, add_zero]

theorem pairS_giA_adj (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (z : Mx D ρ T.rank) :
    pairS T x (giA T ⬝ adj z) = (z ⬝ x).trace := by
  rw [pairS, adj_mul, adj_adj, adj_giA, Matrix.mul_assoc, giA_gA_cancel]

theorem psi_sympl_extY (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hχ : p.IsChar ψ ψk)
    {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (zk : Matrix (Fin ρ) (Fin T.rank) k) (w : WO S T) :
    ψ (symplO S T w (d.extY T (giA T ⬝ adj (zk.map p.ι : Mx D ρ T.rank)))) =
      (ψk ((zk * (w ⬝ d.jX : Mx D T.rank ρ).map p.π).trace) : ℂ) := by
  rw [hχ, symplO, hO_extY, pairS_giA_adj, map_iota_mul, trace_map_iota]
  rfl

theorem isHalf_mul_left {e : AE D} {a b c : ℕ} (x : Mx D a b) {y : Mx D b c} (h : IsHalf e y) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

theorem isHalf_mul_right {e : AE D} {a b c : ℕ} {x : Mx D a b} (y : Mx D b c) (h : IsHalf e x) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem isHalf_adj (p : Place D k) {a b : ℕ} (zk : Matrix (Fin a) (Fin b) k) :
    IsHalf (cA D p.e) (adj (zk.map p.ι : Mx D a b)) := fun i j =>
  (map_mul (cA D) p.e (p.ι (zk j i))).symm.trans (congrArg (cA D) (e_iota p _))

theorem exists_mxAt (p : Place D k) : ∃ v : GlobalTheory.FinPl.Pl D, ∀ (a b : ℕ) (x : Mx D a b), IsHalf (cA D p.e) x →
    GlobalTheory.FinPl.MxAt (· = v) x := by
  obtain ⟨_, h0, v, ε, h1, h2⟩ := p.split
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  refine ⟨v, fun a b x hx i j => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  rw [← h2, add_mul, hx i j, ← hx i j, ← mul_assoc, h0, zero_mul, zero_add]

theorem trace_mul_uni {ρ : ℕ} (M : Mx D ρ ρ) (hM : ∀ i j, j < i → M i j = 0) (u : UX D ρ) :
    (M ⬝ u.1.1).trace = M.trace := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hu := u.2
  rw [Matrix.diag_apply, Matrix.diag_apply, GlobalTheory.UniIndexPrime.diag_mul hM (fun a b h => (hu a b).1 h), (hu i i).2, mul_one]

theorem col_mul {K m l o o' : Type} [Field K] [Fintype l] (M : Matrix m l K) (E : Matrix l o K) (F : Matrix l o' K) (j : o)
    (j' : o') {κ : K} (hκ : κ ≠ 0) (h : ∀ x, F x j' = κ * E x j) (r : m) : (M * E) r j = κ⁻¹ * (M * F) r j' := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by field_simp

theorem row_mul {K m l o : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l o K) (i : Fin ρ) (j : o) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X) i j =
      if i = i₀ then a * (G * X) r j else 0 := by
  by_cases h : i = i₀ <;> simp [Matrix.mul_apply, h, Finset.mul_sum, mul_assoc]

theorem trace_row_mul {K m l : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l (Fin ρ) K) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X).trace = a * (G * X) r i₀ := by
  simp only [Matrix.trace, Matrix.diag_apply, row_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem law_dual_col : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ GlobalTheory.RootEx.Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  intro D _ hFL _ k _ _ _ _ _ _ p ν _ ψ ψk hχ ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW _ hbes hjac Tm hTm r q hq b Φ Φ' hΦ'
  obtain ⟨i, rfl, hi, hfree⟩ := hq
  have hc : c = 2 * ρ := hjac.1
  have hκ : ∀ m : ℕ, s * p.xi ^ m ≠ 0 := fun m => mul_ne_zero hs (pow_ne_zero _ (xi_ne p))
  let i₀ : Fin ρ := ⟨i.val, hi⟩
  let zk : Matrix (Fin ρ) (Fin J.W.rank) k :=
    Matrix.of fun i' β => if i' = i₀ then b * (s * p.xi ^ (ρ - i.val)) * FW.γ r β else 0
  let a : Mx D J.W.rank ρ := giA J.W ⬝ adj (zk.map p.ι : Mx D ρ J.W.rank)
  have ha : IsHalf (cA D p.e) a := isHalf_mul_left _ (isHalf_adj p zk)
  have hy : IsHalf (cA D p.e) (B.d.extY J.W a) := isHalf_mul_right _ ha
  have hW : ∀ j : Fin ρ, (FW.γ * J.d.jX.map p.π) r j = (s * p.xi ^ (ρ - j.val))⁻¹ *
      (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inr ⟨j.val, by omega⟩) := fun j => by
    rw [← FW.γβ]
    exact col_mul _ _ _ _ _ (hκ _) (hjac.2.2.1 j ⟨j.val, by omega⟩ rfl) r
  have hB : ∀ t, ψ (symplO B.V J.W (p.up FV FW t) (B.d.extY J.W a)) = (ψk (b * t r (Sum.inr i)) : ℂ) := fun t => by
    rw [psi_sympl_extY p hχ, trace_row_mul, Place.up, map_iota_mul, map_iota_pi, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, FW.γβ, Matrix.one_mul,
      col_mul _ _ FV.β i₀ (Sum.inr i) (hκ _) (hbes.2.2.1 i₀ i rfl), Matrix.mul_assoc, FV.γβ, Matrix.mul_one, mul_assoc,
      mul_inv_cancel_left₀ (hκ _)]
  have hD : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d)) (B.d.extY J.W a)) =
      (ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) := by
    rw [psi_sympl_extY p hχ, trace_row_mul, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, xZero, hW,
      mul_assoc, mul_inv_cancel_left₀ (hκ _)]
    congr 3
    rcases r with r | r
    · simp [basePt]
    · simp [basePt, Matrix.one_apply, Fin.ext_iff, i₀]
  have hU : GlobalTheory.FinPl.UInv J.W (xZero J.d) a := fun u => by
    rw [pairS_giA_adj, pairS_giA_adj, ← Matrix.mul_assoc]
    refine trace_mul_uni _ (fun i' j hj => ?_) u
    rw [map_iota_mul, Matrix.map_apply, row_mul]
    split_ifs with h
    · subst h
      rw [xZero, hW, Matrix.one_apply_ne, mul_zero, mul_zero, map_zero]
      rintro rfl
      exact hfree hj
    · exact map_zero _
  obtain ⟨v, hv⟩ := exists_mxAt p
  have hlaw := ((hFL ψ (· = v)).1 ρ B J st).Heisenberg₂.dual _ (hTm.theta Φ) a (hv _ _ a ha) hU
  have hmod := hTm.modul _ hy Φ ((ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) • Φ') fun t => by
    rw [hB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΦ', ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← mul_add, add_sub_cancel]
  rw [← hmod, hD, map_smul, GlobalTheory.HandHom.flatBF_smul] at hlaw
  exact smul_right_injective _ (Circle.coe_ne_zero _) hlaw

end GlobalTheory.FlatColLaw

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod Filter
open GlobalTheory.PlaceModel (half mem_half isHalf_iff heisL heisL_half heisL_comm hO_smul_left infPart_half)
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LocMod.Inhab

namespace GlobalTheory.LocMod.Exist

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
  (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)

def loc {m n : Type} (a : Matrix m n D.host.E) : Matrix m n k := a.map (p.π.comp (incA D))

theorem loc_gram_mul (V : HSp D) : loc p V.gram * loc p V.gram⁻¹ = 1 := by
  rw [loc, loc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_ne V).isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

theorem loc_mul_gram (V : HSp D) : loc p V.gram⁻¹ * loc p V.gram = 1 := mul_eq_one_comm.1 (loc_gram_mul p V)

def dual (b : Matrix Y Y' k) : WO S T :=
  (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ.map fun z => cA D (p.ι z)

theorem up_mem (x : Matrix Y Y' k) : p.up FS FT x ∈ half S T p.e :=
  (isHalf_iff S T).1 fun _ _ => e_mul_ι p _

theorem dual_mem (b : Matrix Y Y' k) : dual p FS FT b ∈ half S T (cA D p.e) :=
  (isHalf_iff S T).1 fun _ _ => by
    simp only [dual, Matrix.map_apply]
    rw [← map_mul, e_mul_ι]

theorem up_add (x y : Matrix Y Y' k) : p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  ext i j
  simp only [Place.up, Matrix.mul_add, Matrix.add_mul, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem dual_add (x y : Matrix Y Y' k) : dual p FS FT (x + y) = dual p FS FT x + dual p FS FT y := by
  ext i j
  simp only [dual, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem up_zero : p.up FS FT 0 = 0 := by simpa using up_add p FS FT 0 0

theorem dual_zero : dual p FS FT 0 = 0 := by simpa using dual_add p FS FT 0 0

theorem continuous_up : Continuous (p.up FS FT) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map p.cont_ι

theorem continuous_dual : Continuous (dual p FS FT) :=
  ((((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_transpose).matrix_map ((GlobalTheory.DualPairCompare.continuous_cA D).comp p.cont_ι)

theorem π_hO (x y : WO S T) : p.π (hO S T x y) = Matrix.trace
    (loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * Matrix.map x p.π) := by

  simp only [hO, map_sum, map_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, loc, Matrix.map_apply,
  Matrix.transpose_apply, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem π_hO_dual (t b : Matrix Y Y' k) : p.π (hO S T (p.up FS FT t) (dual p FS FT b)) = ∑ r, ∑ q, b r q * t r q := by
  have h1 : (Matrix.map (dual p FS FT b) fun z => p.π (cA D z)) = (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ := by
    ext i j
    simp only [dual, Matrix.map_apply, cA_cA, p.π_ι]
  have h2 : Matrix.map (p.up FS FT t) p.π = FT.β * t * FS.γ := by
    ext i j
    simp only [Place.up, Matrix.map_apply, p.π_ι]
  rw [π_hO, h1, h2, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [loc_mul_gram, Matrix.one_mul, Matrix.mul_assoc _ _ (loc p T.gram), loc_mul_gram, Matrix.mul_one,
    Matrix.mul_assoc _ _ FT.β, FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [FS.γβ, Matrix.one_mul, Finset.sum_comm]
  rfl

theorem exists_dual {y : WO S T} (hy : IsHalf (cA D p.e) y) : ∃ b, dual p FS FT b = y := by
  refine ⟨(FS.γ * loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * FT.β)ᵀ, ?_⟩
  rw [dual, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ FS.β, FS.βγ, Matrix.mul_one, loc_gram_mul, Matrix.one_mul, Matrix.mul_assoc _ FT.β, FT.βγ,
    Matrix.mul_one, Matrix.mul_assoc, loc_gram_mul, Matrix.mul_one, Matrix.transpose_transpose]
  ext i j
  simp only [Matrix.map_apply, p.ι_π, map_mul, cA_cA]
  exact hy i j

theorem char_sympl {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (t b : Matrix Y Y' k) :
    ψ (symplO S T (p.up FS FT t) (dual p FS FT b)) = pairing ψk t b := by
  rw [pairing, ← π_hO_dual p FS FT, h, p.ι_π, ← hO_smul_left, (mem_half S T).1 (up_mem p FS FT t)]
  rfl

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

end GlobalTheory.LocMod.Exist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.RankZeroSrc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul_incA (p : Place D k) (x : k) (a : D.host.E) : p.ι x * (incA D a : AE D) = p.ι (x * p.pr a) := by
  have h : x * p.pr a = p.π (p.ι x * (incA D a : AE D)) := by rw [map_mul, p.π_ι]; rfl
  rw [h, p.ι_π, ← mul_assoc, Witness.e_ι]

theorem map_ι_mul_rat (p : Place D k) {l m : ℕ} {Y : Type} [Fintype Y] (N : Matrix Y (Fin l) k)
    (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι) * (rat M : Matrix (Fin l) (Fin m) (AE D)) = (N * M.map p.pr).map p.ι := by
  ext i j

  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_incA]

theorem fromCols_toCols₁ {Z n : Type} (x : Matrix Z (n ⊕ Fin 0) k) : fromCols x.toCols₁ 0 = x := by
  conv_rhs => rw [← Matrix.fromCols_toCols x]
  congr 1
  ext i j
  exact j.elim0

theorem splitLocalPlace_up_wittExtendByZero_rankZero (p : Place D k) {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (J : JacLev D 0)
    (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin 0)) (hF : p.IsJacFrame J s hh F₀ F) (T : HSp D)
    (FT : Frame k T.rank Z) (x : Matrix Z n k) :
    J.d.ext0 T (p.up F₀ FT x) = p.up F FT (fromCols x 0) := by
  have hq : J.d.q0 * J.d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact J.d.p0_j0)
  have hq' : J.d.q0.map p.pr * J.d.i₀.map p.pr = 1 := by
    rw [← show (J.d.q0 * J.d.i₀).map p.pr = J.d.q0.map p.pr * J.d.i₀.map p.pr from Matrix.map_mul (f := Witness.prH p), hq]
    exact Matrix.map_one _ (map_zero (Witness.prH p)) (map_one (Witness.prH p))
  have hβ : F.β.toCols₁ = J.d.i₀.map p.pr * F₀.β := by ext r a; exact hF.2.1 r a
  have h1 : F.β * F.γ = 1 := F.βγ
  have h0 : F.β.toCols₂ * F.γ.toRows₂ = 0 := by ext i j; simp [Matrix.mul_apply]
  rw [← Matrix.fromCols_toCols F.β, ← Matrix.fromRows_toRows F.γ, Matrix.fromCols_mul_fromRows, h0, add_zero, hβ] at h1
  have hγ : F.γ.toRows₁ = F₀.γ * J.d.q0.map p.pr := by
    have e : F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) = F.γ.toRows₁ := by
      rw [show F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) =
          F₀.γ * (J.d.q0.map p.pr * J.d.i₀.map p.pr) * F₀.β * F.γ.toRows₁ by simp only [Matrix.mul_assoc],
        hq', Matrix.mul_one, F₀.γβ, Matrix.one_mul]
    rw [← e, h1, Matrix.mul_one]
  rw [HypDec.matrixExtendByZero_apply]
  unfold Place.up
  rw [HypDec.p0, map_ι_mul_rat]
  congr 1
  conv_rhs => rw [← Matrix.fromRows_toRows F.γ, Matrix.mul_assoc, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero, hγ]
  simp only [Matrix.mul_assoc]

theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w w' : WO S₀ T) :
    symplO S T (d.ext0 T w) (d.ext0 T w') = symplO S₀ T w w' := by
  have h := d.hO_ext T 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  unfold symplO
  rw [h]

theorem wittExtensionByZero_preserves_isHalf {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) {e : AE D} {y : WO S₀ T} (hy : IsHalf e y) :
    IsHalf e (d.ext0 T y) := fun i j => by
  rw [HypDec.matrixExtendByZero_apply, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hy i l]

end GlobalTheory.LocMod.RankZeroSrc

namespace GlobalTheory.LocMod.RankZeroSrc

theorem localModel_rankZeroWitt_source_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (J : JacLev D 0) (s hh : k) (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) (F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin 0)), p.IsJacFrame J s hh F₀ F → ∀ (T : HSp D) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (Tm : SB (Matrix Z (n ⊕ Fin 0) k) →ₗ[ℂ] (WO J.W T → ℂ)), p.IsModel ψ F FT Tm → ∃ T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ), p.IsModel ψ F₀ FT T₂ ∧ ∀ (Ψ : SB (Matrix Z n k)) (Φ : SB (Matrix Z (n ⊕ Fin 0) k)), (∀ x, Ψ.1 x = Φ.1 (fromCols x 0)) → ∀ w, T₂ Ψ w = Tm Φ (J.d.ext0 T w) := by
  intro D k _ _ _ _ p ψ hψ J s hh n Z _ _ _ _ F₀ F hF T FT Tm hM
  have hT := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ J.W J.W₀ T J.d hψ
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z) (n' := n ⊕ Fin 0)
  have hc1 : Continuous fun x : Matrix Z (n ⊕ Fin 0) k => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => by
      show Continuous fun a : Matrix Z (n ⊕ Fin 0) k => a i (Sum.inl j)
      exact (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix Z n k => (fromCols x 0 : Matrix Z (n ⊕ Fin 0) k) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · show Continuous fun a : Matrix Z n k => a i j
        exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  let R : SB (Matrix Z n k) → SB (Matrix Z (n ⊕ Fin 0) k) := fun Ψ =>
    ⟨fun x => Ψ.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 fromCols_toCols₁⟩
  have hR : ∀ Ψ x, (R Ψ).1 x = Ψ.1 x.toCols₁ := fun _ _ => rfl
  let T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ) :=
    { toFun := fun Ψ w => Tm (R Ψ) (J.d.ext0 T w)
      map_add' := fun Ψ Ψ' => by
        funext w
        rw [show R (Ψ + Ψ') = R Ψ + R Ψ' from Subtype.ext rfl, map_add (f := _)]
        rfl
      map_smul' := fun c Ψ => by
        funext w
        rw [show R (c • Ψ) = c • R Ψ from Subtype.ext rfl, map_smul]
        rfl }
  have hT₂ : ∀ Ψ w, T₂ Ψ w = Tm (R Ψ) (J.d.ext0 T w) := fun _ _ => rfl
  have hup : ∀ x, p.up F FT x = J.d.ext0 T (p.up F₀ FT x.toCols₁) := fun x => by
    rw [splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT, fromCols_toCols₁]
  refine ⟨T₂, ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun Ψ Φ h w => ?_⟩
  · exact (hT.2.2.1 (Tm (R Ψ))).2 (hM.theta _)
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (p.up F FT (fromCols x 0)) (Tm (R Ψ)) := hM.trans _ _ _ fun t => by
      rw [hR, hR, h]
      congr 1
    funext w
    rw [hT₂, e1, ← splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add (f := _)]
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (J.d.ext0 T y) (Tm (R Ψ)) := hM.modul _ (wittExtensionByZero_preserves_isHalf J.d T hy) _ _ fun t => by
      rw [hR, hR, h, hup, wittExtensionByZero_symplectic_form_eq]
    funext w
    rw [hT₂, e1]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add (f := _)]
  · rw [hT₂, show R Ψ = Φ from Subtype.ext (funext fun x => by rw [hR, h, fromCols_toCols₁])]

end GlobalTheory.LocMod.RankZeroSrc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indicator_hom_selfDual_components_schwartzBruhat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → latInd ΛS ΛT ∈ SB (Matrix n n' k) := by
  first | exact @GlobalTheory.FinPl.latInd_mem_SB_of_selfDual | exact GlobalTheory.FinPl.latInd_mem_SB_of_selfDual | (intros; apply GlobalTheory.FinPl.latInd_mem_SB_of_selfDual <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  first | exact @GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd | exact GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd | (intros; apply GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel

theorem _root_.GlobalTheory.T.iwasawa_decomposition_selfDual_wittSplit_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → IsSelfDualC S₀ L₀ → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), ∃ κ, InK S L (· = v) κ ∧ h = n * d.levi t * d.emb0 γ * κ := by
  first | exact @GlobalTheory.IwaPlace.iwasawa_at_place | exact GlobalTheory.IwaPlace.iwasawa_at_place | (intros; apply GlobalTheory.IwaPlace.iwasawa_at_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  first | exact @GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off | exact GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off | (intros; apply GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nsmul_mem_homLattice_of_integral_frameCoords : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int | exact GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int | (intros; apply GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int <;> assumption)
end
