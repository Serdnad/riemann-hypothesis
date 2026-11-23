module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem jn_smul (hn : r + t = n) (e : AE D) (x : Mx D a r) (v : Mx D a t) :
    e • jn hn x v = jn hn (e • x) (e • v) := by
  ext i j
  simp only [jn, Matrix.smul_apply, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem intOff_jn (hn : r + t = n) {S : Finset (Pl D)} (x : Mx D a r) (v : Mx D a t) :
    IntOff S (jn hn x v) ↔ IntOff S x ∧ IntOff S v := by
  constructor
  · intro h
    refine ⟨fun w hw i j => ?_, fun w hw i j => ?_⟩
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))
      simpa [jn] using this
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))
      simpa [jn] using this
  · rintro ⟨h1, h2⟩ w hw i j
    simp only [jn, Matrix.submatrix_apply, id]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
    · exact h1 w hw i j
    · exact h2 w hw i j

theorem continuous_jn (hn : r + t = n) : Continuous (fun z : Mx D a r × Mx D a t => jn hn z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
  · exact continuous_fst.matrix_elem i j
  · exact continuous_snd.matrix_elem i j

def cutc (hn : r + t = n) (X : Mx D a n) : Mx D a r × Mx D a t :=
  (X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inl j),
    X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))

theorem continuous_cutc (hn : r + t = n) : Continuous (cutc (D := D) (a := a) hn) := by
  refine Continuous.prodMk ?_ ?_ <;> exact continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem cutc_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : cutc hn (jn hn x v) = (x, v) := by
  refine Prod.ext ?_ ?_ <;> ext i j <;> simp [cutc, jn]

theorem intOff_smul {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (x : Mx D a b) : IntOff S (e • x) := by
  intro v hv i j
  have h0 : cv D v e = 0 := by rw [hS.2 v, ite_eq_right hv]
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h0, zero_mul]
  exact zero_mem _

theorem adj_smul {e : AE D} (hc : cA D e = e) (x : Mx D a b) : adj (e • x) = e • adj x := by
  ext i j
  simp [adj, hc]

theorem ip_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem yv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he hc, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem qv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, ip_smul he hc, yv_smul he hc, pr_smul he hc, smul_sub]

theorem pch_smul {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {x : Mx D t t} (hx : e • x = x) (T : Mx D t t) :
    pch ψ x (e • T) = pch ψ x T := by
  have : mm x (e • T) = mm x T := by
    conv_rhs => rw [← hx]
    simp only [mm, Matrix.smul_mul, Matrix.mul_smul]
  simp only [pch, this]

theorem isOrb_smul {V : HSp D} {b₀ : HermE D r} {e : AE D} {ν : Measure (Mx D V.rank r × Mx D V.rank t)}
    (h : IsOrb V b₀ e ν) (c : ℝ≥0) : IsOrb V b₀ e (c • ν) := by
  have := h.fin
  have : SecondCountableTopologyEither (Mx D V.rank r) (Mx D V.rank t) :=
    ⟨Or.inl (lattice_Mx D V.rank r).2.2.1⟩
  have : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  have : BorelSpace (Mx D V.rank r × Mx D V.rank t) := Prod.borelSpace
  have : OpensMeasurableSpace (Mx D V.rank r × Mx D V.rank t) := BorelSpace.opensMeasurable
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.supp, smul_zero]
  · intro g hg
    rw [Measure.map_smul, h.invU g hg]
    apply Continuous.aemeasurable
    exact (continuous_const.matrix_mul continuous_fst).prodMk
      (continuous_const.matrix_mul continuous_snd)
  · intro y hy
    rw [Measure.map_smul, h.invS y hy]
    apply Continuous.aemeasurable
    exact continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  · intro g hg
    rw [Measure.map_smul, h.cov g hg, smul_comm]
    apply Continuous.aemeasurable
    exact continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)

theorem isOrb_zero {V : HSp D} {b₀ : HermE D r} {e : AE D} : IsOrb (t := t) V b₀ e 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩ <;> simp

end GlobalTheory.CompanionTheory.EisE

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

theorem adj_rat_herm (b₀ : HermE D r) : adj (rat b₀.1) = rat b₀.1 := by
  have hb := b₀.2
  ext i j
  have h2 : D.sp.cm.sig (b₀.1 j i) = b₀.1 i j := by
    have := congrFun (congrFun hb i) j
    simpa using this
  change cA D (incA D (b₀.1 j i)) = incA D (b₀.1 i j)
  rw [← h2]
  rfl

theorem rat_inv_mul (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := by
  have h : b₀.1⁻¹ * b₀.1 = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

theorem rat_mul_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1) (rat b₀.1⁻¹) = (1 : Mx D r r) := by
  have h : b₀.1 * b₀.1⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

theorem adj_ip (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) : adj (ip V x y) = ip V y x := by
  unfold ip mm
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem adj_add_r (x y : Mx D a b) : adj (x + y) = adj x + adj y := by
  ext i j
  simp [adj]

theorem adj_one_r : adj (1 : Mx D a a) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [adj]
  · have h' : j ≠ i := fun q => h q.symm
    simp [adj, Matrix.one_apply, h, h']

theorem adj_rat_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : adj (rat b₀.1⁻¹) = rat b₀.1⁻¹ := by
  have h1 : adj (mm (rat b₀.1⁻¹) (rat b₀.1)) = 1 := by rw [rat_inv_mul b₀ hb, adj_one_r]
  have h2 : mm (rat b₀.1) (adj (rat b₀.1⁻¹)) = 1 := by
    have := h1
    simp only [mm] at this ⊢
    rwa [adj_mul, adj_rat_herm] at this
  have h3 := congrArg (fun M : Mx D r r => mm (rat b₀.1⁻¹) M) h2
  simp only [mm] at h3
  have h4 : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := rat_inv_mul b₀ hb
  simp only [mm] at h4
  rwa [← Matrix.mul_assoc, h4, Matrix.one_mul, Matrix.mul_one] at h3

theorem ip_add_right (V : HSp D) (x : Mx D V.rank a) (y y' : Mx D V.rank b) :
    ip V x (y + y') = ip V x y + ip V x y' := by
  unfold ip mm
  rw [Matrix.mul_add, Matrix.mul_add]

theorem ip_add_left (V : HSp D) (x x' : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (x + x') y = ip V x y + ip V x' y := by
  unfold ip mm
  rw [adj_add_r, Matrix.add_mul]

theorem ip_mul_right (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D b c) :
    ip V x (mm y w) = mm (ip V x y) w := by
  unfold ip mm
  simp only [Matrix.mul_assoc]

theorem ip_mul_left (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D a c) :
    ip V (mm x w) y = mm (adj w) (ip V x y) := by
  unfold ip mm
  rw [adj_mul, Matrix.mul_assoc]

theorem ip_smul_right (V : HSp D) (e : AE D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V x (e • y) = e • ip V x y := by
  unfold ip mm
  rw [Matrix.mul_smul, Matrix.mul_smul]

theorem qv_mem (V : HSp D) (b₀ : HermE D r) (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ z ∈ hermA D t := by
  change adj (qv V b₀ z) = qv V b₀ z
  have hp : adj (pr b₀ (yv V b₀ z) (yv V b₀ z)) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
    unfold pr
    rw [hr, adj_mul, adj_mul, adj_adj, adj_rat_herm, Matrix.mul_assoc]
  have hs : ∀ x y : Mx D t t, adj (x - y) = adj x - adj y := by
    intro x y
    ext i j
    simp [adj]
  unfold qv
  rw [hs, hp, adj_ip]

theorem yv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • yv V b₀ z = yv V b₀ z := by
  unfold yv
  conv_rhs => rw [← h, ip_smul_right]
  simp only [mm]
  rw [Matrix.mul_smul]

theorem qv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • qv V b₀ z = qv V b₀ z := by
  have h1 : e • ip V z.2 z.2 = ip V z.2 z.2 := by
    have := ip_smul_right V e z.2 z.2
    rw [h] at this
    exact this.symm
  have h2 : e • pr b₀ (yv V b₀ z) (yv V b₀ z) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    unfold pr
    rw [← Matrix.mul_smul, ← Matrix.mul_smul, yv_smul V b₀ e z h]
  unfold qv
  rw [smul_sub, h1, h2]

theorem pr_add (b₀ : HermE D r) (u u' w w' : Mx D r t) :
    pr b₀ (u + u') (w + w') = pr b₀ u w + pr b₀ u w' + (pr b₀ u' w + pr b₀ u' w') := by
  unfold pr
  rw [adj_add_r, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]

theorem alg4 {M : Type} [AddCommGroup M] (c p a a' s : M) :
    c + a + (a' + s) - (p + a + (a' + s)) = c - p := by abel

theorem qv_shear (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t)
    (y : Mx D r t) (hG : ip V z₁ z₁ = e • rat b₀.1) (hy : e • y = y) :
    qv V b₀ (z₁, z₂ + mm z₁ y) = qv V b₀ (z₁, z₂) := by
  have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
  have hGy : mm (ip V z₁ z₁) y = mm (rat b₀.1) y := by
    rw [hG]
    simp only [mm]
    rw [Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hyv : yv V b₀ (z₁, z₂ + mm z₁ y) = yv V b₀ (z₁, z₂) + y := by
    unfold yv
    simp only
    rw [ip_add_right, ip_mul_right, hGy]
    simp only [mm]
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    have := rat_inv_mul b₀ hb
    simp only [mm] at this
    rw [this, Matrix.one_mul]
  have hPi := rat_inv_mul b₀ hb
  have hPi' := rat_mul_inv b₀ hb
  have hu : adj (yv V b₀ (z₁, z₂)) = mm (ip V z₂ z₁) (rat b₀.1⁻¹) := by
    unfold yv
    simp only [mm]
    rw [adj_mul, adj_rat_inv b₀ hb, adj_ip]
  have hpu : ∀ w : Mx D r t, pr b₀ (yv V b₀ (z₁, z₂)) w = mm (ip V z₂ z₁) w := by
    intro w
    unfold pr
    rw [hu, hr]
    simp only [mm] at hPi ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rat b₀.1⁻¹), hPi, Matrix.one_mul]
  have hpu' : ∀ w : Mx D r t, pr b₀ w (yv V b₀ (z₁, z₂)) = mm (adj w) (ip V z₁ z₂) := by
    intro w
    unfold pr yv
    rw [hr]
    simp only [mm] at hPi' ⊢
    rw [← Matrix.mul_assoc (rat b₀.1), hPi', Matrix.one_mul]
  have hpyy : pr b₀ y y = mm (adj y) (mm (ip V z₁ z₁) y) := by
    rw [hGy, pr, hr]
  unfold qv
  rw [hyv]
  simp only
  rw [pr_add, hpu (yv V b₀ (z₁, z₂)), hpu y, hpu', hpyy, ip_add_left, ip_add_right, ip_add_right, ip_mul_left, ip_mul_left,
    ip_mul_right, ip_mul_right]
  exact alg4 _ _ _ _ _

theorem qv_col (V : HSp D) (b₀ : HermE D r) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t) (g : Mx D t t) :
    qv V b₀ (z₁, mm z₂ g) = mm (mm (adj g) (qv V b₀ (z₁, z₂))) g := by
  have hyv : yv V b₀ (z₁, mm z₂ g) = mm (yv V b₀ (z₁, z₂)) g := by
    unfold yv
    simp only
    rw [ip_mul_right]
    simp only [mm]
    rw [Matrix.mul_assoc]
  unfold qv
  rw [hyv]
  simp only
  rw [ip_mul_left, ip_mul_right]
  unfold pr
  simp only [mm]
  rw [adj_mul, Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

theorem pch_conj (ψ : AddChar (AF D.host.F) ℂ) (x q h : Mx D t t) :
    pch ψ x (mm (mm (adj h) q) h) = pch ψ (mm (mm h x) (adj h)) q := by
  unfold pch
  congr 2
  simp only [mm]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.OrbExist

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

theorem mm_jn (hn : r + t = n) (M : Mx D c a) (x : Mx D a r) (v : Mx D a t) :
    mm M (jn hn x v) = jn hn (mm M x) (mm M v) := by
  unfold jn mm
  rw [← Matrix.mul_fromCols]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t) :
    mm (jn hn w v) (bl hn p q s u) = jn hn (mm w p + mm v s) (mm w q + mm v u) := by
  unfold jn PositivityTheory.Rg.Rsw.L.mm
  rw [show bl hn p q s u =
      (Matrix.fromBlocks p q s u).submatrix
        (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm from rfl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem block_mul₂ (hn : r + t = n) (p p' : Mx D r r) (q q' : Mx D r t) (s s' : Mx D t r) (u u' : Mx D t t) :
    (bl hn p q s u * bl hn p' q' s' u' : Matrix (Fin n) (Fin n) (AE D)) =
      bl hn (mm p p' + mm q s') (mm p q' + mm q u') (mm s p' + mm u s') (mm s q' + mm u u') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : r + t = n) :
    bl hn (1 : Mx D r r) (0 : Mx D r t) (0 : Mx D t r) (1 : Mx D t t) = (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem smul_blockMatrix_sub_one (hn : r + t = n) (e : AE D) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t)
    (h₁ : e • (p - 1) = p - 1) (h₂ : e • q = q) (h₃ : e • s = s) (h₄ : e • (u - 1) = u - 1) :
    e • (bl hn p q s u - 1) = bl hn p q s u - 1 := by
  have h : bl hn p q s u - 1 = bl hn (p - 1) q s (u - 1) := by
    rw [← blockRowSubstitution_one hn]
    unfold bl
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
      rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp
  rw [h]
  unfold bl
  ext i j
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp only [Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact congrFun (congrFun h₁ i) j
  · exact congrFun (congrFun h₂ i) j
  · exact congrFun (congrFun h₃ i) j
  · exact congrFun (congrFun h₄ i) j

def shU (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn

def colU (hn : r + t = n) (g : GL (Fin t) (AE D)) : GL (Fin n) (AE D) where
  val := bl hn 1 0 0 g.1
  inv := bl hn 1 0 0 (g⁻¹).1
  val_inv := by
    rw [block_mul₂]
    have : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    have : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn

theorem smul_inv_sub (e : AE D) (g : GL (Fin t) (AE D)) (h : e • (g.1 - 1) = g.1 - 1) :
    e • ((g⁻¹).1 - 1) = (g⁻¹).1 - 1 := by
  have h1 : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (g⁻¹).1 - 1 = - ((g⁻¹).1 * (g.1 - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]
  rw [h2, smul_neg, ← Matrix.mul_smul, h]

theorem trans_int {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X) (c : N ≃ₜ N) (κ₁ κ₂ : ℝ≥0)
    (h₁ : σ.map Θ = κ₁ • σ) (h₂ : lam.map c = κ₂ • lam) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k (c x) (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((κ₁ * κ₂ : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have hin : ∀ x, ∫ z, f (Θ z) * k x z ∂σ = (κ₁ : ℂ) * ∫ z, f z * k (c x) z ∂σ := by
    intro x
    have e₁ : ∫ z, f (Θ z) * k x z ∂σ = ∫ z, (fun w => f w * k (c x) w) (Θ z) ∂σ :=
      integral_congr_ae ((hk x).mono fun z hz => by simp only [hz])
    have e₃ := Θ.measurableEmbedding.integral_map (μ := σ) (fun w => f w * k (c x) w)
    rw [e₁, ← e₃, h₁, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp only [hin]
  rw [integral_const_mul]
  have e₂ : ∫ x, ∫ z, f z * k (c x) z ∂σ ∂lam = ∫ x, (fun u => ∫ z, f z * k u z ∂σ) (c x) ∂lam := rfl
  have e₄ := c.measurableEmbedding.integral_map (μ := lam) (fun u => ∫ z, f z * k u z ∂σ)
  rw [e₂, ← e₄, h₂, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

theorem map_val_rel {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X) (i : X → Y) (Θ : X → X) (T : Y → Y)
    (κ : ℝ≥0) (hi : Measurable i) (hΘ : Measurable Θ) (hT : Measurable T) (hc : ∀ z, i (Θ z) = T (i z)) (h : ν.map Θ = κ • ν) :
    (ν.map i).map T = κ • ν.map i := by
  rw [Measure.map_map hT hi]
  have : T ∘ i = i ∘ Θ := funext fun z => (hc z).symm
  rw [this, ← Measure.map_map hi hΘ, h, Measure.map_smul]
  exact hi.aemeasurable

end GlobalTheory.CompanionTheory.OrbExist

end
end
