module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle324
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianVolumeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityBoundUnramified
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem isCompact_mt_preimage (V : HSp D) {T : Set (Mx D V.rank V.rank)} (hT : IsCompact T) :
    IsCompact {g : GA D V | mt V g ∈ T} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, i4, -⟩ := top_mx (D := D) V.rank V.rank
  have i1 : T1Space (Mx D V.rank V.rank) := @T2Space.t1Space _ _ i4
  have he : Topology.IsClosedEmbedding (fun g : GA D V =>
      Units.embedProduct (Mx D V.rank V.rank) (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g)) :=
    Units.isClosedEmbedding_embedProduct.comp (isClosedEmbedding_matHom_GAd D.sp.cm.sig V.gram)
  have hc : Continuous fun X : Mx D V.rank V.rank => giA V * (adj X * gA V) :=
    continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)
  have hK := he.isCompact_preimage (hT.prod ((hT.image hc).image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (hT.isClosed.preimage (continuous_mt V)) fun g hg => ?_
  refine ⟨hg, _, ⟨mt V g, hg, rfl⟩, ?_⟩
  simp only [Units.embedProduct_apply]
  rw [← GlobalTheory.MixModel.mt_inv]; rfl

theorem det_ne_zero {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} {b : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hb : b.det ≠ 0) (h : gramQ W x₀ = b) : x₀.det ≠ 0 := by
  intro h0
  apply hb
  rw [← h, gramQ]
  simp [Matrix.det_mul, h0]

theorem rat_inv_mul {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀⁻¹) (rat x₀) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem rat_mul_inv {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀) (rat x₀⁻¹) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem join_first_second_columns_eq (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with s | s <;> simp [jn, c1, c2]

theorem continuous_jn (hn : W.rank + t = n) {a : ℕ} :
    Continuous fun p : Mx D a W.rank × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with s | s
  · exact (continuous_fst.matrix_elem i s)
  · exact (continuous_snd.matrix_elem i s)

theorem box_rec (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    mm d.p0 (mm d.jX u + mm d.j0 w) = w ∧ mm d.pX (mm d.jX u + mm d.j0 w) = u := by
  constructor
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.p0_j0,
      Matrix.zero_mul, Matrix.one_mul, zero_add]
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, d.pX_j0,
      Matrix.zero_mul, Matrix.one_mul, add_zero]

theorem zp_rec (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (p : Par D n t W) :
    mm d.p0 (zp d hn x₀ p).1 = ww W x₀ p.1 ∧ mm d.pX (zp d hn x₀ p).1 = c1 hn p.2.1 ∧
      mm d.p0 (zp d hn x₀ p).2 = mm (ww W x₀ p.1) p.2.2 ∧
      mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2) = c2 hn p.2.1 := by
  obtain ⟨h1, h2⟩ := box_rec (a := W.rank) d (c1 hn p.2.1) (ww W x₀ p.1)
  refine ⟨h1, h2, ?_, ?_⟩
  · change mm d.p0 (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1)) = _
    simp only [mm] at h1 ⊢
    rw [Matrix.mul_add, ← Matrix.mul_assoc d.p0 _ p.2.2, h1, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  · change mm d.pX (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1) -
      mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2) = _
    rw [add_sub_cancel_left, mm, mm, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

theorem ac_ac (V : HSp D) {a b : ℕ} (g : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V g (ac V g⁻¹ z) = z := by
  have e : ∀ {c : ℕ} (x : Mx D V.rank c), mm (mt V g) (mm (mt V g⁻¹) x) = x := fun x => by
    rw [mm, mm, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul]
  exact Prod.ext (e z.1) (e z.2)

theorem exists_box (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (hx : x₀.det ≠ 0)
    {C : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hC : IsCompact C) :
    ∃ (Ah : Set (GA D W)) (AU : Set (Mx D t n)) (Ay : Set (Mx D W.rank t)),
      IsCompact Ah ∧ IsCompact AU ∧ IsCompact Ay ∧ ∀ (k : I.l.K) (p : Par D n t W),
        ac B ((k : GA D B)⁻¹) (zp d hn x₀ p) ∈ C → p.1 ∈ Ah ∧ p.2.1 ∈ AU ∧ p.2.2 ∈ Ay := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨t1, -, -, -, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨t2, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨t3, -, -, -, -⟩ := top_mx (D := D) t W.rank
  obtain ⟨t4, -, -, -, -⟩ := top_mx (D := D) t t
  set C' : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    (fun u : GA D B × (Mx D B.rank W.rank × Mx D B.rank t) => ac B u.1 u.2) '' ((I.l.K : Set (GA D B)) ×ˢ C) with hC'
  have cC' : IsCompact C' := (I.good.isCompact_K.prod hC).image (continuous_ac B)
  set Aw : Set (Mx D W.rank W.rank) := (fun z : Mx D B.rank W.rank × Mx D B.rank t => mm d.p0 z.1) '' C' with hAw
  have cAw : IsCompact Aw := cC'.image (continuous_const.matrix_mul continuous_fst)
  set T : Set (Mx D W.rank W.rank) := (fun X : Mx D W.rank W.rank => mm X (rat x₀⁻¹)) '' Aw with hT
  have cT : IsCompact T := cAw.image (continuous_id.matrix_mul continuous_const)
  set Ah : Set (GA D W) := (fun g : GA D W => g⁻¹) '' {g : GA D W | mt W g ∈ T} with hAh
  have cAh : IsCompact Ah := (isCompact_mt_preimage W cT).image continuous_inv
  set Ay : Set (Mx D W.rank t) :=
    (fun u : GA D W × (Mx D B.rank W.rank × Mx D B.rank t) => mm (rat x₀⁻¹) (mm (mt W u.1) (mm d.p0 u.2.2))) ''
      (Ah ×ˢ C') with hAy
  have cAy : IsCompact Ay := (cAh.prod cC').image (continuous_const.matrix_mul
    (((continuous_mt W).comp continuous_fst).matrix_mul
      (continuous_const.matrix_mul (continuous_snd.comp continuous_snd))))
  set AU : Set (Mx D t n) :=
    (fun u : (Mx D B.rank W.rank × Mx D B.rank t) × Mx D W.rank t =>
      jn hn (mm d.pX u.1.1) (mm d.pX (u.1.2 - mm u.1.1 u.2))) '' (C' ×ˢ Ay) with hAU
  have s2 : ContinuousSub (Mx D B.rank t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ t2
  have cAU : IsCompact AU := (cC'.prod cAy).image ((continuous_jn (W := W) hn).comp
    ((continuous_const.matrix_mul (continuous_fst.comp continuous_fst)).prodMk
      (continuous_const.matrix_mul ((continuous_snd.comp continuous_fst).sub
        ((continuous_fst.comp continuous_fst).matrix_mul continuous_snd)))))
  refine ⟨Ah, AU, Ay, cAh, cAU, cAy, fun k p hp => ?_⟩
  have e1 := rat_mul_inv hx
  have e2 := rat_inv_mul hx
  simp only [mm] at e1 e2
  have hz : zp d hn x₀ p ∈ C' := ⟨((k : GA D B), ac B ((k : GA D B)⁻¹) (zp d hn x₀ p)), ⟨k.2, hp⟩, ac_ac B _ _⟩
  obtain ⟨r1, r2, r3, r4⟩ := zp_rec d hn x₀ p
  have hw : ww W x₀ p.1 ∈ Aw := ⟨_, hz, r1⟩
  have hg : mt W p.1⁻¹ ∈ T := ⟨_, hw, by
    change mm (mm (mt W p.1⁻¹) (rat x₀)) (rat x₀⁻¹) = _
    simp only [mm]
    rw [Matrix.mul_assoc, e1, Matrix.mul_one]⟩
  have hh : p.1 ∈ Ah := ⟨p.1⁻¹, hg, inv_inv _⟩
  have hy : p.2.2 ∈ Ay := ⟨(p.1, zp d hn x₀ p), ⟨hh, hz⟩, by
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm d.p0 (zp d hn x₀ p).2)) = _
    rw [r3]
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm (mm (mt W p.1⁻¹) (rat x₀)) p.2.2)) = _
    simp only [mm]
    rw [← Matrix.mul_assoc (mt W p.1), ← Matrix.mul_assoc (mt W p.1),
      GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, ← Matrix.mul_assoc, e2, Matrix.one_mul]⟩
  have hU : p.2.1 ∈ AU := ⟨(zp d hn x₀ p, p.2.2), ⟨hz, hy⟩, by
    change jn hn (mm d.pX (zp d hn x₀ p).1) (mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2)) = _
    rw [r2, r4, join_first_second_columns_eq]⟩
  exact ⟨hh, hU, hy⟩

end GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem isFiniteMeasureOnCompacts_nuT : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → IsFiniteMeasureOnCompacts (nuT hn I μ x₀) := by
  intro D n t B W d hn I μ hμ b₀ hb x₀ hx
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, -, k4, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, -, l4, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := 𝓕
  have := I.haar
  have := I.probK
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have := sigmaFinite_parameter_product_measure I μ hμ
  refine ⟨fun C hC => ?_⟩
  obtain ⟨Ah, AU, Ay, cAh, cAU, cAy, h⟩ := Cpt.exists_box d hn I (Cpt.det_ne_zero hb hx) hC
  rw [nuT, Measure.map_apply (measurable_pi hn I x₀) hC.measurableSet]
  have hsub : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹' C ⊆
      Set.univ ×ˢ (Ah ×ˢ (AU ×ˢ Ay)) := fun p hp => by
    obtain ⟨a, b, c⟩ := h p.1 p.2 hp
    exact ⟨trivial, a, b, c⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [Q0, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) (ENNReal.mul_lt_top cAh.measure_lt_top
    (ENNReal.mul_lt_top cAU.measure_lt_top cAy.measure_lt_top))

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.LocPhiUnit

section Fixed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
  (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

theorem exists_inclPlus_half (z : k ⊗[maximalRealSubfield E] Fld Q) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q,
      inclPlus Q k a = ((1 : k) ⊗ₜ[maximalRealSubfield E] (2⁻¹ : Fld Q)) * (z + involBase Q k z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨(y + invol Q y) / 2, ?_⟩, ?_⟩
    · change invol Q _ = _
      simp only [map_div₀, map_add (f := _), invol_invol, map_ofNat, AlgHom.id_apply, add_comm]
    · change s ⊗ₜ[maximalRealSubfield E] ((y + invol Q y) / 2) = _ * (s ⊗ₜ y + s ⊗ₜ invol Q y)
      rw [← TensorProduct.tmul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_inv_mul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add (f := _), ha, hb, map_add (f := _)]
    ring

theorem exists_inclPlus_of_fixed {z : k ⊗[maximalRealSubfield E] Fld Q} (hz : involBase Q k z = z) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q, inclPlus Q k a = z := by
  obtain ⟨a, ha⟩ := exists_inclPlus_half Q k z
  refine ⟨a, ?_⟩
  have h2 : (2 : k ⊗[maximalRealSubfield E] Fld Q) = (1 : k) ⊗ₜ[maximalRealSubfield E] (2 : Fld Q) :=
    (map_ofNat (Algebra.TensorProduct.includeRight :
      Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q) 2).symm
  rw [ha, hz, ← two_mul, ← mul_assoc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    inv_mul_cancel₀ two_ne_zero, ← Algebra.TensorProduct.one_def, one_mul]

theorem inclPlus_injective : Function.Injective (inclPlus Q k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (plus Q).val.toLinearMap
    Subtype.val_injective

theorem exists_unit_of_fixed {y : k ⊗[maximalRealSubfield E] Fld Q} (hu : IsUnit y)
    (hy : involBase Q k y = y) :
    ∃ x : (k ⊗[maximalRealSubfield E] plus Q)ˣ,
      inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = y := by
  obtain ⟨u, rfl⟩ := hu
  have hinv : involBase Q k ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) :
      k ⊗[maximalRealSubfield E] Fld Q) = (u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) := by
    have h1 : (u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
        ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.mul_inv, map_one]
    calc _ = ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) *
          ((u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
            ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q)) := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [h1, mul_one]
  obtain ⟨a, ha⟩ := exists_inclPlus_of_fixed Q k hy
  obtain ⟨b, hb⟩ := exists_inclPlus_of_fixed Q k hinv
  have hab : a * b = 1 := inclPlus_injective Q k (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Fixed

section Matrix

theorem aeval_mul_of_intertwine {K : Type} [Field K] {n : ℕ} {B C H : Matrix (Fin n) (Fin n) K}
    (h : B * H = H * C) (g : K[X]) : aeval B g * H = H * aeval C g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial d a =>
    have e : B ^ d * H = H * C ^ d :=
      (((show SemiconjBy H C B from h.symm).pow_right d).eq).symm
    rw [aeval_monomial, aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_assoc, e]

theorem cT_mul {K : Type} [Field K] (s : K →+* K) {n : ℕ} (B C : Matrix (Fin n) (Fin n) K) :
    cT s (B * C) = cT s C * cT s B := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

end Matrix

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem involBase_locPhi (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    {r : ℕ} (Q : SelfRecip E r) {r₀ : E[X]} (hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0)
    (f : (w.adicCompletion E)[X]) :
    involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q f) =
      locPhi hU w hw v hv Q ((f.map (cj w)).comp (atPl w r₀)) := by
  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (inclBase Q k).toRingHom.comp (locJ hU w hw v hv).toRingHom
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (locJ hU w hw v hv y)) =
      inclBase Q k (locJ hU w hw v hv (cj w y))
    rw [locJ_cj]
    generalize locJ hU w hw v hv y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (involBase Q k).toRingHom
  have hR : locPhi hU w hw v hv Q (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [locPhi_atPl]
    congr 1
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at hr
    exact eq_inv_of_mul_eq_one_right hr
  have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
  have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    change (1 : k) ⊗ₜ invol Q (alpha Q) = _
    rw [invol_alpha]
  change ib (eval₂ ι _ f) = eval₂ ι _ _
  rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
  exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm

end Local

theorem locPhi_mem_units_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ hH hdet h3 m hM hMdet r Q hQ
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
  obtain ⟨A, hA⟩ : ∃ A, A = γ₀.val.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H, H = H₀.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  rw [← hA, ← hHd] at hM hMdet
  obtain ⟨M, hMd⟩ : ∃ M, M = aeval A m := ⟨_, rfl⟩
  rw [← hMd] at hM hMdet
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := by rw [hA]; exact Matrix.charpoly_map _ _
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hHh : cT (cj w) H = H := by
    rw [hHd, ← cT_map hU w hw]
    exact congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hH
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h3
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    rw [hA, hHd]
    exact this
  have hint : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hH0 : IsUnit H := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at *
    exact (left_ne_zero_of_mul hMdet).isUnit
  have hM0 : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [Matrix.det_mul] at hMdet
    exact (right_ne_zero_of_mul hMdet).isUnit
  have hfix : M = aeval A ((m.map (cj w)).comp (atPl w r₀)) := by
    have h1 : cT (cj w) M * H = H * M := by
      have := hM
      rw [IsHerm, cT_mul, hHh] at this
      exact this
    rw [hMd, GlobalTheory.NormInert.cT_aeval, aeval_mul_of_intertwine hint, ← aeval_comp, ← hMd] at h1
    exact (hH0.mul_left_cancel h1).symm
  have hdiv : A.charpoly ∣ (m.map (cj w)).comp (atPl w r₀) - m :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by rw [map_sub, ← hfix, ← hMd, sub_self])
  have hΦ0 : locPhi hU w hw v hv Q A.charpoly = 0 := by
    rw [hAP, locPhi_atPl]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hy : involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q m) =
      locPhi hU w hw v hv Q m := by
    obtain ⟨t, ht⟩ := hdiv
    rw [involBase_locPhi hU w hw v hv Q hr, ← sub_eq_zero, ← map_sub, ht, map_mul, hΦ0, zero_mul]
  obtain ⟨u, hu⟩ := hM0
  have hcomm : Commute A (u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hu, hMd]
    have := congrArg (aeval A) (mul_comm (X : (w.adicCompletion E)[X]) m)
    rw [map_mul, map_mul, aeval_X] at this
    exact this
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A
    ((u⁻¹ : (Matrix (Fin n) (Fin n) (w.adicCompletion E))ˣ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    hAsep hcomm.units_inv_right.eq
  have hdiv2 : A.charpoly ∣ m * g - 1 :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by
      rw [map_sub, map_mul, ← hg, ← hMd, ← hu, Units.mul_inv, map_one, sub_self])
  have hone : locPhi hU w hw v hv Q m * locPhi hU w hw v hv Q g = 1 := by
    obtain ⟨t, ht⟩ := hdiv2
    rw [← map_mul, ← sub_eq_zero, ← map_one (locPhi hU w hw v hv Q), ← map_sub, ht, map_mul, hΦ0,
      zero_mul]
  exact exists_unit_of_fixed Q _ (isUnit_iff_exists_inv.2 ⟨_, hone⟩) hy

end GlobalTheory.CompanionTheory.LocPhiUnit

end
end

section


theorem _root_.GlobalTheory.T.coset_measure_formula : PositivityTheory.SiegelWeilFormula.Gunr.CosetMeas := by
  first | exact @GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | exact GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | (intros; apply GlobalTheory.CompanionTheory.GunrCoset.cosetMeas <;> assumption)
end

section


theorem _root_.GlobalTheory.T.multiplicity_power_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  first | exact @GlobalTheory.CompanionTheory.GunrNu.nuPow | exact GlobalTheory.CompanionTheory.GunrNu.nuPow | (intros; apply GlobalTheory.CompanionTheory.GunrNu.nuPow <;> assumption)
end

section


theorem _root_.GlobalTheory.T.residue_ring_structure : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  first | exact @GlobalTheory.CompanionTheory.RvRingPf.rvRing | exact GlobalTheory.CompanionTheory.RvRingPf.rvRing | (intros; apply GlobalTheory.CompanionTheory.RvRingPf.rvRing <;> assumption)
end

section


theorem _root_.GlobalTheory.T.tsum_exhaustion_unramified : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  first | exact @GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | exact GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | (intros; apply GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop <;> assumption)
end

section


theorem _root_.GlobalTheory.T.uniformizer_existence : PositivityTheory.SiegelWeilFormula.Gunr.UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.LocalUnif.unifEx | exact GlobalTheory.CompanionTheory.LocalUnif.unifEx | (intros; apply GlobalTheory.CompanionTheory.LocalUnif.unifEx <;> assumption)
end

section


theorem _root_.GlobalTheory.T.integral_hermitian_volume_one : PositivityTheory.SiegelWeilFormula.Gunr.HermitianLatticeVolumeOne := by
  first | exact @GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one | exact GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one | (intros; apply GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.multiplicity_bound_unramified : PositivityTheory.SiegelWeilFormula.Gunr.NuBound := by
  first | exact @GlobalTheory.CompanionTheory.GunrNuBound.nuBound | exact GlobalTheory.CompanionTheory.GunrNuBound.nuBound | (intros; apply GlobalTheory.CompanionTheory.GunrNuBound.nuBound <;> assumption)
end
