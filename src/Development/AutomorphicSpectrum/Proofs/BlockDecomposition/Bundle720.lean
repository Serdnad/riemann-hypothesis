module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle716
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle715
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

open GlobalTheory.EmbChart (tensAt compFin_tensAt)

theorem compFin_tensAt_ne_place {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (y : Fv F v ⊗[F] E) :
    compFin F E u (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    change (evalV F u (singleFin v a)) ⊗ₜ[F] x = 0
    rw [evalV_singleFin_ne h, TensorProduct.zero_tmul]

theorem compInf_tensAt_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    compInf F E w (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    change (evInf F w (GlobalTheory.EmbChart.atPlace v a)) ⊗ₜ[F] x = 0
    rw [show evInf F w (GlobalTheory.EmbChart.atPlace v a) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul]

theorem cA_tensAt (D : D7) (v : Pl D) (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    cA D (tensAt D.host.E v y) = tensAt D.host.E v (sigR (Fv D.host.F v) D.sp.cm.sig y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem splitProj_sigR (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    splitProj τ (sigR (Fv D.host.F v) D.sp.cm.sig y) = splitProj (τ.comp D.sp.cm.sig) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem exists_herm_at (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (X : Matrix (Fin n) (Fin n) (Fv D.host.F v)) :
    ∃ x : hermA D n, (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧
      (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧ tauC τ x.1 = X ∧
      ((∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) →
        ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) := by
  have h := isCMExt_host D
  set M := splitPairMat h τ X Xᵀ with hM
  have p1 : ∀ i j, splitProj τ (M i j) = X i j := fun i j => by
    have := congrArg Prod.fst ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have p2 : ∀ i j, splitProj (τ.comp D.sp.cm.sig) (M i j) = X j i := fun i j => by
    have := congrArg Prod.snd ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have hs : ∀ i j, sigR (Fv D.host.F v) D.sp.cm.sig (M j i) = M i j := fun i j => by
    apply (splitAlgEquiv h τ).injective
    rw [splitAlgEquiv_apply, splitAlgEquiv_apply, splitProj_sigR, splitProj_comp_sigR h, p1, p2, p1, p2]
  have hc : ∀ i j, cv D v (tensAt D.host.E v (M i j)) = M i j := fun i j => compFin_tensAt v _
  refine ⟨⟨Matrix.of fun i j => tensAt D.host.E v (M i j), ?_⟩, ?_, ?_, ?_, ?_⟩
  · change adj _ = _
    ext i j
    change cA D (tensAt D.host.E v (M j i)) = tensAt D.host.E v (M i j)
    rw [cA_tensAt, hs]
  · intro w i j
    exact compInf_tensAt_eq_zero w v _
  · intro v' hv i j
    exact compFin_tensAt_ne_place hv _
  · refine Matrix.ext fun i j => ?_
    change splitProj τ (cv D v (tensAt D.host.E v (M i j))) = X i j
    rw [hc, p1]
  · intro hX i j
    change cv D v (tensAt D.host.E v (M i j)) ∈ _
    rw [hc, mem_intLoc_iff_split h τ, p1, p2]
    exact ⟨hX i j, hX j i⟩

end GlobalTheory.CompanionTheory.Jp

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.UpTri

theorem transpose_block_matrix {A : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A) :
    (GlobalTheory.StdUnn.blk4 a b c d)ᵀ = GlobalTheory.StdUnn.blk4 aᵀ cᵀ bᵀ dᵀ := by
  ext i j
  simp only [GlobalTheory.StdUnn.blk4, Matrix.transpose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blocks_of_unitary {K : Type} [CommRing K] {n : ℕ} (a : GL (Fin n) K) (b d a' b' c' d' : Matrix (Fin n) (Fin n) K)
    (h : (GlobalTheory.StdUnn.blk4 a' b' c' d')ᵀ * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * GlobalTheory.StdUnn.blk4 a.1 b 0 d =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0) : c' = 0 ∧ a'ᵀ * d = 1 := by
  rw [transpose_block_matrix, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  have e1 : c'ᵀ * a.1 = 0 := by simpa using h1
  have e2 : c'ᵀ = 0 := by
    have := congrArg (· * (a⁻¹).1) e1
    simpa [Matrix.mul_assoc, -Matrix.coe_units_inv] using this
  have e3 : c' = 0 := by simpa using congrArg Matrix.transpose e2
  subst e3
  exact ⟨rfl, by simpa using h2⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem upperParabolic_height_of_split (h : IsCMExt F E σ) (hQ : Q = GlobalTheory.StdUnn.blk4 0 1 (-1) 0) (τ : E →ₐ[F] Fv F v)
    (y : GLoc σ Q v) (a d : GL (Fin n) (Fv F v)) (b : Matrix (Fin n) (Fin n) (Fv F v))
    (hy : (splitHom σ Q τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1) :
    ∃ hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q,
      absEv F E v (GlobalTheory.LocIntw.aUp (Fv F v) σ Q ⟨y, hm⟩) = ‖a.1.det‖₊ / ‖d.1.det‖₊ := by
  obtain ⟨A, B, C, D', e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR (Fv F v) σ y)
  have key : ∀ ρ : E →ₐ[F] Fv F v, (splitHom σ Q ρ y).1 =
      GlobalTheory.StdUnn.blk4 (A.map (splitProj ρ)) (B.map (splitProj ρ)) (C.map (splitProj ρ)) (D'.map (splitProj ρ)) := by
    intro ρ
    rw [splitHom_val]
    change (GlobalTheory.LocIntw.matR (Fv F v) σ y).map (splitProj ρ : Fv F v ⊗[F] E →+* Fv F v) = _
    rw [e]
    exact GlobalTheory.LocIntw.blockMatrix_map _ _ _ _ _
  obtain ⟨ha, -, hc, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective ((key τ).symm.trans hy)
  have hQτ : Q.map τ = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    subst hQ
    have := GlobalTheory.LocIntw.blockMatrix_map (τ : E →+* Fv F v) (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0
    rw [Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have u := splitHom_unitary τ y
  rw [key (τ.comp σ), hQτ, hy] at u
  obtain ⟨hc', hd'⟩ := blocks_of_unitary a b d.1 _ _ _ _ u
  have hC : C = 0 := splitMat_ext h τ
    (by rw [hc]; exact (Matrix.map_zero _ (map_zero _)).symm)
    (by rw [hc']; exact (Matrix.map_zero _ (map_zero _)).symm)
  have hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q := (GlobalTheory.LocIntw.mem_siegelParabolic_iff_lowerLeft_eq_zero hQ).2 fun i j => by
    rw [e, hC, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp
  refine ⟨hm, ?_⟩
  have hA : GlobalTheory.StdUnn.blkA (GlobalTheory.LocIntw.matR (Fv F v) σ y) = A := by rw [e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  have d1 : splitProj τ A.det = a.1.det := by
    rw [← ha]
    exact RingHom.map_det (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) A
  have d2 : splitProj (τ.comp σ) A.det * d.1.det = 1 := by
    have : splitProj (τ.comp σ) A.det = (A.map (splitProj (τ.comp σ))).det :=
      RingHom.map_det (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v) A
    rw [this, ← Matrix.det_transpose, ← Matrix.det_mul, hd', Matrix.det_one]
  rw [absEv_apply, GlobalTheory.LocIntw.coe_aUp, hA, GlobalTheory.SplitInterDet.norm_eq_split h τ, nnnorm_mul, d1,
    eq_inv_of_mul_eq_one_left d2, nnnorm_inv, div_eq_mul_inv]

end General

theorem upperParabolic_height (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v))
    (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (H : thU D n v τ y = pM a d b) :
    ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n),
      absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) =
        nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  have hy : (splitHom D.sp.cm.sig (Jst D n) τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1 := by
    have e : ((splitHom D.sp.cm.sig (Jst D n) τ y).1).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks a.1 b 0 d.1 := congrArg Units.val H
    rw [GlobalTheory.StdUnn.blk4, ← e]
    ext i j
    simp
  exact upperParabolic_height_of_split (isCMExt_host D) (GlobalTheory.LocIntw.Jst_eq D n) τ y a d b hy

end GlobalTheory.CompanionTheory.Jp.UpTri

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.ResChar

theorem local_component_additive_character_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have h1 : singleV F v (r + s) = singleV F v r + singleV F v s := by
    classical
    unfold singleV
    first
    | exact Subtype.ext (Pi.single_add v r s)
    | (apply Subtype.ext
       exact Pi.single_add v r s)
    | (apply Subtype.ext
       funext w
       show Pi.single v (r + s) w = Pi.single v r w + Pi.single v s w
       rw [Pi.single_add]
       rfl)
  have h2 : pairA F 0 (singleV F v (r + s)) = pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [h1]
    show ((0 : Ainf F), singleV F v r + singleV F v s) = ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  simp only [psiV]
  rw [h2, AddChar.map_add_eq_mul]

theorem dvd_of_nonunit {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {p x : R}
    (hp : Irreducible p) (hx : ¬ IsUnit x) : p ∣ x := by
  rcases ValuationRing.dvd_total p x with h | ⟨c, hc⟩
  · exact h
  · rcases hp.isUnit_or_isUnit hc with h | h
    · exact absurd h hx
    · exact ⟨↑h.unit⁻¹, by rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ ϖ : Ov D v, Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → ∃ ψ₀ : AddChar (kv D v) ℂ, ψ₀ ≠ 1 ∧ ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) = ψ₀ (IsLocalRing.residue (Ov D v) c) := by
  intro D ψ v hψ ϖ hϖ w hw
  classical
  set f : Ov D v → ℂ := fun c => psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) with hf
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    simp only [hf, map_add (f := _), mul_add]
    exact local_component_additive_character_add ψ v _ _
  have hker : ∀ d, f (ϖ * d) = 1 := by
    intro d
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (ϖ * d) = algebraMap (Ov D v) (Lv D v) d := by
      rw [map_mul, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
    simp only [hf, e]
    exact hψ.1 _ d.2
  have hwd : ∀ a b, IsLocalRing.residue (Ov D v) a = IsLocalRing.residue (Ov D v) b → f a = f b := by
    intro a b h
    have h0 : IsLocalRing.residue (Ov D v) (a - b) = 0 := by rw [map_sub, h, sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    obtain ⟨d, hd⟩ := dvd_of_nonunit hϖ (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm))
    have e : a = b + ϖ * d := by rw [← hd]; ring
    rw [e, hadd, hker, mul_one]
  have hf0 : f 0 = 1 := by simpa using hker 0
  let g : kv D v → Ov D v := fun z => Classical.choose (IsLocalRing.residue_surjective z)
  have hg : ∀ z, IsLocalRing.residue (Ov D v) (g z) = z := fun z =>
    Classical.choose_spec (IsLocalRing.residue_surjective z)
  let ψ₀ : AddChar (kv D v) ℂ :=
    { toFun := fun z => f (g z)
      map_zero_eq_one' := by
        show f (g 0) = 1
        rw [hwd (g 0) 0 (by rw [hg, map_zero]), hf0]
      map_add_eq_mul' := by
        intro z z'
        show f (g (z + z')) = f (g z) * f (g z')
        rw [← hadd]
        exact hwd _ _ (by rw [hg, map_add (f := _), hg, hg]) }
  have hψ₀ : ∀ c, ψ₀ (IsLocalRing.residue (Ov D v) c) = f c := fun c => by
    show f (g _) = f c
    exact hwd _ _ (hg _)
  refine ⟨ψ₀, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
    intro h1
    apply hb
    have e1 : ψ₀ (IsLocalRing.residue (Ov D v) b) = 1 := by rw [h1]; exact AddChar.one_apply _
    rw [hψ₀] at e1
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) b = (b : Fv D.host.F v) / (ϖ : Fv D.host.F v) := by
      rw [Units.val_inv_eq_inv_val, hw, div_eq_inv_mul]; rfl
    rw [← e]
    exact e1
  · intro c
    exact (hψ₀ c).symm

end GlobalTheory.CompanionTheory.Jp.ResChar

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.DualInt

private theorem trace_single_one_mul {n : ℕ} {R : Type} [CommRing R] (i j : Fin n) (c : R)
    (T : Matrix (Fin n) (Fin n) R) : (Matrix.single j i c * T).trace = c * T i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem mem_of_dual_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  intro D ψ v hψ n T hT i j
  by_contra hx
  set O := v.adicCompletionIntegers D.host.F with hO
  have hx0 : T i j ≠ 0 := by
    intro h
    exact hx (h ▸ O.zero_mem)
  have hy : (T i j)⁻¹ ∈ O := (O.mem_or_inv_mem (T i j)).resolve_left hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : v.adicCompletion D.host.F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hw : (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) ∈ O := by
    rcases O.mem_or_inv_mem ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)) with h | h
    · exact h
    · have h' : (ϖ : v.adicCompletion D.host.F) / (T i j)⁻¹ ∈ O := by
        simpa [inv_div] using h
      have hfac : ϖ = (⟨(T i j)⁻¹, hy⟩ : O) * ⟨_, h'⟩ := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul]
        field_simp
      rcases hϖ.isUnit_or_isUnit hfac with hu | hu
      · exfalso
        apply hx
        obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = T i j := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          field_simp at h1
          simpa using h1
        exact heq ▸ hmem
      · obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          simp only at h1
          rw [eq_div_iff hϖ0]
          rw [div_inv_eq_mul, ← mul_assoc] at h1
          exact eq_inv_of_mul_eq_one_left h1
        exact heq ▸ hmem
  obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
  have hb2 : (b : v.adicCompletion D.host.F) ∈ O := b.2
  apply hb
  have hX := hT (Matrix.single j i ((b : v.adicCompletion D.host.F) * ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)))) (by
    intro k l
    rw [Matrix.single_apply]
    split_ifs
    · exact mul_mem hb2 hw
    · exact O.zero_mem)
  rw [trace_single_one_mul] at hX
  convert hX using 2
  field_simp

end GlobalTheory.CompanionTheory.Jp.DualInt
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleRev

theorem exists_isSocle_prodIrr_of_isRevOrdered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k →
    LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N),
    IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  intro k _ _ _ _ hA hJ hI hC h N Γ y hd hR hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order Γ
  have hR' : IsRevOrdered (Γ ∘ σ) := GlobalTheory.T.canonical_segments_reverse_ordered _ hσ
  have hd' : ∑ a, (y (σ a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp σ (fun a => (y a).1)
  obtain ⟨e₁⟩ := GlobalTheory.T.reverse_ordered_product_perm_equiv hA hC Γ σ y hd hd' hR hR' hL
  have hL' : ∀ i, IsLSeg ((Γ ∘ σ) i) ((y ∘ σ) i).rep := fun i => hL (σ i)
  obtain ⟨g, z, hz, ⟨e₂⟩, hjm⟩ := GlobalTheory.T.canonical_product_equiv_multiplicity_one hA hJ hI (Γ ∘ σ) (y ∘ σ) hd' hσ hL'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.socle_of_multiplicity_one hA z hz hjm
  exact ⟨τ, hτ.of_equiv (Representation.Equiv.refl _) (e₁.trans e₂).symm⟩

end GlobalTheory.CompanionTheory.SocleRev
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Multisegment

theorem inShW_of_wd_cosocle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSeg : LSegJacquet k)
    {𝔫 : Multiset (Segment k)} {N h h' : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (Δ : Fin h → Segment k) (Γ : Fin h' → Segment k)
    (v : Fin h' → IrrGL (k := k)) (hd : ∑ a, (v a).1 = N) (hΓ : IsOrderedForm Γ 𝔫)
    (hv : ∀ i, IsLSeg (Γ i) (v i).rep) (hc : IsCosocle π (prodIrr v hd)) (hw : Wd π (wtW Δ)) :
    InShW 𝔫 (wtW Δ) := by
  have h1 : Wd (prodIrr v hd) (wtW Δ) :=
    GlobalTheory.T.word_occurs_of_subquotient (prodIrr v hd) π (isSmooth_prodIrr v hd) hc.isSubquotient _ hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg v hd Γ hv (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ) h1
  rwa [hΓ.1] at h2

theorem lInjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k) (hSeg : LSegJacquet k) : LInjective k := by
  intro 𝔪 𝔫 x h𝔪 h𝔫
  obtain ⟨h, u, hd, ⟨Δ, hΔ, hu⟩, hc⟩ := id h𝔪
  obtain ⟨h', v, hd', ⟨Γ, hΓ, hv⟩, hc'⟩ := id h𝔫
  have wΔ : Wd x.rep (wtW Δ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 x.rep h𝔪 h Δ hΔ
  have wΓ : Wd x.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 x.rep h𝔫 h' Γ hΓ
  exact GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA 𝔪 𝔫 h h' Δ Γ hΔ hΓ
    (inShW_of_wd_cosocle hA hSeg Δ Γ v hd' hΓ hv hc' wΔ)
    (inShW_of_wd_cosocle hA hSeg Γ Δ u hd hΔ hu hc wΓ)

end GlobalTheory.CompanionTheory.Multisegment
end
