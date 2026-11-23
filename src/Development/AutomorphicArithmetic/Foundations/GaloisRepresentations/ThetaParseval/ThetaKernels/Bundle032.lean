module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FockDecK
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ColEApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle001

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def cmpW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : AddSubgroup (Mx F E d.m d.n) where
  carrier := {X | d.cw w X = 0}
  zero_mem' := by
    show d.cw w 0 = 0
    exact Matrix.map_zero _ (map_zero _)
  add_mem' := by
    intro X Z hX hZ
    show d.cw w (X + Z) = 0
    have e : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
    rw [e, show d.cw w X = 0 from hX, show d.cw w Z = 0 from hZ, add_zero]
  neg_mem' := by
    intro X hX
    show d.cw w (-X) = 0
    have e : d.cw w (-X) = -d.cw w X := Matrix.map_neg _ (map_neg _) X
    rw [e, show d.cw w X = 0 from hX, neg_zero]
def IntFact_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ν : Measure (Mx F E d.m d.n)), d.IsCov ν →
  ∃ (C : ℝ) (μ' : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)), 0 < C ∧ μ'.IsAddHaarMeasure ∧
    ∀ (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ),
      (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
      ∫ X, R.tens w f Ψ X ∂ν = C * (∫ u, f u) * ∫ Z, Ψ Z.1 ∂μ'
section Split
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem cw_add'_k (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
theorem cw_sub'_k (X Z : Mx F E d.m d.n) : d.cw w (X - Z) = d.cw w X - d.cw w Z := Matrix.map_sub _ (map_sub _) X Z
theorem loc_add'_k (X Z : Mx F E d.m d.n) : R.loc w (X + Z) = R.loc w X + R.loc w Z := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add'_k, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _
theorem loc_of_mem_k {b : Mx F E d.m d.n} (hb : b ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) : R.loc w b = 0 := by
  have h : d.cw w b = 0 := hb
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [h, Matrix.mul_zero]
  exact Matrix.map_zero _ (star_zero _)
theorem continuous_loc_k : Continuous (R.loc w) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  exact (continuous_const.matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w)).matrix_map continuous_star
end Split
theorem intFact_k : _root_.PositivityTheory.SiegelWeilFormula.KFock.IntFact_k := by
  intro F E _ _ _ _ _ σ d R w ν hν
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hcl : IsClosed ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w) continuous_const
  haveI : LocallyCompactSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) :=
    TopologicalSpace.Subtype.secondCountableTopology ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := Subtype.borelSpace (fun x' => x' ∈ ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  haveI := volume_isAddHaar d.m d.n
  obtain ⟨s, hsc, hs1, hs2, hsa, -⟩ := Place.exists_sec d.cm d.B.emb
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr
  let U : (Fin d.m → Fin d.n → ℂ) → Matrix (Fin d.m) (Fin d.n) ℂ := fun u => fr * Matrix.of fun b j => star (u b j)
  let sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n := fun u i j => s fun w' => if w' = w then U u i j else 0
  have cw_sW : ∀ u, d.cw w (sW u) = U u := fun u => by
    ext i j
    show piInf (d.B.emb w) (s _) = U u i j
    rw [hs1, if_pos rfl]
  have cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0 := fun u w' h => by
    ext i j
    show piInf (d.B.emb w') (s _) = 0
    rw [hs1, if_neg h]
  have fin_sW : ∀ u, finOne F • sW u = 0 := fun u => by
    ext i j
    show finOne F • s _ = 0
    exact hs2 _
  have inv_fr : ((R.fr w)⁻¹).1 * fr = 1 := Units.inv_mul (R.fr w)
  have fr_inv : fr * ((R.fr w)⁻¹).1 = 1 := Units.mul_inv (R.fr w)
  have loc_sW : ∀ u, R.loc w (sW u) = u := fun u => by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
    rw [cw_sW, ← Matrix.mul_assoc, inv_fr, Matrix.one_mul]
    ext a j
    simp
  have U_loc : ∀ X, U (R.loc w X) = d.cw w X := fun X => by
    simp only [U, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
    have : (Matrix.of fun b j => star ((((R.fr w)⁻¹).1 * d.cw w X).map star b j)) = ((R.fr w)⁻¹).1 * d.cw w X := by
      ext b j; simp
    rw [this, ← Matrix.mul_assoc, fr_inv, Matrix.one_mul]
  have U_add : ∀ u v, U (u + v) = U u + U v := fun u v => by
    simp only [U]
    rw [← Matrix.mul_add]
    congr 1
    ext b j
    simp [star_add]
  have sW_add : ∀ u v, sW (u + v) = sW u + sW v := fun u v => by
    ext i j
    show s _ = s _ + s _
    rw [← hsa]
    congr 1
    funext w'
    show _ = (if w' = w then U u i j else 0) + (if w' = w then U v i j else 0)
    by_cases h : w' = w
    · rw [if_pos h, if_pos h, if_pos h, U_add]; rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have hU : Continuous U := by
    simp only [U]
    exact continuous_const.matrix_mul (continuous_pi fun b => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp (continuous_apply b)))
  have hsW : Continuous sW := by
    refine continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hU)
    · exact continuous_const
  have mem : ∀ X, X - sW (R.loc w X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w := fun X => by
    show d.cw w (X - sW (R.loc w X)) = 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_sub'_k, cw_sW, U_loc, sub_self]
  let Φ : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => sW p.1 + p.2.1
      invFun := fun X => (R.loc w X, ⟨X - sW (R.loc w X), mem X⟩)
      left_inv := fun p => by
        obtain ⟨u, b, hb⟩ := p
        have e1 : R.loc w (sW u + b) = u := by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero]
        refine Prod.ext e1 (Subtype.ext ?_)
        show sW u + b - sW (R.loc w (sW u + b)) = b
        rw [e1, add_sub_cancel_left]
      right_inv := fun X => by
        show sW (R.loc w X) + (X - sW (R.loc w X)) = X
        rw [add_sub_cancel]
      map_add' := fun p q => by
        show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)
        rw [sW_add]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w).prodMk
        ((continuous_id.sub (hsW.comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w))).subtype_mk _) }
  letI hNuHaar : ν.IsAddHaarMeasure := hν.1
  obtain ⟨C, hC, hg⟩ := integral_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)) Φ
  refine ⟨C, Measure.addHaar, hC, inferInstance, fun f Ψ hΨ => ?_⟩
  rw [hg]
  have e : ∀ p : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w, R.tens w f Ψ (Φ p) = f p.1 * Ψ p.2.1 := fun p => by
    obtain ⟨u, b, hb⟩ := p
    show f (R.loc w (sW u + b)) * Ψ (sW u + b) = f u * Ψ b
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero, add_comm, hΨ b (sW u) (cw_sW' u) (fin_sW u)]
  simp_rw [e]
  have hp := integral_prod_mul (μ := (volume : Measure (Fin d.m → Fin d.n → ℂ))) (ν := (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)))
    f (fun Z : _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w => Ψ Z.1)
  rw [hp, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplitP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem siegel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ :=
  ⟨_, fun Φ hΦ => d.ok.dbl.weil.2.2 d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hp Φ hΦ⟩
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T
  congr 1
  funext x
  simp [Darboux.rho, schr, Matrix.zero_mul]
theorem loc_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  ext i j
  simp
theorem iota_isPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  have hn : 0 < d.n := d.ok.hn
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set M := inFrame d.b (R.ι w q) with hM
  have hζ : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hw : dZ d.n R.ζ * d.cw w M = mR q * dZ d.n R.ζ := R.at_w w q
  set C := d.cw w M with hC
  have e1 : dZ d.n R.ζ * C = Matrix.fromBlocks C.toBlocks₁₁ C.toBlocks₁₂ (R.ζ • C.toBlocks₂₁) (R.ζ • C.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    simp [dZ, Matrix.fromBlocks_multiply]
  have e2 : mR q * dZ d.n R.ζ = Matrix.fromBlocks (mR q).toBlocks₁₁ (R.ζ • (mR q).toBlocks₁₂) (mR q).toBlocks₂₁
      (R.ζ • (mR q).toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q)]
    simp [dZ, Matrix.fromBlocks_multiply]
  rw [e1, e2] at hw
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.1 hw
  rw [hq] at h21
  have hC21 : C.toBlocks₂₁ = 0 := (smul_eq_zero.1 h21).resolve_left hζ
  have hoff := R.off_f w q
  have hmem : R.ι w q ∈ SiegelEisensteinSeries.Grp.parS σ d.Y d.b (SiegelEisensteinSeries.Grp.siegelS hn) := by
    refine (SiegelEisensteinSeries.Grp.mem_parS_siegelS hn).2 fun i j => ?_
    refine Place.ad_ext d.cm d.B.emb (fun w' => ?_) ?_
    · by_cases hw' : w' = w
      · subst hw'
        have := congrFun (congrFun hC21 i) j
        simpa [Matrix.toBlocks₂₁, hC, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] using this
      · have := congrFun (congrFun (R.off_w w w' q hw') (Sum.inr i)) (Sum.inl j)
        simpa [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, hM] using this
    · have := congrFun (congrFun hoff (Sum.inr i)) (Sum.inl j)
      simpa [hM] using this
  obtain ⟨t, hPt, hdet⟩ := SiegelEisensteinSeries.Grp.isPar_of_mem_siegelS ht0 hn hmem
  refine ⟨t, hPt, ?_⟩
  set N := M.toBlocks₁₁ with hN
  have hfinN : finOne F • N = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    ext i j
    have := congrFun (congrFun hoff (Sum.inl i)) (Sum.inl j)
    simpa [hN, Matrix.toBlocks₁₁, Matrix.one_apply] using this
  set e := algebraMap (AF F) (AE F E) (finOne F) with he
  have hidem : e * e = e := by rw [he, ← map_mul, Krd.fin_idem]
  have hpow' : ∀ k : ℕ, e ^ (k + 1) = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hidem]
  have hpow : e ^ d.n = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hk]; exact hpow' k
  have hdetN : e * (N.det - 1) = 0 := by
    have h1 : (e • N).det = (e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))).det := by
      rw [he, algebraMap_smul, algebraMap_smul, hfinN]
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hpow, Matrix.det_one, mul_one] at h1
    rw [mul_sub, h1, mul_one, sub_self]
  have hat : ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1 ∈ PositivityTheory.ThKG.CayleyTransformDarboux.atI F E := by
    rw [PositivityTheory.ThKG.CayleyTransformDarboux.mem_atI, hdet]
    intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have eu : u = u * finOne F :=
      Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (by change u.2 = u.2 * 1; rw [mul_one])
    rw [Algebra.smul_def, eu, map_mul, mul_assoc, ← he, hdetN, mul_zero]
  rw [PositivityTheory.ThKG.CayleyTransformDarboux.absE_inf d.cm d.B.emb hat]
  rw [Finset.prod_eq_single w (fun w' _ hne => ?_) (fun h => absurd (Finset.mem_univ w) h)]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w))) = C.toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, h11]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w'))) = (d.cw w' M).toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, R.off_w w w' q hne]
    have h1 : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ).toBlocks₁₁ = 1 := by
      ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    rw [h1, Matrix.det_one, norm_one, one_pow]
end PositivityTheory.SiegelWeilFormula.KSplitP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem tens_add_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ Ψ' : Mx F E d.m d.n → ℂ) :
    R.tens w f (Ψ + Ψ') = R.tens w f Ψ + R.tens w f Ψ' := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.add_apply, mul_add]
theorem tens_smul_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx F E d.m d.n → ℂ) :
    R.tens w f (a • Ψ) = a • R.tens w f Ψ := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
  ring
def tensL_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := R.tens w f
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_add_k R w f
  map_smul' a Ψ := _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_smul_k R w f a Ψ
omit R in
theorem cw_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z :=
  Matrix.map_add _ (map_add _) X Z
theorem loc_add_of_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (h : d.cw w Z = 0) : R.loc w (X + Z) = R.loc w X := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add_k, h, add_zero]
omit R in
theorem crd_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) :
    d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
  rw [Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
omit R in
theorem crd_fin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Z : Mx F E d.m d.n) (h : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have e1 : d.crd (finOne F • Z) k = finOne F * d.crd Z k := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e2 : d.crd (finOne F • Z) k = 0 := by
    rw [h]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
  have e3 : (finOne F * d.crd Z k).2 = (d.crd Z k).2 := by
    show (finOne F).2 * (d.crd Z k).2 = _
    rw [show (finOne F).2 = 1 from rfl, one_mul]
  rw [← e3, ← e1, e2]
  rfl
theorem away_inv_k (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X := by
  intro X Z hZ hf
  induction hΨ using Submodule.span_induction generalizing X with
  | mem x hx =>
    obtain ⟨P, g, -, rfl⟩ := hx
    have e1 : ∀ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z)) = fP (P w') (R.loc w' X) := fun w' hw' => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add_of_k R w' X Z (hZ w' (Finset.ne_of_mem_erase hw'))]
    have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
      funext k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_add_k]
      show (d.crd X k).2 + (d.crd Z k).2 = _
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_fin_k d Z hf k, add_zero]
    show (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z))) * g (fun k => (d.crd (X + Z) k).2) =
      (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2)
    rw [Finset.prod_congr rfl e1, e2]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [Pi.smul_apply, hx]
theorem away_tens_k (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) (P : PX d.m d.n) :
    R.tens w (fP P) Ψ ∈ R.fock := by
  have h : R.away w ≤ R.fock.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w (fP P)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P', g, hg, rfl⟩
    refine Submodule.subset_span ⟨Function.update P' w P, g, hg, ?_⟩
    funext X
    show fP P (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P' w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', fP (Function.update P' w P w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  exact h hΨ
theorem fock_dec_k (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.fock) :
    ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
      (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i) :=
  by apply _root_.UpperTheory.Reformulated.B.Glb2.fock_dec_k <;> assumption
omit R in
theorem T_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ + Φ') = d.T Φ + d.T Φ' := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (Φ + Φ')) = d.l (d.dd.rho d.B.ψ _ Φ) + d.l (d.dd.rho d.B.ψ _ Φ')
  rw [← map_add (f := _)]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_add]
omit R in
theorem T_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a : ℂ) (Φ : d.Fn) : d.T (a • Φ) = a • d.T Φ := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (a • Φ)) = a • d.l (d.dd.rho d.B.ψ _ Φ)
  rw [← map_smul]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_left_comm]
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem thetaSum_S_rat_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {γ : UA σ d.A.J} (hγ : γ ∈ ratU σ d.A.J)
    {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : thetaSum F (d.S γ Ψ) = thetaSum F Ψ := by
  have hS : d.S γ Ψ ∈ d.sch := d.ok.dbl.lin.pres γ Ψ hΨ
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.ThKF0.Resc.rat_mat (inv_mem hγ)
  obtain ⟨g₁, hg₁⟩ := PositivityTheory.ThKF0.Resc.rat_mat hγ
  have hinj : Function.Injective (incM F : Matrix (Fin d.m) (Fin d.m) E → Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    PositivityTheory.SiegelWeilFormula.kfour.incM_injective
  have hmul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) E) (B : Matrix (Fin q) (Fin r) E),
      incM F (A * B) = incM F A * incM F B := fun A B => Matrix.map_mul (f := inclR (F := F) (E := E) (AF F))
  have hone : incM F (1 : Matrix (Fin d.m) (Fin d.m) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e01 : g₀ * g₁ = 1 := hinj (by
    rw [hmul, ← hg₀, ← hg₁, hone]
    have := congrArg (fun u : UA σ d.A.J => ((u.1 : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)))
      (inv_mul_cancel γ)
    simp at this; simpa using this)
  have e10 : g₁ * g₀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 e01
  let e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    ⟨fun X => g₀ * X, fun X => g₁ * X, fun X => by simp [← Matrix.mul_assoc, e10], fun X => by simp [← Matrix.mul_assoc, e01]⟩
  have h1 := (hT F E σ d (d.S γ Ψ) hS).1
  have h2 := (hT F E σ d Ψ hΨ).1
  have h3 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Ψ (incM F (e X))) (thetaSum F (d.S γ Ψ)) := by
    refine h1.congr_fun fun X => ?_
    rw [(hP F E σ d Ψ hΨ).2.2 γ (incM F X)]
    simp only [e, Equiv.coe_fn_mk, hmul, mat, ← hg₀]
  exact h3.unique ((e.hasSum_iff).2 h2)
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem meas_toMx_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (𝓕 : Set (Fin d.n → Fin d.m → AF F ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (MeasP.ratTupA F E d.n d.m) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ (μ.map toMx).IsAddHaarMeasure ∧
      IsAddFundamentalDomain d.ratM (toMx '' 𝓕) (μ.map toMx) ∧ μ.map toMx (toMx '' 𝓕) = 1 := by
  have hemb : MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) := (colM d.m d.n).measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact (colE (F := F) (E := E) d.m d.n).toAddEquiv.isAddHaarMeasure_map μ (colE d.m d.n).continuous
      (colE d.m d.n).symm.continuous
  · rw [_root_.PositivityTheory.SiegelWeilFormula.kfour.ratM_eq_k]
    refine hF.image_of_equiv (colM d.m d.n).toEquiv ?_ (ratEq d.m d.n) ?_
    · exact ((colM d.m d.n).measurePreserving_symm μ).quasiMeasurePreserving
    · intro g x
      rfl
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective, h1]
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end
