module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle485
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle459
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralGlueLocalHomotheties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle484
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle227
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.lastIsotropicLine_homothety_matches_lattices : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S₀ M → z ≠ 0 → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LastLine.lastLine_match | exact GlobalTheory.Core.Mi.LastLine.lastLine_match | (intros; apply GlobalTheory.Core.Mi.LastLine.lastLine_match <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.mem_secondModelStabilizer_iff_carriesRowLattice : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (κ : GA D (D.sp.Y 0)), κ ∈ grpAt (D.sp.Y 0) (· = v) → ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.KsetAt.mem_Kset_iff_moves | exact GlobalTheory.Core.Mi.KsetAt.mem_Kset_iff_moves | (intros; apply GlobalTheory.Core.Mi.KsetAt.mem_Kset_iff_moves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.primitive_character_matches_lines_down_flag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → PrimAt ψ d L v → PrimAt ψ d L' v → NormOneAt v c → ∀ i j : Fin ρ, j.1 = i.1 + 1 → (∀ a ∈ idAt D (· = v), (colMul d.jX j a ∈ latV S L (· = v) ↔ colMul d.jX j (c * a) ∈ latV S L' (· = v))) → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.match_down_flag | exact GlobalTheory.Core.Mi.LatMatch.match_down_flag | (intros; apply GlobalTheory.Core.Mi.LatMatch.match_down_flag <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.CoreHomothety

variable {D : D7}

theorem mulVec_mem_idAt {P : GlobalTheory.FinPl.Pl D → Prop} {m l : ℕ} (X : Matrix (Fin m) (Fin l) (AE D))
    {y : Fin l → AE D} (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (X *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have h1 := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  have h2 : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, show mt S g * mt S g⁻¹ = mt S (g * g⁻¹) from rfl, mul_inv_cancel, mt_one,
      Matrix.one_mulVec]
  rw [h2] at h1
  exact h1.symm

theorem moves_trans {S : HSp D} {g h : GA D S} {L M N : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h1 : Moves S g L M P)
    (h2 : Moves S h M N P) : Moves S (h * g) L N P := by
  intro y hy
  rw [h1 y hy, h2 _ (mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec]
  rfl

theorem moves_conj {S : HSp D} {h : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (hM : Moves S h L M P)
    (a : GA D S) : Moves S (h * a * h⁻¹) M M P ↔ Moves S a L L P := by
  constructor
  · intro H
    have e : h⁻¹ * (h * a * h⁻¹ * h) = a := by group
    have := moves_trans (moves_trans hM H) (moves_inv hM)
    rwa [e] at this
  · intro H
    have := moves_trans (moves_trans (moves_inv hM) H) hM
    rwa [← mul_assoc] at this

theorem sMoves_trans {S : HSp D} {c : AE D} {g h : GA D S} {L M N : Lat S} {v : GlobalTheory.FinPl.Pl D}
    (hS : SMoves S c g L M v) (hM : Moves S h M N (· = v)) : SMoves S c (h * g) L N v := by
  intro y hy
  rw [hS y hy, hM (c • (mt S g *ᵥ y)) (fun i => Ideal.mul_mem_left _ c (mulVec_mem_idAt _ hy i)),
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rfl

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_gluedS_smul (q : GlobalTheory.LatPair.Unif k) {P P' : GlobalTheory.LatPair.Pair k n} {g : GL n k} {s : k} (hs : s ≠ 0)
    (hg : g.val = s • (1 : Matrix n n k)) (hP : P' = g • P) (u : n → k) (t : Fin 1 → k) :
    Sum.elim u t ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec ↔ Sum.elim (s • u) t ∈ GlobalTheory.LatPair.gluedS q 1 P'.ker P'.vec := by
  have hgx : ∀ x : n → k, g • x = s • x := fun x => by
    show g.val *ᵥ x = s • x
    rw [hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hgi : ∀ x : n → k, g⁻¹ • x = s⁻¹ • x := fun x => by
    have : x = g • (s⁻¹ • x) := by rw [hgx, smul_smul, mul_inv_cancel₀ hs, one_smul]
    conv_lhs => rw [this]
    rw [inv_smul_smul]
  have hker : ∀ x : n → k, x ∈ P'.ker ↔ s⁻¹ • x ∈ P.ker := fun x => by
    rw [hP, GlobalTheory.LatPair.Pair.smul_ker, GlobalTheory.LatPair.mem_smul_iff, hgi]
  have hvec : P'.vec - s • P.vec ∈ P'.ker := by
    have h1 := P.hasVal_vec.gl_smul g
    rw [← hP, hgx] at h1
    have := GlobalTheory.LatPair.Pair.sub_vec_mem h1
    rw [← neg_sub]
    exact neg_mem this
  rw [GlobalTheory.LevelUnfold.mem_gluedS, GlobalTheory.LevelUnfold.mem_gluedS]
  refine exists_congr fun σ => and_congr_left' ?_
  have e1 : (Sum.elim u t : n ⊕ Fin 1 → k) ∘ Sum.inl = u := rfl
  have e2 : (Sum.elim (s • u) t : n ⊕ Fin 1 → k) ∘ Sum.inl = s • u := rfl
  rw [e1, e2]
  have e3 : s • u - σ • P'.vec = s • (u - σ • P.vec) - σ • (P'.vec - s • P.vec) := by
    simp only [smul_sub]
    rw [smul_comm σ s P.vec]
    abel
  rw [e3, Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ σ hvec), hker, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem emb_central_frame {p : SplitPt D k} {S A L : HSp D} {o : OrthDec S A L} {ζ : Fin L.rank → D.host.E}
    {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hsum : IsSumFrame o ζ β β₀) {a : GA D A}
    {c' : AE D} (ha : mt A a = c' • (1 : Matrix (Fin A.rank) (Fin A.rank) (AE D))) (y : n ⊕ Fin 1 → k) :
    (mt S (o.emb (a, 1))).map p.pr *ᵥ (β₀.b *ᵥ y) =
      β₀.b *ᵥ Sum.elim (fun i => p.pr c' * y (Sum.inl i)) (fun j => y (Sum.inr j)) := by
  have h3 : (mt A a).map p.pr = β.b * (p.pr c' • (1 : Matrix n n k)) * β.b' := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, β.bb', ha]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have e := GlobalTheory.FinPl.Comm.block_calc p.pr _ _ _ _ _ _ _ (o.emb_jA a 1) (GlobalTheory.FinPl.Comm.emb_vecB o ζ a) h3 β.b'b
  rw [← hsum] at e
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  congr 1
  ext (i | j) <;> simp [Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

end Split

theorem exists_central_sMoves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M M' : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k) (P : GlobalTheory.LatPair.Pair k n) (a₀ : GA D A), 3 ≤ Fintype.card n → IsSumFrame o ζ β β₀ → IsSelfDualC S M → IsSelfDualC S M' → β₀.IsLat M (GlobalTheory.LatPair.gluedS q 1 P.ker P.vec) → μ ≠ 0 → LineAt (vecB o ζ) μ M' p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → (∀ a ∈ grpAt A (· = p.v), Moves S (o.emb (a, 1)) M M (· = p.v) ↔ Moves S (o.emb (a₀ * a * a₀⁻¹, 1)) M' M' (· = p.v)) → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' p.v := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M M' μ T q P a₀ hn hsum hM hM' hlat hμ hline hnorm hval hconj
  obtain ⟨M'', hsd'', hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S M' hM').1 (o.emb (a₀, 1))⁻¹
  have hmv' : Moves S (o.emb (a₀, 1)) M'' M' (· = p.v) := by
    have := moves_inv (hmv (· = p.v))
    rwa [inv_inv] at this
  have hline'' : LineAt (vecB o ζ) μ M'' p.v := by
    intro b hb
    rw [← hline b hb, hmv' (b • ratV (vecB o ζ)) (fun i => Ideal.mul_mem_right _ _ hb), Matrix.mulVec_smul,
      GlobalTheory.FinPl.Comm.emb_vecB]
  obtain ⟨P', hP'⟩ := GlobalTheory.T.selfDualCore_component_gluedAlongPair D k p S A L o ζ n β β₀ M'' μ T q hsum hsd'' hμ hline'' hnorm hval
  have hm : p.pr (incA D μ) ≠ 0 := by
    intro h0
    have h1 : p.pr (incA D μ * incA D μ⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hW : GluedW β₀ M q 1 P := fun x => by
    have e : (Sum.elim (fun a => x (Sum.inl a)) (fun j => 1 * x (Sum.inr j)) : n ⊕ Fin 1 → k) = x := by
      ext (i | i) <;> simp
    rw [e]
    exact (hlat x).symm
  have hstab : ∀ g : GL n k, g • P = P ↔ g • P' = P' := fun g => by
    rw [← GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair D k p S A L o ζ n β β₀ M q 1 P hsum hM one_ne_zero hW g,
      ← GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair D k p S A L o ζ n β β₀ M'' q _ P' hsum hsd'' hm hP' g,
      hconj _ (GlobalTheory.FinPl.FrameLat.gl_mem_grpAt β g)]
    have e : o.emb (a₀ * β.gl g * a₀⁻¹, 1) = o.emb (a₀, 1) * o.emb (β.gl g, 1) * (o.emb (a₀, 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, inv_one, mul_one, mul_one]
    rw [e, moves_conj hmv']
  obtain ⟨g, s, hs, hg, hPP⟩ := GlobalTheory.T.latticeResiduePair_eq_scalar_of_same_stabilizer k n P P' hn hstab
  obtain ⟨c, hc, hcpr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (p.pr (incA D μ))⁻¹ (inv_ne_zero hm)
  obtain ⟨c', hc', hc'pr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (s * p.pr (incA D μ)) (mul_ne_zero hs hm)
  obtain ⟨a, hcen, hamt⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A p.v c' hc'
  refine ⟨a, c, hcen, hc, ?_⟩
  have key : SMoves S c (o.emb (a, 1)) M M'' p.v := by
    refine GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S M M'' c (o.emb (a, 1)) hM hsd'' hc fun x => ?_
    have hx : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    rw [hx, emb_central_frame hsum hamt, ← Matrix.mulVec_smul, hW, hP']
    refine (mem_gluedS_smul q hs hg hPP _ _).trans (iff_of_eq ?_)
    congr 1
    ext (i | j)
    · simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, hcpr, hc'pr]
      field_simp
    · simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, hcpr]
      field_simp
  have e : o.emb (a₀ * a, 1) = o.emb (a₀, 1) * o.emb (a, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e]
  exact sMoves_trans key hmv'

end GlobalTheory.Core.Mi.LatMatch.CoreHomothety
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.exists_central_glue_localHomotheties : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  first | exact @GlobalTheory.Core.Mi.LatGlue.glue | exact GlobalTheory.Core.Mi.LatGlue.glue | (intros; apply GlobalTheory.Core.Mi.LatGlue.glue <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_standardLocalisation_weilDatum_inertPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  first | exact @GlobalTheory.InertFrameLoc.exists_isStd_inert | exact GlobalTheory.InertFrameLoc.exists_isStd_inert | (intros; apply GlobalTheory.InertFrameLoc.exists_isStd_inert <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem basicIdentity_flat : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → ∀ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ → ∀ A : CptF V, ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → GlobalTheory.Eis.BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ :=
  fun hE hC D V hV a ha hI μ hμ _ _ hφ _ hθ _ m hm f₁ h₁ f₂ h₂ s hs =>
    GlobalTheory.T.doubling_basicIdentity_unfolding D V a ha μ hμ s hs _ (GlobalTheory.Eis.flat_mem hI hφ s) (GlobalTheory.T.siegelEisenstein_spherical_moderateGrowth_real_point hE D V hV a ha hI s.re hs) m hm f₁ f₂
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2)
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.2)
      (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2

end GlobalTheory.Core.Rk.IP
end
