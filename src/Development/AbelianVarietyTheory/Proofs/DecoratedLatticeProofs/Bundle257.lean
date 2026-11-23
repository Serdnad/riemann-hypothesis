module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle228
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZeroLat

variable {D : D7}

theorem mxAt_mul {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c) : MxAt P (x ⬝ y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_conjHalf {S T : HSp D} {e : AE D} (he : IsSplitIdem D e) {x y : WO S T}
    (hx : IsHalf (cA D e) x) (hy : IsHalf (cA D e) y) : symplO S T x y = 0 := by
  have h0 : cA D e * cA D (cA D e) = 0 := (GlobalTheory.SplitScalar.isSplitIdem_conj he).2.1
  have : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hx d a, ← hy c b, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D (cA D e) * cA D (y c b)) * incA D (T.gram c d) * (cA D e * x d a)
        = (cA D e * cA D (cA D e)) * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  rw [symplO, this, mul_zero, map_zero]

theorem symplO_resS_symm_left {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T) (t : WO S T) :
    symplO S T ((o.resS T).symm (a, 0)) t = symplO A T a (t ⬝ o.jA) := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  have h0 : symplO L T 0 ((o.resS T) t).2 = 0 := by simp [symplO, hO]
  rw [h0, add_zero]; rfl

theorem smul_isHalf {e : AE D} (he : e * e = e) {m n : ℕ} (u : Mx D m n) : IsHalf e (e • u) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem finPart_idem_mem {e : AE D} (he : e * e = e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])

end GlobalTheory.FinPl.ExtZeroLat


open GlobalTheory.FinPl.ExtZeroLat in
theorem GlobalTheory.FinPl.ExtZero.extZero_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO A T, MxAt (· = p.v) u → (u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), ψ (symplO A T u u') = 1)) → (∀ u : WO S T, MxAt (· = p.v) u → (u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), ψ (symplO S T u u') = 1)) → halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), (o.resS T).symm (u, 0) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu
  classical
  set ΛA := latO A T (LA : Set _) (LT : Set _) (· = p.v) with hΛA
  set ΛS := latO S T (LS : Set _) (LT : Set _) (· = p.v) with hΛS
  have he := p.split
  have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hact := (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1

  have hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x := by
    intro m n x hx
    rw [← add_smul, hsum]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hact _).1 (hx i j)

  have hcol0 : GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT) 0 = 1 := by
    have hz : GlobalTheory.FinPl.ExtZero.zcol β ζ (0 : WO L T) = 0 := by
      simp only [GlobalTheory.FinPl.ExtZero.zcol, Matrix.zero_mulVec, Pi.zero_apply, map_zero]
      exact Matrix.mulVec_zero _
    have h0 : IsHalf p.e (0 : WO L T) := fun i j => by simp
    simp [GlobalTheory.FinPl.ExtZero.colFun, hz, vecInd, h0]

  have hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resS T).symm (a, 0) ∈ ΛS := by
    intro a ha hah
    have h1 := congrFun hfac ((o.resS T).symm (a, 0))
    rw [OrthDec.boxS, AddEquiv.apply_symm_apply, hcol0, mul_one] at h1
    have h2 : halfInd p.e ΛA a = 1 := by simp [halfInd, ha, hah]
    rw [h2] at h1
    unfold halfInd at h1
    by_contra hn
    rw [if_neg fun h => hn h.1] at h1
    exact zero_ne_one h1

  have hres : ∀ t ∈ ΛS, IsHalf p.e t → t ⬝ o.jA ∈ ΛA := by
    intro t ht hth
    have h1 := congrFun hfac t
    have h2 : halfInd p.e ΛS t = 1 := by simp [halfInd, ht, hth]
    rw [h2, OrthDec.boxS] at h1
    by_contra hn
    have : halfInd p.e ΛA ((o.resS T) t).1 = 0 := by
      unfold halfInd; rw [if_neg fun h => hn h.1]
    rw [this, zero_mul] at h1
    exact one_ne_zero h1
  have huM : MxAt (· = p.v) u := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have heu : p.e • u ∈ ΛA := GlobalTheory.LatticeStable.smul_mem_latO D A T _ _ _ _ (finPart_idem_mem he.1) u hu
  have hι : (o.resS T).symm (p.e • u, 0) ∈ ΛS := hext _ heu (smul_isHalf he.1 u)
  have hιM : MxAt (· = p.v) ((o.resS T).symm (u, 0)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
    exact mxAt_mul huM _
  refine (hS _ hιM).2 fun u' hu' => ?_
  have hu'M : MxAt (· = p.v) u' := GlobalTheory.FinPl.LatMem.latO_mxAt hu'
  have heu' : p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem he.1) u' hu'
  have hceu' : cA D p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem hce.1) u' hu'
  rw [symplO_resS_symm_left, ← hsplit u' hu'M, Matrix.add_mul, symplO_add_right, AddChar.map_add_eq_mul]
  have part1 : ψ (symplO A T u ((p.e • u') ⬝ o.jA)) = 1 :=
    (hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))
  have part2 : ψ (symplO A T u ((cA D p.e • u') ⬝ o.jA)) = 1 := by
    rw [← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]
    have hz : symplO A T (cA D p.e • u) ((cA D p.e • u') ⬝ o.jA) = 0 := by
      refine symplO_conjHalf he (smul_isHalf hce.1 u) ?_
      intro i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, (smul_isHalf hce.1 u') i l]
    rw [hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resS_symm_left]
    exact (hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'
  rw [part1, part2, one_mul]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.PutIn

theorem isHalf_nsmul {D : D7} {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := by
  intro i j
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_smul_idem {D : D7} {m n : ℕ} {b : AE D} (hbb : b * b = b) (x : Mx D m n) : IsHalf b (b • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hbb]

theorem isHalf_sub_smul {D : D7} {m n : ℕ} {a b : AE D} (hab : a * b = 0) {u : Mx D m n} (hu : IsHalf (a + b) u) :
    IsHalf a (u - b • u) := by
  intro i j
  have h := hu i j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]
  rw [add_mul] at h
  linear_combination h

theorem isSBHalf_tens : ∀ (D : D7) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (Φ Ψ : WO S T → ℂ),
    a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsSBHalf a Λ Φ → IsSBHalf b Λ Ψ →
    IsSBHalf (a + b) Λ (GlobalTheory.FinPl.PutIn.tens b Φ Ψ) := by
  intro D S T a b Λ Φ Ψ hab hbb hΛ ⟨hΦs, kΦ, hkΦ, hΦi, hΦb⟩ ⟨hΨs, kΨ, hkΨ, hΨi, hΨb⟩
  refine ⟨?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, ?_, ?_⟩
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦs _ (left_ne_zero_of_mul ht)
    have h2 := hΨs _ (right_ne_zero_of_mul ht)
    intro i j
    have e1 := h1 i j
    have e2 := h2 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero] at e1
    rw [add_mul, e1]
    ring
  · intro u hu hhu t
    have hu1 : u - b • u ∈ Λ := Λ.sub_mem hu (hΛ u hu)
    have hu2 : b • u ∈ Λ := hΛ u hu
    have e1 : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    have e2 : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [tens_apply, tens_apply, e1, e2,
      hΦi _ (Λ.nsmul_mem hu1 kΨ) (isHalf_nsmul (isHalf_sub_smul hab hhu) kΨ),
      hΨi _ (Λ.nsmul_mem hu2 kΦ) (isHalf_nsmul (isHalf_smul_idem hbb u) kΦ)]
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦb _ (left_ne_zero_of_mul ht)
    have h2 := hΨb _ (right_ne_zero_of_mul ht)
    have e : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem h1 kΨ) (Λ.nsmul_mem h2 kΦ)

end GlobalTheory.FinPl.PutIn

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem continuous_mt_cutTop (V : HSp D) : Continuous (fun g : GA D V => Formalism.L2.Theta.mt V g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) :
    Continuous (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  refine continuous_matrix fun i j => ?_
  have h : (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g) i j) = fun g : GA D V =>
      ε • Formalism.L2.Theta.mt V g i j +
        ((1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) i j := by
    funext g
    rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def ε]
  rw [h]
  exact (((continuous_mt_cutTop V).matrix_elem i j).const_smul ε).add continuous_const

theorem continuous_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : Continuous (cutG V ε hε) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨continuous_mt_cutG V ε hε, ?_⟩)
  have h := (continuous_mt_cutG V ε hε).comp (continuous_inv (G := GA D V))
  refine h.congr fun g => ?_
  rw [Function.comp_apply, map_inv]
  rfl

theorem isClosed_smul_sub_one_eq_zero (V : HSp D) (c : AF D.host.F) :
    IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e.isEmbedding.t2Space
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  have h : {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} =
      ⋂ i, ⋂ j, {g : GA D V | c • Formalism.L2.Theta.mt V g i j =
        c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero, Algebra.smul_def, Algebra.smul_def]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (((continuous_mt_cutTop V).matrix_elem i j).const_smul c) continuous_const

theorem continuous_cutG_and_isClosed : ∀ (D : D7) (V : HSp D), (∀ (ε : AF D.host.F) (hε : ε * ε = ε), Continuous (GlobalTheory.FinPl.SetCut.cutG V ε hε)) ∧ ∀ c : AF D.host.F, IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} :=
  fun _ V => ⟨continuous_cutG V, isClosed_smul_sub_one_eq_zero V⟩

end GlobalTheory.FinPl.SetCut
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

theorem smul_add_one_sub_smul_sub_one {R : Type} [CommRing R] {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) :
    c • M + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) - 1 = c • (M - 1) := by
  rw [sub_smul, one_smul, smul_sub]; abel

theorem smul_add_one_sub_smul_block {R : Type} [CommRing R] {n m : ℕ} (c : R) (P Q : Matrix (Fin n) (Fin n) R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (h : P + j * p + Q = 1) :
    c • (P + j * M * p + Q) + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      P + j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + Q := by
  rw [← h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_add, sub_smul,
    one_smul, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem smul_add_one_sub_smul_block₂ {R : Type} [CommRing R] {n m k : ℕ} (c : R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (j' : Matrix (Fin n) (Fin k) R) (p' : Matrix (Fin k) (Fin n) R)
    (h : j * p + j' * p' = 1) :
    c • (j * M * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p') + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p' := by
  have := smul_add_one_sub_smul_block c 0 (j' * p') j p M (by rw [zero_add, h])
  simpa only [zero_add, Matrix.mul_one] using this

variable {D : D7}

theorem jac_subOne_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.subOne V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.subOne V g :=
  smul_add_one_sub_smul_sub_one (algebraMap (AF D.host.F) (AE D) ε) (Formalism.L2.Theta.mt V g)

theorem jac_cutG_map_NFlag (V : HSp D) {ρ : ℕ} (e : Matrix (Fin V.rank) (Fin ρ) D.host.E) (ε : AF D.host.F)
    (hε : ε * ε = ε) : (NFlag V e).map (cutG V ε hε) ≤ NFlag V e := by
  unfold NFlag
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, hb⟩ := h1 i
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, fun j hj => ?_, ?_⟩
    · rw [Pi.smul_apply, ha j hj, smul_zero]
    · rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]
  · obtain ⟨a, hb⟩ := h2 x hx
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, ?_⟩
    rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]

theorem unitaryIdempotentCut_wittHyperbolicEmbedding_comm {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D V₀) :
    cutG V ε hε (d.emb0 h) = d.emb0 (cutG V₀ ε hε h) := by
  apply GlobalTheory.MixModel.mt_injective V
  change Formalism.L2.Theta.mt V (cutG V ε hε (d.emb0 h)) = Formalism.L2.Theta.mt V (d.emb0 (cutG V₀ ε hε h))
  rw [mt_cutG, HypDec.unitaryMatrix_wittCoreEmbedding, HypDec.unitaryMatrix_wittCoreEmbedding, mt_cutG]
  exact smul_add_one_sub_smul_block _ _ _ _ _ _ d.sum_eq_one

theorem jac_cutG_emb_inl {V₀ A L : HSp D} (o : OrthDec V₀ A L) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D A) :
    cutG V₀ ε hε (o.emb (h, 1)) = o.emb (cutG A ε hε h, 1) := by
  apply GlobalTheory.MixModel.mt_injective V₀
  change Formalism.L2.Theta.mt V₀ (cutG V₀ ε hε (o.emb (h, 1))) = Formalism.L2.Theta.mt V₀ (o.emb (cutG A ε hε h, 1))
  rw [mt_cutG, OrthDec.mt_emb, OrthDec.mt_emb, mt_cutG, mt_one]
  exact smul_add_one_sub_smul_block₂ _ _ _ _ _ _ o.sum_eq_one

theorem cutG_mem_jacGrp_besGrp (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) :
    (∀ g ∈ jacGrp d, cutG V ε hε g ∈ jacGrp d) ∧
      ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ g ∈ besGrp d o, cutG V ε hε g ∈ besGrp d o := by
  refine ⟨fun g hg => ?_, fun A L o g hg => ?_⟩
  · have H : (jacGrp d).map (cutG V ε hε) ≤ jacGrp d := by
      unfold jacGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨cutG V₀ ε hε h, (unitaryIdempotentCut_wittHyperbolicEmbedding_comm d ε hε h).symm⟩
    exact H ⟨g, hg, rfl⟩
  · have H : (besGrp d o).map (cutG V ε hε) ≤ besGrp d o := by
      unfold besGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      refine ⟨cutG A ε hε h, ?_⟩
      rw [embA_apply, embA_apply, unitaryIdempotentCut_wittHyperbolicEmbedding_comm, jac_cutG_emb_inl]
    exact H ⟨g, hg, rfl⟩

end GlobalTheory.FinPl.SetCut

end
end

section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

theorem _root_.GlobalTheory.T.fourierPairing_charIndicator_dualLattice_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) := by
  first | exact @GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets | exact GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets | (intros; apply GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → IsOpen {h : GA D W | finE W h ∈ K} → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ℂ, Continuous Z → Integrable Z ν → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ))‖ₑ ∂(Measure.pi mR) < ⊤ ∧ ∫ g, Z g ∂ν = ∫ b, ∑' x : FinCos W (levA W K), Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  first | exact @GlobalTheory.CosetDisint.integral_eq_cosetSum | exact GlobalTheory.CosetDisint.integral_eq_cosetSum | (intros; apply GlobalTheory.CosetDisint.integral_eq_cosetSum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), GlobalTheory.StepLaw.ResAt χ PP a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) → LiftsChar φ PP μ a := by
  first | exact @GlobalTheory.ResLift.liftsChar_of_resAt | exact GlobalTheory.ResLift.liftsChar_of_resAt | (intros; apply GlobalTheory.ResLift.liftsChar_of_resAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fock_sign_transpose_exchanges_local_gl_actions : ∀ (a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool), ∃ j : LPol b a ≃+ LPol a b, (∀ (c : ℂ) P, j (c • P) = conj c • j P) ∧ ∀ P : LPol b a, (∀ Y : Matrix (Fin b) (Fin b) ℂ, j (locT ε ε' Y P) = locS ε' ε (Y.map (starRingEnd ℂ)) (j P)) ∧ ∀ X : Matrix (Fin a) (Fin a) ℂ, j (locS ε ε' (X.map (starRingEnd ℂ)) P) = locT ε' ε X (j P) := by
  first | exact @GlobalTheory.Chain.RealIt.SwapFock.locS_locT_exchange | exact GlobalTheory.Chain.RealIt.SwapFock.locS_locT_exchange | (intros; apply GlobalTheory.Chain.RealIt.SwapFock.locS_locT_exchange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_real_discreteSeries_data_theta_properties : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, ChosenSeries X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.RealPlaceTheta.exists_record_theta_all | exact GlobalTheory.RealPlaceTheta.exists_record_theta_all | (intros; apply GlobalTheory.RealPlaceTheta.exists_record_theta_all <;> assumption)
end
