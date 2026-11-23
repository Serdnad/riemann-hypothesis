module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle148
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaGL

theorem kerGL_mul_right_KGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g k : GL (Fin r) (w.adicCompletion E), k ∈ KGL w (n := r) → φ (g * k) = φ g := by
  intro E _ _ w r N z φ hφ g k hk
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have hm := mem_Ov_of_isUnifV hϖ
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin r) (w.adicCompletion E), t = k₁⁻¹ * g * k₂⁻¹ := ⟨_, rfl⟩
  have hg : g = k₁ * t * k₂ := by rw [ht]; group
  have htv : t.1 = Matrix.diagonal fun i => ϖ ^ a i := by
    calc t.1 = ((k₁⁻¹ : GL (Fin r) (w.adicCompletion E)).1 * k₁.1) * Formalism.UG.diagPow E w ϖ a *
          (k₂.1 * (k₂⁻¹ : GL (Fin r) (w.adicCompletion E)).1) := by
          rw [ht, Units.val_mul, Units.val_mul, e]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]; rfl
  rw [hg, mul_assoc (k₁ * t) k₂ k, hφ ϖ hϖ a t htv k₁ hk₁ (k₂ * k) (mul_mem hk₂ hk), hφ ϖ hϖ a t htv k₁ hk₁ k₂ hk₂]

end GlobalTheory.ZetaGL
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem levDatum_ne_zero_spec {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T) :
    levDatum S T βS βT LT Q m e x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ (∀ PP, PP ∈ LT.Pg ∨ PP ∈ Q → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT x))).det) ∧ ∃ a : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1), (∀ PP : ↥LT.Pg, ((a PP : GL (Fin T.rank) (kP PP.1)) : Matrix (Fin T.rank) (Fin T.rank) (kP PP.1)) = topL T.rank (redM PP.1 (frMapAdj S T βS βT x))) ∧ (∀ PP : ↥LT.Pg, a PP ∈ blockTri (blkOf LT.r LT.t)) ∧ (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H := by
  intro hne
  unfold levDatum at hne
  split_ifs at hne with h0
  · refine ⟨h0.1, h0.2, ?_⟩
    have hG : omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := right_ne_zero_of_mul hne
    unfold omegaG at hG
    unfold omegaQ at hQ
    split_ifs at hG with hg
    · split_ifs at hQ with hq
      · obtain ⟨a, ha1, ha2, ha3⟩ := hg.2
        refine ⟨?_, a, ha1, ha2, ha3⟩
        rintro PP (hP | hP)
        · rw [← ha1 ⟨PP, hP⟩]
          exact (a ⟨PP, hP⟩).isUnit.map Matrix.detMonoidHom
        · exact (hq PP hP).2
      · exact absurd rfl hQ
    · exact absurd rfl hG
  · exact absurd rfl hne

end GlobalTheory.FinZeta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.LevelOff

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z =
      ∑ v ∈ Sb, (GlobalTheory.AdelicU.singleFin v).rTensor E
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      LinearMap.rTensor_tmul]
    rw [← TensorProduct.sum_tmul]
    congr 1
    refine GlobalTheory.AdelicU.af_ext fun u => ?_

    rw [map_mul, map_sum]
    by_cases hu : u ∈ Sb
    · rw [Finset.sum_eq_single u (fun v _ hv => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hv) _)
        (fun h => absurd hu h), GlobalTheory.AdelicU.evalV_singleFin_self]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_pos hu, one_mul]
    · rw [Finset.sum_eq_zero (fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _)]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_neg hu, zero_mul]
  | add x y hx hy => rw [mul_add, hx, hy, ← Finset.sum_add_distrib]; simp only [map_add (f := _)]

theorem ind_tmul_mul_eq_zero (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z = 0 := by
  rw [ind_tmul_mul]
  exact Finset.sum_eq_zero fun v hv => by rw [h v hv, map_zero]

theorem one_sub_ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    ((1 - GlobalTheory.AdeleIdem.ind Sb) ⊗ₜ[F] (1 : E)) * z = z := by
  rw [TensorProduct.sub_tmul, sub_mul, ← Algebra.TensorProduct.one_def, one_mul, ind_tmul_mul_eq_zero Sb z h, sub_zero]

open Filter GlobalTheory.AdelicU

variable {D : D7}

theorem mem_KsphC_iff (V : HSp D) (g : GA D V) : g ∈ KsphC V ∅ ↔ g ∈ GfC V ∧ ∀ v, projV V v g ∈ Kv V v := by
  have e : g ∈ KsphC V ∅ ↔ g ∈ ((levelOff D.sp.cm.sig V.gram (frameLat V) ∅ : Subgroup _) : Set (GA D V)) := by
    rw [KsphC_eq]
  rw [e, SetLike.mem_coe, mem_levelOff, GfC_eq]
  simp

theorem eq_L0sub {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) : Λ = GlobalTheory.LevSplit.L0sub V := by
  obtain ⟨-, -, -, h01, h10⟩ := hB
  ext x
  constructor
  · intro hx
    show x ∈ L0c D V
    simpa using h10 x hx
  · intro hx
    simpa using h01 x hx

theorem finE_mem_St_iff {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) {g : GA D V} (hg : g ∈ GfC V) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ g ∈ KsphC V ∅ := by
  have hfr : Formalism.L2.DIV.IsFrame β (GlobalTheory.LevSplit.L0sub V) := eq_L0sub hB ▸ hB.1
  have e1 := GlobalTheory.LevSplit.mem_St_iff β _ hfr (Formalism.IndefR.Lev.finE V g)
  have e2 := GlobalTheory.LevSplit.ksph_iff V g
  exact e1.trans ⟨fun h => e2.2 ⟨hg, h⟩, fun h => (e2.1 h).2⟩

theorem finE_mem_St_of_mem_levG {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Lv : LevDat D.host.E ℂ V.rank}
    {g : GA D V} (hg : g ∈ levG V β Lv) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β :=
  Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg.2)

open Filter GlobalTheory.AdelicU

variable {D : D7}

theorem evalV_finPart (v : HeightOneSpectrum (𝓞 D.host.F)) (w : AE D) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (Formalism.L2.Theta.finPart D w) =
      compFin D.host.F D.host.E v w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, _root_.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), _root_.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem redFn_eq_one_of_proj {V : HSp D} (β : GL (Fin V.rank) (EAf D)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {h : GA D V} (hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β) (h1 : ∀ v ∈ Sb, projV V v h = 1)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V h) = 1 := by
  classical
  set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef
  have hb : b ∈ Formalism.UG.intAd D.host.F := sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)
  refine GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_
  · refine GlobalTheory.AdeleIdem.resS_eq_zero PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl hb ?_
    simp [hbdef, GlobalTheory.AdeleIdem.ind_apply, hPP]
  · ext i j
    set w : AE D := (Formalism.L2.Theta.mt V h - 1) i j with hw
    have e0 : ((Formalism.L2.Theta.mt V h) - 1).map (GlobalTheory.LevSplit.finSw D) = (Formalism.L2.Theta.mt V h).map (GlobalTheory.LevSplit.finSw D) - 1 := by
      rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
    have ex : ((Formalism.IndefR.Lev.finE V h).1 - 1) i j = Formalism.IndefR.Lev.swapAE D (Formalism.L2.Theta.finPart D w) := by
      rw [GlobalTheory.LevSplit.finE_val, ← e0]
      rfl
    have hz : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Formalism.L2.Theta.finPart D w) = 0 := by
      intro v hv
      rw [evalV_finPart]
      have e1 : (Formalism.L2.Theta.mt V h).map (compFin D.host.F D.host.E v) = 1 := by
        have e2 : (matHom _ D.sp.cm.sig V.gram (projV V v h)).1 = 1 := by
          rw [h1 v hv, MonoidHom.map_one, Units.val_one]
        exact e2
      have e3 : ((Formalism.L2.Theta.mt V h) - 1).map (compFin D.host.F D.host.E v) = 0 := by
        rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), e1, sub_self]
      exact congrFun (congrFun e3 i) j
    rw [Matrix.smul_apply, smul_eq_mul, ex]
    show Formalism.IndefR.Lev.swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [← RingHom.map_mul]
    refine congrArg (Formalism.IndefR.Lev.swapAE D) ?_
    exact one_sub_ind_tmul_mul Sb _ hz

open GlobalTheory.AdelicU

theorem level_offS : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Lv : LevDat D.host.E ℂ V.rank) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBaseFrame V β Λ 1 → (∀ PP, PP ∈ Lv.Pg ∨ PP ∈ Lv.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) → SphOff (levG V β Lv : Set (GA D V)) (levChi V β Lv) Sb ∧ (∀ g ∈ GfC V, g ∈ levG V β Lv ↔ (∃ k ∈ levG V β Lv, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v) ∧ (∀ g : GA D V, {v | projV V v g ∉ Kv V v}.Finite) ∧ ∀ k ∈ levG V β Lv, ‖levChi V β Lv k‖ = 1 := by
  intro D V β Λ Lv Sb hB hPl
  have hsplit := GlobalTheory.LevSplit.lev_split V β Λ 1 Lv hB
  have hK : ∀ k ∈ levG V β Lv, ∀ v, projV V v k ∈ Kv V v := fun k hk =>
    ((mem_KsphC_iff V k).1 ((finE_mem_St_iff hB hk.1).1 (finE_mem_St_of_mem_levG hk))).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    rw [GlobalTheory.GoodPrimes.offS_iff] at hP
    obtain ⟨e, f, hpe⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
    have h1P : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [Nat.cast_one]
      exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    obtain ⟨h1, h2, -⟩ := hsplit.2 P e f hpe h1P fun PP hPP =>
      ⟨fun e => by subst e; exact hP (hPl _ hPP),
       fun hc => hP (by rw [← GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc]; exact hPl PP hPP)⟩
    exact ⟨e, f, hpe, h1, h2⟩
  · intro g hg
    constructor
    · intro h
      exact ⟨⟨g, h, fun _ _ => rfl⟩, fun v _ => hK g h v⟩
    · rintro ⟨⟨k, hk, heq⟩, hoff⟩
      have hxf : g * k⁻¹ ∈ GfC V := mul_mem hg (inv_mem hk.1)
      have hx1 : ∀ v ∈ Sb, projV V v (g * k⁻¹) = 1 := fun v hv => by
        rw [MonoidHom.map_mul, MonoidHom.map_inv, heq v hv, mul_inv_cancel]
      have hxK : g * k⁻¹ ∈ KsphC V ∅ := (mem_KsphC_iff V _).2 ⟨hxf, fun v => by
        by_cases hv : v ∈ Sb
        · rw [hx1 v hv]; exact one_mem _
        · rw [MonoidHom.map_mul, MonoidHom.map_inv]; exact mul_mem (hoff v hv) (inv_mem (hK k hk v))⟩
      have hxS := (finE_mem_St_iff hB hxf).2 hxK
      have hxl : g * k⁻¹ ∈ levG V β Lv := ⟨hxf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β Lv _
        (GlobalTheory.LevSplit.finE_mem_UA V _) hxS fun PP hPP => redFn_eq_one_of_proj β Sb hxS hx1 (hPl PP hPP)⟩
      have e : g = g * k⁻¹ * k := by rw [inv_mul_cancel_right]
      rw [e]
      exact mul_mem hxl hk
  · intro g
    haveI := SelfDual.isLattice_frameLat V
    exact Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V) g)
  · intro k hk
    obtain ⟨n, hn, h⟩ := hsplit.1 k hk
    exact Complex.norm_eq_one_of_pow_eq_one h hn.ne'

end GlobalTheory.FinZeta.LevelOff

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompIdem

theorem projV_eq_of_idem : ∀ {D : D7} (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g k : GA D T) (ε : AE D), compFin D.host.F D.host.E v ε = 1 → Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → projV T v k = projV T v g := by
  intro D T v g k ε hε h
  apply GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig T.gram
  apply Units.ext
  show (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v k)).1 =
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v g)).1
  rw [GlobalTheory.AdelicU.matHom_proj, GlobalTheory.AdelicU.matHom_proj]
  show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram k).1).map (compFin D.host.F D.host.E v) =
    ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g).1).map (compFin D.host.F D.host.E v)
  change (Formalism.L2.Theta.mt T k).map _ = (Formalism.L2.Theta.mt T g).map _
  rw [h, GlobalTheory.CompStab.map_idem, hε, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.CompIdem
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricCompact

theorem exists_compact_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) :
    ∃ C : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ x : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) : _ →+* _) x ∈ St β → ∀ i j, x.1 i j ∈ C := by
  classical
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨-, C0, hC0, hC0m⟩ := GlobalTheory.Mass.intTens_open_compact F E
  let s := GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)

  let b : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := (β : Matrix (Fin n) (Fin n) _).map s.symm
  let c : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map s.symm

  let f : Fin n → Fin n → (Fin n → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
    fun i j a => ∑ l, (∑ k, b i k * a k l) * c l j
  have hf : ∀ i j, Continuous (f i j) := fun i j =>
    continuous_finsetSum _ fun l _ =>
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_apply l).comp (continuous_apply k))).mul continuous_const
  have hS : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC0
  refine ⟨⋃ i, ⋃ j, f i j '' Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hS.image (hf i j), ?_⟩
  intro x hx i j
  obtain ⟨y, hy⟩ := hx
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j,
    ⟨fun k l => s.symm ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l), ?_, ?_⟩⟩⟩
  · intro k _ l _
    apply hC0m
    change (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (s.symm _) ∈ Formalism.L2.Herm.intAf F E
    rw [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l).2
  · have hx' : (x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) i j =
        s.symm (((Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x :
          GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) i j) := by
      rw [Formalism.UG.P.bc_coe]
      simp
    have hy' : Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x =
        β * Formalism.L2.DIV.intGL F E n y * β⁻¹ := by
      rw [← hy]
      rfl

    rw [hx', hy', Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_

    rw [map_mul, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Formalism.L2.DIV.intGL, Formalism.UG.P.bc_coe]
    rfl

variable {D : D7}

theorem isOpen_comap_lev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  classical
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hκ
  obtain ⟨hU, hS, hR⟩ := hκ
  show finE V κ ∈ lev D.sp.cm V.gram β L
  refine Formalism.L2.DIV.Kg_le_lev (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right ?_
  simp only [Formalism.L2.DIV.Kg, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact ⟨⟨hU, hS⟩, fun PP hPP => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hR PP hPP⟩⟩

theorem exists_compact (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, k ∈ GfC V → finE V k ∈ St β → k ∈ C := by
  obtain ⟨C1, hC1, hC1m⟩ := exists_compact_entries (F := D.host.F) (E := D.host.E) β
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C1 hC1

  haveI : T2Space (InfiniteAdeleRing D.host.F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  haveI : T2Space (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    inferInstanceAs (T2Space (RestrictedProduct
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
      (fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))) Filter.cofinite))
  haveI : T2Space (AF D.host.F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  obtain ⟨K', hK', hK'm⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) K hK
  refine ⟨K', hK', fun k hk hst => hK'm k fun i j => hKm _ ?_ ?_⟩
  ·
    have hsw : (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _) = swapAE D :=
      RingHom.ext fun _ => rfl
    have hst' : Formalism.UG.bc (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _)
        (finHom V k) ∈ St β := by
      rw [hsw]
      exact hst
    have h := hC1m (finHom V k) hst' i j
    rw [finHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe] at h
    exact h
  ·
    intro ρ
    have h1 : infHom V k = 1 := hk
    have h2 : infPart D ((HA.mat (AF D.host.F) D.sp.cm.sig V.gram k : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
      have h3 := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
        (g : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j) h1
      simp only [infHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe, Units.val_one] at h3
      exact h3
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, norm_one, le_refl]
    · simp only [Matrix.one_apply_ne hij, map_zero, norm_zero, zero_le_one]

theorem isCompact_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsCompact ((levG V β L : Subgroup (GA D V)) : Set (GA D V)) := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  obtain ⟨C, hC, hCm⟩ := exists_compact V β
  refine hC.of_isClosed_subset ?_ ?_
  · rw [levG, levA, Subgroup.coe_inf]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter
      (Subgroup.isClosed_of_isOpen _ (isOpen_comap_lev V β L))
  · intro k hk
    rw [SetLike.mem_coe, levG, levA, Subgroup.mem_inf] at hk
    exact hCm k hk.1 (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2))

theorem isCompact_flag_and_lift : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), IsCompact ((levG V β (flagL L) : Subgroup (GA D V)) : Set (GA D V)) ∧ ∀ g0 κ, IsLevelLift V β L g0 κ → κ ∈ levG V β (flagL L) := by
  intro D V β L
  refine ⟨isCompact_levG V β (flagL L), fun g0 κ hκ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hκ
  rw [levG, levA, Subgroup.mem_inf]
  refine ⟨h1, ?_⟩
  show finE V κ ∈ lev D.sp.cm V.gram β (flagL L)
  rw [Formalism.L2.DIV.mem_lev]
  exact ⟨h2, Subgroup.mem_top _⟩

end GlobalTheory.ParahoricCompact
end
