module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle248
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle539
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle540
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.PlaceLimit

theorem sum_placeIdem {D : D7} {ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F}
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∑ v ∈ A, ε v = pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  choose α h0 h1 h2 using hε
  refine Prod.ext ?_ ?_
  · change fstA D.host.F (∑ v ∈ A, ε v) = 0

    rw [map_sum]
    exact Finset.sum_eq_zero fun v _ => by rw [h0]; rfl
  · change sndA D.host.F (∑ v ∈ A, ε v) = GlobalTheory.LevelClosure.cutIdem A

    rw [map_sum]
    refine RestrictedProduct.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (∑ v ∈ A, sndA D.host.F (ε v)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (GlobalTheory.LevelClosure.cutIdem A)
    have e : ∀ v, sndA D.host.F (ε v) = α v := fun v => by rw [h0]; rfl

    rw [map_sum]
    simp only [e]
    by_cases hw : w ∈ A
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw,
        Finset.sum_eq_single w (fun v _ hv => h2 v w (Ne.symm hv)) (fun h => absurd hw h), h1]
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw]
      exact Finset.sum_eq_zero fun v hv => h2 v w fun h => hw (h ▸ hv)

theorem pair_cutIdem_mul_self {F : Type} [Field F] [NumberField F] (A : Finset (HeightOneSpectrum (𝓞 F))) :
    pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) * pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) =
      pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  refine Prod.ext (mul_zero _) ?_
  change GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A = GlobalTheory.LevelClosure.cutIdem A
  refine RestrictedProduct.ext _ _ fun w => ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A)
  rw [map_mul]
  by_cases hw : w ∈ A
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw, one_mul]
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw, zero_mul]

theorem tendsto_cut_mul {D : D7} {z : AE D} (hz : infPart D z = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) * z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) atTop (𝓝 (pairA D.host.F 0 1)) := by
    have := GlobalTheory.LevelClosure.tendsto_cutIdem_mul (1 : Af D.host.F)
    simp only [mul_one] at this
    exact (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds this
  have h2 := h.smul_const z
  have e : pairA D.host.F 0 1 • z = z := by
    rw [Algebra.smul_def, mul_comm]
    exact GlobalTheory.PlaceDatum.mul_pair_one hz
  rw [e] at h2
  simpa only [Algebra.smul_def] using h2

theorem tendsto_mix {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) atTop (𝓝 (Formalism.L2.Theta.mt V g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1 i j) (show infHom V g = 1 from hg)
  have h2 : infPart D (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
    rw [RingHom.map_sub, h1, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  have h3 := (tendsto_cut_mul h2).add_const ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
  rw [sub_add_cancel] at h3
  refine h3.congr fun A => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eq_mix_of_mul {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} (hf : f * f = f)
    {a a' b b' : Matrix n n R} (ha : a * a' = 1) (hb : b' * b = 1)
    (h : b = f • a + (1 - f) • (1 : Matrix n n R)) : b' = f • a' + (1 - f) • (1 : Matrix n n R) := by
  have : b * (f • a' + (1 - f) • (1 : Matrix n n R)) = 1 := by
    rw [h, GlobalTheory.IdemSupport.mix_mul hf, ha, one_mul, GlobalTheory.IdemSupport.mix_self]
  calc b' = b' * (b * (f • a' + (1 - f) • (1 : Matrix n n R))) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hb, one_mul]

theorem tendsto_components : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  intro D V g hg ε hε gs hgs
  simp only [sum_placeIdem hε] at hgs
  have hinv : ∀ A, Formalism.L2.Theta.mt V (gs A)⁻¹ =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g⁻¹ +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun A =>
    eq_mix_of_mul (by rw [← RingHom.map_mul, pair_cutIdem_mul_self])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel, GlobalTheory.IdemSupport.mt_one]) (hgs A)
  have h1 := (tendsto_mix V hg).congr fun A => (hgs A).symm
  have h2 := (tendsto_mix V (inv_mem hg)).congr fun A => (hinv A).symm
  refine tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

end GlobalTheory.PlaceLimit

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




namespace GlobalTheory.LocalInvIdem

theorem toEAf_surj {D : D7} (a : EAf D) : ∃ α : AE D, toEAf D α = a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [RingHom.map_add (f := _), hp, hq]⟩
  | tmul x y => exact ⟨pairA D.host.F 0 y ⊗ₜ[D.host.F] x, rfl⟩

theorem inv_of_chart {D : D7} {ePP α : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hC : GlobalTheory.SplitHecke.Chart ePP v π) {c : Fv D.host.F v} (hc : π α = c) (hv1 : Valued.v c = 1) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv1; exact zero_ne_one hv1
  obtain ⟨t, ht⟩ := hC.1 c⁻¹
  refine ⟨ePP * t, ?_, ?_⟩
  · refine (hC.2.2.2 t).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
    rw [ht, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  · have h1 : π (α * t - 1) = 0 := by
      rw [map_sub, map_mul, ht, hc, mul_inv_cancel₀ hc0, map_one, sub_self]
    have h2 := (hC.2.1 _).1 h1
    linear_combination h2

theorem exists_local_inv {D : D7} {PP : Pl D.host.E} {ePP : AE D} (hPP : Formalism.L2.NTheta.IsIdemAt ePP PP)
    (α : AE D) (ha : toEAf D α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hu : IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D α, ha⟩)) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  obtain ⟨v, τ, hIdem, hP⟩ := GlobalTheory.SplitIdemDict.exists_emb hPP
  have hProj := (GlobalTheory.SplitIdemDict.isProjAt_iff τ PP).2 hP
  obtain ⟨⟨r, -, hr0, -, hrS⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v (splitProj τ) PP hProj
  obtain ⟨hC, hE, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v (splitProj τ) ePP hIdem
  obtain ⟨hmem, hrr⟩ := hrS (toEAf D α) ha
  obtain ⟨c, hc⟩ : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA (splitProj τ) α = c := ⟨_, rfl⟩
  have hcE := (hE α).trans hc
  have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hv1 : Valued.v c = 1 := by
    have hle : Valued.v c ≤ 1 := by
      rw [← hcE]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hmem
    refine le_antisymm hle (not_lt.1 fun hlt => hu.ne_zero ?_)
    rw [← hrr]
    refine (hr0 _).2 ?_
    exact (congrArg Valued.v hcE).trans_lt hlt
  exact inv_of_chart hC hc hv1

theorem exists_inv : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  intro D Z e he a ha hZ
  obtain ⟨α, rfl⟩ := toEAf_surj a
  obtain ⟨es, hes, hsum⟩ := he.1
  have key : ∀ PP ∈ Z, ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = es PP :=
    fun PP hPP => exists_local_inv (hes PP hPP) α ha (hZ PP hPP)
  choose! γ hγ1 hγ2 using key
  refine ⟨toEAf D (∑ PP ∈ Z, γ PP), GlobalTheory.IdemIntegral.toEAf_mem_of_finPart ?_, ?_⟩

  · rw [map_sum (finPart D)]; exact sum_mem fun PP hPP => hγ1 PP hPP
  · have hαw : α * ∑ PP ∈ Z, γ PP = e := by
      rw [Finset.mul_sum, hsum]; exact Finset.sum_congr rfl fun PP hPP => hγ2 PP hPP
    have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    rw [← map_mul, ← map_mul, hαw, hee]

end GlobalTheory.LocalInvIdem
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCoord

theorem isOpen_isCompact_of_comm {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]
    {m n : ℕ} (O : AddSubgroup K) (ho : IsOpen (O : Set K)) (hc : IsCompact (O : Set K))
    (A : AddSubgroup (Matrix (Fin m) (Fin n) K)) {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (h1 : ∀ y : Matrix (Fin m) (Fin n) K, (∀ i j, y i j ∈ O) → k • y ∈ A)
    (h2 : ∀ y ∈ A, ∀ i j, (M : K) * y i j ∈ O) :
    IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) ∧ IsCompact (A : Set (Matrix (Fin m) (Fin n) K)) := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hU : IsOpen {y : Matrix (Fin m) (Fin n) K | ∀ i j, (k : K)⁻¹ * y i j ∈ O} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ho.preimage (f := fun y : Matrix (Fin m) (Fin n) K => (k : K)⁻¹ * y i j) (by fun_prop)
  have hA : IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) := by
    refine A.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds fun i j => by simp) fun y hy => ?_)
    have := h1 ((k : K)⁻¹ • y) hy
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hk', one_smul] at this
  refine ⟨hA, ?_⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc.image (by fun_prop)
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) hC (A.isClosed_of_isOpen hA) fun y hy i _ j _ => ⟨_, h2 y hy i j, ?_⟩
  simp only [inv_mul_cancel_left₀ hM']

def mulHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ} (P : GL (Fin m) K)
    (Q : GL (Fin n) K) : Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin m) (Fin n) K where
  toFun x := P.val * x * Q.val
  invFun x := (P⁻¹).val * x * (Q⁻¹).val
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

variable {D : D7}

theorem toEAf_mem {w : AE D} (hw : finPart D w ∈ intAE D) : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

variable {v : FinPl D} {S T : HSp D} {e : AE D} {π : AE D →+* Fv D.host.F v}

theorem exists_half (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) : ∃ t : WO S T, IsHalf e t ∧ t.map π = y := by
  choose s hs using hπ.1
  refine ⟨Matrix.of fun i j => e * s (y i j), fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · rw [Matrix.of_apply, ← mul_assoc, he]
  · rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_mul, h1, one_mul, hs]

theorem bijOn_map (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1) :
    Set.BijOn (fun t : WO S T => t.map π) {t | IsHalf e t} Set.univ := by
  refine ⟨Set.mapsTo_univ _ _, fun x hx y hy h => Matrix.ext fun i j => ?_, fun y _ => exists_half hπ he h1 y⟩
  have h0 : π (x i j - y i j) = 0 := by
    rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h i) j
  rw [hπ.2.1, mul_sub, hx i j, hy i j, sub_eq_zero] at h0
  exact h0

private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ

theorem isOpen_isCompact_map {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (hinf : infPart D e = 0) :
    IsOpen ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) ∧
    IsCompact ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) := by
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F _).injective
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨k, hk, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) (selfDual_full S ΛS hS) (selfDual_full T ΛT hT)
  have hset : ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) =
      (((latO S T ΛS ΛT fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e).map π.toAddMonoidHom.mapMatrix :
        AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))) := by
    rw [AddSubgroup.coe_map]
    congr 1
    ext t
    exact and_congr_right fun _ => GlobalTheory.PlaceModel.isHalf_iff S T
  rw [hset]
  refine isOpen_isCompact_of_comm (v.adicCompletionIntegers D.host.F).toSubring.toAddSubgroup
    (Valued.isOpen_valuationSubring _) (isCompact_iff_compactSpace.2 (Formalism.L2.Col.rlt_compact_int v)) _ hk hM
    (fun y hy => ?_) ?_
  · obtain ⟨t, ht, rfl⟩ := exists_half hπ he h1 y
    refine ⟨k • t, ⟨hmul t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht) fun i j => toEAf_mem ?_,
      nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) k⟩, map_nsmul _ _ _⟩
    rw [← ht i j]
    exact (hπ.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 (hy i j))
  · rintro _ ⟨t, ⟨ht, ht'⟩, rfl⟩ i j
    have h2 : toEAf D ((M : AE D) * t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [RingHom.map_mul, map_natCast]; exact hden t ht i j
    have h3 : finPart D (e * ((M : AE D) * t i j)) ∈ intAE D := by
      rw [mul_left_comm, (GlobalTheory.PlaceModel.isHalf_iff S T).2 ht' i j]
      exact GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
    have h4 := GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 h3)
    rw [RingHom.map_mul, map_natCast] at h4
    exact h4

theorem infPart_split (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨a1, a2, v, ε, ⟨β, rfl, -⟩, a3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have hi' : e * (e + cA D e) = e := by rw [mul_add, a1, a2, add_zero]
  rw [← hi', a3, RingHom.map_mul, h0, mul_zero]

theorem isCoord_mapCo : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord e (latO S T ΛS ΛT fun _ => True) (mapCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), mapCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ T BT h)⁻¹).val * mapCo φ S T BS BT t * (grpCo φ S BS g).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  have hπ := (GlobalTheory.T.splitProjAdeleComponent_chart_properties D v φ e he).1
  have hcomp : mapCo φ S T BS BT = mulHomeo BT⁻¹ BS ∘ fun t : WO S T => t.map (rdA φ) := rfl
  have hoc := isOpen_isCompact_map (S := S) (T := T) hS hT hπ he.1.1 he.2.2 (infPart_split he.1)
  refine ⟨⟨fun x y => ?_, ?_, ?_, ?_⟩, fun g h t => ?_⟩
  · unfold mapCo
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
  · rw [hcomp]
    exact (Set.bijOn_univ.2 (mulHomeo BT⁻¹ BS).bijective).comp (bijOn_map hπ he.1.1 he.2.2)
  · rw [hcomp, Set.image_comp]
    exact (mulHomeo BT⁻¹ BS).isOpenMap _ hoc.1
  · rw [hcomp, Set.image_comp]
    exact hoc.2.image (mulHomeo BT⁻¹ BS).continuous
  · have e1 : ((grpCo φ T BT h)⁻¹).val = (BT⁻¹).val * (mt T h⁻¹).map (rdA φ) * BT.val := by
      have : (grpCo φ T BT h)⁻¹ = grpCo φ T BT h⁻¹ := by
        unfold grpCo
        rw [map_inv, map_inv, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
      rw [this]; rfl
    have e2 : (grpCo φ S BS g).val = (BS⁻¹).val * (mt S g).map (rdA φ) * BS.val := rfl
    rw [e1, e2]
    unfold mapCo actO
    rw [inv_inv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]

end GlobalTheory.PlaceCoord

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stableFockSpan_contains_rowHighestPolynomials : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → T.rank ≤ S.rank → ∀ B₀, C.IsB B₀ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∀ f, C.IsTh f → C.IsFock B₀ f → f ≠ 0 → ∀ (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ = C.X.p0) → (∀ τ, q τ = C.q0) → ∀ (pt : MvPolynomial (FVar D T.rank S.rank) ℂ → WO S T → ℂ) (U : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ)), (∀ P, pt P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P) → Formalism.IndefR.Datum.delta p q ap am ∈ U → (∀ h ∈ GinfC S, ∀ P ∈ U, ∃ P' ∈ U, om (h, 1) (pt P) = pt P') → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ ∧ ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q₀ : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q₀ ∈ Harm.rowHighest ℂ c c' ∧ C.fvec (revB C.X.p0 B₀) f Q₀ = pt (Formalism.IndefR.Datum.delta p q ap am) ∧ pt (Formalism.IndefR.Datum.delta p q ap am) ≠ 0 ∧ ∀ Q, C.toH Q ∈ Harm.rowHighest ℂ c c' → ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
  first | exact @GlobalTheory.AdSpan.StableFock.fockSpan_rowHighest | exact GlobalTheory.AdSpan.StableFock.fockSpan_rowHighest | (intros; apply GlobalTheory.AdSpan.StableFock.fockSpan_rowHighest <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.conjCharacter_eq_prod_symmetricEdge_characters_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  first | exact @GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | exact GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | (intros; apply GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.flatTensor_moveArguments_lastRow_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (F : Γ.Args → ℂ)
    (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin (topRank Γ (j + 1))) (Γ.m - 1 - (j + 1)), toFrame hs hj g = v * embX _ κ →
    ∀ (x : ColArgs Γ) (y : RowArgs Γ),
      flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z)) x y = flatTensor hs ψ ν F (colMove j κ x) y := by
  first | exact @GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle | exact GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle | (intros; apply GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
        ∀ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u) g g₁ →
        ∃ f₁ ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) f₁ := by
  first | exact @GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv | exact GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv | (intros; apply GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv <;> assumption)
end
