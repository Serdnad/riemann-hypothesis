module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergComb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle568
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle435
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MovedJoin
open GlobalTheory.AdForm


open _root_.Formalism.L2.Col in
theorem adAt_kb_eq_frsF {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (i : ℕ) (hi : i ≤ B.R.m) (β : Ch₀ i) (r s : Fin (B.R.N i)) :
    adAt B.host.F P.1 (((A.kb i β : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) _) r s) =
      algebraMap B.host.E _ (frsF I.sel (I.tup a) (A.p0 i β).1.1 P (Pi.single s 1) r) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have h1 := ((hA.base i hi β).1).fr ⟨P.1, hSQ⟩ r s
  rw [h1, extTo_fr, frsF_eq_ptFr]

theorem adAt_kStd_of_twist {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) (a : I.ι) (P : BadPr I a)
    (hP : P.1 ∉ (B.primes X).vGs) (u : B.Word) (n : ℕ) (r s : Fin n) :
    adAt B.host.F P.1 (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      algebraMap B.host.E _ (if r = s then 1 else 0) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 (Finset.mem_union_right _ hSQ)
  have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) (GlobalTheory.BasePrimes.primes_ok B X).1 u n).2.1 _ hT
  have he := congrArg (fun g => (g.1 : Matrix (Fin n) (Fin n) _) r s) hb
  simp only [Units.val_one] at he
  have h2 : Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) ((1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
    refine he.trans ?_
    by_cases h : r = s <;> simp [Matrix.one_apply, h]
  rw [GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 h2]
  by_cases h : r = s <;> simp [Matrix.one_apply, h]

theorem map_eq_one_of_pr {D : Formalism.BasicNotions.D7} {k : Type} [CommRing k] {n : ℕ} (φ : Formalism.L2.Theta.AE D →+* k)
    (M : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))
    (h : ∀ c d, φ (M c d) = φ (Formalism.L2.Theta.incA D (if c = d then 1 else 0))) : M.map φ = 1 := by
  ext c d
  rw [Matrix.map_apply, h, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_frameγ_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (M : Matrix (Fin N) Y k) (r : Fin N) (b : Y) :
    (M * F.γ) r (e' b) = M r b := by
  have h1 : M * F.γ * F.β = M := by rw [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 r) b
  rw [hF, Matrix.mul_apply] at h2
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem frameβ_mul_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (g : Matrix Y Y k) (r b : Y) :
    (F.β * g) (e' r) b = g r b := by
  rw [hF, Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem map_eq_sum_frame {E k : Type} [Field E] [CommRing k] {n : ℕ} (φ : E →+* k) (f : (Fin n → E) ≃ₗ[E] (Fin n → E)) (y : Fin n → E)
    (x : Fin n) : φ (y x) = ∑ c, φ (f (Pi.single c 1) x) * φ (f.symm y c) := by

  conv_lhs => rw [← f.apply_symm_apply y, pi_eq_sum_univ' (f.symm y), map_sum]

  rw [Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]

end GlobalTheory.Fam.MovedJoin

namespace GlobalTheory.Fam
open GlobalTheory.AdForm GlobalTheory.Fam.MovedJoin


end GlobalTheory.Fam
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relIndex_couplingCosetStabilizer_eq_chartWeight : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)), (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  first | exact @GlobalTheory.PenVol.relIndex_cosStab_eq_wt | exact GlobalTheory.PenVol.relIndex_cosStab_eq_wt | (intros; apply GlobalTheory.PenVol.relIndex_cosStab_eq_wt <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc



namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_compFin (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D)
    (ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) * a = a) :
    secW hw h (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)) = a := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h _)) = a
  rw [RingEquiv.symm_apply_apply]
  conv_rhs => rw [← ha]
  rw [show algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 from rfl,
    GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

theorem exists_uPt_eq (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} (hk0 : k ≠ 0) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) {u : WO S T}
    (hu : IsHalf (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) u) :
    ∃ y, uPt hw h k aS aT y = u := by
  let U : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) :=
    u.map fun a => GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)
  refine ⟨k⁻¹ • ((aT⁻¹).1 * U * aS.1), ?_⟩
  have e1 : k • (aT.1 * (k⁻¹ • ((aT⁻¹).1 * U * aS.1)) * (aS⁻¹).1) = U := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk0, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply]
  exact secW_compFin hw h _ (hu i j)


open GlobalTheory.Hk3 GlobalTheory.InertLoc GlobalTheory.SplitScalar GlobalTheory.FinWeilO in

theorem om_mem_span_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v), UnrAt χS w → UnrAt χT w → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsUnramInv ϖ c (qV D.host.F v) → IsConjAt D.sp.cm.sig h c → GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ f, VacFin ψ S T v f → ∀ (gS : Gv S v) (gT : Gv T v), om (embV S v gS, embV T v gT) f ∈ Submodule.span ℂ (Set.range fun x => heisO ψ S T (uPt hw h k aS aT x) f) := by
  intro D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gaS gaT f hf gS gT
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have hP : Formalism.DivisionValues.conjPl w = w := by
    by_contra hne
    exact GlobalTheory.LFun.not_isSplit_of_isInertAt hw (dict.1.2 hne)
  have he : IsPrimeIdem w (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v))
      (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) :=
    GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert hw (GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D v)
  set e := algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) with he_def
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  obtain ⟨ϖ0, σ, q, π, hU0, h2, hc0, hV⟩ := exists_chart hP he
  obtain ⟨βS, ιS, hS, gS'⟩ := hV S
  obtain ⟨βT, ιT, hT, gT'⟩ := hV T
  have hψ := hW.std
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := exists_delta_psi hU0 h2 (th ψ hc0 k) (th_conj hc0 hU0.1) (by
    obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
    refine th_cond hψ hc0 hU0.2.1 hβ ⟨0, ?_⟩ hk
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Ranks.rankX', Ranks.r]
    omega)
  let ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D w) → Module.End ℂ (thetaSub ψ S T) := fun x =>
    (heisL ψ S T (kap hc0 βS βT k x)).restrict fun _ hf =>
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (hc0.half_fin (kap_half hc0 x)) hf
  have hρ : ∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (kap hc0 βS βT k x) m := fun _ _ => rfl
  let ω : Formalism.UG.UJ σ (1 : Matrix (Fin S.rank) (Fin S.rank) (LP D w)) ×
      Formalism.UG.UJ σ (1 : Matrix (Fin T.rank) (Fin T.rank) (LP D w)) →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := fun p => (om (ιS p.1, ιT p.2)).restrict fun _ hf => hW.om_pres _ _ hf
      map_one' := LinearMap.ext fun m => Subtype.ext (by
        show om (ιS 1, ιT 1) m = m
        rw [map_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply])
      map_mul' := fun p p' => LinearMap.ext fun m => Subtype.ext (by
        show om (ιS (p.1 * p'.1), ιT (p.2 * p'.2)) m = om (ιS p.1, ιT p.2) (om (ιS p'.1, ιT p'.2) m)
        rw [map_mul, map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]) }
  have hω : ∀ g g' (m : thetaSub ψ S T), (ω (g, g') m : WO S T → ℂ) = om (ιS g, ιT g') m := fun _ _ _ => rfl
  have hlat := kap_mem_iff hc0 hU0.2.1 hS hT hk
  have hvac0 : ∀ m : thetaSub ψ S T, LocVac ρ m ↔
      ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u m = m := fun m => by
    refine ⟨fun hm u hu hh => ?_, fun hm x hx => Subtype.ext (hm _ ((hlat x).2 hx) (kap_half hc0 x))⟩
    obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
    exact congrArg Subtype.val (hm x ((hlat x).1 hu))
  have hvac : ∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T w m := fun m => by
    rw [hvac0]
    refine ⟨fun hm => ⟨m.2, fun e' f' he' u hu hh => hm u hu ?_⟩, fun hm u hu hh => hm.2 e e he u hu (Or.inl hh)⟩
    obtain ⟨rfl, -⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 w e e he).2.2.2.1 e' f' he'
    rwa [hc0.1.2.1, or_self] at hh
  have hhyp : ∀ {V : HSp D} {β ι}, GrpChart V e σ π β ι → ∀ g, ι g ∈ hyp V w ↔
      g.1 ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.intL (LP D w)) := fun hι g =>
    ⟨fun hg => (hι.2.2.2 g).1 hg.1, fun hg => ⟨(hι.2.2.2 g).2 hg, e, e, he, hι.1 g⟩⟩
  have hone : ∀ (n : ℕ) (i j : Fin n), σ ((1 : Matrix (Fin n) (Fin n) (LP D w)) i j) = (1 : Matrix (Fin n) (Fin n) (LP D w)) j i :=
    fun n i j => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, σ.map_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), σ.map_zero]
  have hLP : LocPair ϖ0 σ q δ (1 : GL (Fin S.rank) (LP D w)) (1 : GL (Fin T.rank) (LP D w)) ψ' ρ ω := by
    refine ⟨hU0, odd_of_v_two hU0 h2, one_mem _, one_mem _, hone _, hone _, hδ, p1, p2, ?_, fun x y => ?_, ?_,
      fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [hρ, kap_zero, heisO_zero, Module.End.one_apply]
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [Module.End.mul_apply, hρ, hρ, heisO_heisO, symplOH_kap hc0 hS hT, LinearMap.smul_apply, Submodule.coe_smul, hρ,
        kap_add, locH, p3, inv_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    · refine span_vacua hψ hc0.1.1 hc0.1.2.1 (fun u hu hh => ?_) _ fun u hh s m hs hm => ?_
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        refine ⟨kap hc0 βS βT k ((2⁻¹ : LP D w) • x), (hlat _).2 fun i j => mul_mem (mem_intL.2 ?_) ((hlat x).1 hu i j), ?_⟩
        · rw [map_inv₀, h2, inv_one]
        · rw [← kap_add, half_add_half]
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        exact Submodule.subset_span ⟨x, s, (hvac0 s).2 hs, Subtype.ext hm⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      show om (ιS g, ιT g') (heisO ψ S T (kap hc0 βS βT k x) m) = heisO ψ S T (kap hc0 βS βT k _) (om (ιS g, ιT g') m)
      rw [hW.om_heis _ _ _ _ m.2, actO_kap hc0 gS' gT']
    · exact Subtype.ext (hfix _ ((hvac s).1 hs) _ ((hhyp gS' g).2 hg) _ ((hhyp gT' g').2 hg'))
  obtain ⟨r1, hr1⟩ := gS'.2.2.1 (embV S v gS) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem S he h _).2 ⟨gS, rfl⟩)
  obtain ⟨r2, hr2⟩ := gT'.2.2.1 (embV T v gT) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem T he h _).2 ⟨gT, rfl⟩)
  let fM : thetaSub ψ S T := ⟨f, hf.1⟩
  have hvf : LocVac ρ fM := (hvac fM).2 (dict.2.2.2.1 ψ S T f hf)
  haveI : CharZero (LP D w) := algebraRat.charZero _
  obtain ⟨cc, hcc⟩ := locPair_act_vac_comb (LP D w) ϖ0 σ q δ S.rank T.rank 1 1 ψ' (thetaSub ψ S T) ρ ω hLP (r1, r2)
  have e1 : om (embV S v gS, embV T v gT) f = ((ω (r1, r2) fM : thetaSub ψ S T) : WO S T → ℂ) := by
    rw [hω, hr1, hr2]
  rw [e1, hcc fM hvf, Finsupp.sum, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [Submodule.coe_smul, hρ]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨y, hy⟩ := exists_uPt_eq hw h hk.1 aS aT (kap_half hc0 x)
  rw [← hy]
  exact Submodule.subset_span ⟨y, rfl⟩

end GlobalTheory.InertFrameLoc
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcTheta

section Lift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {χS χT : (AE D)ˣ →* Circle}
  {om : Om S T}

theorem contAut_ker (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ} (hφ : IsContAut A φ)
    (hΞ : IsThetaFunO ψ S T Ξ) (h : GA D T) (u : WO L T) :
    IsContAut A fun a => φ a * om (o.emb (a, 1), h) Ξ ((o.resS T).symm (0, u)) := by
  refine ⟨fun γ hγ a => ?_, hφ.2.mul ((hW.om_cont Ξ hΞ _).comp
    ((o.continuous_emb.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const))⟩
  have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ hW Ξ hΞ _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (a, 1)) h
    ((o.resS T).symm (0, u))
  rw [← map_mul, Prod.mk_mul_mk, one_mul, one_mul, inv_one, mt_one, Matrix.one_mul] at e
  beta_reduce
  rw [hφ.1 γ hγ, e]
  congr 2
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, OrthDec.pB_emb, mt_one, Matrix.one_mul]

theorem liftA_add_left (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ φ' : GA D A → ℂ}
    {Ξ : WO S T → ℂ} (hφ : IsContAut A φ) (hφ' : IsContAut A φ') (hΞ : IsThetaFunO ψ S T Ξ) :
    liftA o om vA (φ + φ') Ξ = liftA o om vA φ Ξ + liftA o om vA φ' Ξ := by
  funext h w
  simp only [liftA, Pi.add_apply, add_mul]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ' hΞ h _))

theorem liftA_add_right (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ}
    {Ξ Ξ' : WO S T → ℂ} (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (hΞ' : IsThetaFunO ψ S T Ξ') :
    liftA o om vA φ (Ξ + Ξ') = liftA o om vA φ Ξ + liftA o om vA φ Ξ' := by
  funext h w
  simp only [liftA, map_add (f := _), Pi.add_apply, mul_add]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ' h _))

theorem liftA_smul_left (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA (c • φ) Ξ = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem liftA_smul_right (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA φ (c • Ξ) = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

theorem liftA_equiv (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ}
    (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (a : GA D A) :
    liftA o om vA (fun x => φ (x * a)) (om (o.emb (a, 1), 1) Ξ) = liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA]
  refine Eq.trans ?_ (Comm.integral_right vA (contAut_ker o hW hφ hΞ h w).1 a)
  congr 1
  funext x
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end Lift

theorem exists_linear_of_rel {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : Submodule ℂ M) (R : M → N → Prop) (hex : ∀ x ∈ P, ∃! y, R x y)
    (hlin : ∀ (c : ℂ) x y x' y', R x y → R x' y' → R (c • x + x') (c • y + y')) :
    ∃ G : M →ₗ[ℂ] N, (∀ x, ∃ x', R x' (G x)) ∧ ∀ x ∈ P, R x (G x) := by
  choose F hF hFu using fun x : P => hex x.1 x.2
  have hc : ∀ (c : ℂ) (x x' : P), F (c • x + x') = c • F x + F x' := fun c x x' =>
    (hFu (c • x + x') _ (hlin c _ _ _ _ (hF x) (hF x'))).symm
  have h0 : F 0 = 0 := by
    have := hc 1 0 0
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  let F' : P →ₗ[ℂ] N :=
    { toFun := F
      map_add' := fun x y => by simpa using hc 1 x y
      map_smul' := fun c x => by simpa [h0] using hc c x 0 }
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  refine ⟨F' ∘ₗ P.linearProjOfIsCompl Q hQ, fun x => ⟨_, hF _⟩, fun x hx => ?_⟩
  have e : P.linearProjOfIsCompl Q hQ x = ⟨x, hx⟩ := Submodule.linearProjOfIsCompl_apply_left hQ ⟨x, hx⟩
  rw [LinearMap.comp_apply, e]
  exact hF ⟨x, hx⟩

theorem exists_theta : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ S A L T o ζ _ hA vA χS χT om hW α α₀ β hsum
  obtain ⟨lS, lT, hlS, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  refine ⟨lS, hlS, fun LS LT f₀ hLS hLT hvac => ?_⟩
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW.std S T α₀ β LS LT hLS hLT f₀ hvac
  obtain ⟨G, hG, hGP⟩ := exists_linear_of_rel (SB (Matrix n (n' ⊕ Fin 1) k)) (Over ψ α₀ β LS LT f₀) hex
    (fun c x y x' y' h h' => (hlin n _ α₀ β LS LT f₀ x y h).2.2 c x' y' h')
  have hGt : ∀ Φ, IsThetaFunO ψ S T (G Φ) := fun Φ => (hG Φ).elim fun x hx => (hth _ _ hx).1
  have hGf : ∀ Φ f, Over ψ α₀ β LS LT f₀ Φ f → G Φ = f := fun Φ f h =>
    (hex Φ h.2.2.2.1).unique (hGP Φ h.2.2.2.1) h
  let θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Φ => liftA o om vA v (G Φ))
      (fun v v' Φ => liftA_add_left o hA vA hW v.2 v'.2 (hGt Φ))
      (fun c v Φ => liftA_smul_left o vA c v (G Φ))
      (fun v Φ Φ' => by rw [map_add (f := _)]; exact liftA_add_right o hA vA hW v.2 (hGt Φ) (hGt Φ'))
      (fun c v Φ => by rw [map_smul]; exact liftA_smul_right o vA c v (G Φ))
  have hθ : ∀ (v : CA A) Φ, θ v Φ = liftA o om vA v (G Φ) := fun _ _ => rfl
  refine ⟨θ, fun v Φ f h => by rw [hθ, hGf Φ f h], fun g v Φ hΦ => ?_⟩
  have h1 := (hlin n _ α₀ β LS LT f₀ Φ _ (hGP Φ hΦ)).1 (blk g) 1
  have hdet : Matrix.GeneralLinearGroup.det (blk g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hemb : α₀.gl (blk g) = o.emb (α.gl g, 1) := by
    rw [Comm.emb_gl hsum]
    congr 1
  have hfun : (fun x : Matrix n (n' ⊕ Fin 1) k => (lS (Matrix.GeneralLinearGroup.det (blk g)) : ℂ) *
      (lT (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂ) * Φ (((1 : GL n k)⁻¹ : GL n k).val * x * (blk g).val)) =
      (lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val) := by
    funext x
    simp only [hdet, map_one, Units.val_one, mul_one, inv_one, Matrix.one_mul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, hemb, map_one] at h1
  have h2 : θ (caRep α g v) ((lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val)) = θ v Φ := by
    rw [hθ, hθ, hGf _ _ h1]
    exact liftA_equiv o vA hW v.2 (hGt Φ) (α.gl g)
  rw [← h2, map_smul, inv_smul_smul₀ (Units.ne_zero _)]

end GlobalTheory.FinPl.SrcTheta

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm

theorem omLoc : ∀ (D : D7), OmLoc D := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT hμS hμT Y Y' _ _ _ _ FS FT Tm hTm g gk h hk hg hh Φ Φ' hΦ'
  have U := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hW.std).1
  have enl : ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → Enl gk hk →
      LawLoc ω μS μT Tm g gk h hk := by
    intro g gk h hk hg hh he
    obtain ⟨T₂, hT₂, hT₂e⟩ := GlobalTheory.T.conj_splitLocalModel_by_supported_pair D k p ψ S T χS χT ω hW μS μT Y Y' FS FT Tm hTm g gk h hk hg hh
    obtain ⟨Φ₀, Φ₀', h0, h0', hv⟩ := GlobalTheory.T.weil_vacuum_local_model_integral_matrix_pair D k p ψ S T χS χT ω hW μS μT hμS hμT Y Y' FS FT Tm hTm g gk h hk hg hh he
    have inv1 : ∀ F, ω (g⁻¹, h⁻¹) (ω (g, h) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have inv2 : ∀ F, ω (g, h) (ω (g⁻¹, h⁻¹) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hT : T₂ = Tm := U T₂ Tm hT₂ hTm Φ₀ h0 (by rw [hT₂e Φ₀ Φ₀' h0', ← hv, inv1])
    intro Φ Φ' hΦ'
    have := hT₂e Φ Φ' hΦ'
    rw [hT] at this
    rw [this, inv2]
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_preservesIntegralMatricesSubst k Y Y' gk hk
  obtain ⟨zk, hzk⟩ : ∃ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) :=
    ⟨Units.map (Matrix.scalar Y : k →+* Matrix Y Y k).toMonoidHom c, by
      simp [Matrix.smul_one_eq_diagonal]⟩
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_splitLocal_supported_scalar_component D k p T Y FT c zk hzk
  have iS := GlobalTheory.T.splitLocalComponents_one_mul_inv D k p S Y' FS
  have iT := GlobalTheory.T.splitLocalComponents_one_mul_inv D k p T Y FT
  have l1 := enl g gk (h * z⁻¹) (hk * zk⁻¹) hg (iT.2.1 _ _ _ _ hh (iT.2.2 _ _ hz)) (hc zk hzk).1
  have l2 := enl 1 1 z⁻¹ zk⁻¹ iS.1 (iT.2.2 _ _ hz) (hc zk hzk).2
  have l3 := GlobalTheory.T.linearLaw_localModel_mul_closed D k S T ω μS μT Y Y' Tm _ _ _ _ _ _ _ _ l1 (GlobalTheory.T.linearLaw_localModel_inv D k S T ω μS μT Y Y' Tm _ _ _ _ l2)
  simp only [inv_one, mul_one, inv_inv, inv_mul_cancel_right] at l3
  exact l3 Φ Φ' hΦ'

end GlobalTheory.LocOm

end
end
