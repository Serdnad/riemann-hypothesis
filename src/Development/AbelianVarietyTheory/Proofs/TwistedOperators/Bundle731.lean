module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle321
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle596
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle727
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle693
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle726
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle724
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (d : FinDatum ch.G t p) (c : WO (ch.G.pS p) (ch.G.pT p) →₀ ℂ), d.z = 1 → ch.S.Z.HasVec d → IsCombOf ch.W d c → movedVec t ch.S.toGridChoice d = comb ch.W.ψ _ _ c (ch.W.om p (ch.G.toPair p (ch.S.N.u p.small).1 (ch.S.N.u p.big).1) (ch.S.Z.vac p)) := by
  first | exact @GlobalTheory.MovedComb.movedVec_eq_comb | exact GlobalTheory.MovedComb.movedVec_eq_comb | (intros; apply GlobalTheory.MovedComb.movedVec_eq_comb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto.IntDatum

theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

theorem finPart_mul_inv_mem {D : D7} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (s : 𝓞 D.host.E)
    (hs : ∀ P ∈ S, s ∉ P.asIdeal) (hs0 : s ≠ 0) : finPart D (e * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he

  rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  by_contra h
  exact hs PP hPP (((hes PP hPP).2 s hs0).2 h)

end GlobalTheory.CoreOnto.IntDatum

open GlobalTheory.CoreOnto.IntDatum in
theorem GlobalTheory.CoreOnto.IntDatum.psi_int : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)), ∀ a ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf (cA D e) a → W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) a) = 1 := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he x₀ hx₀ a ha _
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set N : ℕ := Ideal.absNorm D.host.ccK with hNdef
  have hN : ∀ P ∈ G.pl.W0, ((N : 𝓞 D.host.E)) ∉ P.asIdeal := by
    intro P hP h
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by
      unfold Places.W0 at hP
      simpa using hP
    refine GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces G.pl hv ?_
    rw [← G.pl.under_w hv]
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal
    rwa [map_natCast]
  have hNn : N ≠ 0 := by
    rw [hNdef]
    exact fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hs0 : (N : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hN0 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hα : ((N : 𝓞 D.host.E) : D.host.E) ∈ D.host.AA := by
    have := GlobalTheory.HostClear.absNorm_mem_AA D
    push_cast
    exact this
  have h1 := GlobalTheory.AscFinWit.rat_mem_latO (P := fun _ => True) hS hT x₀ (fun y hy => hx₀ y hy) hα
  have h2 := finPart_mul_inv_mem he (N : 𝓞 D.host.E) hN hs0
  have h3 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ h2 _ h1
  refine GlobalTheory.AscFinWit.psi_eq_one (P := fun _ => True) W.ψ_std hS hT ?_ ha
  convert h3 using 1
  have hu : incA D ((N : 𝓞 D.host.E) : D.host.E)⁻¹ * incA D ((N : 𝓞 D.host.E) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hN0, map_one]
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.MixModel.rat, Matrix.map_apply, map_mul]
  linear_combination (GlobalTheory.FinPlLoc.idem D fun _ => True) * e * incA D (x₀ j k) * hu.symm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.RowVacScalar



theorem splitScal_mul_eq_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S t ht j hj k hk w hw hs
  have hK : inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w) _ := by
    have h1 := hk
    simp only [GridChoice.levRow, prodLev, Subgroup.mem_inf, Subgroup.mem_iInf] at h1
    have h2 := h1.1 ⟨w, hw⟩
    rw [Subgroup.mem_comap] at h2
    rwa [GlobalTheory.LastRowLat.givenLevel_inner G t w (j + 1, D.R.m) (by simp) (by simp; have := D.R.two_le_m; omega)] at h2
  have he : idemAt w * idemAt w = idemAt w := (Classical.epsilon_spec hs).1.1
  have d1 : ∀ V : HSp D, detIdl (idemAt w) V 1 = 1 := fun V => by
    unfold detIdl; split_ifs <;> simp
  have dneg : detIdl (idemAt w) (negSp (G.V (.grid (j + 1) D.R.m))) (negGA _ (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := by
    refine Units.ext ?_
    rw [detIdl_val he, detIdl_val he, mt_negGA]
  have hpar : Odd (G.pS (.chi (j + 1) D.R.m)).rank ↔ Odd (G.pT (.chi j D.R.m)).rank := by
    have r0 := (rank_vertex G t w (X := (j, D.R.m)) ⟨by omega, le_rfl⟩).symm
    have r2 := (rank_vertex G t w (X := (j + 1 + 1, D.R.m)) ⟨by omega, le_rfl⟩).symm
    change Odd (G.V (.grid (j + 1 + 1) D.R.m)).rank ↔ Odd (G.V (.grid j D.R.m)).rank
    rw [r0, r2]
    simp only [Grid.rank, locGrid]
    rw [show D.R.r + D.R.m * D.R.t + (j + 1 + 1) * sLen D = (D.R.r + D.R.m * D.R.t + j * sLen D) + 2 * sLen D by ring]
    rw [Nat.odd_add]
    exact ⟨fun h => h.2 (even_two_mul _), fun h => ⟨fun _ => even_two_mul _, fun _ => h⟩⟩
  have key : ∀ (a b η : (AE D)ˣ →* Circle) (n n' : ℕ), (Odd n ↔ Odd n') → ∀ x,
      (Formalism.IndefR.Lift.attChr a η n x)⁻¹ * Formalism.IndefR.Lift.attChr b η n' x = (a x)⁻¹ * b x := by
    intro a b η n n' h x
    unfold Formalism.IndefR.Lift.attChr
    by_cases hn : Odd n
    · rw [if_pos hn, if_pos (h.1 hn), MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv,
        mul_comm (η x), mul_mul_mul_comm, mul_inv_cancel, mul_one]
    · rw [if_neg hn, if_neg (fun h' => hn (h.2 h'))]
  have hχ : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ y, ((G.ch.chi i (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((G.ch.chiH i).loc w y : ℂˣ) : ℂ) := fun i h1 h2 y => by
    have := congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq i h1 h2) w)
    simpa [GlobalTheory.LFun.locChar] using this
  refine Eq.trans ?_ (GlobalTheory.T.oppositePath_edgeFactor_prod_integral_vertex (locGrid G t w) j hj _ hK).symm
  simp only [splitScal, GridData.toPair, splitFacO, map_one, d1, inv_one, one_mul, mul_one]
  have eqS : detIdl (idemAt w) (G.pS (Pair.chi j D.R.m)) ((negGA (G.V (Node.grid (j + 1) D.R.m))) (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := dneg
  have eqT : detIdl (idemAt w) (G.pT (Pair.chi (j + 1) D.R.m)) (moved S j k) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := rfl
  rw [eqS, eqT, GlobalTheory.T.determinantIdeleAtSplitPlace_moved_gridNode S t j hj k w hs, ← Circle.coe_mul]
  rw [GridData.chrT, GridData.chrS]
  rw [key (G.chr (Pair.chi j D.R.m)) (G.chr (Pair.chi (j + 1) D.R.m)) L.eta _ _ hpar.symm]
  rw [Circle.coe_mul, Circle.coe_inv]
  dsimp only [GridData.chr]
  rw [hχ _ (by omega) (by omega), hχ _ (by omega) (by omega)]
  simp only [locGrid, Units.val_inv_eq_inv_val]
  exact mul_comm _ _

end GlobalTheory.RowVacScalar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem suppAt_conj {V : HSp D} {e : AE D} {y : GA D V} (h : SuppAt e V y) (δ : GA D V) : SuppAt e V (δ * y * δ⁻¹) := by
  have hs : (e + cA D e) • (mt V y - 1) = mt V y - 1 := Matrix.ext fun i j => h i j
  have hδ : mt V δ * mt V δ⁻¹ = 1 := by rw [← GlobalTheory.MixModel.mt_mul, mul_inv_cancel, GlobalTheory.MixModel.mt_one]
  have key : mt V (δ * y * δ⁻¹) - 1 = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hδ]
  have h2 : (e + cA D e) • (mt V δ * (mt V y - 1) * mt V δ⁻¹) = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hs]
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasLoc_conj (B : Frames G) (t : T) {j : ℕ} (hj : j ≤ D.R.m) {y : GA D (G.V (.grid D.R.m j))}
    {g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)} (h : HasLoc t B hj y g)
    (δ : GA D (G.V (.grid D.R.m j))) :
    HasLoc t B hj (δ * y * δ⁻¹) (fun w => locAt B t w.1 j hj δ * g w * (locAt B t w.1 j hj δ)⁻¹) := by
  obtain ⟨e, he, hs, hl⟩ := h
  refine ⟨e, he, suppAt_conj hs δ, fun w => ?_⟩
  change locAt B t w.1 j hj (δ * y * δ⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  exact congrArg (fun z => locAt B t w.1 j hj δ * z * (locAt B t w.1 j hj δ)⁻¹) (hl w)

theorem conj_rowR' {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    {x y : GL (Fin (Γ.rank (Γ.m, j))) k} (hy : ∃ f, (toFrame hs hj y).val = diagonal f) (hx : x ∈ rowR hs hj) :
    y * x * y⁻¹ ∈ rowR hs hj := by
  obtain ⟨f, hf⟩ := hy
  have hy' : ∃ f, (toFrame hs hj y⁻¹).val = diagonal f :=
    ⟨Ring.inverse f, by rw [map_inv, Matrix.coe_units_inv, hf, Matrix.inv_diagonal]⟩
  have := conj_rowR hs hj (g := fun _ => 1) hy' hx
  have e1 : GlobalTheory.SplitFlip.diagGL (fun _ => (1 : kˣ)) = (1 : GL (Fin (Γ.rank (Γ.m, j))) k) :=
    Units.ext (by rw [GlobalTheory.SplitFlip.diagGL_val]; exact diagonal_one)
  rwa [e1, mul_one, inv_inv] at this

theorem sgn_diag {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    (c : Fin (Γ.rank (Γ.m, j)) → kˣ) : ∃ f, (toFrame hs hj (GlobalTheory.SplitFlip.diagGL c)).val = diagonal f := by
  have h : topRank Γ j + (Γ.m - 1 - j) = Γ.rank (Γ.m, j) := by have := topRank_add hs j; omega
  exact ⟨_, submatrix_diagonal_equiv (fun i => (c i : k)) (frame h)⟩

end GlobalTheory.RowLift


open GlobalTheory.RowLift GlobalTheory.RowRep in
theorem GlobalTheory.RowLift.lift_rowR : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  obtain ⟨C1, hJ⟩ := GlobalTheory.T.mem_fourierJacobiGroup_of_local_lattice_matrices
  obtain ⟨C2, hB⟩ := GlobalTheory.T.mem_besselGroup_of_local_lattice_matrices
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hx1⟩ := hJ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, hx2⟩ := hB ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  intro s t j hjI hj hj' δ hδ l hl
  obtain ⟨y, hy⟩ := exists_hasLoc hS.core.lev ch.S.B t hj (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹)
  refine ⟨y, hy, ?_⟩
  have hc := hasLoc_conj ch.S.B t hj hy δ
  have hm : ∀ w : locPl ch.G t, locAt ch.S.B t w.1 j hj δ * (sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) *
      (locAt ch.S.B t w.1 j hj δ)⁻¹ ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj' := fun w =>
    conj_rowR' one_le_sLen hj' (locAt_tilt ch.S.toGridChoice (Set.mem_univ t) w.2 hj hj' hδ)
      (conj_rowR' one_le_sLen hj' (sgn_diag one_le_sLen hj' _) (hl w))
  unfold rowGrp
  split_ifs with h1 h2
  · exact hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' _
      (by have := (idx_le hjI); omega) _ _ hc hm
  · exact hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' h2 _ _ hc hm
  · exfalso; have := idx_le hjI; omega
end
end
