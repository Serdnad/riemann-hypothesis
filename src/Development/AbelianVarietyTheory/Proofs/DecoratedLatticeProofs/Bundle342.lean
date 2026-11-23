module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle334
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanInvolutionEqOfCommute
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle325
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFreeEntryTranslationLawsBesselToJaco
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapTranslationLawsJacobiToBesselFree
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.TwResid

theorem phiT_tw {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1)))
    (hp : TC.PtOf k p.1.1) (hpN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i))
    (hp' : TC.PtOf k' p'.1.1) (hpN' : p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)))
    (hq : TC.PtOf (y * k) q.1.1) (hq' : TC.PtOf (y' * k') q'.1.1) :
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      Formalism.L2.Col.phiT B.fields.K p.1.1.deco.1 p'.1.1.deco.1 x₀ = Formalism.L2.Col.phiT B.fields.K q.1.1.deco.1 q'.1.1.deco.1 x := by
  refine ⟨∏ P ∈ (B.primes X).vT u, Ideal.absNorm P.asIdeal,
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot), fun M₀ hM x x₀ h => ?_⟩
  exact GlobalTheory.Transport.LevelDatum.phiT_eq B.fields.K (B.R.N_pos i) (B.R.N_pos (i + 1)) hp hpN hp' hpN' hq hq' x x₀
    fun P hP r s => lt_of_le_of_lt (h P hP r s) (GlobalTheory.Transport.LevelDatum.val_natCast_lt hM hP)

theorem xiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hok : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ)
    (hi : i + 1 ≤ B.R.m)
    (b : Idx I.sel (I.tup a) (I.idx a) i) (b' : Idx I.sel (I.tup a) (I.idx a) (i + 1))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p → cosetIn q' = cosetIn p' →
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ∀ r s,
        Valued.v (adAt B.host.F P
          ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B (B.R.N (i + 1))).1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E))
          ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
          (y.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
          ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
        Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)) →
      xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' x₀ =
        xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' q q' x := by
  intro B X I l hok u a i hi b b' p q p' q' k y k' y' hk hN hk' hN' hq hq' hc hc'
  obtain ⟨M1, hM1, H1⟩ := phiT_tw I u a i p q p' q' k y k' y' hk hN hk' hN' hq hq'
  have Hent := GlobalTheory.T.entryDatum_transport_badPrime_anyTuple I hok l u a
  have Hcp := GlobalTheory.T.beforeLastStep_datum_transport_badPrime I hok l u a
  have Hlast := GlobalTheory.T.lastStep_datum_transport_badPrime I l hok u a
  have hrowT : ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) ∧
        ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a), GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ :=
    fun M₀ x x₀ hx => ⟨fun P hP => hx P (Finset.mem_union_left _ hP), fun P => hx P.1 (Finset.mem_union_right _ P.2)⟩
  by_cases h2 : i + 2 < B.R.m
  · have hlt : i < B.R.m := by omega
    have hlt' : i + 1 < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hent i h2 (b.get hlt) (b'.get hlt') P p q p' q' k y k' y' hk hN hk' hN' hq hq'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dite_eq_left h2, dite_eq_left h2]
    unfold Formalism.L2.Col.XiEntry
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  by_cases h3 : i + 2 = B.R.m
  · have hlt : i < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hcp i h3 (b.get hlt) P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dite_eq_right h2, dite_eq_right h2, dite_eq_left h3, dite_eq_left h3]
    unfold Formalism.L2.Col.XiCpl1
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  · have h4 : i + 1 = B.R.m := by omega
    have h2m := B.R.two_le_m
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    choose Mf hMf Hf using fun P => Hlast n h4 P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    rw [xiAt_last _ _ _ _ _ h4, xiAt_last _ _ _ _ _ h4]
    unfold xiOver
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)

theorem tw_resid_datum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) g g', g ∈ GfC _ → g' ∈ GfC _ → finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.K i (Nat.le_of_succ_le hi) (A.chOf i c)).y ⟨c, rfl⟩).1.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1.1 → ∃ M : ℕ, 0 < M ∧ ∀ (γ γ₀ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → γ₀.map (fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ g⁻¹ g'⁻¹ (γ.map fun r => A.e * incA (I.rec7 l Z) r) + M • v → A.xi i hi (A.chOf i c) (A.chOf (i + 1) c') γ₀ = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi c c' g g' hg hg' hy hy'
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 (A.chOf i c)
  have hb' := hA.base (i + 1) hi (A.chOf (i + 1) c')
  have hr := hA.rep i hi0 c
  have hr' := hA.rep (i + 1) hi c'
  have hq := (hA.reads i hi0).pt c
  have hq' := (hA.reads (i + 1) hi).pt c'
  obtain ⟨M₀, hM₀, h2⟩ := xiAt_transport_tw I l hok u a i hi (A.b0 i (A.chOf i c)) (A.b0 (i + 1) (A.chOf (i + 1) c'))
    (A.p0 i (A.chOf i c)) ((I.stp u a i).rep c) (A.p0 (i + 1) (A.chOf (i + 1) c')) ((I.stp u a (i + 1)).rep c')
    (A.kb i (A.chOf i c)) (((A.K i hi0 (A.chOf i c)).y ⟨c, rfl⟩).1)
    (A.kb (i + 1) (A.chOf (i + 1) c')) (((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1)
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 (hq.of_extTo hQ hd0) (hq'.of_extTo hQ hd0) hr.2 hr'.2
  refine ⟨d * M₀, Nat.mul_pos hd hM₀, fun γ γ₀ v hv _ hγ => ?_⟩
  have hc := h1 g g' _ _ hy hy' M₀ γ γ₀ v hv hγ
  refine congrArg B.embLL ((h2 _ _ hc).trans ?_)
  rw [← hr.1, ← hr'.1]
  rfl

end GlobalTheory.AdForm.TwResid
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.KComm

variable {D : D7}

theorem comm_of_unitary_isom {m : ℕ} {u J : Matrix (Fin m) (Fin m) ℂ} (hu : uᴴ * u = 1) (hJ : uᴴ * J * u = J) :
    u * J = J * u := by
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.1 hu
  calc u * J = u * (uᴴ * J * u) := by rw [hJ]
    _ = (u * uᴴ) * J * u := by simp only [Matrix.mul_assoc]
    _ = J * u := by rw [hu', Matrix.one_mul]

theorem compAt_K_comm (θ : InfFam D) (hθ : IsInfFam θ) (n : ℕ) (k : G D n) (hk : k ∈ K D n) (τ : D.what₂.Tau) :
    compAt θ τ (mat k) * blk4 0 1 (-1) 0 = blk4 0 1 (-1) 0 * compAt θ τ (mat k) := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = AdelicU.infProj (embOverOf D τ) := AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  have hiso := (AdelicU.archEquiv (Jst D n) (isCMExt_host D) (embOverOf D τ)
    (AdelicU.projArch D.sp.cm.sig (Jst D n) (placeOf D τ) k)).2
  have hiso' : (compAt θ τ (mat k))ᴴ * (Jst D n).map (embOverOf D τ).1 * compAt θ τ (mat k) =
      (Jst D n).map (embOverOf D τ).1 := by
    rw [e1, e2, AdelicU.infMat_infProj (Jst D n) (isCMExt_host D)]
    exact hiso
  rw [Jst, GlobalTheory.CartanPt.blkJ_map] at hiso'
  exact comm_of_unitary_isom hunit hiso'

end GlobalTheory.StdUnn.KComm

namespace GlobalTheory.StdUnn.KComm

theorem exists_stdInv_comm_K : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D A μ hμ κ hκ θ hθ
  obtain ⟨k₀, -, hk₀⟩ := GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv D θ hθ A.rank μ hμ
  have hch : ∀ g τ, (Tm A μ).map (tauE D τ) * compAt θ τ (mat (κ g)) =
      compAt θ τ (Formalism.L2.Theta.mt (dblSp A) g) * (Tm A μ).map (tauE D τ) := by
    intro g τ
    have h2 := congrArg (compAt θ τ) (hκ g)
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, hr] at h2
    exact h2
  refine ⟨fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀)), fun τ => ?_, fun k hk τ => ?_⟩
  · have h := hch (κ.symm k₀) τ
    rw [κ.apply_symm_apply, hk₀] at h
    exact h.symm
  · dsimp only
    set T := (Tm A μ).map (tauE D τ) with hTdef
    have hT : IsUnit T.det := by
      have h := (GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ).2.1.map (tauE D τ)
      rwa [RingHom.map_det] at h
    set X := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)
    set S := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))
    set U := compAt θ τ (mat (κ k))
    have hX : T * U = X * T := hch k τ
    have hS : T * stdInv A.rank μ τ = S * T := by
      have h := hch (κ.symm k₀) τ
      rw [κ.apply_symm_apply, hk₀] at h
      exact h
    have hU : U * stdInv A.rank μ τ = stdInv A.rank μ τ * U := by
      rw [stdInv, Matrix.mul_smul, Matrix.smul_mul, compAt_K_comm θ hθ A.rank (κ k) hk τ]
    have key : X * S * T = S * X * T := by
      calc X * S * T = X * (T * stdInv A.rank μ τ) := by rw [hS, Matrix.mul_assoc]
        _ = T * U * stdInv A.rank μ τ := by rw [hX, Matrix.mul_assoc]
        _ = T * stdInv A.rank μ τ * U := by rw [Matrix.mul_assoc, hU, Matrix.mul_assoc]
        _ = S * X * T := by rw [hS, Matrix.mul_assoc, hX, Matrix.mul_assoc]
    have h2 := congrArg (· * T⁻¹) key
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one] using h2

end GlobalTheory.StdUnn.KComm

end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.StdUnn.CartanMove

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem compAt_mt_one (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) :
    compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this]
  exact Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  rw [mt_mul']
  exact GlobalTheory.AdForm.RatMove.compAt_mul θ τ _ _

theorem compAt_isom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
  GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ

theorem isCartanInv_conj {k : ℕ} {G s P Pi : Matrix (Fin k) (Fin k) ℂ} (hs : IsCartanInv G s)
    (hPi : Pi * P = 1) (hPPi : P * Pi = 1) (hiso : Piᴴ * G * Pi = G) : IsCartanInv G (Pi * s * P) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hP : Pᴴ * G * P = G := by
    calc Pᴴ * G * P = Pᴴ * (Piᴴ * G * Pi) * P := by rw [hiso]
      _ = (Pi * P)ᴴ * G * (Pi * P) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGPi : G * Pi = Pᴴ * G := by
    calc G * Pi = (Pi * P)ᴴ * G * Pi := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = Pᴴ * (Piᴴ * G * Pi) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * G := by rw [hiso]
  refine ⟨?_, ?_, ?_⟩
  · calc Pi * s * P * (Pi * s * P) = Pi * s * (P * Pi) * s * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPPi, Matrix.mul_one, Matrix.mul_assoc Pi s s, h1, Matrix.mul_one, hPi]
  · calc (Pi * s * P)ᴴ * G * (Pi * s * P) = Pᴴ * (sᴴ * (Piᴴ * G * Pi) * s) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hiso, h2, hP]
  · have e : G * (Pi * s * P) = Pᴴ * (G * s) * P := by
      calc G * (Pi * s * P) = G * Pi * s * P := by simp only [Matrix.mul_assoc]
        _ = Pᴴ * (G * s) * P := by rw [hGPi]; simp only [Matrix.mul_assoc]
    rw [e]
    refine h3.conjTranspose_mul_mul_same ?_
    intro v w hvw
    have := congrArg (fun x => Pi.mulVec x) hvw
    simpa [Matrix.mulVec_mulVec, hPi] using this

end GlobalTheory.StdUnn.CartanMove
end

namespace GlobalTheory.StdUnn.CartanMove

open scoped ComplexOrder

theorem cartan_move_std : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  intro D A μ hμ κ hκ a p hp θ hθ sS hsS hcomm
  obtain ⟨k₀, hk₀K, hk₀⟩ := GlobalTheory.T.exists_maximalCompactUnn_component_standardCartanInv D θ hθ A.rank μ hμ
  have hstd : IsStdInv A μ (fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))) := by
    intro τ
    have h := hκ (κ.symm k₀)
    rw [κ.apply_symm_apply k₀] at h
    have h2 := congrArg (compAt θ τ) h
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul] at h2
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [hr, hk₀] at h2
    exact h2.symm
  refine ⟨_, hstd, fun τ => ?_⟩
  dsimp only
  set k₁ := κ.symm k₀ with hk₁
  set P := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))) with hPdef
  set Pi := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))⁻¹) with hPidef
  set S1 := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k₁) with hS1
  have hPi : Pi * P = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, inv_mul_cancel, compAt_mt_one]
  have hPPi : P * Pi = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]
  have hmem : (p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hp]
    have e : (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹) * (p : GA D (dblSp A)) = k₁ := by
      group
    rw [e, hk₁, κ.apply_symm_apply]
    exact hk₀K
  have hc := hcomm _ hmem τ
  rw [compAt_mt_mul, compAt_mt_mul] at hc
  have hcar' : IsCartanInv (gramAt D (dblSp A) τ) (Pi * sS τ * P) :=
    isCartanInv_conj (hsS τ) hPi hPPi (compAt_isom hθ _ _ τ)
  have hcar : IsCartanInv (gramAt D (dblSp A) τ) S1 := GlobalTheory.T.isCartanInv_standardInvolution_doubledGram D A μ hμ _ hstd τ
  have hcm : S1 * (Pi * sS τ * P) = Pi * sS τ * P * S1 := by
    calc S1 * (Pi * sS τ * P) = (Pi * P) * S1 * Pi * sS τ * P := by rw [hPi, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = Pi * (P * S1 * Pi * sS τ) * P := by simp only [Matrix.mul_assoc]
      _ = Pi * (sS τ * (P * S1 * Pi)) * P := by rw [hc]
      _ = Pi * sS τ * P * S1 * (Pi * P) := by simp only [Matrix.mul_assoc]
      _ = Pi * sS τ * P * S1 := by rw [hPi, Matrix.mul_one]
  have heq : S1 = Pi * sS τ * P := GlobalTheory.T.cartanInvolution_eq_of_commute _ _ _ _ hcar hcar' hcm
  rw [heq, Matrix.mul_assoc (Pi * sS τ) P Pi, hPPi, Matrix.mul_one]

end GlobalTheory.StdUnn.CartanMove
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitUpStd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul' (q : GlobalTheory.FinPl.SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]


theorem int_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  intro D k _ _ _ _ q S T a₀ ha₀ _ FS FT hβ _ hγ t ht
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]

  let G : Fin T.rank → Fin S.rank → WO S T := fun i l =>
    Matrix.of fun i' j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)
  have hsingle : ∀ (n : ℕ) (l : Fin n), (Pi.single l (1 : D.host.E) : Fin n → D.host.E) ∈ intVecSub D n := by
    intro n l m
    by_cases hm : m = l
    · subst hm; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hm]; exact isIntegral_zero
  have hG : ∀ i l, G i l ∈ stdHom S T := fun i l =>
    Formalism.IndefR.Fin.gen_mem S T (intVecSub D S.rank) (intVecSub D T.rank) hα ha₀ (hsingle _ l) (hsingle _ i)
  have htm : ∀ (x : k) (y : D.host.E), q.sec x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) = q.sec (x * q.pr (incA D y)) := by
    intro x y
    have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] y = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D y := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have h2 : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
    rw [e1, ← mul_assoc, ← h2, mul_assoc q.e, mul_comm (q.sec x), ← mul_assoc q.e, hee, h2, sec_mul']
  have hrow : ∀ (l : Fin S.rank) j,
      ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j = S.gram l j := by
    intro l j
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, star_one, one_mul]
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hGapp : ∀ i l i' j, (q.sec (t i l) • G i l) i' j = q.sec (t i l) * (pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)) := fun _ _ _ _ => rfl
  have key : (Place.ofSplitPt q).up FS FT t = ∑ i, ∑ l, q.sec (t i l) • G i l := by
    ext i' j
    change q.sec ((FT.β * t * FS.γ) i' j) = _
    rw [hβ, hγ, Matrix.one_mul, Matrix.sum_apply, Finset.sum_eq_single i']

    · rw [Matrix.sum_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hGapp, htm, hrow, Pi.single_eq_same, mul_one, map_mul (incA D), map_mul q.pr, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    · intro i _ hi
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hGapp, Pi.single_eq_of_ne (Ne.symm hi), mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i') h
  rw [key]
  refine sum_mem fun i _ => sum_mem fun l _ => ?_
  exact Formalism.IndefR.Fin.latO_smul_mem S T (intVecSub D S.rank) (intVecSub D T.rank) ((q.int_iff _).1 (ht i l)) (hG i l)

end GlobalTheory.SplitUpStd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.stdHomLattice_point_integral_matrix_at_split_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (c : k), c ≠ 0 → (∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / c ∈ 𝒪[k]) → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = c • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k] := by
  first | exact @GlobalTheory.LocMod.StdHomDown.down_mem_integer | exact GlobalTheory.LocMod.StdHomDown.down_mem_integer | (intros; apply GlobalTheory.LocMod.StdHomDown.down_mem_integer <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.localFlatMap_dualColumn_multiplicationLaws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ GlobalTheory.RootEx.Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  first | exact @GlobalTheory.FlatColLaw.law_dual_col | exact GlobalTheory.FlatColLaw.law_dual_col | (intros; apply GlobalTheory.FlatColLaw.law_dual_col <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.localFlatMap_freeEntry_translationLaws_besselToJacobi : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), GlobalTheory.RootEx.Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → flatBF st (Tm Φ') = (ψk (GlobalTheory.RootEx.ch (Matrix.single r q a)) : ℂ) • flatBF st (Tm Φ) := by
  first | exact @GlobalTheory.FlatTransLaw.flatBF_trans | exact GlobalTheory.FlatTransLaw.flatBF_trans | (intros; apply GlobalTheory.FlatTransLaw.flatBF_trans <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

theorem _root_.GlobalTheory.T.localFlatMap_translationLaws_jacobiToBessel_free : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (σ + 1) (r, q) → (∀ i, q = Sum.inr i → σ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → flatFB st (Tm Φ') = (ψk (ch (Matrix.single r q a)) : ℂ) • flatFB st (Tm Φ) := by
  first | exact @GlobalTheory.LocMod.flatFB_trans_free | exact GlobalTheory.LocMod.flatFB_trans_free | (intros; apply GlobalTheory.LocMod.flatFB_trans_free <;> assumption)
end
