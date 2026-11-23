module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle098
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle465
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle472
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle471
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385

@[expose] public section

section

open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.Core.Rk.HgtFin

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_le_one_of_absFin_le_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E), absFin F v x ≤ 1 → ‖Algebra.norm (Fv F v) x‖₊ ≤ 1 := by
  intro F E _ _ _ _ _ σ hσ v x hx
  have hN := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x
  have e1 : absFin F v (algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) x)) =
      ‖Algebra.norm (Fv F v) x‖₊ := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact absFin_tmul_one F v _
  have hs : absFin F v (sigR (Fv F v) σ x) ≤ absFin F v x := by
    refine (absFin_le_iff F v).2 fun τ => ?_
    have e2 : ∀ w, finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v ((τ : E →ₐ[F] FvBar F v).comp σ) w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    rw [e2]
    exact le_absFin F v _ x
  rw [← e1, hN]
  calc _ ≤ absFin F v x * absFin F v (sigR (Fv F v) σ x) := absFin_mul_le F v _ _
    _ ≤ 1 * 1 := mul_le_mul' hx (hs.trans hx)
    _ = 1 := one_mul 1

theorem absFin_tmul_one_mul (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (y : Fv F v ⊗[F] E) :
    absFin F v (c ⊗ₜ[F] (1 : E) * y) = ‖c‖₊ * absFin F v y := by
  simp only [absFin, map_mul, finEmb_tmul, map_one, mul_one, absBar_mul, absBar_algebraMap]
  rw [NNReal.mul_finset_sup]

theorem absFin_le_one_of_pow_le {v : HeightOneSpectrum (𝓞 F)} {x : Fv F v ⊗[F] E} {C : ℝ≥0}
    (h : ∀ k : ℕ, absFin F v (x ^ k) ≤ C) : absFin F v x ≤ 1 := by
  refine (absFin_le_iff F v).2 fun τ => ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
  have := (le_absFin F v τ (x ^ k)).trans (h k)
  have hpw : ∀ (z : FvBar F v) (m : ℕ), absBar F v (z ^ m) = absBar F v z ^ m := by
    intro z m
    induction m with
    | zero => simpa using absBar_algebraMap F v 1
    | succ m ih => rw [pow_succ, absBar_mul, ih, pow_succ]
  rw [map_pow, hpw] at this
  exact absurd this (not_le.2 hk)

theorem absFin_det_le (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    absFin F v M.det ≤ normFin F v M ^ n := by
  rw [Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun s _ => ?_
  have hp : absFin F v (∏ i, M (s i) i) ≤ normFin F v M ^ n :=
    calc absFin F v (∏ i, M (s i) i) ≤ ∏ i, absFin F v (M (s i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, normFin F v M := Finset.prod_le_prod' fun i _ => absFin_le_normFin F v M _ _
      _ = normFin F v M ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hp

theorem normDet_le_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hM : ∀ x ∈ latLoc F L v, M *ᵥ x ∈ latLoc F L v) : ‖Algebra.norm (Fv F v) M.det‖₊ ≤ 1 := by
  obtain ⟨c, hc, hcL⟩ := GlobalTheory.T.exists_single_mem_localLatticeCompletion L v
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_bound_abs_localLatticeCompletion_entries L v
  have hpow : ∀ k : ℕ, ∀ x ∈ latLoc F L v, (M ^ k) *ᵥ x ∈ latLoc F L v := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (hM _ hx)
  have hent : ∀ k i j, absFin F v ((M ^ k) i j) ≤ C / ‖c‖₊ := by
    intro k i j
    have h1 := hC _ (hpow k _ (hcL j)) i
    rw [Matrix.mulVec_single] at h1
    change absFin F v ((M ^ k) i j * c ⊗ₜ[F] (1 : E)) ≤ C at h1
    rw [mul_comm, absFin_tmul_one_mul] at h1
    rw [le_div_iff₀ (nnnorm_pos.2 hc), mul_comm]
    exact h1
  have hdet : ∀ k : ℕ, absFin F v (M.det ^ k) ≤ (C / ‖c‖₊) ^ n := fun k => by
    rw [← Matrix.det_pow]
    exact (absFin_det_le v _).trans (pow_le_pow_left' ((normFin_le_iff F v).2 (hent k)) n)
  exact absNorm_le_one_of_absFin_le_one hσ v _ (absFin_le_one_of_pow_le hdet)

theorem levi_mulVec_mem (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GLoc σ J v) (p : siegelH (Fv F v) σ Q) {k : GLoc σ Q v} (hk : k ∈ KFin σ Q L v)
    (e : ioH _ σ hQ (y, 1) = p * k) {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc F L v) :
    leviMat finSumFinEquiv (matHom _ σ Q p).1 *ᵥ x ∈ latLoc F L v := by
  have hp : KeepsDiag finSumFinEquiv (matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := matHom (Fv F v) σ Q)).1 p.2
  have hk' := inv_mem hk
  have ek : k⁻¹ = ioH _ σ hQ (y⁻¹, 1) * p := by
    have : k = (p : GLoc σ Q v)⁻¹ * ioH _ σ hQ (y, 1) := by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this, mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk, inv_one]
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hk' _).1 h1
  have e3 : (matHom _ σ Q (ioH _ σ hQ (y⁻¹, 1))).1 =
      blkMat finSumFinEquiv (matHom _ σ J y⁻¹).1 (matHom _ σ J 1).1 := rfl
  rw [ek, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hp.mulVec_diag, e3, blkMat_mulVec, latLoc_sumLat,
    pairVec_mem_sumLat] at h2
  simpa using h2.2

theorem hgtFin_ioH_le_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)) (y : GLoc σ J v) :
    hgtFin σ Q L v (ioH _ σ hQ (y, 1)) ≤ 1 := by
  by_cases h : ∃ p : siegelH (Fv F v) σ Q, ∃ k ∈ KFin σ Q L v, ioH _ σ hQ (y, 1) = p * k
  · obtain ⟨p, k, hk, e⟩ := h
    rw [e, hgtFin_mul p hk, absEv_apply]
    exact normDet_le_one hσ L v _ fun x hx => levi_mulVec_mem σ hQ L v y p hk e hx
  · show iwAbs _ _ _ ≤ 1
    rw [iwAbs, dite_eq_right h]

end GlobalTheory.Core.Rk.HgtFin

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Rk.IP

theorem hgtFin_ioAt_le_one : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (y : Gv A v), hgtFin D.sp.cm.sig (dblSp A).gram L v (ioAt A v y) ≤ 1 := by
  intro D A L hL v y
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  exact GlobalTheory.Core.Rk.HgtFin.hgtFin_ioH_le_one (isCMExt_host D) (gram_hdbl A) L v y

end GlobalTheory.Core.Rk.IP
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

noncomputable section

namespace GlobalTheory.TwSuppLev

theorem isSBHalf_twDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  classical
  intro D S T ΛS ΛT βS βT L χ ξ Q Z e hS hT _ _ he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ (L.Pg ∪ Q)
    (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
        GlobalTheory.PlaceDatum.omegaQ_congr Q L.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)]

theorem eq_of_under_eq {D : D7} {e : AE D} {Z : Finset (Pl D.host.E)} (h : IsIdemSum e Z) {PP PP' : Pl D.host.E}
    (hP : PP ∈ Z) (hP' : PP' ∈ Z) (hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) : PP' = PP := by
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h1 | h1
  · exact h1
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1) (GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hP PP' hP')

theorem gAt_mem_levG_of_supp : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → (∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG S βS L := by
  intro D S T ΛS βS βT L χ ξ e hsd hfr hrk he hP g x hx hx' PP hPP huniq hQu
  obtain ⟨hSt, hB, hR⟩ := GlobalTheory.T.principalPlace_component_stabilises_lattice_twisted D S T ΛS βS βT L χ ξ e hsd hfr hrk he hP g x hx hx' PP hPP huniq
  exact GlobalTheory.T.principalPlace_component_mem_level_of_reduction D S βS L hP g PP hPP (fun PP' hP' hu => huniq PP' (Finset.mem_union_left _ hP') hu) hQu hSt hB hR

theorem supp_at_principal : ∀ D : D7, ForStepQ D fun c w _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ P (g : GA D s.V), coefW p.ω m X (p.pt P) g ≠ 0 → ∀ v ∈ w.S₀, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L := by
  intro D _hgap c w hw k _hk s s' hs hs' p hp m X hX φ g hne v hv
  obtain ⟨hr, hL, hfl⟩ := hs
  obtain ⟨hr', hL', hfl'⟩ := hs'
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hsd' : IsSelfDualC s'.V s'.Λ := hfl'.selfDual
  have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
  have hfr' : Formalism.L2.DIV.IsFrame s'.β s'.Λ := hfl'.frame
  have hrank : s.V.rank ≤ s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hfl.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [h1, h2]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hthf : IsThetaFunO c.ψ s.V s'.V p.f := GlobalTheory.VecTheta.isThetaFunO_stepVec hvec
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  have hQ : s.L.Q = w.Q := by rw [hL]; rfl
  have hPg : s.L.Pg = w.Pg := by rw [hL]; rfl
  have hPH : s.L.P.H = ⊥ := by rw [hL]; rfl
  simp only [Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
  obtain ⟨PP, hPP, rfl⟩ := hv
  by_contra hnot
  have hsupp := fun x hx => by_contra fun h => hnot
    (gAt_mem_levG_of_supp D s.V s'.V s.Λ s.β s'.β s.L (w.chi (k + 1)) w.ξ e hsd hfr hrank (hQ ▸ he) hPH g x
      (by rw [hQ]; exact hx) (by rw [hQ]; exact h) PP (hPg ▸ hPP)
      (fun PP' hP' hu => eq_of_under_eq he (Finset.mem_union_left _ (hPg ▸ hPP)) (hQ ▸ hP') hu)
      fun PP' hP' hu => Finset.disjoint_left.1 hw.disj hPP (by
        have hP'' : PP' ∈ w.Q := hQ ▸ hP'
        have := eq_of_under_eq he (Finset.mem_union_left _ (hPg ▸ hPP)) (Finset.mem_union_right _ hP'') hu
        subst this
        exact hP''))
  have hsb := isSBHalf_twDatum D s.V s'.V s.Λ s'.Λ s.β s'.β s.L (w.chi (k + 1)) w.ξ w.Q (s.L.Pg ∪ w.Q) e hsd hsd' hfr hfr' he
  obtain ⟨n, a, y, hy, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D c.ψ s.V s'.V hw.com.std s.Λ s'.Λ hsd hsd'
    (s.L.Pg ∪ w.Q) e he f₀ _ p.f hsb hth g hsupp
  obtain ⟨H1, -⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hw.com.std hw.com.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n a y (fun i => (hy i).1) φ
  obtain ⟨H2, H0⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hw.com.std hw.com.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n (fun i => conj (a i)) (fun i => actO s.V s'.V g⁻¹ 1 (-(y i))) (fun i => (hy i).2) φ
  have R1 : ∑ i, a i • heisO c.ψ s.V s'.V (y i) (p.pt φ) = p.pt φ := by
    show ∑ i, a i • heisO c.ψ s.V s'.V (y i) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H1, h1]
    rfl
  have R2 : ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i))) (p.pt φ) = 0 := by
    show ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i)))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H2, h2, H0]
  exact hne (GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil m X hX (p.pt φ) (hp.theta φ) g n a y R1 R2)

end GlobalTheory.TwSuppLev

end
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
open scoped NNReal
namespace GlobalTheory.ChartHgt


open GlobalTheory.Doubling in
theorem hgtV_mul_stab (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    {k k' : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v)
    (hk' : k' ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v (k * g * k') = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v g := by
  haveI : Submodule.IsFullLattice D.host.E Λ := GlobalTheory.ProjXCols.selfDual_isFullLattice V Λ hΛ
  have hI := GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom (GlobalTheory.AdelicU.isCMExt_host D) (gram_hdbl V) (isHermND_gram V)
    (isHermND_gram (dblSp V)) τ Λ (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
  congr 1
  have e1 : ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k * g * k', 1) =
      (ioDiag (R := Fv D.host.F v) (gram_hdbl V) k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig (dblSp V).gram v) *
        ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (g, 1) * ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k', k⁻¹) := by
    rw [coe_ioDiag, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp [mul_assoc]
  rw [e1]
  refine (HasIwasawa.hgtH_right (continuous_absEv v) (isCompact_KFin v) hI _
    ((ioH_mem_KFin (gram_hdbl V)).2 ⟨hk', inv_mem hk⟩)).trans ?_
  refine (HasIwasawa.hgtH_left (continuous_absEv v) (isCompact_KFin v) hI _ _).trans ?_
  rw [aH_ioDiag, abs_detH (absEv_conjUnit _ v) (isHermND_gram V).2, one_mul]


open ValuativeRel in
theorem nnnorm_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : (Fv F v)ˣ)
    (h : letI := GlobalTheory.LocalData.complRel v; valuation (Fv F v) (ϖ : Fv F v) = uniformizer (Fv F v)) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    ‖(ϖ : Fv F v)‖₊ = ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℕ) : ℝ≥0)⁻¹ := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
  apply GlobalTheory.norm_uniformiser_eq_inv_absNorm
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have h1 : Valued.v (ϖ : Fv F v) < 1 := by
    rw [← he.lt_one_iff_lt_one, h]; exact uniformizer_lt_one
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have h2 : Valued.v p ≤ Valued.v (ϖ : Fv F v) := by
    rw [← he.le_iff_le, h, le_uniformizer_iff, he.lt_one_iff_lt_one, hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have h0 : Valued.v (ϖ : Fv F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [hp, ← WithZero.exp_log h0, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold Formalism.UG.IsUnifV
  rw [← WithZero.exp_log h0]
  have : WithZero.log (Valued.v (ϖ : Fv F v)) = -1 := by omega
  rw [this]; rfl

theorem hgtFin_ioH_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (hQ : Q = GlobalTheory.Doubling.dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (g : GlobalTheory.AdelicU.GLoc σ J v) :
    GlobalTheory.Doubling.hgtFin σ Q L v (GlobalTheory.Doubling.ioH (Fv F v) σ hQ (g, 1)) =
      GlobalTheory.Doubling.hgtFin σ (GlobalTheory.Doubling.dblGram finSumFinEquiv J) L v (GlobalTheory.Doubling.ioH (Fv F v) σ rfl (g, 1)) := by
  subst hQ; rfl

theorem min_zpow_inv (q : ℝ≥0) (hq : 1 ≤ q) (m : ℤ) : min ((q⁻¹) ^ m) (((q⁻¹) ^ m)⁻¹) = q ^ (-|m|) := by
  rw [_root_.inv_zpow', ← _root_.zpow_neg, neg_neg]
  rcases le_total 0 m with hm | hm
  · rw [abs_of_nonneg hm, min_eq_left (zpow_le_zpow_right₀ hq (by omega))]
  · rw [abs_of_nonpos hm, neg_neg, min_eq_right (zpow_le_zpow_right₀ hq (by omega))]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (q : ℝ≥0) (hq : q ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem bridge : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ →
    Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v,
    (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) →
    ∃ (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (β : GL (Fin s.V.rank) (Fv D.host.F v))
      (ε : Fin D.R.r ⊕ Blocks k D.R.t ≃ Fin s.V.rank), GlobalTheory.AdelicU.IsSplitBasis τ s.Λ β ∧
      ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1.submatrix ε ε = y.1 := by
  intro D s k v φ ι _ hfr ⟨ε, _, hε⟩ e he
  refine ⟨_, _, ε, GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ, fun y => ?_⟩
  have h2 := (hε y).2
  rw [he y, GlobalTheory.ChartStab.grpCo_emb] at h2
  exact h2

theorem isHgt_chart : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y) := by
  intro D s k v φ ι hΛ hβ hι e he x ϖ hϖ
  obtain ⟨τ, β, ε, hB, hy⟩ := bridge D s k v φ ι hΛ hβ hι e he
  have hΨ : ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1 =
      y.1.submatrix ε.symm ε.symm := fun y => by
    rw [← hy y, Matrix.submatrix_submatrix]; simp
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β).injective
      (Units.ext (by rw [map_mul, Units.val_mul, hΨ, hΨ, hΨ, Units.val_mul, Matrix.submatrix_mul_equiv]))
  have hK := GlobalTheory.ChartStab.chart_stab D s k v φ ι hΛ hβ hι e he
  refine ⟨fun κ hκ g => ⟨?_, ?_⟩, fun e' => ?_⟩
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ ((hK κ).2 hκ) (one_mem _) (e g)
    rwa [mul_one, ← hmul] at this
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ (one_mem _) ((hK κ).2 hκ) (e g)
    rwa [one_mul, ← hmul] at this
  · haveI : Submodule.IsFullLattice D.host.E s.Λ := GlobalTheory.ProjXCols.selfDual_isFullLattice s.V s.Λ hΛ
    have hsd := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
    obtain ⟨-, hval, -⟩ := (GlobalTheory.GraphNorm.graphNormFinite D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D)
      s.V.rank s.V.gram (GlobalTheory.Doubling.isHermND_gram s.V) s.Λ v hsd).1 τ β hB
      (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e'))
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.IsElemDiv (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D)
        (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')))
        (fun i => ϖ ^ e' (ε.symm i)) := by
      refine ⟨1, one_mem _, 1, one_mem _, ?_⟩
      rw [hΨ, GlobalTheory.GLDoubling.val_torusElt, Matrix.submatrix_diagonal_equiv]
      simp
    have h1 := hval _ hd
    obtain ⟨-, -, -, -, hv⟩ := hϖ
    have hn := nnnorm_unif _ v ϖ hv
    have hq : 1 ≤ ((GlobalTheory.SplitWeil.resCard (Fv D.host.F v) : ℕ) : ℝ≥0) := by
      rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (fun h0 => v.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0))
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) =
        (GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt D.sp.cm.sig s.V.gram s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt
      exact congrArg _ (hgtFin_ioH_eq _ _ _ _ _ _ _)
    refine e2.trans ?_
    rw [h1]
    simp only [Units.val_zpow_eq_zpow_val, nnnorm_zpow, hn]
    simp only [min_zpow_inv _ hq]
    rw [prod_zpow_eq _ _ (zero_lt_one.trans_le hq).ne', NNReal.coe_zpow, NNReal.coe_natCast, Finset.sum_neg_distrib]
    congr 2
    exact Equiv.sum_comp ε.symm (fun a => |e' a|)

end GlobalTheory.ChartHgt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weilOperator_lastDefiniteLocal_biModel_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  first | exact @GlobalTheory.LastOmb.weil_last_local | exact GlobalTheory.LastOmb.weil_last_local | (intros; apply GlobalTheory.LastOmb.weil_last_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.LastStep

theorem chars_unram : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  intro D c v k _ _ _ _ ι o hS j h t hU hK χz χS' χT h1 h2 x hx
  obtain ⟨i, rfl⟩ := (hS.pre.tP x).1 hx
  have hpos : ∀ n, 0 < (c.X n).rank := fun n => by
    apply Nat.pos_of_ne_zero
    intro h0
    have P := o.Q n i
    revert P
    rw [h0]
    intro P
    exact P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have hV : 0 < (c.V (j + 1)).rank := by
    have := (c.jac j 0 h).d.rank_add
    have := hpos (j + 1)
    omega
  obtain ⟨χS₃, χT₃, hW₃, hu₃⟩ := hK (j + 1) (by omega)
  obtain ⟨χS₂, χT₂, hW₂, hu₂⟩ := hU.top j h
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₃ χT₃ χS' (χT * χz⁻¹) (t.kom (j + 1)) hW₃ h1).2 (hpos _) (hu₃ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).1
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₂ χT₂ χS' χT (t.omT j h) hW₂ h2).1 hV (hu₂ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).2

end GlobalTheory.LastStep
end
