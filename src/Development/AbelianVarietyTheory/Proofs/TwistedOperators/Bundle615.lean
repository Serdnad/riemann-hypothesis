module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle610
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IndVac

variable {D : D7} {S T : HSp D}

theorem mem_of_indL_ne {L : AddSubgroup (WO S T)} {t : WO S T} (h : GlobalTheory.LiftLevel.indL L t ≠ 0) : t ∈ L := by
  by_contra hn
  exact h (by simp only [GlobalTheory.LiftLevel.indL, hn, if_false])

theorem isSBHalf_indL (a : AE D) (Λ L : AddSubgroup (WO S T)) (hL : ∀ x ∈ L, IsHalf a x)
    (h1 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ Λ) (h2 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ Λ, IsHalf a x → m • x ∈ L) :
    IsSBHalf a Λ (GlobalTheory.LiftLevel.indL L) := by
  obtain ⟨m, hm, hm1⟩ := h1
  obtain ⟨n, hn, hn2⟩ := h2
  refine ⟨fun t ht => hL t (mem_of_indL_ne ht), m * n, Nat.mul_pos hm hn, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have hk : (m * n) • u ∈ L := by
      rw [← smul_smul]
      exact L.nsmul_mem (hn2 u hu hu') m
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hk]
  · rw [mul_comm, ← smul_smul]
    exact Λ.nsmul_mem (hm1 t (mem_of_indL_ne ht)) n

theorem partAt_eq (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := rfl

theorem symplO_half_eq_zero {a b : AE D} (hab : cA D b * a = 0) {r x : WO S T}
    (hr : r ∈ GlobalTheory.PlaceModel.half S T b) (hx : x ∈ GlobalTheory.PlaceModel.half S T a) : symplO S T r x = 0 := by
  rw [← (GlobalTheory.PlaceModel.mem_half S T).1 hr, ← (GlobalTheory.PlaceModel.mem_half S T).1 hx, GlobalTheory.PlaceModel.symplO_smul,
    smul_smul, hab, zero_smul, GlobalTheory.PlaceModel.symplO_zero_right]

theorem heisO_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    (r : WO S T) (hr0 : heisO ψ S T r f₀ = f₀) (hx : ∀ x, IsHalf a x → symplO S T r x = 0)
    (hy : ∀ y, IsHalf (cA D a) y → symplO S T r y = 0)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) : heisO ψ S T r (Tm Φ) = Tm Φ := by
  have hc : ∀ w, symplO S T r w = 0 → ∀ g, heisO ψ S T r (heisO ψ S T w g) = heisO ψ S T w (heisO ψ S T r g) :=
    fun w hw g => by
      have := GlobalTheory.PlaceModel.heisL_comm S T ψ r w g
      rw [hw, AddChar.map_zero_eq_one, one_smul] at this
      exact this
  have h' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀
      ((GlobalTheory.PlaceModel.heisL S T ψ r).comp Tm) :=
    { trans := fun Φ hΦ x hxa => by
        change heisO ψ S T r (Tm _) = heisO ψ S T x (heisO ψ S T r (Tm Φ))
        rw [hTm.trans Φ hΦ x hxa, hc x (hx x hxa)]
      modul := fun Φ hΦ y hya => by
        change heisO ψ S T r (Tm _) = heisO ψ S T y (heisO ψ S T r (Tm Φ))
        rw [hTm.modul Φ hΦ y hya, hc y (hy y hya)]
      vac := by
        change heisO ψ S T r (Tm _) = f₀
        rw [hTm.vac, hr0] }
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf h' hTm hΦ

theorem heisenbergTranslate_add_three_fixes_of_trivial_phase (ψ : AddChar (AF D.host.F) ℂ) {f : WO S T → ℂ} {x y z : WO S T}
    (hx : heisO ψ S T x f = f) (hy : heisO ψ S T y f = f) (hz : heisO ψ S T z f = f)
    (p1 : ψ (symplOH S T y z) = 1) (p2 : ψ (symplOH S T x (y + z)) = 1) : heisO ψ S T (x + (y + z)) f = f := by
  have e1 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y z f
  have e2 := GlobalTheory.PlaceModel.heisL_heisL S T ψ x (y + z) f
  change heisO ψ S T y (heisO ψ S T z f) = _ • heisO ψ S T (y + z) f at e1
  change heisO ψ S T x (heisO ψ S T (y + z) f) = _ • heisO ψ S T (x + (y + z)) f at e2
  rw [hz, hy, p1, one_smul] at e1
  rw [← e1, hx, p2, one_smul] at e2
  exact e2.symm




theorem indL_theta_fock_latVac : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ f₀ : WO S T → ℂ, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel C.ψ (symplO S T) (heisO C.ψ S T) (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ L : AddSubgroup (WO S T), (∀ x ∈ L, IsHalf (cA D e) x) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) → IsSBHalf (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (GlobalTheory.LiftLevel.indL L) ∧ C.IsTh (Tm (GlobalTheory.LiftLevel.indL L)) ∧ C.IsFock B (Tm (GlobalTheory.LiftLevel.indL L)) ∧ ∀ Λ'' : AddSubgroup (WO S T), (∀ u ∈ Λ'', GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → IsLatVac (heisO C.ψ S T) Λ'' (Tm (GlobalTheory.LiftLevel.indL L)) := by
  intro D S T C B hB ΛT hT P e he f₀ hvac Tm hTm L hL hm1 hm2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hea : e * cA D e = 0 := he.2
  have ha : cA D e * cA D e = cA D e := ho.conj.idem
  have hcc : cA D (cA D e) = e := cA_cA e
  have hS := GlobalTheory.Ker.Base.selfDualC_stdL C.m.gS
  have hψ := C.std
  have hinf : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  have hinf' : infPart D (cA D (cA D e)) = 0 := ho.conj.conj.infPart_eq
  have hSB := isSBHalf_indL (cA D e) _ L hL hm1 hm2
  have hth : IsThetaAt C.ψ (symplO S T) (heisO C.ψ S T) (cA D e)
      (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      1 f₀ (GlobalTheory.LiftLevel.indL L) (Tm (GlobalTheory.LiftLevel.indL L)) :=
    ⟨⟨Tm, hTm⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf hTm hT' hSB⟩
  have hθf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ C.inf hth hvac.2.theta
  refine ⟨hSB, hθf, fun τ => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 C.inf hinf hinf' hth hvac.2.theta hθf
    (hvac.2.fock τ), ?_⟩
  obtain ⟨b, hbd⟩ : ∃ b : AE D, b = 1 - e - cA D e := ⟨_, rfl⟩
  have hb : b * b = b := by rw [hbd]; linear_combination hee + ha + 2 * hea
  have hcb : cA D b = b := by rw [hbd, map_sub, map_sub, map_one, hcc]; ring
  have hba : cA D b * cA D e = 0 := by rw [hcb, hbd]; linear_combination -hea - ha
  have hbe : cA D b * e = 0 := by rw [hcb, hbd]; linear_combination -hee - hea
  have hfix_a : ∀ x ∈ L, heisO C.ψ S T x (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun x hx => by
    rw [← hTm.trans _ hSB x (hL x hx)]
    congr 1
    funext t
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hx]
  have hfix_e : ∀ y, IsHalf e y → (∀ t ∈ L, C.ψ (symplO S T t y) = 1) →
      heisO C.ψ S T y (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun y hy ht => by
    rw [← hTm.modul _ hSB y (by rw [hcc]; exact hy)]
    congr 1
    funext t
    by_cases h : t ∈ L
    · simp only [GlobalTheory.LiftLevel.indL, h, if_true, ht t h, one_mul]
    · simp only [GlobalTheory.LiftLevel.indL, h, if_false, mul_zero]
  have hfix_r : ∀ r ∈ GlobalTheory.PlaceModel.half S T b, heisO C.ψ S T r f₀ = f₀ →
      heisO C.ψ S T r (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun r hr hr0 =>
    heisO_fix hψ hS hT ha hinf hTm r hr0
      (fun x hx => symplO_half_eq_zero hba hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx))
      (fun y hy => symplO_half_eq_zero (by rw [hcc]; exact hbe) hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy)) hSB
  have hdec : ∀ u : WO S T, u = cA D e • u + (e • u + b • u) := fun u => by
    rw [← add_smul, ← add_smul, show cA D e + (e + b) = 1 by rw [hbd]; ring, one_smul]
  have hbmem : ∀ u : WO S T, b • u ∈ GlobalTheory.PlaceModel.half S T b := fun u => by
    show b • b • u = b • u
    rw [smul_smul, hb]
  have hemem : ∀ u : WO S T, e • u ∈ GlobalTheory.PlaceModel.half S T e := fun u => by
    show e • e • u = e • u
    rw [smul_smul, hee]
  have hamem : ∀ u : WO S T, cA D e • u ∈ GlobalTheory.PlaceModel.half S T (cA D e) := fun u => by
    show cA D e • cA D e • u = cA D e • u
    rw [smul_smul, ha]
  have hez : ∀ u : WO S T, symplO S T (e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hbe (hbmem u) (hemem u), neg_zero]
  have haz : ∀ u : WO S T, symplO S T (cA D e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hba (hbmem u) (hamem u), neg_zero]
  intro Λ'' hΛ''
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have e2u : 2 • u = 2 • (cA D e • u) + (2 • (e • u) + 2 • (b • u)) := by
      conv_lhs => rw [hdec u]
      rw [smul_add, smul_add]
    rw [e2u]
    have h2' : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ (L.nsmul_mem h1 2))
      (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 ((GlobalTheory.PlaceModel.half S T e).nsmul_mem (hemem u) 2))
        fun t ht => by rw [two_nsmul, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul, h2 t ht, one_mul])
      (hfix_r _ ((GlobalTheory.PlaceModel.half S T _).nsmul_mem (hbmem u) 2) (hvac.2.lat.1 _ h3)) ?_ ?_
    · simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, hez, add_zero,
        mul_zero, AddChar.map_zero_eq_one]
    · have hs : symplOH S T (2 • (cA D e • u)) (2 • (e • u) + 2 • (b • u)) =
          symplO S T (cA D e • u) (e • u) + symplO S T (cA D e • u) (e • u) := by
        simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, haz, add_zero]
        linear_combination (2 * symplO S T (cA D e • u) (e • u)) * h2'
      rw [hs, AddChar.map_add_eq_mul, h2 _ h1, one_mul]
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have hu' : u ∈ GlobalTheory.PlaceModel.half S T e' := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hh
    have hin : ∀ c : AE D, c • u ∈ GlobalTheory.PlaceModel.half S T e' := fun c => by
      rw [GlobalTheory.PlaceModel.mem_half, smul_comm, (GlobalTheory.PlaceModel.mem_half S T).1 hu']
    have hae : symplO S T (cA D e • u) (e • u) = 0 :=
      symplO_half_eq_zero (by rw [mul_comm]; exact he'.2.1) (hin _) (hin _)
    rw [hdec u]
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ h1) (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hemem u)) h2)
      (hfix_r _ (hbmem u) (hvac.2.lat.2 e' he' _ h3 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hin _)))) ?_ ?_
    · rw [symplOH, hez, mul_zero, AddChar.map_zero_eq_one]
    · rw [symplOH, GlobalTheory.PlaceModel.symplO_add_right, hae, haz, add_zero, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.IndVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

section SlopeTestRemainingChoices

open GlobalTheory.LatVac GlobalTheory.SplitScalar

def stO (x : 𝓞 D.host.E) : 𝓞 D.host.E :=
  ⟨star (x : D.host.E), (show IsIntegral ℤ (x : D.host.E) from x.2).map (starRingEnd D.host.E).toIntAlgHom⟩

theorem coe_stO (x : 𝓞 D.host.E) : ((stO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := rfl

theorem mem_of_mem_conjI {P : Ideal (𝓞 D.host.E)} {x : 𝓞 D.host.E} (hx : x ∈ conjI P) : stO x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, hab⟩ := ha
    have : stO a = b := by
      apply RingOfIntegers.ext
      rw [coe_stO, show (a : D.host.E) = star (b : D.host.E) from hab, star_star]
    rw [this]; exact hb
  | zero =>
    have : stO (0 : 𝓞 D.host.E) = 0 := RingOfIntegers.ext (by rw [coe_stO]; simp)
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : stO (a + b) = stO a + stO b := RingOfIntegers.ext (by
      show star ((a : D.host.E) + b) = star (a : D.host.E) + star (b : D.host.E)
      exact star_add _ _)
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : stO (r • a) = stO r * stO a := RingOfIntegers.ext (by
      show star ((r : D.host.E) * a) = star (r : D.host.E) * star (a : D.host.E)
      exact star_mul' _ _)
    rw [this]; exact Ideal.mul_mem_left _ _ ha

theorem smul_mem_tens {n r : ℕ} {Λ : Lt D.host.E n} {L L' : Lt D.host.E r} (c : 𝓞 D.host.E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) D.host.E} (hy : y ∈ tens Λ L) :
    (c : D.host.E) • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_hatA_of_int {S T : HSp D} {A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)}
    (hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ A, (o : D.host.E) • y ∈ A) {z : AE D} (hz : finPart D z ∈ intAE D)
    {u : WO S T} (hu : u ∈ hatA S T A) : z • u ∈ hatA S T A := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => z • u ∈ hatA S T A) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    have key : ∀ x ∈ intAE D,
        (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D (x * (α ⊗ₜ[D.host.F] (yᵀ i j)))) ∈ hatA S T A := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, o, rfl⟩ := hx
        have e1 : (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D
            ((a ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] (yᵀ i j)))) =
            GlobalTheory.LatVac.finTens (a * α) (((o : D.host.E) • y)ᵀ) := by
          ext i j
          rw [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.TensLatMove.emb_tmul]
          rfl
        rw [e1]
        exact GlobalTheory.Ker.SignVac.finTens_mem (mul_mem_intAf ha hα) (hA o y hy)
      | zero =>
        convert zero_mem (hatA S T A) using 1
        ext i j
        rw [Matrix.of_apply, zero_mul, LinearMap.map_zero, Matrix.zero_apply]
      | add x x' _ _ hx hx' =>
        convert add_mem hx hx' using 1
        ext i j
        rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, add_mul, LinearMap.map_add (f := _)]
      | neg x _ hx =>
        convert neg_mem hx using 1
        ext i j
        rw [Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, neg_mul, LinearMap.map_neg]
    convert key _ hz using 1
    ext i j
    rw [Matrix.of_apply, GlobalTheory.TensLatMove.emb_mul, GlobalTheory.TensLatMove.emb_tmul]
    rfl
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

end SlopeTestRemainingChoices

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (x : WO S T) : partAt c x = c • x := by
  ext i j; rfl

theorem partAt_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ hPg _ e he a k₀ Λ' _ hMv hGen hMov Lv hLv u hu

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hMov
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩
  have hu' : actO S T k₀ 1 (actO S T k₀⁻¹ 1 u) = u := by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k₀ 1 u
    rwa [inv_one] at this
  generalize actO S T k₀⁻¹ 1 u = w at hw hu'

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hs : stO t ∈ conjI Lv.𝔪 := Ideal.subset_span ⟨t, ht, rfl⟩
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPg
    intro h
    apply htP PP (Finset.mem_union_left _ hPP)
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _
  have hs0 : ((stO t : 𝓞 D.host.E) : D.host.E) ≠ 0 := by rw [coe_stO]; exact star_ne_zero.2 ht0

  have hsL : ∀ v ∈ Lv.sh C.X.Λ, stO t • v ∈ Lv.𝔪 • C.X.Λ := fun v hv => hv _ hs
  have h0 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w ∈
      hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)) := by
    refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)))
      ?_ ?_ ?_ ?_ hw
    · intro α hα y hy
      rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
      exact GlobalTheory.Ker.SignVac.finTens_mem hα (smul_mem_tens _ hsL hy)
    · rw [smul_zero]; exact zero_mem _
    · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
    · intro x hx; rw [smul_neg]; exact neg_mem hx

  have hz1 : finPart D (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    have h7 := (GlobalTheory.FinPl.FrameLat.cA_int_iff (e * incA D ((t : D.host.E))⁻¹)).2
      (GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP)
    rwa [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, star_inv₀] at h7
  have hA' : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ),
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ) :=
    fun o y hy => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hy
  have hx0 : partAt (cA D e) w ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
    have e1 : partAt (cA D e) w = (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) •
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w := by
      rw [smul_smul, mul_assoc]
      have e2 : incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) *
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hs0]
      rw [e2, mul_smul, GlobalTheory.Ker.SignVac.one_smul_hatA hw, partAt_eq_smul]
    rw [e1, ← hLv]
    exact smul_mem_hatA_of_int hA' hz1 h0

  have hidem : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : IsHalf (cA D e) (partAt (cA D e) w) := fun i j => by
    change cA D e * (cA D e * w i j) = cA D e * w i j
    rw [← mul_assoc, hidem]
  obtain ⟨hI, hR⟩ := ((hGen _ hhalf).2).2 hx0
  have hmv := hMv.2.2 _ hhalf
  have hcomm : partAt (cA D e) u = actO S T k₀ 1 (partAt (cA D e) w) := by
    rw [partAt_eq_smul, partAt_eq_smul, ← hu']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  rw [hcomm]
  refine ⟨GlobalTheory.WeilVacMove.isHalf_actO _ _ _ hhalf, ?_, fun PP hPP => ?_⟩
  · rw [hmv]; exact hI
  · rw [hmv]; exact hR PP hPP

end GlobalTheory.LiftLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowFock

theorem isThetaFunO_fock_right : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} {W : G'.Weil}, W.Over R → ∀ (ρ : RealMatch W), RealMatch.Over R ρ → ∀ (t : T) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f → ∀ Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank, IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (W.fock (.chi i j) f Q) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W _ ρ _ t i j hi hj e _ φ f hf Q
  have h₀ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (vacOf ρ (.right i j)) :=
    (ρ.vX_is i j hi hj).2.theta
  have hfθ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 h₀
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hfθ Q

end GlobalTheory.RowFock
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownFock

theorem isThetaFunO_fock_down : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (ρ : RealMatch W)
    (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m → ∀ {e : AE D}, IsIdemSum e (locPl G t) →
    ∀ {φ f : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ}, IsLocVec W (.mu t i j) e (vacOf ρ (.down t i j)) φ f →
    ∀ Q : PolF D (G.pT (.mu t i j)).rank (G.pS (.mu t i j)).rank,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (W.fock (.mu t i j) f Q) := by
  intro D T L sc G W ρ t i j hi hj e _he φ f hf Q
  have hv : IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.mu t i j)) (G.onT W.cart (.mu t i j))
      (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) (ρ.vT i j) := ρ.vT_is t i j hi hj
  have hf' : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 hv.2.theta
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf' Q

end GlobalTheory.DownFock
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  exact @GlobalTheory.SeeEval.evalTieT_of_levelMatch
end
