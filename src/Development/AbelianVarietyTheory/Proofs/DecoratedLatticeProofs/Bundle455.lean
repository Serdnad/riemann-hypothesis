module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle248
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle421
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.FinData

theorem isFinComb_smul {D : D7} {S T : HSp D} (r : ℂ) (c : WO S T →₀ ℂ) (h : GlobalTheory.SeeSaw.IsFinComb c) :
    GlobalTheory.SeeSaw.IsFinComb (r • c) := fun u hu => h u (Finsupp.support_smul hu)

end GlobalTheory.Fam.FinData
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

theorem GlobalTheory.Fam.finComb3 (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' c'' : WO S T →₀ ℂ) :
    GlobalTheory.SeeSaw.IsFinComb c → GlobalTheory.SeeSaw.IsFinComb c' → GlobalTheory.SeeSaw.IsFinComb c'' → ∃ d, GlobalTheory.SeeSaw.IsFinComb d ∧
      ∀ f, comb ψ S T d f = comb ψ S T c (comb ψ S T c' (comb ψ S T c'' f)) := by
  intro h h' h''
  obtain ⟨c1, hs1, he1⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c' c''
  obtain ⟨d, hs, he⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c c1
  have key : ∀ x y : WO S T, Matrix.map x (infPart D) = 0 → Matrix.map y (infPart D) = 0 →
      Matrix.map (x + y) (infPart D) = 0 := by
    intro x y hx hy
    rw [Matrix.map_add _ (fun a b => (infPart D).map_add a b), hx, hy, add_zero]
  refine ⟨d, fun w hw => ?_, fun f => by rw [he, he1]⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := hs w hw
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hs1 y hy
  exact key _ _ (h x hx) (key _ _ (h' y1 hy1) (h'' y2 hy2))
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section

namespace GlobalTheory.Unf

theorem mixS_om_compact_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  intro D ψ S T χS χT om hω θ hθ S₀ ρ d v f hf Kp hKp
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact D ψ S T χS χT om hω f hf Kp hKp
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.T.mixedCoordinate_thetaFun_le_schwartz_majorant_level D ψ hω.std θ hθ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hKN N
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hω θ hθ N
  obtain ⟨c, hc⟩ := hA f hf
  have hcont : Continuous fun p : GA D S × GA D T =>
      c * (GlobalTheory.Grow.height S p.1 * GlobalTheory.Grow.height T p.2) ^ A :=
    continuous_const.mul ((((GlobalTheory.Grow.continuous_height S).comp continuous_fst).mul
      ((GlobalTheory.Grow.continuous_height T).comp continuous_snd)).pow A)
  obtain ⟨B, hB⟩ := hKp.bddAbove_image hcont.continuousOn
  refine ⟨(C : ℝ) * max B 0, fun p hp x w => ?_⟩
  have h1 := hC (om p f) (hUK p hp) x w
  have h2 : supSob ψ θ N (om p f) ≤ ENNReal.ofReal (max B 0) :=
    (hc p.1 p.2).trans (ENNReal.ofReal_le_ofReal ((hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)))
  have hm := maj_nonneg θ K N x
  have h3 : ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * max B 0 * maj θ K N x) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    gcongr
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

end GlobalTheory.Unf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineProj

variable {D : D7}

theorem latV_le_of {S : HSp D} (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    GlobalTheory.FinPl.latV S L P ≤ GlobalTheory.FinPl.latV S L P' := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, hα, hP, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun v hv => hP v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem row_iA {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    star (vecB o ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0 := by
  show star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, o.orth,
    Matrix.vecMul_zero]

theorem row_vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  show (star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ (o.iB *ᵥ ζ) = _
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem star_self {L : HSp D} (ζ : Fin L.rank → D.host.E) :
    star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, gram_conjTranspose, ← Matrix.dotProduct_mulVec]

theorem sum_incA_mulVec {s t : ℕ} (ρ : Fin s → D.host.E) (N : Matrix (Fin s) (Fin t) D.host.E) (u : Fin t → AE D) :
    ∑ j, incA D (ρ j) * (rat N *ᵥ u) j = ∑ a, incA D ((ρ ᵥ* N) a) * u a := by

  simp only [rat, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul,
  Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {q : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} {o : OrthDec S₀ A L} {ζ : Fin L.rank → D.host.E}
  {α : Frame q A n} {α₀ : Frame q S₀ (n ⊕ Fin 1)} {M : Lat S₀} {Λ : Submodule 𝒪[k] (n → k)}

theorem e_vecB_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) :
    (fun r => q.e * incA D (vecB o ζ r)) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  let y0 : n ⊕ Fin 1 → k := Sum.elim 0 (fun _ => 1)
  have hb0 : α₀.b *ᵥ y0 = fun r => q.pr (incA D (vecB o ζ r)) := by
    rw [hsum, Matrix.fromCols_mulVec]
    funext r
    have h1 : y0 ∘ Sum.inl = 0 := Sum.elim_comp_inl _ _
    rw [Pi.add_apply, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y0,
      Sum.elim_inr, mul_one]
    rfl
  have hy0 : y0 ∈ lastKer Λ := by
    refine GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨?_, ?_⟩
    · show (Sum.elim 0 (fun _ => 1) : n ⊕ Fin 1 → k) ∘ Sum.inl ∈ Λ
      rw [Sum.elim_comp_inl]; exact zero_mem _
    · exact one_mem _
  have h := (hlat y0).1 hy0
  rw [hb0] at h
  simpa only [q.sec_pr] using h

theorem pr_coeff_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) {m : Fin S₀.rank → AE D} {c : AE D}
    (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r))
    (hem : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v)) : q.pr c ∈ 𝒪[k] := by
  let pu : Fin A.rank → k := fun a => q.pr ((o.pA *ᵥ m) a)
  let y : n ⊕ Fin 1 → k := Sum.elim (α.b' *ᵥ pu) (fun _ => q.pr c)
  have hbx : α₀.b *ᵥ y = fun r => q.pr (m r) := by
    rw [hsum, Matrix.fromCols_mulVec]
    have h1 : (o.jA.map q.pr * α.b) *ᵥ (y ∘ Sum.inl) = o.jA.map q.pr *ᵥ pu := by
      show (o.jA.map q.pr * α.b) *ᵥ (α.b' *ᵥ pu) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one]
    rw [h1]
    funext r
    rw [hmdec r, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mulVec, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y,
      Sum.elim_inr]
    exact mul_comm _ _
  have hy : y ∈ lastKer Λ := by
    refine (hlat y).2 ?_
    rw [hbx]
    simpa only [q.sec_pr] using hem
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).2

theorem pr_cA_mem {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : q.pr (cA D a) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) ((FrameLat.cA_int_iff a).2 ha.2)

theorem e_mul_mem (hM : IsSelfDualC S₀ M) {P : Pl D → Prop} {m : Fin S₀.rank → AE D}
    (hm : m ∈ GlobalTheory.FinPl.latV S₀ M P) : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  refine FrameLat.mem_of_pairing hM (fun r => Ideal.mul_mem_right _ _ (FrameLat.e_mem_idAt q)) fun s hs => ?_
  have h : FrameLat.pairing S₀ s (fun r => q.e * m r) = q.e * FrameLat.pairing S₀ s m := by
    simp only [FrameLat.pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) (FrameLat.pairing_int hM hs hm)

end Local

theorem pairing_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (e c : AE D)
    {m : Fin S₀.rank → AE D} (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r)) :
    (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * (c * incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ)) := by
  have h1 : (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * ∑ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b := by

    simp only [RingHom.map_mul, FrameLat.cA_incA, Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.star_apply]; ring
  rw [h1]
  congr 1
  have h2 : ∀ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b =
      incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * (o.jA *ᵥ (o.pA *ᵥ m)) b +
        c * (incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * incA D (vecB o ζ b)) := fun b => by
    rw [hmdec b]; ring
  simp only [h2, Finset.sum_add_distrib]
  rw [OrthDec.jA, sum_incA_mulVec, row_iA]

  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← RingHom.map_mul,
  ← map_sum]
  rfl

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj



theorem lineProj_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr m hm
  have hr : L.rank = 1 := hζ.1
  let i0 : Fin L.rank := ⟨0, by omega⟩
  have hsub : ∀ j : Fin L.rank, j = i0 := fun j => Fin.ext (by have := j.2; simp only [i0]; omega)
  have hz0 : ζ i0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [hsub j, h0]; rfl
    rw [this]; simp
  have hmid : ∀ r, m r ∈ idAt D P := FrameLat.latV_supp hm
  set c : AE D := (o.pB *ᵥ m) i0 * incA D (ζ i0)⁻¹ with hc
  have hcid : c ∈ idAt D P := by
    refine Ideal.mul_mem_right _ _ ?_
    show (∑ j, o.pB i0 j * m j) ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmid j)
  have hpB : o.pB *ᵥ m = fun j => c * incA D (ζ j) := by
    funext j
    rw [hsub j, hc, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hz0, RingHom.map_one, mul_one]
  have hjB : o.jB *ᵥ (o.pB *ᵥ m) = fun r => c * incA D (vecB o ζ r) := by
    rw [hpB]; funext r

    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, vecB, map_sum, RingHom.map_mul,
    Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r) := by
    intro r
    have h : m = o.jA *ᵥ (o.pA *ᵥ m) + o.jB *ᵥ (o.pB *ᵥ m) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        rw [OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, rat, rat, rat,
          ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
          o.iA_qA_add, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hs, Matrix.one_mulVec]
    conv_lhs => rw [h]
    rw [Pi.add_apply, hjB]
  rw [hjB]
  refine (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n S₀ A L o ζ hζ α α₀ M Λ hM hfr c hcid).2 fun i => ?_
  obtain ⟨hsum, hlat⟩ := hfr i
  have hvP : P (p i).v := (hP.mem _).2 ⟨i, rfl⟩
  have hpre : (p i).pr (p i).e = 1 := by rw [← FrameLat.sec_one, (p i).pr_sec]
  refine ⟨pr_coeff_mem hsum hlat hmdec (e_mul_mem hM hm), ?_⟩
  have hzP := latV_le_of M (P := (· = (p i).v)) (P' := P) (fun w hw => by rw [hw]; exact hvP) (e_vecB_mem hsum hlat)
  have hH := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S₀ M hM P m hmid).1 hm _ hzP
  have h := pr_cA_mem (q := p i) hH
  rw [pairing_eq o ζ (p i).e c hmdec, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, Formalism.L2.Theta.cA_cA, hpre, one_mul,
    FrameLat.cA_incA, row_vecB, star_self, RingHom.map_mul] at h
  exact h

end GlobalTheory.LineProj

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllCombProof

variable {D : D7}

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (h : ∀ x, Q x → P x) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hmono : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (h v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hmono hu), fun e he u hu hh => hf.2.2 e he u (hmono hu) hh⟩

theorem combAt_mono {S T : HSp D} {P Q : Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {J : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔
      ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem over_unique (hψ : IsStdChar D ψ (-1)) {i : ι} {g f' f'' : WO S T → ℂ}
    (h' : Over ψ (α i) (β i) LS LT g (Ψ i) f') (h'' : Over ψ (α i) (β i) LS LT g (Ψ i) f'') : f' = f'' :=
  ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k (p i) n n' ψ hψ S T (α i) (β i) LS LT h'.1 h'.2.1 g h'.2.2.1).1 (Ψ i) h'.2.2.2.1).unique h' h''

theorem overAll_unique (hψ : IsStdChar D ψ (-1)) (J : List ι) : ∀ f f' f'' : WO S T → ℂ,
    OverAll ψ α β LS LT Ψ J f f' → OverAll ψ α β LS LT Ψ J f f'' → f' = f'' := by
  induction J with
  | nil => intro f f' f'' h' h''; rw [overAll_nil.1 h', overAll_nil.1 h'']
  | cons i J ih =>
    intro f f' f'' h' h''
    obtain ⟨g, hg, h'⟩ := overAll_cons.1 h'
    obtain ⟨g', hg', h''⟩ := overAll_cons.1 h''
    obtain rfl := ih f g g' hg hg'
    exact over_unique hψ h' h''

theorem over_comb (hψ : IsStdChar D ψ (-1)) {i : ι} (hu : (p i).UnitAA) {Q : Pl D → Prop} (hQ : ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) {g f : WO S T → ℂ} (h : Over ψ (α i) (β i) LS LT g (Ψ i) f) :
    Over ψ (α i) (β i) LS LT (comb ψ S T d g) (Ψ i) (comb ψ S T d f) := by
  obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ hu S T (α i) (β i) LS LS LT LT h.1 h.2.1 h.1 h.2.1).2
    (Ψ i) h.2.2.2.1
  have M := GlobalTheory.DisjComb.main D ψ hψ S T Q (· = (p i).v) (fun x hx hx' => hQ (hx' ▸ hx))
  have hf : f = comb ψ S T c g := over_unique hψ h (hcf g h.2.2.1)
  rw [hf, M.1 d c hd hc g]
  exact hcf _ ((M.2.1 d hd).2 LS LT g h.2.2.1)

theorem overAll_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) {Q : Pl D → Prop} (hQ : ∀ i, ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) (J : List ι) (f : WO S T → ℂ) : ∀ f', OverAll ψ α β LS LT Ψ J f f' →
      OverAll ψ α β LS LT Ψ J (comb ψ S T d f) (comb ψ S T d f') := by
  induction J with
  | nil => intro f' h; rw [overAll_nil.1 h]; exact overAll_nil.2 rfl
  | cons i J ih =>
    intro f' h
    obtain ⟨g, hg, h⟩ := overAll_cons.1 h
    exact overAll_cons.2 ⟨_, ih g hg, over_comb hψ (hu i) (hQ i) hd h⟩

theorem exists_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) (hΨ : ∀ i, Ψ i ∈ SB (Matrix n n' k)) (J : List ι) (hJ : J.Nodup) :
    ∃ c : WO S T →₀ ℂ, CombAt (fun x => ∃ i ∈ J, x = (p i).v) c ∧
      ∀ f, (∀ i ∈ J, Vac ψ S T LS LT (· = (p i).v) f) → OverAll ψ α β LS LT Ψ J f (comb ψ S T c f) := by
  induction J with
  | nil =>
    exact ⟨Finsupp.single 0 1, OffTest.combAt_single_zero _ _, fun f _ => overAll_nil.2 (OffTest.comb_single_zero ψ S T f)⟩
  | cons i J ih =>
    obtain ⟨hi, hJ'⟩ := List.nodup_cons.1 hJ
    obtain ⟨c', hc', hf'⟩ := ih hJ'
    obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hu i) S T (α i) (β i) LS LS LT LT hLS hLT hLS hLT).2
      (Ψ i) (hΨ i)
    have M := GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ∃ j ∈ J, x = (p j).v) (· = (p i).v) (by
      rintro x ⟨j, hj, rfl⟩ hx
      exact hi (hinj hx ▸ hj))
    obtain ⟨c'', hc'', heq⟩ := M.2.2.2.1 c c' (combAt_mono (fun x hx => Or.inr hx) hc)
      (combAt_mono (fun x hx => Or.inl hx) hc')
    refine ⟨c'', combAt_mono ?_ hc'', fun f hf => ?_⟩
    · rintro x (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
      · exact ⟨i, List.mem_cons_self, rfl⟩
    · rw [heq]
      exact overAll_cons.2 ⟨_, hf' f fun j hj => hf j (List.mem_cons_of_mem _ hj),
        hcf _ ((M.2.1 c' hc').2 LS LT f (hf i List.mem_cons_self))⟩

end GlobalTheory.FinPl.AllCombProof

namespace GlobalTheory.FinPl


open AllCombProof in
theorem allComb : ∀ D : D7, AllComb D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ ψ hψ S T α β LS LT hLS hLT Ψ
  refine ⟨fun hΨ => ?_, overAll_unique hψ I, fun d hd f hf => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, hf⟩ := exists_comb (α := α) (β := β) hψ hP.unit hP.inj hLS hLT hΨ I hP.nodup
    refine ⟨c, combAt_mono ?_ hc, fun f h => hf f fun i _ => vac_mono ?_ h⟩
    · rintro x ⟨i, -, rfl⟩
      exact (hP.mem _).2 ⟨i, rfl⟩
    · rintro x rfl
      exact (hP.mem _).2 ⟨i, rfl⟩
  · exact ((GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ¬ P x) P fun x hx => hx).2.1 d hd).2 LS LT f hf
  · exact overAll_comb hψ hP.unit (fun i h => h ((hP.mem _).2 ⟨i, rfl⟩)) hd I f

end GlobalTheory.FinPl

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm GlobalTheory.QTw
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw

theorem frsF_base_eq_self : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀), A.Is → I.Ok → ∀ (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (i : ℕ), i ≤ B.R.m → ∀ (β : Ch₀ i), (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1) → ∀ (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i β).1.1 P x = x := by
  intro B X I l Z u a Ch₀ A hA hI P hP i hi β hv x
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
    intro hm
    apply GlobalTheory.KerT.T_notMem_rowSG (I.tup a) (GlobalTheory.BasePrimes.primes_ok B X).1 hI.sel_ok (hI.T_mem u) P.1 P.2
    have := Ideal.mem_comap.1 hm
    simpa [map_natCast] using this
  have hk := hv _ hT
  have hpt := (hA.base i hi β).1
  have hfr := hpt.fr ⟨P.1, hSQ⟩
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩]
  set f := (extTo I.SQ (A.p0 i β).1.1).fr ⟨P.1, hSQ⟩ with hf
  have key : ∀ j : Fin (B.R.N i), f (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext r
    have h1 := hfr r j
    rw [GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_one P.1 hk r j] at h1
    apply (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective
    rw [← h1, Pi.single_apply]
    split_ifs <;> simp
  have : (f : Formalism.L2.Col.Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N i)) = LinearMap.id :=
    LinearMap.pi_ext' fun j => LinearMap.ext_ring (key j)
  exact congrArg (fun g => g x) this

end GlobalTheory.QTw
end
