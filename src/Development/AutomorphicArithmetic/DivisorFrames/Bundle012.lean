module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle363
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace UpperTheory.standardActionStabilizer

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem isIntM_mul {b a c : ℕ} {N : Matrix (Fin b) (Fin a) (Lev.EAf D)} {κ : Matrix (Fin a) (Fin c) (Lev.EAf D)}
    (hN : IsIntM N) (hκ : IsIntM κ) : IsIntM (N * κ) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hN i l) (hκ l j)

private theorem inId_mul {b a c : ℕ} {I : Ideal (𝓞 D.host.E)} {N : Matrix (Fin b) (Fin a) (Lev.EAf D)}
    {κ : Matrix (Fin a) (Fin c) (Lev.EAf D)} (hκ : IsIntM κ) (i : Fin b) (hN : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i l))
    (j : Fin c) : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((N * κ) i j) := by
  choose hInt hId using hN
  have hm : (N * κ) i j ∈ OO := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => mul_mem (hInt l) (hκ l j)
  refine ⟨hm, ?_⟩
  let entry (l : Fin a) : OO := (⟨N i l, hInt l⟩ : OO) * ⟨κ l j, hκ l j⟩
  have e : (⟨(N * κ) i j, hm⟩ : OO) = ∑ l, entry l := by
    apply Subtype.ext
    change (N * κ) i j = (OO).subtype (∑ l, entry l)
    rw [Matrix.mul_apply]
    exact (map_sum (OO).subtype entry Finset.univ).symm
  rw [e]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hId l)

private theorem topL_mul {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Lev.EAf D)) (κ : Matrix (Fin a) (Fin a) (Lev.EAf D)) :
    topL a (N * κ) = topL a N * κ := by
  ext i j
  simp only [topL, Matrix.mul_apply]
  by_cases hi : i.1 < b
  · simp [hi]
  · simp [hi]

private theorem det_int {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N) : N.det ∈ OO := by
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, hN i j⟩
  have eA : N.det = ((A.det : OO) : Lev.EAf D) := by
    rw [show N = (OO).subtype.mapMatrix A from rfl]
    exact (RingHom.map_det (OO).subtype A).symm
  rw [eA]
  exact A.det.2

private theorem isUnitDet_unique {e : AE D} {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} {x x' : (AE D)ˣ}
    (h : IsUnitDet e N x) (h' : IsUnitDet e N x') : x = x' :=
  Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm))

private theorem idem_mul {R : Type} [CommRing R] {ε a b : R} (hε : ε * ε = ε) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (a * b - a - b + 1) * hε

private theorem succ_mul_succ_sub_one_div_succ {R : Type} [CommRing R] {ε z y yi a b : R} (hε : ε * ε = ε) (hz : z = 1 - ε + ε * (a * b))
    (hy : y = 1 - ε + ε * b) (hyy : y * yi = 1) : z * yi = 1 - ε + ε * a := by
  subst hz hy
  linear_combination (1 - ε + ε * a) * hyy - (a * b - a - b + 1) * yi * hε

private theorem isUnitDet_mul {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (Lev.EAf D)} {x y : (AE D)ˣ} (hx : IsUnitDet e L x) (hy : IsUnitDet e κ y) :
    IsUnitDet e (L * κ) (x * y) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx.1, hy.1, mul_one]
  · rw [Units.val_mul, map_mul, hx.2.1, hy.2.1, Matrix.det_mul, idem_mul hε]
  · rw [_root_.mul_inv_rev, Units.val_mul, map_mul]
    exact mul_mem hy.2.2 hx.2.2


private theorem isUnitDet_div {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hκ : IsIntM κ) {z y : (AE D)ˣ} (hz : IsUnitDet e (L * κ) z)
    (hy : IsUnitDet e κ y) : IsUnitDet e L (z * y⁻¹) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hyy : toEAf D (y : AE D) * toEAf D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : infPart D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv y)
    rwa [map_mul, hy.1, one_mul, map_one] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hz.1, hinv, mul_one]
  · rw [Units.val_mul, map_mul]
    exact succ_mul_succ_sub_one_div_succ hε (hz.2.1.trans (by rw [Matrix.det_mul])) hy.2.1 hyy
  · have e0 : (z * y⁻¹)⁻¹ = y * z⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    rw [Units.val_mul]
    rw [map_mul]
    refine mul_mem ?_ hz.2.2
    rw [hy.2.1]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ))

private theorem unitChar_mul (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {k : ℕ} (L κ : Matrix (Fin k) (Fin k) (Lev.EAf D)) (hκ : IsIntM κ) {y : (AE D)ˣ} (hy : IsUnitDet e κ y) :
    unitChar ν e (L * κ) = (((ν y)⁻¹ : Circle) : ℂ) * unitChar ν e L := by
  unfold unitChar
  by_cases hL : ∃ x, IsUnitDet e L x
  · have hLκ : ∃ x, IsUnitDet e (L * κ) x := ⟨_, isUnitDet_mul he hL.choose_spec hy⟩
    rw [dite_eq_left hL, dite_eq_left hLκ, isUnitDet_unique hLκ.choose_spec (isUnitDet_mul he hL.choose_spec hy), map_mul,
      _root_.mul_inv_rev, Circle.coe_mul]
  · have hLκ : ¬ ∃ x, IsUnitDet e (L * κ) x := fun ⟨z, hz⟩ => hL ⟨_, isUnitDet_div he hκ hz hy⟩
    rw [dite_eq_right hL, dite_eq_right hLκ, mul_zero]

private theorem half_act {e : AE D} (S T : HSp D) (g : GA D S) {x : WO S T} (h : IsHalf e x) :
    IsHalf e (actO S T g 1 x) := fun i j => by
  unfold actO
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_assoc, mul_left_comm, h m l]

private theorem act_act (S T : HSp D) (g : GA D S) (x : WO S T) :
    actO S T g⁻¹ 1 (actO S T g 1 x) = x := by
  have h1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
  have h2 : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    rw [← h1 S, ← inv_mul_cancel g]; simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_inv, h1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem st_int {n : ℕ} {β k : GL (Fin n) (Lev.EAf D)} (h : k ∈ Formalism.L2.DIV.St β) :
    IsIntM (β⁻¹ * k * β : GL (Fin n) (Lev.EAf D)).val := by
  obtain ⟨y, rfl⟩ := h
  have e : (β⁻¹ * Formalism.L2.DIV.frGL β y * β : GL (Fin n) (Lev.EAf D)) = Formalism.L2.DIV.intGL _ _ n y := by
    show β⁻¹ * (β * Formalism.L2.DIV.intGL _ _ n y * β⁻¹) * β = _
    group
  rw [e]
  exact fun i j => (y.val i j).2

end UpperTheory.standardActionStabilizer

open UpperTheory.standardActionStabilizer in


theorem UpperTheory.stdFst_actO_of_mem_stabilizer :
    ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (ν : (AE D)ˣ →* Circle) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (I : Ideal (𝓞 D.host.E)),
      IsIdemSum e Z → ∀ g : GA D S, Lev.finE S g ∈ Formalism.L2.DIV.St βS → ∀ y : (AE D)ˣ,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val y →
      ∀ x : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT (actO S T g 1 x) = ((ν y : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x := by
  intro D S T βS βT ν e Z I he g hg y hy x
  have hκ' := st_int hg
  have hκ := st_int ((Formalism.L2.DIV.St βS).inv_mem hg)
  have einv : (βS⁻¹ * (Lev.finE S g)⁻¹ * βS : GL (Fin S.rank) (Lev.EAf D)) = (βS⁻¹ * Lev.finE S g * βS)⁻¹ := by group
  rw [einv] at hκ
  have hfr := GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x
  generalize (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)) = γ at hy hκ hκ' hfr
  have hkk : (γ⁻¹).val * γ.val = 1 := Units.inv_mul γ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [hfr]
  generalize frMapO S T βS βT x = N
  have hH : IsHalf e (actO S T g 1 x) ↔ IsHalf e x :=
    ⟨fun h => by have := half_act S T g⁻¹ h; rwa [act_act] at this, half_act S T g⟩
  have hI : IsIntM (N * (γ⁻¹).val) ↔ IsIntM N := by
    refine ⟨fun h => ?_, fun h => isIntM_mul h hκ⟩
    have := isIntM_mul h hκ'
    rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
  have hR : (∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((N * (γ⁻¹).val) i j)) ↔
      ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i j) := by
    refine ⟨fun h i j hi => ?_, fun h i j hi => inId_mul hκ i (fun l => h i l hi) j⟩
    have := inId_mul hκ' i (fun l => h i l hi) j
    rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
  have hU := unitChar_mul ν he (topL S.rank N * (γ⁻¹).val) γ.val hκ' hy
  rw [Matrix.mul_assoc, hkk, Matrix.mul_one] at hU
  by_cases hc : IsHalf e x ∧ IsIntM N ∧ ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i j)
  · rw [if_pos hc, if_pos ⟨hH.2 hc.1, hI.2 hc.2.1, hR.2 hc.2.2⟩, topL_mul, hU, ← mul_assoc, ← Circle.coe_mul,
      mul_inv_cancel, Circle.coe_one, one_mul]
  · rw [if_neg hc, if_neg fun h => hc ⟨hH.1 h.1, hI.1 h.2.1, hR.1 h.2.2⟩, mul_zero]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] {ε : R} (h : ε * ε = ε) (n : ℕ) : (1 : R) = 1 - ε + ε * ε ^ n := by
  have : ε * ε ^ n = ε := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, h]
  rw [this]; ring

private theorem matrix_map_ringHom_add_smul_sandwich {R : Type} [CommRing R] {a b : ℕ} (βS : GL (Fin a) R) (βT : GL (Fin b) R) (ε : R)
    (J : Matrix (Fin b) (Fin a) R) :
    (βT⁻¹).val * (ε • (βT.val * J * (βS⁻¹).val)) * βS.val = ε • J := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
    Matrix.mul_one]

private theorem topL_smul_identity {R : Type} [CommRing R] {a b : ℕ} (hab : a ≤ b) (ε : R) :
    topL a (ε • (Matrix.of fun (i : Fin b) (j : Fin a) => if i.1 = j.1 then (1 : R) else 0)) =
      ε • (1 : Matrix (Fin a) (Fin a) R) := by
  ext i j
  unfold topL
  rw [dite_eq_left ⟨lt_of_lt_of_le i.2 hab, j.2⟩]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem UpperTheory.exists_stdFst_ne_zero_of_rank_le :
    ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (ν : (AE D)ˣ →* Circle) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (I : Ideal (𝓞 D.host.E)),
      S.rank ≤ T.rank → IsIdemSum e Z → ∃ x : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x ≠ 0 := by
  intro D S T βS βT ν e Z I hr he
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hεε : toEAf D e * toEAf D e = toEAf D e := by rw [← RingHom.map_mul, hee]
  let J : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of fun i j => if i.1 = j.1 then 1 else 0
  let M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := βT.val * J * (βS⁻¹).val
  choose w _ hw using fun i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj (D := D) (M i j)
  let x : WO S T := fun i j => e * w i j
  have hx : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • M := by
    ext i j
    change toEAf D (e * w i j) = toEAf D e * M i j
    rw [RingHom.map_mul, hw]
  have hf : frMapO S T βS βT x = toEAf D e • J := by
    unfold frMapO
    rw [hx]
    exact matrix_map_ringHom_add_smul_sandwich βS βT (toEAf D e) J
  have hJ : ∀ i j, (toEAf D e • J) i j = if i.1 = j.1 then toEAf D e else 0 := fun i j => by
    change toEAf D e * (if i.1 = j.1 then 1 else 0) = _
    split_ifs
    · exact mul_one _
    · exact mul_zero _
  have h1 : IsHalf e x := fun i j => by
    change e * (e * w i j) = e * w i j
    rw [← mul_assoc, hee]
  have h2 : IsIntM (toEAf D e • J) := fun i j => by
    rw [hJ]
    split_ifs
    · exact hE
    · exact zero_mem _
  have h3 : ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((toEAf D e • J) i j) := fun i j hi => by
    have hj := j.2
    rw [hJ, if_neg (by omega)]
    exact ⟨zero_mem _, zero_mem _⟩
  have h4 : ∃ y, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL S.rank (toEAf D e • J)) y := by
    refine ⟨1, RingHom.map_one _, ?_, ?_⟩
    · rw [topL_smul_identity hr, Matrix.det_smul, Matrix.det_one, mul_one, Units.val_one, RingHom.map_one]
      exact units_mul_relation_rearrange_commRing hεε _
    · rw [inv_one, Units.val_one, RingHom.map_one]
      exact one_mem _
  refine ⟨x, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [hf, if_pos ⟨h1, h2, h3⟩]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar
  rw [dite_eq_left h4]
  exact Circle.coe_ne_zero _
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ v (GlobalTheory.WeilM.schr ψ w Φ) =
      ψ (⅟(2 : R) * (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2)) • GlobalTheory.WeilM.schr ψ (v + w) Φ := by
  funext z
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add,
    Prod.snd_add, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(v.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : R)

private theorem thetaSum_rho_rho' {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U]
    {B : U → U → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Φ : (κ → AF F) → ℂ) (x y : U) :
    GlobalTheory.WeilM.thetaSum F (co.rho ψ x (co.rho ψ y Φ)) =
      ψ (⅟(2 : AF F) * B x y) * GlobalTheory.WeilM.thetaSum F (co.rho ψ (x + y) Φ) := by
  simp only [GlobalTheory.WeilM.Darboux.rho, schr_schr', GlobalTheory.WeilM.thetaSum, map_add (f := _), Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    co.form]

private theorem exists_co' {D : D7} {ε : Bool} {S X : HSp D} {d : ℕ} (e : Fin d ≃ Fin X.rank)
    {Vs : Spc D.host.F D.host.E S.rank} {Ws : Spc D.host.F D.host.E d} (M : Model D.sp.cm.sig Vs Ws)
    (hX : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) 1 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))) (Fin S.rank × Fin d),
      ∀ x, co.e x = M.co.e (ptO (sgn ε S).gram e x) := by
  have hdet : IsUnit (sgn ε S).gram.det := (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hG : ((sgn ε S).gram.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = ((sgn ε S).gram.map (incA D))ᵀ := by
    ext i j
    show cA D (incA D ((sgn ε S).gram i j)) = incA D ((sgn ε S).gram j i)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  have hVJ : Vs.J = -(sgn ε S).gram := by
    rw [hX]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  obtain ⟨G, hGd⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G = (sgn ε S).gram := ⟨_, rfl⟩
  rw [← hGd] at hdet hG hVJ ⊢
  have h1 : G.map (incA D) * (G⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (G⁻¹).map (incA D) * G.map (incA D) = 1 := mul_eq_one_comm.1 h1
  have hp : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), ptO G e x = ((x * (G⁻¹).map (incA D))ᵀ).submatrix id e :=
    fun _ => rfl
  have hr : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), (ptO G e x)ᵀ.submatrix e.symm id * G.map (incA D) = x := fun x => by
    have e1 : (ptO G e x)ᵀ.submatrix e.symm id = x * (G⁻¹).map (incA D) := by
      rw [hp]
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [e1, Matrix.mul_assoc, h2, Matrix.mul_one]
  let T : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ Matrix (Fin X.rank) (Fin S.rank) (AE D) :=
    { toFun := fun u => uᵀ.submatrix e.symm id * G.map (incA D)
      invFun := ptO G e
      left_inv := fun u => by
        rw [hp, Matrix.mul_assoc, h1, Matrix.mul_one]
        ext i j
        simp only [submatrix_apply, transpose_apply, id, Equiv.symm_apply_apply]
      right_inv := hr
      map_add' := fun u v => by rw [← Matrix.add_mul]; rfl }
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
    (X.gram.map (incA D)) (incA D D.host.xi0) h2 hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • G⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _)
    (by rw [hW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co T (fun _ => rfl)
  exact ⟨co, fun x => (congrArg co.e (hr x)).symm.trans (hco _)⟩

theorem UpperTheory.thetaOperator_intertwines_heisenberg :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M →
        (∀ x y : WO (sgn ε S) X, GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (ptO (sgn ε S).gram e x) (ptO (sgn ε S).gram e y) =
          symplO (sgn ε S) X x y) ∧
        (∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (y : WO (sgn ε S) X),
          thO M ψ (sgn ε S).gram e (M.co.rho ψ (ptO (sgn ε S).gram e y) Φ) = heisO ψ (sgn ε S) X y (thO M ψ (sgn ε S).gram e Φ)) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e (Φ + Φ') = thO M ψ (sgn ε S).gram e Φ + thO M ψ (sgn ε S).gram e Φ') ∧
        (∀ (c : ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), thO M ψ (sgn ε S).gram e (c • Φ) = c • thO M ψ (sgn ε S).gram e Φ) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e Φ = thO M ψ (sgn ε S).gram e Φ' → Φ = Φ') ∧
        ∀ f : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f ↔
          ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), thO M ψ (sgn ε S).gram e Φ = f := by
  intro D ψ ε S X d e Bs Vs Ws M hP
  have hψ : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hP.psi ▸ hP.base.std)
  obtain ⟨co, hco⟩ := exists_co' e M hP.JV hP.JW
  have hr : ∀ x, co.rho ψ x = M.co.rho ψ (ptO (sgn ε S).gram e x) := fun x => by
    simp only [GlobalTheory.WeilM.Darboux.rho, hco]
  have hth : ∀ Φ, thO M ψ (sgn ε S).gram e Φ = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := fun Φ => by
    funext x
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, hr]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε S) (T := X) co hψ rfl (one_smul _ _) (fun x => by
    obtain ⟨y, z, h⟩ := hP.good.rat (((x * (sgn ε S).gram⁻¹)ᵀ).submatrix id e)
    refine ⟨y, z, Eq.trans ?_ h⟩
    rw [hco]
    congr 1
    exact (congrArg (fun m => (transpose m).submatrix id e) (Matrix.map_mul (f := incA D))).symm)
  have hs := GlobalTheory.ThetaTransform.symplO_eq_symp (S := sgn ε S) (T := X) (ξ := 1) rfl (one_smul _ _)
  simp only [hth]
  refine ⟨fun x y => ?_, fun Φ y => ?_, h1, GlobalTheory.ThetaTransform.thetaTr_smul co, h2, h3⟩
  · rw [hs, co.form, M.co.form, hco, hco]
  · funext x
    rw [← hr]
    show GlobalTheory.WeilM.thetaSum D.host.F (co.rho ψ x (co.rho ψ y Φ)) = _
    rw [thetaSum_rho_rho', ← hs, GlobalTheory.ThetaTransform.invOf_two_eq]
    rfl
end
