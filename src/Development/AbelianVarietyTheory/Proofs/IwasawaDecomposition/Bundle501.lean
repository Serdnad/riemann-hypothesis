module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.AdjDatumNe

open GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec

def rectOne (R : Type) [Zero R] [One R] (b a : ℕ) : Matrix (Fin b) (Fin a) R :=
  fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rectOne (R : Type) [Zero R] [One R] (b a k : ℕ) : LowZero k (rectOne R b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rectOne (R : Type) [Zero R] [One R] {b a : ℕ} (h : a ≤ b) : topL a (rectOne R b a) = 1 := by
  ext i j
  have h1 : i.val < b ∧ j.val < a := ⟨by omega, j.2⟩
  unfold topL rectOne
  rw [dif_pos h1, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem sandwich_cancel' {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (c : R) (hA : A' * A = 1) (hG : G * G' = 1)
    (hB : B' * B = 1) (hH : H * H' = 1) : (A' * G') * (c • ((G * A) * N * (B' * H'))) * (H * B) = c • N := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have hH' : H' * H = 1 := mul_eq_one_comm.1 hH
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (A' * (G' * G) * A) * N * (B' * (H' * H) * B) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hG', hH', Matrix.mul_one, Matrix.mul_one, hA, hB, Matrix.one_mul, Matrix.mul_one]

variable {D : D7}

theorem toEAf_surjective (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add (f := _), hs, ht]⟩

theorem exists_half_frMapAdj (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} (he : e * e = e) (I : Matrix (Fin S.rank) (Fin T.rank) (EAf D)) :
    ∃ x : WO S T, IsHalf (cA D e) x ∧ frMapAdj S T βS βT x = toEAf D e • I := by
  choose N hN using fun (i : Fin S.rank) (j : Fin T.rank) => toEAf_surjective
    (((S.gram.map (eToEAf D) * βS.val) * I * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) i j)
  refine ⟨Matrix.of fun j i => cA D (e * N i j), fun j i => ?_, ?_⟩
  · change cA D e * cA D (e * N i j) = cA D (e * N i j)
    rw [← RingHom.map_mul, ← mul_assoc, he]
  · rw [frMapAdj_eq, ← sandwich_cancel' _ _ _ _ _ _ _ _ I (toEAf D e) βS.inv_mul (gram_map_mul_inv S) βT.inv_mul
      (gram_map_mul_inv T)]
    congr 2
    refine Matrix.ext fun i j => ?_
    change cF D (toEAf D (cA D (e * N i j))) = toEAf D e * _
    rw [toEAf_cA, cF_cF_toEAf, RingHom.map_mul, hN]

theorem idemSum_res {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      ∀ PP ∈ P, Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := idemSum_mul_self h
  have hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hi, fun PP hPP => ?_⟩
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  have h3 : es PP * ∑ j ∈ P, es j = es PP :=
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij =>
      (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h =>
        hij (isIdemAt_inj (h1 j hj) (h ▸ h1 i hi))) hPP
  rw [← h2] at h3
  obtain ⟨k, hk⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)
  have h4 : (⟨toEAf D (es PP), k⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D e, hi⟩ = ⟨toEAf D (es PP), k⟩ :=
    Subtype.ext (by change toEAf D (es PP) * toEAf D e = toEAf D (es PP); rw [← RingHom.map_mul, h3])
  have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
  rwa [RingHom.map_mul, hk, one_mul] at h5

theorem isIntM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b a : ℕ) :
    IsIntM (ε • rectOne (EAf D) b a) := by
  intro i j
  change ε * (if i.val = j.val then 1 else 0) ∈ _
  split_ifs
  · rwa [mul_one]
  · rw [mul_zero]; exact zero_mem _

theorem redM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hi⟩ = 1) (b a : ℕ) :
    redM PP (ε • rectOne (EAf D) b a) = rectOne _ b a := by
  funext i j
  refine (dif_pos (isIntM_smul_rectOne hi b a i j)).trans ?_
  by_cases hij : i.val = j.val
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) (h.trans (if_pos hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = ε
    rw [if_pos hij, mul_one]
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) ((RingHom.map_zero _).trans (if_neg hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = 0
    rw [if_neg hij, mul_zero]

theorem exists_datum_ne_zero : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q P : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D), T.rank ≤ S.rank → IsIdemSum e P → (∀ PP ∈ Pg, PP ∈ P) → (∀ PP ∈ Q, PP ∈ P) → ∃ x : WO S T, IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := by
  intro D S T βS βT Pg Q P ξ e hr he hg hQ
  obtain ⟨x, hx, hx'⟩ := exists_half_frMapAdj S T βS βT (idemSum_mul_self he) (rectOne _ _ _)
  obtain ⟨hi, hres⟩ := idemSum_res he
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hx']; exact isIntM_smul_rectOne hi _ _
  · have key : ∀ PP ∈ P, LowZero T.rank (redM PP (frMapAdj S T βS βT x)) ∧
        topL T.rank (redM PP (frMapAdj S T βS βT x)) = 1 := fun PP hPP => by
      rw [hx', redM_smul_rectOne hi PP (hres PP hPP)]
      exact ⟨lowZero_rectOne _ _ _ _, topL_rectOne _ hr⟩
    refine mul_ne_zero ?_ ?_
    · unfold omegaK
      rw [if_pos fun PP hPP => key PP (hg PP hPP)]
      exact one_ne_zero
    · unfold omegaQ
      rw [dif_pos fun PP hPP => ⟨(key PP (hQ PP hPP)).1, by
        rw [(key PP (hQ PP hPP)).2, Matrix.det_one]; exact isUnit_one⟩]
      exact Finset.prod_ne_zero_iff.2 fun PP _ => zpow_ne_zero _ (Units.ne_zero _)

end GlobalTheory.AdjDatumNe

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayRosEx.ThetaPull

section Jets

variable {S : Type} [CommRing S] {ρ : Type}

end Jets

section Vals

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans
      (gm_val (κ ≫ r) w _ h _).symm))

end Vals

end GlobalTheory.RayRosEx.ThetaPull
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

abbrev Frame {X Y : Scheme.{0}} (L : LB X) (ψ : Y ⟶ X) : Type :=
  LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1)

section Defs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def Lies {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left),
    y ≫ fGl I G e = r ≫ x' → y ≫ pGl U e = r ≫ b

def FrRel {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) (g' : Frame U.LG.L x')
    (g : Frame D.toPre.P.L b) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left), y ≫ fGl I G e = r ≫ x' →
    ∀ (z : Z) (JM) (JL), Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val g r z JM = wVal U e z JM JL y * val g' r z JL

end Defs

end GlobalTheory.RayEv.Transport
end
end
