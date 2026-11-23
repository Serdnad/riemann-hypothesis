module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle321
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle588
public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsEqPureVacuumOfLatticeInvariant
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsSplitIdempotentMulEqOfPiWEqZero
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle008
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle012
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem prod_orthogonal_idempotents {R ι : Type} [CommRing R] [DecidableEq ι] (d : R) (es : ι → R) (Z : Finset ι)
    (ho : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → es i * es j = 0) :
    ∏ w ∈ Z, (es w * d + (1 - es w)) = (∑ w ∈ Z, es w) * d + (1 - ∑ w ∈ Z, es w) := by
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : es a * ∑ w ∈ s, es w = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        ho a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) fun h => ha (h ▸ hj)
    linear_combination (d - 1) ^ 2 * h0

private theorem inv_aux {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Aˣ) (ε d d' : B)
    (hε : ε * ε = ε) (hd : d * d' = 1) (hx : f (x : A) = 1 - ε + ε * d) :
    f ((x⁻¹ : Aˣ) : A) = 1 - ε + ε * d' := by
  have h1 : f ((x⁻¹ : Aˣ) : A) * f (x : A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h2 : f (x : A) * (1 - ε + ε * d') = 1 := by
    rw [hx]; linear_combination (1 - d - d' + d * d') * hε + ε * hd
  calc f ((x⁻¹ : Aˣ) : A) = f ((x⁻¹ : Aˣ) : A) * (f (x : A) * (1 - ε + ε * d')) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

private theorem det_conj_eq {n : ℕ} {B : Type} [CommRing B] (β γ : GL (Fin n) B) :
    (β⁻¹ * γ * β : GL (Fin n) B).val.det = γ.val.det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem UpperTheory.isUnitDet_prod_detIdl_of_mem_St :
    ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)),
      IsIdemSum e Z → ∀ g : GA D S, Lev.finE S g ∈ Formalism.L2.DIV.St βS →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val
        (∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g) := by
  classical
  intro D S βS e Z hZ g hg
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hZ
  have hee : e * e = e := GlobalTheory.Tow.idemSum_mul_of_subset hZ hZ (Finset.Subset.refl Z)
  have hint := GlobalTheory.IdemRes.toEAf_mem_of_finPart
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee]))
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hZ
  have hid : ∀ w ∈ Z, GlobalTheory.RowVacScalar.idemAt w = es w := fun w hw =>
    GlobalTheory.Tow.idemAt_unique
      (Classical.epsilon_spec (p := fun a : AE D => Formalism.L2.NTheta.IsIdemAt a w) ⟨es w, hes w hw⟩) (hes w hw)
  have hval : ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = e * (Formalism.L2.Theta.mt S g).det + (1 - e) := by
    rw [Units.coe_prod, hsum, ← prod_orthogonal_idempotents _ es Z fun i hi j hj hij => GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hid w hw, GlobalTheory.RowVacScalar.detIdl_val (hes w hw).1.1]
  have hdet : toEAf D (Formalism.L2.Theta.mt S g).det = (Lev.finE S g).val.det := by
    rw [RingHom.map_det]; rfl
  have h2 : toEAf D ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = 1 - toEAf D e + toEAf D e * (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det := by
    rw [hval, det_conj_eq, map_add (f := _), map_mul, map_sub, map_one, hdet, add_comm]
  refine ⟨?_, h2, ?_⟩
  · rw [hval, map_add (f := _), map_mul, map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · obtain ⟨z, hz⟩ := hg
    have hz' : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)) = Formalism.L2.DIV.intGL _ _ _ z := by
      rw [← hz]
      show βS⁻¹ * (βS * Formalism.L2.DIV.intGL _ _ _ z * βS⁻¹) * βS = _
      group
    have hzd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det
        = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype z.val.det := by
      rw [hz', RingHom.map_det]; rfl
    have hd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det *
        (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (z⁻¹).val.det = 1 := by
      rw [hzd, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
    rw [inv_aux (toEAf D) _ _ _ _ (by rw [← map_mul, hee]) hd h2]
    exact add_mem (sub_mem (one_mem _) hint) (mul_mem hint (z⁻¹).val.det.2)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_crd {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) :
    ptO G e (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)) = u := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  ext i j
  simp

private theorem ptO_two {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d)
    (x : Matrix (Fin d) (Fin m) (AE D)) : ptO G e (2 • x) = 2 • ptO G e x := by
  unfold GlobalTheory.TripleRead.ptO
  rw [two_nsmul, two_nsmul, Matrix.add_mul]
  rfl

private theorem isHalf_crd {D : D7} {m k d : ℕ} (H : Matrix (Fin m) (Fin m) (AE D)) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) (a : AE D) (h : ∀ i j, a * u i j = u i j) :
    IsHalf a (HMul.hMul (uᵀ.submatrix e.symm id) H : Matrix (Fin d) (Fin m) (AE D)) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc]
  exact congrArg (· * H l j) (h l (e.symm i))

theorem UpperTheory.exists_thO_eq_of_isLatVac_thetaFun :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        ∀ f₀ : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f₀ → IsLatVac (heisO ψ (sgn ε S) X) (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True) f₀ →
        ∃ g : SInf D.host.F (Fin S.rank × Fin d), f₀ = thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) := by
  intro D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL f₀ hth hvac
  obtain ⟨-, hrho, -, -, hinj, hon⟩ := UpperTheory.thetaOperator_intertwines_heisenberg D ψ ε S X d e Bs Vs Ws M hP
  obtain ⟨hlat, -⟩ := UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL
  obtain ⟨Ψ, hΨ, rfl⟩ := (hon f₀).1 hth
  obtain ⟨r, s, hV⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  have hψ := hP.psi
  subst hψ
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hfix : ∀ y : WO (sgn ε S) X, heisO Bs.ψ (sgn ε S) X y (thO M Bs.ψ (sgn ε S).gram e Ψ) = thO M Bs.ψ (sgn ε S).gram e Ψ →
      M.co.rho Bs.ψ (ptO (sgn ε S).gram e y) Ψ = Ψ := fun y hy =>
    hinj _ (GlobalTheory.HeisSchA.rho_mem_schA M Bs.ψ hP.base.std _ Ψ hΨ) _ hΨ ((hrho Ψ y).trans hy)
  obtain ⟨g, hg⟩ := UpperTheory.exists_eq_pure_vacuum_of_lattice_invariant D.host.F D.host.E D.sp.cm.sig Bs S.rank d Vs Ws M r s r' s' hP.base hV hW hP.good Ψ hΨ
    (fun v γ hγ => by
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have h2 := hfix _ (hvac.1 _ h1)
      have h3 := (ptO_two (D := D) _ e _).trans (congrArg (2 • ·) h0)
      exact h3 ▸ h2)
    (fun v t γ hγ ht => by
      obtain ⟨a, ha, haz⟩ := UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero D v t
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have hat := (GlobalTheory.LatVac.latAtV_at_stable Vs Ws v).1 γ hγ
      have h2 := hfix _ (hvac.2 a ha _ h1 (isHalf_crd _ e γ a fun i j =>
        haz _ (fun u hu => congrFun (congrFun (hat u hu) i) j) (congrFun (congrFun ht i) j)))
      exact h0 ▸ h2)
  exact ⟨g, by rw [← hg]⟩
end
