module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle639
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle566
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle512
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle513
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP

theorem eq_mul_of_inv_mul {a b c d : ℂ} (ha : a ≠ 0) (h : a⁻¹ * b = c * d) : b = a * c * d := by
  rw [mul_assoc, ← h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

theorem mul_eq_of {a c d u v p q : ℂ} (h1 : u = a * p) (h2 : v = c * d * q) : u * v = a * (c * d) * (p * q) := by
  rw [h1, h2]; ring

theorem const_eq {a b c I : ℂ} (hb : b ≠ 0) : a * b⁻¹ * (b * c) * I = c * a * I := by
  field_simp



theorem ioX_levChi_gen {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ)
    (hL : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T)
    (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) (κ : GA D (Yc D (D.R.m - 1)))
    (hκ : κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P)) (φ x g) :
    (R.ioX t F).1 (R.ItX φ x) (g * κ) =
      levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ * (R.ioX t F).1 (R.ItX φ x) g := by
  have hθ : IsInfFam R.θ := hm.inf
  have hio := hc.ioX t
  have hκG : κ ∈ GfC (Yc D (D.R.m - 1)) := hκ.1
  have hκP : Lev.finE (Yc D (D.R.m - 1)) κ ∈ parLev D.sp.cm (Yc D (D.R.m - 1)).gram (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) := hκ.2.1
  have hκH : rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ) ∈ P.H := hκ.2.2
  have hκl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)
      (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ)) κ := ⟨hκG, hκP, rfl⟩
  refine (GlobalTheory.Fam.FamInhab.lifts_top (R := R) hL t
    (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ))).elim fun κ' hκ' => ?_
  have hlaw := GlobalTheory.StepLaw.last_step_law R hL hθ hc.ωX hc.vX t _ κ κ' hκl hκ'
  have hsS : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' ≠ 0 := levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ •
      R.ωX t (κ, κ') (R.vX t) =
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := hlaw
  have hv : R.ωX t (κ, κ') (R.vX t) =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ *
        (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.vX t := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ _ _ _ _ (R.ωX t) hθ (hc.ωX t)
    _ _ _ _ (R.vX t) (hc.ptX t) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ _ _ _ _ (R.ωX t) (hc.ωX t)
    (R.ptX t φ) (hc.ptX t φ)
  have e1 : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ =
      ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := R.datYt t (D.R.m - 1) R.triv) P, extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hfd : (R.νX t).IsHaarMeasure ∧ IsFundamentalDomain (GQ D.sp.X') (R.fdX t) (R.νX t) :=
    ⟨(hm.νX t).1.1, (hm.νX t).2⟩
  have hi := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable D.sp.X'
  haveI i1 := hi.1
  haveI i2 := hi.2.1
  haveI i3 := hi.2.2.1
  haveI i4 := hi.2.2.2
  have htg : IsTopologicalGroup (GA D D.sp.X') := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig D.sp.X'.gram))
  haveI := hfd.1
  haveI hR : (R.νX t).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') (R.νX t) = R.νX t := map_mul_right_eq_self _ κ'
  have hFv := (GlobalTheory.StepLevelP.IoLevPf.multT_val R.θ R.MX _ _ F.1 hF x).1
  have hF1 := ((GlobalTheory.Fam.FamInhab.cxp_iff P t F.1).1 hF).2 ⟨_, hκH⟩ κ' hκ' x
  have hF2 : ∀ h, F.1 x (h * κ') =
      levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * F.1 x h := fun h =>
    eq_mul_of_inv_mul hsT (hF1 h)
  have hpt' : R.ωX t (κ, κ') (R.ptX t φ) = (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.ptX t φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ D.sp.X') (R.νX t)
    (R.fdX t) hfd.2 κ' hmap
    (fun h => thetaKO (R.ωX t) (g * κ) h (R.ptX t φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D (D.R.m - 1))).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, hFv γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO (R.ωX t) (g * κ) (h * κ') (R.ptX t φ) * F.1 x (h * κ') =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ))) * (thetaKO (R.ωX t) g h (R.ptX t φ) * F.1 x h) := fun h => by
    exact mul_eq_of (hth g h) (hF2 h)
  refine (hio.eq F φ x (g * κ)).symm.trans (hint.2.symm.trans ?_)
  refine (congrArg (fun f => ∫ h in R.fdX t, f h ∂(R.νX t)) (funext hpw)).trans ((integral_const_mul _ _).trans ?_)
  refine (const_eq hsT).trans ?_
  exact congrArg₂ (· * ·) e1.symm (hio.eq F φ x g)

end GlobalTheory.StepLevelP

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvStep

variable {D : D7}

theorem diag_inv {ρ : ℕ} (t : GL (Fin ρ) (AE D)) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    t.1 = diagonal (fun k => t.1 k k) ∧ (t⁻¹).1 = diagonal (fun k => (t⁻¹).1 k k) ∧
      ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := by
  have h1 : t.1 = diagonal (fun k => t.1 k k) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · rw [diagonal_apply_ne _ h, ht a b h]
  have hm : t.1 * (t⁻¹).1 = 1 := t.mul_inv
  have h3 : ∀ a b, t.1 a a * (t⁻¹).1 a b = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) a b := by
    intro a b
    have := congrFun (congrFun hm a) b
    rw [h1, diagonal_mul] at this
    exact this
  have h4 : ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := fun k => by
    have := h3 k k; rwa [one_apply_eq] at this
  refine ⟨h1, ?_, h4⟩
  ext a b
  by_cases h : a = b
  · subst h; simp
  · rw [diagonal_apply_ne _ h]
    have e := h3 a b
    rw [one_apply_ne h] at e
    calc (t⁻¹).1 a b = (t⁻¹).1 a a * (t.1 a a * (t⁻¹).1 a b) := by
          rw [← mul_assoc, mul_comm ((t⁻¹).1 a a), h4, one_mul]
      _ = 0 := by rw [e, mul_zero]

theorem mat_mem_idAt {P : Pl D → Prop} {m n k l : ℕ} (A : Mx D m n) (M : Mx D n k) (B : Mx D k l)
    (hM : ∀ a b, M a b ∈ idAt D P) (i : Fin m) (j : Fin l) : (A ⬝ M ⬝ B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hM a b)

theorem levi_sub_one_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {t : GL (Fin ρ) (AE D)}
    (ht : d.levi t ∈ grpAt S P) (i j : Fin ρ) : t.1 i j - (1 : Mx D ρ ρ) i j ∈ idAt D P := by
  have hm : ∀ a b, (mt S (d.levi t) - 1) a b ∈ idAt D P := by
    intro a b
    have h := (MonoidHom.mem_ker).1 ht
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idAt D P) => u.1 a b) h
    simp only [Units.val_one] at h2
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have e1 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idAt D P))).comp (matHom S) (d.levi t)).1 =
      (mt S (d.levi t)).map (Ideal.Quotient.mk (idAt D P)) := rfl
    rw [e1, Matrix.map_apply] at h2
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e : t.1 - 1 = d.pX ⬝ (mt S (d.levi t) - 1) ⬝ d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d.pX_jX, Matrix.mul_assoc, ← blockX, blockX_levi]
  rw [← Matrix.sub_apply, e]
  exact mat_mem_idAt _ _ _ hm i j

theorem symplO_extX_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

theorem trace_single_mul {ρ : ℕ} (i : Fin ρ) (β : AE D) (M : Mx D ρ ρ) :
    (Matrix.single i i β ⬝ M).trace = β * M i i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem adj_single {ρ : ℕ} (i : Fin ρ) (β : AE D) : adj (Matrix.single i i β) = Matrix.single i i (cA D β) := by
  ext a b
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨h1.2, h1.1⟩ h2 | exact absurd ⟨h2.2, h2.1⟩ h1 | exact map_zero _



theorem vac_fix_Y : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (LS : Lat S) (LT : Lat T) (v : Pl D), Tame D v → ∀ f, Vac ψ S T LS LT (· = v) f → ∀ y : Mx D T.rank ρ, d.extY T y ∈ latO S T (LS : Set _) (LT : Set _) (· = v) → heisO ψ S T (d.extY T y) f = f := by
  intro D ψ S S₀ T ρ d LS LT v hT f hf y hy
  have hsm : ∀ (c : AE D) (z : Mx D T.rank ρ), c • d.extY T z = d.extY T (c • z) := by
    intro c z
    rw [HypDec.extY_apply, HypDec.extY_apply, Matrix.smul_mul]
  have hadd : ∀ y₁ y₂ : Mx D T.rank ρ, heisO ψ S T (d.extY T (y₁ + y₂)) f =
      heisO ψ S T (d.extY T y₁) (heisO ψ S T (d.extY T y₂) f) := by
    intro y₁ y₂
    funext w
    simp only [heisO, map_add (f := _)]
    rw [GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.symplOH_extY_extY, add_zero, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul, add_assoc]
    ring
  rcases hT.2 with h2 | ⟨e, ε, he, hε, hb⟩
  · have hε : IsPlaceIdem D v (GlobalTheory.SplitIdem.placeHom D.host.F v 1) :=
      ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _,
        fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
    obtain ⟨a, ha, ha2⟩ : ∃ a : AE D, finPart D a ∈ intAE D ∧
        2 * a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v 1) := by
      obtain ⟨yv, hyv⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
      rw [map_ofNat] at hyv
      have hy' : (2 : Fv D.host.F v) * yv = 1 := congrArg Subtype.val hyv
      refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v yv), ?_, ?_⟩
      · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v yv, 1, rfl⟩
      · rw [two_mul, ← map_add (f := _), ← map_add (f := _), ← two_mul, hy']
    have h1 : 2 • (a • d.extY T y) = d.extY T y := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have h3 := hf.2.1 (a • d.extY T y) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha _ hy)
    rwa [h1] at h3
  · have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
    have hint : ∀ c : AE D, c * c = c → finPart D c ∈ intAE D := fun c hc =>
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc])
    have hu : d.extY T y = d.extY T (e • y) + d.extY T (cA D e • y) := by
      rw [← hsm, ← hsm, ← add_smul, hb, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have f1 : heisO ψ S T (d.extY T (e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e (hint e he.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
    have f2 : heisO ψ S T (d.extY T (cA D e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 _ he' _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (hint _ he'.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he'.1])
    rw [hu, ← map_add (f := _), hadd, f2, f1]

end GlobalTheory.FinPl.InvStep

namespace GlobalTheory.FinPl.InvStep



theorem inv_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 hF f hf t htd ht hne i
  obtain ⟨-, h2, -⟩ := diag_inv t htd
  have hc1 : (t⁻¹).1 i i - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) i i
    rwa [one_apply_eq] at this
  refine GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ B.d J.d LV LV₀ LW LW₀ v hG.tame hG.sdV hG.sdW hG.monoV
    hG.monoW hG.cols i _ hc1 ?_
  intro b hb hY
  have hfix := vac_fix_Y D ψ B.V B.V₀ J.W ρ B.d LV LW v hG.tame f hf _ hY
  have hθ : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hf.1
  have hg : heisO ψ B.V J.W (actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)))
      (s.om (1, J.d.levi t) f) = s.om (1, J.d.levi t) f := by
    rw [← s.weil.om_heis 1 (J.d.levi t) _ f hf.1, hfix]
  have hact : actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)) =
      B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extY_apply, HypDec.extY_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, HypDec.levi_jY, Matrix.mul_assoc J.d.jY]
  have hS : ∀ a c, Matrix.single i i b a c ∈ idAt D (· = v) := by
    intro a c
    rw [Matrix.single_apply]
    split_ifs
    · exact hb
    · exact zero_mem _
  have hMx : MxAt (· = v) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro a c
    have := mat_mem_idAt (J.d.jY ⬝ adj (t⁻¹).1) (Matrix.single i i b) 1 hS a c
    rwa [Matrix.mul_one, Matrix.mul_assoc] at this
  have hpair : ∀ U : Mx D ρ ρ, pairS J.W (J.d.jX ⬝ U) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) =
      cA D b * ((t⁻¹).1 i i * U i i) := by
    intro U
    rw [pairS, adj_mul, adj_mul, adj_adj, adj_single, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY), HypDec.gram_YX, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc, trace_single_mul]
    congr 1
    conv_lhs => rw [h2]
    rw [diagonal_mul]
  have hUI : UInv J.W (xZero J.d) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro u
    have h1 : u.1.1 i i = 1 := ((mem_UX.1 u.2) i i).2
    have e := hpair 1
    rw [Matrix.mul_one] at e
    rw [xZero, hpair, e, h1, one_apply_eq]
  have hd := hF.Heisenberg₂.dual _ hθ _ hMx hUI
  rw [hact] at hg
  rw [hg] at hd
  have hψ : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d))
      (B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)))) = 1 := by
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hd w
    simp only [Pi.smul_apply, smul_eq_mul] at h1 hw
    exact mul_right_cancel₀ hw (h1.symm.trans (one_mul _).symm)
  rw [← hψ, symplO_extX_extY, symplO_extX_extY]
  congr 3
  have e := hpair 1
  rw [Matrix.mul_one, one_apply_eq, mul_one] at e
  rw [xZero, e, pairS, adj_mul, adj_single, Matrix.mul_assoc, ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY),
    HypDec.gram_YX, Matrix.one_mul, trace_single_mul, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

end GlobalTheory.FinPl.InvStep
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SmallAllPf

variable {D : D7}

theorem vac_at_place {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}
    {f : WO S T → ℂ} (h : Vac ψ S T LS LT P f) {v : Pl D} (hv : P v) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨α, hα, hP, rest⟩
    exact ⟨α, hα, fun w hw => hP w fun e => hw (e ▸ hv), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem main : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ q χ hχ
  have hSO := GlobalTheory.T.smallPair_pairing_at_one_gluedPlace D
  have hOB := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have hAB := GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D
  choose r e hr hval using fun i => hSO k (p i) n n' q (χ i) (hχ i)
  refine ⟨r, e, hr, ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT hunr vA vS vT a b s L₁ L₂ L₃ hL₁ hL₂ hL₃ hloc
    Ξ Ξ' Φ₂ hΞ hΦ₂ hO φ hφ F hF
  have hstd : IsStdChar D ψ (-1) := hom₁.std
  have hinj : Function.Injective fun i => (p i).v := hP.inj
  have hPi : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  set c : ι → ℂ := fun i => (r i : ℂ) * chrPow χW ((p i).idele q.unit) (e i) with hc
  set Ψ : ι → Matrix n (n' ⊕ Fin 1) k → ℂ :=
    fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (s i • b.Q i)) with hΨ

  have keep : ∀ (l : List ι) (f f' : WO V₀ S → ℂ),
      OverAll ψ a.α₀ b.β L₁ L₂ Ψ l f f' → ∀ i, i ∉ l → Vac ψ V₀ S L₁ L₂ (· = (p i).v) f →
        Vac ψ V₀ S L₁ L₂ (· = (p i).v) f' := by
    intro l
    induction l with
    | nil =>
      intro f f' h i _ hv
      have h' : f' = f := h
      rw [h']
      exact hv
    | cons j l ih =>
      intro f f' h i hi hv
      obtain ⟨g, hg, hOj⟩ := h
      have hgv := ih f g hg i (fun hm => hi (List.mem_cons_of_mem j hm)) hv
      have hij : i ≠ j := fun e => hi (e ▸ List.mem_cons_self)
      exact ((hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hOj.2.2.1).2.1 _ _
        hOj).2 L₁ L₂ _ (fun e => hij (hinj e).symm) hgv
  have val : ∀ l : List ι, l.Nodup → ∀ (Ξ₀ Ξ₁ : WO V₀ S → ℂ),
      (∀ i, Vac ψ V₀ S L₁ L₂ (· = (p i).v) Ξ₀) → OverAll ψ a.α₀ b.β L₁ L₂ Ψ l Ξ₀ Ξ₁ →
      ∀ φ, a.Ram φ → smallPair o om₁ omT vA vS vT φ Ξ₀ Φ₂ F =
        (l.map c).prod * smallPair o om₁ omT vA vS vT (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) Ξ₁ Φ₂ F := by
    intro l
    induction l with
    | nil =>
      intro _ Ξ₀ Ξ₁ _ h φ _
      have h' : Ξ₁ = Ξ₀ := h
      subst h'
      simp [PairDat.sAll]
    | cons j l ih =>
      intro hnd Ξ₀ Ξ₁ h1 h φ hφ
      obtain ⟨g, hg, hOj⟩ := h
      have hj : j ∉ l := (List.nodup_cons.1 hnd).1
      have hgv := keep l Ξ₀ g hg j hj (h1 j)
      rw [ih hnd.tail Ξ₀ g h1 hg φ hφ]
      have hR : a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) :=
        (hAB k ι p q χ hχ s n' A V₀ a hinj l).1.mapsTo hφ
      have hself := (hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hgv).2.2
        (hP.unit j) _ _ (hloc j).2.1 (hloc j).2.2
      obtain ⟨u1, u2, u3, u4⟩ := hunr _ (hPi j)
      have key := hval j ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT u1 u2 u3 u4 vA vS vT
        (a.α j) (a.α₀ j) (b.β j) (hloc j).1 (a.P j) (b.Q j) (s j) L₁ L₂ L₂ L₃ g g Ξ₁ Φ₂ hself hOj hL₂ hL₃
        (hloc j).2.2 (vac_at_place hΦ₂ (hPi j)) _ (hR.2 j) F hF
      have hcons : a.sAll q (fun i => resChar (χ i) (hχ i) q) s (j :: l) φ =
          sOp (a.α j) (a.P j) q (resChar (χ j) (hχ j) q) (s j)
            (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) := rfl
      rw [key, hcons, List.map_cons, List.prod_cons, hc]
      ring
  exact val I hP.nodup Ξ Ξ' (fun i => vac_at_place hΞ (hPi i)) hO φ hφ

end GlobalTheory.FinPl.SmallAllPf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

theorem _root_.GlobalTheory.T.jointHarmonics_lowest_KType_coefficient_real : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W), l2 μ 𝓧 (ω (1, realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w))) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) = Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ * l2 μ 𝓧 f f := by
  first | exact @GlobalTheory.FockCoefReal.fock_coef_real | exact GlobalTheory.FockCoefReal.fock_coef_real | (intros; apply GlobalTheory.FockCoefReal.fock_coef_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistChainLevelProductOverPlaces_compact_open : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ IsCompact (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) ∧ IsOpen (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q))) := by
  first | exact @GlobalTheory.QFinGrp.qK_grp | exact GlobalTheory.QFinGrp.qK_grp | (intros; apply GlobalTheory.QFinGrp.qK_grp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselPeriodCharacter_primitive_normalFrames : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.PrimAt ψ ((y.bes j ρ h).lev (a.x j).vol).d (N j) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.PrimNormal.prim_of_normal | exact GlobalTheory.PrimNormal.prim_of_normal | (intros; apply GlobalTheory.PrimNormal.prim_of_normal <;> assumption)
end
