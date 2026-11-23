module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeH
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.ShFam.BdArc

open GlobalTheory.HolHom GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections LatSec

theorem exists_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), IsArc Z σ φ x ψ r → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ h : ℂ → (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), ∀ u ∈ Metric.ball (0 : ℂ) ρ, (h u).IsInvertible ∧ ContinuousAt (fun u => (h u).inverse) u ∧ ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = e' u (h u z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  have hA : ∀ u ∈ Metric.ball (0 : ℂ) ρ, HolAt (fun z => (e' u z).left) 0 := fun u hu =>
    holAt_of_isHolTo (hexp u hu).2.2.1 trivial
  have hh : ∀ u, ∃ h : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), u ∈ Metric.ball (0 : ℂ) ρ → h.IsInvertible ∧
      ∀ j, IsDerivAt (fun z => (e' u z).left) 0 (h (Pi.single j 1))
        (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2) := fun u => by
    by_cases hu : u ∈ Metric.ball (0 : ℂ) ρ
    · obtain ⟨D, hD⟩ := exists_lieEquiv Z.t (hexp u hu).1 (hA u hu) (hexp u hu).2.2.2.2
      have ex : ∃ f : EigFrame Z ((ψ u).comp φ) (spMap (ψ u) ≫ (x ≫ genι Z)), ∀ τ i, f.v τ i = spMap (dualMap (ψ u)) ≫ fr.v τ i := by
        open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
        have h : GlobalTheory.LocM.IsFrame Z.t ((ψ u).comp φ) (spMap (ψ u) ≫ (x ≫ genι Z)) ((fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i)) := by
          letI : Algebra c.F A := φ.toAlgebra
          letI : Algebra c.F ℂ := ((ψ u).comp φ).toAlgebra
          let v : ∀ τ, Fin (Dw.mult τ) → TanM (x ≫ genι Z) Z.t.G := fun τ i => tanOf (fr.tan τ i)
          have eps_dual (a : A) : spMap (dualMap (ψ u)) ≫ spMap (epsMul a) = spMap (epsMul ((ψ u) a)) ≫ spMap (dualMap (ψ u)) := by
            rw [spMap_comp_spMap, spMap_comp_spMap]
            congr 1
            refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]
          have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
              spMap (epsMul (((ψ u).comp φ) (embK c τ a))) ≫ (fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i) τ i := fun τ i a => by
            show (spMap (dualMap (ψ u)) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (dualMap (ψ u)) ≫ fr.v τ i
            rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
          have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
            exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
          have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM (ψ u) (v k.1 k.2) := by
            have h := full_equiv (eB Dw).symm (full_bc (ψ u) (full_equiv (eB Dw) h1))
            exact (funext fun k => congrArg (fun j : IxB Dw => resM (ψ u) (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
          refine ⟨fun τ i => ⟨isTan_map (ψ u) rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
          have h3 := eig_of_full c (fun τ i => resM (ψ u) (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
            ((eig_iff c τ _).1 hwe)
          exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM (ψ u) (v τ i)) a (tanOf hw)).2 h3
        exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
      let f := Classical.choose ex
      have hf := Classical.choose_spec ex
      obtain ⟨b, hb⟩ := exists_basis f
      refine ⟨((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv, fun _ => ⟨⟨_, rfl⟩, fun j => ?_⟩⟩
      have h1 := hD (D.symm (f.vec (e j).1 (e j).2))
      rw [D.apply_symm_apply] at h1
      have h2 : ((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv (Pi.single j 1) =
          D.symm (f.vec (e j).1 (e j).2) := by simp [hb, Pi.single_apply]
      rw [← hf, ContinuousLinearEquiv.coe_coe, h2]
      exact h1
    · exact ⟨0, fun h => absurd h hu⟩
  choose h hh using hh
  refine ⟨h, fun u hu => ⟨(hh u hu).1, ?_, fun ex hadd hex hd z => ?_⟩⟩
  · refine ((hh u hu).1.contDiffAt_map_inverse (n := 1)).continuousAt.comp (continuousAt_clm_apply.2 fun z => ?_)
    have : ∀ u, h u z = ∑ j, z j • h u (Pi.single j 1) := fun u => by

      simp only [← map_smul, ← map_sum]
      exact congrArg _ (pi_eq_sum_univ' z)
    simp only [this]
    refine tendsto_finsetSum _ fun j _ => ContinuousAt.const_smul ?_ (z j)
    exact continuousAt_dir (e := e') (w := fun b => h b (Pi.single j 1))
      (v := fun b => spMap (dualMap (ψ b)) ≫ fr.v (e j).1 (e j).2) hol hu (hexp u hu).2.2.2.2 (fun b hb => (hh b hb).2 j) (continuousAt_snd (fun a =>
      ((harc.1.2 a).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρr hu))).continuousAt) _)
  · obtain ⟨hu1, -, hu2, -, hu3⟩ := hexp u hu
    obtain ⟨k, hk, -⟩ := existsUnique_linear hadd hu1 hex hu2 hu3
    have hkh : k = (h u).toLinearMap := (Pi.basisFun ℂ (Fin g)).ext fun i => by
      have h1 := (isDerivAt0_iff _ _ _).1 (hd i)
      simp only [hk] at h1
      have h2 := (isDerivAt_comp_iff (hA u hu) (LinearMap.toContinuousLinearMap k) _ _).1 h1
      rw [Pi.basisFun_apply]
      exact (hu3 (Over.homMk _ h2.over) h2.1).unique ((isDerivAt0_iff _ _ _).2 h2)
        ((isDerivAt0_iff _ _ _).2 ((hh u hu).2 i))
    rw [hk, hkh, ContinuousLinearMap.coe_coe]

end GlobalTheory.ShFam.BdArc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def sharpPair (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (a b : Fin 8) : D.P.A.left ⟶ (G2 Q.B).left :=
  (lift (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr a))
    (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr b))).left

theorem sharp_cls_pair (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (a b : Fin 8) :
    (∏ I : ULift.{0} (Finset (Fin 2)), GlobalTheory.PrimNorm.cls Q.M.L (sharpPair ρ Q D pr a b ≫ (psum Q.B (x2 Q.B) I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card))) ^ W a b =
      ∏ k : Fin 4, GlobalTheory.PrimNorm.cls Q.M.L (lamPts (pr a) (pr b) k ≫ pullback.fst Q.B.hom (spMap ρ)) ^
        (-(W a b * negε k)) := by
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  set xa := pushPt h.1.w (pr a) with hxa
  set xb := pushPt h.1.w (pr b) with hxb
  have e := GlobalTheory.PrimNorm.prod_square (lift xa xb) (fst Q.B Q.B) (snd Q.B Q.B) (GlobalTheory.PrimNorm.cls Q.M.L)
  rw [lift_fst, lift_snd] at e
  have e' : sharpPair ρ Q D pr a b = (lift xa xb).left := rfl
  rw [e', show x2 Q.B = ![fst Q.B Q.B, snd Q.B Q.B] from rfl, e]
  have m : (pr a * pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = (xa * xb).left :=
    (h.2 D.P.A (pr a) (pr b) xa xb rfl rfl).symm
  have o : (1 : D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B).left ≫ pullback.fst Q.B.hom (spMap ρ) =
      (1 : Over.mk (D.P.A.hom ≫ spMap ρ) ⟶ Q.B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h D.P.A))
  rw [Fin.prod_univ_four]
  simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, m, o]
  change GlobalTheory.PrimNorm.diff₂ _ xa xb ^ W a b = _
  simp only [GlobalTheory.PrimNorm.diff₂]
  have ha : (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = xa.left := rfl
  have hb : (pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = xb.left := rfl
  rw [ha, hb]
  simp only [mul_neg, neg_neg, zpow_neg, mul_zpow, inv_zpow]
  ac_rfl

theorem sharp_bundle {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : w.IsGen) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (hM₀ : M₀.IsLB)
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)) (hw₀ : w₀.IsGen) :
    LBIso D.P.L (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
      (fun p => W p.1 p.2)) := by
  have hL : Q.M.L.IsLB := Q.M.isLB
  have hLam : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hLam₀ : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  have hS : (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))).IsLB := DVR.linComb_isLB _ hL _ _
  have h₂ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))) := by
    refine GlobalTheory.PrimNorm.lbIso_nested hL _ _ _ _ _ _ ?_
    refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
    exact Finset.prod_congr rfl fun p _ => sharp_cls_pair W ρ Q D pr p.1 p.2
  have h₃ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb ⟨w₀, hw₀⟩ _ _
  have h₄ : LBIso (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2))
      (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
        (fun p => W p.1 p.2)) :=
    LBIso.chartPull (chartPullLinComb (abelian₂ B₀ M₀) β₂ _ _ _ (𝟙 _) fun p => (Category.id_comp _).symm)
      (chartPullId _) ((GlobalTheory.PrimNorm.lbIso_iff hLam₀ _ _ _ _).2 rfl)
  have hN₁ := DVR.linComb_isLB (abelian₂ Q.B Q.M.L) hLam (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₂ := DVR.linComb_isLB _ (pull_isLB hLam₀ β₂) (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₃ := DVR.linComb_isLB (abelian₂ B₀ M₀) hLam₀ (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
    (fun p => W p.1 p.2)
  exact LBIso.trans D.P.isLB hS hN₃ ⟨w, hw⟩
    (LBIso.trans hS hN₁ hN₃ h₂.symm (LBIso.trans hN₁ hN₂ hN₃ h₃ h₄))

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsDomain R]

abbrev SecF (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) : Type :=
  GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) F) A.A).left
    (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (N : ℤ)))

def baseEm {F : Type} [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) :
    TFK (R := R) F ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom em.toRingHom)) (by
    show Spec.map (CommRingCat.ofHom em.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact em.commutes r)

def famExt (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ) :
    Fam D (Kb R) N →ₛₗ[em.toRingHom] Fam D F N :=
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  GlobalTheory.FieldBaseChange.famPull D (Kb R) F GlobalTheory.allSixLaws.1.globalFns N

def secExt (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) (N : ℕ) : SecF A (Kb R) N →ₛₗ[em.toRingHom] SecF A F N :=
  GlobalTheory.FieldBaseChange.pullOver A.L (fun _ => (N : ℤ))
    (p := (baseEm em ▷ A.A).left)
    (congrArg (fun q => q.left) (whiskerRight_fst (baseEm em) A.A))
    (fun _ => (congrArg (fun q => q.left) (whiskerRight_snd (baseEm em) A.A)).symm)

end GlobalTheory.Mum.Desc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorusExt

open GlobalTheory.BXOf ReciprocityTheory.ChartRestriction.G.DVR

theorem gtExt_eq_self_of_charVal_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  intro R _ _ D F _ _ σ hσ g hb J hJ hfix
  have hb' : extMap σ hσ ≫ g.b = g.b := Over.OverMorphism.ext hb
  have hφ0 : ∀ χ k, Spec.map (CommRingCat.ofHom σ) ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k := by
    intro χ k
    show (extMap σ hσ).left ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k
    fin_cases k
    · show (extMap σ hσ ≫ (cP D _ χ * g.b)).left = (cP D _ χ * g.b).left
      rw [MonObj.comp_mul, comp_cP, hb']
    · show (extMap σ hσ ≫ cP D _ χ).left = (cP D _ χ).left
      rw [comp_cP]
    · show (extMap σ hσ ≫ g.b).left = g.b.left
      rw [hb']
    · show (extMap σ hσ ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
      rw [MonObj.comp_one]
  refine gt_ext_val ((gtExt_b σ hσ g).trans hb') fun χ y J' hJ' => ?_
  obtain rfl : y = closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hdel : ∀ ψ : Spec (CommRingCat.of F) ⟶ D.P.A.left, Spec.map (CommRingCat.ofHom σ) ≫ ψ = ψ →
      GlobalTheory.BXOf.del D.P.L σ J J' ψ = GlobalTheory.BXOf.del D.P.L (RingHom.id F) J J' ψ := by
    intro ψ h
    unfold GlobalTheory.BXOf.del
    rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have e₁ := val_nat (g.isGen χ) σ hJ hJ' (𝟙 _)
  have e₂ := val_nat (g.isGen χ) (RingHom.id F) hJ hJ' (𝟙 _)
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at e₂
  have hu : Units.map σ.toMonoidHom (sig F (charVal g χ (closedPoint F) J)) = sig F (charVal g χ (closedPoint F) J) :=
    Units.ext (hfix χ)
  have hu' : Units.map (RingHom.id F).toMonoidHom (sig F (charVal g χ (closedPoint F) J)) =
      sig F (charVal g χ (closedPoint F) J) := Units.ext rfl
  have key : sig F (charVal (gtExt D σ hσ g) χ (closedPoint F) J') = sig F (charVal g χ (closedPoint F) J') := by
    rw [gtExt_val σ hσ g χ hJ', extMap_left, ← Category.comp_id (spMap σ)]
    refine e₁.trans (Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ DegPre.gtε k)
      (hdel _ ((congrArg _ (Category.id_comp _)).trans ((hφ0 χ k).trans (Category.id_comp _).symm))))
      (hu.trans hu'.symm)) e₂.symm)
  exact Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of F)).hom.hom.toMonoidHom)
    (stalkClosedPointIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective key

end GlobalTheory.TorusExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramCharPow

open GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

theorem charVal_pow_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → (∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F)) → ∀ (k : ℕ) (p : QkPt D F k) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = p.g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal p.g χ (closedPoint F) J) : F) ^ k = ((u : T) : F) := by
  intro R _ _ D hB F _ _ T _ φ₁ hφ J₀ h₀ J hJ eJ hψ k p b hb hbA χ
  let H : Subgroup Fˣ := (Units.map T.subtype.toMonoidHom).range
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ ⧸ H :=
    (QuotientGroup.mk' H).comp (sig F)
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hb' : ρ ≫ b' = p.g.b := Over.OverMorphism.ext hb
  have mem : ∀ s : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ,
      (∃ u : Tˣ, (sig F s : F) = ((u : T) : F)) → w s = 1 := fun s ⟨u, hu⟩ => by
    show (QuotientGroup.mk' H) (sig F s) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨u, Units.ext hu.symm⟩
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    exact mem _ (val_integral T.subtype h₀ eJ t r)
  have e₁ := w_nsmul ρ hJ w hw p.g b' hb' χ k
  obtain ⟨g, hg, hi⟩ := p.eq
  have hp : k • p.g = g := ((isNsmul_iff_eq _ _ _).1 hg).symm
  have hv : charVal g χ (closedPoint F) J = tauVal D F p.y χ (closedPoint F) J :=
    ((isIota_iff _ _).1 hi).2 χ (closedPoint F) J hJ
  rw [hp, hv, w_tau ρ hJ w hw, mem _ (hψ _), mem _ (hψ _), mem _ (hψ _)] at e₁
  simp only [inv_one, _root_.mul_one] at e₁
  have e₂ : (QuotientGroup.mk' H) (sig F (charVal p.g χ (closedPoint F) J) ^ k) = 1 := by
    rw [map_pow]; exact e₁.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at e₂
  obtain ⟨u, hu⟩ := e₂
  exact ⟨u, by rw [← Units.val_pow_eq_pow_val, ← hu]; rfl⟩

end GlobalTheory.UnramCharPow
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CharValsFixed

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  intro R _ _ D F _ _ T _ φ₁ hφ₁ J₀ h₀ J hJ eJ σ hσ g b hb hbA S hS hSfix
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ₁)
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ :=
    (Units.map σ.toMonoidHom).comp (sig F) * (sig F)⁻¹
  have hwv : ∀ u, ((w u : Fˣ) : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) := fun u => rfl
  have hw1 : ∀ u, w u = 1 ↔ σ (sig F u : F) = (sig F u : F) := fun u => by
    constructor
    · intro h
      have e := congrArg Units.val h
      rw [hwv, Units.val_one] at e
      calc σ (sig F u : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) * (sig F u : F) := by
            rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]
        _ = (sig F u : F) := by rw [e, _root_.one_mul]
    · intro h
      apply Units.ext
      rw [hwv, h, Units.mul_inv, Units.val_one]
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    obtain ⟨u, hu⟩ := val_integral T.subtype h₀ eJ t r
    refine (hw1 _).2 ?_
    have hu' : (sig F (val t (ρ.left ≫ r) (closedPoint F) J) : F) = T.subtype u := hu
    rw [hu']
    exact hσ _ (u : T).2
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hgb : g.b = ρ ≫ b' := by
    ext1
    exact hb.symm
  have hth : ∀ χ χ', w (th D (closedPoint F) J (cP D _ χ) (cP D _ χ') g.b) = 1 := fun χ χ' => by
    rw [hgb, ← comp_cP D ρ χ, ← comp_cP D ρ χ']
    exact w_th ρ w hw _ _ _
  let H : AddSubgroup D.X :=
    { carrier := {χ | w (charVal g χ (closedPoint F) J) = 1}
      zero_mem' := by
        show w _ = 1
        rw [charVal_zero g hJ, map_one]
      add_mem' := fun {χ χ'} (h : w _ = 1) (h' : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ χ')
        rw [map_mul, map_mul, hth, h, h', _root_.mul_one, _root_.mul_one] at e
        exact e
      neg_mem' := fun {χ} (h : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ (-χ))
        rw [map_mul, map_mul, hth, h, _root_.mul_one, _root_.one_mul, add_neg_cancel, charVal_zero g hJ,
          map_one] at e
        exact e.symm }
  have hSH : S ⊆ H := fun χ hχ => (hw1 _).2 (hSfix χ hχ)
  have hH : H = ⊤ := eq_top_iff.2 (hS ▸ (AddSubgroup.closure_le H).2 hSH)
  intro χ
  exact (hw1 _).1 (show χ ∈ H by rw [hH]; trivial)

end GlobalTheory.CharValsFixed
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  first | exact @GlobalTheory.PlaneComplement.plane_split_complement | exact GlobalTheory.PlaneComplement.plane_split_complement | (intros; apply GlobalTheory.PlaneComplement.plane_split_complement <;> assumption)
end
