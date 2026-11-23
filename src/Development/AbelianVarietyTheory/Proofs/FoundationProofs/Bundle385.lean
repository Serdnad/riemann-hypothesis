module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalHeightFrobeniusPlace
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle079
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle384
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

theorem _root_.GlobalTheory.T.graph_element_iwasawa_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v, ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v, ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  first | exact @GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin | exact GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin | (intros; apply GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

theorem _root_.GlobalTheory.T.unramified_away_from_l_of_twisted_shapiro_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → y ∈ Z1 (Loc.colRep W) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → Unr W y := by
  first | exact @GlobalTheory.KA.unr_of_twisted_limit | exact GlobalTheory.KA.unr_of_twisted_limit | (intros; apply GlobalTheory.KA.unr_of_twisted_limit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.tateDual_cocycle_coboundary_of_vanish_on_fixing : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∀ g ∈ N0g W, z g = 0) → z ∈ ReciprocityTheory.Gal.B1 (Loc.colRep (dual1 W)) := by
  first | exact @GlobalTheory.Ord2.h1dual_of_vanish_fix | exact GlobalTheory.Ord2.h1dual_of_vanish_fix | (intros; apply GlobalTheory.Ord2.h1dual_of_vanish_fix <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.local_height_frobenius_place : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω), 1 ≤ n → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B w → l ^ n ∣ normV w - 1 → IsFrob B (normV w) τ → τ ∈ Dec (F := ℚ) B → dt W τ = 1 → Ine (F := ℚ) B ≤ W.ker → IsLocallyConstant ψ → (∃ t ∈ Ine (F := ℚ) B, (ψ t).toAdd = 1) → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ Ine (F := ℚ) B, y a = 0 ∧ z a = 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ Ine (F := ℚ) B, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Cob2 c n (Dec (F := ℚ) B) (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) → Cg n (P * ht W y z u τ) 0 := by
  first | exact @GlobalTheory.Ord2.LocW.local_height_at_frobenius | exact GlobalTheory.Ord2.LocW.local_height_at_frobenius | (intros; apply GlobalTheory.Ord2.LocW.local_height_at_frobenius <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt
  Formalism.L2.Pj.CompSplitPfB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_of_frMap_test {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {p : TRing c.F} {S : Type}
    [CommRing S] [Algebra c.F S] {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R} {z : FrPt Xo c S} (h : FrMap φ y z) :
    evR Xo c f z = φ (f p y) := by
  have ht : Tested z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left ht]
  exact GlobalTheory.TransferCompare.evalWD_framed Xo c f hf S _ p _ φ _ y z ht.choose_spec.choose_spec.choose_spec h

theorem idem_notMem_iff (Z : Comp Xo c) {p : TRing c.F} (y : FrPt Xo c p.R) (q : PrimeSpectrum p.R) :
    idem Z p y ∉ q.asIdeal ↔ ptF y q ∈ (Z : Set (Xo.XF c)) :=
  cspB_idem_spec _ (cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over q

theorem liesOff_of_map_idem {Z : Comp Xo c} {p : TRing c.F} {S : Type} [CommRing S] [Algebra c.F S]
    {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R} {z : FrPt Xo c S} (h : FrMap φ y z) (h0 : φ (idem Z p y) = 0) :
    LiesOff Z z := fun q hq => by
  have hC := cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z
  have h1 : cspB_idem _ hC z.x z.x_over = 0 := (cspB_idem_map _ hC φ y.x_over z.x_over h.1).symm.trans h0
  exact (cspB_idem_spec _ hC z.x z.x_over q).2 hq (h1 ▸ q.asIdeal.zero_mem)

theorem mem_suppOn_iff_idem_mul_of_natural {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (Z : Comp Xo c) :
    f ∈ suppOn Z ↔ idem Z * f = f := by
  refine ⟨fun h => funext fun p => funext fun y => ?_, fun h => ?_⟩
  · obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _
      (Ideal.Quotient.mkₐ c.F (Ideal.span {idem Z p y})) y
    have h0 := h _ z (liesOff_of_map_idem hz (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)))
    rw [evR_of_frMap_test hf hz] at h0
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : idem Z p y * idem Z p y = idem Z p y := congrFun (congrFun (idem_mul_idem Z) p) y
    show idem Z p y * f p y = f p y
    rw [← ha, mul_left_comm, h1]
  · rw [← h, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem mem_suppOn_iff_idem_mul {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (Z : Comp Xo c) :
    f ∈ suppOn Z ↔ idem Z * f = f := mem_suppOn_iff_idem_mul_of_natural hf.1 Z

theorem idem_mul_eq {e : Ix Dw → ℤ} {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ secZ Xo c e ⊓ suppOn Z) :
    idem Z * f = f := (mem_suppOn_iff_idem_mul hf.1 Z).1 hf.2

theorem idem_mul_mem {e : Ix Dw → ℤ} (Z : Comp Xo c) {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    idem Z * f ∈ secZ Xo c e ⊓ suppOn Z :=
  ⟨zero_add e ▸ mul_mem_secZ (idem_mem_secZ Z) hf, mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z)⟩

theorem eq_zero_of_forall_prime {K : Type} [Field K] {p : TRing K} {a : p.R}
    (h : ∀ q : PrimeSpectrum p.R, a ∈ q.asIdeal) : a = 0 := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  exact (nilpotent_iff_mem_prime.2 fun J hJ => h ⟨J, hJ⟩).eq_zero

theorem idem_mul_idem_of_ne {Z Z' : Comp Xo c} (h : Z ≠ Z') : idem Z * idem Z' = 0 :=
  funext fun p => funext fun y => eq_zero_of_forall_prime fun q => by
    show idem Z p y * idem Z' p y ∈ q.asIdeal
    by_contra hn
    have h1 := not_or.1 (mt q.isPrime.mul_mem_iff_mem_or_mem.2 hn)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) ((idem_notMem_iff Z y q).1 h1.1)
      ((idem_notMem_iff Z' y q).1 h1.2)


variable (Xo c) in
theorem sum_idem [Fintype (Comp Xo c)] : ∑ Z : Comp Xo c, idem Z = 1 := by
  classical
  refine funext fun p => funext fun y => ?_
  rw [Finset.sum_apply, Finset.sum_apply]
  show _ = (1 : p.R)
  refine sub_eq_zero.1 (eq_zero_of_forall_prime fun q => ?_)
  have hall : ptF y q ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
    rw [sUnion_irreducibleComponents]; trivial
  obtain ⟨W, hW, hq⟩ := Set.mem_sUnion.1 hall
  let Z₀ : Comp Xo c := ⟨W, hW⟩
  have h1 : idem Z₀ p y ∉ q.asIdeal := (idem_notMem_iff Z₀ y q).2 hq
  refine (q.isPrime.mem_or_mem (x := idem Z₀ p y) ?_).resolve_left h1
  have h2 : idem Z₀ p y * ∑ Z : Comp Xo c, idem Z p y = idem Z₀ p y := by
    rw [Finset.mul_sum]
    exact (Finset.sum_eq_single Z₀ (fun Z _ h => congrFun (congrFun (idem_mul_idem_of_ne h.symm) p) y)
      (fun h => absurd (Finset.mem_univ _) h)).trans (congrFun (congrFun (idem_mul_idem Z₀) p) y)
  rw [mul_sub, h2, mul_one, sub_self]
  exact q.asIdeal.zero_mem


theorem sum_idem_mul [Fintype (Comp Xo c)] (f : Rul Xo c) : ∑ Z : Comp Xo c, idem Z * f = f := by
  rw [← Finset.sum_mul, sum_idem, one_mul]

namespace ConstSec

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {la : _root_.GlobalTheory.AllWt.Weight Dw}
  {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ)

end ConstSec

end GlobalTheory.FlatLine
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  first | exact @GlobalTheory.ArchFree.coord.coord_conj_le | exact GlobalTheory.ArchFree.coord.coord_conj_le | (intros; apply GlobalTheory.ArchFree.coord.coord_conj_le <;> assumption)
end
