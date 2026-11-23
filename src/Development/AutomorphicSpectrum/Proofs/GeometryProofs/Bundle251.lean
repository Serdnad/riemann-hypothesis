module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeStalkDvrTwistedModels
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeDvrDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle250
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle053
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle046
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle027
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle047
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle028
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle032
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TeichmullerTestFunction
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle249
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle054
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle196
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle226
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle194
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle248
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.CompanionTheory.Relay.full_torsion_twist_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t t' : SAB H X) (m : SABMap o.t t ξ) (m' : SABMap (twistSAB o.t g) t' ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ o.t.G, v.left ≫ m.φ = (M.pt e).left ∧ v.left ≫ m'.φ = (M'.pt e).left) → (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) → M'.htOm t'.PP.L n q = M.htOm t.PP.L n q := by
  first | exact @PositivityTheory.UnitarySelfGeneration.lattice_stalk_dvr_twisted_models | exact PositivityTheory.UnitarySelfGeneration.lattice_stalk_dvr_twisted_models
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem htat_link_of (h758 : type_of% @GlobalTheory.T.HTChartExists_holds) (h576 : type_of% @GlobalTheory.T.hodge_tate_chart_integral) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), ∃ (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc ∧ ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (κ : chartRing o (mseg y) s.1), PointHT → IsCp p (κ : Ω) → (Dc s).HasTestPoints κ := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq o _ _ ho
  obtain ⟨h0, hN, hprop, hT, hrk, -, hch⟩ := Hcptgen.hcpt_generic E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho
  have hp := (Fact.out : p.Prime)
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.ne_zero
  obtain ⟨ev, ζ₀, hev⟩ := exists_isParam D 𝔐.t 𝔐.ξ level_param (p ^ 𝔐.R p) (Nat.pos_of_ne_zero hn) hpq hprop
    (𝔐.tors p hpS) hT
  obtain ⟨u, hu⟩ := pol_lattice E H D p
  obtain ⟨π, e, hπ, he, hdec, hsurj, hker, halt, hadj, hes, hei⟩ :=
    exists_levPairing (cmConj E) p (𝔐.R p) D.EF u hu
  have key : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      ∃ Dc : HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li), Dc.e = e ∧
      (∀ a w, Dc.ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)) ∧
      (∀ w, w ∈ Dc.om ↔ ∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) ∧
      (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q →
        𝔐.M.omLat q = Submodule.span (regAt 𝔐.ξ q) (Dc.om : Set (Module.Dual Ω 𝔐.Li))) ∧
      (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → ∀ z w',
        𝔐.M.IsHTAt 𝔐.t.PP.L (p ^ 𝔐.R p) (ev (∑ k, z k • u k)) q w' ↔
          ∃ v ∈ 𝔐.M.omLat q, w' = Dc.h z + (p ^ 𝔐.R p) • v) ∧
      ∀ κ : chartRing o (mseg y) s.1, PointHT → IsCp p (κ : Ω) → Dc.HasTestPoints κ := by
    intro s
    obtain ⟨_, _, _, x, hx, hr⟩ := hch s.1 s.2
    obtain ⟨Dc, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.CompanionTheory.HtLink.exists_chart Twhopf.sec_inj Twexists.exists_torsion' h758 h576 D 𝔐.t 𝔐.ξ 𝔐.tie.gen 𝔐.all 𝔐.M 𝔐.ρ 𝔐.act
      p (𝔐.R p) hev hprop (𝔐.tors p hpS) hrk u hu π e hπ he hsurj hker halt hadj hes hei (chartRing o (mseg y) s.1) x hx
      (fun q hq => chart_le_regAt 𝔐 p o ho s.1 q ((hr q).1 hq).1 ((hr q).1 hq).2)
    exact ⟨Dc, h1, h2, fun w => (h3 w).trans ⟨fun h q a b => h q ((hr q).2 ⟨a, b⟩),
      fun h q hq => h q ((hr q).1 hq).1 ((hr q).1 hq).2⟩, fun q a b => h4 q ((hr q).2 ⟨a, b⟩),
      fun q a b => h5 q ((hr q).2 ⟨a, b⟩), h6⟩
  choose Dc h1 h2 h3 h4 h5 h6 using key
  refine ⟨Dc, ⟨h2, fun s t => (h1 s).trans (h1 t).symm, h3, h4, fun s q hs hq => ?_, fun s t q hs ht hq z => ?_⟩, h6⟩
  · have hz := ModelTest.overZp_of_inFibre 𝔐 hp q hq
    have hpow : ∀ w : Module.Dual Ω 𝔐.Li, ((p : chartRing o (mseg y) s.1) ^ 𝔐.R p) • w = (p ^ 𝔐.R p) • w := fun w => by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    have hsub := chart_le_regAt 𝔐 p o ho s.1 q hs hz
    have hmem : ∀ z, ∀ v ∈ 𝔐.M.omLat q, (Dc s).h z + (p ^ 𝔐.R p) • v ∈ omP 𝔐 p q := fun z v hv =>
      Submodule.subset_span ⟨_, (hev.onto _).2 ⟨_, rfl⟩, (h5 s q hs hz z _).2 ⟨v, hv, rfl⟩⟩
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨g, hg, hw⟩
      obtain ⟨a, rfl⟩ := (hev.onto g).1 hg
      obtain ⟨z, b, rfl⟩ := hdec a
      rw [hev.add, (hev.ker _).2 ⟨b, rfl⟩, _root_.mul_one] at hw
      obtain ⟨v, hv, rfl⟩ := (h5 s q hs hz z w).1 hw
      refine add_mem (Submodule.subset_span (Submodule.mem_sup_left (Submodule.subset_span ⟨z, rfl⟩))) ?_
      rw [h4 s q hs hz] at hv
      clear hw
      induction hv using Submodule.span_induction with
      | mem v hv => exact Submodule.subset_span (Submodule.mem_sup_right ⟨v, hv, hpow v⟩)
      | zero => simp
      | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
      | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
    · obtain ⟨w₁, hw₁, _, ⟨w₂, hw₂, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
      refine add_mem ?_ ?_
      · clear hw
        induction hw₁ using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨z, rfl⟩ := hv
          simpa using hmem z 0 (zero_mem _)
        | zero => exact zero_mem _
        | add v v' _ _ h h' => exact add_mem h h'
        | smul r v _ h => exact Submodule.smul_mem (omP 𝔐 p q) ⟨_, hsub r⟩ h
      · have := hmem 0 w₂ (((h3 s w₂).1 hw₂) q hs hz)
        rw [map_zero, zero_add, ← hpow] at this
        exact this
  · exact (h5 t q ht hq z _).1 ((h5 s q hs hq z _).2 ⟨0, zero_mem _, by simp⟩)

end GlobalTheory.CompanionTheory.HtLink
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodge_lattice_dvr_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : O) (p : ℕ) (σ : E →+* Ω), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → ξ ≫ s = spMap (algebraMap O Ω) → IsCptGen ξ → PowFns t → S.Gives 𝓗 → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → 𝓗.DegZero σ (algebraMap O Ω ϖ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.germ_degZero | exact GlobalTheory.CompanionTheory.Ar.Flat.germ_degZero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.germ_degZero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] (σ' : MulChar F RC) (ee : Sg → ℕ), (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) → ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)) := by
  first | exact @PositivityTheory.Xgn.teichmuller_test_function | exact PositivityTheory.Xgn.teichmuller_test_function
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  first | exact @PositivityTheory.Xgn.test_order_sections | exact PositivityTheory.Xgn.test_order_sections
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curveSemiAbelianConjecture : CurveSemiAbelianConjecture := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds | exact GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HFlag

section Lemmas

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']

theorem exists_forms_eq {n : ℕ} {b : Fin n → Module.Dual Ω V} (hb : LinearIndependent Ω b) (l : Fin n) :
    ∃ u : V, ∀ k, b k u = if k = l then 1 else 0 := by
  classical
  have hs : Function.Surjective (LinearMap.pi b : V →ₗ[Ω] (Fin n → Ω)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hc : ∑ k, φ (Pi.single k 1) • b k = 0 := by
      ext u
      have h1 := LinearMap.congr_fun hφ u
      have h2 : (LinearMap.pi b : V →ₗ[Ω] (Fin n → Ω)) u = ∑ k, b k u • (Pi.single k 1 : Fin n → Ω) := by
        ext m
        simp [Finset.sum_apply, Pi.single_apply]

      rw [LinearMap.dualMap_apply, h2, map_sum] at h1
      simpa [mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hb _ hc
    refine LinearMap.pi_ext fun k x => ?_
    have : (Pi.single k x : Fin n → Ω) = x • (Pi.single k 1 : Fin n → Ω) := by
      ext m
      simp [Pi.single_apply]
    rw [this, map_smul, h0 k]
    simp
  obtain ⟨u, hu⟩ := hs (Pi.single l 1)
  refine ⟨u, fun k => ?_⟩
  have := congrFun hu k
  simpa [Pi.single_apply] using this

theorem li_of_adjoint {i : Ω →+* Ω'} (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V')
    (h : ∀ w v, jd w (j v) = i (w v)) {n : ℕ} {b : Fin n → Module.Dual Ω V} (hb : LinearIndependent Ω b) :
    LinearIndependent Ω' fun k => jd (b k) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc l => ?_
  obtain ⟨u, hu⟩ := exists_forms_eq hb l
  have h1 := LinearMap.congr_fun hc (j u)
  simpa [LinearMap.sum_apply, h, hu] using h1

end Lemmas

theorem isVBOn_mono {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T T' : Set (Cpt ξ)} (hT : T' ⊆ T) {r : ℕ} {V : Submodule Ω E}
    (h : L.IsVBOn T r V) : L.IsVBOn T' r V := by
  intro p hp
  obtain ⟨U, hU, b, hb, hfr⟩ := h p (hT hp)
  exact ⟨U, hU, b, hb, fun q hq => hfr q (hT hq)⟩

theorem exists_adjoint {Ω Ω' : Type} [Field Ω] [Field Ω'] {V V' : Type} [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] [AddCommGroup V'] [Module Ω' V'] {i : Ω →+* Ω'} {j : V →+ V'} (hj : IsExtOver i j)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) :
    Module.finrank Ω' V' = Module.finrank Ω V ∧ ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V',
      (∀ w v, jd w (j v) = i (w v)) ∧ (∀ (a : Ω) w, jd (a • w) = i a • jd w) ∧
        Submodule.span Ω' (jd '' ((⊤ : Submodule Ω (Module.Dual Ω V)) : Set (Module.Dual Ω V))) = ⊤ := by
  classical
  let v := Module.finBasis Ω V
  have hexp : ∀ u, j u = ∑ k, i (v.repr u k) • j (v k) := fun u => by
    conv_lhs => rw [← v.sum_repr u]

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj.1 _ _
  have hli : LinearIndependent Ω' fun k => j (v k) := by
    have h0 := hj.2 _ v v.linearIndependent
    exact h0
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (v k)) := by
    rw [← hs]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, hexp]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let v' := Module.Basis.mk hli hsp
  have hv' : ∀ k, v' k = j (v k) := fun k => by simp [v']
  let jd : Module.Dual Ω V →+ Module.Dual Ω' V' := AddMonoidHom.mk' (fun w => v'.constr Ω' fun k => i (w (v k)))
    (fun a b => by
      rw [← map_add (f := _)]
      congr 1
      funext k
      simp)
  have hjd : ∀ w k, jd w (v' k) = i (w (v k)) := fun w k => by
    show (v'.constr Ω' fun k => i (w (v k))) (v' k) = _
    simp [Module.Basis.constr_basis]
  have hadj : ∀ w u, jd w (j u) = i (w u) := fun w u => by
    rw [hexp u]
    conv_rhs => rw [← v.sum_repr u]

    simp only [map_sum, map_smul, ← hv', hjd, smul_eq_mul, map_mul]
  refine ⟨?_, jd, hadj, fun a w => v'.ext fun k => ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis v']
    simp
  · rw [hjd]
    show i ((a • w) (v k)) = i a • jd w (v' k)
    rw [hjd]
    simp
  · rw [eq_top_iff]
    rintro w' -
    have hc : ∀ k, jd (v.coord k) = v'.coord k := fun k => v'.ext fun l => by
      rw [hjd]
      simp [Finsupp.single_apply, Module.Basis.coord_apply, eq_comm]
    rw [← v'.sum_dual_apply_smul_coord w']
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨v.coord k, trivial, hc k⟩)

theorem omP_ext : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (g : A'.X ⟶ A.X) (m : SABMap A'.t A.t g) (j₁ : A.Li →+ A'.Li) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ), p ∈ S → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ g i → A'.f = g ≫ A.f → A'.R = A.R → IsExtOver i j₁ → (∀ v, (A'.M.pt (j₁ v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) → A.ξ ≫ A.f = y₀ ≫ Y.j → (∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤ → (HT.omP A' p).IsVBOn {q | InFibre A'.ξ p q} (Module.finrank Ω' A'.Li) ⊤ := by
  intro hW E _ _ _ H D l Xo c Y S Ω Ω' _ _ _ _ i K K' _ _ J J' _ _ y y' A A' g m j₁ y₀ p hp hd hf hR hext hpt hy hζ h
  classical
  have hn : p ^ A.R p ≠ 0 := pow_ne_zero _ (A.S_prime p hp).ne_zero
  obtain ⟨ζ, hζ⟩ := hζ
  have hζi : IsPrimitiveRoot (i ζ) (p ^ A.R p) := hζ.map_of_injective i.injective
  obtain ⟨ζ, rfl⟩ := hζ.isUnit hn
  obtain ⟨ζ₁, hz⟩ := hζi.isUnit hn
  rw [← hz] at hζi
  have hζ' := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hζ₁ := IsPrimitiveRoot.coe_units_iff.1 hζi
  have hy' : A'.ξ ≫ A'.f = (spMap i ≫ y₀) ≫ Y.j := by
    have hd' : A'.ξ ≫ g = spMap i ≫ A.ξ := hd
    rw [hf, ← Category.assoc, hd', Category.assoc, hy, Category.assoc]
  obtain ⟨-, e, -, -, -, -, he, -⟩ := GlobalTheory.T.primitive_root_hodge_cpt hW E H D l Xo c Y S Ω K J y A y₀ p ζ hp hy hζ'
  obtain ⟨-, e', -, -, -, -, he', -⟩ := GlobalTheory.T.primitive_root_hodge_cpt hW E H D l Xo c Y S Ω' K' J' y' A' (spMap i ≫ y₀) p ζ₁ hp hy'
    (by rw [hR]; exact hζ₁)
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω' A'.ξ ℤ _ _ A'.tie).2 A'.all).1
  rw [hR] at he'
  have hfd : FiniteDimensional Ω A.Li :=
    (GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y A.X Ω A.ξ A.f y₀ A.t A.m A.Li A.M A.ρ A.cst hy A.cst_over A.act).1
  obtain ⟨-, hspan, -⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X A'.X Ω Ω' A.ξ A'.ξ g i A.t.G A'.t.G m.φ A.Li A'.Li A.M A'.M j₁
    A.tie.gen A'.tie.gen hd m.cart A.t.semi.smooth hpt
  obtain ⟨hrk, jd, hadj, hsm, hjs⟩ := exists_adjoint hext hspan
  have key := (GlobalTheory.T.hodge_tate_weil_pullback A.X Ω A.ξ A.tie.gen ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω A.ξ A.tie.gen A.all).2.2 A.normal) A.t.G A.t.semi
    A.t.PP.L _ (Nat.one_le_iff_ne_zero.2 hn) (A.tors p hp) e he A.Li A.M A'.X Ω' A'.ξ A'.tie.gen
    ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω' A'.ξ A'.tie.gen A'.all).2.2 A'.normal) g i hd A'.t.G m.φ m.cart A'.t.PP.L e' he' A'.Li
    A'.M j₁ jd hpt hadj).1
  have h2 := GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ (Module.Dual Ω A.Li) A'.X Ω' A'.ξ g i (Module.Dual Ω' A'.Li) jd (HT.omP A p)
    {q | InFibre A.ξ p q} _ ⊤ hd hsm (fun _ _ hb => li_of_adjoint j₁ jd hadj hb) h
  rw [← key, hjs, ← hrk, ← hR] at h2
  refine isVBOn_mono (fun q hq => ?_) h2
  refine ⟨LatModel.dominates_spec hd q, fun hu => hq ?_⟩
  have hu' : unitAt A.ξ ⟨g q.1, LatModel.dominates_spec hd q⟩ (p : Ω) := hu
  have e1 : (p : Ω') = i (p : Ω) := (map_natCast i p).symm
  have e2 : (p : Ω')⁻¹ = i (p : Ω)⁻¹ := by rw [map_inv₀, map_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact (map_ne_zero i).2 hu'.1
  · rw [e1]; exact LatModel.dominates_regAt hd q _ hu'.2.1
  · rw [e2]; exact LatModel.dominates_regAt hd q _ hu'.2.2

end GlobalTheory.CompanionTheory.Ar.HFlag
end
end
