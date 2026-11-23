module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle725
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle726
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechDeRhamHypercohomologyCup_anticomm : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  first | exact @GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | exact GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | (intros; apply GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (a b : GlobalTheory.CatCoh.H1 F), cup F a b = - cup F b a := by
  first | exact @GlobalTheory.AbCoh.cup_anticomm | exact GlobalTheory.AbCoh.cup_anticomm | (intros; apply GlobalTheory.AbCoh.cup_anticomm <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tensor_algebra_product_diagram_compat : ∀ (K : Type) [Field K] (P Q : Type) [Category.{0} P] [Category.{0} Q] [Finite Q] [Quiver.IsThin Q] (F : P ⥤ CommAlgCat.{0} K) (G : Q ⥤ CommAlgCat.{0} K) (E : P × Q ⥤ CommAlgCat.{0} K) (i₁ : ∀ T : P × Q, F.obj T.1 →ₐ[K] E.obj T) (i₂ : ∀ T : P × Q, G.obj T.2 →ₐ[K] E.obj T), (∀ (T T' : P × Q) (a : T ⟶ T') (b : F.obj T.1), i₁ T' (mp F a.1 b) = mp E a (i₁ T b)) → (∀ (T T' : P × Q) (a : T ⟶ T') (b : G.obj T.2), i₂ T' (mp G a.2 b) = mp E a (i₂ T b)) → (∀ T, Function.Bijective (Algebra.TensorProduct.productMap (i₁ T) (i₂ T))) → ∀ (n : ℕ) (x : Fin n → Z1 F) (y : Fin n → Z1 G) (f : C1 E), (∀ (T T' T'' : P × Q) (a : T ⟶ T') (b : T' ⟶ T''), d1 E f T T' T'' a b = ∑ i, mp E b (i₁ T' ((x i).1 _ _ a.1)) * i₂ T'' ((y i).1 _ _ b.2)) → ∑ i, GlobalTheory.CatCoh.H1.mk F (x i) ⊗ₜ[K] GlobalTheory.CatCoh.H1.mk G (y i) = 0 := by
  first | exact @GlobalTheory.CatCoh.KunnethOne.sum_tmul_eq_zero_of_cup | exact GlobalTheory.CatCoh.KunnethOne.sum_tmul_eq_zero_of_cup | (intros; apply GlobalTheory.CatCoh.KunnethOne.sum_tmul_eq_zero_of_cup <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_affine_open_product_sections_iso : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (U : X.left.affineOpens) (V : Y.left.affineOpens), ∃ (W : (X ⊗ Y).left.affineOpens) (h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1) (h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1) (i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1) (i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1), W.1 = (fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1 ∧ (∀ b, i₁ b = ((fst X Y).left.appLE U.1 W.1 h₁).hom b) ∧ (∀ b, i₂ b = ((snd X Y).left.appLE V.1 W.1 h₂).hom b) ∧ Function.Bijective (Algebra.TensorProduct.productMap i₁ i₂) := by
  first | exact @GlobalTheory.functions_on_product_of_affine_opens | exact GlobalTheory.functions_on_product_of_affine_opens | (intros; apply GlobalTheory.functions_on_product_of_affine_opens <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.existsUnique_ringHom_of_sqZeroExt_point_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U → ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  first | exact @GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero | exact GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero | (intros; apply GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cech_pull_one_bijective_lattice_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull1 := by
  first | exact @GlobalTheory.CoverO.restrict_bijective | exact GlobalTheory.CoverO.restrict_bijective | (intros; apply GlobalTheory.CoverO.restrict_bijective <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QLogTangent

theorem smodEq_iff' {O : Type} [CommRing O] (p : O) (n : ℕ) (x y : O) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule O O)] ↔ p ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_dvd {O : Type} [CommRing O] (p : O) [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff' p n x 0).2 (by simpa using h n)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f hf
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hlift : IsLift (RingHom.id O) c.μ :=
    ⟨c.isLaw.const, c.isLaw.unit, c.isLaw.comm, by simpa using c.isLaw⟩
  have hser : ∀ {τ : Type} (F : MvPowerSeries τ E), In (⊤ : Ideal O) F →
      ∃ s : MvPowerSeries τ O, map (algebraMap O E) s = F := by
    intro τ F hF'
    choose b _ hb using hF'
    let S : MvPowerSeries τ O := fun α => b α
    exact ⟨S, by ext α; rw [coeff_map, hb α]; rfl⟩
  have hminj : ∀ (s s' : MvPowerSeries (Fin d) O),
      map (algebraMap O E) s = map (algebraMap O E) s' → s = s' := by
    intro s s' h
    ext α
    apply hinj
    have := congrArg (coeff α) h
    simpa [coeff_map] using this
  have hdef : ∀ k, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ k f :=
    fun k => hser _ (GlobalTheory.QLogDefect.main p O O E (RingHom.id O) hF d c.μ hlift ⊤ f hf k).1
  obtain ⟨g, hg⟩ := hser _ hf.2.2
  choose s hs using hdef
  let a : ∀ n, G.A n := fun n => c.ev n (s (p ^ n))
  have hprim : ∀ n, ∃ t : G.A n ⊗[O] G.A n,
      Coalgebra.comul (R := O) (a n) = a n ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] a n + ((p : O) ^ n) • t := by
    intro n
    obtain ⟨h1, h2⟩ := GlobalTheory.CobDefect.main O E d c.μ c.isLaw hinj f g (s (p ^ n)) (p ^ n) hf.1 hg (hs _)
    refine ⟨c.ev₂ n g, ?_⟩
    show Coalgebra.comul (R := O) (c.ev n (s (p ^ n))) = _
    rw [GlobalTheory.QLog.Chart.comul_ev p C v O hv G d c n, h1, map_sub, map_smul, GlobalTheory.EvTor.ev₂_at_nmul_pow_self p C v O hv G d c n, h2, map_zero, sub_zero,
      Nat.cast_pow]
  have hcomp : ∀ n, ∃ b : G.A (n + 1), a (n + 1) = G.mulP n (a n) + ((p : O) ^ n) • b := by
    intro n
    have h := GlobalTheory.DefectComp.main O E d c.μ c.isLaw hinj f hf.1 (p ^ n) p (s (p ^ n)) (s p) (s (p ^ n * p))
      (hs _) (hs _) (hs _)
    refine ⟨c.ev (n + 1) (s p), ?_⟩
    show c.ev (n + 1) (s (p ^ (n + 1))) = G.mulP n (c.ev n (s (p ^ n))) + _
    rw [pow_succ, h, map_add (f := _), map_smul, GlobalTheory.EvP.ev_subst_nmul_p p C v O hv G d c n, Nat.cast_pow]
  have key : ∀ n (φ ψ : CartierDual O (G.A n)), PDiv.dUnit (R := O) φ = PDiv.dUnit (R := O) ψ →
      (p : O) ^ n ∣ φ (a n) - ψ (a n) := by
    intro n φ ψ h
    obtain ⟨t, ht⟩ := hprim n
    exact GlobalTheory.CotDualLin.dvd_sub_of_dUnit_eq O (G.A n) (a n) _ t ht φ ψ h
  have dsurj : ∀ n (x : PDiv.Cot O (CartierDual O (G.A n))), ∃ φ : CartierDual O (G.A n),
      PDiv.dUnit (R := O) φ = x := fun n x => AugCot.d_surjective _ x
  have haus : ∀ x : O, (∀ n : ℕ, (p : O) ^ n ∣ x) → x = 0 := eq_zero_of_forall_dvd (p : O)
  let Good : G.dual.omega → O → Prop := fun w L => ∀ n (φ : CartierDual O (G.A n)),
    PDiv.dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ L - φ (a n)
  have good_unique : ∀ w L L', Good w L → Good w L' → L = L' := by
    intro w L L' h h'
    refine sub_eq_zero.1 (haus _ fun n => ?_)
    obtain ⟨φ, hφ⟩ := dsurj n (w.1 n)
    have := dvd_sub (h n φ hφ) (h' n φ hφ)
    rwa [sub_sub_sub_cancel_right] at this
  have good_exists : ∀ w, ∃ L, Good w L := by
    intro w
    choose φ hφ using fun n => dsurj n (w.1 n)
    have step : ∀ n, (p : O) ^ n ∣ φ (n + 1) (a (n + 1)) - φ n (a n) := by
      intro n
      obtain ⟨b, hb⟩ := hcomp n
      have h1 : PDiv.dUnit (R := O) (CartierDual.map (G.mulP n) (φ (n + 1))) = w.1 n := by
        rw [← w.2 n, ← hφ (n + 1)]
        exact (PDiv.cotMap_d (G.dual.res n) (φ (n + 1))).symm
      have h2 := key n _ _ (h1.trans (hφ n).symm)
      rw [CartierDual.map_apply] at h2
      rw [hb, map_add (f := _), map_smul, smul_eq_mul]
      have e : φ (n + 1) (G.mulP n (a n)) + (p : O) ^ n * φ (n + 1) b - φ n (a n) =
          (φ (n + 1) (G.mulP n (a n)) - φ n (a n)) + (p : O) ^ n * φ (n + 1) b := by ring
      rw [e]
      exact dvd_add h2 (dvd_mul_right _ _)
    have cauchy : ∀ m n, m ≤ n → (p : O) ^ m ∣ φ n (a n) - φ m (a m) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := dvd_add ih ((pow_dvd_pow (p : O) hmn).trans (step n))
        rwa [add_comm, sub_add_sub_cancel] at this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => φ n (a n))
      (fun {m n} hmn => (smodEq_iff' _ _ _ _).2 (dvd_sub_comm.1 (cauchy m n hmn)))
    refine ⟨L, fun n ψ hψ => ?_⟩
    have h1 := (smodEq_iff' _ _ _ _).1 (hL n)
    have h2 := key n _ _ ((hφ n).trans hψ.symm)
    have := dvd_add (dvd_sub_comm.1 h1) h2
    rwa [sub_add_sub_cancel] at this
  choose Lf hLf using good_exists
  have hgood_add : ∀ w w', Good (w + w') (Lf w + Lf w') := by
    intro w w' n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    obtain ⟨φ2, h2⟩ := dsurj n (w'.1 n)
    have e : PDiv.dUnit (R := O) (φ1 + φ2) = PDiv.dUnit (R := O) φ := by
      have ea : PDiv.dUnit (R := O) (φ1 + φ2) = PDiv.dUnit (R := O) φ1 + PDiv.dUnit (R := O) φ2 := map_add (AugCot.d _) φ1 φ2
      rw [ea, h1, h2, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_add (hLf w n φ1 h1) (hLf w' n φ2 h2)) k
    have e2 : (φ1 + φ2) (a n) = φ1 (a n) + φ2 (a n) := rfl
    rw [e2] at this
    have e3 : Lf w - φ1 (a n) + (Lf w' - φ2 (a n)) + (φ1 (a n) + φ2 (a n) - φ (a n)) =
        Lf w + Lf w' - φ (a n) := by ring
    rwa [e3] at this
  have hgood_smul : ∀ (r : O) w, Good (r • w) (r * Lf w) := by
    intro r w n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    have e : PDiv.dUnit (R := O) (r • φ1) = PDiv.dUnit (R := O) φ := by
      have ea : PDiv.dUnit (R := O) (r • φ1) = r • PDiv.dUnit (R := O) φ1 := map_smul (AugCot.d _) r φ1
      rw [ea, h1, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_mul_of_dvd_right (hLf w n φ1 h1) r) k
    have e2 : (r • φ1) (a n) = r * φ1 (a n) := rfl
    rw [e2] at this
    have e3 : r * (Lf w - φ1 (a n)) + (r * φ1 (a n) - φ (a n)) = r * Lf w - φ (a n) := by ring
    rwa [e3] at this
  let l : G.dual.Lie :=
    { toFun := Lf
      map_add' := fun w w' => good_unique _ _ _ (hLf (w + w')) (hgood_add w w')
      map_smul' := fun r w => good_unique _ _ _ (hLf (r • w)) (hgood_smul r w) }
  have hisLie : ∀ l' : G.dual.Lie, c.IsLie f l' ↔ ∀ w, Good w (l' w) := by
    intro l'
    constructor
    · intro h w n φ hφ
      exact h.2 n w φ (s (p ^ n)) hφ (hs _)
    · intro h
      refine ⟨fun n => In.top_iff.2 ⟨s (p ^ n), hs _⟩, fun n w φ s' hφ hs' => ?_⟩
      have : s' = s (p ^ n) := hminj _ _ (hs'.trans (hs _).symm)
      subst this
      exact h w n φ hφ
  refine ⟨l, (hisLie l).2 fun w => hLf w, fun l' hl' => ?_⟩
  exact LinearMap.ext fun w => good_unique _ _ _ ((hisLie l').1 hl' w) (hLf w)

end GlobalTheory.QLogTangent
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieZero

theorem eq_zero_of_pow_dvd {O : Type} [CommRing O] {p : O} [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {p}) ‹_› x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (h n)

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun k => X k) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem constantCoeff_nmul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    have hb : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j)
        = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    rw [nmul_succ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hb) hb (hμ i)

theorem subst_eq_add_of_cob1_eq_zero {E : Type} [CommRing E] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) E)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) (hf : cob1 μ f = 0)
    {τ : Type} (b : Fin d ⊕ Fin d → MvPowerSeries τ E) (hb : HasSubst b) :
    subst (fun i => subst b (μ i)) f = subst (fun i => b (Sum.inl i)) f + subst (fun i => b (Sum.inr i)) f := by
  have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have h := congrArg (subst b) hf
  unfold cob1 inL inR at h
  rw [subst_sub hb, subst_sub hb, subst_comp_subst_apply hμs hb,
    subst_comp_subst_apply hL hb, subst_comp_subst_apply hR hb, ← coe_substAlgHom hb, map_zero,
    coe_substAlgHom hb] at h
  simp only [subst_X hb] at h
  rw [← sub_eq_zero, ← h, sub_sub]

theorem subst_nmul_of_cob1_eq_zero {O E : Type} [CommRing O] [CommRing E] [Algebra O E]
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) E) (hf : cob1 (up E μ) f = 0) (m : ℕ) :
    subst (up E (nmul μ m)) f = (m : E) • f := by
  have hμ' : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hμ i]
  induction m with
  | zero =>
    have h0 : up E (nmul μ 0) = (0 : Fin d → MvPowerSeries (Fin d) E) := by
      funext i; simp [up, nmul]
    rw [h0, Nat.cast_zero, zero_smul]
    have h := subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E)
      HasSubst.zero
    have h1 : (fun i => subst (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (up E μ i)) = 0 := by
      funext i; exact subst_zero_of_constantCoeff_zero (hμ' i)
    rw [h1] at h
    have h2 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inl i)) = 0 := rfl
    have h3 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inr i)) = 0 := rfl
    rw [h2, h3] at h
    linear_combination -h
  | succ m ih =>
    have hc : ∀ j, constantCoeff (Sum.elim (nmul μ m) (fun k => (X k : MvPowerSeries (Fin d) O)) j)
        = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ m j
      · simp
    have hc' : ∀ j, constantCoeff (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E)) j) = 0 := by
      rintro (j | j)
      · simp [up, constantCoeff_map, constantCoeff_nmul μ hμ m j]
      · simp
    have hs : up E (nmul μ (m + 1)) = fun i => subst (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E))) (up E μ i) := by
      funext i
      simp only [up, nmul_succ, op, at2]
      rw [map_subst (hasSubst_of_constantCoeff_zero hc)]
      congr 1
      funext j
      rcases j with j | j <;> simp [up]
    rw [hs, subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf _ (hasSubst_of_constantCoeff_zero hc')]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [ih, show (subst (fun k => (X k : MvPowerSeries (Fin d) E)) f) = f from
      congrFun (subst_self (R := E) (σ := Fin d)) f]
    push_cast
    rw [add_smul, one_smul]

theorem lie_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), c.IsLie f l →
    (In (⊤ : Ideal O) f → constantCoeff f = 0 → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  intro p _ O E _ _ _ hF G d c f l hl
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  unfold Chart.IsLie at hl
  have key : (∀ n, ∃ s : MvPowerSeries (Fin d) O, MvPowerSeries.map (algebraMap O E) s =
      defect c.μ (p ^ n) f ∧ ∃ z, c.ev n s = (p : O) ^ n • z) → l = 0 := by
    intro H
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    refine eq_zero_of_pow_dvd (p := (p : O)) _ fun n => ?_
    obtain ⟨s, hs, z, hz⟩ := H n
    obtain ⟨φ, hφ⟩ := (T.dvd_of_forall_invariantDifferential_dvd p O G n 1 0 (fun _ _ _ => one_dvd _)).2 w
    have h1 := hl.2 n w φ s hφ hs
    have h2 : (p : O) ^ n ∣ φ (c.ev n s) := by
      rw [hz]
      simp
    simpa using dvd_add h1 h2
  refine ⟨fun hIn hc0 => key fun n => ?_, fun hcob => key fun n => ?_⟩
  · choose g hg using hIn
    let s0 : MvPowerSeries (Fin d) O := fun α => g α
    have hs0 : MvPowerSeries.map (algebraMap O E) s0 = f := by
      ext α
      rw [coeff_map, (hg α).2]
      rfl
    have hc : constantCoeff s0 = 0 := by
      apply hF.inj
      rw [map_zero, ← constantCoeff_map, hs0, hc0]
    have hsub : HasSubst (nmul c.μ (p ^ n)) :=
      hasSubst_of_constantCoeff_zero (constantCoeff_nmul c.μ c.isLaw.const _)
    refine ⟨(p ^ n) • s0 - subst (nmul c.μ (p ^ n)) s0, ?_, c.ev n s0, ?_⟩
    · rw [map_sub, map_nsmul, map_subst hsub, hs0]
      unfold defect
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    · rw [map_sub, map_nsmul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).1 s0, hc, map_zero, sub_zero,
        ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  · refine ⟨0, ?_, 0, ?_⟩
    · unfold defect
      rw [subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hcob, sub_self, map_zero]
    · simp

end GlobalTheory.LieZero
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ), cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧ defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  first | exact @GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw | exact GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw | (intros; apply GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  first | exact @GlobalTheory.cob_symCoc_mod | exact GlobalTheory.cob_symCoc_mod | (intros; apply GlobalTheory.cob_symCoc_mod <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.tail_subst_pAdically_small_of_integral_differential : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → ∀ m : ℕ, ∃ M0 : ℕ, ∀ M ≥ M0, ∀ n : σ →₀ ℕ, ∃ b : B, MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) (f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q)))) = algebraMap B Q (p ^ m * b) := by
  first | exact @GlobalTheory.tail_subst_small | exact GlobalTheory.tail_subst_small | (intros; apply GlobalTheory.tail_subst_small <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G), ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  first | (exact @GlobalTheory.Katz.existsUnique_semiHom_ev) | (exact GlobalTheory.Katz.existsUnique_semiHom_ev) | (intros; apply GlobalTheory.Katz.existsUnique_semiHom_ev  <;> assumption)
end
