module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle088
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def chartHom (Y : Model Xo c β) (U : Y.X.affineOpens) {k : Type} [Field k] {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ gen Y)
    (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) : Γ(Y.X, U.1) →+* ChartRing k m d :=
  (Scheme.stalkClosedPointTo ξ).hom.comp
    (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)

end GlobalTheory.LocReg
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDerBd

theorem X_dvd_of_X_mul {σ K : Type} [Field K] {s t : σ} (hst : t ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ MvPowerSeries.X t * g) : MvPowerSeries.X s ∣ g := by
  classical
  rw [MvPowerSeries.X_dvd_iff] at h ⊢
  intro n hn
  have h1 := h (n + Finsupp.single t 1) (by simp [Finsupp.single_apply, hst, hn])
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul] at h1
  simpa using h1

theorem X_dvd_of_prod_mul {σ K : Type} [Field K] {Idx : Type} (f : Idx → σ) {s : σ}
    (S : Finset Idx) (hS : ∀ j ∈ S, f j ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ (∏ j ∈ S, MvPowerSeries.X (f j)) * g) : MvPowerSeries.X s ∣ g := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc] at h
    exact ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
      (X_dvd_of_X_mul (hS a (Finset.mem_insert_self a S)) h)

theorem deriv_bdParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  classical
  intro A _ k _ m d ψ δ D' I hI hD hJ i

  have hpres : ∀ x ∈ I.map ψ, D' x ∈ I.map ψ := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD]
      exact Ideal.mem_map_of_mem ψ (hI a ha)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
    | smul r x hxm hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hx)
        (Ideal.mul_mem_right _ _ (Ideal.span_le.2 (fun y hy => Ideal.subset_span hy) hxm))
  set t := bdParam k m d with ht
  have hP : t i * ∏ j ∈ Finset.univ.erase i, t j = ∏ j, t j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmem : D' (∏ j, t j) ∈ Ideal.span {∏ j, t j} := by
    rw [← hJ]; apply hpres; rw [hJ]; exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hmem ⊢
  rw [← hP, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hmem
  have h1 : t i ∣ t i * D' (∏ j ∈ Finset.univ.erase i, t j) + (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_mul_right (t i) _).trans hmem
  have h2 : t i ∣ (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_add_right (dvd_mul_right _ _)).1 h1
  exact X_dvd_of_prod_mul (fun j : Fin m => (Sum.inl j : Fin m ⊕ Fin d)) (Finset.univ.erase i)
    (fun j hj h => (Finset.ne_of_mem_erase hj) (Sum.inl_injective h)) h2

end GlobalTheory.ChartDerBd
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartAbLocus

theorem mem_abLocus_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))), SABMap t Y.t (ξ ≫ genι Y) → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  intro E _ _ _ H Dw l Xo c Y k _ m d ξ t φ hbd p
  rw [← hbd, mem_genBd_iff, not_not, ← abLocus_pullback abLocusOne Y.t.semi φ.cart.1 p]
  rfl

end GlobalTheory.ChartAbLocus
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem charZero_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y), CharZero k := by
  intro E _ _ _ H Dw l Xo c Y k _ m d ξ
  have : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  exact (algebraMap k (ChartRing k m d)).charZero_iff (RingHom.injective _) |>.2 this

end GlobalTheory.LocReg
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_psi_val_eq_monomial_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ)
    (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ (χ : Q.X) (n : Fin m → ℕ),
    (∀ i, gam i χ χ = 2 * n i) → ∃ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1),
      ψ₀.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
        Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n i) * (val ψ₀ (r ≫ jK R) z J).val := by
  intro R _ _ _ Q m t gam hM χ n hn
  obtain ⟨u, n', hn', hc⟩ := hM χ
  obtain rfl : n = n' := funext fun i => by have := (hn' i).symm.trans (hn i); omega
  obtain ⟨j, hj, h, e⟩ := hc
  have hL := Q.P.isLB
  obtain ⟨e₀, he₀⟩ := exists_gen_of_local (V := R) Q.P.L hL (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun k => by cases k; exact hj hy
  have hx : Q.xK χ = jK R ≫ (Q.c χ).left := by simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let w : Γ(Spec (CommRingCat.of R), ⊤)ˣ :=
    Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u * (res le (e₀.s j))⁻¹
  let v : LB.Gen (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top w⟩
  have hv : v.IsGen := fun i i' => by
    obtain rfl : i = i' := funext fun k => k.elim
    have e' : (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
      dsimp only [LB.LinComb]
      erw [Fintype.prod_empty]
      rfl
    rw [e', _root_.one_mul]
  have hf : FormEq (Sum.elim (fun _ : PUnit => (Q.c χ).left) (PEmpty.elim : PEmpty.{1} → _))
      (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (PEmpty.elim : PEmpty.{1} → ℤ))
      (fun _ : PUnit => (Q.c χ).left) (fun _ => -1) := fun U _ g => by
    rw [Fintype.prod_sum_type]
    simp
  obtain ⟨ψ₀, hψ₀, vψ₀⟩ := exists_gen hL hf (LB.mulGen Q.P.L _ _ _ _ e₀ v)
    (mulGen_isGen _ _ _ _ _ _ _ he₀ hv)
  refine ⟨ψ₀, hψ₀, fun Z r z J hJ => ?_⟩
  rw [vψ₀ _ _ z J hJ, val_mul hJ]
  have m₁ : r z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j := h trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j := le trivial
  have e₁ : val (Q.psi χ) r z J = _ := gen_trans (Q.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e₀ (r ≫ jK R) z J = _ := gen_trans he₀ (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := Q.P.L) (K := PUnit) (fun _ => Q.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ Q.xK χ)) j =
      trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j := by
    have hq : r ≫ Q.xK χ = (r ≫ jK R) ≫ (Q.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j) ((Q.psi χ).s j)).val =
      cst (r ≫ jK R) z (u * ∏ i, t i ^ n i) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z h trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) e.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : val v (r ≫ jK R) z J = gm (r ≫ jK R) z ⊤ w := gm_res _ z _ (hJ.mem PEmpty.elim _) _
  have e₆ : (gm (r ≫ jK R) z ⊤ (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)).val = cst (r ≫ jK R) z u := by
    rw [← gs_unit _ z ⊤ trivial, Units.coe_map, cst, ← hto]; rfl
  have e₇ : ∀ a b : R, cst (r ≫ jK R) z (a * b) = cst (r ≫ jK R) z a * cst (r ≫ jK R) z b := fun a b => by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  have e₈ : gm (r ≫ jK R) z ⊤ (res le (e₀.s j)) =
      gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j) := gm_res _ z le trivial _
  have hg := Units.mul_inv (gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j))
  rw [e₁, e₂, e₅, Units.val_mul, Units.val_mul, e₄]
  erw [e₃]
  rw [map_mul, map_inv, e₈]
  simp only [Units.val_mul]
  rw [e₆, e₇]
  linear_combination (-((trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j).val * cst (r ≫ jK R) z u * cst (r ≫ jK R) z (∏ i, t i ^ n i))) * hg

end GlobalTheory.UnitPart
end
end

section

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {r m : ℕ}

theorem Supports.mul {d : ℕ} {γ : Fin r → LinearMap.BilinForm ℤ X} {a : Fin m → X} (h : Supports bar φ d γ a) {k : ℕ}
    (hk : 0 < k) : Supports bar φ (d * k) γ fun j : Fin (m * k) => a (finProdFinEquiv.symm j).1 := by
  have key : ∀ β : LinearMap.BilinForm ℤ X,
      (∑ j : Fin (m * k), β (a (finProdFinEquiv.symm j).1) (a (finProdFinEquiv.symm j).1) : ℤ) =
        k * ∑ i, β (a i) (a i) := fun β => by
    rw [finProdFinEquiv.symm.sum_comp (fun p : Fin m × Fin k => β (a p.1) (a p.1)), Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => h.only β hβ hp ?_⟩
  · rw [← h.span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨finProdFinEquiv (i, ⟨0, hk⟩), by simp⟩
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    have := h.le β hβ hp
    nlinarith
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← h.eq j]; ring
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast] at he
    have : (k : ℝ) * (d * φ.evalZ β) = k * (∑ i, β (a i) (a i) : ℤ) := by rw [← he]; ring
    exact mul_left_cancel₀ hk'.ne' this

theorem Supports.of_pull {d : ℕ} (e : X ≃ₗ[O] X₁) {γ : Fin r → LinearMap.BilinForm ℤ X₁} {a : Fin m → X}
    (h : Supports bar φ d (fun j => pull e.toLinearMap (γ j)) a) : Supports bar φ d γ fun i => e (a i) := by
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩
  · have h1 : Set.range (fun i => e (a i)) = e.toAddEquiv.toIntLinearEquiv.toLinearMap '' Set.range a := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h.span, Submodule.map_top, LinearMap.range_eq_top]
    exact e.toAddEquiv.toIntLinearEquiv.surjective
  · have := h.le _ (pull_mem e.toLinearMap hβ) fun y => hp _
    rwa [evalZ_pull φ e.surjective] at this
  · have := h.eq j
    rwa [evalZ_pull φ e.surjective] at this
  · have he' : d * φ.evalZ (pull e.toLinearMap β) = (∑ i, pull e.toLinearMap β (a i) (a i) : ℤ) := by
      rw [evalZ_pull φ e.surjective]; exact he
    obtain ⟨k, c, hk, hc⟩ := h.only _ (pull_mem e.toLinearMap hβ) (fun y => hp _) he'
    refine ⟨k, c, hk, LinearMap.ext₂ fun x y => ?_⟩
    have := LinearMap.congr_fun₂ hc (e.symm x) (e.symm y)
    simpa [LinearMap.sum_apply] using this

end Transport

theorem exists_common {ι : Type} [Finite ι] (P : ι → ℕ → Prop) (hmul : ∀ i d d', P i d → d ∣ d' → 0 < d' → P i d')
    (h : ∀ i, ∃ d, 1 ≤ d ∧ P i d) : ∃ d, 1 ≤ d ∧ ∀ i, P i d := by
  have := Fintype.ofFinite ι
  choose d hd hP using h
  have hpos : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  exact ⟨_, hpos, fun i => hmul i _ _ (hP i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hpos⟩

section Module

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}

theorem exists_common_module {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (hX : IsPolFanOn bar φ X)
    (hs : ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
      Supports bar φ d γ a) :
    ∃ d, 1 ≤ d ∧ ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → X),
      Supports bar φ d γ a := by
  obtain ⟨S, hS, hfin⟩ := hX.finite
  have := hS.to_subtype
  let N := Nat.card S
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Σ r : Fin (N + 1), (Fin r → S))
    (fun i d => IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) →
      ∃ (m : ℕ) (a : Fin m → X), Supports bar φ d (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) a)
    (fun i d d' h hdd hd' hc => by
      obtain ⟨m, a, ha⟩ := h hc
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun i => by
      by_cases hc : IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X))
      · obtain ⟨d, m, a, hd, ha⟩ := hs _ _ hc
        exact ⟨d, hd, fun _ => ⟨m, a, ha⟩⟩
      · exact ⟨1, le_rfl, fun h => (hc h).elim⟩)
  refine ⟨d, hd, fun r γ hγ => ?_⟩
  obtain ⟨e, he⟩ := hfin r γ hγ
  have hγ' := hγ.pull_equiv e
  have hr : r ≤ N := by
    have := Nat.card_le_card_of_injective (fun i : Fin r => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rwa [Nat.card_fin] at this
  obtain ⟨m, a, ha⟩ := hP ⟨⟨r, by omega⟩, fun i => ⟨_, he i⟩⟩ hγ'
  exact ⟨m, _, ha.of_pull e⟩

end Module

theorem exists_hasSupports : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O]
    [Finite (ClassGroup O)] (bar : O → O) (q : ℕ) (φ : InvFun O), IsPolFan bar q φ →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
        Supports bar φ d γ a) → ∃ d, 1 ≤ d ∧ HasSupports bar q φ d := by
  intro O _ _ _ _ _ bar q φ hpol hs
  obtain ⟨n, Y, hY⟩ := GlobalTheory.ProjModFinIso.exists_finite_reps (R := O) q
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Fin n)
    (fun k d => ∀ [Module.Finite O (Y k)] [Module.Projective O (Y k)], Module.finrank O (Y k) ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ (Y k)), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → Y k),
        Supports bar φ d γ a)
    (fun k d d' h hdd hd' _ _ hq r γ hγ => by
      obtain ⟨m, a, ha⟩ := h hq r γ hγ
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun k => by
      by_cases hk : Module.Finite O (Y k) ∧ Module.Projective O (Y k) ∧ Module.finrank O (Y k) ≤ q
      · obtain ⟨h1, h2, h3⟩ := hk
        obtain ⟨d, hd, h⟩ := exists_common_module (hpol _ h3) (hs _ h3)
        exact ⟨d, hd, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h3 => (hk ⟨‹_›, ‹_›, h3⟩).elim⟩)
  refine ⟨d, hd, fun X _ _ _ _ hX r γ hγ => ?_⟩
  obtain ⟨k, ⟨e⟩⟩ := hY X hX
  haveI := Module.Finite.equiv e
  haveI := Module.Projective.of_equiv e
  obtain ⟨m, a, ha⟩ := hP k (e.finrank_eq ▸ hX) r _ (hγ.pull_equiv e.symm)
  exact ⟨m, _, ha.of_pull e.symm⟩

end GlobalTheory.Poinc
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section

theorem GlobalTheory.CompHS.exists_modif_map_of_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  intro hPr F _ _ Y T _ p d t U r₀ hs hpY hpT hU hr
  obtain ⟨N, i, hi, hit⟩ := hpT
  have hφ : (r₀ ≫ i) ≫ PSpace.str F N = U.ι ≫ p := by rw [Category.assoc, hit, hr]
  obtain ⟨w, i₀, hw₀, hwU, hext⟩ := GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace F Y p N U (r₀ ≫ i) hφ hU
  obtain ⟨I, hI0, hIU, hC⟩ := GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family Y N w i₀ U hw₀ hwU
  obtain ⟨Y', s, hY', hs', hp', -, hiso, hEC, -⟩ := hPr F d Y p inferInstance hs hpY I hI0
  have hUle : U ≤ I.support.compl := fun y hy => hIU y hy
  have hisoU : IsIso (s ∣_ U) := ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le s hUle
  have : Nonempty U := hU.to_subtype
  let c : U.toScheme ⟶ Y' := inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι
  have hc : c ≫ s = U.ι := by simp [c, morphismRestrict_ι]
  have hcη : c (genericPoint U) = genericPoint Y' := genericPoint_eq_of_isOpenImmersion c
  have hη : s (genericPoint Y') = genericPoint Y := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hne : ((s ⁻¹ᵁ U : Y'.Opens) : Set Y').Nonempty :=
    ⟨genericPoint Y', show s (genericPoint Y') ∈ U from hη ▸ GlobalTheory.Cartier.gen_mem hU.some_mem⟩
  have hdense : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y') := (s ⁻¹ᵁ U).isOpen.dense hne
  let M : Modif p U d := ⟨Y', s, hs', hp', hisoU, hdense⟩
  obtain ⟨g, hg1, hg2⟩ := hext Y' s hη (hC Y' s hη hEC)
  obtain ⟨r, hr'⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i g _ hdense fun x hx => by
    refine ⟨(s ∣_ U ≫ r₀) ⟨x, hx⟩, ?_⟩
    have e := congrArg (fun f : (s ⁻¹ᵁ U).toScheme ⟶ PSpace F N => f ⟨x, hx⟩) hg2
    exact e.symm
  refine ⟨M, r, hY', ?_, ?_⟩
  · show r ≫ t = s ≫ p
    rw [← hit, ← Category.assoc, hr', hg1]
  · show (s ⁻¹ᵁ U).ι ≫ r = (s ∣_ U) ≫ r₀
    rw [← cancel_mono i, Category.assoc, hr', hg2, Category.assoc]
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.two_mul_finrank_balancedSymmIntBilinForms : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], 2 * Module.finrank ℤ (balForms H.bar X) = Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar X) := by
  first | exact @GlobalTheory.BalRankSym.two_mul_finrank_balForms | exact GlobalTheory.BalRankSym.two_mul_finrank_balForms | (intros; apply GlobalTheory.BalRankSym.two_mul_finrank_balForms <;> assumption)
end
