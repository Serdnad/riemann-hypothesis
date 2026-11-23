module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle850
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.CondNumber

theorem exists_mul_pow_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ M j : ℕ, ¬ l ∣ M ∧ (M : 𝓞 K) * (l : 𝓞 K) ^ j ∈ I := by
  have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨j, M, hM, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨M, j, hM, ?_⟩
  have := Ideal.absNorm_mem I
  rw [he] at this
  push_cast at this
  rwa [mul_comm] at this

theorem mem_of_forall_pow {R : Type} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {x : R}
    (h : ∀ (v : HeightOneSpectrum R) (n : ℕ), v.asIdeal ^ n ∣ I → x ∈ v.asIdeal ^ n) : x ∈ I := by
  have e := Ideal.iInf_maxPowDividing_eq (I := I) hI
  rw [← e, Submodule.mem_iInf]
  intro v
  apply h v
  rw [Ideal.dvd_iff_le]
  exact e.ge.trans (iInf_le _ v)

theorem exists_mem_condQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  intro E _ _ _ l 𝔣 Q hl h𝔣 hQ
  obtain ⟨M₁, j, hM₁, hj⟩ := exists_mul_pow_mem hl h𝔣.1
  have h1 : (M₁ : OF E) * (l : OF E) ^ a0 𝔣 l ∈ 𝔣 := by
    refine mem_of_forall_pow h𝔣.1 fun v n hn => ?_
    by_cases hv : (l : OF E) ∈ v.asIdeal
    · have hfin : FiniteMultiplicity v.asIdeal 𝔣 :=
        FiniteMultiplicity.of_not_isUnit v.irreducible.not_isUnit h𝔣.1
      have hle : n ≤ a0 𝔣 l :=
        (hfin.le_multiplicity_of_pow_dvd hn).trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime h𝔣 hv)
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hv _))
    · have h2 := Ideal.le_of_dvd hn hj
      have := v.isPrime
      rcases Ideal.IsPrime.mem_pow_mul v.asIdeal h2 with h3 | h3
      · exact Ideal.mul_mem_right _ _ h3
      · exact absurd (v.isPrime.mem_of_pow_mem _ h3) hv
  have h2 : ∀ q : HeightOneSpectrum (OF E), ∃ M : ℕ, ¬ l ∣ M ∧ (q ∈ Q → (M : OF E) ∈ q.asIdeal) := by
    intro q
    obtain ⟨M, i, hM, hi⟩ := exists_mul_pow_mem hl q.ne_bot
    refine ⟨M, hM, fun hq => ?_⟩
    rcases q.isPrime.mem_or_mem hi with h3 | h3
    · exact h3
    · exact absurd (q.isPrime.mem_of_pow_mem _ h3) (hQ q hq)
  choose N hN hNq using h2
  refine ⟨M₁ * ∏ q ∈ Q, N q, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · exact hM₁ h
    · obtain ⟨q, -, hq⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
      exact hN q hq
  · have h3 : (∏ q ∈ Q, (N q : OF E)) ∈ ∏ q ∈ Q, q.asIdeal := Ideal.prod_mem_prod fun q hq => hNq q hq
    have h4 := Ideal.mul_mem_mul h1 h3
    unfold condQ
    convert h4 using 1
    push_cast
    ring

end GlobalTheory.HilbFam.CondNumber
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.period_comp_translationGroup_hom : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  first | exact @GlobalTheory.AnPer.Reindex.isPeriod_comp | exact GlobalTheory.AnPer.Reindex.isPeriod_comp | (intros; apply GlobalTheory.AnPer.Reindex.isPeriod_comp <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.period_pullback_eq_of_chartMap_class : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k)) (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)), (∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) → ∀ (r₁ : Real K₁ s₁ σ₁) (r₂ : Real K₂ s₂ σ₂) (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), (∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l))) → r₂.coef.pull1 c = K₂.perCl per₂ → r₁.coef.pull1 (m.pull1 c) = K₁.perCl per₁ := by
  first | exact @GlobalTheory.AnPer.CmpCore.period_pullback_eq_of_chartMap_class_alt | exact GlobalTheory.AnPer.CmpCore.period_pullback_eq_of_chartMap_class_alt | (intros; apply GlobalTheory.AnPer.CmpCore.period_pullback_eq_of_chartMap_class_alt <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem exists_bound_glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F), K.Rich → ∀ (r : Real K s σ) (f : Form s) (per : Λ →+ Hol F.V), r.coef.pull1 (Form.cl s f) = K.perCl per → ∃ (q : GlobalTheory.CatCoh.C0 K.Oc) (G : Tot I g → ℂ), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 ∧ AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, Hol.fn (W := K.W k) (q (K.triv k)) p = G p) ∧ ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → G (F.shift l p) = G p + (per l).fn p.1 := by
  intro I _ g Λ _ F B _ X s σ K hK r f per hc
  have hc' : GlobalTheory.CatCoh.H1.mk K.Oc (r.coef.pullbackOneCocycle f.1) = GlobalTheory.CatCoh.H1.mk K.Oc (K.perZ per) := hc
  obtain ⟨q, hq⟩ := GlobalTheory.CatCoh.H1.mk_eq_mk.1 hc'
  have key : ∀ (l : Λ) (k k' : K.K) (h : K.le l k' k),
      Charts.sh h (q (K.triv k)) = q (K.triv k') + K.cst k' (per l) := by
    intro l k k' h
    have e := congrFun (congrFun (congrFun hq (K.triv k)) (K.triv k')) (Charts.ptHom (K.triv k') h)
    have h0 : (r.coef.pullbackOneCocycle f.1).1 _ _ (Charts.ptHom (K.triv k') h) = 0 :=
      f.2 (r.functor.map (Charts.ptHom (K.triv k') h)) rfl rfl
    rw [GlobalTheory.CatCoh.amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0, zero_sub] at e
    change q (K.triv k') - Charts.sh h (q (K.triv k)) = -K.cst k' (per l) at e
    linear_combination -e
  obtain ⟨G, hGa, hG, hsh, -⟩ := Charts.glue K hK (fun k ↦ q (K.triv k))
    (fun k k' h ↦ by rw [key 0 k k' h, map_zero, map_zero, add_zero])
  exact ⟨q, G, hq, hGa, hG, fun l p hp ↦ hsh l (per l) (fun k k' h ↦ key l k k' h) p hp⟩

end GlobalTheory.AnPer.Charts
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_real_isFor : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ K : Charts F, (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ r : Real K s σ, r.IsFor u ∧ ∀ k (U : X.Opens), IsAffineOpen U → (∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ⊤ ≤ r.x k ⁻¹ᵁ U := by
  intro I _ g Λ _ F B _ X s σ u hX K hK
  choose U hU hUE using hK
  have hx := fun k => exists_pt_of_affine u (K.W k) (K.base k) (U k) (hU k) (hUE k)
  choose x hxU hxE using hx
  have uniq : ∀ k (y : Sp (Hol (K.W k)) ⟶ X),
      (∀ p (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ y = u.E p) → y = x k := fun k y hy =>
    point_hol_ext_of_isSeparated (K.W k) hX y (x k) (fun p hp => (hy p hp).trans (hxE k p hp).symm)
  refine ⟨⟨x, ?_, ?_⟩, ?_, ?_⟩
  · intro k
    apply point_hol_ext_of_isSeparated (K.W k) inferInstance
    intro p hp
    rw [← Category.assoc, hxE k p hp, u.w p (K.base k p hp), ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    congr 1
  · intro l k k' h
    apply uniq k'
    intro p hp
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    have e : ((Hol.ev p hp).toRingHom.comp (Charts.sh h)) = (Hol.ev (F.shift l p) (K.maps h p hp)).toRingHom := by
      ext f
      simp [Hol.ev_apply, Charts.fn_sh h f hp]
    rw [e, hxE k _ (K.maps h p hp), u.per l p (K.base k' p hp)]
  · intro k p hp
    exact hxE k p hp
  · intro k V hV hVE
    obtain ⟨y, hyV, hyE⟩ := exists_pt_of_affine u (K.W k) (K.base k) V hV hVE
    have e := uniq k y hyE
    subst e
    exact hyV

end GlobalTheory.AnPer
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.LiftHc

theorem galAct_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (x : GL (Fin n) F) : galAct F F' n t (incl F F' n x) = incl F F' n x := by
  ext i j; simp [galAct_apply, gal, incl]

theorem inPar_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (x : GL (Fin n) F) :
    InPar a (incl F F' n x) ↔ InPar a x := by
  simp [InPar, incl, gal]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a n : ℕ) (x : GL (Fin n) F) (hx : InPar a x) :
    InPar a (gal t n x) := by
  intro i j hj hi; simp [gal, hx i j hj hi]

theorem gal_id {F : Type} [Field F] (n : ℕ) (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem nrm_conj_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (y₀ : GL (Fin n) F) :
    nrm s ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) = (incl F F' n y₀)⁻¹ * nrm s δ * incl F F' n y₀ := by
  unfold nrm nrmG
  set c := incl F F' n y₀
  set L := List.range (Module.finrank F F')
  have h : ∀ i : ℕ, galAct F F' n (s ^ i) (c⁻¹ * δ * c) =
      MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ) := by
    intro i
    rw [map_mul, map_mul, map_inv, galAct_incl, MulAut.conj_apply, inv_inv]
  simp only [h]
  have e := map_list_prod (MulAut.conj c⁻¹) (L.map fun i => galAct F F' n (s ^ i) δ)
  rw [List.map_map] at e
  rw [show (fun i => MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ)) =
    (⇑(MulAut.conj c⁻¹) ∘ fun i => galAct F F' n (s ^ i) δ) from rfl, ← e, MulAut.conj_apply, inv_inv]

theorem count {G₀ G : Type} [Group G₀] [Group G] [Finite G₀] [Finite G] (ι : G₀ →* G)
    (H : Subgroup G) (T : G → ℂ) (hT : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) :
    (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) :=
  GlobalTheory.T.card_comap_mul_finsum_eq_finsum_fibres G₀ G ι H T hT

theorem blocks_twist {F : Type} [Field F] (t : F →+* F) (a b n : ℕ) (hn : n = a + b)
    (p x : GL (Fin n) F) (hp : InPar a p) (hx : InPar a x) :
    tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧
    brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) :=
  GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular F t a b n hn p x hp hx

theorem inPar_conj_adjoin {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ)
    (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hP : InPar a (y₀⁻¹ * γ * y₀)) : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) :=
  GlobalTheory.T.inPar_conj_of_mem_adjoin_incl_of_inPar_conj F F' a n γ y₀ δ hA hP

theorem term (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) (y₀ : GL (Fin n) F) (p : GL (Fin n) F') (hp : InPar a p) :
    (if InPar a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)) then
      shLift s α (tlG a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p))) *
      shLift s β (brG a b ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)))
      else 0) =
    (if InPar a (y₀⁻¹ * γ * y₀) then α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0) := by
  have hle : a ≤ n := by omega
  obtain ⟨H, π, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  obtain ⟨H₀, π₀, hH₀, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  set c := incl F F' n y₀ with hc
  set δ₁ := c⁻¹ * δ * c with hδ₁def
  have hgc : gal (s : F' →+* F') n c = c := galAct_incl n s y₀
  have key : (c * p)⁻¹ * δ * gal (s : F' →+* F') n (c * p) = p⁻¹ * δ₁ * gal (s : F' →+* F') n p := by
    rw [map_mul, hgc, hδ₁def]; group
  by_cases h1 : InPar a (y₀⁻¹ * γ * y₀)
  · rw [key]
    have hδ₁ : InPar a δ₁ := inPar_conj_adjoin a n γ y₀ δ hA h1
    have hin : InPar a (p⁻¹ * δ₁ * gal (s : F' →+* F') n p) := by
      rw [← hH]
      exact H.mul_mem (H.mul_mem (H.inv_mem ((hH p).2 hp)) ((hH _).2 hδ₁))
        ((hH _).2 (inPar_gal _ a n p hp))
    rw [if_pos hin, if_pos h1]
    obtain ⟨et, eb⟩ := blocks_twist (s : F' →+* F') a b n hn p δ₁ hp hδ₁
    have hN₁ : nrm s δ₁ = incl F F' n (y₀⁻¹ * γ * y₀) := by
      rw [hδ₁def, nrm_conj_incl, hN, map_mul, map_mul, map_inv]
    obtain ⟨nt, nb⟩ := GlobalTheory.T.galoisTwistedNormGL_diagonal_blocks F F' s hs a b n hn _ δ₁ h1 hδ₁ hN₁
    have lα := GlobalTheory.T.base_change_lift_class_function F F' s hs a α hα
    have lβ := GlobalTheory.T.base_change_lift_class_function F F' s hs b β hβ
    rw [et, eb]
    have eα := lα.2 (tlG a δ₁) (tlG a p)
    have eβ := lβ.2 (brG a b δ₁) (brG a b p)
    rw [galAct_apply] at eα eβ
    rw [eα, eβ, lα.1 _ _ (by unfold IsNorm; rw [nt]), lβ.1 _ _ (by unfold IsNorm; rw [nb])]
  · rw [if_neg h1, if_neg]
    intro hin
    obtain ⟨y₁, p₁, hp₁, e, hγ₁⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n hle γ δ (c * p) hA hN).1 hin
    have hh : incl F F' n (y₁⁻¹ * y₀) = p₁ * p⁻¹ := by
      rw [map_mul, map_inv, ← hc, show c = incl F F' n y₁ * p₁ * p⁻¹ by rw [← e]; group]
      group
    have hP : InPar a (y₁⁻¹ * y₀) := by
      rw [← inPar_incl (F' := F'), hh, ← hH]
      exact H.mul_mem ((hH _).2 hp₁) (H.inv_mem ((hH _).2 hp))
    apply h1
    have : y₀⁻¹ * γ * y₀ = (y₁⁻¹ * y₀)⁻¹ * (y₁⁻¹ * γ * y₁) * (y₁⁻¹ * y₀) := by group
    rw [this, ← hH₀]
    exact H₀.mul_mem (H₀.mul_mem (H₀.inv_mem ((hH₀ _).2 hP)) ((hH₀ _).2 hγ₁)) ((hH₀ _).2 hP)

theorem pointwise (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) :
    hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n δ = hc a b α β n γ := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  obtain ⟨H, -, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  set T : GL (Fin n) F' → ℂ := fun y => if InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) then
      shLift s α (tlG a (y⁻¹ * δ * gal (s : F' →+* F') n y)) *
      shLift s β (brG a b (y⁻¹ * δ * gal (s : F' →+* F') n y)) else 0 with hTdef
  set c₀ : GL (Fin n) F → ℂ := fun y₀ => if InPar a (y₀⁻¹ * γ * y₀) then
      α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0 with hc₀
  have hsupp : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = incl F F' n k * p := by
    intro y hy
    have hin : InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) := by
      by_contra h; exact hy (if_neg h)
    obtain ⟨k, p, hp, e, -⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n (by omega) γ δ y hA hN).1 hin
    exact ⟨k, p, (hH p).2 hp, e⟩
  have hcnt := count (incl F F' n) H T hsupp
  have hterm : ∀ k (p : H), T (incl F F' n k * p) = c₀ k := fun k p =>
    term F F' s hs a b n hn α β hα hβ γ δ hA hN k p ((hH p).1 p.2)
  simp only [hterm] at hcnt
  have e1 : Nat.card (H.comap (incl F F' n)) = Nat.card {p : GL (Fin n) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [Subgroup.mem_comap, hH, inPar_incl])
  have e2 : Nat.card H = Nat.card {p : GL (Fin n) F' // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hH x)
  have hpos1 : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    rw [← e1]; exact_mod_cast (Nat.card_pos (α := H.comap (incl F F' n))).ne'
  have hpos2 : (Nat.card {p : GL (Fin n) F' // InPar a p} : ℂ) ≠ 0 := by
    rw [← e2]; exact_mod_cast (Nat.card_pos (α := H)).ne'
  haveI := Fintype.ofFinite H
  have hconst : ∀ k, ∑ᶠ _p : H, c₀ k = (Nat.card H : ℂ) * c₀ k := by
    intro k; rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  simp only [hconst] at hcnt
  rw [← mul_finsum] at hcnt
  have hhc : hc a b α β n γ = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ * ∑ᶠ y₀, c₀ y₀ := by
    simp only [hc, hcTw, gal_id, hc₀]
  rw [hhc, e1, e2] at *
  unfold hcTw
  rw [← hTdef]
  field_simp
  linear_combination hcnt

end GlobalTheory.Shin.LiftHc

theorem GlobalTheory.Shin.shLift_hc_eq_hcTw : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  intro F F' _ _ _ _ s hs a b n hn α β hα hβ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  funext δ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  obtain ⟨y, hyA, hyN⟩ := GlobalTheory.T.conjugate_into_adjoined_algebra F F' s hs n δ γ hγ
  have hcl := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) a b n α β).2.1
  have hL := (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).2 δ y
  have hR := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F' (s : F' →+* F') a b n (shLift s α) (shLift s β)).1 δ y
  rw [← hL, ← hR, (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).1 _ γ (by unfold IsNorm; rw [hyN])]
  exact (GlobalTheory.Shin.LiftHc.pointwise F F' s hs a b n hn α β hα hβ γ _ hyA hyN).symm
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem shLift_isometry : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f f' : GL (Fin n) F → ℂ), IsCl f → IsCl f' →
    (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ δ, shLift s f δ * star (shLift s f' δ) =
      (Nat.card (GL (Fin n) F') : ℂ) * ∑ᶠ γ, f γ * star (f' γ) := by
  intro F F' _ _ _ _ s hs n f f' hf hf'
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  letI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  letI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  have hex := GlobalTheory.T.every_element_is_norm F F' s hs n
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hlf := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f hf).1
  have hlf' := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f' hf').1
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  obtain ⟨c, hc⟩ : ∃ c : GL (Fin n) F → ℂ, ∀ γ, c γ = (Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} : ℂ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GL (Fin n) F → ℂ, ∀ γ, v γ = f γ * star (f' γ) := ⟨_, fun _ => rfl⟩
  have hcne : ∀ γ, c γ ≠ 0 := by
    intro γ
    rw [hc, Nat.cast_ne_zero]
    haveI : Nonempty {γ' : GL (Fin n) F // IsConj γ γ'} := ⟨⟨γ, IsConj.refl γ⟩⟩
    exact Nat.card_pos.ne'

  have hclass : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∀ γ' : GL (Fin n) F, IsNorm s δ γ' ↔ IsConj γ γ' := by
    intro δ γ h γ'
    unfold IsNorm at *
    constructor
    · intro h'
      exact hnd γ γ' (IsConj.trans h (IsConj.symm h'))
    · intro h'
      exact IsConj.trans (IsConj.symm (MonoidHom.map_isConj (incl F F' n) h')) h
  have hcard : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → c γ = ((Finset.univ.filter fun γ' => IsNorm s δ γ').card : ℂ) := by
    intro δ γ h
    rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    ext γ'
    simp [hclass δ γ h γ']
  have key : ∀ δ : GL (Fin n) F',
      (∑ γ, if IsNorm s δ γ then v γ / c γ else 0) = shLift s f δ * star (shLift s f' δ) := by
    intro δ
    obtain ⟨γ0, h0⟩ := hex δ
    have e : ∀ γ, (if IsNorm s δ γ then v γ / c γ else 0) =
        if IsNorm s δ γ then (shLift s f δ * star (shLift s f' δ)) / c γ0 else 0 := by
      intro γ
      split_ifs with h
      · rw [hv, hcard δ γ h, ← hcard δ γ0 h0, hlf δ γ h, hlf' δ γ h]
      · rfl
    rw [Finset.sum_congr rfl (fun γ _ => e γ), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, ← hcard δ γ0 h0]
    field_simp [hcne γ0]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have lhs : (∑ δ, shLift s f δ * star (shLift s f' δ)) =
      ∑ γ, ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ) := by
    rw [← Finset.sum_congr rfl (fun δ _ => key δ), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [lhs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  have h := hfib γ
  rw [Nat.card_eq_fintype_card (α := {δ : GL (Fin n) F' // IsNorm s δ γ}), Fintype.card_subtype] at h
  have h' : (Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) =
      c γ * (Nat.card (GL (Fin n) F') : ℂ) := by
    rw [hc]
    exact_mod_cast (by rw [mul_comm]; exact h)
  rw [show (Nat.card (GL (Fin n) F) : ℂ) * (((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ)) =
      ((Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ)) * v γ / c γ by ring,
    h', hv]
  field_simp [hcne γ]

end GlobalTheory.Shin

end
end
