module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle160
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem exists_thG_of_symLift (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen) (k : ℕ) (T' : Over S)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T')) (y : T' ⟶ P.A) (hy : y ^ (k ^ 2) = 1)
    (U : ThetaGrp P.A P.L ((k ^ 2 : ℕ) : ℤ) T') (hU : SymLift P.A P.L ((k ^ 2 : ℕ) : ℤ) (k ^ 2) y U) :
    ∃ c, ThG P.A P.L ρ k th y c := by
  have hL := P.isLB
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P k
  have e₁ : (snd T' P.A).left ≫ (mulA P.A k).left = (snd T' P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T' P.A).left, (snd T' P.A ^ k).left])
    (ε' := ![((k ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow k 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T' P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) (ε' := fun _ => ((k ^ 2 : ℕ) : ℤ))
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T').left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T' k) (snd T' P.A ^ k) (lift_snd _ _)
    ((k ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  obtain ⟨s₂, hs₂⟩ := ThetaPtExist.exists_isTwistPull hL (translT P.A U.pt) (translPt P.A U.pt) (lift_snd _ _)
    ((k ^ 2 : ℕ) : ℤ) ((k ^ 2 : ℕ) : ℤ) U.φ U.isGen s₁
  obtain ⟨w, hw⟩ := ThetaPtExist.exists_isValueAt hL s₂ 1 τ hτ
  obtain ⟨e, he⟩ := exists_thG hL hρ k _ rfl (x := fun _ : Unit => y) (fun _ => hy) (th := th) (α := α)
    (U := fun _ => U) (s₂ := fun _ => s₂) (w := fun _ => w) hα hτ hs₁ (fun _ => hU) (fun _ => hs₂) (fun _ => hw)
  exact ⟨_, he ()⟩

theorem exists_thG_of_polFib_field : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (F : Type) [Field F] (x : Sp F ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : F) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : F, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let T := baseOver (Sp K)
  let τ : T.left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = T.hom ≫ x := rfl
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hu : IsUnit (m : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast e]
    exact (IsUnit.mk0 _ hK).map e
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨z₀⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨V, hV, U, hU⟩ := (hLaw.symLift _ P (m ^ 2) hm.pow (by rw [Nat.cast_pow]; exact hu.pow 2) T q hqm).1 z₀
  obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ => by rwa [Subsingleton.elim y z₀]
  let T' : Over (Sp K) := overRes (T := T) ⊤
  let j₀ : T' ⟶ T := overResι (T := T) ⊤
  haveI : IsIso j₀.left := inferInstanceAs (IsIso (Sp K).topIso.hom)
  let τ' : T'.left ⟶ (Over.mk x).left := j₀.left ≫ τ
  have hτ' : τ' ≫ (Over.mk x).hom = T'.hom ≫ x := by
    rw [Category.assoc, hτ, ← Category.assoc, Over.w j₀]
  have hq' : τ' ≫ p.left = (j₀ ≫ q).left ≫ α := by
    rw [Category.assoc, hq, Over.comp_left, Category.assoc]
  have hqm' : (j₀ ≫ q) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hqm, MonObj.comp_one]
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp τ' hτ' hw hL hL₁ θ
  obtain ⟨c, hc⟩ := exists_thG_of_symLift hLaw P hρ' m T' th (j₀ ≫ q) hqm' U hU
  have up := ThG.up hp τ' hτ' hw hL hL₁ hr hq' hpm hrel hc
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from (CategoryTheory.inv τ').appTop.hom c), ?_⟩
  convert up using 1
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply _

end GlobalTheory.UMin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_unit_of_prim : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (e : Fin N → FractionRing V), Prim (io.comp (algebraMap V (FractionRing V))) c → (∀ j, io (e j) = symTup c j) → ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro V K _ _ _ _ _ io N c e hP he
  set i := io.comp (algebraMap V (FractionRing V)) with hi
  have hio : Function.Injective io := io.injective
  have hinj : Function.Injective i := hio.comp (IsFractionRing.injective V (FractionRing V))
  letI : Algebra V K := i.toAlgebra
  have hcI : ∀ a, IsIntegral V (c a) := hP.1
  have hsI : ∀ j, IsIntegral V (symTup c j) := by
    intro j
    have : symTup c j ∈ integralClosure V K := by
      unfold symTup
      refine Subalgebra.pow_mem _ ?_ _
      rw [Finset.esymm_map_val]
      exact Subalgebra.sum_mem _ fun t _ => Subalgebra.prod_mem _ fun b _ => hcI b
    exact this
  let φ : FractionRing V →ₐ[V] K := { io with commutes' := fun r => rfl }
  have heI : ∀ j, IsIntegral V (e j) := fun j =>
    (isIntegral_algHom_iff φ hio).1 (by rw [show φ (e j) = io (e j) from rfl, he j]; exact hsI j)
  choose e' he' using fun j => IsIntegrallyClosed.isIntegral_iff.1 (heI j)
  refine ⟨e', he', ?_⟩
  obtain ⟨a₀, hc0, hinv⟩ := hP.2
  obtain ⟨W, hle⟩ := (LocalSubring.range i).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hle
  have memW : ∀ x : K, i.IsIntegralElem x → x ∈ W := by
    intro x ⟨p, hp, hx⟩
    have : IsIntegral W x := by
      let g : V →+* W := i.codRestrict W (fun v => hle ⟨v, rfl⟩)
      refine ⟨p.map g, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]; exact hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [← hy]; exact y.2
  have hcW : ∀ a, c a ∈ W := fun a => memW _ (hP.1 a)
  have hc0W : (c a₀)⁻¹ ∈ W := memW _ hinv
  let y : Fin N → W := fun a => ⟨c a * (c a₀)⁻¹, mul_mem (hcW a) hc0W⟩
  have hy0 : y a₀ = 1 := Subtype.ext (mul_inv_cancel₀ hc0)
  obtain ⟨k, hk1, hkN, hu⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) y a₀ hy0
  rw [Fintype.card_fin] at hkN
  set E := (Finset.univ.val.map y).esymm k with hE
  let u0 : W := ⟨c a₀, hcW a₀⟩
  have hu0 : IsUnit u0 := isUnit_iff_exists_inv.2 ⟨⟨(c a₀)⁻¹, hc0W⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩
  let Z : W := (u0 ^ k * E) ^ (N.factorial / k)
  have hZ : IsUnit Z := ((hu0.pow k).mul hu).pow _
  let j : Fin N := ⟨k - 1, by omega⟩
  have hjk : (j : ℕ) + 1 = k := by simp only [j]; omega
  have hZj : (Z : K) = i (e' j) := by
    have : i (e' j) = io (e j) := by rw [hi, RingHom.comp_apply, he' j]
    rw [this, he j]
    simp only [Z, symTup, hjk, hE, Finset.esymm_map_val]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.1 ht).2.symm, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [y, u0]
    field_simp
  refine ⟨j, ?_⟩
  have hmem : i (e' j) ∈ (LocalSubring.range i).toSubring := ⟨e' j, rfl⟩
  have h1 : IsUnit (Subring.inclusion hle ⟨i (e' j), hmem⟩) := by
    have h0 : Subring.inclusion hle ⟨i (e' j), hmem⟩ = Z := by apply Subtype.ext; exact hZj.symm
    rw [h0]; exact hZ
  obtain ⟨u, hu'⟩ := hloc.map_nonunit _ h1
  obtain ⟨w, hw⟩ := ((u⁻¹ : Units _) : (LocalSubring.range i).toSubring).2
  refine isUnit_iff_exists_inv.2 ⟨w, hinj ?_⟩
  have h3 : ((u : (LocalSubring.range i).toSubring) : K) * (((u⁻¹ : Units _) : (LocalSubring.range i).toSubring) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [map_mul, map_one, hw, ← h3, hu']

end GlobalTheory.UMin
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.TorsList

theorem card_torsion_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {g : ℕ} {K : Type} [Field K]
    {x : Sp K ⟶ S} (hx : PolFib G L g x) {k : Type} [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp K) {n : ℕ}
    (hn : (n : k) ≠ 0) : Nat.card {p : Over.mk (t ≫ x) ⟶ G // p ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨P, α, hg, h, -⟩ := hx
  subst hg
  rw [← GlobalTheory.TorsionCover.card_torsion P.A P.isAb P.smoothDim t hn]
  let Φ := GlobalTheory.ObjPull.pushEquiv h (Over.mk t)
  exact (Nat.card_congr (Φ.toEquiv.subtypeEquiv fun y => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow]; rfl)).symm

theorem exists_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  intro S G _ _ L g m K _ _ x hm hx
  have hpow : (m ^ 2) ^ (2 * g) = m ^ (4 * g) := by rw [← pow_mul]; congr 1; ring
  have hm2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hc : Nat.card {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} = m ^ (4 * g) := by
    have := card_torsion_comp G L hx (𝟙 (Sp K)) hm2
    rw [Category.id_comp, hpow] at this
    exact this
  have hfin : Finite {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hm0)
  let e := Finite.equivFinOfCardEq hc
  refine ⟨fun a => (e.symm a).1, fun a b hab => e.symm.injective (Subtype.ext hab), fun a => (e.symm a).2, ?_⟩
  intro K' _ _ i p hp
  have hm' : ((m ^ 2 : ℕ) : K') ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hm2
  have hc' := card_torsion_comp G L hx (spMap i) hm'
  rw [hpow] at hc'
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hepi : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  let F : {q : Over.mk x ⟶ G // q ^ (m ^ 2) = 1} → {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    fun q => ⟨preHom u q.1, by rw [← map_pow, q.2, map_one]⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have h1 : spMap i ≫ a.1.left = spMap i ≫ b.1.left := congrArg (fun z => (Subtype.val z).left) hab
    exact (cancel_epi (spMap i)).1 h1
  have hfin' : Finite {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ hm0)
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hF, by rw [hc, hc']⟩).2 ⟨p, hp⟩
  refine ⟨e q, ?_⟩
  show p.left = spMap i ≫ (e.symm (e q)).1.left
  rw [Equiv.symm_apply_apply]
  exact (congrArg (fun z => (Subtype.val z).left) hq).symm

end GlobalTheory.UMin.TorsList
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.TorsionList

theorem pow_exp (n k : ℕ) (c : Multiplicative (Fin k → ZMod n)) : c ^ n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem pushHom_bij {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ?_), fun y => ?_⟩
  · exact (Over.w x).trans (Over.w y).symm
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem spMap_comp_assoc {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] {X : Scheme.{0}}
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (y : Sp A ⟶ X) :
    spMap (h.comp g) ≫ spMap f ≫ y = spMap h ≫ spMap (g.comp f) ≫ y := by
  simp only [spMap_comp, Category.assoc]

abbrev lft {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (p : Over.mk a ⟶ G) : X ⟶ G.left := p.left

theorem pow_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (y : Over.mk b ⟶ G) (hx : lft x = lft y) (n : ℕ) : lft (x ^ n) = lft (y ^ n) := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem one_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    lft (1 : Over.mk a ⟶ G) = lft (1 : Over.mk b ⟶ G) := by
  subst h
  rfl

theorem transport {S X : Scheme.{0}} {G : Over S} {a b : X ⟶ S} (h : a = b) (p : Over.mk b ⟶ G) :
    ∃ p' : Over.mk a ⟶ G, lft p' = lft p := by
  subst h
  exact ⟨p, rfl⟩

theorem lft_pushHom {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {X : Scheme.{0}} (t : X ⟶ S') (y : Over.mk t ⟶ A') :
    lft (pushHom h (Over.mk t) y) = y.left ≫ φ := rfl

theorem toUnit_mk_left {X Y : Scheme.{0}} (f : Y ⟶ X) : (toUnit (Over.mk f)).left = f :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk f)))

theorem toUnit_left {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

theorem exists_cover_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ (∀ a, q a ^ (m ^ 2) = 1) ∧ ∀ (K : Type) [Field K] (i₁ : R₁ →+* K) (pt : Fin N → (Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G)), (∀ a, (pt a).left = spMap i₁ ≫ (q a).left) → Function.Injective pt ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i' : K →+* K') (p : Over.mk (spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i' ≫ (pt a).left := by
  intro S G _ _ L g m N R _ _ x hm hmu hN hP
  obtain ⟨P, α, hg, hp, -⟩ := hP
  haveI := P.isAb.comm
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  haveI : NeZero (m ^ 2) := ⟨pow_ne_zero _ hm0⟩
  have hsm : SmoothOfRelativeDimension g P.A.hom := hg ▸ P.smoothDim
  have hu : IsUnit (((m ^ 2 : ℕ)) : R) := by rw [Nat.cast_pow]; exact hmu.pow 2
  obtain ⟨R₁, _, _, ⟨hfin, -, hff⟩, H⟩ :=
    GlobalTheory.TorsionCover.exists_torsion_basis_cover R P.A g (m ^ 2) P.isAb hsm hu
  let b := spMap (algebraMap R R₁)
  let A₁ := (Over.pullback b).obj P.A
  haveI : IsCommMonObj A₁ := Functor.isCommMonObj_obj
  have h₁ := isGrpPullback_pullback P.A b
  obtain ⟨ψ, hψ⟩ := H A₁ _ h₁
  have hc := h₁.comp hp
  have hcard : Fintype.card (Multiplicative (Fin (2 * g) → ZMod (m ^ 2))) = N := by
    rw [hN]
    simp [Fintype.card_fun, ZMod.card, ← pow_mul]
    ring_nf
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let U : Over.mk (b ≫ x) ⟶ Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ b ≫ x) := Over.homMk (𝟙 _) (by simp)
  let Q := (preHom (G := G) U).comp ((pushHom hc (𝟙_ (Over (Sp R₁)))).comp ψ)
  have hQ : ∀ c, (Q c).left = (ψ c).left ≫ pullback.fst P.A.hom b ≫ α := fun c => by
    simp [Q, U, pushHom, pushPt, preHom]
  refine ⟨R₁, inferInstance, inferInstance, fun a => Q (e a), hfin, hff, fun a => by
    rw [← map_pow, pow_exp, map_one], ?_⟩
  intro K _ i₁ pt hpt
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁) c d,
      t ≫ (Q c).left = t ≫ (Q d).left → c = d := by
    intro k _ _ t c d h
    have hinj : Function.Injective ((preHom (G := A₁) (toUnit (Over.mk t))).comp ψ) := by
      rw [injective_iff_map_eq_one]
      exact fun c hc => (hψ k t).2 c hc
    apply hinj
    apply Over.OverMorphism.ext
    show (toUnit (Over.mk t) ≫ ψ c).left = (toUnit (Over.mk t) ≫ ψ d).left
    rw [Over.comp_left, Over.comp_left, toUnit_left]
    apply hc.1.hom_ext
    · rw [hQ, hQ] at h
      simpa [Category.assoc] using h
    · have e1 := Over.w (ψ c)
      have e2 := Over.w (ψ d)
      simp only [Category.assoc]
      erw [e1, e2]
  refine ⟨fun a a' h => ?_, ?_⟩
  · have h' := congrArg (fun z => z.left) h
    simp only [hpt] at h'
    let k := AlgebraicClosure K
    have := key k (spMap ((algebraMap K k).comp i₁)) (e a) (e a') (by
      rw [spMap_comp, Category.assoc, Category.assoc]; exact congrArg (spMap (algebraMap K k) ≫ ·) h')
    exact e.injective this
  · intro K' _ _ i' p hp2
    have ht : spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x = spMap (i'.comp i₁) ≫ b ≫ x :=
      (spMap_comp_assoc (algebraMap R R₁) i₁ i' x).symm
    obtain ⟨p', hp'⟩ := transport ht.symm p
    obtain ⟨p₁, hp₁⟩ := (pushHom_bij hc (Over.mk (spMap (i'.comp i₁)))).2 p'
    have hk : p₁ ^ (m ^ 2) = 1 := by
      apply (pushHom_bij hc _).1
      rw [map_pow, hp₁, map_one]
      apply Over.OverMorphism.ext
      change lft _ = lft _
      rw [pow_lft_congr ht.symm p' p hp', hp2]
      exact one_lft_congr ht
    obtain ⟨c, rfl⟩ := ((hψ K' _).1 p₁).1 hk
    refine ⟨e.symm c, ?_⟩
    rw [hpt]
    simp only [Equiv.apply_symm_apply]
    change lft p = _
    have h2 := congrArg lft hp₁
    rw [← hp', ← h2, lft_pushHom, hQ, Over.comp_left, toUnit_mk_left, spMap_comp]
    simp only [Category.assoc]

end GlobalTheory.UMin.TorsionList
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (P.H (e * q + a) b).FG ∧ Module.finrank ℤ (P.H (e * q + a) b) ≤ Module.finrank (ratF x) X.functionField * (q + c + D).choose D ∧ ∀ R κ : ℝ, 0 ≤ R → 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (P.Bl (e * q + a) b R).Finite ∧ (P.Bl (e * q + a) b R).ncard ≤ (2 * ⌊C * R / κ ^ (q + c)⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + c + D).choose D) := by
  first | exact @GlobalTheory.HSAmp.HSUpper.upper_bound | exact GlobalTheory.HSAmp.HSUpper.upper_bound | (intros; apply GlobalTheory.HSAmp.HSUpper.upper_bound <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.homogeneousNormFactor_flatLine_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (τ : Psi H) (k : U.Comp) (w : (U.X k).dom), (U.X k).IsOrtho w.1 → GlobalTheory.CompHS.homFac U x (flatWt Dw τ) k w = Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) := by
  first | exact @GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho | exact GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho | (intros; apply GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem dbarCoh_chernFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ j, DbarCoh A (chernFld A G j) (chernFld A G' j) := by
  intro M _ n A r _ _ G G' hG j
  obtain ⟨h1, -, halg⟩ := GlobalTheory.T.dbarCohomologousEvenForms_algebra_closed M n A
  have hpow := GlobalTheory.T.curvaturePowerSums_dbarCohomologous M n A r G G' hG
  have hzero : DbarCoh A 0 0 := by
    have := (halg 0 1 1 1 1 h1 h1).1
    simpa using this
  have hsum : ∀ (s : Finset ℕ) (w w' : ℕ → A.Pt → Ev n), (∀ i ∈ s, DbarCoh A (w i) (w' i)) →
      DbarCoh A (∑ i ∈ s, w i) (∑ i ∈ s, w' i) := by
    intro s w w' h
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (halg 0 _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).2.1
  have key : ∀ (H : M → M → Matrix r r ℂ) (j : ℕ), 0 < j → chernFld A H j = (j : ℂ)⁻¹ • ((-1 : ℂ) •
      ∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powFld A H (i + 1) * chernFld A H (j - 1 - i))) := by
    intro H j hj
    funext x
    have := (GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r (fun v => H x.pt (x.ch.symm v)) x.crd).2 j
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, chernFld, powFld, HolAtlas.chern]
    rw [neg_one_smul, ← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hj.ne'), one_smul]
  have key0 : ∀ H : M → M → Matrix r r ℂ, chernFld A H 0 = 1 := by
    intro H; funext x
    exact (GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r _ x.crd).1
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [key0, key0]; exact h1
    · rw [key G j hj, key G' j hj]
      refine (halg _ _ _ _ _ ?_ h1).1
      refine (halg _ _ _ _ _ ?_ h1).1
      refine hsum _ _ _ fun i hi => ?_
      refine (halg _ _ _ _ _ ?_ h1).1
      exact (halg 0 _ _ _ _ (hpow (i + 1)) (ih _ (by simp at hi; omega))).2.2

end GlobalTheory.ChernCalc
end
