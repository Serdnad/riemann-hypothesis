module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bLev_of :
    LatB → EtaPtB → UpperTheory.Gal.crystallineComparison.Mod.EtInj → BLev := by
  intro hLat hEta hInj p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hle hb _ h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂
    C₁ C₂ W f mf _ e _ _ Tj P Ω _ _ x x' hj hy
  have atq' : AtPrime D q r 𝔴' := { S.atq with max := hmax, le := hle }
  refine hInj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M 𝔟₂ 1 X₂.Y X₂.π X₂.ov X₂.mπ _ _ _ ?_ ?_
  · have e₁ : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ X₂.π = z ≫ P.y ≫ Tj.t := fun z => by
      rw [P.yt]; simp only [Category.assoc]
    rw [e₁, e₁, reassoc_of% hy]
  · intro y₀
    obtain ⟨x₀, v, hv, e₀⟩ := hLat p D G L q r 𝔴' 𝔟₁ 𝔟₂ i h atq' htj hint hb X₁.lev.2.2.2.2 M₁ M₂ a₁ a₂ n₁.2 n₂.2 y₀
    have key : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ (X₂.Y.lv y₀).left ≫ X₂.mπ.φ =
        (z ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa) ≫ Tj.ψ.left ≫ Tj.mt.φ := fun z => by
      have h1 := congrArg (fun g => g.left) (hEta p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω z
        (algebraMap (𝓞 D.F) D.O a₁ • x₀) (algebraMap (𝓞 D.F) D.O a₂ • y₀) ⟨v, hv, e₀⟩)
      have ht : (toUnit (Over.mk z)).left = z := by simpa using Over.w (toUnit (Over.mk z))
      simp only [Over.comp_left, ht] at h1
      have h2 := W.φ.eta (algebraMap (𝓞 D.F) D.O a₂ • y₀)
      have h3 := C₂.lv y₀
      simp only [Category.assoc]
      rw [reassoc_of% P.sq, P.mt, reassoc_of% h1, reassoc_of% h2, reassoc_of% h3]
    have sec : ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ (T.M M₁).univ.A.hom = 𝟙 _ := by
      simpa using Over.w ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀))
    have hA : x ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa =
        x' ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa := by
      refine Tj.ms.cart.1.hom_ext ?_ ?_
      · have h4 := C₁.lv x₀
        simp only [Category.assoc]
        rw [P.ms, reassoc_of% h4, reassoc_of% hj]
      · simp only [Category.assoc]
        rw [P.ca.1.w, reassoc_of% sec, hy]
    rw [key x, key x', hA]
end

section

set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Form

variable {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)

private lemma skew (alt : ∀ x, B x x = 0) (x y : M) : B x y = - B y x := by
  have h := alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, alt x, alt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

private lemma bezout {e n : ℕ} (hc : e.Coprime n) : ∃ a b : ℤ, a * e + b * n = 1 :=
  Nat.isCoprime_iff_coprime.2 hc

private lemma first {n e : ℕ} (hn : 0 < n) (hc : e.Coprime n) (nd : Function.Injective B)
    (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (x : M) (h : ∀ y, (n : ℤ) ∣ B x y) :
    ∃ z, x = n • z := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let f : M →ₗ[ℤ] ℤ :=
    { toFun := fun y => B x y / n
      map_add' := fun y y' => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_right (h y')
      map_smul' := fun c y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (h y) }
  have hf : ∀ y, (n : ℤ) * f y = B x y := fun y => Int.mul_ediv_cancel' (h y)
  obtain ⟨w, hw⟩ := perf f
  have key : n • w = e • x := by
    apply nd
    ext y
    simp only [map_nsmul, LinearMap.smul_apply, hw, nsmul_eq_mul, ← hf]
    ring
  have key' : (e : ℤ) • x = (n : ℤ) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]
  refine ⟨a • w + b • x, ?_⟩
  calc x = ((a * e + b * n : ℤ)) • x := by rw [hab, one_smul]
    _ = a • ((e : ℤ) • x) + b • ((n : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = n • (a • w + b • x) := by
      rw [key', ← Nat.cast_smul_eq_nsmul ℤ n, smul_add, smul_comm a, smul_comm b]

private lemma second {n e : ℕ} (hc : e.Coprime n) (nd : Function.Injective B)
    (alt : ∀ x, B x x = 0) (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (h : M →+ M) :
    ∃ k : M →+ M, ∀ x y, (n : ℤ) ∣ B (h x) y - B x (k y) := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let F : M → M →ₗ[ℤ] ℤ := fun y => (B.flip y) ∘ₗ h.toIntLinearMap
  have hF : ∀ y x, F y x = B (h x) y := fun y x => rfl
  choose w hw using fun y => perf (F y)
  have wadd : ∀ y y', w (y + y') = w y + w y' := by
    intro y y'
    apply nd
    ext x
    simp only [map_add (f := _), LinearMap.add_apply, hw, LinearMap.smul_apply, hF, smul_add]
  let k : M →+ M := AddMonoidHom.mk' (fun y => -(a • w y)) (by
    intro y y'
    simp only [wadd, smul_add, neg_add])
  refine ⟨k, fun x y => ?_⟩
  have h1 : B x (k y) = a * (e * B (h x) y) := by
    simp only [k, AddMonoidHom.mk'_apply, map_neg, map_zsmul, smul_eq_mul, skew B alt x (w y), hw,
      LinearMap.smul_apply, hF, nsmul_eq_mul]
    ring
  rw [h1]
  exact ⟨b * B (h x) y, by linear_combination (-(B (h x) y)) * hab⟩

private lemma third {n : ℕ} (hn : 0 < n) [Module.Finite ℤ M] (g : M →+ M)
    (inj : ∀ x z, g x = n • z → ∃ w, x = n • w) (x : M) : ∃ y z, g y = x + n • z := by
  classical
  let N : AddSubgroup M := (nsmulAddMonoidHom n).range
  have memN : ∀ y, y ∈ N ↔ ∃ z, n • z = y := fun y => by
    simp [N, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  have hle : N ≤ N.comap g := by
    intro y hy
    obtain ⟨z, rfl⟩ := (memN y).1 hy
    exact (memN _).2 ⟨g z, (map_nsmul g n z).symm⟩
  let G := QuotientAddGroup.map N N g hle
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (M ⧸ N) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨y, rfl⟩
  have ginj : Function.Injective G := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hu
    obtain ⟨z, hz⟩ := (memN _).1 hu
    obtain ⟨w, hw⟩ := inj y z hz.symm
    rw [QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨w, hw.symm⟩
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.1 ginj (QuotientAddGroup.mk x)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hu
  obtain ⟨z, hz⟩ := (memN _).1 hu
  exact ⟨y, -z, by rw [smul_neg, hz]; abel⟩

end Form

theorem adj : UpperTheory.Gal.FiniteEtaleModels.O.Adj := by
  intro q _ D e
  haveI := D.finLa
  obtain ⟨e', he', perf⟩ := D.perfP
  have hc : e'.Coprime (q ^ e) := Nat.Coprime.pow_right e he'
  have hn : 0 < q ^ e := pow_pos (Fact.out : Nat.Prime q).pos e
  have fst : ∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0 := by
    intro x hx
    obtain ⟨z, hz⟩ := first D.EF hn hc D.nondeg perf x hx
    exact ⟨z, by rw [zero_add]; exact hz⟩
  refine ⟨fst, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := second D.EF hc D.nondeg D.alt perf h.toAddMonoidHom
    refine ⟨k, hk, ?_⟩
    intro c y
    obtain ⟨z, hz⟩ := fst (k (c • y) - c • k y) (by
      intro x
      obtain ⟨b', hb'⟩ : ∃ b', MulOpposite.unop (D.star b') = c := ⟨_, D.star_star c⟩
      have e1 := hk x (c • y)
      have e2 := hk (b' • x) y
      have a1 : D.EF (h.toAddMonoidHom (b' • x)) y = D.EF (h.toAddMonoidHom x) (c • y) := by
        rw [LinearMap.toAddMonoidHom_coe, map_smul, D.adj, hb']
      have a2 : D.EF (b' • x) (k y) = D.EF x (c • k y) := by rw [D.adj, hb']
      rw [a1, a2] at e2
      rw [skew D.EF D.alt, map_sub, dvd_neg]
      have h5 := dvd_sub e2 e1
      rwa [sub_sub_sub_cancel_left] at h5)
    exact ⟨z, by rw [zero_add, sub_eq_iff_eq_add'] at hz; exact hz⟩
  · intro g hg
    have ginj : ∀ x z, g x = (q ^ e) • z → ∃ w, x = (q ^ e) • w := by
      intro x z hz
      apply first D.EF hn hc D.nondeg perf x
      intro y
      have h3 := hg x y
      rw [hz, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h2 : ((q ^ e : ℕ) : ℤ) ∣ ((q ^ e : ℕ) : ℤ) * D.EF z (g y) := dvd_mul_right _ _
      have h4 := dvd_sub h2 h3
      rwa [sub_sub_cancel] at h4
    refine ⟨fun x ⟨z, hz⟩ => ?_, fun x => ?_⟩
    · obtain ⟨w, hw⟩ := ginj x z (by rw [hz, zero_add])
      exact ⟨w, by rw [zero_add]; exact hw⟩
    · obtain ⟨y, z, hyz⟩ := third hn g ginj x
      exact ⟨y, z, hyz⟩

end UpperTheory.Gal.FiniteEtaleModels.O
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.FiniteEtaleModels.O.tExt :
    UpperTheory.Gal.FiniteEtaleModels.O.TExt := by
  intro G R _ _ gb N Ω _ _ σ o I k _ _ x
  obtain ⟨f, rfl⟩ : ∃ f : Ω →+* k, x = spMap f := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  obtain ⟨g, rfl⟩ : ∃ g : R →+* Ω, σ = spMap g := ⟨(Spec.preimage σ).hom, by simp [spMap]⟩
  have hcomp : spMap f ≫ spMap g = spMap (f.comp g) := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨J, -⟩ := o.geom k (spMap f) (f.comp g) hcomp
  haveI := G.finLa
  let h : Over.mk (spMap f) ⟶ Over.mk (𝟙 (Sp Ω)) := Over.homMk (spMap f) (by simp)
  haveI : Epi h := by
    haveI : Epi h.left := (GlobalTheory.UPel.GeometricLevelExistence.epi_spMap_field f : _)
    exact Over.epi_of_epi_left h
  have hadd : ∀ n a b, h ≫ I.ev n (a + b) = (h ≫ I.ev n a) * (h ≫ I.ev n b) := by
    intro n a b
    rw [I.add, MonObj.comp_mul]
  have hker : ∀ n, 0 < n → ∀ a, h ≫ I.ev n a = 1 ↔ ∃ b, a = n • b := by
    intro n hn a
    rw [← I.ker n hn a]
    constructor
    · intro e
      apply (cancel_epi h).1
      rw [e, MonObj.comp_one]
    · intro e
      rw [e, MonObj.comp_one]
  have htors : ∀ n, 0 < n → ∀ a, (h ≫ I.ev n a) ^ n = 1 := by
    intro n hn a
    rw [← MonObj.comp_pow, (I.onto n hn _).2 ⟨a, rfl⟩, MonObj.comp_one]
  refine ⟨{ ζ := fun n => Units.map (f : Ω →* k) (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective f.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n y => h ≫ I.ev n y
            add := hadd
            lin := fun n b a => by
              show h ≫ I.ev n (b • a) = (h ≫ I.ev n a) ≫ o.act.act b
              rw [I.lin, Category.assoc]
            ker := hker
            onto := fun n hn q => by
              constructor
              · intro hq
                obtain ⟨c, rfl⟩ := (J.onto n hn q).1 hq
                obtain ⟨a, ha⟩ := GlobalTheory.UPel.GeometricLevelExistence.exists_eq_of_count n hn (fun a => h ≫ I.ev n a)
                  (J.ev n) (hadd n) (J.add n) (hker n hn) (J.ker n hn)
                  (fun a => (J.onto n hn _).1 (htors n hn a) |>.imp fun c hc => hc.symm) c
                exact ⟨a, ha⟩
              · rintro ⟨a, rfl⟩
                exact htors n hn a
            tower := fun n m hn hm a => by
              show (h ≫ I.ev (n * m) a) ^ m = h ≫ I.ev n a
              rw [← MonObj.comp_pow, I.tower n m hn hm]
            isom := fun n hn a b => by
              have hw := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds o.ab
                (pull_isLB o.isLB _) h (I.isom n hn a b)
              convert hw using 1
              rw [← map_zpow]
              exact (GlobalTheory.UPel.GeometricLevelExistence.unitOn_pull_spMap f _).symm }, fun n hn y => rfl⟩
end
end

section

open NumberField GlobalTheory.UPel.HT

theorem UpperTheory.Gal.FiniteEtaleModels.O.mOne :
    UpperTheory.Gal.FiniteEtaleModels.O.MOne := by
  intro q _ D hm
  haveI := D.freeLa
  haveI := D.finLa
  have hb : Function.Bijective (algebraMap (𝓞 D.F) D.O) :=
    ⟨D.algebraMap_injective hm, Datum.algebraMap_surjective_of_m_eq_one q D hm⟩
  have hfin : Module.Finite D.O D.La := Module.Finite.of_restrictScalars_finite ℤ D.O D.La
  refine ⟨hb, ?_, hfin⟩
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective _ hb
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (r : 𝓞 D.F) (x : D.La), r • x = algebraMap (𝓞 D.F) D.O r • x :=
    fun _ _ => rfl
  haveI : IsScalarTower ℤ (𝓞 D.F) D.La :=
    ⟨fun n r x => by rw [hsmul, hsmul, map_zsmul, smul_assoc]⟩
  have htors : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨r, hr⟩, hx⟩
    have hx' : r • x = 0 := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {r}))
    have hN : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr0
    have hz : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = 0 := by
      have h1 : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x =
          ((Ideal.absNorm (Ideal.span {r}) : ℕ) : 𝓞 D.F) • x := by
        rw [natCast_zsmul]
        exact (Nat.cast_smul_eq_nsmul (𝓞 D.F) _ x).symm
      rw [h1, ← hs, mul_smul, hx', smul_zero]
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hN)
  haveI : Module.Flat (𝓞 D.F) D.La := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htors
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.FinitePresentation (𝓞 D.F) D.La := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 D.F) D.La := Module.Flat.projective_of_finitePresentation
  haveI h1 : RingHomInvPair (e : 𝓞 D.F →+* D.O) (e.symm : D.O →+* 𝓞 D.F) :=
    RingHomInvPair.of_ringEquiv e
  haveI h2 : RingHomInvPair (e.symm : D.O →+* 𝓞 D.F) (e : 𝓞 D.F →+* D.O) :=
    RingHomInvPair.symm _ _
  let f : D.La ≃ₛₗ[(e : 𝓞 D.F →+* D.O)] D.La :=
    { AddEquiv.refl D.La with map_smul' := fun _ _ => rfl }
  exact Module.Projective.of_equiv f
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem exists_geomPoint (P : Scheme.{0}) (p : P) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (t : Sp Ω ⟶ P) (q : Sp Ω), t q = p := by
  refine ⟨AlgebraicClosure (P.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (P.residueField p) (AlgebraicClosure (P.residueField p)))) ≫
      P.fromSpecResidueField p, IsLocalRing.closedPoint _, ?_⟩
  change (P.fromSpecResidueField p) ((Spec.map (CommRingCat.ofHom (algebraMap (P.residueField p)
    (AlgebraicClosure (P.residueField p))))) (IsLocalRing.closedPoint _)) = p
  exact Scheme.fromSpecResidueField_apply p _

private theorem isDominant_genericFibre (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap (algebraMap O E))) := by
  refine ⟨fun x => ?_⟩
  let gp : Sp E := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E)
  have hgp : spMap (algebraMap O E) gp ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O) _ _).1 ?_
    show Ideal.comap (algebraMap O E) ⊥ ≤ _
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective O E)]
    exact bot_le
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hgp
  refine hx'.mem_closed isClosed_closure (subset_closure ?_)
  rw [Scheme.Pullback.range_fst]
  exact ⟨gp, e.symm⟩

private theorem eq_of_geomPoints {P Y B : Scheme.{0}} [IsReduced P] (a b : P ⟶ Y) (g : Y ⟶ B) [IsSeparated g]
    (hab : a ≫ g = b ≫ g)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ P), t ≫ a = t ≫ b) : a = b := by
  let d : P ⟶ pullback g g := pullback.lift a b hab
  let k₀ : pullback d (pullback.diagonal g) ⟶ P := pullback.fst d (pullback.diagonal g)
  have hd₁ : d ≫ pullback.fst g g = a := pullback.lift_fst _ _ _
  have hd₂ : d ≫ pullback.snd g g = b := pullback.lift_snd _ _ _
  have hc : k₀ ≫ d = pullback.snd d (pullback.diagonal g) ≫ pullback.diagonal g := pullback.condition
  have hk : k₀ ≫ a = k₀ ≫ b := by
    have h1 : k₀ ≫ a = pullback.snd d (pullback.diagonal g) := by
      calc k₀ ≫ a = (k₀ ≫ d) ≫ pullback.fst g g := by rw [Category.assoc, hd₁]
        _ = _ := by rw [hc]; simp
    have h2 : k₀ ≫ b = pullback.snd d (pullback.diagonal g) := by
      calc k₀ ≫ b = (k₀ ≫ d) ≫ pullback.snd g g := by rw [Category.assoc, hd₂]
        _ = _ := by rw [hc]; simp
    rw [h1, h2]
  have hsur : Surjective k₀ := ⟨fun p => by
    obtain ⟨Ω, _, _, t, q, rfl⟩ := exists_geomPoint P p
    have hd : t ≫ d = (t ≫ a) ≫ pullback.diagonal g := by
      apply pullback.hom_ext
      · rw [Category.assoc, hd₁]; simp
      · rw [Category.assoc, hd₂, ← h Ω t]; simp
    refine ⟨(pullback.lift t (t ≫ a) hd : Sp Ω ⟶ _) q, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun m : Sp Ω ⟶ P => m q) (pullback.lift_fst _ _ _)⟩
  have : IsDominant k₀ := inferInstance
  exact ext_of_isDominant_of_isSeparated g hab k₀ hk

theorem UpperTheory.Gal.FiniteEtaleModels.descExt_of :
    NormExt → DescExt := by
  intro hN O E _ _ _ _ _ _ V X Y B s σ j ov hs hfin het hgeo f g y hg hy hker
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsLocalization.Away ϖ E := GlobalTheory.Reg.ChartOpens.away_irreducible hϖ
  have : IsOpenImmersion (spMap (algebraMap O E)) := IsOpenImmersion.of_isLocalization ϖ
  let e : Sp E ⟶ Sp O := spMap (algebraMap O E)
  let u : pullback s e ⟶ X := pullback.fst s e
  let j' : V ⟶ pullback s e := pullback.lift j σ ov
  have hj' : j' ≫ u = j := pullback.lift_fst _ _ _
  have hjσ : j' ≫ pullback.snd s e = σ := pullback.lift_snd _ _ _
  have hdom : IsDominant u := isDominant_genericFibre O E s
  have hsurj : Surjective j' := ⟨fun w => by
    obtain ⟨Ω, _, _, t, q, rfl⟩ := exists_geomPoint _ w
    obtain ⟨v, hv₁, hv₂⟩ := hgeo Ω (t ≫ u) (t ≫ pullback.snd s e) (by
      rw [Category.assoc, Category.assoc]
      exact congrArg (t ≫ ·) pullback.condition)
    have hv : v ≫ j' = t := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        change v ≫ j' ≫ u = t ≫ u
        rw [hj', hv₁]
      · rw [Category.assoc, hjσ, hv₂]
    refine ⟨v q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hv]⟩

  have stalk_normal (T : Scheme.{0}) (t : T ⟶ Sp O) [Smooth t] (x : T) :
      IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x) := by
    refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth t (fun q => ?_) x
    haveI : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
    let _ : Algebra O ((Sp O).presheaf.stalk q) := StructureSheaf.stalkAlgebra O q
    have h : IsLocalization.AtPrime ((Sp O).presheaf.stalk q) q.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk O q
    have hle : q.asIdeal.primeCompl ≤ nonZeroDivisors O := q.asIdeal.primeCompl_le_nonZeroDivisors
    have hd : IsDomain ((Sp O).presheaf.stalk q) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
    exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩
  have hsm : Smooth (pullback.fst j' j' ≫ j' ≫ u ≫ s) := inferInstance
  have hred : IsReduced (pullback j' j') := by
    have : ∀ x : (pullback j' j' : Scheme.{0}), _root_.IsReduced ((pullback j' j' : Scheme.{0}).presheaf.stalk x) := fun x => by
      letI : IsDomain ((pullback j' j' : Scheme.{0}).presheaf.stalk x) :=
        (stalk_normal _ (pullback.fst j' j' ≫ j' ≫ u ≫ s) x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hP : pullback.fst j' j' ≫ y = pullback.snd j' j' ≫ y := by
    refine eq_of_geomPoints _ _ g ?_ fun Ω _ _ t => ?_
    · rw [Category.assoc, Category.assoc, hy, ← hj', Category.assoc, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine hker Ω _ _ ?_
      rw [Category.assoc, Category.assoc, ← hj', pullback.condition_assoc]
  have hee : EffectiveEpi j' := inferInstance
  let z : pullback s e ⟶ Y := EffectiveEpi.desc j' y (fun {T} g₁ g₂ h => by
    calc g₁ ≫ y = (pullback.lift g₁ g₂ h ≫ pullback.fst j' j') ≫ y := by rw [pullback.lift_fst]
      _ = (pullback.lift g₁ g₂ h ≫ pullback.snd j' j') ≫ y := by
        rw [Category.assoc, Category.assoc, hP]
      _ = g₂ ≫ y := by rw [pullback.lift_snd])
  have hz : j' ≫ z = y := EffectiveEpi.fac _ _ _
  have hzg : z ≫ g = u ≫ f := by
    rw [← cancel_epi j', ← Category.assoc, hz, hy, ← hj', Category.assoc]
  obtain ⟨y', h₁, h₂⟩ := hN _ X Y B u f g z inferInstance hdom (LocallyOfFiniteType.isLocallyNoetherian s)
    (fun x => (stalk_normal X s x).1)
    (fun x => (stalk_normal X s x).2) hg hzg
  exact ⟨y', by rw [← hj', Category.assoc, h₁, hz], h₂⟩
end
