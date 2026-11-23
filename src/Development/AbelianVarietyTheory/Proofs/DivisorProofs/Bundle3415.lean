module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.LiftWitness

theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem spMap_id (L : Type) [CommRing L] : spMap (RingHom.id L) = 𝟙 _ := by
  simp [spMap]

theorem laurentProd_bijective (B C : Type) [CommRing B] [CommRing C] : Function.Bijective
    ((laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.coeff_injective
    ext n
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h1
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h2
  · rintro ⟨f, g⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk rfl f.coeff g.coeff), ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor <;> (apply AddMonoidAlgebra.coeff_injective; ext n; simp [laurentMap_coeff])


open GlobalTheory.EtC.GmPhiNat in
theorem eq_zero_of_pull_laurent_fst_snd (q : ℕ) (B C : Type) [CommRing B] [CommRing C] (n i : ℤ)
    (z : Ht q (sp (LaurentPolynomial (B × C))) n i)
    (h1 : pull _ (spMap (laurentMap (RingHom.fst B C))) _ n z = 0)
    (h2 : pull _ (spMap (laurentMap (RingHom.snd B C))) _ n z = 0) : z = 0 := by
  let e := (laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))
  let E := RingEquiv.ofBijective e (laurentProd_bijective B C)
  have hinv : E.symm.toRingHom.comp e = RingHom.id _ :=
    RingHom.ext fun x => E.symm_apply_apply x
  have hw : pull _ (spMap e) _ n z = 0 := by
    apply (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q (LaurentPolynomial B) (LaurentPolynomial C) n i).1
    simp only [← pull_spMap_comp, map_zero, e, RingHom.fst_comp_prod, RingHom.snd_comp_prod]
    exact Prod.ext h1 h2
  have := GlobalTheory.EtC.GmPhiNat.pull_spMap_comp q e E.symm.toRingHom n i z
  rw [hinv, spMap_id, pull_id, hw, map_zero] at this
  exact this

theorem surj_prod (q : ℕ) [NeZero q] (B C : Type) [CommRing B] [CommRing C] (hq : IsUnit (q : B × C)) (i : ℤ)
    (hB : Function.Surjective (gmPhi q B i)) (hC : Function.Surjective (gmPhi q C i)) :
    Function.Surjective (gmPhi q (B × C) i) := by
  intro y
  obtain ⟨b, hb⟩ := hB (pull _ (spMap (laurentMap (RingHom.fst B C))) _ 1 y)
  obtain ⟨c, hc⟩ := hC (pull _ (spMap (laurentMap (RingHom.snd B C))) _ 1 y)
  obtain ⟨a, ha⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q B C 0 (i - 1)).2 (b, c)
  simp only [Prod.mk.injEq] at ha
  refine ⟨a, (sub_eq_zero.mp ?_).symm⟩
  apply eq_zero_of_pull_laurent_fst_snd q B C 1 i
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.1, hb, sub_self]
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.2, hc, sub_self]

theorem exists_factor (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (p : Ideal A) [p.IsPrime] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  let D := A ⧸ p
  let Ω := AlgebraicClosure (FractionRing D)
  let T := integralClosure D Ω
  letI : Algebra A T := ((algebraMap D T).comp (Ideal.Quotient.mk p)).toAlgebra
  have hint : Algebra.IsIntegral A T := by
    have h1 : (Ideal.Quotient.mk p).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : (algebraMap D T).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := D) x
    exact ⟨fun x => RingHom.IsIntegral.trans _ _ h1 h2 x⟩
  have hloc : IsLocalRing T := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A T
  have hqT : IsUnit (q : T) := by simpa using hq.map (algebraMap A T)
  refine ⟨T, inferInstance, inferInstance, hint, fun a ha => ?_,
    (GlobalTheory.T.units_cohomology_bijective q T (GlobalTheory.aic_integralClosure_algebraicClosure D) hqT i).2⟩
  have hinjΩ : Function.Injective (algebraMap D Ω) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) Ω]
    exact (algebraMap (FractionRing D) Ω).injective.comp (IsFractionRing.injective D (FractionRing D))
  have hinj : Function.Injective (algebraMap D T) := by
    intro x y h
    exact hinjΩ (congrArg Subtype.val h)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact ha

theorem exists_witness (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (S : Finset (Ideal A)) (hS : ∀ p ∈ S, p.IsPrime) (hne : S.Nonempty) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → ∀ p ∈ S, a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton p =>
    have := hS p (Finset.mem_singleton_self p)
    obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_factor q A hq i p
    exact ⟨B, inferInstance, inferInstance, hint, fun a ha r hr => by
      rw [Finset.mem_singleton] at hr; subst hr; exact hker a ha, hsurj⟩
  | cons p S hp hSne ih =>
    have := hS p (Finset.mem_cons_self p S)
    obtain ⟨B, _, _, hintB, hkerB, hsurjB⟩ := ih fun r hr => hS r (Finset.mem_cons_of_mem hr)
    obtain ⟨C, _, _, hintC, hkerC, hsurjC⟩ := exists_factor q A hq i p
    have hqBC : IsUnit (q : B × C) := by simpa using hq.map (algebraMap A (B × C))
    refine ⟨B × C, inferInstance, inferInstance, inferInstance, fun a ha r hr => ?_,
      surj_prod q B C hqBC i hsurjB hsurjC⟩
    rw [Prod.algebraMap_apply, Prod.mk_eq_zero] at ha
    rcases Finset.mem_cons.1 hr with rfl | hr
    · exact hkerC a ha.2
    · exact hkerB a ha.1 r hr

theorem lift_witness : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
      ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  intro q _ A _ _ hSH hq i x
  obtain ⟨hH, -⟩ := hSH
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hne : hfin.toFinset.Nonempty := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
    exact ⟨p, hfin.mem_toFinset.2 hp⟩
  obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_witness q A hq i hfin.toFinset
    (fun p hp => (hfin.mem_toFinset.1 hp).1.1) hne
  obtain ⟨a', ha'⟩ := hsurj (pull _ (spMap (laurentMap (algebraMap A B))) _ 1 x)
  refine ⟨B, inferInstance, inferInstance, hint, fun a ha => ?_, a', ha'.symm⟩
  rw [RingHom.mem_ker] at ha
  have : a ∈ (⊥ : Ideal A).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.2 fun p hp => hker a ha p (hfin.mem_toFinset.2 hp)
  exact this
end GlobalTheory.EtC.LiftWitness
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem exists_factor (hN : 3 ≤ N) (hNp : N.Coprime p) {S₀ S₁ T : Scheme.{0}} {s₀ : S₀ ⟶ Sp R} {s₁ : S₁ ⟶ Sp R}
    {t : T ⟶ Sp R} {o₀ : Obj b N s₀} {o₁ : Obj b N s₁} {o : Obj b N t} {g : S₁ ⟶ S₀} {h : T ⟶ S₁} {x : T ⟶ S₀}
    (e : h ≫ g = x) (m₁ : ObjMap o₁ o₀ g) (m : ObjMap o o₀ x) : ∃ m' : ObjMap o o₁ h, m'.φ ≫ m₁.φ = m.φ := by
  subst e
  obtain ⟨m'⟩ := GlobalTheory.T.harrisTaylorPullback_comp_factors p D R b N _ _ _ _ _ _ o₀ o₁ o g h m₁ m
  obtain ⟨n, hn⟩ := exists_comp m' m₁
  exact ⟨m', hn.symm.trans (GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n m rfl)⟩

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S) (o : Obj b N s) {s' : S' ⟶ Sp R}
    (e : f ≫ s = s') : ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  subst e
  exact GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S S' s f o

theorem isUnit_pow {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : R)) {c : ℕ} (hc : ∃ e : ℕ, c = p ^ e) :
    IsUnit (c : Γ(S, ⊤)) := by
  obtain ⟨e, rfl⟩ := hc
  have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  rwa [← Nat.cast_pow, map_natCast] at this

theorem exists_obj {c : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] {s : Y ⟶ Sp R} (o : Obj b N s) (B : Over Y)
    [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A) (hp : IsUnit ((p : ℕ) : R)) (hc : ∃ e : ℕ, c = p ^ e)
    (hB : IsAbelianScheme B) (hq : IsQuasiInv c ψ ψ') (h1 : KerStableAt o ψ (𝟙 Y)) (h2 : PolKerAt o ψ' c (𝟙 Y)) :
    ∃ (o' : Obj b N s) (χ : o.A ⟶ o'.A) (θ : o'.A.left ⟶ B.left), IsPIsog c o o' χ ∧
      IsGrpPullback o'.A B (𝟙 Y) θ ∧ ψ.left = χ.left ≫ θ := by
  obtain ⟨act', hact⟩ := GlobalTheory.T.exists_orderAction_descent_along_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h1
  obtain ⟨P', hP', w1, w2⟩ := GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h2
  have hlie := GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny p D R b N c Y s o B ψ ψ' hp hc hB hq act' hact
  haveI := hq.1
  let o' : Obj b N s :=
    { A := B, ab := hB, act := act', P := P', isLB := hP'.1, rig₁ := hP'.2.1, rig₂ := hP'.2.2
      symm := GlobalTheory.T.quasiInverse_root_bundle_symmetric p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      ample := GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      kerP := GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat p D R b N c Y s o B ψ ψ' hp hc hB hq h2 P' hP' w1 w2
      rosati := GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact
      lie := hlie.1, lieRank := hlie.2
      eta := fun y => o.eta y ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, MonObj.mul_comp]
      eta_lin := fun a x => by rw [o.eta_lin, Category.assoc, hact, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, MonObj.one_comp]
      geom := GlobalTheory.T.pow_polarization_iso_pullback_of_descent p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact }
  exact ⟨o', ψ, 𝟙 _, ⟨hc, hq.1, hact, fun _ => rfl, ⟨w2⟩, ψ', hq.2.1, hq.2.2.1, hq.2.2.2⟩,
    GlobalTheory.SiegLower.isGrpPullback_id B, (Category.comp_id _).symm⟩

end

theorem exists_rep : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c _ _ _ hc0 _ S _ s o
  have hc : ∃ e : ℕ, c = p ^ e := hc0.imp fun _ h => h.1
  have hcpos : 0 < c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨Z, hZf, hZe, hZ⟩ := GlobalTheory.T.isogeny_representable_finite_etale S o.A c o.ab hcpos (isUnit_pow s hp hc)
  obtain ⟨oZ, ⟨mZ⟩⟩ := exists_pull Z.hom o rfl
  obtain ⟨B, _, _, ψ, ψ', hB, hq, huniv⟩ := hZ oZ.A mZ.φ mZ.cart
  obtain ⟨W₁, a₁, c₁, H₁⟩ := GlobalTheory.T.exists_clopen_kernelStable_harrisTaylor p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₂, a₂, c₂, H₂⟩ := GlobalTheory.T.harrisTaylor_pullback_kernel_locus_isClopen p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₃, a₃, c₃, H₃⟩ := GlobalTheory.T.exists_clopen_locus_of_annihilator p D R b N c _ _ oZ B ψ ψ' hp hc hB hq r w j
  haveI := hZf
  haveI := hZe
  obtain ⟨Y, i, hYf, hYe, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub (Z := Z)
    ⟨W₁ ∩ W₂ ∩ W₃, (a₁.inter a₂).inter a₃⟩ ((c₁.inter c₂).inter c₃)
  haveI := hYf
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hi : Set.range i.left.base ⊆ W₁ ∩ W₂ ∩ W₃ := (Hi Y i).2 ⟨𝟙 Y, Category.id_comp i⟩
  obtain ⟨o₀, ⟨mi⟩⟩ := exists_pull i.left oZ (s' := Y.hom ≫ s) (by rw [← Category.assoc, Over.w i])
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ObjMap o₀ o Y.hom, m₀.φ = mi.φ ≫ mZ.φ := by
    have H : ∀ g, i.left ≫ Z.hom = g → ∃ m₀ : ObjMap o₀ o g, m₀.φ = mi.φ ≫ mZ.φ := by
      rintro _ rfl
      exact exists_comp mi mZ
    exact H _ (Over.w i)
  obtain ⟨B₀, _, _, θ₀, ψ₀, ψ₀', hB₀, hθ₀, hq₀, e₀, e₀'⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback _ _ i.left oZ.A B c ψ ψ' o₀.A mi.φ hB hq mi.cart
  obtain ⟨o', χ, θ₁, hχ, hθ₁, e₁⟩ := exists_obj o₀ B₀ ψ₀ ψ₀' hp hc hB₀ hq₀
    ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀ ψ hθ₀ e₀).1 ((H₁ _ _).1 fun z hz => (hi hz).1.1))
    ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀' ψ' c hθ₀ e₀').1 ((H₂ _ _).1 fun z hz => (hi hz).1.2))
  have hθ : IsGrpPullback o'.A B i.left (θ₁ ≫ θ₀) := (hθ₁.comp hθ₀).congr (Category.id_comp _) rfl
  have eχ : mi.φ ≫ ψ.left = χ.left ≫ θ₁ ≫ θ₀ := by rw [e₀, e₁, Category.assoc]
  have htj : IsTj r w j o₀ o' χ := (tjAt_id_iff r w j o₀ o' χ).1
    ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi o'.A B (θ₁ ≫ θ₀) χ ψ r w j hθ eχ).1
      ((H₃ _ _).1 fun z hz => (hi hz).2))
  refine ⟨Y, o₀, m₀, o', χ, hYf, hYe, hχ, htj, fun T x o₁ o₁' m ψ₁ h1 h2 => ?_⟩
  obtain ⟨ψ₁', hq₁⟩ := h1.exists_quasiInv
  obtain ⟨z, ⟨hz, θ, θ', eθ, hθa, hθb, eψ⟩, zu⟩ := huniv T x o₁.A m.φ o₁'.A ψ₁ ψ₁' m.cart o₁'.ab hq₁
  obtain ⟨mz, hmz⟩ := exists_factor hN hNp hz mZ m
  obtain rfl : θ = mz.φ := mZ.cart.1.hom_ext (eθ.trans hmz.symm) (hθa.1.w.trans mz.cart.1.w.symm)
  have eψ' := GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv _ _ z oZ.A B c ψ ψ' o₁.A o₁'.A mz.φ θ' ψ₁ ψ₁' o₁'.ab hcpos hq hq₁ mz.cart eψ
  have hr : Set.range z.base ⊆ W₁ ∩ W₂ ∩ W₃ := Set.subset_inter (Set.subset_inter
    ((H₁ _ z).2 ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ hθb eψ).2 (h1.kerStableAt _)))
    ((H₂ _ z).2 ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁' ψ' c hθb eψ').2
      (GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse p D R b N c _ _ o₁ o₁' ψ₁ ψ₁' hp h1 hq₁))))
    ((H₃ _ z).2 ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ r w j hθb eψ).2
      ((tjAt_id_iff r w j o₁ o₁' ψ₁).2 h2)))
  obtain ⟨y, hy⟩ := (Hi (Over.mk x) (Over.homMk z hz)).1 hr
  have hyz : y.left ≫ i.left = z := congrArg CommaMorphism.left hy
  haveI : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · obtain ⟨m₀', hm⟩ := exists_factor hN hNp hyz mi mz
    let φ₁ : o₁'.A.left ⟶ o'.A.left := hθ.1.lift θ' (o₁'.A.hom ≫ y.left) (by rw [hθb.1.w, Category.assoc, hyz])
    have f1 : φ₁ ≫ θ₁ ≫ θ₀ = θ' := hθ.1.lift_fst _ _ _
    have f2 : φ₁ ≫ o'.A.hom = o₁'.A.hom ≫ y.left := hθ.1.lift_snd _ _ _
    have hφ₁ : IsGrpPullback o₁'.A o'.A y.left φ₁ := hθ.cancel (hθb.congr hyz.symm f1.symm) f2
    have e : m₀'.φ ≫ χ.left = ψ₁.left ≫ φ₁ := by
      apply hθ.1.hom_ext
      · rw [Category.assoc, ← eχ, ← Category.assoc, hm, eψ, Category.assoc, f1]
      · rw [Category.assoc, Over.w χ, m₀'.cart.1.w, Category.assoc, f2, ← Category.assoc, Over.w ψ₁]
    obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.exists_objMap_of_p_isogeny_pullback p D R b N c _ _ _ _ y.left o₁ o₁' o₀ o' m₀' ψ₁ χ φ₁ hp h1 hχ hφ₁ e
    exact ⟨m₀', m₁, by rw [hm₁, e]⟩
  · rintro y' ⟨hy', n₀, n₁, e⟩
    rw [← cancel_mono i.left, hyz]
    have hx : (y' ≫ i.left) ≫ Z.hom = x := by rw [Category.assoc, Over.w i, hy']
    obtain ⟨n, hn⟩ := exists_comp n₀ mi
    obtain ⟨n', hn'⟩ := exists_comp n mZ
    refine zu _ ⟨hx, n₀.φ ≫ mi.φ, n₁.φ ≫ θ₁ ≫ θ₀, ?_, n₀.cart.comp mi.cart, n₁.cart.comp hθ, ?_⟩
    · rw [← hn, ← hn']
      exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n' m hx
    · rw [Category.assoc, eχ, ← Category.assoc, e, Category.assoc]

end GlobalTheory.UPel.HT.ES.IsogRep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem red_pull_constMorV_pull {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀]
    (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem eq_of_liftSemi_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) (π : C →+* K)
    (Q : M' →ₛₗ[π] M) (e : M' →ₗ[C] C) (y : M →ₗ[K] K) (hQ : ∀ c, Q (P c) = c)
    (he : ∀ c, π (e (P c)) = y c) (c' : M') : y (Q c') = π (e c') := by
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, hQ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, he]

theorem corr_of_fst {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (y : HdR A₀) (hc : ∀ c, (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom
      (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) = y c) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr e y :=
  eq_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)).2 _ _ e y (red_pull_constMorV_pull A₀) hc

theorem fil_iff_red_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _ y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, corr_of_fst o₀.A o₀.ab e y fun c => ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, hz, he⟩, hcorr⟩
    have hxy : y = x := LinearMap.ext fun c => by
      have h1 := hcorr ((GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).pull c)
      rw [red_pull_constMorV_pull, he c] at h1
      simpa using h1
    exact hxy ▸ hx

end GlobalTheory.HTGlue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem primPull_constMorV_pull {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (q : primDR A₀) :
    primPull (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g
        ((GlobalTheory.FODef.constMorV k V A₀).pull q) =
      (GlobalTheory.FODef.constMorV k V A₀).pull (primPull (dp0 k) (𝟙 _) g q) := by
  apply Subtype.ext
  have K := (homMor (dp0 k) (𝟙 _) g).isMor.comp (GlobalTheory.FODef.constMorV k V A₀).isMor
  have e1 := IsMor.pullback1_comp (GlobalTheory.FODef.constMorV k V A₀).isMor
    (homMor (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g).isMor K
    (fun _ ↦ rfl) (by simp) q.1
  have e2 := IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (GlobalTheory.FODef.constMorV k V A₀).isMor K
    (fun _ ↦ rfl) rfl q.1
  exact e1.trans e2.symm

theorem push_mem_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f hf c e he
  haveI := o₀.act.hom c
  obtain ⟨x, hx, z, hz, hxz⟩ := he
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := GlobalTheory.HTCount.crysAct o₀ c
  have hg : ∀ h, g h = push (dp0 k) (𝟙 _) (o₀.act.act c) h := fun _ ↦ rfl
  refine ⟨g x, push_mem_Fil _ hx, fun j ↦ g (z j) - (f j (g x) - g (f j x)),
    fun j ↦ sub_mem (push_mem_Fil _ (hz j)) ((hf j).1 c x hx), fun q ↦ ?_⟩
  rw [push_apply, primPull_constMorV_pull, hxz]
  congr 2
  funext j
  rw [← push_apply, ← hg]
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.sub_apply, map_sub]
  abel

end GlobalTheory.HTGlue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_siegel_family_point_of_principal_object : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁] (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal → ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  first | exact @GlobalTheory.LowChart.exists_sFam_point | exact GlobalTheory.LowChart.exists_sFam_point | (intros; apply GlobalTheory.LowChart.exists_sFam_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual

theorem _root_.GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  first | (exact @GlobalTheory.DualFactor.main) | (exact GlobalTheory.DualFactor.main) | (intros; apply GlobalTheory.DualFactor.main <;> assumption)
end
