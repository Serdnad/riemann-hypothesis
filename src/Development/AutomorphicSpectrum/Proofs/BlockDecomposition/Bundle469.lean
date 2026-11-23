module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle410
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle104
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle438
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle439
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe w

namespace GlobalTheory.CompanionTheory.RedPull

theorem cls_eq_of_eq {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (e : a = b)
    (ha : K.d n a = 0) (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst e
  rfl

theorem pull_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {F G : C ⥤ ModuleCat.{0} R} {F' G' : C' ⥤ ModuleCat.{0} R'}
    (a : CH.Mor F G (RingHom.id R)) (b : CH.Mor G G' σ) (c : CH.Mor F F' σ) (d : CH.Mor F' G' (RingHom.id R'))
    (j : ℕ) (h : ∀ x : CH.Cn F j, b.pullC j (a.pullC j x) = d.pullC j (c.pullC j x)) (z : CH.H F j) :
    b.pull j (a.pull j z) = d.pull j (c.pull j z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) j).1 z
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc a.hom x hx
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc b.hom _ h1
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc c.hom x hx
  have h4 := CrystallineSemistableComparison.CechClassBoundaries.cyc d.hom _ h3
  change b.hom.mapH j (a.hom.mapH j _) = d.hom.mapH j (c.hom.mapH j _)
  rw [CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' a.hom x hx h1, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' b.hom _ h1 h2,
    CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' c.hom x hx h3, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' d.hom _ h3 h4]
  exact cls_eq_of_eq (h x) h2 h4

theorem sq_toSq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} (mm : SMor Φ Φ' σ) (b : IdF Φ.A) (b' : IdF Φ'.A)
    (ha : mm.Le (IdF.top _) (IdF.top _)) (hb : mm.Le b b') (j : ℕ) (z : CH.H (CH.modF Φ.A) j) :
    (mm.sq ha hb).pull j ((toSq (IdF.top _) b fun _ => rfl).pull j z) =
      (toSq (IdF.top _) b' fun _ => rfl).pull j (mm.o.pull j z) := by
  refine pull_square _ _ _ _ j (fun x => ?_) z
  funext t
  exact Subtype.ext Ideal.quotientMap_mk

theorem nmHM_redM : ∀ {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
    {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ) (r : Option ℤ) (n j : ℕ) (z : HO (TS γ q l s {⊤}) j),
    nmHM m l s r n j (redM (TS γ q l s {⊤}) r ((l : A) ^ n) j z) = redM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j (nmHO m l s j z) := by
  intro O A A' _ _ _ _ _ I I' γ γ' X X' q q' σ m l s r n j z
  exact sq_toSq (nmS m l s) _ _ (fun _ _ _ => trivial) (nm_std m l s r n) j z

end GlobalTheory.CompanionTheory.RedPull
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

universe w w' w'' u v u' v' u'' v''

theorem one_cyc {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) :
    (CH.cx (CH.modF A)).d 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem pull_oneH_eq {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R''} {σ' : R' →+* R''} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    {E : C'' ⥤ ModuleCat.{w''} R''} (m : CH.Mor (CH.modF A) E σ) (m' : CH.Mor (CH.modF A') E σ')
    (h : ∀ T : C'', m.τ T (1 : A.obj (m.G.obj T)) = m'.τ T (1 : A'.obj (m'.G.obj T))) :
    m.pull 0 (CH.oneH A) = m'.pull 0 (CH.oneH A') := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0)))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : (CH.cx E).d 0 (m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m.hom.comm, one_cyc, map_zero]
  have c' : (CH.cx E).d 0 (m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m'.hom.comm, one_cyc, map_zero]
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ c).trans (Eq.trans ?_ (CrystallineSemistableComparison.P.mapH_cls m'.hom 0 _ _ c').symm)
  exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem redMor_mul {O A R Λ : Type} [CommRing O] [CommRing A] [CommRing R] [CommRing Λ] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (T)
    (x y : (B.OM (nlFun δ l X q κ) c).obj ((redMor q s d 𝒱 c lam hc r).G.obj T)) :
    (redMor q s d 𝒱 c lam hc r).τ T ((CH.mulP (B.OA (nlFun δ l X q κ) c)).μ _ x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).μ T ((redMor q s d 𝒱 c lam hc r).τ T x) ((redMor q s d 𝒱 c lam hc r).τ T y) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
  refine Subtype.ext ?_
  rfl

theorem redMor_cup_one {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) :
    (∀ {i j k : ℕ} (h : i + j = k) x y, (redMor q s d 𝒱 c lam hc r).pull k ((CH.mulP (B.OA (nlFun δ l X q κ) c)).cup h x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).cup h ((redMor q s d 𝒱 c lam hc r).pull i x) ((redMor q s d 𝒱 c lam hc r).pull j y)) ∧
    (redMor q s d 𝒱 c lam hc r).pull 0 (CH.oneH (B.OA (nlFun δ l X q κ) c)) =
      redM (TS γ q l s 𝒱) r ((l : A) ^ n) 0 (CH.oneH (sP (TS γ q l s 𝒱)).A) := by
  refine ⟨fun {i j k} h x y => ?_, ?_⟩
  · exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (B.OA (nlFun δ l X q κ) c)) (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)))
      (redMor q s d 𝒱 c lam hc r).G (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).τ
      (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).nat (redMor q s d 𝒱 c lam hc r).nat
      (redMor q s d 𝒱 c lam hc r).nat (redMor_mul d q s 𝒱 c lam hc r) h x y
  · exact pull_oneH_eq _ _ (redMor q s d 𝒱 c lam hc r) (toSq (IdF.top _) (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)) fun _ => rfl)
      fun T => Subtype.ext (by
        change Ideal.Quotient.factor (ln_le q s 𝒱 r T) 1 = 1
        exact map_one _)

end GlobalTheory.CompanionTheory.RedCup
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatLevel

theorem exists_trivial_of_smul_eq_zero {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Flat A M]
    (f : A) (y : M) (h : f • y = 0) :
    ∃ (n : ℕ) (u : Fin n → A) (v : Fin n → M), y = ∑ j, u j • v j ∧ ∀ j, f * u j = 0 := by
  classical
  have h' : ∑ i : Unit, (fun _ : Unit => f) i • (fun _ : Unit => y) i = 0 := by simpa using h
  obtain ⟨n, a, z, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  refine ⟨n, fun j => a () j, z, ?_, fun j => ?_⟩
  · simpa using hx ()
  · simpa using ha j

theorem exists_mul_of_flat {W B : Type} [CommRing W] [CommRing B] {t : W} (ht : t ∈ nonZeroDivisors W)
    {a b m : ℕ} (h : a + b = m) (c : W ⧸ Ideal.span {t ^ m} →+* B) (hc : c.Flat) (y : B)
    (hy : c (Ideal.Quotient.mk _ (t ^ b)) * y = 0) : ∃ z, c (Ideal.Quotient.mk _ (t ^ a)) * z = y := by
  let _ := c.toAlgebra
  have : Module.Flat (W ⧸ Ideal.span {t ^ m}) B := hc
  have hb : Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ b) • y = 0 := by
    rw [Algebra.smul_def]
    exact hy
  obtain ⟨n, u, v, hyv, hu⟩ := exists_trivial_of_smul_eq_zero (A := W ⧸ Ideal.span {t ^ m}) (M := B) _ y hb
  have key : ∀ j, ∃ s : W, u j = Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ a * s) := by
    intro j
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (u j)
    have h1 := hu j
    rw [← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨s, hs⟩ := h1
    refine ⟨s, ?_⟩
    rw [← hw]
    congr 1
    have hb' : t ^ b ∈ nonZeroDivisors W := pow_mem ht b
    have h2 : (w - t ^ a * s) * t ^ b = 0 := by
      rw [← h, pow_add] at hs
      linear_combination (-1 : W) * hs
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hb').mp h2)
  choose s hs using key
  refine ⟨∑ j, c (Ideal.Quotient.mk _ (s j)) * v j, ?_⟩
  rw [hyv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, hs j, ← mul_assoc, ← map_mul, ← map_mul]
  rfl

theorem natCast_mem_nonZeroDivisors (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    (l : WittVector l k) ∈ nonZeroDivisors (WittVector l k) := by
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

set_option backward.isDefEq.respectTransparency false in
theorem flatL_Kt : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  intro l _ k _ _ _ O _ F ρ m
  show FlatL l m (CrystallineSemistableComparison.CH.cx (CrystallineSemistableComparison.CH.modF (CrystallineSemistableComparison.Pb.LsG.sW l F ρ m).A))
  rw [CrystallineSemistableComparison.Pb.LsG.modF_sW]
  intro i
  refine ⟨fun x => ?_, fun a b hab x hx => ?_⟩
  · funext s
    have h0 : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m}) ((l : WittVector l k) ^ m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    change ((s.obj (Fin.last i)).obj.i (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})
      ((l : WittVector l k) ^ m))) * (show (s.obj (Fin.last i)).obj.B from x s) = 0
    rw [h0, map_zero, zero_mul]
  · have key : ∀ s : ComposableArrows (fl l F ρ m).FullSubcategory i,
        ∃ z : ((fl l F ρ m).ι ⋙ Wc.OM l F ρ m).obj (s.obj (Fin.last i)),
          (l : WittVector l k) ^ a • z = x s := by
      intro s
      have hs : (s.obj (Fin.last i)).obj.i.Flat := (s.obj (Fin.last i)).property
      have h0 : (l : WittVector l k) ^ b • x s = 0 := congrFun hx s
      obtain ⟨z, hz⟩ := exists_mul_of_flat (natCast_mem_nonZeroDivisors l k) hab
        (s.obj (Fin.last i)).obj.i hs (x s) h0
      exact ⟨z, hz⟩
    choose z hz using key
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    exact ⟨z, funext fun s => hz s⟩

end GlobalTheory.CompanionTheory.FlatLevel

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv.EtaFn

section Var

variable {S : Type} [CommRing S] {l : ℕ} [Fact l.Prime] {ϖ x : S}

theorem pow_sub_one_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) (m : ℕ) :
    x ^ l ^ m - 1 ∈ Ideal.span {ϖ ^ l ^ m} := by
  rcases subsingleton_or_nontrivial S with h | h
  · rw [Subsingleton.elim (x ^ l ^ m - 1) 0]
    exact zero_mem _
  · haveI : CharP S l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl
    haveI : ExpChar S l := ExpChar.prime Fact.out
    have e : x ^ l ^ m - 1 = (x - 1) ^ l ^ m := by
      rw [sub_pow_char_pow, one_pow]
    rw [e, ← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hx _

theorem pow_sub_pow_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) {a b m : ℕ}
    (h : a ≡ b [MOD l ^ m]) : x ^ a - x ^ b ∈ Ideal.span {ϖ ^ l ^ m} := by
  have key : ∀ a b : ℕ, a ≤ b → a ≡ b [MOD l ^ m] → x ^ b - x ^ a ∈ Ideal.span {ϖ ^ l ^ m} := by
    intro a b hab h
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hab).1 h
    have hb : b = a + l ^ m * c := by omega
    obtain ⟨d, hd⟩ : x ^ l ^ m - 1 ∣ (x ^ l ^ m) ^ c - 1 := by
      simpa using sub_dvd_pow_sub_pow (x ^ l ^ m) 1 c
    have e : x ^ b - x ^ a = (x ^ l ^ m - 1) * (d * x ^ a) := by
      rw [hb, pow_add, pow_mul]
      linear_combination x ^ a * hd
    rw [e]
    exact Ideal.mul_mem_right _ _ (pow_sub_one_mem hl hx m)
  rcases le_total a b with hab | hab
  · rw [← neg_sub]
    exact neg_mem (key a b hab h)
  · exact key b a hab h.symm

theorem span_pow_le {k n : ℕ} (h : k ≤ n) : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ k} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ h)

theorem le_pow (k : ℕ) : k ≤ l ^ k := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem exists_lim [IsAdicComplete (Ideal.span {ϖ}) S] (hl : (l : S) = 0)
    (hx : x - 1 ∈ Ideal.span {ϖ}) (a : ℕ → ℕ) (ha : ∀ m m', m ≤ m' → a m' ≡ a m [MOD l ^ m]) :
    ∃ L, ∀ m, L - x ^ a m ∈ Ideal.span {ϖ ^ l ^ m} := by
  obtain ⟨L, hL⟩ := exists_tends (ϖ := ϖ) (fun m => x ^ a m) fun k =>
    ⟨k, fun m hm => span_pow_le (le_pow (l := l) k) (pow_sub_pow_mem hl hx (ha k m hm))⟩
  refine ⟨L, fun m => ?_⟩
  obtain ⟨M, hM⟩ := hL (l ^ m)
  have h1 := hM (max M m) (le_max_left _ _)
  have h2 := pow_sub_pow_mem (ϖ := ϖ) hl hx (ha m (max M m) (le_max_right _ _))
  have := sub_mem h2 h1
  convert this using 1
  ring

theorem eq_of_forall_mem [IsHausdorff (Ideal.span {ϖ}) S] {a b : S}
    (h : ∀ m, a - b ∈ Ideal.span {ϖ ^ l ^ m}) : a = b :=
  Tends.unique (ϖ := ϖ) (x := fun _ => a) (tends_const a)
    fun k => ⟨0, fun _ _ => span_pow_le (le_pow (l := l) k) (h k)⟩

end Var

variable {l : ℕ} [Fact l.Prime]

theorem val_modEq {m m' : ℕ} (h : m ≤ m') (z : ℤ_[l]) :
    (PadicInt.toZModPow m' z).val ≡ (PadicInt.toZModPow m z).val [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val,
    PadicInt.cast_toZModPow _ _ h]

theorem val_add_one (m : ℕ) (z : ℤ_[l]) :
    (PadicInt.toZModPow m (z + 1)).val ≡ (PadicInt.toZModPow m z).val + 1 [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    map_add, map_one, Nat.cast_one]

theorem exists_fn (A : PAlg l) (x : A.A) (hx : x - 1 ∈ Ideal.span {A.pi}) :
    ∃ η : (A.cont ℤ_[l]).A,
      (∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) η - x ^ (PadicInt.toZModPow m z).val ∈
        Ideal.span {A.pi ^ (l ^ m)}) ∧
      ∀ z : ℤ_[l], Hom.f (A.evCont (z + 1)) η = x * Hom.f (A.evCont z) η := by
  haveI hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have hl : (l : A.A) = 0 := A.natCast_l
  choose L hL using fun z : ℤ_[l] => exists_lim (ϖ := A.pi) hl hx
    (fun m => (PadicInt.toZModPow m z).val) (fun m m' h => val_modEq h z)
  refine ⟨⟨L, fun k => ?_⟩, fun m z => hL z m, fun z => ?_⟩
  · have e : (Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L =
        (fun c : ZMod (l ^ k) => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (x ^ c.val)) ∘
          PadicInt.toZModPow k := funext fun z =>
      Ideal.Quotient.eq.2 (span_pow_le (le_pow (l := l) k) (hL z k))
    have h : IsLocallyConstant ((Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L) := by
      rw [e]
      exact (GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l k).comp _
    exact h
  · refine eq_of_forall_mem (ϖ := A.pi) (l := l) fun m => ?_
    have h1 := hL (z + 1) m
    have h2 := Ideal.mul_mem_left _ x (hL z m)
    have h3 := pow_sub_pow_mem (ϖ := A.pi) hl hx (val_add_one m z)
    have := add_mem h1 (sub_mem h3 h2)
    change L (z + 1) - x * L z ∈ _
    convert this using 1
    ring

theorem exists_eta (ε : Eps l) : ∃ η : ((base l).cont ℤ_[l]).A,
    (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
    Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  have hx : (base l).s (ε.e 0) - 1 ∈ Ideal.span {(base l).pi} :=
    ((RL.sharp_cong (base l)).2.1 _ 1).1 (by
      rw [ε.sharp_e (base l), map_one, sub_self]
      exact zero_mem _)
  obtain ⟨η, h1, h2⟩ := exists_fn (base l) _ hx
  refine ⟨η, h1, cont_ext fun z => ?_⟩
  have e : Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) = (base l).s (ε.e 0) :=
    RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  rw [map_mul, e]
  exact h2 z

end GlobalTheory.CompanionTheory.ContUniv.EtaFn
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ElOnto

variable {l : ℕ} [Fact l.Prime]

theorem elMap_full {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (hu : ∀ A, Function.Injective (u.app A)) : (elMap u).Full := by
  refine ⟨fun {X Y} f => ⟨⟨f.1, ?_⟩, rfl⟩⟩
  apply hu
  exact (NatTrans.naturality_apply u ((testι l).map f.1) X.2).trans f.2

theorem elMap_faithful {P P' : PAlg l ⥤ Type} (u : P ⟶ P') : (elMap u).Faithful := by
  refine ⟨fun {X Y} f g h => Functor.Elements.Hom.ext ?_⟩
  have h' := congrArg (fun f => f.hom) h
  exact h'

variable {O : Type} [CommRing O]

theorem inc_pt_injective {F : Fn O} (κ : O →+* OC l) (V : F.Sub) (A : PAlg l) :
    Function.Injective ((V.inc.pt κ).app A) := by
  intro a b h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  exact h'

theorem onto_subEl : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 S k n hn
  refine ⟨elMap_full _ (inc_pt_injective κ _), elMap_faithful _, ?_, ?_⟩
  · intro T α hα
    exact (𝒜.V α).in_map _ (T.2.1.2 α hα)
  · intro T hT
    obtain ⟨hs, hj⟩ := (GlobalTheory.T.period_ring_base_change_from_universal T.1.obj n).2.2.2.2.2.2 k hn
    refine ⟨⟨⟨⟨T.2.1, fun α hα => 𝒜.jac α _ _ (CommRingCat.ofHom (uJ k T.1.obj n)) T.2.1 hs hj (hT α hα)⟩, T.2.2⟩⟩, ⟨Iso.refl _⟩⟩

end GlobalTheory.CompanionTheory.ElOnto
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

theorem _root_.GlobalTheory.T.divided_power_log_multiplicative : ∀ {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ),
    (∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) → ∀ v w : A, v - 1 ∈ J → w - 1 ∈ J →
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  first | exact @GlobalTheory.CompanionTheory.TruncLog.dlog_mul | exact GlobalTheory.CompanionTheory.TruncLog.dlog_mul | (intros; apply GlobalTheory.CompanionTheory.TruncLog.dlog_mul <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

theorem _root_.GlobalTheory.T.exists_crystalline_lift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  first | exact @GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | exact GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | (intros; apply GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.crystalline_point_universal_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  first | exact @GlobalTheory.CompanionTheory.TowerHom.tower_hom | exact GlobalTheory.CompanionTheory.TowerHom.tower_hom | (intros; apply GlobalTheory.CompanionTheory.TowerHom.tower_hom <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisFrob

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redLe (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem phi_base_le {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((phiPt F κ m).app B₀ ((basePt F _ (red_κb κ true h)).app B₀ y)).1.2 =
      ((basePt F _ (red_κb κ true h)).app B₀ ((phiPt F κ n).app B₀ y)).1.2 := by
  rw [SH.phi_snd F κ m B₀ _ (l_zero y.1.1), SH.base_snd, SH.base_snd, SH.phi_snd F κ n B₀ _ (l_zero y.1.1)]

theorem red_phi_le : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) := by
  intro l _ O _ F κ m n h j x
  unfold redHc phiHc redMor phiMorC
  exact cr_square (SH.phiM F κ m) (redLe F κ true h) (redLe F κ true h) (SH.phiM F κ n) ((base l).phi_cris m)
    (red_cris _ h) (red_cris _ h) ((base l).phi_cris n) ((pdOk_frob _).red_acr h) (phi_base_le F κ h) j x

end GlobalTheory.CompanionTheory.CrisFrob
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.epsilon_cyclotomic_element_properties : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.EpsFacts.eps_facts | exact GlobalTheory.CompanionTheory.EpsFacts.eps_facts | (intros; apply GlobalTheory.CompanionTheory.EpsFacts.eps_facts <;> assumption)
end
