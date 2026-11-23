module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.CompHS.FunDer

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TangentOrigin GlobalTheory.Frames GlobalTheory.FlagTan
open TrivSqZeroExt hiding map lift
open scoped Classical

theorem primeSpectrum_trivSqZeroExt_eq {L ι : Type} [Field L] (x y : PrimeSpectrum (TrivSqZeroExt L (ι → L))) :
    x = y := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt L (ι → L)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem primeSpectrum_field_eq {L : Type} [Field L] (x y : PrimeSpectrum L) : x = y :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)

theorem le_preimage_of_unique {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R']
    (hR : ∀ x y : PrimeSpectrum R, x = y) {T : Scheme.{0}} (φ : R →+* R') (x : Sp R ⟶ T) (V : T.Opens)
    (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint R') = s := hR _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint R') ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem top_le_comp {S T U : Scheme.{0}} (f : S ⟶ T) (x : T ⟶ U) (V : U.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ (f ≫ x) ⁻¹ᵁ V := fun s _ => h (Set.mem_univ (f s))

theorem top_le_of_red {L R : Type} [Field L] [CommRing R] (hR : ∀ x y : PrimeSpectrum R, x = y) (ρ : R →+* L)
    {T : Scheme.{0}} {p : Sp R ⟶ T} {z : Sp L ⟶ T} (e : spMap ρ ≫ p = z) {O : T.Opens} (h : ⊤ ≤ z ⁻¹ᵁ O) :
    ⊤ ≤ p ⁻¹ᵁ O :=
  le_preimage_of_unique hR ρ p O (e ▸ h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem lift_eq {S : Scheme.{0}} {a b : S ⟶ M.X} (h : a ≫ toFlag M = b ≫ toFlag M) (ha : ⊤ ≤ a ⁻¹ᵁ M.off) :
    a = b := by
  have hU : ⊤ ≤ (a ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ha (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have e : a ≫ M.σ = b ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc]
    exact h
  exact (M.existsUnique_lift (a ≫ M.σ) hU).unique rfl e.symm

theorem exists_lift_of_unique {L R : Type} [Field L] [Algebra c.F L] [CommRing R] [Algebra c.F R]
    (hR : ∀ x y : PrimeSpectrum R, x = y) (ρ : R →ₐ[c.F] L) {Q : FrPt Xo c L} {W : FrPt Xo c R} (hd : FrMap ρ W Q)
    {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ ZW : Sp R ⟶ M.X, ZW ≫ toFlag M = X.ptY W ∧ spMap ρ.toRingHom ≫ ZW = z := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_unique hR ρ.toRingHom _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY W := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap ρ.toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_unique hR ρ.toRingHom _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap ρ.toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, hred⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

theorem red_eq {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {z : Sp L ⟶ M.X}
    (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {R : Type} [CommRing R] [Algebra c.F R]
    {ρ : R →ₐ[c.F] L} {u : FrPt Xo c R} (hu : FrMap ρ u Q) {p : Sp R ⟶ M.X} (hp : p ≫ toFlag M = X.ptY u) :
    spMap ρ.toRingHom ≫ p = z :=
  (lift_eq M (by rw [Category.assoc, hp, X.ptY_frMap hu, hz]) ho).symm

variable {K : Type} [Field K] [Algebra c.F K]

theorem der_dir {ι : Type} [Fintype ι] {Q : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q)
    (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} (hW : FrMap (fstHom c.F K (ι → K)) W Q) :
    ∃ ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, ∀ (m : ι → K) (u : FrPt Xo c (DualNumber K))
      (p : Sp (DualNumber K) ⟶ M.X), FrMap (dir c m) W u → p ≫ toFlag M = X.ptY u →
      ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hp : ⊤ ≤ p ⁻¹ᵁ O), ∃ hZ : ⊤ ≤ ZW ⁻¹ᵁ O,
        (evalPt p O hp g).snd = ∑ k, (evalPt ZW O hZ g).snd k * m k := by
  obtain ⟨ZW, h1, h2⟩ := exists_lift_of_unique M primeSpectrum_trivSqZeroExt_eq _ hW hz ho
  have hZo : ⊤ ≤ ZW ⁻¹ᵁ M.off := top_le_of_red primeSpectrum_trivSqZeroExt_eq _ h2 ho
  refine ⟨ZW, fun m u p hu hp O g hpO => ?_⟩
  have e : p = spMap (dir c m).toRingHom ≫ ZW :=
    (lift_eq M (by rw [Category.assoc, h1, X.ptY_frMap hu, hp]) (top_le_comp _ _ _ hZo)).symm
  subst e
  have hZ : ⊤ ≤ ZW ⁻¹ᵁ O := le_preimage_of_unique primeSpectrum_trivSqZeroExt_eq _ ZW O hpO
  refine ⟨hZ, ?_⟩
  rw [evalPt_spMap_comp _ ZW O hZ hpO]
  exact snd_dir m _

theorem der_vert_eq_zero {y : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY y) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {N : FIx Dw → K} {u : FrPt Xo c (DualNumber K)} (h : IsVert y N u)
    (hN : ∀ σ i j, i < j → N (some ⟨σ, i, j⟩) = 0) {p : Sp (DualNumber K) ⟶ M.X} (hp : p ≫ toFlag M = X.ptY u)
    (O : M.X.Opens) (g : Γ(M.X, O)) (h1 : ⊤ ≤ p ⁻¹ᵁ O) : (evalPt p O h1 g).snd = 0 := by
  obtain ⟨y₀, h₀, hs⟩ := h
  have hb : FrBor (fun k => oneAddEps (Multiplicative.ofAdd (diagOf N k))) y₀ u :=
    (frBor_iff_frChg _ _ _).2 ⟨unip K N, fun σ i j hij => by simp [unip, hN σ i j hij, hij.ne],
      fun _ _ => by simp [unip, oneAddEps, diagOf], hs⟩
  have e : p = spMap (cst c K).toRingHom ≫ z := by
    refine (lift_eq M ?_ (top_le_comp _ _ _ ho)).symm
    rw [Category.assoc, hz, X.ptY_frMap h₀, X.ptY_frBor hb, hp]
  subst e
  have hzO : ⊤ ≤ z ⁻¹ᵁ O := le_preimage_of_unique primeSpectrum_field_eq _ z O h1
  rw [evalPt_spMap_comp _ z O hzO h1]
  rfl

theorem der_shift {y : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY y) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {N : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v) (h' : IsShift N v v')
    {zz : FIx Dw → FrPt Xo c (DualNumber K)} (hzz : ∀ k, IsVert y (Pi.single k (1 : K)) (zz k))
    {p p' : Sp (DualNumber K) ⟶ M.X} {q : FIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hp : p ≫ toFlag M = X.ptY v)
    (hp' : p' ≫ toFlag M = X.ptY v') (hq : ∀ k, q k ≫ toFlag M = X.ptY (zz k)) (O : M.X.Opens) (g : Γ(M.X, O))
    (h1 : ⊤ ≤ p ⁻¹ᵁ O) (h2 : ⊤ ≤ p' ⁻¹ᵁ O) (h3 : ∀ k, ⊤ ≤ q k ⁻¹ᵁ O) :
    (evalPt p' O h2 g).snd = (evalPt p O h1 g).snd + ∑ k, N k * (evalPt (q k) O (h3 k) g).snd := by
  let emb : DualNumber K →ₐ[c.F] TrivSqZeroExt K (Option (FIx Dw) → K) :=
    (TrivSqZeroExt.map (LinearMap.single K (fun _ : Option (FIx Dw) => K) none)).restrictScalars c.F
  have e1 : ∀ a, (emb a).fst = a.fst := fun a => fst_map _ a
  have e2 : ∀ a, (emb a).snd = Pi.single none a.snd := fun a => snd_map _ a
  obtain ⟨W₀, hW₀⟩ := exists_frMap emb v
  let n : FIx Dw → Option (FIx Dw) → K := fun k => Pi.single (some k) 1
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)
  have key : ∀ (m : Option (FIx Dw) → K) (z₀ z : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      IsShift (fun k => m (some k)) z₀ z → FrMap (dir c m) W z := fun m z₀ z k₀ k => by
    refine (frMap_iff_frChg hW k₀).2 ?_
    unfold IsShift at k
    convert k using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have k1 : ∀ m : Option (FIx Dw) → K, m none = 1 → FrMap (dir c m) W₀ v := fun m hm =>
    frMap_of_comp hW₀ (frMap_id v) fun a => by ext <;> simp [e1, e2, Pi.single_apply, hm]
  have kv : FrMap (dir c (Pi.single none 1)) W v :=
    key _ v v (k1 _ (by simp)) (by convert isShift_zero v using 2; simp)
  have hWy : FrMap (fstHom c.F K (Option (FIx Dw) → K)) W y := frMap_comp kv h fun a => by simp
  obtain ⟨ZW, hZW⟩ := der_dir M hz ho hWy
  obtain ⟨hZ1, a1⟩ := hZW _ _ p' (key (fun k => k.elim 1 N) v v' (k1 _ rfl) h') hp' O g h2
  obtain ⟨hZ2, a2⟩ := hZW _ _ p kv hp O g h1
  rw [a1, a2, Fintype.sum_option]
  congr 1
  · simp [Pi.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨y₀, h₀, hk⟩ := hzz k
  obtain ⟨hZ3, a3⟩ := hZW _ _ (q k) (key (Pi.single (some k) 1) y₀ (zz k)
    (frMap_of_comp hW₀ (frMap_comp (χ := (cst c K).comp (red c K)) h h₀ fun _ => rfl) fun a => by
      ext <;> simp [e1, e2, Pi.single_apply]) (by
      convert hk using 2; simp [Pi.single_apply])) (hq k) O g (h3 k)
  rw [a3]
  simp [Pi.single_apply, mul_comm]

theorem evalPt_eq_of_eq {R : Type} [CommRing R] {T : Scheme.{0}} {a b : Sp R ⟶ T} (e : a = b) (O : T.Opens)
    (ha : ⊤ ≤ a ⁻¹ᵁ O) (hb : ⊤ ≤ b ⁻¹ᵁ O) (g : Γ(T, O)) : evalPt a O ha g = evalPt b O hb g := by
  subst e
  rfl

end GlobalTheory.CompHS.FunDer
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped RestrictedProduct

namespace GlobalTheory.AfPZero

theorem natCast_eq_algebraMap (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (n : ℤ) :=
  (map_natCast (algebraMap ℤ (v.adicCompletion ℚ)) n).symm

theorem valued_natCast (v : HeightOneSpectrum ℤ) (n : ℕ) :
    Valued.v (n : v.adicCompletion ℚ) = v.intValuation (n : ℤ) := by
  rw [natCast_eq_algebraMap]
  have := valuedAdicCompletion_eq_valuation (K := ℚ) v (n : ℤ)
  rw [← valuation_of_algebraMap (K := ℚ)]
  exact this

theorem eq_zero_of_dvd (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ)
    (h : ∀ k : ℕ, ∃ n : ℕ, (n : ℤ) ∈ v.asIdeal ^ k ∧
      ∃ y ∈ v.adicCompletionIntegers ℚ, x = (n : v.adicCompletion ℚ) * y) : x = 0 := by
  by_contra hx
  have hγ : Valued.v x ≠ 0 := by simpa using hx
  set L : ℤ := log (Valued.v x) with hL
  obtain ⟨n, hn, y, hy, hxe⟩ := h ((-L).toNat + 1)
  have h1 : Valued.v x ≤ exp (-(((-L).toNat + 1 : ℕ) : ℤ)) := by
    rw [hxe, map_mul]
    calc Valued.v (n : v.adicCompletion ℚ) * Valued.v y ≤ Valued.v (n : v.adicCompletion ℚ) * 1 :=
          by gcongr; exact (mem_adicCompletionIntegers ℤ ℚ v).1 hy
      _ = v.intValuation (n : ℤ) := by rw [_root_.mul_one, valued_natCast]
      _ ≤ _ := (intValuation_le_pow_iff_mem v _ _).2 hn
  rw [← exp_log hγ, ← hL] at h1
  have h2 := exp_le_exp.1 h1
  omega

open GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem exists_prime (p : ℕ) [Fact p.Prime] (v : AwayP p) :
    ∃ l : ℕ, l.Prime ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  set q : ℤ := Submodule.IsPrincipal.generator v.1.asIdeal with hq
  have hspan : v.1.asIdeal = Ideal.span {q} := (Submodule.IsPrincipal.span_singleton_generator v.1.asIdeal).symm
  have hq0 : q ≠ 0 := by
    intro h0
    apply v.1.ne_bot
    rw [hspan, h0, Ideal.span_singleton_eq_bot]
  have hqp : Prime q := by
    have := v.1.isPrime
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hq0).1 this
  have hl : q.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan' : v.1.asIdeal = Ideal.span {((q.natAbs : ℕ) : ℤ)} := by
    rw [hspan, Int.span_natAbs]
  refine ⟨q.natAbs, hl, (Nat.coprime_primes hl (Fact.out)).2 ?_, ?_⟩
  · intro he
    apply v.2
    rw [hspan', he]
  · rw [hspan']
    exact Ideal.subset_span rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (α : AfP p),
    (∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) → α = 0 := by
  intro p _ α h
  have hloc : ∀ v : AwayP p, AfP.eval v α = 0 := by
    intro v
    obtain ⟨l, hl, hlp, hlv⟩ := exists_prime p v
    apply eq_zero_of_dvd v.1
    intro k
    obtain ⟨β, hβ, hαβ⟩ := h (l ^ k) (pow_pos hl.pos k) (Nat.Coprime.pow_left k hlp)
    refine ⟨l ^ k, by push_cast; exact Ideal.pow_mem_pow hlv k, AfP.eval v β, hβ v, ?_⟩
    rw [hαβ, map_nsmul, nsmul_eq_mul]
  exact Subtype.ext (funext fun v => hloc v)

end GlobalTheory.AfPZero
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.IntDvd

open IsDedekindDomain HeightOneSpectrum

theorem int_dvd_of_local (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) (c : ℤ)
    (h : ∀ v : AwayP p, ∃ y ∈ v.1.adicCompletionIntegers ℚ,
      algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ) = algebraMap ℚ (v.1.adicCompletion ℚ) ((n : ℤ) : ℚ) * y) :
    (n : ℤ) ∣ c := by
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp
  · obtain ⟨ℓ, hℓ, n₁, hn₁⟩ : ∃ ℓ, ℓ.Prime ∧ ∃ n₁, n = ℓ * n₁ :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    have hℓp : ℓ ≠ p := by
      intro he
      have h3 : ℓ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n₁, hn₁⟩ hc
      rw [he, Nat.coprime_self] at h3
      exact (Fact.out : p.Prime).one_lt.ne' h3
    let w : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ),
      by simp [hℓ.ne_zero]⟩
    have hw : w.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro he
      rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at he
      simp only [Int.natAbs_natCast] at he
      exact hℓp he
    let v : AwayP p := ⟨w, hw⟩
    have hval : ∀ c : ℤ, Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ)) = v.1.intValuation c := by
      intro c
      rw [← valuation_of_algebraMap (K := ℚ), ← valuedAdicCompletion_eq_valuation]
      rfl
    have hℓc : (ℓ : ℤ) ∣ c := by
      obtain ⟨y, hy, e⟩ := h v
      have hy' : Valued.v y ≤ 1 := (mem_adicCompletionIntegers ℤ ℚ v.1).1 hy
      have h1 : v.1.intValuation c ≤ v.1.intValuation (n : ℤ) := by
        rw [← hval, ← hval, e, map_mul]
        exact mul_le_of_le_one_right' hy'
      have h2 : v.1.intValuation (n : ℤ) < 1 :=
        (intValuation_lt_one_iff_mem _ _).2 (Ideal.mem_span_singleton.2 ⟨n₁, by rw [hn₁]; push_cast; ring⟩)
      exact Ideal.mem_span_singleton.1 ((intValuation_lt_one_iff_mem _ _).1 (lt_of_le_of_lt h1 h2))
    obtain ⟨c₁, rfl⟩ := hℓc
    have hn₁pos : 0 < n₁ := by
      rcases Nat.eq_zero_or_pos n₁ with h0 | h0
      · rw [h0, mul_zero] at hn₁; omega
      · exact h0
    have hlt : n₁ < n := by
      rw [hn₁]; exact lt_mul_left hn₁pos hℓ.one_lt
    have hc₁ : n₁.Coprime p := Nat.Coprime.coprime_dvd_left ⟨ℓ, by rw [hn₁, Nat.mul_comm]⟩ hc
    have hd : (n₁ : ℤ) ∣ c₁ := ih n₁ hlt hn₁pos hc₁ c₁ fun v' => by
      obtain ⟨y, hy, e⟩ := h v'
      refine ⟨y, hy, ?_⟩
      have hne : algebraMap ℚ (v'.1.adicCompletion ℚ) ((ℓ : ℤ) : ℚ) ≠ 0 :=
        (map_ne_zero _).2 (by exact_mod_cast hℓ.ne_zero)
      apply mul_left_cancel₀ hne
      rw [← map_mul, ← _root_.mul_assoc, ← map_mul, ← Int.cast_mul, ← Int.cast_mul, e, hn₁]
      push_cast
      ring
    rw [hn₁]
    push_cast
    exact mul_dvd_mul_left _ hd

theorem int_dvd_of_eq_mul_isIntAf : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p),
    IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  intro p _ n hn hc c a ha e
  refine int_dvd_of_local p n hn hc c fun v => ⟨AfP.eval v a, ha v, ?_⟩
  have e' := congrArg (AfP.eval v) e
  rw [(AfP.eval v).commutes, map_mul, map_natCast] at e'
  rw [e']
  simp

end GlobalTheory.LKGeo.IntDvd
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem det_gram_ne_zero {L : Type} [AddCommGroup L] {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℤ L) (B : LinearMap.BilinForm ℤ L) (hB : Function.Injective B) :
    (Matrix.of fun i j => B (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  apply hc0
  have hx : B (∑ i, c i • b i) = 0 := by
    apply b.ext
    intro j
    have := congrFun hc j

    simpa [Matrix.vecMul, dotProduct, map_sum, map_smul, mul_comm] using this
  have h1 : ∑ i, c i • b i = 0 := hB (hx.trans (map_zero B).symm)
  funext i
  exact Fintype.linearIndependent_iff.mp b.linearIndependent c h1 i

theorem nondeg_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D),
    (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  intro p _ D z hz
  classical
  haveI := D.freeLa; haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  let bA := Algebra.TensorProduct.basis (AfP p) bQ
  have hg : ∀ i j, (D.EF.baseChange ℚ).baseChange (AfP p) (bA i) (bA j) = ((D.EF (b i) (b j) : ℤ) : AfP p) := by
    intro i j
    simp [bA, bQ, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
  set c := bA.repr z
  let M : Matrix _ _ (AfP p) := (Matrix.of fun i j => D.EF (b i) (b j)).map (Int.castRingHom (AfP p))
  have hzs : z = ∑ j, c j • bA j := (bA.sum_repr z).symm
  have hM : M.mulVec c = 0 := by
    funext i
    have := hz (bA i)

    rw [hzs, map_sum] at this
    simpa [Matrix.mulVec, dotProduct, M, hg, mul_comm] using this
  have hdet : IsUnit M.det := by
    rw [show M.det = Int.castRingHom (AfP p) (Matrix.of fun i j => D.EF (b i) (b j)).det from
      (RingHom.map_det _ _).symm]
    have h0 := det_gram_ne_zero b D.EF D.nondeg
    have hq : IsUnit (((Matrix.of fun i j => D.EF (b i) (b j)).det : ℤ) : ℚ) :=
      isUnit_iff_ne_zero.mpr (by exact_mod_cast h0)
    have := hq.map (algebraMap ℚ (AfP p))
    simpa using this
  have hc : (⇑c : _ → AfP p) = 0 := by
    have := congrArg (M⁻¹).mulVec hM
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have hc' : ∀ j, c j = 0 := fun j => congrFun hc j
  rw [hzs]
  simp [hc']

end GlobalTheory.LKGeo
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem actG_mem_laHat {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {g : G.GAf}
    (hg : g ∈ L.KN N) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : L.actG g v ∈ LaHat D := by
  obtain ⟨w, hw, e⟩ := hg.1 v hv
  rw [e]
  exact add_mem hv (nsmul_mem hw N)

end GlobalTheory.LKGeo
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

theorem _root_.GlobalTheory.T.theta_moderate_growth_height : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  first | exact @GlobalTheory.ThetaModGrowthPair.theta_modGrowth | exact GlobalTheory.ThetaModGrowthPair.theta_modGrowth | (intros; apply GlobalTheory.ThetaModGrowthPair.theta_modGrowth <;> assumption)
end
