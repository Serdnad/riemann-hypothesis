module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActSum

theorem act_sum_zsmul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  intro S A _ _ O _ act h r e c
  let f : Multiplicative O →* (A ⟶ A) := MonoidHom.mk' (fun a => act (Multiplicative.toAdd a)) (fun a b => h.2.2.2 _ _)
  have key : ∀ x : O, act x = f (Multiplicative.ofAdd x) := fun x => rfl
  rw [key, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

end GlobalTheory.ActSum
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.WpFam.TrIs

theorem main : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → IsTr ι Λ₀ Λ₁ (Tr t) := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  obtain ⟨_, _, _, hL0, ⟨𝔞, h𝔞, hL1⟩, _, _, _⟩ := hT
  obtain ⟨hsub, _, hleft, hright⟩ := GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hmem𝔞 : ∀ a' : K, a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a'
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ ι '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ ι '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : ∀ a : K, ι a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : ∀ a' : K, ι a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    intro a'
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  have hTr : ∀ x x' : K, Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x x' => (hA _).symm
  refine ⟨hsub, ?_, ?_, hleft, hright, ?_, ?_⟩
  · intro x x' h
    have hd := (hTr x x').1 h
    rw [h0, h1, hone, hmem𝔞]
    constructor
    · intro hx
      have := add_mem hd hx
      rwa [sub_add_cancel] at this
    · intro hx
      have := sub_mem hx hd
      rwa [sub_sub_cancel] at this
  · intro x x' hx hx'
    rw [hTr]
    exact sub_mem ((hmem𝔞 x').1 ((h1 x').1 hx')) ((hone x).1 ((h0 x).1 hx))
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL0' z).1 hz
    exact ⟨k, e⟩
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL1' z).1 hz
    exact ⟨k, e⟩

end GlobalTheory.WpFam.TrIs
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.GhostKer

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem phiInv_frobenius (b : Ainf p O) : phiInv p O (WittVector.frobenius b) = b := by
  rw [WittVector.frobenius_eq_map_frobenius]
  unfold phiInv
  ext n
  simp only [WittVector.map_coeff]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

theorem frobenius_iterate_teichmuller (k : ℕ) (x : PreTilt O p) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[k] (WittVector.teichmuller p x) =
      WittVector.teichmuller p (x ^ p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]


variable (p O) in
def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by rw [ghost, iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

theorem ghost_succ_xi {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (k : ℕ) :
    ghost p O (k + 1) (xi ε) = p := by
  have h : ghost p O (k + 1) (WittVector.teichmuller p (root ε)) = 1 := by
    rw [ghost, frobenius_iterate_teichmuller, WittVector.fontaineTheta_teichmuller, pow_succ',
      pow_mul, root, frobeniusEquiv_symm_pow_p, map_pow]
    have h0 := hε.zeta_zero
    simp only [zeta, Function.iterate_zero, id] at h0
    rw [h0, one_pow]
  change ghostHom p O (k + 1) (xi ε) = p
  unfold xi

  rw [map_sum]
  simp only [map_pow]
  change ∑ i ∈ Finset.range p, (ghost p O (k + 1) (WittVector.teichmuller p (root ε))) ^ i = p
  simp [h]

theorem nu_eq_mu_root (x : PreTilt O p) : nu x = mu (root x) := rfl

end SlopeTestRemainingChoices

theorem mu_dvd_of_ghost : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2
  have key : ∀ n, ∀ a : Ainf p O, (∀ m, ghost p O m a = 0) → mu ε ∣ mu (root^[n] ε) * a := by
    intro n
    induction n with
    | zero => intro a _; exact dvd_mul_right _ _
    | succ n ih =>
      intro a ha
      have ha0 : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
        rw [RingHom.mem_ker]; exact ha 0
      rw [GlobalTheory.AinfXi.ker_theta hv ε h1, Ideal.mem_span_singleton] at ha0
      obtain ⟨b, rfl⟩ := ha0
      have hb : ∀ m, ghost p O m (WittVector.frobenius b) = 0 := by
        intro m
        rw [ghost_frobenius]
        have h3 := ha (m + 1)
        rw [ghost_mul, ghost_succ_xi hε] at h3
        exact (mul_eq_zero.1 h3).resolve_left hp0
      obtain ⟨c, hc⟩ := ih _ hb
      have hc' := congrArg (phiInv p O) hc
      have e : root (root^[n] ε) = root^[n + 1] ε := (Function.iterate_succ_apply' root n ε).symm
      rw [map_mul, map_mul, phiInv_frobenius, phiInv_mu, phiInv_mu, nu_eq_mu_root, e] at hc'
      refine ⟨phiInv p O c, ?_⟩
      linear_combination xi ε * hc' + phiInv p O c * xi_mul_nu ε
  exact GlobalTheory.MuDivides.mu_dvd_of_forall_dvd p C v O hv ε h1 a (fun n => key n a ha)

end GlobalTheory.GhostKer
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lie_condition_descends_finite_etale_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ X), x ≫ (π ≫ sY) = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ sY = spMap β → ∀ v : epsPtR x ⟶ A₀, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A₀), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) := by
  first | (exact @GlobalTheory.LieGalDesc.lie_descends) | (exact GlobalTheory.LieGalDesc.lie_descends) | (intros; apply GlobalTheory.LieGalDesc.lie_descends  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.EtLevMorita

theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

section Act

variable {O : Type} [Ring O] {G : Type} [CommGroup G] (act : O → G → G)
  (hmul : ∀ b g h, act b (g * h) = act b g * act b h) (hone : ∀ g, act 1 g = g)
  (hcomp : ∀ b c g, act (b * c) g = act b (act c g)) (hadd : ∀ b c g, act (b + c) g = act b g * act c g)

include hmul in
theorem act_one_eq (b : O) : act b 1 = 1 := by
  have h := hmul b 1 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.1 h

include hadd in
theorem act_zero_eq (g : G) : act 0 g = 1 := by
  have h := hadd 0 0 g
  rw [add_zero] at h
  exact left_eq_mul.1 h

def actModule : Module O (Additive G) where
  smul b x := Additive.ofMul (act b x.toMul)
  one_smul x := by show Additive.ofMul (act 1 x.toMul) = x; rw [hone]; rfl
  mul_smul b c x := congrArg Additive.ofMul (hcomp b c x.toMul)
  smul_zero b := congrArg Additive.ofMul (act_one_eq act hmul b)
  smul_add b x y := congrArg Additive.ofMul (hmul b x.toMul y.toMul)
  add_smul b c x := congrArg Additive.ofMul (hadd b c x.toMul)
  zero_smul x := congrArg Additive.ofMul (act_zero_eq act hadd x.toMul)

end Act

end GlobalTheory.EtLevMorita


open GlobalTheory.EtLevMorita in
theorem GlobalTheory.EtLevMorita.exists_lev : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 →
  ∀ (G : Type) [CommGroup G] (act : D.O → G → G), (∀ b g h, act b (g * h) = act b g * act b h) → (∀ g, act 1 g = g) →
  (∀ b c g, act (b * c) g = act b (act c g)) → (∀ b c g, act (b + c) g = act b g * act c g) →
  ∀ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → G, (∀ a a', f (a + a') = f a * f a') →
  (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = act (algebraMap (𝓞 D.F) D.O c) (f a)) → Function.Injective f →
  (∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ a, f a = g) →
  ∃ l : D.La → G, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (b : D.O) x, l (b • x) = act b (l x)) ∧
    (∀ x, l x = 1 ↔ x ∈ wSub D w0 r) ∧ ∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g := by
  intro p _ D w0 r hw hp G _ act hmul hone hcomp hadd f hfadd hfsm hfinj hfonto
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨fun _ => 1, fun _ _ => (_root_.mul_one 1).symm, fun b _ => (act_one_eq act hmul b).symm,
      fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
    · simp only [true_iff]
      have hx : x = algebraMap (𝓞 D.F) D.O 1 • x := by simp
      rw [hx]
      exact Submodule.subset_span ⟨1, by simp, x, rfl⟩
    · have h1 := hg 1 (by simp)
      rw [map_one, hone] at h1
      exact h1.symm
  · haveI := isLocalRing_quot_pow w0 r hr.ne'
    letI : Module D.O (Additive G) := actModule act hmul hone hcomp hadd
    letI : Module (𝓞 D.F) (Additive G) := Module.compHom (Additive G) (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O (Additive G) := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    have hsm : ∀ (b : D.O) (x : Additive G), b • x = Additive.ofMul (act b x.toMul) := fun _ _ => rfl
    let T : Submodule D.O (Additive G) :=
      { carrier := {x | ∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) x.toMul = 1}
        add_mem' := fun {x y} hx hy c hc => by
          show act _ (x.toMul * y.toMul) = 1
          rw [hmul, hx c hc, hy c hc, _root_.mul_one]
        zero_mem' := fun c _ => act_one_eq act hmul _
        smul_mem' := fun b x hx c hc => by
          show act _ (act b x.toMul) = 1
          rw [← hcomp, Algebra.commutes, hcomp, hx c hc, act_one_eq act hmul] }
    have hf0 : f 0 = 1 := by
      have h := hfadd 0 0
      rw [add_zero] at h
      exact left_eq_mul.1 h
    have hfT : ∀ a, Additive.ofMul (f a) ∈ T := fun a c hc => by
      show act _ (f a) = 1
      rw [← hfsm, Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_smul, hf0]
    let fl : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) →ₗ[𝓞 D.F] T :=
      { toFun := fun a => ⟨Additive.ofMul (f a), hfT a⟩
        map_add' := fun a a' => Subtype.ext (by
          show Additive.ofMul (f (a + a')) = Additive.ofMul (f a) + Additive.ofMul (f a')
          rw [hfadd]; rfl)
        map_smul' := fun c a => Subtype.ext (by
          show Additive.ofMul (f (c • a)) = algebraMap (𝓞 D.F) D.O c • Additive.ofMul (f a)
          rw [← algebraMap_smul (𝓞 D.F ⧸ w0 ^ r) c a, Ideal.Quotient.algebraMap_eq, hfsm]
          rfl) }
    have hfl : Function.Bijective fl := by
      refine ⟨fun a a' h => hfinj (congrArg (fun t : T => (t : Additive G).toMul) h), fun t => ?_⟩
      obtain ⟨a, ha⟩ := hfonto (t : Additive G).toMul t.2
      exact ⟨a, Subtype.ext (by show Additive.ofMul (f a) = _; rw [ha]; rfl)⟩
    let eT : T ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) := (LinearEquiv.ofBijective fl hfl).symm
    obtain ⟨g, hgs, hgsm, hgker⟩ := GlobalTheory.T.level_quotient_module_surjection p D w0 r hw
    let gl : D.La →ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c x => by
          show g (algebraMap (𝓞 D.F) D.O c • x) = c • g x
          rw [hgsm, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
    have hker : LinearMap.ker gl = (wSub D w0 r).restrictScalars (𝓞 D.F) := by
      ext x
      rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
      exact hgker x
    let eL : (D.La ⧸ wSub D w0 r) ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      (Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D w0 r)).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ gl.quotKerEquivOfSurjective hgs
    obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power p D w0 r hw hp
    obtain ⟨e⟩ := GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix (𝓞 D.F) (w0 ^ r) inferInstance D.m D.n D.m_pos D.O φ hφs hφk
      (D.La ⧸ wSub D w0 r) T eL eT
    refine ⟨fun x => ((e (Submodule.Quotient.mk x) : T) : Additive G).toMul, fun x y => ?_, fun b x => ?_,
      fun x => ?_, fun g hg => ?_⟩
    · simp only [Submodule.Quotient.mk_add, map_add (f := _), Submodule.coe_add, toMul_add]
    · simp only [Submodule.Quotient.mk_smul, map_smul, Submodule.coe_smul, hsm, toMul_ofMul]
    · rw [toMul_eq_one, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm ⟨Additive.ofMul g, hg⟩)
      refine ⟨y, ?_⟩
      simp only [hy, LinearEquiv.apply_symm_apply, toMul_ofMul]
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

namespace KerGrp

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

def sub (T : Over S) : Subgroup (T ⟶ A) := (IsMonHom.monoidHom f T).ker

theorem mem_sub {T : Over S} (x : T ⟶ A) : x ∈ sub f T ↔ x ≫ f = 1 := by
  simp [sub, MonoidHom.mem_ker]

def pts : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (sub f T.unop)
  map {T T'} g := GrpCat.ofHom
    { toFun := fun x => ⟨g.unop ≫ x.1, (mem_sub f _).2 (by
        rw [Category.assoc, (mem_sub f _).1 x.2, MonObj.comp_one])⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp g h := by ext x; exact Category.assoc _ _ _

theorem fst_comp : pullback.fst f η[B] ≫ f = 1 := by
  rw [pullback.condition, Hom.one_def, toUnit_unique (pullback.snd f η[B]) (toUnit _)]

def lift {T : Over S} (x : T ⟶ A) (hx : x ≫ f = 1) : T ⟶ ker f :=
  pullback.lift x (toUnit T) (by rw [hx, Hom.one_def])

@[simp] theorem lift_fst {T : Over S} (x : T ⟶ A) (hx : x ≫ f = 1) : lift f x hx ≫ pullback.fst f η[B] = x :=
  pullback.lift_fst _ _ _

theorem hom_ext {T : Over S} {y z : T ⟶ ker f} (h : y ≫ pullback.fst f η[B] = z ≫ pullback.fst f η[B]) :
    y = z :=
  pullback.hom_ext h (toUnit_unique _ _)

def rep : (pts f ⋙ forget _).RepresentableBy (ker f) where
  homEquiv {T} :=
    { toFun := fun y => (⟨y ≫ pullback.fst f η[B], (mem_sub f _).2 (by rw [Category.assoc, fst_comp,
        MonObj.comp_one])⟩ : sub f T)
      invFun := fun x => lift f (x : sub f T).1 ((mem_sub f _).1 (x : sub f T).2)
      left_inv := fun y => hom_ext f (lift_fst _ _ _)
      right_inv := fun x => Subtype.ext (lift_fst _ _ _) }
  homEquiv_comp g y := Subtype.ext (Category.assoc _ _ _)

@[instance_reducible]
def grp : GrpObj (ker f) := GrpObj.ofRepresentableBy _ (pts f) (rep f)

theorem mul_fst {T : Over S} (y z : T ⟶ ker f) :
    letI := grp f
    (y * z) ≫ pullback.fst f η[B] = (y ≫ pullback.fst f η[B]) * (z ≫ pullback.fst f η[B]) := by
  letI := grp f
  have := ((yonedaGrpObjIsoOfRepresentableBy (ker f) _ (rep f)).hom.app (.op T)).hom.map_mul y z
  exact congrArg Subtype.val this

theorem isMonHom_fst : letI := grp f; IsMonHom (pullback.fst f η[B]) := by
  letI := grp f
  exact isMonHom_of_mul _ fun T y z => mul_fst f y z

instance mono_fst : Mono (pullback.fst f η[B]) := ⟨fun _ _ h => hom_ext f h⟩

end KerGrp

end GlobalTheory.IwLevel
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_differential_comm : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  first | exact @GlobalTheory.CechPoset.Φ_dB | exact GlobalTheory.CechPoset.Φ_dB | (intros; apply GlobalTheory.CechPoset.Φ_dB <;> assumption)
end
