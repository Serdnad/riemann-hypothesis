module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle012
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} (G₀ G₁ : V n → Matrix r r ℂ) {v : V n}, ρ =ᶠ[𝓝 v] (fun _ => 0) → corrC ρ G₀ G₁ v = 0 := by
  first | exact @GlobalTheory.GoodTop.corrC_eq_zero_of_eventuallyEq_zero | exact GlobalTheory.GoodTop.corrC_eq_zero_of_eventuallyEq_zero | (intros; apply GlobalTheory.GoodTop.corrC_eq_zero_of_eventuallyEq_zero <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O
open scoped NNReal

namespace GlobalTheory.VertForm

section Algebra

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {D : ℕ}


variable (E D) in
abbrev Form : Type u := (Π _ : Fin (D + 1), E) →ₘₗ[ℝ] ℝ

variable {num : Form E D} {G : Set E}

end Algebra

section Bundles

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}



def NefOver (L : HermLB p) (l : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [CharP κ l] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

theorem nefFib_iff (L : HermLB p) : NefFib L ↔ ∀ l : ℕ, l.Prime → NefOver L l :=
  ⟨fun h _ _ Z i _ _ κ _ _ _ _ hZ => h Z i κ hZ, fun h Z i _ _ κ _ _ _ hZ =>
    h (ringChar κ) (CharP.char_is_prime κ _) Z i κ hZ⟩

end Bundles

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Lies (V' V : Cover Y) (π : V'.X ⟶ V.X) : Prop := ∃ g : V'.G ⟶ V.G, g ≫ V.j = V'.j ≫ π ∧ g ≫ V.π = V'.π

end Covers

end GlobalTheory.VertForm

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.CoverHt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem isPreimmersion_j : IsPreimmersion V.j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h


end GlobalTheory.Mean4O.CoverHt
end
end

section

noncomputable section

open Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.PolyTensor

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
  (γ : Matrix (Fin n) (Fin n) K)

def polySub : Subalgebra ℚ_[p] (Matrix (Fin n) (Fin n) K) := (Algebra.adjoin K {γ}).restrictScalars ℚ_[p]

theorem mem_polySub {x : Matrix (Fin n) (Fin n) K} : x ∈ polySub p K n γ ↔ x ∈ Algebra.adjoin K {γ} :=
  Iff.rfl

theorem polySub_comm (a b : polySub p K n γ) : a * b = b * a :=
  Subtype.ext (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (mem_polySub p K n γ |>.1 b.2)
    (fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact (Algebra.commute_of_mem_adjoin_singleton_of_commute (mem_polySub p K n γ |>.1 a.2)
        (Commute.refl γ)).symm)).eq

def PolyAlg : Type := polySub p K n γ

instance : CommRing (PolyAlg p K n γ) :=
  { (polySub p K n γ).toRing with mul_comm := polySub_comm p K n γ }

instance : Algebra ℚ_[p] (PolyAlg p K n γ) := inferInstanceAs (Algebra ℚ_[p] (polySub p K n γ))

instance [FiniteDimensional ℚ_[p] K] : Module.Finite ℚ_[p] (PolyAlg p K n γ) :=
  inferInstanceAs (Module.Finite ℚ_[p] (polySub p K n γ))

def val : PolyAlg p K n γ →ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) K := (polySub p K n γ).val

variable (r : ℕ)

def phi : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r →ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) (KQ p K r) :=
  Algebra.TensorProduct.lift (((inclK p K r).mapMatrix).comp (val p K n γ))
    (((Algebra.ofId (KQ p K r) (Matrix (Fin n) (Fin n) (KQ p K r))).restrictScalars ℚ_[p]).comp (inclQ p K r))
    (fun x y => (Algebra.commutes (inclQ p K r y) (((inclK p K r).mapMatrix.comp (val p K n γ)) x)).symm)

theorem phi_tmul (b : PolyAlg p K n γ) (q : Qr p r) :
    phi p K n γ r (b ⊗ₜ q) = (val p K n γ b).map (inclK p K r) * algebraMap (KQ p K r) _ (inclQ p K r q) := by
  unfold phi
  exact Algebra.TensorProduct.lift_tmul _ _ _ b q

def tw : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r →ₐ[ℚ_[p]] PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] _) (frobQ p r)

theorem phi_tw (x : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r) :
    phi p K n γ r (tw p K n γ r x) = (phi p K n γ r x).map (sigKQ p K r) := by
  change ((phi p K n γ r).comp (tw p K n γ r)) x = ((sigKQ p K r).mapMatrix.comp (phi p K n γ r)) x
  congr 1
  refine Algebra.TensorProduct.ext' fun b q => ?_
  simp only [AlgHom.comp_apply, tw, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi_tmul, map_mul,
    AlgHom.mapMatrix_apply]
  congr 1
  · ext i j
    simp only [Matrix.map_apply]
    exact (sigKQ_apply_inclK p K r _).symm
  · ext i j
    simp only [Matrix.map_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [sigKQ_apply_inclQ]

theorem phi_commute (y : Matrix (Fin n) (Fin n) K) (hy : Commute y γ) (x : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r) :
    Commute (y.map (inclK p K r)) (phi p K n γ r x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_right _
  | tmul b q =>
    rw [phi_tmul]
    refine Commute.mul_right ?_ (Algebra.commutes _ _).symm
    have h : Commute y (val p K n γ b) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute ((mem_polySub p K n γ).1 b.2) hy
    exact h.map (inclK p K r).mapMatrix
  | add a b ha hb => rw [map_add (f := _)]; exact ha.add_right hb

end GlobalTheory.PolyTensor
end
end

section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem frobQ_fixed_mem (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (b : Qr p r) (hb : frobQ p r b = b) :
    ∃ c : ℚ_[p], algebraMap ℚ_[p] (Qr p r) c = b := by
  have h1 : frobK p (Q0 p) (b : PadicAlgCl p) = b := congrArg Subtype.val hb
  have h2 : (b : PadicAlgCl p) ∈ Q0 p := mem_of_frobK_fixed inferInstance (Kn_le_Kur hr b.2) h1
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 h2
  exact ⟨c, Subtype.ext hc⟩

theorem sigKQ_fixed_eq_inclK : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ x : GlobalTheory.LKRes.KQ p K r, GlobalTheory.LKRes.sigKQ p K r x = x → ∃ a : K, GlobalTheory.LKRes.inclK p K r a = x := by
  intro p _ K r hr
  change ∀ x : K ⊗[ℚ_[p]] Qr p r, Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) x = x →
    ∃ a : K, (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] Qr p r) a = x
  intro x hx
  let f : ℚ_[p] →ₗ[ℚ_[p]] Qr p r := Algebra.linearMap _ _
  let g : Qr p r →ₗ[ℚ_[p]] Qr p r := (frobQ p r).toLinearMap - LinearMap.id
  have hex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : frobQ p r b = b := sub_eq_zero.1 hb
      exact frobQ_fixed_mem p r hr b hb'
    · rintro ⟨c, rfl⟩
      simp [g, f]
  have hex2 := Module.Flat.lTensor_exact K hex
  have hg : g.lTensor K =
      (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)).toLinearMap - LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [g, TensorProduct.tmul_sub]
  have hx0 : g.lTensor K x = 0 := by
    rw [hg, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    exact sub_eq_zero.2 hx
  obtain ⟨y, hy⟩ := (hex2 x).1 hx0
  refine ⟨TensorProduct.rid ℚ_[p] K y, ?_⟩
  rw [← hy]
  clear hy hx hx0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, f, Algebra.linearMap_apply]
    change (c • a) ⊗ₜ[ℚ_[p]] (1 : Qr p r) = a ⊗ₜ[ℚ_[p]] (algebraMap ℚ_[p] (Qr p r) c)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add u v hu hv =>
    rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _)]

end GlobalTheory.LKRes
end

section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKResNrmConj

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem coe_frobQ_iterate (r k : ℕ) (b : Qr p r) :
    (((⇑(frobQ p r))^[k] b : Qr p r) : PadicAlgCl p) = (frobK p (_root_.GlobalTheory.LKRes.Q0 p) ^ k) (b : PadicAlgCl p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
    rfl

theorem frobQ_iterate_self (r : ℕ) (hr : 0 < r) (b : Qr p r) : (⇑(frobQ p r))^[r] b = b := by
  refine Subtype.ext ?_
  have hK : FiniteDimensional ℚ_[p] (_root_.GlobalTheory.LKRes.Q0 p) := inferInstance
  rw [coe_frobQ_iterate]
  exact (IsFrobOn.pow_fixes_iff p (_root_.GlobalTheory.LKRes.Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ b.2

theorem sigKQ_iterate_self (r : ℕ) (hr : 0 < r) (y : KQ p K r) : (⇑(sigKQ p K r))^[r] y = y := by
  have ht : ∀ (k : ℕ) (a : K) (b : Qr p r), (⇑(sigKQ p K r))^[k] (inclK p K r a * inclQ p K r b) =
      inclK p K r a * inclQ p K r ((⇑(frobQ p r))^[k] b) := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, sigKQ_apply_inclK, sigKQ_apply_inclQ,
        Function.iterate_succ_apply']
  have key : ∀ z : K ⊗[ℚ_[p]] Qr p r, (⇑(sigKQ p K r))^[r] (z : KQ p K r) = (z : KQ p K r) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact iterate_map_zero (sigKQ p K r) r
    | tmul a b =>
      have e : inclK p K r a * inclQ p K r b = (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) := by
        change (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b) = a ⊗ₜ[ℚ_[p]] b
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have h := ht r a b
      rw [frobQ_iterate_self p r hr, e] at h
      exact h
    | add z w hz hw =>
      exact (iterate_map_add (sigKQ p K r) r (z : KQ p K r) (w : KQ p K r)).trans (congrArg₂ (· + ·) hz hw)
  exact key y

theorem sigRes_iterate_self (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    (⇑(sigRes p K n r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin n), ((⇑(sigRes p K n r))^[k] g).val i j = (⇑(sigKQ p K r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, sigKQ_iterate_self p K r hr]

end GlobalTheory.LKResNrmConj
end

section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime]

noncomputable def frobQEquiv (r : ℕ) (hr : 0 < r) : Qr p r ≃ₐ[ℚ_[p]] Qr p r :=
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  AlgEquiv.ofBijective (frobQ p r)
    ((frobQ p r).toLinearMap.injective_iff_surjective.mp (frobQ p r).toRingHom.injective |>
      fun hs => ⟨(frobQ p r).toRingHom.injective, hs⟩)

theorem frobQEquiv_pow_apply (r : ℕ) (hr : 0 < r) (i : ℕ) (b : Qr p r) :
    (((frobQEquiv p r hr ^ i) b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  induction i generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]
    rfl

theorem orderOf_frobQEquiv (r : ℕ) (hr : 0 < r) : orderOf (frobQEquiv p r hr) = r := by
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  have key : ∀ i : ℕ, frobQEquiv p r hr ^ i = 1 ↔ r ∣ i := by
    intro i
    rw [← IsFrobOn.pow_fixes_iff p (Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) i]
    constructor
    · intro h x hx
      have := frobQEquiv_pow_apply p r hr i ⟨x, hx⟩
      rw [h] at this
      exact this.symm
    · intro h
      refine AlgEquiv.ext fun b => Subtype.ext ?_
      rw [frobQEquiv_pow_apply]
      exact h _ b.2
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((key r).2 dvd_rfl)
  · exact (key _).1 (pow_orderOf_eq_one _)

end GlobalTheory.LKRes
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.EtNormal

theorem isDomain_and_isIntegrallyClosed_of_formallyEtale (A T : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    [Algebra.FormallyEtale A T] [Algebra.EssFiniteType A T] :
    IsDomain T ∧ IsIntegrallyClosed T := by
  let B := Algebra.EssFiniteType.subalgebra A T
  let P : Ideal B := (IsLocalRing.maximalIdeal T).comap (algebraMap B T)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hM : Algebra.EssFiniteType.submonoid A T = P.primeCompl := by
    ext x
    change IsUnit (algebraMap B T x) ↔ x ∉ P
    simp [P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI hloc : IsLocalization.AtPrime T P := by
    have := Algebra.EssFiniteType.isLocalization A T
    rw [hM] at this
    exact this
  haveI : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType).1 inferInstance
  let e : T ≃ₐ[A] Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars A
  haveI : Algebra.FormallySmooth A (Localization.AtPrime P) := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.IsSmoothAt A P := inferInstance
  obtain ⟨f, hfP, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := P)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) P ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) T
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

end GlobalTheory.EtNormal

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T), IsEtTower cK R cL T ι ψ τ → IsIntegrallyClosed T := by
  intro K L _ _ cK cL r R T ι ψ τ h
  haveI := h.top.isLocalRing
  haveI := h.normal
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra A T := φ.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  haveI : Algebra.FormallyEtale A T := h.etale
  haveI : Algebra.EssFiniteType ℂ T := h.top.essFiniteType
  haveI : IsScalarTower ℂ A T := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change cT a = φ (MvPolynomial.C (c0 a))
    have e : φ (MvPolynomial.C (c0 a)) = ι (c0 a) := MvPolynomial.eval₂Hom_C _ _ _
    rw [e]
    exact Subtype.ext (h.const a).symm
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp ℂ A T
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial_fin R r
  exact (GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale A T).2

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_residue_complex : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K) (h : IsLocModel (algebraMap ℂ K) R),
  RatRes (algebraMap ℂ K) R →
  ∃ ε : R →+* ℂ, (∀ a : ℂ, ε ⟨algebraMap ℂ K a, h.const_mem a⟩ = a) ∧ ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  intro K _ _ R h hr
  haveI := h.isLocalRing
  let c0 : ℂ →+* R := (algebraMap ℂ K).codRestrict R h.const_mem
  let φ : ℂ →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp c0
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y => ?_⟩
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr r r.2
    refine ⟨a, ?_⟩
    have hn : NonUnit R ((r - c0 a : R) : K) := by simpa [c0] using ha
    have hm : r - c0 a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := R) (r - c0 a)).1 hn)
    have := (IsLocalRing.residue_eq_zero_iff (r - c0 a)).2 hm
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  let e := RingEquiv.ofBijective φ hφ
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue R), fun a => ?_, fun r => ?_⟩
  · show e.symm (φ a) = a
    exact e.symm_apply_apply a
  · rw [nonUnit_iff (R := R) r, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_eq_zero_iff _ e.symm.injective, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]

end GlobalTheory.FieldPair
end
