module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle114
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle126
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle127
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.FinGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartMaps

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem nil_J (T : Thick (nlFun γ p X q κ)) : ∀ x ∈ T.J, IsNilpotent x := by
  intro x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

theorem isDP {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) : IsDPMorphism c.D.δ T.δ f := by
  have e : f.comp c.D.i = T.i := RingHom.ext hf
  refine IsDPMorphism.of_comp γ c.D.δ T.δ c.D.i f c.J_eq c.D.compat ?_
  rw [e]
  exact T.compat

theorem exists_unique_lift {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d)
    (T : Thick (nlFun γ p X q κ)) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : ∀ r, g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r))
    (y : Fin d → T.B) (hy : ∀ k, Ideal.Quotient.mk T.J (y k) = g (Ideal.Quotient.mk _ (c.t k))) :
    ∃! f : c.D.B →+* T.B, (∀ r, f (c.D.i r) = T.i r) ∧ (∀ k, f (c.t k) = y k) ∧
      (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J) := by
  have hL := GlobalTheory.T.etale_lifting_of_nil_ideal T.J (nil_J T)
  have hc : (g.comp (Ideal.Quotient.mk c.D.J)).comp
      (MvPolynomial.eval₂Hom c.D.i c.t : MvPolynomial (Fin d) R →+* c.D.B) =
      (Ideal.Quotient.mk T.J).comp (MvPolynomial.eval₂Hom T.i y : MvPolynomial (Fin d) R →+* T.B) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simpa using hg r
    · simpa using (hy k).symm
  obtain ⟨f, ⟨h1, h2⟩, hu⟩ := hL (MvPolynomial (Fin d) R) c.D.B _ c.etale
    (MvPolynomial.eval₂Hom T.i y) (g.comp (Ideal.Quotient.mk c.D.J)) hc
  refine ⟨f, ⟨fun r => ?_, fun k => ?_, h2⟩, ?_⟩
  · simpa using RingHom.congr_fun h1 (MvPolynomial.C r)
  · simpa using RingHom.congr_fun h1 (MvPolynomial.X k)
  · rintro f' ⟨a1, a2, a3⟩
    refine hu f' ⟨MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_), a3⟩
    · simpa using a1 r
    · simpa using a2 k

theorem inU_of_hom {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)}
    (σ : c.D ⟶ T) : InU V T := by
  have e : pt T = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) ≫ pt c.D := by
    unfold pt
    rw [← σ.pt]
    rfl
  unfold InU
  rw [e]
  intro x _
  exact c.inV (show (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle))) x ∈ ⊤ from trivial)

theorem quot_comm {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) (r : R) :
    g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r) := by
  have e := congrArg (fun z : PtOver X q κ (T.B ⧸ T.J) => z.1.1 (Ideal.Quotient.mk _ r)) hg
  have w1 := c.D.w r
  have w2 := T.w r
  calc g (Ideal.Quotient.mk _ (c.D.i r))
      = g ((nlFun γ p X q κ).str c.D.y (Ideal.Quotient.mk _ r)) := by rw [w1]
    _ = (nlFun γ p X q κ).str T.y (Ideal.Quotient.mk _ r) := e
    _ = Ideal.Quotient.mk _ (T.i r) := w2

def homOf {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hq : (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J))
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) : c.D ⟶ T :=
  have hdp := isDP c T f hf
  have hle : c.D.J ≤ T.J.comap f := fun _ hx => hdp.1 (Ideal.mem_map_of_mem f hx)
  mkH f hf hdp hle (by
    have e : Ideal.quotientMap T.J f hle = g :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun x => RingHom.congr_fun hq x)
    rw [e]
    exact hg)

theorem good {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) : c.Good := by
  refine ⟨fun T hT => ?_, fun T σ y hy => ?_⟩
  · obtain ⟨g, hg, -⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
    have hg' : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y := hg
    choose y hy using fun k => Ideal.Quotient.mk_surjective (g (Ideal.Quotient.mk _ (c.t k)))
    obtain ⟨f, ⟨h1, -, h3⟩, -⟩ := exists_unique_lift c T g (quot_comm c T g hg') y hy
    exact ⟨homOf c T f h1 g h3 hg'⟩
  · have hg : (nlFun γ p X q κ).Pt.map
        (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) c.D.y = T.y := σ.pt
    have hs : ∀ k, Ideal.Quotient.mk T.J (σ.φ (c.t k) + y k) =
        Ideal.quotientMap T.J σ.φ σ.hle (Ideal.Quotient.mk _ (c.t k)) := fun k => by
      rw [Ideal.quotientMap_mk, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 (hy k), add_zero]
    obtain ⟨f, ⟨h1, h2, h3⟩, hu⟩ := exists_unique_lift c T (Ideal.quotientMap T.J σ.φ σ.hle)
      (quot_comm c T _ hg) (fun k => σ.φ (c.t k) + y k) hs
    refine ⟨homOf c T f h1 _ h3 hg, fun i => ?_, fun τ hτ => hom_ext ?_⟩
    · change f (c.t i) - σ.φ (c.t i) = y i
      rw [h2 i]
      ring
    · obtain ⟨g₀, -, hu₀⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y (inU_of_hom c σ)
      have e : Ideal.quotientMap T.J τ.φ τ.hle = Ideal.quotientMap T.J σ.φ σ.hle :=
        (hu₀ _ τ.pt).trans (hu₀ _ σ.pt).symm
      refine hu τ.φ ⟨τ.comm, fun k => ?_, ?_⟩
      · have := hτ k
        rw [← this]
        ring
      · rw [← e]
        rfl

end GlobalTheory.CompanionTheory.ChartMaps
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LengthOneCochainExactness

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

noncomputable def incl (b : IdF A) : CH.Mor (sq b (IdF.bot A)) (CH.modF A) (RingHom.id R) where
  G := 𝟭 C
  τ T := (AlgEquiv.quotientBot R (A.obj T)).toLinearMap ∘ₗ (sqM b (IdF.bot A) T).subtype
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

theorem incl_mem (b : IdF A) {T : C} (x : (sq b (IdF.bot A)).obj T) : (incl b).τ T x ∈ b.S T := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact hy

theorem cochain_exact (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ n, Function.Injective ((incl b).hom.f n)) ∧
    (∀ n, Function.Exact ((incl b).hom.f n) ((toSq a b ha).hom.f n)) ∧
    ∀ n, Function.Surjective ((toSq a b ha).hom.f n) := by
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    have h : (incl b).τ _ (x (s ⋙ 𝟭 C)) = (incl b).τ _ (y (s ⋙ 𝟭 C)) := congrFun hxy s
    exact Subtype.ext ((AlgEquiv.quotientBot R _).injective h)
  · have hm : ∀ s : ComposableArrows C n,
        (show A.obj (s.obj (Fin.last n)) from y s) ∈ b.S (s.obj (Fin.last n)) := fun s => by
      have h := congrArg Subtype.val (congrFun hy s)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h
    exact ⟨fun s => sqMk b (IdF.bot A) _ (hm s), rfl⟩
  · rintro ⟨x, rfl⟩
    funext s
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (incl_mem b (x (s ⋙ 𝟭 C))))
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

theorem pull_toSq_bijective (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) →
      ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  intro hv j
  obtain ⟨hf, hfg, hg⟩ := cochain_exact a b ha
  obtain ⟨δ, -, -, hex, hex2, -⟩ := CrystallineSemistableComparison.P.les _ _ hf hfg hg
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex j x).1 hx
    rw [(hv j).elim y 0, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := (hex2 j y).1 ((hv (j + 1)).elim _ _)
    exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.LengthOneCochainExactness
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLim

theorem module_finite_lim : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W]
    (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  intro W _ l _ S S' L h1
  have hfl := GlobalTheory.T.finite_length_of_lseq_first W l S S' L h1
  have hart : ∀ n, IsArtinian W (S.M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl n)).2
  have hinj := GlobalTheory.T.limit_divisible_of_vanishing_level W l S S' L hart

  have hvan : ∀ n, (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) ≤ LinearMap.ker (pr S n) := by
    intro n
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Ideal.span_singleton_pow] at hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul]
    rw [L.kill n, smul_zero]
  have hH : IsHausdorff (Ideal.span {(l : W)}) S.lim := by
    refine ⟨fun x hx => Subtype.ext (funext fun n => ?_)⟩
    have hm : x ∈ (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) := by
      simpa [SModEq.zero] using hx n
    exact hvan n hm
  have hmem1 : ∀ x : S.lim, pr S 1 x = 0 → x ∈ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) := by
    intro x hx
    obtain ⟨y, hy⟩ := hinj 1 x hx
    rw [hy, pow_one]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hle : Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) ≤ LinearMap.ker (pr S 1) := by
    simpa using hvan 1
  let q := (Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).liftQ (pr S 1) hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem1 x hz
  have : IsNoetherian W (S.M 1) := (isFiniteLength_iff_isNoetherian_isArtinian.1 h1).1
  have : Module.Finite W (S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := W)
    (M := S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {(l : W)}) (Fin r → W) := ReciprocityTheory.Coh.isPrecomplete_pi _
  have hsurj : Function.Surjective ((Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).mkQ ∘ₗ
      Fintype.linearCombination W s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory.CompanionTheory.TowerLim
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfBC

theorem bc_laur : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : A[T;T⁻¹] →ₐ[A] B) (f g : A), Pf p A → Pf p K → PQ p (i : A[T;T⁻¹] →+* B) (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → ∃ i₁ : K[T;T⁻¹] →+* B ⊗[A] K, PQ p i₁ (Ideal.span {LaurentPolynomial.C (algebraMap A K f) - LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)}) ∧ (∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i f g hA hK hPQ
  let j : A[T;T⁻¹] →+* K[T;T⁻¹] :=
    AddMonoidAlgebra.liftNCRingHom ((LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K))
      (AddMonoidAlgebra.of K ℤ) (fun _ _ => Commute.all _ _)
  let i₁ : K[T;T⁻¹] →+* B ⊗[A] K :=
    AddMonoidAlgebra.liftNCRingHom
      (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K).comp
        (i : A[T;T⁻¹] →+* B)).toMonoidHom.comp (AddMonoidAlgebra.of A ℤ))
      (fun _ _ => Commute.all _ _)
  have hi1 : ∀ (n : ℤ) (k : K), i₁ (AddMonoidAlgebra.single n k) =
      ((1 : B) ⊗ₜ[A] k) * (i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K)) := by
    intro n k
    exact AddMonoidAlgebra.liftNC_single _ _ n k
  have hj1 : ∀ (n : ℤ) (a : A), j (AddMonoidAlgebra.single n a) =
      LaurentPolynomial.C (algebraMap A K a) * LaurentPolynomial.T n := by
    intro n a
    exact AddMonoidAlgebra.liftNC_single _ _ n a
  have hC : ∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    have h1 := hi1 0 a
    rw [LaurentPolynomial.T_zero, map_one, ← Algebra.TensorProduct.one_def, mul_one] at h1
    exact h1
  have hT : ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
    intro n
    have h1 := hi1 n 1
    rw [← Algebra.TensorProduct.one_def, one_mul] at h1
    exact h1
  have hjC : ∀ a, j (LaurentPolynomial.C a) = LaurentPolynomial.C (algebraMap A K a) := by
    intro a
    have h1 := hj1 0 a
    rw [LaurentPolynomial.T_zero, mul_one] at h1
    exact h1
  have hjT : ∀ n : ℤ, j (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    have h1 := hj1 n 1
    rw [map_one, map_one, one_mul] at h1
    exact h1
  have hiC : ∀ a, i (LaurentPolynomial.C a) = algebraMap A B a := by
    intro a
    rw [← AlgHom.commutes i a, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self_apply]
  have hcomp : (LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K) =
      j.comp (algebraMap A A[T;T⁻¹]) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.algebraMap_apply,
      Algebra.algebraMap_self_apply, hjC]
  have hgen : Subring.closure (Set.range (LaurentPolynomial.C : K →+* K[T;T⁻¹]) ∪ Set.range j) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    refine LaurentPolynomial.induction_on' q ?_ ?_
    · intro a b ha hb
      exact Subring.add_mem _ ha hb
    · intro n a
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨LaurentPolynomial.T n, hjT n⟩))
  have hij : ∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    refine LaurentPolynomial.induction_on' s ?_ ?_
    · intro a b ha hb
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), TensorProduct.add_tmul]
    · intro n a
      rw [map_mul, map_mul, hjC, hjT, map_mul, hC, hT, hiC, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
  have hmap : (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g} :
      Ideal A[T;T⁻¹]).map j = Ideal.span {(LaurentPolynomial.C (algebraMap A K f) -
        LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g))} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, hjC, hjC, hjT]
  refine ⟨i₁, ?_, hC, hT⟩
  rw [← hmap]
  exact GlobalTheory.T.perfect_tensor_generated_lift p A A[T;T⁻¹] B K K[T;T⁻¹] i _ LaurentPolynomial.C j i₁ hA hK hPQ hcomp hgen
    hC hij

end GlobalTheory.CompanionTheory.PerfBC
end
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Perfection

theorem pq_baseChange_polynomial : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : Polynomial A →ₐ[A] B) (h : Polynomial A), Pf p A → Pf p K → PQ p (i : Polynomial A →+* B) (Ideal.span {h}) → ∃ i₁ : Polynomial K →+* B ⊗[A] K, PQ p i₁ (Ideal.span {h.map (algebraMap A K)}) ∧ (∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i h hA hK hPQ
  let i₁ : Polynomial K →+* B ⊗[A] K :=
    Polynomial.eval₂RingHom (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (i Polynomial.X ⊗ₜ[A] (1 : K))
  have hC : ∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    simp [i₁]
  have hX : i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
    simp [i₁]
  have hj : ∀ s : Polynomial A, i₁ (Polynomial.mapRingHom (algebraMap A K) s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    induction s using Polynomial.induction_on with
    | C a =>
      have h1 : i (Polynomial.C a) = algebraMap A B a := by
        rw [← Polynomial.algebraMap_eq]
        exact i.commutes a
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hC, h1, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add f g hf hg =>
      rw [map_add (f := _), map_add (f := _), hf, hg, map_add (f := _), TensorProduct.add_tmul]
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial A)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e, map_mul, map_mul, ih, map_mul]
      have e2 : Polynomial.mapRingHom (algebraMap A K) (Polynomial.X : Polynomial A) = Polynomial.X := by
        simp
      rw [e2, hX, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [map_mul]
  have hcl : Subring.closure (Set.range (Polynomial.C : K →+* Polynomial K) ∪
      Set.range (Polynomial.mapRingHom (algebraMap A K))) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    induction f using Polynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add f g hf hg => exact Subring.add_mem _ (hf trivial) (hg trivial)
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e]
      refine Subring.mul_mem _ (ih trivial) (Subring.subset_closure (Or.inr ⟨Polynomial.X, ?_⟩))
      simp
  have hcomp : (Polynomial.C : K →+* Polynomial K).comp (algebraMap A K)
      = (Polynomial.mapRingHom (algebraMap A K)).comp (algebraMap A (Polynomial A)) := by
    ext a
    simp [Polynomial.algebraMap_apply]
  have key := GlobalTheory.T.perfect_tensor_generated_lift p A (Polynomial A) B K (Polynomial K) i (Ideal.span {h})
    Polynomial.C (Polynomial.mapRingHom (algebraMap A K)) i₁ hA hK hPQ hcomp hcl hC hj
  refine ⟨i₁, ?_, hC, hX⟩
  rw [Ideal.map_span, Set.image_singleton] at key
  simpa using key

end GlobalTheory.CompanionTheory.Perfection
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem exists_finite_sys_of_separated_quasiCompact :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s → QuasiCompact s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  intro R _ X s hsep hqc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hdiag : IsAffineHom (Limits.pullback.diagonal s) := inferInstance
  have hinf : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => isAffineHom_diagonal_iff.mp hdiag ⊤ (isAffineOpen_top _) U (by simp) V
      (by simp) hU hV
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  let A : Set X.Opens := infClosure ((fun i : X.affineOpens => i.1) '' S)
  have hA : ∀ U ∈ A, IsAffineOpen U :=
    infClosure_min (t := {U | IsAffineOpen U}) (by rintro _ ⟨i, -, rfl⟩; exact i.2)
      (fun a ha b hb => hinf a b ha hb)
  letI inst : SemilatticeInf A :=
    Subtype.semilatticeInf (fun _ _ ha hb => infClosed_infClosure ha hb)
  haveI hfin : Finite A := ((hS.image _).infClosure).to_subtype
  refine ⟨A, inst, hfin, ⟨⟨fun j => ⟨j.1, hA j.1 j.2⟩, fun a b => rfl, ?_⟩⟩⟩
  apply top_le_iff.mp
  rw [e]
  exact iSup₂_le fun i hi => le_iSup_of_le (⟨i.1, subset_infClosure ⟨i, hi, rfl⟩⟩ : A) le_rfl

end GlobalTheory.CompanionTheory.Axis
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

theorem _root_.GlobalTheory.T.smooth_phi_minus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.SmPhiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirSmooth.smPhiMinus | exact GlobalTheory.CompanionTheory.BZMirSmooth.smPhiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMirSmooth.smPhiMinus <;> assumption)
end
