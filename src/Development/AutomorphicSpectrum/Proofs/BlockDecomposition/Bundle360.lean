module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle340
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle342
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B CrystallineSemistableComparison.Pb DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.KMVan

section Sc

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure Sc (Φ : PDF R C) (Λ : Type) [CommRing Λ] where
  ρ : ∀ T : C, Λ →+* Φ.A.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (a : Λ), (Φ.A.map φ).hom (ρ T a) = ρ T' a

variable {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Sc

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section Loc
open TensorProduct
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Loc
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section D
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end D
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section LT
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end LT
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section FV
variable {R : Type} [CommRing R]

end FV
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section PS
open CrystallineSemistableComparison.Pb.Site GlobalTheory.PDA GlobalTheory.CompanionTheory.ChartLocBc
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end PS

section Res
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

end Res

section Fr
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

end Fr
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section CL
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V V' : X.Opens} {d : ℕ}

end CL
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU (⊤ : X.Opens) T := fun _ _ => trivial

def evT (T : Thick (nlFun γ p X q κ)) : Γ(X, ⊤) →+* T.B ⧸ T.J := ev T (inU_top T)

theorem evT_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    evT T' f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ ⊤), GlobalTheory.Cris.evalAt y ⊤ hh f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) (inU_top T) hh f
  exact key _ (pt_hom φ) (inU_top T')

end TAU
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU2
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end TAU2
end GlobalTheory.CompanionTheory.KMVan
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GlobBc

universe w w'

theorem tens_transport {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f) : Tens R f₁ := by
  obtain ⟨g, hg⟩ := hT
  let c : (∀ i, N i ⊗[R] M₁ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (e i).symm).toAddEquiv
  refine ⟨c.trans (g.trans e'), fun i n x => ?_⟩
  have hc : c (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (e i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [c]
    · simp [c, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply]
  rw [hc, hg, h, LinearEquiv.apply_symm_apply]

theorem tens_transport_symm {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f₁) : Tens R f :=
  tens_transport (fun i => (e i).symm) e'.symm
    (fun i n x => by rw [AddEquiv.symm_apply_eq, h, LinearEquiv.apply_symm_apply]) hT

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

def thM : SMor (thP (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))) (thP (nlFun γ 0 X q (κA O I)))
    (algebraMap O A) where
  G := ((nmO γ q).mor 0).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

theorem leC {c : A} {i : ℕ} (hc : c ∈ pdP γ i) (r : ℤ) :
    (thM γ q).LeC c (thFil _ (r - i)) (thFil _ r) := by
  intro T x hx
  have h1 : T.i c ∈ pdP T.δ i := dividedPowerFiltration_map T.compat i hc
  have h2 : x ∈ pdP T.δ (r - i).toNat := hx
  have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ _ _ (Ideal.mul_mem_mul h1 h2)
  exact T.pdPow_anti (by omega) h3

end

abbrev rq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    CH.Mor (sq (sFil Q r) (sFil Q r')) (sq (sFil Q' r) (sFil Q' r')) (RingHom.id _) :=
  (incl h).sq (incl_fil h r) (incl_fil h r')

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) {m : ℕ} (S : GrSplit O γ m)

theorem leS (𝒱 : Set X.Opens) (i : Fin m) (n : S.N i) (r : ℤ) :
    (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
  fun T x hx => leC γ q (S.mem i n) r T.obj x hx

abbrev mC (𝒱 : Set X.Opens) (r r' : ℤ) (i : Fin m) (n : S.N i) :=
  (smO γ q l s 𝒱).sqC (S.ν i n) (leS γ q l s S 𝒱 i n r) (leS γ q l s S 𝒱 i n r')

def BcAt (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) : Prop :=
  Tens O (N := S.N) (M := fun i => HQ (TO q l s 𝒱) (r - i) (r' - i) j) (M' := HQ (TS γ q l s 𝒱) r r' j)
    fun i n x => (mC γ q l s S 𝒱 r r' i n).pull j x

variable {γ q l s}

theorem st_top {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {p : ℕ} {κ : O →+* R ⧸ J}
    (Q : ObjectProperty (Thick (nlFun δ p X q κ))) (𝒱 : Set X.Opens) : St Q 𝒱 ≤ St Q {⊤} := by
  rintro T ⟨h, V, -, -⟩
  exact ⟨h, ⊤, rfl, fun _ _ => trivial⟩

theorem comm_top (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) (i : Fin m) (n : S.N i) (x) :
    (rq (st_top (TF l s) 𝒱) r r').pull j ((mC γ q l s S {⊤} r r' i n).pull j x) =
    (mC γ q l s S 𝒱 r r' i n).pull j ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j x) := by
  refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (mC γ q l s S {⊤} r r' i n) (rq (st_top (TF l s) 𝒱) r r') j x).1).symm.trans
    (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (rq (st_top (TF l s) 𝒱) (r - i) (r' - i)) (mC γ q l s S 𝒱 r r' i n) j x).1))
  refine CrystallineSemistableComparison.P.prism (σ := algebraMap O A) ((mC γ q l s S {⊤} r r' i n).comp (rq (st_top (TF l s) 𝒱) r r'))
    ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).comp (mC γ q l s S 𝒱 r r' i n)) (𝟙 _) (fun T y => ?_) j x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  first
    | rfl
    | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)

theorem used_TF {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} (l s : ℕ) :
    Used (TF l s : ObjectProperty (Thick (nlFun δ 0 X q κ))) :=
  Or.inl ⟨rfl, l, s, rfl⟩

theorem bcAt_iff (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (j : ℕ) :
    BcAt γ q l s S {⊤} r r' j ↔ BcAt γ q l s S 𝒱 r r' j := by
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := fun W hW => by rw [h𝒱]; exact le_top
  have bO := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk (⊥ : Ideal O)) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  have bA := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := γ) (p := 0) (q := q) (κ := κA O I) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  let eO : ∀ i : Fin m, HQ (TO q l s {⊤}) (r - i) (r' - i) j ≃ₗ[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j := fun i =>
    LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j) (bO _ _)
  let eA : HQ (TS γ q l s {⊤}) r r' j ≃+ HQ (TS γ q l s 𝒱) r r' j :=
    (LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) r r').pull j) (bA _ _)).toAddEquiv
  have hcomm : ∀ i n x, eA ((mC γ q l s S {⊤} r r' i n).pull j x) = (mC γ q l s S 𝒱 r r' i n).pull j (eO i x) :=
    fun i n x => comm_top S 𝒱 r r' j i n x
  exact ⟨tens_transport eO eA hcomm, tens_transport_symm eO eA hcomm⟩

end

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {m : ℕ} (S : GrSplit O γ m)

abbrev thO (q : X ⟶ Spec (CommRingCat.of O)) (r r' : ℤ) :
    Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) ⥤ ModuleCat.{0} O :=
  sq (thFil _ r) (thFil _ r')

abbrev thS (r r' : ℤ) : Thick (nlFun γ 0 X q (κA O I)) ⥤ ModuleCat.{0} A :=
  sq (thFil _ r) (thFil _ r')

abbrev tM (r r' : ℤ) (i : Fin m) (n : S.N i) : CH.Mor (thO q (r - i) (r' - i)) (thS γ q r r') (algebraMap O A) :=
  (thM γ q).sqC (S.ν i n) (leC γ q (S.mem i n) r) (leC γ q (S.mem i n) r')

theorem tM_add (r r' : ℤ) (i : Fin m) (n n' : S.N i) (T) (x) :
    (tM γ q S r r' i (n + n')).τ T x = (tM γ q S r r' i n).τ T x + (tM γ q S r r' i n').τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (n + n')) * z' = algebraMap A B (S.ν i n) * z' + algebraMap A B (S.ν i n') * z' := by
    rw [map_add (f := _), map_add (f := _), add_mul]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

theorem tM_smul (r r' : ℤ) (i : Fin m) (c : O) (n : S.N i) (T) (x) :
    (tM γ q S r r' i (c • n)).τ T x = algebraMap O A c • (tM γ q S r r' i n).τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (c • n)) * z' = algebraMap O A c • (algebraMap A B (S.ν i n) * z') := by
    rw [map_smul, Algebra.smul_def c, map_mul, mul_assoc, Algebra.smul_def (algebraMap O A c)]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

end

theorem main : KH.GlobBcSt → BcOn True → BcOn False := by
  intro hG hT O A _ _ _ I γ l s m hO hA S X q 𝒱 hc r r' hrr hr's ha hb j
  obtain ⟨U, h𝒱⟩ : Nonempty (Cov q) ∧ sSup 𝒱 = ⊤ := by
    rcases hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h.elim
    · exact h
  obtain ⟨U⟩ := U
  have hU : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hmem : ∀ (𝒲 : Set X.Opens) (T), St (TF l s) 𝒲 T → St (TF l s) 𝒲 ((((nmO γ q).mor 0).functor).obj T) :=
    fun 𝒲 T h => nmO_mem γ q l s 𝒲 T h
  have key : ∀ j, BcAt γ q l s S (Set.range U.U) r r' j := fun j =>
    hG (O := O) (R := O) (I := ⊥) (γ := dividedPowersBot O) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥)
      (O' := O) (R' := A) (I' := I) (γ' := γ) (p' := 0) (X' := X) (q' := q) (κ' := κA O I)
      (Λ := O) (Λ' := A) (σ := algebraMap O A) ((nmO γ q).mor 0).functor S.N
      (fun i => thO q (r - i) (r' - i)) (thS γ q r r')
      (fun i n T => (tM γ q S r r' i n).τ T) (fun i n {T T'} φ x => (tM γ q S r r' i n).nat φ x)
      (fun i n n' T x => tM_add γ q S r r' i n n' T x) (fun i c n T x => tM_smul γ q S r r' i c n T x)
      (TF l s) (TF l s) U.U U.U (fun α T h => hmem _ T h) (fun S' T h => hmem _ T h) (fun T h => hmem _ T h)
      (fun S' hS' j => by
        obtain ⟨α, hα⟩ := hS'
        obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S', U.U α) ≤ U.U α) (U.inter S' ⟨α, hα⟩)
        exact hT γ l s m hO hA S q {⨅ α ∈ S', U.U α} (Or.inl ⟨trivial, _, _, rfl, ⟨c'⟩⟩) r r' hrr hr's
          (fun i n => leS γ q l s S _ i n r) (fun i n => leS γ q l s S _ i n r') j) j
  exact (bcAt_iff S 𝒱 h𝒱 r r' j).1 ((bcAt_iff S (Set.range U.U) hU r r' j).2 (key j))

end GlobalTheory.CompanionTheory.GlobBc
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.twisted_jacquet_phi_minus_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m n : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), Nonempty (TwJacquet (phiMinus k ψ τ) (derUnipM k m n) (derCharM k ψ m n) ≃ₗ[ℂ] TwJacquet τ (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv | exact GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv | (intros; apply GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.central_character_eq_of_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
  first | exact @GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | exact GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | (intros; apply GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.central_character_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  first | exact @GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | exact GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | (intros; apply GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.central_character_twist_pow_degree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | exact GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | (intros; apply GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.jacquet_two_factor_central_character_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  first | exact @GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | exact GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | (intros; apply GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZlScalar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_absPow_range (u : kˣ) (n : ℕ) :
    ∏ a ∈ Finset.range n, ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ) =
      ((absPow k (((n * (n - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [← Finset.sum_range_id]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, Nat.cast_add, absPow_add, MonoidHom.mul_apply,
      Units.val_mul]

theorem prod_fin_absPow (l : ℕ) (c : ℂ) (u : kˣ) :
    ∏ a : Fin l, (c * ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)) =
      c ^ l * ((absPow k (((l * (l - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun a => ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)), prod_absPow_range]

theorem smul_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Surjective f)
    (g : G) (C : ℂ) (h : ∀ w, π g w = C • w) (v : W) : σ g v = C • v := by
  obtain ⟨w, rfl⟩ := hf v
  rw [← map_smul, ← h w]
  exact (Representation.IntertwiningMap.isIntertwining π σ f g w).symm

theorem exists_surjective_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π) :
    ∃ f : π.IntertwiningMap σ, Function.Surjective f :=
  let ⟨_, f, hf, _⟩ := h
  ⟨f, hf⟩

theorem smul_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π)
    (g : G) (C : ℂ) (hg : ∀ w, π g w = C • w) (v : W) : σ g v = C • v :=
  let ⟨f, hf⟩ := exists_surjective_of_isCosocle h
  smul_of_surjective f hf g C hg v

theorem scalarBy_term (Δ : Segment k) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) (a : Fin Δ.len) :
    Zl.ScalarBy (Δ.term a) t (c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) :=
  GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first ((a : ℕ) : ℂ) t c hc

theorem scalarBy_lseg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) (y : IrrGL (k := k)) (hy : IsLSeg Δ y.rep) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) :
    Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  rcases hy with ⟨hd, hco⟩
  have key := GlobalTheory.CompanionTheory.ZCentre.prodIrr_scalar k Δ.len y.1 Δ.term hd t (fun a => c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) (scalarBy_term Δ t c hc)
  simp only [prod_fin_absPow] at key
  intro v
  exact smul_of_isCosocle hco (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) _ key v

end GlobalTheory.CompanionTheory.ZlScalar
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.fine_jacquet_length_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_one | exact GlobalTheory.CompanionTheory.SegFine.fineJac_one | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_one <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.dual_class_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)), x.IsCusp → (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | exact GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | (intros; apply GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp <;> assumption)
end
