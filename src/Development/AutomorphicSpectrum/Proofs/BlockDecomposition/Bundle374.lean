module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle197
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle342
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle292
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle164
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle360
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle362
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle363
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcCov

theorem tens_transport {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    {A B : Type 1} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {S : Type} [CommRing S] {A' B' : Type 1} [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B']
    (f : Unit → N → A → A') (f' : Unit → N → B → B') (e : B →ₗ[R] A) (he : Function.Bijective e)
    (e' : B' →ₗ[S] A') (he' : Function.Bijective e') (comm : ∀ i n x, e' (f' i n x) = f i n (e x))
    (H : Tens R (N := fun _ : Unit => N) (M := fun _ => A) (M' := A') f) :
    Tens R (N := fun _ : Unit => N) (M := fun _ => B) (M' := B') f' := by
  obtain ⟨g, hg⟩ := H
  let E : B ≃ₗ[R] A := LinearEquiv.ofBijective e he
  let TE : N ⊗[R] B ≃ₗ[R] N ⊗[R] A := TensorProduct.congr (LinearEquiv.refl R N) E
  let P : (∀ _ : Unit, N ⊗[R] B) ≃+ (∀ _ : Unit, N ⊗[R] A) := AddEquiv.piCongrRight fun _ => TE.toAddEquiv
  let E' : B' ≃+ A' := (LinearEquiv.ofBijective e' he').toAddEquiv
  refine ⟨(P.trans g).trans E'.symm, fun i n x => ?_⟩
  apply E'.injective
  have hP : P (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ e x) := by
    funext k
    obtain rfl : k = i := Subsingleton.elim _ _
    simp [P, TE, E]
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hP, hg]
  exact (comm i n x).symm

section
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem pt_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (T : Thick (nlFun γ' p X q κ')) :
    pt ((m.mor p).functor.obj T) = pt T ≫ m.u := rfl

theorem inU_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (V : X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : InU V T) : InU V ((m.mor p).functor.obj T) := by
  unfold InU at h ⊢
  rw [pt_obj, hu, Category.comp_id]
  exact h

def tmor (m : NMor γ q κ γ' q κ' (algebraMap R R')) (p : ℕ) :
    SMor (thP (nlFun γ p X q κ)) (thP (nlFun γ' p X q κ')) (algebraMap R R') where
  G := (m.mor p).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end

abbrev aT {b : Base} (L : b.Fun) : IdF (thA L) := (thFil L 0).sup (IdF.span _ 0)

abbrev aB {b : Base} (L : b.Fun) : IdF (thA L) := (IdF.bot _).sup (IdF.span _ 0)

theorem aT_top {b : Base} (L : b.Fun) (T : Thick L) : (aT L).S T = ⊤ := by
  have h : (thFil L 0).S T = ⊤ := T.pdPow_zero
  exact top_le_iff.1 (h ▸ le_sup_left)

theorem aB_bot {b : Base} (L : b.Fun) (T : Thick L) : (aB L).S T = ⊥ := by
  change (⊥ : Ideal _) ⊔ Ideal.span {algebraMap b.R _ 0} = ⊥
  simp

theorem mapH_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K L : Cx.{1} R} {L' P : Cx.{1} R'}
    (φ : Cx.Hom K L' σ) (ψ : Cx.Hom L' P (RingHom.id R')) (φ' : Cx.Hom K L (RingHom.id R)) (ψ' : Cx.Hom L P σ) (n : ℕ)
    (h : ∀ z, ψ.f n (φ.f n z) = ψ'.f n (φ'.f n z)) (c : K.H n) : ψ.mapH n (φ.mapH n c) = ψ'.mapH n (φ'.mapH n c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (h z.1))

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem leC_top (f : SMor Φ Φ' σ) (c : R') (a : IdF Φ.A) (a' : IdF Φ'.A) (h : ∀ T, a'.S T = ⊤) : f.LeC c a a' :=
  fun T _ _ => by rw [h]; trivial

theorem leC_bot (f : SMor Φ Φ' σ) (c : R') (b : IdF Φ.A) (b' : IdF Φ'.A) (h : ∀ T, b.S (f.G.obj T) = ⊥) : f.LeC c b b' := by
  intro T x hx
  rw [h, Ideal.mem_bot] at hx
  subst hx
  rw [map_zero, mul_zero]
  exact Ideal.zero_mem _

theorem sqC_add (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c c' : R') (ha : f.LeC c a a') (hb : f.LeC c b b')
    (ha' : f.LeC c' a a') (hb' : f.LeC c' b b') (ha'' : f.LeC (c + c') a a') (hb'' : f.LeC (c + c') b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (c + c') ha'' hb'').τ T x = (f.sqC c ha hb).τ T x + (f.sqC c' ha' hb').τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * f.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * f.ρ T y)
  rw [map_add (f := _), add_mul, map_add (f := _)]

theorem sq_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : f.Le a a') (hb : f.Le b b') (T : C')
    (v : sqM a b (f.G.obj T)) :
    (show sqM a' b' T from (f.sq ha hb).τ T v).1 = Ideal.quotientMap (b'.S T) (f.ρ T) (fun y hy => hb T y hy) v.1 := rfl

theorem sqC_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c : R') (ha : f.LeC c a a') (hb : f.LeC c b b') (T : C')
    (v : sqM a b (f.G.obj T)) : (show sqM a' b' T from (f.sqC c ha hb).τ T v).1 = f.qC c hb T v.1 := rfl

end Gen

theorem sqC_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (f : SMor Φ Φ' (algebraMap R R')) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (r : R) (c : R')
    (ha : f.LeC c a a') (hb : f.LeC c b b') (ha' : f.LeC (r • c) a a') (hb' : f.LeC (r • c) b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (r • c) ha' hb').τ T x = algebraMap R R' r • (f.sqC c ha hb).τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (r • c) * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R R' r • (algebraMap R' _ c * f.ρ T y))
  refine congrArg (Ideal.Quotient.mk _) ?_
  rw [Algebra.smul_def r c, map_mul, mul_assoc, Algebra.smul_def (algebraMap R R' r)]

section Sq
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem st_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (𝒱 : Set X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : St ⊤ 𝒱 T) : St ⊤ 𝒱 ((m.mor p).functor.obj T) := by
  obtain ⟨-, W, hW, hi⟩ := h
  exact ⟨trivial, W, hW, inU_obj m hu W T hi⟩

theorem square_tau (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (T : Q₂'.FullSubcategory) (w : (sq (oT Q₁) (oB Q₁)).obj ((m.smor Q₁ Q₁' k₁).G.obj ((incl h').G.obj T))) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).τ T (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).τ _ w) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).τ T (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).τ _ w) := by
  obtain ⟨w, hw⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine Subtype.ext ?_
  refine (sq_val (incl h') _ _ T _).trans ?_
  refine Eq.trans ?_ (sqC_val (m.smor Q₂ Q₂' k₂) a ha₂ hb₂ T _).symm
  rw [sqC_val, sq_val]
  dsimp only
  refine (congrArg (Ideal.quotientMap _ _ _) (SMor.qC_mk (m.smor Q₁ Q₁' k₁) a hb₁ ((incl h').G.obj T) y)).trans ?_
  refine (Ideal.quotientMap_mk).trans ?_
  refine Eq.trans ?_ (congrArg ((m.smor Q₂ Q₂' k₂).qC a hb₂ T) Ideal.quotientMap_mk).symm
  refine Eq.trans ?_ (SMor.qC_mk (m.smor Q₂ Q₂' k₂) a hb₂ T _).symm
  rfl

theorem pull_square (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (j : ℕ) (x : CH.H (sq (oT Q₁) (oB Q₁)) j) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).pull j (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).pull j x) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).pull j (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).pull j x) :=
  mapH_square _ _ _ _ j (fun z => funext fun s => square_tau m h h' k₁ k₂ a ha₁ hb₁ ha₂ hb₂ _ _) x

end Sq

theorem bc_cover : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) (U : Cov q)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {⊤}) (hQ' : Q' = St ⊤ {⊤}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  intro O R R' _ _ _ _ _ I I' γ γ' p hp hn X q κ κ' m hu hg U Q Q' hQ hQ' h ha hb j
  subst hQ hQ'
  have hA : ∀ a : R', (tmor m p).LeC a (aT _) (aT _) := fun a => leC_top _ a _ _ (aT_top _)
  have hB : ∀ a : R', (tmor m p).LeC a (aB _) (aB _) := fun a => leC_bot _ a _ _ fun T => aB_bot _ _
  have A : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oT _) (oT _) := fun 𝒱 k a => leC_top _ a _ _ fun T => aT_top _ T.obj
  have B : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oB _) (oB _) := fun 𝒱 k a => leC_bot _ a _ _ fun T => aB_bot _ _
  have Hg : Tens R (N := fun _ : Unit => R')
      (M := fun _ => CH.H (sq (oT (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      (M' := CH.H (sq (oT (St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      fun _ a x => ((m.smor _ _ (st_obj m hu _)).sqC a (A _ (st_obj m hu _) a) (B _ (st_obj m hu _) a)).pull j x := by
    refine GlobalTheory.T.stable_cover_cech_vanishing.2.2 (m.mor p).functor (fun _ : Unit => R') (fun _ => sq (aT _) (aB _)) (sq (aT _) (aB _))
      (fun _ a T => ((tmor m p).sqC a (hA a) (hB a)).τ T) (fun _ a _ _ φ x => ((tmor m p).sqC a (hA a) (hB a)).nat φ x)
      (fun _ a a' T x => sqC_add (tmor m p) a a' (hA a) (hB a) (hA a') (hB a') (hA _) (hB _) T x) (fun _ r a T x => sqC_smul (tmor m p) r a (hA a) (hB a) (hA _) (hB _) T x)
      ⊤ ⊤ U.U U.U (fun _ => st_obj m hu _) (fun _ => st_obj m hu _) (st_obj m hu _) ?_ j
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    obtain ⟨c', -⟩ := coord_res (U.c α) (iInf₂_le α hα) (U.inter S hS)
    exact GlobalTheory.CompanionTheory.ChartLocBc.local_bc hp hn m hu hg c' _ _ rfl rfl (st_obj m hu _) (A _ _) (B _ _) j
  have h₁ : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have h₂ : St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := by
    rintro W rfl
    rw [sSup_range, U.cover]
  have b₁ := (zar (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₁ hc j).2.1 (some 0) none 0 0
  have b₂ := (zar (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₂ hc j).2.1 (some 0) none 0 0
  exact tens_transport _ _ _ b₁ _ b₂
    (fun _ a x => pull_square m h₁ h₂ h (st_obj m hu _) a (ha a) (hb a) (A _ _ a) (B _ _ a) j x) Hg

end GlobalTheory.CompanionTheory.BcCov
end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMirDer.NonZero

section Alg

variable {k : Type} [Field k]

theorem mir_zero_eq_one (g : Mir k 0) : g = 1 := by
  have h := (mem_Mir_iff k (g : GL (Fin 1) k)).1 g.2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
  have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
  subst hi
  subst hj
  have := congrFun h (Fin.last 0)
  simpa [eLast] using this

end Alg

theorem twKer_eq_bot_of_forall_eq_one {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (hN : ∀ n : N, n = 1) :
    twKer ρ N θ = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  rw [hN n]
  simp

theorem nontrivial_quot_of_not_mem {V : Type} [AddCommGroup V] [Module ℂ V] (p : Submodule ℂ V) (v : V)
    (hv : v ∉ p) : Nontrivial (V ⧸ p) :=
  nontrivial_of_ne (Submodule.Quotient.mk v) 0 (by rwa [Ne, Submodule.Quotient.mk_eq_zero])

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmb (n : ℕ) : Continuous (glEmb k n) := by
  apply Continuous.units_map
  show Continuous (glEmbMat k n)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases <;> simp [glEmbMat] <;>
      first | exact continuous_const | exact (continuous_apply _).comp (continuous_apply _) | fun_prop
  | cast i => induction j using Fin.lastCases <;> simp [glEmbMat] <;>
      first | exact continuous_const | exact (continuous_apply _).comp (continuous_apply _) | fun_prop

theorem continuous_levi_comp_subtype (m : ℕ) : Continuous ((levi k (m + 1)).comp (Mir k m).subtype) :=
  continuous_induced_rng.2 ((continuous_glEmb (m + 1)).comp continuous_subtype_val)

end Top

theorem exists_derivative_nontrivial (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ψ ≠ 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V),
      IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ τ _ hV
    refine ⟨0, le_rfl, ?_⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply nontrivial_quot_of_not_mem _ v
    rw [twKer_eq_bot_of_forall_eq_one τ _ _ (fun n => Subtype.ext (mir_zero_eq_one _))]
    exact hv
  | succ m ih =>
    intro V _ _ τ hτ hV
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    by_cases h1 : v ∈ twKer τ (MirUin k (m + 1)) 1
    · have hex : ∃ g : GL (Fin (m + 1)) k,
          τ (levi k (m + 1) g) v ∉ twKer τ (MirUin k (m + 1)) (mirChar k ψ m) := by
        by_contra hcon
        push_neg at hcon
        exact hv (GlobalTheory.T.smooth_mirabolic_kernel_eq_zero k ψ hψc hψ m V τ hτ v h1 hcon)
      obtain ⟨g, hg⟩ := hex
      haveI := nontrivial_quot_of_not_mem _ _ hg
      have hs : IsSmooth (phiMinus k ψ τ) :=
        GlobalTheory.T.twisted_action_smooth τ hτ _ _ _ (continuous_levi_comp_subtype m) (levi_stab ψ m)
      obtain ⟨n, hn, hnt⟩ := ih _ (phiMinus k ψ τ) hs inferInstance
      obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ m n hn V τ
      exact ⟨n, hn.trans (Nat.le_succ m), e.injective.nontrivial⟩
    · refine ⟨m + 1, le_rfl, ?_⟩
      apply nontrivial_quot_of_not_mem _ v
      rwa [← GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ (m + 1) V τ]

end GlobalTheory.CompanionTheory.BZMirDer.NonZero

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.CentralExp

theorem continuous_scalarGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k) := by
  have hs : Continuous (fun a : k => Matrix.scalar (Fin n) a) := by
    have : (fun a : k => Matrix.scalar (Fin n) a) = fun a => Matrix.diagonal (fun _ => a) := by
      funext a; rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hs.comp Units.continuous_val
  · exact hs.comp (Units.continuous_val.comp continuous_inv)

theorem norm_scalarBy_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  intro k _ _ _ _ x hx
  have hirr := x.2.rep.irr
  obtain ⟨v, hv⟩ : ∃ v : x.2.rep.V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton x.2.rep.V := ⟨fun a b => by rw [hcon a, hcon b]⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Subrepresentation x.rep)
    exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have huniq : ∀ (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
    intro t c c' h h'
    exact smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  choose f hf using GlobalTheory.T.central_character_exists k x
  have hmul : ∀ a b : kˣ, f (a * b) = f a * f b := by
    intro a b
    refine huniq (a * b) _ _ (hf _) fun w => ?_
    rw [map_mul, map_mul, Module.End.mul_apply, hf b w, map_smul, hf a w, smul_smul, mul_comm]
  have hone : f 1 = 1 := by
    refine huniq 1 _ _ (hf _) fun w => ?_
    simp
  let χ₀ : kˣ →* ℂ := { toFun := f, map_one' := hone, map_mul' := hmul }
  let χ : kˣ →* ℂˣ := χ₀.toHomUnits
  have hχ : ∀ t, ((χ t : ℂˣ) : ℂ) = f t := fun t => rfl
  have hsm : IsSmoothChar χ := by
    have hset : (χ.ker : Set kˣ) = (Matrix.GeneralLinearGroup.scalar (Fin x.1) : kˣ →* GL (Fin x.1) k) ⁻¹'
        {g | x.rep g v = v} := by
      ext t
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]
      rw [hf t v]
      constructor
      · intro h
        have : f t = 1 := by rw [← hχ, h]; rfl
        rw [this, one_smul]
      · intro h
        have : f t = 1 := smul_left_injective ℂ hv (by simpa using h)
        exact Units.ext (by rw [hχ, this]; rfl)
    show IsOpen (χ.ker : Set kˣ)
    rw [hset]
    exact (x.2.rep.smooth v).preimage (continuous_scalarGL k x.1)
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k χ hsm
  have hn : (x.1 : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ⟨s / x.1, fun t c hc => ?_⟩
  rw [huniq t c (f t) hc (hf t), ← hχ, hs t, mul_div_cancel₀ _ hn]

end GlobalTheory.CompanionTheory.CentralExp
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.congruence_subgroup_finite_volume : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KmVol.measure_image_Km_lt_top | exact GlobalTheory.CompanionTheory.KmVol.measure_image_Km_lt_top | (intros; apply GlobalTheory.CompanionTheory.KmVol.measure_image_Km_lt_top <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.cartan_decomposition_congruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m : ℕ), 1 ≤ m → 1 ≤ N → ∃ s : Finset (GL (Fin N) k × GL (Fin N) k), (∀ p ∈ s, p.1 ∈ KO k (Fin N) ∧ p.2 ∈ KO k (Fin N)) ∧ ∀ h : GL (Fin N) k, ∃ p ∈ s, ∃ g : Fin (N - 1) → ℕ, ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, ∃ z ∈ Subgroup.center (GL (Fin N) k), h = p.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.2 * z := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CartanCover.cartan_cover | exact GlobalTheory.CompanionTheory.Dblock.CartanCover.cartan_cover | (intros; apply GlobalTheory.CompanionTheory.Dblock.CartanCover.cartan_cover <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.congruence_subgroup_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | exact GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | (intros; apply GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.congruence_subgroup_basis_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (U : Set (GL (Fin N) k)), IsOpen U → (1 : GL (Fin N) k) ∈ U → ∃ m : ℕ, 1 ≤ m ∧ (Zls.Km k N m : Set (GL (Fin N) k)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset | exact GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset | (intros; apply GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.matrix_coefficient_cartan_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (m : ℕ) (v : V), v ∈ fixed π (Zls.Km k N m) → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → (π p2 v ∈ fixed π (Zls.Km k N m)) ∧ (∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1) ∧ ∀ (D : GL (Fin N) k), ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, l (π (p1 * x * D * y * p2) v) = (l ∘ₗ π p1) (π D (π p2 v)) := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset | exact GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset | (intros; apply GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.uniformizer_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Filter.Tendsto (fun n : ℕ => ((Zls.unifU k : kˣ) : k) ^ n) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow | exact GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow | (intros; apply GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.segment_dual_precedes_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k), (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes | exact GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes | (intros; apply GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes <;> assumption)
end
