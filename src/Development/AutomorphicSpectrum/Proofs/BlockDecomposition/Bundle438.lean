module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle196
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThetaEx

section Gen
variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}
  (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

theorem arrow_ex (T : Thick (F.cr b ht κ)) (g' : s.R →+* T.B ⧸ T.J)
    (hg' : F.Pt.map (CommRingCat.ofHom g') s.y₀ = T.y.1.2) (u : Fin d → T.B)
    (hu : ∀ k, Ideal.Quotient.mk T.J (u k) = g' (s.T k)) :
    ∃ c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, -, hg, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  obtain ⟨g₀, -, h₀⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have e : g' = g := (h₀ g' hg').trans (h₀ g hg).symm
  subst e
  exact (hU u hu).exists

theorem arrow_uniq (T : Thick (F.cr b ht κ)) (c c' : liftObj s ht 𝓛 δ hδ hp hn ⟶ T)
    (h : ∀ k, c.φ (𝓛.t k) = c'.φ (𝓛.t k)) : c = c' := by
  obtain ⟨g, hc, -, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  exact (hU (fun k => c'.φ (𝓛.t k)) (fun k => hc c' _ _ (𝓛.hT k).symm)).unique h fun _ => rfl

end Gen

theorem gamma_comp {C C₀ : Type*} [Category C] [Category C₀] {j : C₀ ⥤ C} {U : UF C} {d : ℕ} {D T : C}
    (A : Act j U d D) (a : Gam d) (θ : D ⟶ T) :
    (A.γ a).asHom ≫ θ = A.act (fun k => U.q T ^ (Multiplicative.toAdd a k)) θ := by
  change A.act _ (𝟙 D) ≫ θ = _
  rw [A.act_comp, Category.id_comp]
  congr 1
  funext k
  rw [map_pow, U.map_q]

theorem i_qU {l : ℕ} [Fact l.Prime] (ε : Eps l) (A : PAlg l) (n : ℕ) :
    mapAcr A.fromBase n (ε.qU n : (base l).Acr n) = A.toAcr n (WittVector.teichmuller l (A.s (ε.e 0))) := by
  rw [ε.qU_val, mapAcr_cris, ε.cris_qk]

theorem teich_step {l : ℕ} [Fact l.Prime] (A : PAlg l) (f : A ⟶ A) (n m : ℕ) (e c : A.A)
    (h : Hom.f f c = e ^ m * c) :
    A.toAcr n (WittVector.teichmuller l e) ^ m * A.toAcr n (WittVector.teichmuller l c) =
      mapAcr f n (A.toAcr n (WittVector.teichmuller l c)) := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_mul, map_pow, map_mul, map_pow]

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (A : Act (𝟭 _) (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) d (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (A' : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj), (∀ (T : Thick (Lc F κ k n)) (a : Fin d → (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)).U T) (c : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ T) (j : Fin d), (A.act a c).φ (𝓛.t j) = ((a j).1 : T.B) * c.φ (𝓛.t j)) → (∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (j : Fin d), PAlg.Hom.f (A'.act a φ).hom (𝒯.c j 0).val = ((a j).1 : T.1.A) * PAlg.Hom.f φ.hom (𝒯.c j 0).val) → ∃ θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj, (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) ∧ ∀ a, (A.γ a).asHom ≫ θ = θ ≫ (gE F κ k n).map (A'.γ a).asHom := by
  intro l _ O _ F κ d s 𝒯 k n 𝓛 δ hδ hp hn ε A A' hA hA'
  have hy : F.Pt.map (CommRingCat.ofHom ((uJ k 𝒯.A n).comp 𝒯.g)) s.y₀ = ((gE F κ k n).obj 𝒯.obj).y.1.2 := by
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
    rfl
  have hu : ∀ j, Ideal.Quotient.mk (JJ k 𝒯.A n) (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) =
      (uJ k 𝒯.A n).comp 𝒯.g (s.T j) := fun j => by
    rw [RingHom.comp_apply, ← 𝒯.c_sharp j]
    exact (uJ_th k 𝒯.A n _).symm
  obtain ⟨θ, hθ⟩ := arrow_ex s rfl 𝓛 δ hδ hp hn ((gE F κ k n).obj 𝒯.obj) ((uJ k 𝒯.A n).comp 𝒯.g) hy
    (fun j => 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) hu
  refine ⟨θ, hθ, fun a => arrow_uniq s rfl 𝓛 δ hδ hp hn _ _ _ fun j => ?_⟩
  have h1 : ((A.γ a).asHom ≫ θ).φ (𝓛.t j) =
      𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.A.s (ε.e 0))) ^ (Multiplicative.toAdd a j) *
        𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A)) := by
    rw [gamma_comp A a θ, hA _ _ θ j, hθ j, ← i_qU]
    rfl
  have h2 : PAlg.Hom.f (A'.γ a).asHom.hom (𝒯.c j 0).val =
      (𝒯.A.s (ε.e 0)) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val := hA' 𝒯.obj _ (𝟙 𝒯.obj) j
  have h3 : (θ ≫ (gE F κ k n).map (A'.γ a).asHom).φ (𝓛.t j) =
      mapAcr (A'.γ a).asHom.hom n (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) :=
    congrArg (mapAcr (A'.γ a).asHom.hom n) (hθ j)
  rw [h1, h3]
  exact teich_step 𝒯.A _ n _ _ _ h2

end GlobalTheory.CompanionTheory.ThetaEx
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerHom

theorem exists_roots {R : Type} [CommRing R] {l : ℕ} (h : ∀ x : R, ∃ y, y ^ l = x) (u : R) :
    ∃ y : ℕ → R, y 0 = u ∧ ∀ m, y (m + 1) ^ l = y m := by
  choose r hr using h
  exact ⟨fun m => Nat.rec u (fun _ z => r z) m, rfl, fun m => hr _⟩

theorem roots_unique {R : Type} [CommRing R] {l : ℕ} (h : ∀ x y : R, x ^ l = y ^ l → x = y) {y z : ℕ → R}
    (h0 : y 0 = z 0) (hy : ∀ m, y (m + 1) ^ l = y m) (hz : ∀ m, z (m + 1) ^ l = z m) (m : ℕ) : y m = z m := by
  induction m with
  | zero => exact h0
  | succ m ih => exact h _ _ (by rw [hy, hz, ih])

theorem pow_sub_pow {R : Type} [CommRing R] {l : ℕ} (F : R →+* R) (hF : ∀ x, F x = x ^ l) (x y : R) (m : ℕ) :
    x ^ l ^ m - y ^ l ^ m = (x - y) ^ l ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ l m, pow_mul, pow_mul, pow_mul, ← ih, ← hF, ← hF, ← hF, map_sub]

theorem iter_root {R : Type} [CommRing R] {l : ℕ} {x : ℕ → R} (hx : ∀ m, x (m + 1) ^ l = x m) (m : ℕ) :
    x m ^ l ^ m = x 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ' l m, pow_mul, hx, ih]

variable {l : ℕ} [Fact l.Prime]

theorem pow_char (A : PAlg l) (x : A.A) : A.frob x = x ^ l := rfl

theorem pow_inj (A : PAlg l) (x y : A.A) (h : x ^ l = y ^ l) : x = y := A.frob_bijective.1 h

theorem pow_surj (A : PAlg l) (x : A.A) : ∃ y, y ^ l = x := A.frob_bijective.2 x

theorem eq_of_roots_mod (A : PAlg l) {x y : ℕ → A.A} (hx : ∀ m, x (m + 1) ^ l = x m) (hy : ∀ m, y (m + 1) ^ l = y m)
    (h : ∀ m, x m - y m ∈ Ideal.span {A.pi}) : x 0 = y 0 := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hH : IsHausdorff (Ideal.span {A.s (pFlat l)}) A.A := A.compl.toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun n => ?_)
  rw [SModEq.zero, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id, ← iter_root hx n, ← iter_root hy n,
    pow_sub_pow A.frob (pow_char A)]
  exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl).le (Ideal.pow_mem_pow (h n) _)

theorem mapU_mem {A A' : PAlg l} (φ : A ⟶ A') {x : A.U} (hx : x ∈ Ideal.span {(l : A.U)}) :
    mapU φ x ∈ Ideal.span {(l : A'.U)} := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_sharp_cong (A : PAlg l) (x : A.U) : ∃ a, A.sharp a - x ∈ Ideal.span {(l : A.U)} := by
  obtain ⟨a, ha⟩ := (RL.u_mod A).1 (Ideal.Quotient.mk _ x)
  refine ⟨a, ?_⟩
  rw [A.sharpMap_eq] at ha
  simpa using Ideal.Quotient.eq.1 ha

def modEquiv (A : PAlg l) : (A.A ⧸ Ideal.span {A.pi}) ≃+* A.Un 1 :=
  (Ideal.quotEquivOfEq (RL.u_mod A).2.symm).trans (RingHom.quotientKerEquivOfSurjective (RL.u_mod A).1)

theorem modEquiv_mk (A : PAlg l) (a : A.A) : modEquiv A (Ideal.Quotient.mk _ a) = A.aToU1 a := rfl

def gBar (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) : R →+* A.A ⧸ Ideal.span {A.pi} :=
  ((modEquiv A).symm : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi}).comp ((Ideal.Quotient.mk _).comp g)

theorem gBar_iff (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) (r : R) (a : A.A) :
    gBar A g r = Ideal.Quotient.mk _ a ↔ A.sharp a - g r ∈ Ideal.span {(l : A.U)} := by
  have e : gBar A g r = (modEquiv A).symm (Ideal.Quotient.mk _ (g r)) := rfl
  rw [e, RingEquiv.symm_apply_eq, modEquiv_mk, A.sharpMap_eq, eq_comm, Ideal.Quotient.eq, pow_one]


open CrystallineSemistableComparison.PAlg in
theorem core {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (A' : PAlg l)
    (g : s.R →+* A'.U) (hga : g.comp s.a = A'.oC.comp κ) (u : Fin d → A'.A) (hu : ∀ k, A'.sharp (u k) = g (s.T k)) :
    ∃ φ : 𝒯.A ⟶ A', ((mapU φ).comp 𝒯.g = g ∧ ∀ k, Hom.f φ (𝒯.c k 0).val = u k) ∧
      ∀ φ' : 𝒯.A ⟶ A', (mapU φ').comp 𝒯.g = g → (∀ k, Hom.f φ' (𝒯.c k 0).val = u k) → φ' = φ := by
  have hy : ∀ k, ∃ y : ℕ → A'.A, y 0 = u k ∧ ∀ m, y (m + 1) ^ l = y m := fun k => exists_roots (pow_surj A') (u k)
  choose y hy0 hys using hy
  have hc : ∀ k m, ((𝒯.c k (m + 1)).val) ^ l = (𝒯.c k m).val := fun k m => by
    rw [← Units.val_pow_eq_pow_val, 𝒯.c_succ]
  have ho : ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (pFlat l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have h1 : ∀ x w, theta0 l w = κ x → gBar A' g (s.a x) = ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (w.coeff 0) := by
    intro x w hw
    have hcf : (A'.sW w).coeff 0 = A'.s (w.coeff 0) := WittVector.map_coeff _ _ _
    refine (gBar_iff A' g _ _).2 ?_
    have e1 : g (s.a x) = A'.th (A'.sW w) := by
      rw [← A'.oC_theta0, hw]
      exact RingHom.congr_fun hga x
    have e2 := A'.sharpMap_coeff (A'.sW w)
    rw [hcf, A'.sharpMap_eq] at e2
    rw [e1]
    simpa using Ideal.Quotient.eq.1 e2
  have h2 : ∀ k, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k 0) = gBar A' g (s.T k) := fun k =>
    ((gBar_iff A' g _ _).2 (by rw [hy0, hu, sub_self]; exact Ideal.zero_mem _)).symm
  have h3 : ∀ k m, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k (m + 1)) ^ l = Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k m) :=
    fun k m => by rw [← map_pow, hys]
  obtain ⟨f, ⟨hfo, hfg, hfc⟩, hfu⟩ := 𝒯.univ (A'.A ⧸ Ideal.span {A'.pi}) ((Ideal.Quotient.mk _).comp A'.s) (gBar A' g)
    (fun k m => Ideal.Quotient.mk _ (y k m)) ho h1 h2 h3
  obtain ⟨φ, hφ, hφu⟩ := GlobalTheory.CompanionTheory.PerfLift.existsUnique_hom 𝒯.A A' f hfo
  have hφa : ∀ a, Ideal.Quotient.mk (Ideal.span {A'.pi}) (Hom.f φ a) = f a := fun a => RingHom.congr_fun hφ a
  have hck : ∀ k, Hom.f φ (𝒯.c k 0).val = u k := by
    intro k
    rw [← hy0 k]
    refine eq_of_roots_mod A' (x := fun m => Hom.f φ (𝒯.c k m).val) (fun m => ?_) (hys k) fun m => ?_
    · rw [← map_pow, hc]
    · refine Ideal.Quotient.eq.1 ?_
      rw [hφa, hfc]
  have hgφ : (mapU φ).comp 𝒯.g = g := by
    have hE := GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete (Ideal.span {(l : A'.U)}) A'.completeU
      (MvPolynomial (Fin d) O) s.R (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R)) s.et
      (g.comp (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R))) ((Ideal.Quotient.mk _).comp g) rfl
    refine hE.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun o => ?_) fun k => ?_
      · have e1 : 𝒯.g (s.a o) = 𝒯.A.oC (κ o) := RingHom.congr_fun 𝒯.hg o
        have e2 : g (s.a o) = A'.oC (κ o) := RingHom.congr_fun hga o
        simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        rw [e1, e2, mapU_oC]
      · simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        rw [← 𝒯.c_sharp, mapU_sharp, hck, hu]
    · refine RingHom.ext fun r => ?_
      obtain ⟨a, ha⟩ := exists_sharp_cong 𝒯.A (𝒯.g r)
      have e : gBar A' g r = Ideal.Quotient.mk _ (Hom.f φ a) := by rw [hφa]; exact (hfg r a ha).symm
      have e1 := (gBar_iff A' g r _).1 e
      have e2 := mapU_mem φ ha
      rw [map_sub, mapU_sharp] at e2
      refine Ideal.Quotient.eq.2 ?_
      have e3 : mapU φ (𝒯.g r) - g r = (A'.sharp (Hom.f φ a) - g r) - (A'.sharp (Hom.f φ a) - mapU φ (𝒯.g r)) := by ring
      change mapU φ (𝒯.g r) - g r ∈ _
      rw [e3]
      exact Ideal.sub_mem _ e1 e2
  refine ⟨φ, ⟨hgφ, hck⟩, fun φ' hg' hk' => hφu φ' (hfu _ ⟨?_, ?_, ?_⟩)⟩
  · rw [RingHom.comp_assoc, Hom.comm]
  · intro r a ha
    have e2 := mapU_mem φ' ha
    rw [map_sub, mapU_sharp] at e2
    have e3 : mapU φ' (𝒯.g r) = g r := RingHom.congr_fun hg' r
    rw [e3] at e2
    exact ((gBar_iff A' g r _).2 e2).symm
  · intro k m
    have := roots_unique (pow_inj A') (y := fun m => Hom.f φ' (𝒯.c k m).val) (z := y k)
      ((hk' k).trans (hy0 k).symm) (fun m => by
        rw [← map_pow, hc]) (hys k) m
    exact congrArg (Ideal.Quotient.mk _) this

theorem tower_hom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  intro l _ O _ F κ d s 𝒯 T
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of T.1.U) T.2.1 (T.1.oC.comp κ) T.2.2
  have hga : g.comp s.a = T.1.oC.comp κ :=
    F.ov_uniq (hg ▸ F.ov_map (CommRingCat.ofHom g) s.ov) T.2.2
  have hall : ∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g := by
    intro φ
    refine hgu _ ?_
    have h1 : F.Pt.map (CommRingCat.ofHom (mapU φ.1)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1 :=
      congrArg Subtype.val φ.2
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ.1).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
      exact h1
    exact h2
  refine ⟨g, hg, hall, fun u hu => ?_⟩
  obtain ⟨φ, ⟨hφg, hφk⟩, hφu⟩ := core 𝒯 T.1 g hga u hu
  have hpt : (F.pt κ).map φ 𝒯.obj.2 = T.2 := by
    refine Subtype.ext ?_
    change F.Pt.map (CommRingCat.ofHom (mapU φ)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [hφg]
      exact hg
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp] at h2
    exact h2
  refine ⟨⟨φ, hpt⟩, hφk, fun φ' hk => CategoryTheory.Functor.Elements.Hom.ext (hφu φ'.1 (hall φ') hk)⟩

end GlobalTheory.CompanionTheory.TowerHom
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaRed

universe w₁ w₂ w₃ w₄ u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

theorem square_pull {R : Type} [CommRing R] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R} {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (a : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₄ (RingHom.id R))
    (c : CH.Mor F₁ F₃ (RingHom.id R)) (d : CH.Mor F₃ F₄ (RingHom.id R))
    (η : d.G ⋙ c.G ⟶ b.G ⋙ a.G)
    (hτ : ∀ T x, b.τ T (a.τ (b.G.obj T) ((F₁.map (η.app T)).hom x)) = d.τ T (c.τ (d.G.obj T) x))
    (j : ℕ) (x : CH.H F₁ j) : b.pull j (a.pull j x) = d.pull j (c.pull j x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) a b j x).1, ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) c d j x).1]
  exact (CrystallineSemistableComparison.P.prism (c.comp d) (a.comp b) η hτ j x).symm

theorem map_map_eq (P : CommRingCat.{0} ⥤ Type) {A B D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ D)
    (h : f ≫ g = f') (y : P.obj A) : P.map g (P.map f y) = P.map f' y := by
  subst h
  rw [Functor.map_comp_apply]

variable {l : ℕ} [Fact l.Prime]

theorem uJ_red (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) (e) :
    (Ideal.quotientMap (JJ k A n) (A.red h) e).comp (uJ k A m) = uJ k A n := RingHom.ext fun x => by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

abbrev redCr (k : Bool) {m n : ℕ} (h : n ≤ m) :
    GlobalTheory.LogCris.Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl (dd_red k _ h)
    (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

def redTh (k : Bool) {m n : ℕ} (h : n ≤ m) (T : (F.pt κ).Elements) :
    gObj F κ k m T ⟶ (redCr F κ k h).obj (gObj F κ k n T) :=
  crHom (T := gObj F κ k m T) (T' := (redCr F κ k h).obj (gObj F κ k n T)) (T.1.red h)
    (fun r => (pdOk_hom T.1.fromBase).red_acr h r) (dd_red k T.1 h) fun e => by
      exact map_map_eq F.Pt (CommRingCat.ofHom (uJ k T.1 m)) (CommRingCat.ofHom (Ideal.quotientMap (JJ k T.1 n) (T.1.red h) e))
        (CommRingCat.ofHom (uJ k T.1 n)) (CommRingCat.hom_ext (uJ_red k T.1 h e)) T.2.1

def redNat (k : Bool) {m n : ℕ} (h : n ≤ m) :
    (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).G ⋙ (βMor F κ k m).G ⟶ (βMor F κ k n).G ⋙ (redMor F κ k h).G where
  app T := redTh F κ k h ((jE (F.pt κ)).obj T)
  naturality T T' f := Thick.Hom.ext (RingHom.ext fun x => (pdOk_hom f.1.hom).red_acr h x) (funext fun j => j.elim)

theorem beta_red (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j) :
    β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x) :=
  square_pull (redMor F κ k h) (βMor F κ k n) (βMor F κ k m) (CH.Mor.ofNatTrans (redEl (F.pt κ) h))
    (redNat F κ k h) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaRed
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaCmp

theorem quotientMap_factor {B : Type} [CommRing B] {I J K : Ideal B} (hJ : I ≤ J) (hK : I ≤ K) (h : J ≤ K.comap (RingHom.id B))
    (w : B ⧸ I) : Ideal.quotientMap K (RingHom.id B) h (Ideal.Quotient.factor hJ w) = Ideal.Quotient.factor hK w := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem pt_uJ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (A : PAlg l) (n : ℕ) (y : F.Pt.obj (CommRingCat.of A.U))
    (h : JJ false A n ≤ (JJ true A n).comap (RingHom.id _)) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap (JJ true A n) (RingHom.id _) h)) (F.Pt.map (CommRingCat.ofHom (uJ false A n)) y) =
      F.Pt.map (CommRingCat.ofHom (uJ true A n)) y := by
  have e : (Ideal.quotientMap (JJ true A n) (RingHom.id _) h).comp (uJ false A n) = uJ true A n :=
    RingHom.ext fun x => quotientMap_factor (fil_le false A n) (fil_le true A n) h _
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

theorem β_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x := by
  intro l _ O _ F κ n j x
  have e : β F κ true n j ((cmpMor F κ n).pull j x) =
      ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n)).pull j x :=
    pull_pull (RingHom.id _) (cmpMor F κ n) (βMor F κ true n) j x
  refine e.trans ?_
  refine (cr_pull_eq (βMor F κ false n) ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n))
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (T.1.obj.dp_fil_pfil n) ?_) ?_ ?_ j x).symm
  · intro h
    exact pt_uJ F T.1.obj n T.2.1 h
  · intro T T' f z; rfl
  · intro T z; rfl

end GlobalTheory.CompanionTheory.BetaCmp
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisUnit

universe w w' u v u' v'

theorem pull_oneH {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : ∀ s : ComposableArrows C' 1, (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A'.map (GlobalTheory.CatH.toLast i s)).hom 1 : A'.obj _) = 0 := by
    intro s
    rw [Fin.sum_univ_two, map_one, map_one]
    simp
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ ?_).trans ?_
  · rw [e]
    exact funext c
  · exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem omMor_oneH {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
    (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) :
    (omMor m σ₀ h).pull 0 (CH.oneH (OA L c)) = CH.oneH (OA L' c') :=
  pull_oneH _ _ _ fun _ => rfl

theorem redHc_oneH : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m), redHc F κ k h 0 (CH.oneH (OcA F κ k m)) = CH.oneH (OcA F κ k n) := by
  intro l _ O _ F κ k m n h
  exact omMor_oneH _ _ _

end GlobalTheory.CompanionTheory.CrisUnit
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupTrans

theorem omMor_cup {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} (h : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    {p q s : ℕ} (e : p + q = s) (x : CH.H (OM L c) p) (y : CH.H (OM L c) q) :
    (omMor m (RingHom.id Λ) h).pull s ((CH.mulP (OA L c)).cup e x y) =
      (CH.mulP (OA L' c')).cup e ((omMor m (RingHom.id Λ) h).pull p x) ((omMor m (RingHom.id Λ) h).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (CH.mulP (OA L c)) (CH.mulP (OA L' c')) m.functor (omMor m (RingHom.id Λ) h).τ
    (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).nat
    (omMor m (RingHom.id Λ) h).nat (omMor m (RingHom.id Λ) h).nat (fun _ _ _ => rfl) e x y

theorem redHc_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) {i j s : ℕ} (e : i + j = s) (x : Hc F κ k m i) (y : Hc F κ k m j), redHc F κ k h s ((CH.mulP (OcA F κ k m)).cup e x y) = (CH.mulP (OcA F κ k n)).cup e (redHc F κ k h i x) (redHc F κ k h j y) := by
  intro l _ O _ F κ k m n h i j s e x y
  exact omMor_cup _ _ e x y

end GlobalTheory.CompanionTheory.CupTrans
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

theorem _root_.GlobalTheory.T.lie_operator_gl_relations : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ), Formalism.REAL.GlRel (EopV π τ) := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.glRel_EopV | exact GlobalTheory.CompanionTheory.Clozel.glRel_EopV | (intros; apply GlobalTheory.CompanionTheory.Clozel.glRel_EopV <;> assumption)
end

section


theorem _root_.GlobalTheory.T.sobolev_operator_facts : PositivityTheory.RgBcC.Fc.SobOps := by
  first | exact @GlobalTheory.CompanionTheory.SobOpsPf.sobOps | exact GlobalTheory.CompanionTheory.SobOpsPf.sobOps | (intros; apply GlobalTheory.CompanionTheory.SobOpsPf.sobOps <;> assumption)
end

section


theorem _root_.GlobalTheory.T.functional_calculus_joint_curve : PositivityTheory.RgBcC.Fc.CurveJoint := by
  first | exact @GlobalTheory.CompanionTheory.CurveJ.curveJoint | exact GlobalTheory.CompanionTheory.CurveJ.curveJoint | (intros; apply GlobalTheory.CompanionTheory.CurveJ.curveJoint <;> assumption)
end
