module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle340
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle318
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle463
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle510
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle003
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle536
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle506
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle525
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle462
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle461
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

theorem mapH_bijective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{1} R} {M : Cx.{1} R'}
    (φ : Cx.Hom K M σ) (h : ∀ n, Function.Bijective (φ.f n)) (n : ℕ) : Function.Bijective (φ.mapH n) := by
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (φ.mapH n)).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ.f n z.1 ∈ M.B n := (Submodule.Quotient.mk_eq_zero ((M.B n).submoduleOf (M.Z n)) (x := φ.mapZ n z)).1 hx
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change z.1 ∈ K.B n
    cases n with
    | zero =>
      have h2 : φ.f 0 z.1 = 0 := h1
      have h3 : z.1 = 0 := (h 0).1 (h2.trans (map_zero _).symm)
      rw [h3]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := h1
      obtain ⟨y', rfl⟩ := (h n).2 y
      refine ⟨y', (h (n + 1)).1 ?_⟩
      rw [← φ.comm, hy]
  · intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, hx⟩ := (h n).2 w.1
    have h0 : K.d n x = 0 := (h (n + 1)).1 (by
      rw [← φ.comm, hx, map_zero]
      exact w.2)
    exact ⟨Submodule.Quotient.mk ⟨x, h0⟩, congrArg _ (Subtype.ext hx)⟩

section Gen

variable {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def toO (Q : ObjectProperty (Thick L)) : CH.Mor (Q.ι ⋙ B.OM L c) (CH.modF (sP Q).A) c where
  G := 𝟭 _
  τ T := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toO_bij (Q : ObjectProperty (Thick L)) (n : ℕ) : Function.Bijective ((toO c Q).pull n) :=
  mapH_bijective _ (fun _ => Function.bijective_id) n

def sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) : CH.Mor (P.ι ⋙ B.OM L c) (Q.ι ⋙ B.OM L c) (RingHom.id Λ) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem sub_square {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (toO c Q).pull j ((sub c h).pull j x) = (incl h).o.pull j ((toO c P).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem sub_bij {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (hb : Function.Bijective ((incl h).o.pull j)) :
    Function.Bijective ((sub c h).pull j) := by
  have e : (toO c Q).pull j ∘ (sub c h).pull j = (incl h).o.pull j ∘ (toO c P).pull j :=
    funext (sub_square c h j)
  refine (Function.Bijective.of_comp_iff' (toO_bij c Q j) _).1 ?_
  rw [e]
  exact hb.comp (toO_bij c P j)

theorem sub_sub {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h' : S ≤ Q) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (sub c h').pull j ((sub c h).pull j x) = (sub c (h'.trans h)).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (B.OM L c) j) :
    (sub c h).pull j ((CH.Mor.restrict (B.OM L c) P.ι).pull j x) = (CH.Mor.restrict (B.OM L c) Q.ι).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_all (P : ObjectProperty (Thick L)) (hP : ∀ T, P T) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) P.ι).pull j) := by
  refine mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) j
  · funext t
    exact congrFun e (P.lift t fun i => hP _)
  · exact ⟨fun t => g (P.lift t fun i => hP _), rfl⟩

theorem bij_three {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h1 : S ≤ Q) (h2 : S ≤ P) (j : ℕ)
    (b1 : Function.Bijective ((incl h1).o.pull j)) (b2 : Function.Bijective ((incl h2).o.pull j)) (hP : ∀ T, P T) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) Q.ι).pull j) := by
  have s1 := sub_bij c h1 j b1
  have s2 := sub_bij c h2 j b2
  have s3 : Function.Bijective ((sub c h).pull j) := by
    have e : (sub c h1).pull j ∘ (sub c h).pull j = (sub c h2).pull j := funext (sub_sub c h h1 j)
    refine (Function.Bijective.of_comp_iff' s1 _).1 ?_
    rw [e]
    exact s2
  have e : (sub c h).pull j ∘ (CH.Mor.restrict (B.OM L c) P.ι).pull j =
      (CH.Mor.restrict (B.OM L c) Q.ι).pull j := funext (res_sub c h j)
  rw [← e]
  exact s3.comp (res_all c _ hP j)

end Gen

end GlobalTheory.CompanionTheory.CrystallineChernClass

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

theorem exu_core (D : E.LineData X) (Q : ObjectProperty (Thick ((B.schFn q).cr b ht κ)))
    (hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T)
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (N : ℕ)
    (hbij : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2))
    (hN : ∀ (T : Thick ((B.schFn q).cr b ht κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0) :
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N x := by
  obtain ⟨Λ₀⟩ := GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift Q.ι D (fun T => (hQ _).1 T.property)
  have hz₀ := (GlobalTheory.T.crystalline_cocycle_closed Q.ι D c N (fun T k hk x _ => by
    change ((k.factorial : ℕ) : (T.obj).B) * _ = 0
    rw [hN _ k hk, zero_mul])).1 Λ₀
  obtain ⟨x, hx⟩ := hbij.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G Λ₁
    have hG : ∀ T, Q (G.obj T) := fun T => (hQ _).2 ⟨Λ₁.p T, Λ₁.hp T⟩
    have hcl := GlobalTheory.T.crystalline_cocycle_closed G D c N (fun T k hk x _ => by rw [hN _ k hk, zero_mul])
    let Λ' : B.CLift G D := precomp Λ₀ (Q.lift G hG)
    refine ⟨hcl.1 Λ₁, ?_⟩
    rw [hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')]
    have e1 : (CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) G).pull 2 x =
        (CH.Mor.restrict (Q.ι ⋙ B.OM ((B.schFn q).cr b ht κ) c) (Q.lift G hG)).pull 2
          ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hbij.1
    obtain ⟨h1, h2⟩ := hy _ Q.ι Λ₀
    rw [hx, ← h2]

end Core

section Main

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def Lifts (D : E.LineData X) : ObjectProperty (Thick (nlFun γ p X q κ)) :=
  fun T => ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T

theorem st_le_lifts (D : E.LineData X) : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ Lifts D := by
  rintro T ⟨-, V, ⟨σ, hσ⟩, hV⟩
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem lifts_map (D : E.LineData X) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : Lifts D T) : Lifts D T' := by
  obtain ⟨a, ha⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ a, ?_⟩
  rw [Category.assoc, ha]
  exact congrArg (fun y => y.1.2) φ.pt

theorem res_bij (hp : p ≠ 0) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ] (c : Λ →+* R) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM (nlFun γ p X q κ) c) (Lifts D).ι).pull j) := by
  have hU : Used (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) := Or.inr ⟨hp, Or.inl rfl⟩
  have h1 : St ⊤ (𝒱D D) ≤ Lifts (γ := γ) (p := p) (q := q) (κ := κ) D := st_le_lifts D
  have h1' : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {sSup (𝒱D D)} := fun T _ =>
  ⟨trivial, _, rfl, by rw [hD]; exact inU_top T⟩
  have b1 := (GlobalTheory.T.cohomology_restriction_between_stable_families ⊤ hU (𝒱D D) (Lifts D) h1 h1' (fun T T' φ h _ => lifts_map D φ h) j).2.2
  have h2 : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have b2 := (GlobalTheory.T.cech_refinement_cohomology_bijective ⊤ hU (𝒱D D) {⊤} h2 (by rintro W rfl; rw [hD]) j).2.2
  have h3 : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have hall : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⊤} T := fun T => ⟨trivial, ⊤, rfl, inU_top T⟩
  exact bij_three (b := nlBase R I γ p) (L := nlFun γ p X q κ) c h3 h1 h2 j b1 b2 hall

end Main

theorem existsUnique_crystalline_chern_class : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  intro O R _ _ I γ p hp X q κ D hD Λ _ c N hN
  have hf : ∀ (T : Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0 := fun T k hk => by
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hk
    have h0 : (k.factorial : R) = 0 := by rw [hm, Nat.cast_mul, hN, zero_mul]
    have := congrArg T.i h0
    rwa [map_natCast, map_zero] at this
  have hb := res_bij (γ := γ) (q := q) (κ := κ) hp D hD c 2
  let Q : ObjectProperty (Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) := Lifts (γ := γ) (p := p) (q := q) (κ := κ) D
  have hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T := fun T => Iff.rfl
  have hb' : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr (nlBase R I γ p) rfl κ) c) Q.ι).pull 2) := hb
  exact exu_core (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D Q hQ c N hb' hf

end GlobalTheory.CompanionTheory.CrystallineChernClass
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_bruhat_decomposition : PositivityTheory.GramSchwartzFunctions.EC.Bruhat := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.bruhat | exact GlobalTheory.CompanionTheory.BruhatCell.bruhat | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.bruhat <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covar_of (hB : Bruhat) (hR : RatPts) : Covar := by
  intro D n V ψ χ θ μ ω hS γ hγ v Φ Ψ hΨ
  obtain ⟨-, -, -, -, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat hB D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer hR D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem covar : Covar :=
  covar_of GlobalTheory.CompanionTheory.BruhatCell.bruhat GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn

end GlobalTheory.CompanionTheory.EisCovar
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace GlobalTheory.CompanionTheory.CxAvg

section Abstract

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  (μ : Measure K) [μ.IsHaarMeasure] (F : K →* (E →L[ℂ] E))

variable {F}

end Abstract

section Concrete

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC

variable {n : ℕ}

theorem Rm_unitary (lam : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam k.1 = LinearMap.toMatrix (wb lam) (wb lam)
      (GlobalTheory.Branching.sqRep ℂ n (dw lam) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dite_eq_left h, e]

theorem Rm_mul (lam : Fin n → ℤ) (k k' : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam (k * k').1 = Rm lam k.1 * Rm lam k'.1 := by
  rw [Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Matrix.unitaryGroup (Fin n) ℂ).1 = 1 := by
  rw [Rm_unitary, map_one, map_one]
  exact LinearMap.toMatrix_id _

theorem continuous_unitaryIncl : Continuous (GlobalTheory.Branching.unitaryIncl n) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem continuous_Rm (lam : Fin n → ℤ) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rm lam k.1 := by
  simp only [Rm_unitary]
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp
    continuous_unitaryIncl

end Concrete

end GlobalTheory.CompanionTheory.CxAvg
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

section Abstract

variable {A B : Type}

def prodSpan (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)) : Submodule ℂ (A × B → ℂ) :=
  Submodule.span ℂ {F | ∃ a ∈ U₁, ∃ b ∈ U₂, F = fun x => a x.1 * b x.2}

end Abstract

section Lin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s : ℕ}


variable (E) in
abbrev KO (n : ℕ) : Subgroup (GL (Fin n) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n

def typeF (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) : Submodule ℂ (GA E N → ℂ) where
  carrier := {f | (∀ u ∈ K, ∀ g, f (g * finGL E N u) = f g) ∧
    ∀ g, (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ W}
  add_mem' := fun {f f'} h h' => ⟨fun u hu g => by simp only [Pi.add_apply, h.1 u hu g, h'.1 u hu g],
    fun g => W.add_mem (h.2 g) (h'.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  smul_mem' := fun c f h => ⟨fun u hu g => by simp only [Pi.smul_apply, h.1 u hu g],
    fun g => W.smul_mem c (h.2 g)⟩

def typed (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) :
    Submodule ℂ (Sm E N) :=
  U ⊓ (typeF K W).comap (Sm E N).subtype

structure FlatFn (e : GA E N → ℂ) : Prop where
  ne : ∀ x, e x ≠ 0
  rinv : ∀ x (k : Kinf E N), ∀ c ∈ KO E N, e (x * cf N k c) = e x
  sm : e ∈ Sm E N

def Carries (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∃ φ' ∈ U', ∀ x, φ'.1 x = e x * φ.1 x

def FinStable (U : Submodule ℂ (Sm E N)) : Prop := ∀ (g : GL (Fin N) (Af E)), ∀ φ ∈ U, act (.fin g) φ ∈ U

def indSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) :=
  Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ}

theorem exists_iw (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) ∧ x = unip u * lev (Ad E) r s m * cf (r + s) k c := by
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) x)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) x)
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add (f := _), show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add (f := _), show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), k, c, hc, ga_ext ?_ ?_⟩
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf]

def leviOf (x : GA E (r + s)) : GA E r × GA E s := (exists_iw x).choose_spec.choose

def nodeFn (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (x : GA E (r + s)) : ℂ := e₁ (leviOf x).1 * e₂ (leviOf x).2

def absFn (N : ℕ) (w : ℂ) (x : GA E N) : ℂ := (chiDet N (GlobalTheory.CuspRep.Model.absC E w) x : ℂˣ)

end Lin

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def typeHF (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) : Submodule ℂ (H E a b → ℂ) where
  carrier := {F | TypeH K₁ K₂ W₁ W₂ F}
  add_mem' := fun {F F'} h h' => ⟨fun u₁ hu₁ u₂ hu₂ x => by
      simp only [Pi.add_apply, h.1 u₁ hu₁ u₂ hu₂ x, h'.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.add_mem _ (h.2 x) (h'.2 x)⟩
  zero_mem' := ⟨fun _ _ _ _ _ => rfl, fun _ => Submodule.zero_mem _⟩
  smul_mem' := fun c F h => ⟨fun u₁ hu₁ u₂ hu₂ x => by simp only [Pi.smul_apply, h.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.smul_mem _ c (h.2 x)⟩

end Pair

end GlobalTheory.CompanionTheory.LimV

end
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.conjugate_places_facts : ConjPlaces := by
  first | exact @GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | exact GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | (intros; apply GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces <;> assumption)
end
