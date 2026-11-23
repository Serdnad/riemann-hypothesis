module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle469
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle451
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle438
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle083
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle163
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle320
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.ZariskiStratumQuotient

open GlobalTheory.CompanionTheory.DisoHm

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)

abbrev mkW (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (m : ℕ) : WittVector l k →+* Wc.Wm l k m :=
  Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})

theorem span_eq (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k) (T : (stF q ρ m 𝒱).FullSubcategory) :
    ((IdF.span (sV q ρ m 𝒱).A c).S T : Ideal T.obj.B) = (stdI (stF q ρ m 𝒱) none (mkW l k m c)).S T := by
  change _ = (⊥ : Ideal T.obj.B) ⊔ _
  rw [bot_sup_eq]
  rfl



def scQ (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k) :
    CH.Mor (sq (IdF.top (sV q ρ m 𝒱).A) (IdF.span (sV q ρ m 𝒱).A c))
      (sq (IdF.top (sP (stF q ρ m 𝒱)).A) (stdI (stF q ρ m 𝒱) none (mkW l k m c))) (mkW l k m) where
  G := 𝟭 _
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (span_eq q ρ m 𝒱 c T).le x.1, by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.factor (span_eq q ρ m 𝒱 c T).le x.1)
        rw [← hy]
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun a x => by
        obtain ⟨x, hx⟩ := x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  nat {T T'} φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Subtype.ext ?_
    rfl

theorem scQ_bij (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k) (j : ℕ) :
    Function.Bijective ((scQ q ρ m 𝒱 c).pull j) := by
  refine idM_bij (scQ q ρ m 𝒱 c).τ (scQ q ρ m 𝒱 c).nat (fun T => ⟨?_, ?_⟩) j
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have e : Ideal.Quotient.mk ((stdI (stF q ρ m 𝒱) none (mkW l k m c)).S T) (show T.obj.B from a) =
        Ideal.Quotient.mk _ (show T.obj.B from b) := congrArg Subtype.val h
    exact Subtype.ext (Ideal.Quotient.eq.2 ((span_eq q ρ m 𝒱 c T).ge (Ideal.Quotient.eq.1 e)))
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨Ideal.Quotient.mk _ a, Ideal.mem_map_of_mem _ trivial⟩, Subtype.ext rfl⟩

theorem st_le_top (m : ℕ) (𝒱 : Set X.Opens) : stF q ρ m 𝒱 ≤ stF q ρ m {⊤} :=
  fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩

theorem top_F (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤) (c : Wc.Wm l k m) (j : ℕ) :
    Function.Bijective ((resO (st_le_top q ρ m 𝒱) c).pull j) := by
  have hle := st_le_top q ρ m 𝒱
  have hz := (GlobalTheory.CompanionTheory.ZarCosieve.main (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 (stF q ρ m {⊤}) hle
    (fun T hT => ⟨hT.1, _, rfl, by rw [hU]; exact inU_top T⟩)
    (fun _ T' _ _ hT' => ⟨hT', ⊤, rfl, inU_top T'⟩) j).2.1 (some 0) none 0 c
  have t0 := sqLe_bij (b := stdI (stF q ρ m {⊤}) none c) (b' := stdI (stF q ρ m {⊤}) none c) (std0 (stF q ρ m {⊤})) (fun _ => rfl) j
  have t1 := sqLe_bij (b := stdI (stF q ρ m 𝒱) none c) (b' := stdI (stF q ρ m 𝒱) none c) (std0 (stF q ρ m 𝒱)) (fun _ => rfl) j
  refine (Function.Bijective.of_comp_iff' t1 _).1 ?_
  have e : ⇑((sqLe (a := IdF.top (sP (stF q ρ m 𝒱)).A) (b := stdI (stF q ρ m 𝒱) none c) (a' := stdI (stF q ρ m 𝒱) (some 0) 0) (b' := stdI (stF q ρ m 𝒱) none c) (fun T => (std0 (stF q ρ m 𝒱) T).le) (fun _ => le_rfl)).pull j) ∘
      ⇑((resO hle c).pull j) = ⇑(((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)).pull j) ∘
      ⇑((sqLe (a := IdF.top (sP (stF q ρ m {⊤})).A) (b := stdI (stF q ρ m {⊤}) none c) (a' := stdI (stF q ρ m {⊤}) (some 0) 0) (b' := stdI (stF q ρ m {⊤}) none c) (fun T => (std0 (stF q ρ m {⊤}) T).le) (fun _ => le_rfl)).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id (Wc.Wm l k m)) (resO hle c) (sqLe (a := IdF.top (sP (stF q ρ m 𝒱)).A) (b := stdI (stF q ρ m 𝒱) none c) (a' := stdI (stF q ρ m 𝒱) (some 0) 0) (b' := stdI (stF q ρ m 𝒱) none c) (fun T => (std0 (stF q ρ m 𝒱) T).le) (fun _ => le_rfl)) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id (Wc.Wm l k m)) (sqLe (a := IdF.top (sP (stF q ρ m {⊤})).A) (b := stdI (stF q ρ m {⊤}) none c) (a' := stdI (stF q ρ m {⊤}) (some 0) 0) (b' := stdI (stF q ρ m {⊤}) none c) (fun T => (std0 (stF q ρ m {⊤}) T).le) (fun _ => le_rfl)) ((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)) j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id (Wc.Wm l k m)) _ _ (𝟙 _) (fun T y => ?_) j x
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact hz.comp t0

abbrev backF (m : ℕ) : (fl l (B.schFn q) ρ m).FullSubcategory ⥤ (stF q ρ m {⊤}).FullSubcategory :=
  (stF q ρ m {⊤}).lift (fl l (B.schFn q) ρ m).ι fun T => ⟨T.property, ⊤, rfl, inU_top T.obj⟩

def adjF (m : ℕ) : ιS q ρ m {⊤} ⊣ backF q ρ m :=
  (CategoryTheory.Equivalence.mk (ιS q ρ m {⊤}) (backF q ρ m)
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))).toAdjunction

theorem top_res (m : ℕ) (c : WittVector l k) (j : ℕ) : Function.Bijective ((resVq q ρ m {⊤} c).pull j) :=
  CrystallineSemistableComparison.P.adj (sq (IdF.top (sW l (B.schFn q) ρ m).A) (IdF.span (sW l (B.schFn q) ρ m).A c)) (ιS q ρ m {⊤}) (backF q ρ m) (adjF q ρ m) j

end Main



theorem main : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resVq q ρ m 𝒱 c).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 c hU j
  have hle := st_le_top q ρ m 𝒱
  refine (Function.Bijective.of_comp_iff' (scQ_bij q ρ m 𝒱 c j) _).1 ?_
  have e : ⇑((scQ q ρ m 𝒱 c).pull j) ∘ ⇑((resVq q ρ m 𝒱 c).pull j) =
      ⇑((resO hle (mkW l k m c)).pull j) ∘ ⇑((scQ q ρ m {⊤} c).pull j) ∘ ⇑((resVq q ρ m {⊤} c).pull j) := by
    funext x
    have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := mkW l k m) (resVq q ρ m {⊤} c) (scQ q ρ m {⊤} c) j x).1
    have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := mkW l k m) (CH.Mor.comp (σ'' := mkW l k m) (resVq q ρ m {⊤} c) (scQ q ρ m {⊤} c))
      (resO hle (mkW l k m c)) j x).1
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := mkW l k m) (resVq q ρ m 𝒱 c) (scQ q ρ m 𝒱 c) j x).1).symm.trans
      (Eq.trans ?_ (h2.trans (congrArg _ h1)))
    refine CrystallineSemistableComparison.P.prism (σ := mkW l k m) (CH.Mor.comp (σ'' := mkW l k m) (resVq q ρ m 𝒱 c) (scQ q ρ m 𝒱 c))
      (CH.Mor.comp (σ'' := mkW l k m) (CH.Mor.comp (σ'' := mkW l k m) (resVq q ρ m {⊤} c) (scQ q ρ m {⊤} c))
        (resO hle (mkW l k m c))) (𝟙 _) (fun T y => ?_) j x
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact (top_F q ρ m 𝒱 hU _ j).comp ((scQ_bij q ρ m {⊤} c j).comp (top_res q ρ m c j))

end GlobalTheory.CompanionTheory.ZariskiStratumQuotient
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerAct

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}

def val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : T.1.A :=
  PAlg.Hom.f φ.1 (𝒯.c k 0).val

theorem val_comp (𝒯 : Tower κ s) {T T' : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (ψ : T ⟶ T') (k : Fin d) :
    val 𝒯 (φ ≫ ψ) k = PAlg.Hom.f ψ.1 (val 𝒯 φ k) := rfl

theorem sharp_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    T.1.sharp (val 𝒯 φ k) = mapU φ.1 (𝒯.g (s.T k)) := by
  rw [val, ← mapU_sharp]
  exact congrArg (mapU φ.1) (𝒯.c_sharp k)

def valU (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : (T.1.A)ˣ :=
  Units.map (PAlg.Hom.f φ.1).toMonoidHom (𝒯.c k 0)

theorem valU_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    ((valU 𝒯 φ k : (T.1.A)ˣ) : T.1.A) = val 𝒯 φ k := rfl

theorem hom_ext (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T)
    (h : ∀ k, val 𝒯 φ k = val 𝒯 ψ k) : φ = ψ := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, -, hχ⟩ := huniq (fun k => val 𝒯 φ k) hu
  exact (hχ φ (fun k => rfl)).trans (hχ ψ (fun k => (h k).symm)).symm

theorem sharp_mem (ε : Eps l) {T : (F.pt κ).Elements} (x : (epsU ε (F.pt κ)).U T) :
    T.1.sharp ((x.1 : (T.1.A)ˣ) : T.1.A) = 1 := by
  have hx : Units.map T.1.sharp x.1 = 1 := x.2
  exact congrArg Units.val hx

theorem exists_act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) :
    ∃ ψ : 𝒯.obj ⟶ T, ∀ k, val 𝒯 ψ k = ((a k).1 : T.1.A) * val 𝒯 φ k := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (((a k).1 : T.1.A) * val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [map_mul, sharp_mem ε (a k), one_mul, sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, hχ, -⟩ := huniq _ hu
  exact ⟨χ, fun k => hχ k⟩

def act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) : 𝒯.obj ⟶ T :=
  (exists_act 𝒯 ε a φ).choose

theorem act_val (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    val 𝒯 (act 𝒯 ε a φ) k = ((a k).1 : T.1.A) * val 𝒯 φ k :=
  (exists_act 𝒯 ε a φ).choose_spec k

theorem exists_quot (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T) :
    ∃ a : Fin d → (epsU ε (F.pt κ)).U T, ∀ k, ((a k).1 : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k := by
  obtain ⟨g, -, hg, -⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hs : ∀ (χ : 𝒯.obj ⟶ T) k, T.1.sharp (val 𝒯 χ k) = g (s.T k) := fun χ k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg χ) _
  refine ⟨fun k => ⟨valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹, ?_⟩, fun k => ?_⟩
  · show Units.map T.1.sharp (valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, valU_val, valU_val, hs ψ k, hs φ k]
  · show ((valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹ : (T.1.A)ˣ) : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k
    rw [← valU_val 𝒯 φ k, ← Units.val_mul, inv_mul_cancel_right, valU_val]

theorem act_unique (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a b : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (h : act 𝒯 ε a φ = act 𝒯 ε b φ) : a = b := by
  funext k
  have h1 := act_val 𝒯 ε a φ k
  rw [h, act_val, ← valU_val 𝒯 φ k] at h1
  apply Subtype.ext
  apply Units.ext
  exact ((valU 𝒯 φ k).isUnit.mul_left_inj).1 h1.symm

theorem tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val := by
  intro l _ O _ F κ d s 𝒯 ε
  refine ⟨{ act := fun a φ => act 𝒯 ε a φ
            act_one := fun c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val]
              exact one_mul _
            act_mul := fun a b c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val, act_val, act_val, ← mul_assoc]
              rfl
            act_comp := fun a c φ => hom_ext 𝒯 _ _ fun k => by
              rw [val_comp, act_val, act_val, val_comp, map_mul]
              rfl
            ne := fun t => by
              obtain ⟨g, -, -, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 ((jE (F.pt κ)).obj t)
              choose u hu using fun k => PAlg.IsTest.sharp_surjective t.1.property (g (s.T k))
              obtain ⟨χ, -, -⟩ := huniq u hu
              exact ⟨χ⟩
            trans := fun t c c' => by
              obtain ⟨a, ha⟩ := exists_quot 𝒯 ε c c'
              have hac : act 𝒯 ε a c = c' := hom_ext 𝒯 _ _ fun k => by rw [act_val, ha]
              exact ⟨a, hac, fun b hb => act_unique 𝒯 ε b a c (hb.trans hac.symm)⟩ }, ?_⟩
  intro T a φ k
  exact act_val 𝒯 ε a φ k

end GlobalTheory.CompanionTheory.TowerAct
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

theorem _root_.GlobalTheory.T.generic_finite_by_induction : (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a) → (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r) → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GenFin E a := by
  first | exact @GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | exact GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | (intros; apply GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters <;> assumption)
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspSubspace

theorem mem_of_mem_span_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
      (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
      (J : Set (Module.End ℂ (Sm E a))),
      ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1},
        φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  intro E _ _ _ a L W _ _ ρ J φ hφ
  induction hφ using Submodule.span_induction with
  | mem x h => exact h
  | zero =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).zero_mem, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    change ∫ _ in 𝓕, (0 : ℂ) ∂μ = 0
    simp
  | add x y _ _ hx hy =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).add_mem hx.1 hy.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have ix := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r x hx.1.1.left hx.1.1.level μ 𝓕 hμ hF).2 g
    have iy := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r y hy.1.1.left hy.1.1.level μ 𝓕 hμ hF).2 g
    have e : ∫ u in 𝓕, (x + y).1 (unip u * g) ∂μ =
        (∫ u in 𝓕, x.1 (unip u * g) ∂μ) + ∫ u in 𝓕, y.1 (unip u * g) ∂μ := integral_add ix iy
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, hy.2 r hr hr' μ 𝓕 hμ hF g, add_zero]
  | smul c x _ hx =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).smul_mem c hx.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∫ u in 𝓕, (c • x).1 (unip u * g) ∂μ = c • ∫ u in 𝓕, x.1 (unip u * g) ∂μ :=
      integral_smul c _
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, smul_zero]

end GlobalTheory.CompanionTheory.CuspSubspace

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem hasInfChar_conj_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ) (hB : IsHerm π B) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : π.HasInfChar τ m) (hm' : π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨φ, hφ⟩ := hB.2
  refine GlobalTheory.T.multiset_conjugate_neg_of_prod a m m' hm.1 hm'.1 fun u => ?_
  have val : ∀ (σ : E →+* ℂ) (l : Multiset ℂ), π.HasInfChar σ l → ∀ w : ℂ,
      Formalism.REAL.qdet (EopV π σ) (w + ((a : ℂ) - 1) / 2) φ = (l.map (w + ·)).prod • φ := by
    intro σ l hl w
    apply Subtype.ext
    rw [GlobalTheory.T.quantum_det_capelli_operator E a π σ w φ, hl.2 w φ.1 φ.2]
    rfl
  have key := GlobalTheory.T.quantum_det_adjoint_form π.V B a (EopV π τ) (EopV π (NumberField.ComplexEmbedding.conjugate τ))
    (GlobalTheory.T.lie_operator_gl_relations E a π _) (GlobalTheory.T.lie_operator_hermitian_skew E a π B hB τ) (u + ((a : ℂ) - 1) / 2) φ φ
  have arg : (a : ℂ) - 1 - (starRingEnd ℂ) (u + ((a : ℂ) - 1) / 2) =
      -(starRingEnd ℂ) u + ((a : ℂ) - 1) / 2 := by
    simp only [map_add (f := _), map_div₀, map_sub, map_one, Complex.conj_natCast, map_ofNat]
    ring
  rw [arg, val τ m hm u, LinearMap.smul_apply, val _ m' hm' (-(starRingEnd ℂ) u)] at key
  simp only [map_smul, LinearMap.smul_apply, smul_smul, map_smulₛₗ, smul_eq_mul] at key
  exact mul_right_cancel₀ hφ key

end GlobalTheory.CompanionTheory.Clozel
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZDeriv

theorem isSmooth_resM {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V)
    (hπ : IsSmooth π) : IsSmooth (resM k π).ρ := by
  intro v
  exact (hπ v).preimage continuous_subtype_val

theorem isGenericFor_of_isCuspidal_of
    (hNZ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V →
      ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)))
    (hRes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (m + 1)) k) V),
      twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n))
    (hVan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤)
    (hW0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V),
      twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N)) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  intro k _ _ _ _ ψ hψc hψ1 N V _ _ π hπ hV
  have hV' : Nontrivial (resM k π).V := hV
  obtain ⟨n, hn, hnt⟩ := hNZ k ψ hψc hψ1 N (resM k π).V (resM k π).ρ (isSmooth_resM π hπ.1) hV'
  rw [Submodule.Quotient.nontrivial_iff, hRes k ψ N n V π] at hnt
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [hW0 k ψ (N + 1) V π] at hnt
    exact Submodule.Quotient.nontrivial_iff.2 hnt
  · exact absurd (hVan k ψ (N + 1) n V π hπ hpos (Nat.lt_succ_of_le hn)) hnt

theorem isGenericFor_of_isCuspidal :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  isGenericFor_of_isCuspidal_of GlobalTheory.T.exists_nontrivial_derivative (fun k _ _ _ _ ψ m n V _ _ π =>
    GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) GlobalTheory.T.cuspidal_twisted_kernel_top
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)

end GlobalTheory.CompanionTheory.BZDeriv
end
end

section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

theorem _root_.GlobalTheory.T.hermitian_block_solution_exists : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C → ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧ C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_cells_decomposition : PositivityTheory.GramSchwartzFunctions.EC.Bruhat → PositivityTheory.GramSchwartzFunctions.EC.RatPts → PositivityTheory.GramSchwartzFunctions.EC.PInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 → PositivityTheory.GramSchwartzFunctions.EisCells := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | exact GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | (intros; apply GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_second_term_from_parts : PositivityTheory.GramSchwartzFunctions.EC.HeisSch → PositivityTheory.GramSchwartzFunctions.EC.Covar → PositivityTheory.GramSchwartzFunctions.EC.Zero → PositivityTheory.GramSchwartzFunctions.EC.Unfold2 → PositivityTheory.GramSchwartzFunctions.EC.ThetaInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 := by
  first | exact @GlobalTheory.CompanionTheory.EisCells.term_of_covariance | exact GlobalTheory.CompanionTheory.EisCells.term_of_covariance | (intros; apply GlobalTheory.CompanionTheory.EisCells.term_of_covariance <;> assumption)
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.integral_right_derivative_eq_zero : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew | exact GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew | (intros; apply GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew <;> assumption)
end
