module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle246
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecay
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtReduction

section Abstract
universe w u v
variable {R R₁ R₂ R₃ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃] {C : Type u} [Category.{v} C]

theorem pull_sq {F : C ⥤ ModuleCat.{w} R} {F₁ : C ⥤ ModuleCat.{w} R₁} {F₂ : C ⥤ ModuleCat.{w} R₂} {F₃ : C ⥤ ModuleCat.{w} R₃}
    {σ₁ : R →+* R₁} {σ₂ : R₁ →+* R₃} {σ₃ : R →+* R₂} {σ₄ : R₂ →+* R₃}
    (a : Mor F F₁ σ₁) (b : Mor F₁ F₃ σ₂) (c : Mor F F₂ σ₃) (e : Mor F₂ F₃ σ₄) (n : ℕ)
    (h : ∀ z, b.pullC n (a.pullC n z) = e.pullC n (c.pullC n z)) (x : CH.H F n) :
    b.pull n (a.pull n x) = e.pull n (c.pull n x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

end Abstract

variable {l : ℕ} [Fact l.Prime]

def lcCast {U : Type*} [TopologicalSpace U] {Q q : ℕ} (h : q ∣ Q) :
    LocallyConstant U (ZMod Q) →+ LocallyConstant U (ZMod q) where
  toFun f := f.map (ZMod.castHom h (ZMod q))
  map_zero' := by ext v; simp
  map_add' f g := by
    ext v
    exact map_add (ZMod.castHom h (ZMod q)) (f v) (g v)

theorem pow_div_pow_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ', Nat.mul_div_cancel _ h]

theorem rho_pow (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem lcRes_id {U : Scheme.{0}} (q : ℕ) (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  simp [lcRes]

theorem zeta_red (r : Roots l) (A : PAlg l) (n : ℕ) :
    (r.zeta A n).1 = (primRes (𝟙 (SU A)) (r.zeta A (n + 1))).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_pow_succ]
  change ((toΓ A.Ug).comp (kb A)) (r.ρ n).1 = (𝟙 (SU A) : SU A ⟶ SU A).appTop.hom (((toΓ A.Ug).comp (kb A)) (r.ρ (n + 1)).1) ^ l
  rw [rho_pow r n, map_pow]
  simp

theorem lc_red (hN : LcNat) (H : RIn l) (A : Test l) (n : ℕ) (f : LocallyConstant (SU A.obj) (ZMod (l ^ (n + 1)))) :
    A.obj.red n.le_succ (lcA A.obj (n + 1) f) = lcA A.obj n (lcCast (pow_dvd_pow l n.le_succ) f) :=
  (hN l H _ A.property n).2 f

variable {C : Type 1} [Category.{0} C]

def redMor (H : RIn l) (r : Roots l) (G : C ⥤ Test l) (n : ℕ) :
    Mor (probe H r G (n + 1)).L (probe H r G n).L (RingHom.id ℤ) where
  G := 𝟭 C
  τ c :=
    { toFun := lcCast (pow_dvd_pow l n.le_succ)
      map_add' := map_add _
      map_smul' := fun z x => (map_zsmul (lcCast (U := (probe H r G n).U c) (pow_dvd_pow l n.le_succ)) z x).trans rfl }
  nat φ x := rfl

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

variable {l : ℕ} [Fact l.Prime]

theorem red_lc_sq (hN : LcNat) (H : RIn l) (r : Roots l) (P : PAlg l ⥤ Type) (n j : ℕ)
    (c : CH.H (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L j) :
    (MSys P j).r n ((lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).pull j c) =
      (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j
        ((redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j c) :=
  pull_sq (F := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L)
    (F₁ := CH.modF (AcrEl P (n + 1))) (F₂ := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).L)
    (F₃ := CH.modF (AcrEl P n))
    (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)) (Mor.ofNatTrans (redEl P n.le_succ))
    (redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) j
    (fun z => funext fun s => lc_red hN H (s.obj (Fin.last j)).1 n (z s)) c

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

theorem fred_of_etRed : EtRed → FRed := by
  intro hE E hN l _ H r K M n j x
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := hE E.gen E.red E.op (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) (El M.P) (El M.P)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) (n + 1)) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M (𝟭 _) (n + 1)) (pts H r M (𝟭 _) n) (redMor H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => 𝟙 _) (fun φ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun c f => (lcRes_id _ _).symm)
    (fun c => (Category.id_comp _).symm)
    (fun c => zeta_red r _ n) 0 j x
  exact (red_lc_sq hN H r M.P n j _).trans (congrArg _ key)

end GlobalTheory.CompanionTheory.EtReduction
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FNatProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem geomPt_geomMap {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      geomPt N A ((pxMap (okToOC l K) u hu).app A y) := by
  refine gb_ext N ?_ ?_
  · have e1 : GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) ≫
        pullback.fst _ _ ≫ pullback.fst _ _ = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ u := by
      rw [GlobalTheory.Et.geomMap, pullback.lift_fst_assoc, Category.assoc, Model.genMap, pullback.lift_fst, Category.assoc]
    rw [Category.assoc, e1, geomPt_fst, ← Category.assoc, geomPt_fst, Category.assoc]
    rfl
  · rw [Category.assoc, GlobalTheory.Et.geomMap, pullback.lift_snd, geomPt_snd, geomPt_snd]

def lcPull (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) :
    Mor (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := elMap (pxMap (okToOC l K) u hu)
  τ _ := LinearMap.id
  nat _ _ := rfl

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem cls_surj {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (h : CH.H F n) :
    ∃ (z : Cn F n) (hz : d F n z = 0), (cx F).cls z hz = h := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  exact ⟨z, hz, rfl⟩

theorem pull_square {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
    {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄}
    {σ₁₂ : R₁ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₁₃ : R₁ →+* R₃} {σ₃₄ : R₃ →+* R₄}
    (a : Mor F₁ F₂ σ₁₂) (b : Mor F₂ F₄ σ₂₄) (c : Mor F₁ F₃ σ₁₃) (e : Mor F₃ F₄ σ₃₄) (j : ℕ)
    (h : ∀ z : Cn F₁ j, b.pullC j (a.pullC j z) = e.pullC j (c.pullC j z)) (x : CH.H F₁ j) :
    b.pull j (a.pull j x) = e.pull j (c.pull j x) := by
  obtain ⟨z, hz, rfl⟩ := cls_surj F₁ j x
  change (cx F₄).cls (b.pullC j (a.pullC j z)) _ = (cx F₄).cls (e.pullC j (c.pullC j z)) _
  simp only [h]

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ)
    (h : CH.H (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L j) :
    (lcM hN H r M n).pull j ((lcPull H r u hu n).pull j h) =
      Model.pullMH u hu n j ((lcM hN H r N n).pull j h) :=
  pull_square (lcPull H r u hu n) (lcM hN H r M n) (lcM hN H r N n) (pullMor (pxMap (okToOC l K) u hu) n) j
    (fun z => funext fun s => rfl) h

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  rfl

def gId (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).U c ⟶
      (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c) :=
  𝟙 (Spec (CommRingCat.of c.1.obj.Ug))

theorem gId_nat (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ)
    {c c' : El M.P} (φ : c ⟶ c') :
    gId H r u hu n c' ≫ ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).S.map ((lcPull H r u hu n).G.map φ)).unop =
      ((probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S.map φ).unop ≫ gId H r u hu n c :=
  (Category.id_comp _).trans (Category.comp_id _).symm

theorem gId_lc (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P)
    (f : LocallyConstant ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c)) (ZMod (l ^ n))) :
    (lcPull H r u hu n).τ c f = lcRes (l ^ n) (gId H r u hu n c) f :=
  (lcRes_id _ f).symm

theorem gId_pts (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (pts H r M (𝟭 _) n).y c ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      gId H r u hu n c ≫ (pts H r N (𝟭 _) n).y ((lcPull H r u hu n).G.obj c) :=
  (geomPt_geomMap u hu c.1.obj c.2).trans (Category.id_comp _).symm

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    (lcPull H r u hu n).pull j ((pts H r N (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) :=
  hE hG (l ^ n) (El N.P) (El M.P) (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb N) (gb M) (pts H r N (𝟭 _) n) (pts H r M (𝟭 _) n)
    (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu)) (lcPull H r u hu n)
    (gId H r u hu n) (gId_nat H r u hu n) (gId_lc H r u hu n) (gId_pts H r u hu n) 0 (Or.inl rfl) j x

theorem nat_step (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    eM hN H r M n 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) =
      Model.pullMH u hu n j (eM hN H r N n 0 j x) :=
  (congrArg ((lcM hN H r M n).pull j) (key hE hG H r u hu n j x).symm).trans (square hN H r u hu n j _)

theorem fNat : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FNat := by
  intro hE E hN l _ H r K M N u hu n j x
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact nat_step hE E.gen hN H r u hu n j x

end GlobalTheory.CompanionTheory.FNatProof

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FUntwPf

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def vn (E : Spc) (k : ℕ) (a : Ht (l ^ k) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ k) E ((0 : ℕ) : ℤ) (-1)) : Ht (l ^ k) E ((2 : ℕ) : ℤ) 0 :=
  (cup (l ^ k) a b).cast rfl rfl

theorem vn_red (h : A11) (E : Spc) (k : ℕ) (a : Ht (l ^ (k + 1)) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ (k + 1)) E ((0 : ℕ) : ℤ) (-1)) :
    red (l ^ (k + 1)) (l ^ k) E ((2 : ℕ) : ℤ) 0 (vn E (k + 1) a b) =
      vn E k (red (l ^ (k + 1)) (l ^ k) E _ _ a) (red (l ^ (k + 1)) (l ^ k) E _ _ b) := by
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact (h (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l k.le_succ) E).1 a b

theorem step (hF : FCup) (hO : CupOne) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ)
    (a : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1))
    (hb : eM hN H r M n (-1) 0 b = oneH (AcrEl M.P n)) :
    eM hN H r M n 0 2 (vn (sch.obj (gb M)) n a b) = eM hN H r M n 1 2 a := by
  have h := hF E hN l H r K M n 1 (-1) 0 rfl 2 0 2 rfl a b
  have h2 := congrArg ((mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a)) hb
  have h' : (mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a) (oneH (AcrEl M.P n)) = eM hN H r M n 1 2 a :=
    hO _ _ _ _ _
  exact h.trans (h2.trans h')

theorem core (E : EtIn) (hF : FCup) (hO : CupOne) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (x : Hl l (sch.obj (gb M)) (2 : ℕ) 1) (w : Hl l (sch.obj (gb M)) (0 : ℕ) (-1))
    (hw : ∀ n, eM hN H r M n (-1) 0 (w.1 n) = oneH (AcrEl M.P n)) :
    ∃ v : Hl l (sch.obj (gb M)) (2 : ℕ) 0, ∀ n, eM hN H r M n 0 2 (v.1 n) = eM hN H r M n 1 2 (x.1 n) := by
  have hv : ∀ k, red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0
      (vn (sch.obj (gb M)) (k + 1) (x.1 (k + 1)) (w.1 (k + 1))) = vn (sch.obj (gb M)) k (x.1 k) (w.1 k) := by
    intro k
    have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1 (x.1 (k + 1)) = x.1 k := x.2 k
    have h2 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1) (w.1 (k + 1)) = w.1 k := w.2 k
    exact (vn_red E.a11 _ k _ _).trans (congrArg₂ (vn (sch.obj (gb M)) k) h1 h2)
  exact ⟨⟨fun k => vn (sch.obj (gb M)) k (x.1 k) (w.1 k), hv⟩, fun n => step hF hO E hN H r M n (x.1 n) (w.1 n) (hw n)⟩

theorem main : CrystallineSemistableComparison.E.FCup → CrystallineSemistableComparison.E.FRoot → CrystallineSemistableComparison.E.CupOne → CrystallineSemistableComparison.E.FUntw :=
  fun hF hR hO E hN l _ H r K M x => (hR E hN l H r K M (-1)).elim fun w hw => core E hF hO hN H r M x w hw

end GlobalTheory.CompanionTheory.FUntwPf
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FEquiProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pull_pull_of_pullC {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {C₀ C₁ C₂ C₃ : Type 1} [Category.{0} C₀] [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃]
    {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃}
    {a : R₀ →+* R₁} {b : R₁ →+* R₃} {c : R₀ →+* R₂} {e : R₂ →+* R₃}
    (m₁ : Mor F₀ F₁ a) (m₂ : Mor F₁ F₃ b) (m₃ : Mor F₀ F₂ c) (m₄ : Mor F₂ F₃ e) (j : ℕ)
    (h : ∀ z : Cn F₀ j, m₂.pullC j (m₁.pullC j z) = m₄.pullC j (m₃.pullC j z)) (x : H F₀ j) :
    m₂.pull j (m₁.pull j x) = m₄.pull j (m₃.pull j x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((cx F₃).B j).submoduleOf ((cx F₃).Z j))) (Subtype.ext (h z))

theorem twUg_sharp (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (e : (PAlg.tw σ A).A) :
    twUg σ A (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug ((PAlg.tw σ A).sharp e)) =
      algebraMap A.U A.Ug (A.sharp (PAlg.twId σ A e)) := by
  rw [twUg_algebraMap]
  refine congrArg (algebraMap A.U A.Ug) ?_
  change PAlg.twU σ A ((PAlg.tw σ A).th (WittVector.teichmuller l e)) = A.th (WittVector.teichmuller l (PAlg.twId σ A e))
  rw [PAlg.twU_th, WittVector.map_teichmuller]

theorem twAcr_lcA (hN : LcNat) (H : RIn l) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU (PAlg.tw σ A)) (ZMod (l ^ n))) :
    PAlg.twAcr σ A n (lcA (PAlg.tw σ A) n f) =
      lcA A n (lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (twUg σ A))) f) :=
  (hN l H _ (hA.tw σ) n).1 A hA (PAlg.twId σ A) (PAlg.pdOk_twId σ A) (twUg σ A) (fun e _ => twUg_sharp σ A e) f

theorem lcRes_sq {q : ℕ} {A B C D : Scheme.{0}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (e : a ≫ b = c ≫ d)
    (x : LocallyConstant D (ZMod q)) : lcRes q a (lcRes q b x) = lcRes q c (lcRes q d x) := by
  ext v
  have e' : b (a v) = d (c v) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact congrArg x e'

abbrev pM (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) : Probe (El M.P) (l ^ n) :=
  probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev tM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) : El M.P ⥤ El M.P :=
  elTw σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ))

def gM (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) (c : El M.P) :
    (pM H r M n).U c ⟶ (pM H r M n).U ((tM M σ).obj c) :=
  Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))

theorem gM_sq (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) {c c' : El M.P}
    (φ : c ⟶ c') : gM H r M σ n c' ≫ ((pM H r M n).S.map ((tM M σ).map φ)).unop =
      ((pM H r M n).S.map φ).unop ≫ gM H r M σ n c := by
  change Spec.map (CommRingCat.ofHom (twUg σ c'.1.obj)) ≫
      Spec.map (CommRingCat.ofHom (PAlg.mapUg (PAlg.twMap σ φ.1.hom))) =
    Spec.map (CommRingCat.ofHom (PAlg.mapUg φ.1.hom)) ≫ Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) ((hT l K σ).1 _ _ φ.1.hom)

def twMor (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    Mor (pM H r M n).L (pM H r M n).L (RingHom.id ℤ) where
  G := tM M σ
  τ c := (lcRes (l ^ n) (gM H r M σ n c)).toAddMonoidHom.toIntLinearMap
  nat {c c'} φ x := by
    have e := gM_sq hT H r M σ n φ
    change lcRes (l ^ n) (gM H r M σ n c') (lcRes (l ^ n) ((pM H r M n).S.map ((tM M σ).map φ)).unop x) =
      lcRes (l ^ n) ((pM H r M n).S.map φ).unop (lcRes (l ^ n) (gM H r M σ n c) x)
    exact lcRes_sq e x

def lM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (pM H r M n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev gaM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Mor (modF (AcrEl M.P n)) (modF (AcrEl M.P n)) (ACris.galCris σ) :=
  galMor σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ)) n

theorem lM_pullC_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (z : Cn (pM H r M n).L j) :
    (lM hN H r M n).pullC j ((twMor hT H r M σ n).pullC j z) = (gaM M σ n).pullC j ((lM hN H r M n).pullC j z) := by
  funext s
  have hA := (s.obj (Fin.last j)).1.property
  let f : LocallyConstant (SU (PAlg.tw σ (s.obj (Fin.last j)).1.obj)) (ZMod (l ^ n)) := z (s ⋙ tM M σ)
  exact (twAcr_lcA hN H σ (s.obj (Fin.last j)).1.obj hA n f).symm

theorem lM_pull_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : CH.H (pM H r M n).L j) :
    (lM hN H r M n).pull j ((twMor hT H r M σ n).pull j x) = (gaM M σ n).pull j ((lM hN H r M n).pull j x) :=
  pull_pull_of_pullC (twMor hT H r M σ n) (lM hN H r M n) (lM hN H r M n) (gaM M σ n) j
    (lM_pullC_twMor hT hN H r M σ n j) x

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    (twMor hT H r M σ n).pull j ((pts H r M (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) :=
  hE E.gen (l ^ n) (El M.P) (El M.P) (pM H r M n) (pM H r M n) (gb M) (gb M)
    (pts H r M (𝟭 _) n) (pts H r M (𝟭 _) n) (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ) (twMor hT H r M σ n)
    (gM H r M σ n) (fun φ => gM_sq hT H r M σ n φ) (fun c f => rfl)
    (fun c => (hT l K σ).2.2 M c.1.obj c.2) 0 (Or.inl rfl) j x

theorem eM_apply (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j x = (lM hN H r M n).pull j ((pts H r M (𝟭 _) n).et 0 j x) := rfl

theorem galMH_apply (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (y : M.MH n j) :
    M.galMH σ n j y = (gaM M σ n).pull j y := rfl

theorem equi_at (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) = M.galMH σ n j (eM hN H r M n 0 j x) :=
  (eM_apply hN H r M n j _).trans ((congrArg ((lM hN H r M n).pull j) (key hE hT E H r M σ n j x).symm).trans
    ((lM_pull_twMor hT hN H r M σ n j _).trans ((congrArg ((gaM M σ n).pull j) (eM_apply hN H r M n j x).symm).trans
      (galMH_apply M σ n j _).symm)))

theorem fEqui : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.TwUg → CrystallineSemistableComparison.E.FEqui :=
  fun hE hT E hN l _ H r K M n j σ x => equi_at hE hT E hN H r M σ n j x

end GlobalTheory.CompanionTheory.FEquiProof
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_lattice_base : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  first | exact @GlobalTheory.CompanionTheory.LatCBase.latBase_lev | exact GlobalTheory.CompanionTheory.LatCBase.latBase_lev | (intros; apply GlobalTheory.CompanionTheory.LatCBase.latBase_lev <;> assumption)
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

theorem relNull_cast {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of K))
    {Q : ObjectProperty (Thick (smFun Y q))} {a n c c' N N' : ℕ} (hc : 1 + a = c) (hc' : 1 + a = c') (hN : 2 + n = N)
    (hN' : 2 + n = N') (r : CH.Cn (G q 1) 2) (z : CH.Cn (G q a) n)
    (h : RelNull (G q c) Q N (cupC q (a := 1) (a' := a) hc hN r z)) :
    RelNull (G q c') Q N' (cupC q (a := 1) (a' := a) hc' hN' r z) := by
  subst hc hc' hN hN'
  exact h

theorem relKillOf : TopRes → FormUniq → OmRes → RelKillOf := by
  intro hTop hFU hOR hSL hCD hZR hAO hON hAR hFL hDW hDL hFC hC1 hDC hCK K _ _ W Z Y q _ _ i π _ D d hd hB r hr hc1 a n z hz hzr
  obtain ⟨B⟩ := hB
  haveI := B.closed
  obtain ⟨m, U, σ, hσ, hU, haff, hcov⟩ := hDC K W Z Y q i π D d B
  obtain ⟨-, hQ, -⟩ := hSL K (pullback i π) Y Y (π ≫ q) (pullback.snd i π) (𝟙 Y)
  exact relNull_cast (π ≫ q) _ _ _ _ r z
    (kill_over hTop hFU hOR hSL hCD hZR hAO hAR hFL hDW hDL hFC hC1 hCK D hQ B.f B.f_nat B.f_u U σ hσ hU haff hcov
      r hr hc1 a n z hz hzr)

end GlobalTheory.CompanionTheory.RelKill
end
end

section


theorem _root_.GlobalTheory.T.kernel_weight_facts : PositivityTheory.RgBcC.Fc.KerW := by
  first | exact @GlobalTheory.CompanionTheory.KerWord.kerW | exact GlobalTheory.CompanionTheory.KerWord.kerW | (intros; apply GlobalTheory.CompanionTheory.KerWord.kerW <;> assumption)
end

section


theorem _root_.GlobalTheory.T.paley_wiener_decay : PositivityTheory.RgBcC.Fc.PWdecay := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay | exact GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay <;> assumption)
end
