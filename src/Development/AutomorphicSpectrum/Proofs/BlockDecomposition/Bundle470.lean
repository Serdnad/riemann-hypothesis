module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DescOfDes
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle439
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle440
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle441
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedNat

universe w w' v u v' u'

section Retype
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ σ₂ : R →+* R'}

def retype (m : CH.Mor F F' σ) (σ₂ : R →+* R') (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) : CH.Mor F F' σ₂ where
  G := m.G
  τ T :=
    { toFun := m.τ T
      map_add' := map_add _
      map_smul' := fun a x => (LinearMap.map_smulₛₗ (m.τ T) a x).trans (h T a _) }
  nat := m.nat

theorem pull_retype (m : CH.Mor F F' σ) (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) (n : ℕ) (x : CH.H F n) :
    (retype m σ₂ h).pull n x = m.pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
  have hb : CH.d F' n (m.pullC n a) = 0 := by rw [CH.Mor.d_pullC]; exact (congrArg _ ha).trans (map_zero _)
  exact (CrystallineSemistableComparison.P.mapH_cls (retype m σ₂ h).hom n a ha hb).trans (CrystallineSemistableComparison.P.mapH_cls m.hom n a ha hb).symm

end Retype

section Eta
variable {O A₁ A₂ R₁ R₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n s : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ')

theorem eta_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (r : R₁) :
    iBar ((nm.mor 0).obj T) l n (d₁.ρ r) = iBar T l n (d₂.ρ (σ' r)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [hρ, ← ha]
  rfl

def etaR (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (h₁ : TF l s ((nm.mor 0).obj T)) (h₂ : TF l s T) :
    redObj ((nm.mor 0).obj T) d₁ h₁ ⟶ m.obj (redObj T d₂ h₂) :=
  mkH (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun r => eta_comm d₁ d₂ nm hρ T r)
    ⟨le_of_eq (Ideal.map_id _), fun x hx => rfl⟩ (fun x hx => hx) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have hw1 := (redObj ((nm.mor 0).obj T) d₁ h₁).w r
        have hw2 := (m.obj (redObj T d₂ h₂)).w r
        have h3 : Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((redObj ((nm.mor 0).obj T) d₁ h₁).i r) =
            Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((m.obj (redObj T d₂ h₂)).i r) :=
          congrArg (Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J) (eta_comm d₁ d₂ nm hρ T r)
        exact (congrArg (Ideal.quotientMap (m.obj (redObj T d₂ h₂)).J
          (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun x hx => hx)) hw1).trans (h3.trans hw2.symm)
      · have e := hpt _ (redObj T d₂ h₂).y
        refine Eq.trans ?_ e.symm
        change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (qBar ((nm.mor 0).obj T) l n)) ≫ (pt T ≫ nm.u) =
          (Spec.map (CommRingCat.ofHom (qBar T l n)) ≫ pt T) ≫ nm.u
        rw [Category.assoc, ← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end Eta

section Main
variable {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a))


include hc₁ hc₂ h₀ in
theorem lam_mem (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (a : Λ₁) :
    σ (lam₁ a) - lam₂ (σ₀ a) ∈ Ideal.span {(l : A₂) ^ n} := by
  refine Ideal.Quotient.eq.1 ?_
  have e := hρ (c₁ a)
  rw [h₀, hc₂, hc₁] at e
  exact e.symm


include hc₁ hc₂ h₀ in
theorem lam_smul (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (r : Option ℤ)
    (T : (TS γ₂ q₂ l s {⊤}).FullSubcategory) (a : Λ₁)
    (y : (sq (IdF.top (sP (TS γ₂ q₂ l s {⊤})).A) (stdI (TS γ₂ q₂ l s {⊤}) r ((l : A₂) ^ n))).obj T) :
    (σ.comp lam₁) a • y = (lam₂.comp σ₀) a • y := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext (Ideal.Quotient.eq.2 ?_)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (lam_mem d₁ d₂ c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ a)
  refine ln_le q₂ s {⊤} r T ?_
  change T.obj.i (σ (lam₁ a)) * (show T.obj.B from b) - T.obj.i (lam₂ (σ₀ a)) * (show T.obj.B from b) ∈ lnT T.obj l n
  rw [← sub_mul, ← map_sub, ← hz, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

end Main

theorem red_nm : ∀ {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u) →
    (∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X₁ q₁ κ₁) c₁) j),
    (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r).pull j ((B.omMor m σ₀ h₀).pull j x) =
      nmHM nm l s r n j ((redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).pull j x) := by
  intro O A₁ A₂ R₁ R₂ Λ₁ Λ₂ _ _ _ _ _ _ _ _ _ I₁ I₂ γ₁ γ₂ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X₁ X₂ q₁ q₂ s σ nm σ' m c₁ c₂ lam₁ lam₂
    hc₁ hc₂ σ₀ h₀ hpt hρ r j x
  let S2 := (nmS nm l s).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (nm_std nm l s r n)
  letI t1 : RingHomCompTriple σ₀ lam₂ (lam₂.comp σ₀) := ⟨rfl⟩
  letI t2 : RingHomCompTriple lam₁ σ (σ.comp lam₁) := ⟨rfl⟩
  let M1 : CH.Mor _ _ (lam₂.comp σ₀) := (B.omMor m σ₀ h₀).comp (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r)
  let M2 : CH.Mor _ _ (σ.comp lam₁) := (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).comp S2
  have hsc := lam_smul (q₂ := q₂) d₁ d₂ s c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ r
  have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := lam₂.comp σ₀) (B.omMor m σ₀ h₀) (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r) j x).1
  have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := σ.comp lam₁) (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r) S2 j x).1
  have h3 := pull_retype M2 (σ₂ := lam₂.comp σ₀) hsc j x
  let η : (retype M2 (lam₂.comp σ₀) hsc).G ⟶ M1.G :=
    { app := fun T => etaR d₁ d₂ nm m hpt hρ T.obj T.property.1 T.property.1
      naturality := fun T T' f => hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)) }
  have h4 := CrystallineSemistableComparison.P.prism (retype M2 (lam₂.comp σ₀) hsc) M1 η (fun T y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
    rfl) j x
  exact h1.symm.trans (h4.symm.trans (h3.trans h2))

end GlobalTheory.CompanionTheory.RedNat
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisCmp

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redMk (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

def cmpMk (n : ℕ) : Mor (Lc F κ false n) (Lc F κ true n) (RingHom.id _) :=
  B.crMor (F := F) (F' := F) (b := bs l false n) (b' := bs l true n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    ((base l).dp_fil_pfil n) (basePt F (Ideal.Quotient.factor le_sup_right) rfl) fun _ _ _ => rfl

theorem fac_κb (n : ℕ) :
    (Ideal.Quotient.factor (S := JJ false (base l) n) (T := JJ true (base l) n) le_sup_right).comp (κb κ false n) = κb κ true n := rfl

theorem cmp_pt {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((cmpMk F κ m).pt.app B₀ ((redMk F κ true h).pt.app B₀ y)).1.2 =
      ((redMk F κ false h).pt.app B₀ ((cmpMk F κ n).pt.app B₀ y)).1.2 :=
  SH.base_base F (κ₁ := κb κ false m) (κ₂ := κb κ true m) (κ₃ := κb κ false n) (κ₄ := κb κ true n)
    (fac_κb κ m) (red_κb κ true h) (red_κb κ false h) (fac_κb κ n) B₀ y

theorem red_cmp {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j) :
    redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) := by
  unfold redHc redMor cmpMor
  exact cr_square (cmpMk F κ m) (redMk F κ true h) (redMk F κ false h) (cmpMk F κ n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (cmp_pt F κ h) j x

theorem main : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j), redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) :=
  fun F κ _ _ h j x => red_cmp F κ h j x

end GlobalTheory.CompanionTheory.CrisCmp
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

def redFn (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) :
    Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem redHc_pullHc {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F' κ k m j) : redHc F κ k h j (pullHc κ u k m j x) = pullHc κ u k n j (redHc F' κ k h j x) := by
  unfold redHc pullHc redMor pullMorC
  exact cr_square (SH.pullM κ u k m) (redFn F κ k h) (redFn F' κ k h) (SH.pullM κ u k n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (SH.base_map u (red_κb κ k h)) j x

end GlobalTheory.CompanionTheory.CrisTransition
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

section

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

theorem red_galBase_le (σ : Gal(PadicAlgCl l/K)) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    (base l).red h (galBase σ m r) = galBase σ n ((base l).red h r) :=
  ((pdOk_twId σ _).red_acr h _).trans (congrArg (twAcr σ _ n) ((pdOk_hom (baseTw σ)).red_acr h r))

def redMle (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem reduction_commutes_galois_action (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ k m j) :
    redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  unfold redHc galHc redMor galMorC
  exact cr_square (SH.galM F κ σ hσ k m) (redMle F κ k h) (redMle F κ k h) (SH.galM F κ σ hσ k n) (galBase_cris σ m)
    (red_cris _ h) (red_cris _ h) (galBase_cris σ n) (red_galBase_le σ h)
    (SH.base_base F (gal_κb κ σ hσ k m) (red_κb κ k h) (red_κb κ k h) (gal_κb κ σ hσ k n)) j x

end

theorem redHc_galHc : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  intro l _ O _ F κ K σ hσ k m n h j x
  exact reduction_commutes_galois_action F κ σ hσ k h j x

end GlobalTheory.CompanionTheory.CrisTransition
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.DescTest

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem step_desc (hOut : D.Out l) (hk : k = false ∨ ρ = 0) (r : ℕ) :
    Desc (ε.qk 1 - 1) (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).fn (jE (F.pt κ)) :=
  desc_fil F κ ε k n ρ hρ hk r _ (des_qk hOut ε (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).1 n (ρ r))

theorem xi_thick (T : (F.pt κ).Elements) :
    ((gE F κ k n).obj T).i ((base l).cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i)) ∈ ((gE F κ k n).obj T).J :=
  xi_mem F κ k n T _ ((GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.1 T.1 n)

theorem mu_factor : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i :=
  (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.2.1

end



theorem main : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) →
    Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) := by
  intro l _ hOut O _ F κ ε k n ρ hρ hk
  exact desc_flt (b := bs l k n) (L := Lc F κ k n) (Λ := Acris l) (F.pt κ) ((base l).cris n) (gE F κ k n) ρ hρ
    ε.μ (ε.μ_mem k (base l) n) (jE (F.pt κ)) (ε.qk 1 - 1) (∑ i ∈ Finset.range l, ε.qk 1 ^ i)
    (mu_factor ε) (xi_thick F κ ε k n) (step_desc F κ ε k n ρ hρ hOut hk)

end GlobalTheory.CompanionTheory.DescTest
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.JSPair

def dotL (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] Cinf E :=
  ∑ i : Fin k, (ContinuousLinearMap.mul ℝ (Cinf E)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)

theorem dotL_apply {E : Type} [Field E] [NumberField E] {k : ℕ} (x z : Fin k → Cinf E) :
    dotL E k x z = ∑ i, x i * z i := by
  simp [dotL, ContinuousLinearMap.sum_apply]

theorem exists_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  intro E _ _ _ k ψ h8 hψ
  obtain ⟨l, hl⟩ := h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ)
    (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)
  let β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k
  have hβ : ∀ x z, β x z = -l (∑ i, x i * z i) := fun x z => by
    simp [β, dotL_apply]
  refine ⟨β, fun y hy => ?_, fun x z => ?_⟩
  · funext i
    refine GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_
    have h0 := hy (Pi.single i w)
    rw [hβ] at h0
    have e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_comm]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · simp
    rw [e] at h0
    have h1 : l (y i * w) = 0 := neg_eq_zero.1 h0
    rw [hl, h1]
    simp
  · have := hl (∑ i, x i * z i)
    rw [GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply] at this
    rw [this, hβ]
    simp

end GlobalTheory.CompanionTheory.JSPair

end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.Affgl

theorem exists_monic_aeval_mem_of_le_sup {R : Type*} [Ring R] [Algebra ℂ R] (A : Subalgebra ℂ R)
    (V I : Submodule ℂ R) [FiniteDimensional ℂ V] (h : ∀ z ∈ A, z ∈ V ⊔ I) (z : R) (hz : z ∈ A) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval z p ∈ I := by
  have hmemA : ∀ p : Polynomial ℂ, Polynomial.aeval z p ∈ A := by
    intro p
    have e : Polynomial.aeval z p = ((Polynomial.aeval (⟨z, hz⟩ : A) p : A) : R) := by
      simpa using (Polynomial.aeval_algHom_apply A.val (⟨z, hz⟩ : A) p)
    rw [e]
    exact Subtype.property _
  let f : Polynomial ℂ →ₗ[ℂ] R ⧸ I := I.mkQ ∘ₗ (Polynomial.aeval z).toLinearMap
  have hf : ∀ p, f p ∈ V.map I.mkQ := by
    intro p
    obtain ⟨v, hv, i, hi, e⟩ := Submodule.mem_sup.1 (h _ (hmemA p))
    refine ⟨v, hv, ?_⟩
    change I.mkQ v = I.mkQ (Polynomial.aeval z p)
    have hi0 : I.mkQ i = 0 := by simpa using hi
    rw [← e, map_add (f := _), hi0, add_zero]
  let g : Polynomial ℂ →ₗ[ℂ] V.map I.mkQ := f.codRestrict _ hf
  have hnot : ¬ Function.Injective g := fun hinj =>
    Polynomial.not_finite (R := ℂ) (Module.Finite.of_injective g hinj)
  obtain ⟨p, hgp, hp⟩ : ∃ p, g p = 0 ∧ p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnot ((injective_iff_map_eq_zero g).2 fun p hp => hcon p hp)
  have hI : Polynomial.aeval z p ∈ I := by
    have : f p = 0 := congrArg Subtype.val hgp
    simpa [f] using this
  refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [map_mul, Polynomial.aeval_C, ← Algebra.commutes, ← Algebra.smul_def]
  exact I.smul_mem _ hI

theorem exists_monic_aeval_apply_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (J : Set (Module.End ℂ (Sm E a))) (hJ : Cofin J) (z : Module.End ℂ (Sm E a))
    (hz : z ∈ Zalg E a) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) →
      Polynomial.aeval z p φ = 0 := by
  obtain ⟨-, V, hV, hcov⟩ := hJ
  obtain ⟨p, hp, hI⟩ := exists_monic_aeval_mem_of_le_sup (Zalg E a) V _ hcov z hz
  refine ⟨p, hp, fun φ hφ => ?_⟩
  have key : ∀ y ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, y φ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, -, j, hj, rfl⟩ := hy
      simp [hφ j hj]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key _ hI

theorem minpoly_on_killed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ z ∈ Zalg E a, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ a J hJ z hz => exists_monic_aeval_apply_eq_zero E a J hJ z hz

end GlobalTheory.CompanionTheory.Affgl
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

theorem _root_.GlobalTheory.T.quantum_det_capelli_operator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (u : ℂ) (φ : π.V), (Formalism.REAL.qdet (EopV π τ) (u + ((a : ℂ) - 1) / 2) φ).1 = cap τ u φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | exact GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | (intros; apply GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.cuspidal_twisted_kernel_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N → twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal <;> assumption)
end
