module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotient
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPre_actPB_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O)
    (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s)
    (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act →
    ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧
      Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  intro h M B _ ζ O _ bar S S' s s' f z act hs hz hR hA
  obtain ⟨⟨w, φ, φ₂, hφ, hsq, hP, hlev⟩, hpr⟩ := GlobalTheory.siegPre_pullback h M B ζ S S' s s' f z hs
  have hwP : w.Principal := hpr w ⟨φ, φ₂, hφ, hsq, hP, hlev⟩ hz
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hφ (isGrpPullback_pullback z.A f)
  haveI := he
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  let actw : O → (w.A ⟶ w.A) := fun a => e.hom ≫ (Over.pullback f).map (act a) ≫ e.inv
  have hv : ∀ a, (actw a).left ≫ φ = φ ≫ (act a).left := fun a => by
    have hm : ((Over.pullback f).map (act a)).left ≫ pullback.fst z.A.hom f =
        pullback.fst z.A.hom f ≫ (act a).left := pullback.lift_fst _ _ _
    rw [← heφ]
    simp only [actw, Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  have hRw : IsRAct w.A actw := ActUnr.isRAct_conj e _ (ActUnr.isRAct_pullback f z.A act hR)
  have lf : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (fst Y Y).left = x.left :=
    fun x y => by rw [← Over.comp_left, lift_fst]
  have ls : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (snd Y Y).left = y.left :=
    fun x y => by rw [← Over.comp_left, lift_snd]
  have hc1 : ∀ a, (lift (fst w.A w.A ≫ actw a) (snd w.A w.A)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A ≫ act a) (snd z.A z.A)).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, Over.comp_left _ _ _ (fst w.A w.A) (actw a),
        Over.comp_left _ _ _ (fst z.A z.A) (act a), Category.assoc, hv, ← Category.assoc, ← hsq.1, Category.assoc]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, hsq.2]
  have hc2 : ∀ a, (lift (fst w.A w.A) (snd w.A w.A ≫ actw (bar a))).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar a))).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, hsq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, Over.comp_left _ _ _ (snd w.A w.A) (actw (bar a)),
        Over.comp_left _ _ _ (snd z.A z.A) (act (bar a)), Category.assoc, hv, ← Category.assoc, ← hsq.2, Category.assoc]
  have hadj : Adj w.A w.P bar actw := fun a => by
    have h1 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc1 a).symm
    have h2 := GlobalTheory.GenSpread.lbIso_pull_comp (L := z.P) (M := z.P) φ₂ rfl rfl (hA a)
    have h3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc2 a).symm
    exact LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB w.isLB _)
      (LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB z.isLB _) h1 h2) h3.symm
  exact ⟨w, actw, hwP, hRw, hadj, φ, φ₂, hφ, hsq, hP, hlev, hv⟩

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem actPB_of_zRel : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d _ _ _ hd _ jl n o κ S t c z₁ z₂ act₁ act₂ hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂ hZ₁ hZ₂
  obtain ⟨inc₁, pr₁, hi₁, hp₁, hip₁, hpi₁, hL₁, -, hz₁⟩ := hZ₁
  obtain ⟨inc₂, pr₂, hi₂, hp₂, hip₂, hpi₂, hL₂, -, hz₂⟩ := hZ₂
  have hker : ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔
      x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1 := fun T x =>
    ⟨fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x hx),
     fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x hx)⟩
  obtain ⟨e, he, hinc, hact⟩ := GlobalTheory.T.zarhinTrick_actions_isomorphic h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ hdS hA₁ hA₂
    hi₁ hp₁ hip₁ hpi₁ hi₂ hp₂ hip₂ hpi₂ hker
  have hLB := GlobalTheory.T.zarhinTrick_bundle_unique_of_order_linear_iso h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ e hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂
    hi₁ hp₁ hip₁ hpi₁ hL₁ hL₂ he hinc hact
  haveI := he
  refine ⟨e.hom.left, (e.hom ⊗ₘ e.hom).left, isGrpPullback_of_iso e, ⟨?_, ?_⟩, hLB, fun a => ?_, fun o => ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [Category.id_comp, ← Over.comp_left, hz₁ a, hz₂ a]
    congr 1
    have key := map_list_prod (IsMonHom.monoidHom e.hom (𝟙_ (Over S)))
      (List.ofFn fun k => c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))
    refine key.trans ?_
    rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    show (c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)) ≫ e.hom = _
    rw [Category.assoc, Category.assoc, hact, ← Category.assoc inc₁, hinc]
  · rw [← Over.comp_left, ← Over.comp_left, hact o]

end GlobalTheory.ZarhinFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPB_of_zRel_actPB : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B)
    (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A))
    (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)),
    ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hZ₁ hZ₂
  obtain ⟨ψ, ψ₂, hψ, sψ, lψ, vψ, aψ⟩ := hA
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, L₁, V₁, -⟩ := hZ₁
  obtain ⟨inc₂, pr₂, mi₂, mp₂, ip₂, pi₂, L₂, V₂, -⟩ := hZ₂
  have ip₁' : inc₁.left ≫ pr₁.left = 𝟙 _ := by rw [← Over.comp_left, ip₁]; rfl
  have ip₂' : inc₂.left ≫ pr₂.left = 𝟙 _ := by rw [← Over.comp_left, ip₂]; rfl
  have pi₁' : pr₁.left ≫ inc₁.left = (act₁ e).left := by rw [← Over.comp_left, pi₁]
  have pi₂' : pr₂.left ≫ inc₂.left = (act₂ e).left := by rw [← Over.comp_left, pi₂]
  have K0 : inc₂.left ≫ (act₂ e).left = inc₂.left := by
    rw [← pi₂', ← Category.assoc, ip₂', Category.id_comp]
  obtain ⟨φ, hφ⟩ : ∃ φ : c₂.A.left ⟶ c₁.A.left, φ = inc₂.left ≫ ψ ≫ pr₁.left := ⟨_, rfl⟩
  have K1 : φ ≫ inc₁.left = inc₂.left ≫ ψ := by
    rw [hφ, Category.assoc, Category.assoc, pi₁', ← aψ e, ← Category.assoc, K0]
  have K2 : pr₂.left ≫ φ = ψ ≫ pr₁.left := by
    have : (act₁ e).left ≫ pr₁.left = pr₁.left := by
      rw [← pi₁', Category.assoc, ip₁', Category.comp_id]
    rw [hφ, ← Category.assoc, ← Category.assoc, pi₂', aψ e, Category.assoc, this]
  have hw : φ ≫ c₁.A.hom = c₂.A.hom ≫ y := by
    rw [hφ, Category.assoc, Category.assoc, Over.w pr₁, hψ.1.w, ← Category.assoc, Over.w inc₂]
  have hpb : IsPullback φ c₂.A.hom c₁.A.hom y := by
    let lft : ∀ s : PullbackCone c₁.A.hom y, s.pt ⟶ c₂.A.left := fun s =>
      hψ.1.lift (s.fst ≫ inc₁.left) s.snd (by rw [Category.assoc, Over.w inc₁]; exact s.condition) ≫ pr₂.left
    refine IsPullback.of_isLimit (c := PullbackCone.mk φ c₂.A.hom hw)
      (PullbackCone.IsLimit.mk hw lft (fun s => ?_) (fun s => ?_) (fun s m hm1 hm2 => ?_))
    · simp only [lft]
      rw [Category.assoc, K2, ← Category.assoc, hψ.1.lift_fst, Category.assoc, ip₁', Category.comp_id]
    · simp only [lft]
      rw [Category.assoc, Over.w pr₂, hψ.1.lift_snd]
    · have e₁ : m ≫ inc₂.left = hψ.1.lift (s.fst ≫ inc₁.left) s.snd
          (by rw [Category.assoc, Over.w inc₁]; exact s.condition) := by
        apply hψ.1.hom_ext
        · rw [hψ.1.lift_fst, Category.assoc, ← K1, ← Category.assoc, hm1]
        · rw [hψ.1.lift_snd, Category.assoc, Over.w inc₂, hm2]
      calc m = m ≫ inc₂.left ≫ pr₂.left := by rw [ip₂', Category.comp_id]
        _ = lft s := by rw [← Category.assoc, e₁]
  have hmul : ∀ (T : Over S₂) (x x' : T ⟶ c₂.A) (x₀ x₀' : Over.mk (T.hom ≫ y) ⟶ c₁.A),
      x₀.left = x.left ≫ φ → x₀'.left = x'.left ≫ φ → (x₀ * x₀').left = (x * x').left ≫ φ := by
    intro T x x' x₀ x₀' hx hx'
    haveI := mi₂
    haveI := mp₁
    have wx : ∀ z : T ⟶ c₂.A, ((z ≫ inc₂).left ≫ ψ) ≫ w₁.A.hom = (Over.mk (T.hom ≫ y)).hom := fun z => by
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w (z ≫ inc₂)]; rfl
    let X₀ : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x ≫ inc₂).left ≫ ψ) (wx x)
    let X₀' : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x' ≫ inc₂).left ≫ ψ) (wx x')
    have m := hψ.2 T (x ≫ inc₂) (x' ≫ inc₂) X₀ X₀' rfl rfl
    rw [← mul_comp] at m
    have e₀ : X₀ ≫ pr₁ = x₀ := by
      ext1
      rw [Over.comp_left, hx, hφ]
      show ((x ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    have e₀' : X₀' ≫ pr₁ = x₀' := by
      ext1
      rw [Over.comp_left, hx', hφ]
      show ((x' ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    rw [← e₀, ← e₀', ← mul_comp, Over.comp_left, m, hφ, Over.comp_left, Category.assoc, Category.assoc]
  have sq := ActUnr.sqMap_fst hw
  have sq' := ActUnr.sqMap_snd hw
  refine ⟨φ, ActUnr.sqMap hw, ⟨hpb, hmul⟩, ⟨sq, sq'⟩, ?_, fun a => ?_⟩
  · have f₁ : (inc₁ ⊗ₘ inc₁).left ≫ (fst w₁.A w₁.A).left = (fst c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₁ : (inc₁ ⊗ₘ inc₁).left ≫ (snd w₁.A w₁.A).left = (snd c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have f₂ : (inc₂ ⊗ₘ inc₂).left ≫ (fst w₂.A w₂.A).left = (fst c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₂ : (inc₂ ⊗ₘ inc₂).left ≫ (snd w₂.A w₂.A).left = (snd c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have E : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = ActUnr.sqMap hw ≫ (inc₁ ⊗ₘ inc₁).left := by
      apply ActUnr.left_hom_ext
      · rw [Category.assoc, sψ.1, ← Category.assoc, f₂]
        simp only [Category.assoc]
        rw [f₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq, Category.assoc, K1]
      · rw [Category.assoc, sψ.2, ← Category.assoc, g₂]
        simp only [Category.assoc]
        rw [g₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq', Category.assoc, K1]
    have l₂ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB w₂.isLB c₂.isLB lψ L₂
    have hN := pull_isLB c₁.isLB (ActUnr.sqMap hw)
    have l₁ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB c₁.isLB hN L₁ ((GlobalTheory.CechPic.cls_eq_iff hN hN).1 rfl)
    rw [E] at l₂
    exact LBIso.trans c₂.isLB (pull_isLB w₁.isLB _) hN l₂ (LBIso.symm l₁)
  · calc (c₂.lev a).left ≫ φ = (c₂.lev a ≫ inc₂).left ≫ ψ ≫ pr₁.left := by
          rw [hφ, Over.comp_left, Category.assoc]
      _ = (w₂.lev (jl a)).left ≫ ψ ≫ pr₁.left := by rw [V₂ a]
      _ = y ≫ (w₁.lev (jl a)).left ≫ pr₁.left := by rw [← Category.assoc, vψ, Category.assoc]
      _ = y ≫ (c₁.lev a).left := by rw [← V₁ a, Over.comp_left, Category.assoc, ip₁', Category.comp_id]

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem zRel_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hS hZ
  obtain ⟨ψ, ψ₂, hψ, sqψ, hwP, hwl, hact⟩ := hA
  obtain ⟨φ, φ₂, hφ, sqφ, hcP, hcl⟩ := hS
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, hP₁, hl₁, hz₁⟩ := hZ
  haveI := mi₁
  haveI := mp₁
  have wi : (φ ≫ inc₁.left) ≫ w₁.A.hom = c₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w inc₁]; exact hφ.1.w
  let inc₂ : c₂.A ⟶ w₂.A := Over.homMk (hψ.1.lift (φ ≫ inc₁.left) c₂.A.hom wi) (hψ.1.lift_snd _ _ _)
  have inc₂_l : inc₂.left ≫ ψ = φ ≫ inc₁.left := hψ.1.lift_fst _ _ _
  have wp : (ψ ≫ pr₁.left) ≫ c₁.A.hom = w₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w pr₁]; exact hψ.1.w
  let pr₂ : w₂.A ⟶ c₂.A := Over.homMk (hφ.1.lift (ψ ≫ pr₁.left) w₂.A.hom wp) (hφ.1.lift_snd _ _ _)
  have pr₂_l : pr₂.left ≫ φ = ψ ≫ pr₁.left := hφ.1.lift_fst _ _ _
  have extW : ∀ {T : Over S₂} (a b : T ⟶ w₂.A), a.left ≫ ψ = b.left ≫ ψ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hψ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have extC : ∀ {T : Over S₂} (a b : T ⟶ c₂.A), a.left ≫ φ = b.left ≫ φ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hφ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have pI : ∀ (T : Over S₂) (x : T ⟶ c₂.A), pushHom hψ T (x ≫ inc₂) = pushHom hφ T x ≫ inc₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ inc₂).left ≫ ψ = (x.left ≫ φ) ≫ inc₁.left
      rw [Over.comp_left, Category.assoc, inc₂_l, Category.assoc])
  have pP : ∀ (T : Over S₂) (x : T ⟶ w₂.A), pushHom hφ T (x ≫ pr₂) = pushHom hψ T x ≫ pr₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ pr₂).left ≫ φ = (x.left ≫ ψ) ≫ pr₁.left
      rw [Over.comp_left, Category.assoc, pr₂_l, Category.assoc])
  have mI : IsMonHom inc₂ := isMonHom_of_mul _ fun T x z => extW _ _ (congrArg (fun q => q.left)
    (calc pushHom hψ T ((x * z) ≫ inc₂) = pushHom hφ T (x * z) ≫ inc₁ := pI _ _
      _ = (pushHom hφ T x * pushHom hφ T z) ≫ inc₁ := by rw [map_mul]
      _ = (pushHom hφ T x ≫ inc₁) * (pushHom hφ T z ≫ inc₁) := MonObj.mul_comp _ _ _
      _ = pushHom hψ T (x ≫ inc₂) * pushHom hψ T (z ≫ inc₂) := by rw [pI, pI]
      _ = pushHom hψ T ((x ≫ inc₂) * (z ≫ inc₂)) := (map_mul _ _ _).symm))
  have mP : IsMonHom pr₂ := isMonHom_of_mul _ fun T x z => extC _ _ (congrArg (fun q => q.left)
    (calc pushHom hφ T ((x * z) ≫ pr₂) = pushHom hψ T (x * z) ≫ pr₁ := pP _ _
      _ = (pushHom hψ T x * pushHom hψ T z) ≫ pr₁ := by rw [map_mul]
      _ = (pushHom hψ T x ≫ pr₁) * (pushHom hψ T z ≫ pr₁) := MonObj.mul_comp _ _ _
      _ = pushHom hφ T (x ≫ pr₂) * pushHom hφ T (z ≫ pr₂) := by rw [pP, pP]
      _ = pushHom hφ T ((x ≫ pr₂) * (z ≫ pr₂)) := (map_mul _ _ _).symm))
  have h1 : inc₂ ≫ pr₂ = 𝟙 c₂.A := extC _ _ (by
    rw [Over.comp_left, Over.id_left, Category.assoc, pr₂_l, ← Category.assoc, inc₂_l, Category.assoc,
      ← Over.comp_left, ip₁, Over.id_left, Category.comp_id, Category.id_comp])
  have h2 : pr₂ ≫ inc₂ = act₂ e := extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, pr₂_l, Category.assoc, ← Over.comp_left, pi₁,
      hact])
  have eι : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = φ₂ ≫ (inc₁ ⊗ₘ inc₁).left := by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, sqψ.1, ← Category.assoc, ← Over.comp_left, tensorHom_fst, Category.assoc, ← Over.comp_left,
        tensorHom_fst, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.1,
        Category.assoc]
    · rw [Category.assoc, sqψ.2, ← Category.assoc, ← Over.comp_left, tensorHom_snd, Category.assoc, ← Over.comp_left,
        tensorHom_snd, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.2,
        Category.assoc]
  have P1 : LBIso (c₁.P.pull φ₂) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c₁.P φ₂ φ₂ rfl)
      (chartPullSame w₁.P _ (fun _ => (inc₁ ⊗ₘ inc₁).left) _ φ₂ fun _ => rfl) hP₁
  have P2 : LBIso (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull w₂.P (inc₂ ⊗ₘ inc₂).left (inc₂ ⊗ₘ inc₂).left rfl)
      (chartPullSame w₁.P _ (fun _ => ψ₂) _ (inc₂ ⊗ₘ inc₂).left fun _ => eι.symm) hwP
  have hP₂ : LBIso c₂.P (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) :=
    LBIso.trans c₂.isLB (pull_isLB c₁.isLB _) (pull_isLB w₂.isLB _) hcP
      (LBIso.trans (pull_isLB c₁.isLB _) (pull_isLB w₁.isLB _) (pull_isLB w₂.isLB _) P1 P2.symm)
  have lv : ∀ a, c₂.lev a ≫ inc₂ = w₂.lev (jl a) := fun a => extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, hcl, Category.assoc, ← Over.comp_left, hl₁, hwl])
  let T₀ : Over S₂ := 𝟙_ (Over S₂)
  let u : Over.mk (T₀.hom ≫ y) ⟶ 𝟙_ (Over S₁) := toUnit _
  have hu : u.left = y := by
    simp [u, T₀]
  have pL : ∀ a, pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := fun a => Over.OverMorphism.ext (by
    show (w₂.lev a).left ≫ ψ = u.left ≫ (w₁.lev a).left
    rw [hu, hwl])
  have pT : ∀ (b : Fin h ⊕ Fin h → ℤ) (r : O), pushHom hψ T₀ (c₂.lev b ≫ inc₂ ≫ act₂ r) =
      u ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r) := fun b r => Over.OverMorphism.ext (by
    show (c₂.lev b ≫ inc₂ ≫ act₂ r).left ≫ ψ = u.left ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r).left
    simp only [Over.comp_left, Category.assoc]
    rw [hact, reassoc_of% inc₂_l, reassoc_of% (hcl b), hu])
  have lz : ∀ a, w₂.lev a = (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := fun a =>
    extW _ _ (congrArg (fun q => q.left)
      (calc pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := pL a
        _ = preHom (G := w₁.A) u (List.ofFn fun k => c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)).prod := by
          rw [hz₁ a]; rfl
        _ = (List.ofFn fun k => u ≫ (c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl
        _ = (List.ofFn fun k => pushHom hψ T₀ (c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k))).prod := by
          simp only [pT]
        _ = pushHom hψ T₀ (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl))
  exact ⟨inc₂, pr₂, mI, mP, h1, h2, hP₂, lv, lz⟩

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZRelLevs

theorem zrel_levs : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  intro h h' M O _ e jl n o κ S' T t z act g c' w' actw' hpb hz
  obtain ⟨φ, φ₂, hφ, -, -, hl, ha⟩ := hpb
  obtain ⟨inc, pr, -, -, hip, hpi, -, hc, hw⟩ := hz
  have key : ∀ b (oo : O), (w'.lev b ≫ actw' oo).left ≫ φ = g ≫ (z.lev b ≫ act oo).left := by
    intro b oo
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hl, Category.assoc]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← key, ← hl]
    congr 2
    rw [← hc, Category.assoc, ← hpi, ← Category.assoc inc, hip, Category.id_comp]
  · rw [← hl, hw a]
    have e1 : ((List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left ≫ φ =
        (pushHom hφ (𝟙_ (Over T)) (List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left := rfl
    rw [e1, map_list_prod, List.map_ofFn]
    have e2 : g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left =
        (toUnit (Over.mk ((𝟙_ (Over T)).hom ≫ g)) ≫
          (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
      rw [Over.comp_left, Over.toUnit_left]
      rfl
    rw [e2, GlobalTheory.comp_list_prod_ofFn]
    congr 3
    funext k
    apply Over.OverMorphism.ext
    show (c'.lev (κ k a) ≫ inc ≫ actw' (o k)).left ≫ φ = _
    rw [← Category.assoc, hc, key]
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_hom]
    rfl

end GlobalTheory.ZRelLevs
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  first | (exact @GlobalTheory.HInvAic.main) | (exact GlobalTheory.HInvAic.main) | (intros; apply GlobalTheory.HInvAic.main  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.units_cohomology_bijective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective_of_aic) | (exact GlobalTheory.EtC.gmPhi_bijective_of_aic) | (intros; apply GlobalTheory.EtC.gmPhi_bijective_of_aic  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurent_cohomology_finite_killing : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (_root_.GlobalTheory.EtC.GmStep.laurentMap (algebraMap A A'))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmKill.main) | (exact GlobalTheory.EtC.GmKill.main) | (intros; apply GlobalTheory.EtC.GmKill.main  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_identity_of_hodge_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) := by
  first | (exact @GlobalTheory.HTLieCrys.lieAt_id_of_liftFil) | (exact GlobalTheory.HTLieCrys.lieAt_id_of_liftFil) | (intros; apply GlobalTheory.HTLieCrys.lieAt_id_of_liftFil <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.harrisTaylor_pullback_kernel_locus_isClopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ PolKerAt o ψ' c t := by
  first | exact @GlobalTheory.UPel.HT.ES.polKer_locus_clopen | exact GlobalTheory.UPel.HT.ES.polKer_locus_clopen | exact @GlobalTheory.UPel.HT.ES.isMonHom_id_npow | exact GlobalTheory.UPel.HT.ES.isMonHom_id_npow
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → GlobalTheory.HTRho.jSub (GlobalTheory.HTCount.crysAct o₀) (fun i => β.comp (b.t i)) ⊤ ≤ (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ∧ ∀ i, Module.finrank k (HdR o₀.A ⧸ ((Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ⊔ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤)) = D.m := by
  first | (exact @GlobalTheory.HTLieRho.lie_rho_quot) | (exact GlobalTheory.HTLieRho.lie_rho_quot) | (intros; apply GlobalTheory.HTLieRho.lie_rho_quot  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β → ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  first | (exact @GlobalTheory.HTCount.lieZ_le_Fil) | (exact GlobalTheory.HTCount.lieZ_le_Fil) | (intros; apply GlobalTheory.HTCount.lieZ_le_Fil  <;> assumption)
end
