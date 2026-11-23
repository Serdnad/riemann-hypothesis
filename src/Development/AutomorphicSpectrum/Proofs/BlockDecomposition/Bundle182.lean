module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle126
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle171
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle162
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle174
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
open TensorProduct DividedPowers

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem dividedPowerFiltration_dividedPowersBot_of_one_le {K : Type} [CommRing K] {r : ℕ} (hr : 1 ≤ r) : pdP (dividedPowersBot K) r = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact (dividedPowersBot K).dpow_eval_zero h0

theorem tfBase_dpBot {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s := by
  refine ⟨dividedPowerFiltration_dividedPowersBot_of_one_le hs, ?_, ?_⟩
  · intro r x h
    simpa only [Nat.cast_one, one_mul] using h
  · intro n hn
    refine ⟨0, (n : K)⁻¹, ?_⟩
    rw [pow_zero, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)]

theorem exists_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ), 1 ≤ s →
    ∃ (E : Frame (sP (KS q s {W})) d) (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε := by
  intro K _ _ X q W d c s hs
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase_dpBot hs
  obtain ⟨c', e, hTF, he1, he2, he3⟩ := GlobalTheory.CompanionTheory.ChartAlg.chart_exists (O := K) (R := K) (dividedPowersBot K) 1 s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  letI := (strV q W).toAlgebra
  have hg := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hD : KS q s {W} c'.D := ⟨hTF, W, rfl, c'.inV⟩
  let E := c'.frame hg (KS q s {W}) (ks_in q s W) hD
  have hpow (r : ℕ) : c'.D.pdPow r = (pdP (dividedPowersBot K) r).map c'.D.i :=
    GlobalTheory.CompanionTheory.ChartFil.dividedPowerFiltration_eq_map _ _ _ c'.D.compat c'.J_eq r
  have hc : E.GrConst (sFil (KS q s {W})) := by
    intro n T u v x hx
    have hx' : (show c'.D.B from x) ∈ c'.D.pdPow ((n : ℤ).toNat) := hx
    rw [Int.toNat_natCast, hpow] at hx'
    change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
    rw [show ((n : ℤ) + 1).toNat = n + 1 by omega]
    exact GlobalTheory.CompanionTheory.ChartFil.sub_mem_pdP c' (ks_in q s W _ T.property) u.hom v.hom n hx'
  let ε : Γ(X, W) ≃+* c'.D.B := (Algebra.TensorProduct.lid K Γ(X, W)).symm.toRingEquiv.trans e
  have hε : ∀ f, ε f = e ((1 : K) ⊗ₜ[K] f) := fun f => rfl
  refine ⟨E, ε, hc, fun x hx => ?_, fun a => ?_, fun T u g => ?_, fun i T u v => ?_⟩
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow 1 := hx
    rw [hpow, dividedPowerFiltration_dividedPowersBot_of_one_le le_rfl, Ideal.map_bot] at h2
    exact Ideal.mem_bot.1 h2
  · have e1 : (1 : K) ⊗ₜ[K] (strV q W a) = a ⊗ₜ[K] (1 : Γ(X, W)) := by
      have : strV q W a = a • (1 : Γ(X, W)) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change ε (strV q W a) = c'.D.i a
    rw [hε, e1, he1]
  · have h1 := GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) u.hom c'.inV (ks_in q s W _ T.property) g
    exact h1.trans ((congrArg (Ideal.quotientMap T.obj.J u.hom.φ u.hom.hle) (he3 g)).trans rfl)
  · change (v.hom.φ (c'.t i) - u.hom.φ (c'.t i) : T.obj.B) = v.hom.φ (ε (c.t i)) - u.hom.φ (ε (c.t i))
    rw [hε, he2]

end GlobalTheory.CompanionTheory.ConeLocal
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem cechOmAdd_smul {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j) :
    cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  letI := GlobalTheory.HodgeCoh.algΓ q
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  have h1 : ∀ z : CO q U a j, GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j (cechOmAdd q U hU hUaff a j z) =
      cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j z :=
    fun z => (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).apply_symm_apply _
  have h2 := cechHAddEquivH_naturality.{0} U hU hUaff
    (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j x
  have h3 := GlobalTheory.coh.toH_map K (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j
    (cechOmAdd q U hU hUaff a j x)
  rw [h1] at h3 ⊢
  exact h2.trans h3.symm

end GlobalTheory.CompanionTheory.OmCech
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCechDelta

theorem app_res_nat {X : TopCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (a : Q ⟶ Q₂)
    {A B : Opens X} (h : A ≤ B) (x : Q.obj (op B)) :
    a.app (op A) (res Q h x) = res Q₂ h (a.app (op B) x) := by
  exact NatTrans.naturality_apply a (homOfLE h).op x

theorem push_pullCoch {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {P P₂ : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (a : P ⟶ P₂) (a' : Q ⟶ Q₂) (φ : P ⟶ (Opens.map f).op ⋙ Q) (φ₂ : P₂ ⟶ (Opens.map f).op ⋙ Q₂)
    (h : ∀ W x, φ₂.app W (a.app W x) = a'.app _ (φ.app W x)) (n : ℕ) (σ : Cochain P V n) :
    push U a' n (pullCoch f φ V U τ hτ n σ) = pullCoch f φ₂ V U τ hτ n (push V a n σ) := by
  funext t
  exact (app_res_nat a' _ _).trans (congrArg (res Q₂ _) (h _ _).symm)

theorem cechPullH_delta : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
  intro X Y f κ ι V U τ hτ F I Q F' I' Q' g₁ g₂ g₁' g₂' hC hC' φ₁ φ₂ φ₃ h₁₂ h₂₃ n σ
  obtain ⟨t, ρ, hρ, ht, hρt, hc⟩ := hC.delta_spec n σ
  have h1 : push U g₂' n (pullCoch f φ₂ V U τ hτ n t) = pullCoch f φ₃ V U τ hτ n σ.1 := by
    rw [push_pullCoch f V U τ hτ g₂ g₂' φ₂ φ₃ h₂₃ n t, ht]
  have h2 : push U g₁' (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) =
      d I' U n (pullCoch f φ₂ V U τ hτ n t) := by
    rw [push_pullCoch f V U τ hτ g₁ g₁' φ₁ φ₂ h₁₂ (n + 1) ρ, hρt, pullCoch_d]
  have h3 : d F' U (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) = 0 := by
    rw [← pullCoch_d, hρ, map_zero]
  rw [hc, cechPullH_cls]
  exact hC'.deltaRel_unique ⟨pullCoch f φ₂ V U τ hτ n t, pullCoch f φ₁ V U τ hτ (n + 1) ρ, h3, h1, h2, rfl⟩
    (hC'.delta_spec n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩)

end GlobalTheory.CompanionTheory.OmCechDelta
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechDelta

theorem terminalEquiv_δ {X : TopCat.{0}} {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (n : ℕ)
    (y : Sheaf.H'.{0} S.X₃ n (⊤ : Opens X)) :
    GlobalTheory.SiteCoh.terminalEquiv S.X₁ (n + 1) isTerminalTop (GlobalTheory.SheafLES.δ hS n ⊤ y) =
      H.δ hS n (n + 1) rfl (GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y) := by
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (GlobalTheory.SiteCoh.freeSheafIsoConst isTerminalTop).inv) y hS.extClass (zero_add n) rfl (by omega)).symm

theorem hPull_δ {X Y : TopCat.{0}} (f : X ⟶ Y) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (α : S ⟶ S'.map (push f)) (n : ℕ) (x : Sheaf.H.{0} S.X₃ n) :
    hPull f α.τ₁ (n + 1) (H.δ hS n (n + 1) rfl x) = H.δ hS' n (n + 1) rfl (hPull f α.τ₃ n x) := by
  obtain ⟨y, rfl⟩ : ∃ y, GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y = x :=
    ⟨_, AddEquiv.apply_symm_apply _ x⟩
  rw [← terminalEquiv_δ hS n y]
  dsimp only [hPull, GlobalTheory.SheafPull.pull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  erw [GlobalTheory.SheafPull.sitePull_δ (TopologicalSpace.Opens.map f) hS hS' α n]
  exact terminalEquiv_δ hS' n _

end GlobalTheory.CompanionTheory.CechDelta
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.HT CrystallineSemistableComparison.Pb GlobalTheory.LogCris

namespace GlobalTheory.CompanionTheory.HodgePull

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem thick_ext {T T' : Thick (smFun X q)} (hB : T.B = T'.B) (hr : HEq T.ring T'.ring) (hi : HEq T.i T'.i)
    (hJ : HEq T.J T'.J) (hδ : HEq T.δ T'.δ) (hy : HEq T.y T'.y) : T = T' := by
  have hs : T.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T
  have hs' : T'.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T'
  cases T with
  | @mk B ring i J δ adm compat α y inα w x v s hx hs0 hv =>
  cases T' with
  | @mk B' ring' i' J' δ' adm' compat' α' y' inα' w' x' v' s' hx' hs0' hv' =>
  dsimp only at hB hr hi hJ hδ hy hs hs'
  subst hB
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hy
  obtain rfl : x = x' := funext fun j => Empty.elim j
  obtain rfl : v = v' := funext fun j => Empty.elim j
  obtain rfl : s = s' := hs.trans hs'.symm
  rfl

theorem hom_heq {T₁ T₂ T₁' T₂' : Thick (smFun X q)} (h : T₁ = T₂) (h' : T₁' = T₂') (f : T₁ ⟶ T₁') (g : T₂ ⟶ T₂')
    (hφ : HEq f.φ g.φ) : HEq f g := by
  subst h h'
  exact heq_of_eq (Thick.Hom.ext (eq_of_heq hφ) (funext fun j => Empty.elim j))

theorem obj_id (T : Thick (smFun X q)) : (smMor (𝟙 X) (Category.id_comp q)).obj T = T :=
  thick_ext rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Subtype.ext (Prod.ext rfl (Category.comp_id _))))

theorem functor_id : (smMor (𝟙 X) (Category.id_comp q)).functor = 𝟭 _ :=
  Functor.hext obj_id fun T T' f => hom_heq (obj_id T) (obj_id T') _ _ HEq.rfl

abbrev idMor (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ) : CH.Mor (grT (smFun X q) a) (grT (smFun X q) a) (RingHom.id K) :=
  (smS (𝟙 X) (Category.id_comp q)).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ))
    (b' := thFil _ ((a : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx

theorem τ_id (a : ℕ) (T : Thick (smFun X q)) (y : (grT (smFun X q) a).obj T) :
    (idMor q a).τ T y = y := by
  obtain ⟨x, hx⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem pullC_id (a n : ℕ) (z : CH.Cn (grT (smFun X q) a) n) : (idMor q a).pullC n z = z := by
  funext s
  have h : s ⋙ (idMor q a).G = s := by
    change s ⋙ (smMor (𝟙 X) (Category.id_comp q)).functor = s
    rw [functor_id]
    exact Functor.comp_id s
  exact (τ_id a _ _).trans (eq_of_heq (congr_arg_heq z h))

theorem pullH_id : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (a n : ℕ) (x : Hdg q a n),
    pullH (𝟙 X) (Category.id_comp q) a n x = x := by
  intro K _ X q a n x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (pullC_id a n z))

end GlobalTheory.CompanionTheory.HodgePull

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

theorem serre_of_equiv {R : Type} [CommRing R] (𝒮 : Serre.{1} R) {M N : Type 1} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : 𝒮.P M) : 𝒮.P N := by
  refine 𝒮.mid M N PUnit.{2} e.toLinearMap 0 ?_ h (𝒮.zero PUnit.{2} inferInstance)
  intro y
  exact iff_of_true (Subsingleton.elim _ _) ⟨e.symm y, e.apply_symm_apply y⟩

theorem serre_union : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (𝒮 : Serre.{1} R) (n : ℕ),
    (∀ p q, p + q = n → 𝒮.P ((_root_.CrystallineSemistableComparison.Pb.cechH F W q).cx.H p)) → 𝒮.P (HU F (fun T => ∃ α, W α T) n) := by
  intro R _ C _ F ι W hW 𝒮 n h
  have hle : ∀ α, W α ≤ (fun T => ∃ β, W β T : ObjectProperty C) := fun α T hT => ⟨α, hT⟩
  refine GlobalTheory.T.serre_class_of_cech_spectral_sequence ((ObjectProperty.ι (fun T => ∃ β, W β T : ObjectProperty C)) ⋙ F)
    (fun α T => W α T.obj) (fun α => by
      intro T T' f hT
      exact hW α f.hom hT T'.property) (fun T => T.property) 𝒮 n ?_
  intro p q hpq
  obtain ⟨e⟩ := GlobalTheory.T.cech_cohomology_full_subcategory_iso F (fun T => ∃ β, W β T : ObjectProperty C) W hle q p
  exact serre_of_equiv 𝒮 e.symm (h p q hpq)

end GlobalTheory.CompanionTheory.CosieveRel
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.scalar_multiplication_shifts_filtration : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  first | exact @GlobalTheory.CompanionTheory.LecShift.leC_shift | exact GlobalTheory.CompanionTheory.LecShift.leC_shift | (intros; apply GlobalTheory.CompanionTheory.LecShift.leC_shift <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeTwistingSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_chartHom {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (N : ℕ) (j : Fin (N + 1)) :
    ∃ c : ChartR R N j →+* ChartR R' N j,
      chart R' N j ≫ GlobalTheory.ProjSpace.baseChange N φ = spMap c ≫ chart R N j ∧
      ∀ k, c (ratio R N j k) = ratio R' N j k := by
  have key : ∀ (s : MvPolynomial (Fin (N + 1)) R') (_ : s = MvPolynomial.X j)
      (hd : s ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R' 1),
      ∃ ψ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s →+* ChartR R' N j,
        chart R' N j = spMap ψ ≫ Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s hd one_pos ∧
        ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R') (hf),
          ψ (HomogeneousLocalization.Away.mk _ hd n f hf) =
            HomogeneousLocalization.Away.mk _ (X_mem R' N j) n f hf := by
    rintro _ rfl hd
    refine ⟨RingHom.id _, ?_, fun _ _ _ => rfl⟩
    have e : spMap (RingHom.id (ChartR R' N j)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    rfl
  obtain ⟨ψ, h1, h2⟩ := key (GlobalTheory.ProjSpace.gradedMap N φ (MvPolynomial.X j)) (MvPolynomial.map_X φ j)
    ((GlobalTheory.ProjSpace.gradedMap N φ).2 (X_mem R N j))
  refine ⟨ψ.comp (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j)), ?_, fun k => ?_⟩
  · rw [h1, Category.assoc, GlobalTheory.ProjSpace.baseChange, Proj.awayι_comp_map _ _ one_pos _ (X_mem R N j),
      ← Spec.map_comp_assoc]
    rfl
  · change ψ (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j) _) = _
    rw [ratio, HomogeneousLocalization.Away.map_mk, h2]
    simp [ratio, GlobalTheory.ProjSpace.gradedMap]

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hO : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := by
  obtain ⟨N, i, hi, hp, het, s, hs, hu⟩ := hO
  have H := GlobalTheory.ProjSpace.isPullback_baseChange N φ
  have hw : (pullback.fst p (spMap φ) ≫ i) ≫ PSpace.str R N = pullback.snd p (spMap φ) ≫ spMap φ := by
    rw [Category.assoc, hp]
    exact pullback.condition
  obtain ⟨i', hi1, hi2⟩ : ∃ i' : pullback p (spMap φ) ⟶ PSpace R' N,
      i' ≫ GlobalTheory.ProjSpace.baseChange N φ = pullback.fst p (spMap φ) ≫ i ∧
      i' ≫ PSpace.str R' N = pullback.snd p (spMap φ) :=
    ⟨H.lift _ _ hw, H.lift_fst _ _ hw, H.lift_snd _ _ hw⟩
  have Hl : IsPullback i' (pullback.fst p (spMap φ)) (GlobalTheory.ProjSpace.baseChange N φ) i := by
    refine IsPullback.of_right (h₁₂ := PSpace.str R' N) (v₁₃ := spMap φ) (h₂₂ := PSpace.str R N) ?_ hi1 H.flip
    rw [hi2, hp]
    exact (IsPullback.of_hasPullback p (spMap φ)).flip
  have hc : IsClosedImmersion i' :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) Hl.flip hi
  choose c hc1 hc2 using fun j => exists_chartHom φ N j
  have hm : ∀ j, (pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ)) ≫ i =
      (pullback.snd i' (chart R' N j) ≫ spMap (c j)) ≫ chart R N j := fun j => by
    rw [Category.assoc, Category.assoc, ← hc1, ← hi1, ← Category.assoc, pullback.condition, Category.assoc]
  let m : ∀ j, pullback i' (chart R' N j) ⟶ pullback i (chart R N j) := fun j => pullback.lift _ _ (hm j)
  have hm1 : ∀ j, m j ≫ pullback.fst i (chart R N j) =
      pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => pullback.lift_fst _ _ _
  have hm2 : ∀ j, m j ≫ pullback.snd i (chart R N j) =
      pullback.snd i' (chart R' N j) ≫ spMap (c j) := fun j => pullback.lift_snd _ _ _
  have hl : ∀ j, (m j ≫ s j) ≫ D.f = pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => by
    rw [Category.assoc, hs, hm1]
  refine ⟨N, i', hc, hi2, ?_, fun j => pullback.lift (m j ≫ s j) (pullback.fst i' (chart R' N j)) (hl j),
    fun j => pullback.lift_snd _ _ _, ?_⟩
  · change Etale (pullback.snd D.f (pullback.fst p (spMap φ)))
    infer_instance
  · intro V j k a b h
    have h₀ : (a ≫ m j) ≫ pullback.fst i (chart R N j) = (b ≫ m k) ≫ pullback.fst i (chart R N k) := by
      rw [Category.assoc, Category.assoc, hm1, hm1, ← Category.assoc, ← Category.assoc, h]
    have e := hu V j k (a ≫ m j) (b ≫ m k) h₀
    have ueq : ∀ {a₁ a₂ b₁ b₂ : V ⟶ D.Y} (_ : a₁ = a₂) (_ : b₁ = b₂) (h₁ : a₁ ≫ D.f = b₁ ≫ D.f)
        (h₂ : a₂ ≫ D.f = b₂ ≫ D.f), D.u a₁ b₁ h₁ = D.u a₂ b₂ h₂ := by
      intro a₁ a₂ b₁ b₂ ha hb h₁ h₂
      subst ha hb
      rfl
    have nat : ∀ x, (spMap (c j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom x) =
        (Scheme.ΓSpecIso (CommRingCat.of (ChartR R' N j))).inv.hom (c j x) := fun x =>
      (congrArg (fun f => f.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (c j)))).symm
    have hs₂ : (a ≫ m j) ≫ pullback.snd i (chart R N j) =
        (a ≫ pullback.snd i' (chart R' N j)) ≫ spMap (c j) := by
      rw [Category.assoc, hm2, Category.assoc]
    refine (congrArg Units.val (ueq (by simp) (by simp) _ _)).trans (e.trans ?_)
    rw [hs₂, Scheme.Hom.comp_appTop]
    change (a ≫ pullback.snd i' (chart R' N j)).appTop.hom ((spMap (c j)).appTop.hom _) = _
    rw [nat, hc2]

end GlobalTheory.CompanionTheory.ConeTwistingSheaf
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.algebraically_independent_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), IsIntegral X → 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → (AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) → (V : Set X).Nonempty → letI := (strV q V).toAlgebra; AlgebraicIndependent K (tV i y hy V hV) := by
  first | exact @GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | exact GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | (intros; apply GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.homogeneous_ratio_isUnit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) (W : X.Opens)
    (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k'), IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  first | exact @GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit | exact GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit | (intros; apply GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_local_of_frame : GlobalTheory.CompanionTheory.GrForm.StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → GlobalTheory.CompanionTheory.GrForm.StLoc := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stLoc | exact GlobalTheory.CompanionTheory.GrForm.stLoc | (intros; apply GlobalTheory.CompanionTheory.GrForm.stLoc <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_vanish_of_frame : GlobalTheory.CompanionTheory.GrForm.StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → GlobalTheory.CompanionTheory.GrForm.StVan := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.van | exact GlobalTheory.CompanionTheory.GrForm.van | (intros; apply GlobalTheory.CompanionTheory.GrForm.van <;> assumption)
end
