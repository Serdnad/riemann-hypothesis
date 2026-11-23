module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle023
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle106
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TensorComponentNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU.SuppRel

theorem component_ne_zero_iff_mod_two (F : Type) [Field F] (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (α : X) (s : E), ∃ s' : E, ∀ β,
      ((∃ mu, β = α + 2 • mu) → ex β s' = ex β s) ∧ ((¬ ∃ mu, β = α + 2 • mu) → ex β s' = 0))
    (hinj : ∀ α, ex α ≠ 0 → ∀ s, (∀ β, (¬ ∃ mu, β = α + 2 • mu) → ex β s = 0) → ex α s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → TensorProduct.map (ex α) (ex β) w = 0)
    (a b : X) :
    TensorProduct.map (ex (a + b)) (ex (a - b)) w ≠ 0 ↔ ex (a + b) ≠ 0 ∧ ex (a - b) ≠ 0 := by
  let H : AddSubgroup X := (nsmulAddMonoidHom 2 : X →+ X).range
  have hfg : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : H.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X two_ne_zero
  have hfin : Finite (X ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  have hcl : ∀ α β : X, (QuotientAddGroup.mk β : X ⧸ H) = QuotientAddGroup.mk α ↔ ∃ mu, β = α + 2 • mu := by
    intro α β
    rw [eq_comm, QuotientAddGroup.eq]
    constructor
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply] at h; rw [h]; abel⟩
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply, h]; abel⟩
  refine GlobalTheory.tensor_component_ne_zero_iff F X (X ⧸ H) QuotientAddGroup.mk E W ex hsep ?_ ?_ w hfull ?_ _ _ ?_
  · intro c s
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨s', hs'⟩ := hcut α s
    exact ⟨s', fun β => ⟨fun h => (hs' β).1 ((hcl α β).1 h), fun h => (hs' β).2 fun h' => h ((hcl α β).2 h')⟩⟩
  · intro α hα s hs h0
    exact hinj α hα s (fun β hβ => hs β fun h => hβ ((hcl α β).1 h)) h0
  · intro α β h
    refine hoff α β ?_
    rintro ⟨x, y, rfl, rfl⟩
    exact h ((hcl _ _).2 ⟨y, by rw [two_nsmul]; abel⟩)
  · exact (hcl _ _).2 ⟨b, by rw [two_nsmul]; abel⟩

theorem supp_rel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ a b : D.X, ((∃ j, (f a).f j ≠ 0) ∧ ∃ j, (f b).f j ≠ 0) ↔ (U.Supp (Kbar V) 2 (a + b) ∧ U.Supp (Kbar V) 2 (a - b))) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ a b
  obtain ⟨hG, hB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hG θ
  obtain ⟨s₀, hs₀, -⟩ := hB f
  obtain ⟨r, n, t, t', s, s', hr, hexp, hA, hAB⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨hth0, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨ex, hex, huniq, hsep, hsupp⟩ := GlobalTheory.T.exists_linear_fourierJacobi_expansion_family hL hL2 V hV D A G U (Kbar V) 2 (by norm_num)
  obtain ⟨hcut, -, hinj⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U 2 (by norm_num)
  obtain ⟨hon, hoff⟩ := GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff V D (Kbar V) s₀ r n s s' hr hAB
  have hcV : CharZero V := hV.2.2
  have hchar : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  have h2 : (2 : Kbar V) ≠ 0 := two_ne_zero
  let u : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t i)
  let u' : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t' i)
  have hfull := GlobalTheory.T.additionTensor_full_left_support hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) h2 (SecMod.mk _ th) n u u' hA
    (fun h => by
      obtain ⟨j, hj⟩ := hth0
      exact hj ((SecMod.eq_zero_iff _).1 h j))
  have hmap : ∀ α β : D.X, TensorProduct.map (ex α) (ex β) (∑ i, TensorProduct.tmul (Kbar V) (u i) (u' i)) =
      ∑ i, TensorProduct.tmul (Kbar V) (SecMod.mk _ (s i α) : WB D (Kbar V) 2 α)
        (SecMod.mk _ (s' i β) : WB D (Kbar V) 2 β) := by
    intro α β

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul, huniq _ _ (hexp i).1 α, huniq _ _ (hexp i).2 β]
    rfl
  have key := component_ne_zero_iff_mod_two (Kbar V) D.X (EA A (jFK (R := V) (Kbar V)) 2)
    (fun α => WB D (Kbar V) 2 α) ex hsep ?_ ?_ _ hfull (fun α β h => (hmap α β).trans (hoff α β h)) a b
  · rw [hsupp, hsupp, ← key, hmap, hon, GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ a,
      GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ b]
  · intro α v
    obtain ⟨v', p, hp, hβ⟩ := hcut α _ _ (hex v)
    refine ⟨SecMod.mk _ v', fun β => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases hβ β with h' | h'
      · exact (huniq _ _ hp β).symm.trans h'.2
      · exact absurd h h'.1
    · rcases hβ β with h' | h'
      · exact absurd h'.1 h
      · refine (SecMod.eq_zero_iff _).2 fun j => ?_
        rw [← huniq _ _ hp β]
        exact h'.2 j
  · intro α hα v hv h0
    exact (SecMod.eq_zero_iff _).2 (hinj α ((hsupp α).2 hα) _ _ (hex v)
      (fun β hβ => (SecMod.eq_zero_iff _).1 (hv β hβ)) ((SecMod.eq_zero_iff _).1 h0))

end GlobalTheory.UU.SuppRel
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SymLiftPhi

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_ratio (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val ^ k = gs (𝟙 _) z ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c ^ k)) * (val w (𝟙 _) z J).val ^ k) ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → PhiRel D F k p w' s (c • t) := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (mulGen_isGen _ _ _ _ _ _ _ hw' (invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ rfl (prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w' r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val w r z J).val := by
    intro Z r z J hJ
    have e := ha Z r z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine Eq.trans ?_ (congrArg (· * (val w r z J).val) e)
    rw [← Units.val_mul, inv_mul_cancel_right]
  refine ⟨c, fun z J hJ => ?_, fun s t h => ?_⟩
  · rw [hv _ _ z J hJ, mul_pow, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_pow, map_pow, map_pow]
  · rw [phiRel_iff hG p w hw] at h
    rw [phiRel_iff hG p w' hw']
    intro α β hαβ T ρ z J hJ
    refine (sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β hαβ T ρ z J hJ, val_mul hJ, val_mul hJ]
    simp only [Units.val_mul]
    rw [hv _ _ z J hJ]
    simp only [Over.comp_left]
    ring

theorem phiRel_of_val_eq (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen)
    (hw' : w'.IsGen) (h : ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J) {s t : Fam D F k}
    (hs : PhiRel D F k p w' s t) : PhiRel D F k p w s t := by
  have hc := corr_of_val D.P.isLB h
  rw [phiRel_iff hG p w' hw'] at hs
  rw [phiRel_iff hG p w hw]
  intro α β hαβ T ρ z J hJ
  rw [hs α β hαβ T ρ z J hJ, val_mul hJ, val_mul hJ, val_corr hJ hc]

end GlobalTheory.UT.SymLiftPhi

namespace GlobalTheory.UT

open SymLiftPhi in
theorem symLift_acts_as_phi : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) x, QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ w, TXFrame N p w → ∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s' := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact
  have hN1 : 1 ≤ N := hN.pos
  have gf : GlobalFnsSt := hL.1.globalFns
  obtain ⟨hxN, hx'⟩ := hx w₀ hw₀
  obtain ⟨w', hw', H⟩ := hx' θ hθ.pt_eq
  obtain ⟨b₁, b₂⟩ := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F N hN1 w₀ hw₀
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL.1 R I D F N hN1 p w hw.1
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL.1 R I D F N hN1 p w' hw'
  obtain ⟨c, hc, hcΦ⟩ := exists_ratio gf p hw.1 hw'
  have e : Φ' = c • Φ := LinearMap.ext fun u => ((hΦ' _ _).1 (hcΦ u _ ((hΦ _ _).2 rfl))).symm
  have h₁ : ∀ u, (Φ ^ N) u = u := fun u => by
    have := GlobalTheory.T.symmetricFrame_phi_pow_order_eq_id hL R I hI D F N hN p w hw (fun i => (Φ ^ (i : ℕ)) u) (fun i => (hΦ _ _).2 (by
      simp [pow_succ']))
    simpa using this
  have h₂ : ∀ u, (Φ' ^ N) u = u := fun u => by
    choose act hact using fun v => GlobalTheory.ThetaNu.exists_isActOf A.isLB θ v
    obtain ⟨v, hv, -⟩ := b₂ u
    have key : ∀ i : ℕ, U.ExpandsF F N w₀ (act^[i] v) ((Φ' ^ i) u) := fun i => by
      induction i with
      | zero => exact hv
      | succ i ih =>
        obtain ⟨u', hu', -⟩ := b₁ (act^[i + 1] v)
        have := (hΦ' _ _).1 (H _ _ _ _ ih hu' (by rw [Function.iterate_succ_apply']; exact hact _))
        rw [pow_succ', Module.End.mul_apply, ← this]
        exact hu'
    have hp := GlobalTheory.thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB N _ θ N (hθ.pt_eq ▸ hxN) hθ.pow_eq
      (fun i => act^[i] v) (fun i => by
        rw [Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']; exact hact _)
    have hp' : act^[N] v = v := SecOps.sec_ext hp
    have kN := key N
    rw [hp'] at kN
    exact (b₁ v).unique kN hv
  by_cases hcN : c ^ N = 1
  · have hT : TXFrame N p w' := ⟨hw', GlobalTheory.T.frame_sq_eq_of_symmetric_thetaElement hL R I hI D A G hG U F N hN1 p θ w₀ w' hw₀ hw' H hθ.sym,
      fun κ hκ z J hJ => by
        have a := hc z J hJ
        rw [hcN, map_one, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul,
          ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at a
        rw [Units.ext a]
        exact hw.2.2 κ hκ z J hJ⟩
    exact phiRel_of_val_eq gf p hw.1 hw' ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w' hw hT) (H t t' s s' hs hs' hact)
  · have z : ∀ u : Fam D.toPre F N, u = 0 := fun u => by
      have a := h₂ u
      rw [e, smul_pow, LinearMap.smul_apply, h₁] at a
      have b : (c ^ N - 1) • u = 0 := by rw [sub_smul, a, one_smul, sub_self]
      exact (smul_eq_zero.1 b).resolve_left (sub_ne_zero.2 hcN)
    exact (hΦ _ _).2 ((z _).trans (z _).symm)

end GlobalTheory.UT
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcRigidity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
  {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
  {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}

theorem core (hL : Laws) (hL₂ : Laws2) (hL₅ : Laws5)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c)
    (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ) (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ')
    (hs : y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF)
    (hs' : y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) :
    y = y' ∧ ∃ ψ : W.t.G ≅ W'.t.G,
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left)
        (τ : T ⟶ Sp (FractionRing (PowerSeries k))),
        g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ W.m.φ = g₁ ≫ Y.m.φ →
        g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
        g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) ∧
      ((∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ) := by
  letI := H.starRing
  obtain ⟨hD, hdat⟩ := GlobalTheory.arcWit_data_iso hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W'
  have hI : Ideal.span {(PowerSeries.X : PowerSeries k)} = IsLocalRing.maximalIdeal (PowerSeries k) :=
    PowerSeries.maximalIdeal_eq_span_X.symm
  obtain ⟨ψ, bc, hψ, hbc, hfst, hU⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data hL hL₂ (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD
  have hx : ∀ (x : 𝓞 E) (z : W.P.D.toPre.X), hD.xe (x • z) = x • hD.xe z := by
    intro x z
    obtain ⟨z₀, rfl⟩ := W.e.surjective z
    rw [← W.e.map_smul, hdat.2.1, hdat.2.1]
    exact W'.e.map_smul x z₀
  have hB : ∀ x, (W.P.oD.onB.act x).left ≫
        (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) =
      (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
        (W'.P.oD.onB.act x).left := by
    intro x
    apply W'.spec.1.1.hom_ext
    · have h₁ : (W.P.oD.onB.act x).left ≫ W.φ = W.φ ≫ (a.oa.onB.act x).left := W.spec.2.2.2.1 x
      have h₂ : (W'.P.oD.onB.act x).left ≫ W'.φ = W'.φ ≫ (a.oa.onB.act x).left := W'.spec.2.2.2.1 x
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hdat.1).trans h₁)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hdat.1)))).symm
    · have e : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
          W'.P.D.toPre.P.A.hom = W.P.D.toPre.P.A.hom := by
        have w : hD.e.hom.left ≫ pullback.snd W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k))) =
          W.P.D.toPre.P.A.hom := Over.w hD.e.hom
        rw [Category.assoc, pullback.condition, ← Category.assoc, w, specOf_id, Category.comp_id]
      rw [Category.assoc, e, Over.w, Category.assoc, Over.w, e]
  have hlin := act_comm_of_isPullUnif_id hL.globalFns (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD bc hbc hU (𝓞 E) W'.P.oD W.P.oD W'.P.oA W.P.oA
    W'.t.act.toRingAct W.t.act.toRingAct W'.P.lin W.P.lin hx hB
  have hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x := by
    intro x
    have q := congrArg (fun z => z.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k)))) (hlin x)
    ext
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at q
    rw [hfst, ← Category.assoc, hfst] at q
    exact q
  have hlev := GlobalTheory.T.uniformisedArc_iso_matches_levelPoints hL hL₂ hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact
    y y' hy hy' hs hs'
  have hb : LBIso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hU.lg
    rw [← W.P.bundle, ← W'.P.bundle, ← hfst]
    exact ⟨w, hw⟩
  obtain ⟨e, h⟩ := ArcObj.point_eq hL W.m W'.m ψ hact hb _ y y' hy hy' (hs.trans hs'.symm) hlev
  exact ⟨e, ψ, h, arcWit_agree_of_isPullUnif E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact⟩

theorem exists_generic
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    {T : Scheme.{0}} (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (h₁ : g ≫ W.m.φ = g₁ ≫ Y.m.φ) :
    (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j ∧
      ∃ τ : T ⟶ Sp (FractionRing (PowerSeries k)), g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) := by
  have := ThetaShiftProofs.isOpenImmersion_jK_powerSeries k
  have q : (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j := by
    have h₁' : g ≫ W.m.cm.F = g₁ ≫ Y.m.cm.F := h₁
    rw [Category.assoc, ← W.m.cart.1.w, reassoc_of% h₁', Y.m.cart.1.w, Category.assoc]; rfl
  have hr : Set.range (g ≫ W.t.G.hom) ⊆ Set.range (jK (PowerSeries k)) := by
    rintro _ ⟨p, rfl⟩
    exact arcWit_mem_range_jK_of_mem_range_j E H D l Xo c k bF a O β Y χ W _
      ⟨(g₁ ≫ Y.oF.t.G.hom) p, congrArg (fun z => z p) q.symm⟩
  exact ⟨q, _, (IsOpenImmersion.lift_fac (jK (PowerSeries k)) _ hr).symm⟩

end ArcRigidity

theorem rigidArc_of_mono : Laws → Laws2 → Laws5 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β')
    (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
    y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' →
    y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) := by
  intro hL hL₂ hL₅ E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' y y' hy hy' hs hs'
  obtain ⟨e, ψ, h, hA⟩ := ArcRigidity.core hL hL₂ hL₅ W W' y y' hy hy' hs hs'
  refine ⟨e, fun hm => ⟨ψ, hA fun T g g₁ g₂ h₁ h₂ h₃ => ?_⟩⟩
  obtain ⟨q, τ, hτ⟩ := ArcRigidity.exists_generic W g g₁ h₁
  refine h T g g₁ g₂ τ hτ ?_ h₁ h₂ h₃
  rw [← cancel_mono Y.j, ← q, hτ, Category.assoc, Category.assoc, hy]

end GlobalTheory
end
