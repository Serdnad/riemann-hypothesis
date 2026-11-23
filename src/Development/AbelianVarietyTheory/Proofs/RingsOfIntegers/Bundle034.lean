module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle027
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle008
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle028
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.PlaceInt

theorem span_mul_prod_of_eq {E T : Type} [Field E] [Fintype T] {F F' : IntermediateField ℚ ℂ} (h : F' = F)
    (A B : Set E) (f : T → E →+* F) (f' : T → E →+* F')
    (hf : ∀ τ x, f' τ x = IntermediateField.equivOfEq h.symm (f τ x)) (m : T → ℕ) (β : F)
    (hβ : Submodule.span (𝓞 F) {β} * ∏ τ, Submodule.span (𝓞 F) (f τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F) (f τ '' B) ^ m τ) :
    Submodule.span (𝓞 F') {IntermediateField.equivOfEq h.symm β} * ∏ τ, Submodule.span (𝓞 F') (f' τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F') (f' τ '' B) ^ m τ := by
  subst h
  have hff : f' = f := funext fun τ => RingHom.ext fun x => hf τ x
  subst hff
  exact hβ

theorem totalDegree_le_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) {k : Type} [Field k] (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : RowDeg r n k a P) :
    P.totalDegree ≤ ∑ τ, ∑ i : Fin (r τ), a τ i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => le_of_eq ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hP m hm σ i

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_embF (τ : E →+* ℂ) (x : E) : d.eF (embF c τ x) = embF d.c₂ τ x := by
  exact Subtype.ext rfl

theorem map_eF_mem_symO (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ symO c Λ) :
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ symO (Dw := Dw) d.c₂ Λ := by
  have key : symO c Λ ≤ (symO (Dw := Dw) d.c₂ Λ).comap (MvPolynomial.map (d.eF : c.F →+* d.c₂.F)) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨⟨d.eF o, ?_⟩, ?_⟩))
      · exact o.2.map (d.eF : c.F →+* d.c₂.F).toIntAlgHom
      · rw [MvPolynomial.map_C]
        rfl
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨σ, i, b, hb, ?_⟩))

      simp only [letB, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, RingHom.coe_coe, eF_embF]
  exact key hP

end

theorem eF_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Λ : GenLat E n), (∀ β : c.F, BetaIs (Dw := Dw) c Λ β → BetaIs (Dw := Dw) d.c₂ Λ (d.eF β)) ∧ (∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ Λ w ∧ P.totalDegree ≤ Formalism.L2.Pj.DF Dw w) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E), d.eF (nrm Dw c w α) = nrm Dw d.c₂ w α := by
  intro E _ _ _ H Dw l Xo c n d Λ
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    unfold BetaIs idealAt at hβ ⊢
    exact span_mul_prod_of_eq d.hF (detSet Λ.La) (detSet Λ.Ln) (fun τ => embF c τ) (fun τ => embF d.c₂ τ)
      (fun τ x => (eF_embF d τ x).symm) Dw.mult β hβ
  · intro w P hP
    obtain ⟨hH, hS⟩ := hP
    refine ⟨⟨GlobalTheory.map_mem_HHa Dw.mult n (d.eF : c.F →+* d.c₂.F) d.eF.surjective ComplexEmbedding.conjugate
      (InPsi H) (fun τ i => w (τ, i)) P hH, map_eF_mem_symO d Λ P hS⟩, ?_⟩
    exact totalDegree_le_of_rowDeg Dw.mult n (fun τ i => w (τ, i)) P hH.2.2
  · intro w α
    simp only [nrm, embK, map_prod, map_pow, RingHom.comp_apply, eF_embF]

end GlobalTheory.PlaceInt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpansion

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_mul_of_id {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → sval a (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval b (𝟙 Y) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) :
    sval a r z J = gs r z ⊤ c * sval b r z J := by
  have key : ∀ j : K → L.ι, a.f j =
      (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from b.f j) := fun j =>
    fn_ext (V := LB.wchart L φ j) fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hI' : Good L y I := hI
      refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y le_top hy c)
        (sec_trans b (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))))).symm
      refine (sec_trans a (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))).trans ?_
      exact (congrArg _ (h y I hI')).trans (mul_left_comm _ _ _)
  have hm := hJ.mem φ r
  exact (congrArg (gs r z _) (key _)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg (· * sval b r z J) (gs_res r z le_top hm c)))

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

theorem unitK_snd : unitK (G := G) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := pullback.lift_snd _ _ _

theorem unitK_endK (f : G ⟶ G) [IsMonHom f] : unitK (G := G) ≫ endK f = unitK := by
  have he : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply pullback.hom_ext
  · simp only [unitK, endK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact congrArg (jK V ≫ ·) he
  · simp only [unitK, endK, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

end

theorem expands_pull_of_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  intro hLaws V _ _ _ E _ _ _ H t P a N hN hN0
  letI := H.starRing
  intro k hk s F hs s' hs'
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN0
  choose Fx hFx hFu using (P.U.expand k hk1).1
  choose Fp hFp using fun F : Fam P.D.toPre (FractionRing V) k =>
    exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
      (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  choose sp hsp _ using (P.U.expand (k * N) hkN).2
  obtain rfl : F = Fx s := hFu s F hs
  refine ⟨Fp (Fx s), ?_, hFp _⟩
  obtain ⟨u, hu, hn, hrel⟩ := hs'
  haveI : IsMonHom (t.act.act a) := t.act.hom a
  have hF : FormEq (fun _ : Fin 1 => gK (G := t.G)) (fun _ => ((k * N : ℕ) : ℤ))
      (Sum.elim (fun _ : Fin 1 => endK (t.act.act a) ≫ gK) ![gK, endK (t.act.act a) ≫ gK])
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := fun U _ g => by
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.SectionRatio.ratio_glue _ _ P.U.LG.L hL _ _ _ _ _ (fun _ : Fin 1 => gK) _ _ _
    (endK (t.act.act a)) hF u hu (P.U.SecK k) (fun s₀ => sp (Fp (Fx s₀))) (fun s₀ => s₀)
    (fun y J hJ => GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _ _ y J hJ)
    (fun i i' y J hJ => by
      have e := GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 k i _ _ _ (hFx i) (hsp _) (hFp _) k i' _ _ _ (hFx i') (hsp _)
        (hFp _) 1 1 rfl y J hJ
      simpa only [pow_one] using e)
  obtain ⟨c₀, rfl⟩ := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ P.D P.A t.G
    P.U.toUnifPre).1 c
  have hF' := fun (U : Type) (i : CommGroup U) g => (@hF U i g).symm
  have hc₀ : c₀ = 1 := fn_ext (V := ⊤) fun y _ => by
    choose J hJ using fun χ : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => exists_chart hL (χ y)
    have hJ' : Good P.U.LG.L y J := hJ
    obtain ⟨s₀, hs₀⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _
      unitK y J hJ'
    obtain ⟨b, hb⟩ := exists_sec hL hF' (pullMulSec s₀ (endK (t.act.act a)) u hu)
    have e₁ := sval_eq_mul_of_id hL (sp (Fp (Fx s₀))) b _ (fun y J hJ => by
      rw [hb _ _ y J hJ, sval_pullMulSec _ _ u hu _ y hJ, Category.id_comp]
      exact hc s₀ y J hJ) unitK y J hJ'
    rw [hb _ _ y J hJ', sval_pullMulSec _ _ u hu _ y hJ', unitK_endK] at e₁
    have e₂ := GlobalTheory.T.value_at_unitSection_genericFibre hLaws V E H t P a N hN hN0 k s₀ _ _ _ (hFx s₀) (hsp _) (hFp _) y J hJ'
    have e₃ : val u unitK y J = val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1)) := by
      have e := val_corr hJ' hn (𝟙 _)
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp, val_pow] at e
      exact e
    have e₄ : gs unitK y ⊤ ((pullback.snd t.G.hom (jK V)).appTop.hom c₀) = gs (𝟙 _) y ⊤ c₀ :=
      (gs_pull unitK (pullback.snd t.G.hom (jK V)) y ⊤ trivial c₀).trans (by rw [unitK_snd])
    rw [e₂, e₃, e₄] at e₁
    rw [gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one]
    refine (hs₀.mul (Units.isUnit (val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))))).mul_right_cancel ?_
    rw [← e₁, _root_.one_mul, mul_comm]
  have hss : s' = sp (Fp (Fx s)) := SecOps.sec_ext (sec_ext_val hL fun y J hJ => by
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, Category.id_comp, hc s y J hJ, hc₀, map_one,
      gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one, _root_.one_mul])
  rw [hss]
  exact hsp _

end GlobalTheory.PullExpansion
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitBallFree

theorem exists_basis_of_coord {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {M : Type*} [AddCommGroup M]
    [Module F M] {J : Type} [Fintype J] [DecidableEq J] (φ : M →ₗ[F] (J → F)) (hφ : Function.Injective φ)
    (B : J → M) (hB : ∀ p, φ (B p) = Pi.single p 1) (q : J → ℚ)
    (ht : ∀ p, ∃ t : F, t ≠ 0 ∧ ((q p : ℚ) : WithTop ℚ) ≤ v t ∧
      ∀ a : F, ((q p : ℚ) : WithTop ℚ) ≤ v a → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t)
    (P : M → Prop) (hP : ∀ s, P s ↔ ∀ p, ((q p : ℚ) : WithTop ℚ) ≤ v (φ s p)) {n : ℕ} (e : Fin n ≃ J) :
    ∃ b : Fin n → M, LinearIndependent F b ∧ (∀ i, P (b i)) ∧
      ∀ s : M, P s ↔ ∃ c : Fin n → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧ s = ∑ i, c i • b i := by
  choose t ht0 htq htd using ht

  have key : ∀ (c : Fin n → F) (p : J), φ (∑ i, c i • (t (e i) • B (e i))) p = c (e.symm p) * t p := by
    intro c p

    simp only [map_sum, map_smul, hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_single (e.symm p)]
    · simp
    · intro i _ hi
      have hne : p ≠ e i := fun h => hi (by rw [h, Equiv.symm_apply_apply])
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨fun i => t (e i) • B (e i), ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrFun (congrArg φ hg) (e i)
    rw [key g (e i), map_zero, Equiv.symm_apply_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_right (ht0 _)
  · intro i
    rw [hP]
    intro p
    rw [map_smul, hB]
    by_cases h : p = e i
    · subst h
      simpa using htq (e i)
    · simp [h]
  · intro s
    constructor
    · intro hs
      rw [hP] at hs
      choose c hc0 hce using fun p => htd p _ (hs p)
      refine ⟨fun i => c (e i), fun i => hc0 _, hφ ?_⟩
      funext p
      rw [key, Equiv.apply_symm_apply, hce p]
    · rintro ⟨c, hc, rfl⟩
      rw [hP]
      intro p
      rw [key, AddValuation.map_mul]
      simpa using add_le_add (hc (e.symm p)) (htq p)

theorem main : GlobalFnsSt → TwistBaseChangeStatement → UUStatement := by
  classical
  intro hG hTw V _ _ _ ϖ hϖ D Q hQ F _ _ v hv hF k hk
  obtain ⟨hinj, e0, he0⟩ := GlobalTheory.exists_representatives_mod_nsmul D.toPre.X k hk
  choose bb hbb using fun i => GlobalTheory.IntegralCoord.main hTw V ϖ hϖ D F v hv k hk (e0 i)
  choose crd crd_spec using fun (s : Fam D.toPre F k) i => ((hbb i).1 (s.s (e0 i))).exists

  have hadd : ∀ (s t : Fam D.toPre F k) i, crd (s + t) i = fun c => crd s i c + crd t i c := by
    intro s t i
    refine ((hbb i).1 _).unique (crd_spec _ i) ?_
    intro j
    rw [add_f, crd_spec s i j, crd_spec t i j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [constBF_eq, constBF_eq, constBF_eq]
    simp only [map_add (f := _), resTop, add_mul]
  have hsmul : ∀ (ζ : F) (s : Fam D.toPre F k) i, crd (ζ • s) i = fun c => ζ * crd s i c := by
    intro ζ s i
    refine ((hbb i).1 _).unique (crd_spec _ i) ?_
    intro j
    rw [smul_f, crd_spec s i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [constBF_eq, constBF_eq]
    simp only [map_mul, resTop, _root_.mul_assoc]
  let φ : Fam D.toPre F k →ₗ[F] (Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) → F) :=
    { toFun := fun s p => crd s p.1 p.2
      map_add' := fun s t => by
        funext p
        simp only [hadd, Pi.add_apply]
      map_smul' := fun ζ s => by
        funext p
        simp only [hsmul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }

  have hφ : Function.Injective φ := by
    intro s t h
    apply fam_ext
    intro χ j
    obtain ⟨i, ⟨m, rfl⟩, -⟩ := he0 χ
    have hag : ∀ j, (s.s (e0 i)).f j = (t.s (e0 i)).f j := by
      intro j
      rw [crd_spec s i j, crd_spec t i j]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show crd s i c = crd t i c from congrFun h (i, c)]
    exact GlobalTheory.fam_eq_on_class_of_eq hG V D.toPre F k s t (e0 i) hag m j

  have hcls : ∀ i (a b : D.toPre.X), e0 i + k • a = e0 i + k • b → a = b :=
    fun i a b h => hinj a b (add_left_cancel h)
  choose B hB1 hB2 using fun p : Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) =>
    ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep hG D.tau_bimult k (e0 p.1) (hcls p.1) (bb p.1 p.2)
  have hB : ∀ p, φ (B p) = Pi.single p 1 := by
    rintro ⟨i, c⟩
    funext ⟨i', c'⟩
    show crd (B (i, c)) i' c' = _
    by_cases hi : i' = i
    · subst hi
      have h1 : crd (B (i', c)) i' = Pi.single c 1 := by
        refine ((hbb i').1 _).unique (crd_spec _ i') ?_
        intro j
        rw [hB1, Finset.sum_eq_single c]
        · rw [constBF_eq]
          simp [resTop]
        · intro b _ hb
          rw [constBF_eq]
          simp [resTop, hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [h1]
      by_cases hc : c' = c
      · subst hc
        simp
      · have hne : (i', c') ≠ (i', c) := fun h => hc (Prod.ext_iff.1 h).2
        simp [hc, hne]
    · have hz : ∀ j, ((B (i, c)).s (e0 i')).f j = 0 := by
        refine hB2 (i, c) (e0 i') fun mu h => hi ?_
        exact ((he0 (e0 i')).unique ⟨0, by simp⟩ ⟨mu, h.symm⟩)
      have h1 : crd (B (i, c)) i' = 0 := by
        refine ((hbb i').1 _).unique (crd_spec _ i') ?_
        intro j
        rw [hz j]
        symm
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [constBF_eq]
        simp [resTop]
      have hne : (i', c') ≠ (i, c) := fun h => hi (Prod.ext_iff.1 h).1
      rw [h1]
      simp [hne]

  have hπ : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)) = ((1 : ℚ) : WithTop ℚ) := by
    have h1 := hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩
    simpa using h1
  let q : Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) → ℚ :=
    fun p => 0 + (Q (e0 p.1) : ℚ) / k
  have ht := fun p => GlobalTheory.ValuedPrincipal.main F v _ hπ hF (q p)

  have hP : ∀ s, NuGe D Q F v k s 0 ↔ ∀ p, ((q p : ℚ) : WithTop ℚ) ≤ v (φ s p) := by
    intro s
    have hS : ∀ χ : D.toPre.X, ∃ α ∈ Finset.univ.image e0, ∃ m0, χ = α + k • m0 := by
      intro χ
      obtain ⟨i, hi, -⟩ := he0 χ
      exact ⟨e0 i, Finset.mem_image_of_mem _ (Finset.mem_univ _), hi⟩
    rw [n1a V ϖ hϖ D Q hQ F v hv k hk _ hS s 0]
    constructor
    · rintro h ⟨i, c⟩
      have h1 := h (e0 i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      rw [(hbb i).2 _ _ (crd_spec s i)] at h1
      exact h1 c
    · intro h α hα
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
      rw [(hbb i).2 _ _ (crd_spec s i)]
      intro c
      exact h (i, c)
  have hr : D.toPre.rank = Module.finrank ℤ D.toPre.X := Nat.add_zero _
  exact exists_basis_of_coord v φ hφ B hB q ht (fun s => NuGe D Q F v k s 0) hP
    ((finCongr (by rw [pow_add, hr])).trans finProdFinEquiv.symm)

end GlobalTheory.UnitBallFree
end
end
