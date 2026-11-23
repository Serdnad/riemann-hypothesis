module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
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
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem nuGe_iff_of_isActOf_of_qkToAkU : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G), Geo.Tor.ExpBijF U.toUnifPre → ∀ (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := V) F)) (p : QkPt D.toPre F k), QkToAkU U.toUnifPre F k p θ.pt → ∀ (n : ℕ), 1 ≤ n → θ.pt ^ n = 1 → LB.Gen.Corr A.L _ _ _ _ (Out.powGen A.A A.L (k : ℤ) θ n) (LB.oneGen A.L) → ∀ (t t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam D.toPre F k), U.ExpandsF F k w t s → U.ExpandsF F k w t' s' → IsActOf A.A A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' r := by
  intro hL hTW V _ _ _ ϖ hϖ D A G _ _ U hB Q hQ F _ _ v hv k hk w hw θ p hp n hn hx hc t t' s s' hs hs' hact r
  obtain ⟨w₀, hw₀, hΦθ⟩ := (hp w hw).2 θ rfl
  obtain ⟨hB₁, hB₂⟩ := hB F k hk w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V (maximalIdeal V) D F k hk p w₀ hw₀
  choose act hact' using fun x : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)) =>
    (VVRank.exists_isTwistPull A.A A.isLB θ.isGen x : ∃ y, IsActOf A.A A.L (k : ℤ) θ x y)
  have hfin : FinOrd D F k p w₀ 1 := by
    refine ⟨n, hn, fun ss ts hss => ?_⟩
    obtain ⟨t₀, ht₀, -⟩ := hB₂ (ss 0)
    have key : ∀ (i : ℕ) (hi : i < n + 1), U.ExpandsF F k w (act^[i] t₀) (ss ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero => exact fun _ => ht₀
      | succ i ih =>
        intro hi
        obtain ⟨s₁, hs₁, -⟩ := hB₁ (act^[i + 1] t₀)
        have h₁ := (hΦ _ _).1 (hΦθ _ _ _ _ (ih (by omega)) hs₁
          (by rw [Function.iterate_succ_apply']; exact hact' _))
        obtain ⟨h₂, h₃⟩ := hss ⟨i, by omega⟩
        have h₄ : ss ⟨i + 1, hi⟩ = s₁ :=
          ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h₃).trans
            ((one_smul F _).trans (((hΦ _ _).1 h₂).trans h₁.symm))
        rw [h₄]; exact hs₁
    have hcyc := thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB (k : ℤ) _ θ n hx hc
      (fun i => act^[i.val] t₀) (fun i => by
        show IsActOf _ _ _ θ (act^[i.val] t₀) (act^[i.val + 1] t₀)
        rw [Function.iterate_succ_apply']; exact hact' _)
    have he : act^[n] t₀ = t₀ := by
      have ext : ∀ a b : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)), (∀ j, a.f j = b.f j) → a = b := by
        rintro ⟨a, _⟩ ⟨b, _⟩ h
        obtain rfl : a = b := funext h
        rfl
      exact ext _ _ hcyc
    have h₅ := key n (Nat.lt_succ_self n)
    rw [he] at h₅
    have h₆ : ss (Fin.last n) = ss 0 := (hB₁ t₀).unique h₅ ht₀
    intro α j
    rw [h₆]
  exact galois_fixed_adelic_matrices_descend hL hTW V ϖ hϖ D Q hQ F v hv k hk p w₀ hw₀ 1 one_ne_zero hfin s s' s'
    (hΦθ t t' s s' hs hs' hact) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 (one_smul F _).symm) r

end GlobalTheory
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpandsFracLinear

open GlobalTheory.ExpandsLinear

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k n : ℕ) (c : Fin n → FractionRing R) (s : Fin n → U.SecK k) (E : Fin n → Fam D.toPre (FractionRing R) k) (s₀ : U.SecK k), (∀ l, U.Expands k (s l) (E l)) → (∀ jj, s₀.f jj = ∑ l, resTop _ (scal (pullback.snd G.hom (jK R)) (c l)) * (s l).f jj) → U.Expands k s₀ (∑ l, c l • E l) := by
  intro R _ _ I D A G _ _ U k n c s E s₀ hE hs
  simp only [UnifPre.Expands] at hE ⊢
  choose r hr σ f h1 h2 h3 using hE
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset (Fin n))
    (fun l => c l / algebraMap R (FractionRing R) (r l))
  choose a ha using fun l => hb l (Finset.mem_univ l)
  have hc : ∀ l, algebraMap R (FractionRing R) (a l) * algebraMap R (FractionRing R) (r l) =
      algebraMap R (FractionRing R) (b : R) * c l := by
    intro l
    have hrl : algebraMap R (FractionRing R) (r l) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
      exact fun h => hr l (IsFractionRing.injective R (FractionRing R) h)
    rw [ha l, Algebra.smul_def]
    field_simp
  refine ⟨b, nonZeroDivisors.ne_zero b.2, secComb (fun l => scal G.hom (a l)) σ,
    fun α => secComb (fun l => scal D.toPre.P.A.hom (a l)) (fun l => f l α), ?_, ?_, ?_⟩
  · exact secScal_comb (algebraMap R (FractionRing R)) U.LG.L _ _ _ _ (pullback.fst G.hom (jK R))
      (pullback.snd G.hom (jK R)) _ G.hom rfl pullback.condition s σ r a b c hc h1 s₀ hs
  · intro α
    refine secScal_comb (algebraMap R (FractionRing R)) D.toPre.P.L _ _ _ _ (D.toPre.prB (FractionRing R)).left
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_ ?_ (fun l => (E l).s α)
      (fun l => f l α) r a b c hc (fun l => h2 l α) _ ?_
    · have hh := (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
      unfold DegPre.BF TF at *
      rw [hh]
      congr 1
      show jFK (FractionRing R) ≫ jK R = _
      unfold jFK jK
      rw [← Spec.map_comp]
      rfl
    · exact Over.w (D.toPre.prB (FractionRing R))
    · intro j
      rw [fam_sum_f]
      simp only [smul_f]
      rfl
  · intro e
    exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun l => h3 l e) (fun j => rfl) (fun α j => rfl)

end GlobalTheory.ExpandsFracLinear
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullGenG

theorem hasGen_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) :
    HasGen Lr.L (lf (Finsupp.single (1 : G ⟶ G) 1)) := by
  have h0 := (HasGen.of_gen (L := Lr.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) Lr.rig Lr.rigGen).pull G.hom
  have e1 : (1 : G ⟶ G).left = G.hom ≫ eSec G := rfl
  convert h0 using 1
  rw [lf_single, e1]
  simp [fsum, Finsupp.mapDomain_single]

theorem hasGen_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (cub : CubicalStr G Lr)
    {O : Type} [CommRing O] [StarRing O] (ra : RingAct G O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (hadj : Geo.Tor.LBIso (cubeLB G ![fst G G ≫ ra.act a, snd G G] Lr.L)
      (cubeLB G ![fst G G, snd G G ≫ ra.act (star a)] Lr.L))
    (hprim : Geo.Tor.LBIso Lr.L (cubeLB G ![𝟙 G, ra.act w0] Lr.L)) (k : ℕ) :
    HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, (ra.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := by
  have := ra.hom w0
  obtain ⟨uR, huR⟩ := GlobalTheory.NormRos.exists_gen_rosati Lr.isLB (ra.act a) (ra.act (star a)) hadj
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim S G Lr (ra.act w0) hprim
  have hP : HasGen Lr.L (fsum (GlobalTheory.JetSer.primφ (ra.act w0)) GlobalTheory.JetSer.primε) := HasGen.of_gen ρ hρ
  have h1 := hasGen_one Lr
  obtain ⟨uΨ, huΨ⟩ := HasGen.gen Lr.isLB (h1.sub hP) (K' := Fin 4)
    ![(padd G (𝟙 _) (ra.act w0)).left, 𝟙 G.left, (ra.act w0).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      unfold GlobalTheory.JetSer.primφ GlobalTheory.JetSer.primε
      have e1 : toUnit G ≫ η[G] = (1 : G ⟶ G) := rfl
      rw [padd_eq_mul, e1, lf_single]
      classical
      ext x
      simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
      split_ifs <;> omega)
  have hM := hasGen_pullMul ra w0 a N hN uΨ huΨ uR huR cub.t cub.isGen
  have h2 := (hM.zsmul (-(k : ℤ))).add (h1.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  convert h2 using 1
  classical
  simp only [lf_add, lf_sub, lf_smul, lf_single]
  ext x
  simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
  split_ifs <;> ring

end GlobalTheory.PullGenG
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowTorus

section Box

variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

private theorem units_map_stalkMap_gm_eq_gm_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (s : Y ⟶ X) (z : Z) (U : X.Opens)
    (a : Γ(X, U)ˣ) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (gm s (r z) U a) =
      gm (r ≫ s) z U a := by
  unfold gm
  by_cases h : s (r z) ∈ U
  · have h' : (r ≫ s) z ∈ U := h
    rw [dite_eq_left h, dite_eq_left h']
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    unfold pullU
    simp only [Units.coe_map, MonoidHom.coe_coe, MonoidHom.comp_apply]
    have key := congrArg (fun φ => φ.hom ((s.app U).hom a.val)) (Scheme.Hom.germ_stalkMap r (s ⁻¹ᵁ U) z h)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
    exact key
  · have h' : ¬ (r ≫ s) z ∈ U := h
    rw [dite_eq_right h, dite_eq_right h']
    simp

private theorem units_map_stalkMap_bw_eq_bw_comp {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (r : Z ⟶ Y) (ψ : Y ⟶ X') (z : Z) (jN : Fin j → M.ι) (k : M'.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (bw w ψ (r z) jN k) =
      bw w (r ≫ ψ) z jN k := by
  unfold bw
  exact units_map_stalkMap_gm_eq_gm_comp r ψ z _ _

private theorem units_map_stalkMap_val_eq_val_comp {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₁ ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (s : Y ⟶ Y₁) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z)
        (val t s (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ s) z J := by
  rw [val_of t (r ≫ s) z J (fun k => J (r ≫ s ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t s (r z) _ (fun k => J (r ≫ s ≫ φ k)) (fun k => rfl)]
  exact units_map_stalkMap_gm_eq_gm_comp r s z _ _

theorem box_gen_val_along (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (r ≫ φ' a) y (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r y J' =
      ∏ i, val (t i) (r ≫ ρ i) y J := by
  have E := box_gen_val w hψ t' t H (r y) (J := fun ψ => J (r ≫ ψ)) (J' := fun ψ => J' (r ≫ ψ))
    (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ' (r ≫ ψ))
  have E2 := congrArg (Units.map ((r.stalkMap y).hom : Y.presheaf.stalk (r y) →* Z.presheaf.stalk y)) E
  rw [map_mul, map_prod, map_prod] at E2
  simp only [map_zpow, units_map_stalkMap_bw_eq_bw_comp, units_map_stalkMap_val_eq_val_comp, Category.comp_id] at E2
  simp only [Category.assoc]
  exact E2

end Box

section Coord

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem val_on_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) {z : Z.left}
    {J : (Z.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (τ : Z ⟶ splitTorus _ D.X) :
    val (g.t χ) (τ ≫ g.i).left z J = gm τ.left z ⊤ (charUnit _ D.X χ) := by
  have h1 := GlobalTheory.TorusCoord.val_torus g χ hJ τ 1
  rw [_root_.mul_one] at h1
  rw [h1, GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

theorem prod_on_torus (χ : D.X) {V : Type} [CommGroup V]
    (f : ((splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left ⟶ D.P.A.left) → V) :
    ∏ k, f (g.i.left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have k0 : g.i ≫ g.q = (1 : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ thickObj R I e G) ≫ g.q := by
    have := g.q_hom
    rw [g.isKernel.w, MonObj.one_comp]
    rfl
  have k1 : (Over.map (thick R I e)).map g.i ≫ g.pG = 1 := by
    have h := GlobalTheory.TorusCoord.im_congr g k0
    rw [GlobalTheory.TorusCoord.im_one] at h
    exact h
  have e0 : g.i.left ≫ (padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ)).left =
      g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    have hp : padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) =
        g.pG * (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) := rfl
    rw [hp, MonObj.comp_mul, k1, _root_.one_mul]
  have e2 : g.i.left ≫ g.pG.left = g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    rw [k1, ← Category.assoc, toUnit_unique ((Over.map (thick R I e)).map g.i ≫ toUnit _) (toUnit _)]
    rfl
  simp only [Fin.prod_univ_four, Oinvε, DegPre.Oφ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  erw [e0, e2]
  group

end Coord

theorem gm_char_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have h := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
  rw [ofAdd_zero, map_one, Units.val_one] at h
  have h2 : charUnit S X 0 = 1 := by
    ext
    rw [Units.val_one, h]
    simp
  rw [h2, map_one]

theorem torus_ext {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ τ' : Z ⟶ splitTorus S X)
    (h : ∀ χ z, gm τ.left z ⊤ (charUnit S X χ) = gm τ'.left z ⊤ (charUnit S X χ)) : τ = τ' := by
  apply (splitTorusPointsEquiv S X Z).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val]
  exact GlobalTheory.TorusCoord.appTop_eq_of_gm _ _ _ (h x)

section Pow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

theorem exists_factor (P : UnifPowOf3 pD pA pG U' U) (e : ℕ) (i : Fin j) :
    ∃ h : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      h ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) := by
  have hk := (U.gt e).isKernel
  have hη : (η : 𝟙_ _ ⟶ thickObj R I e D'.toPre.P.A) ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = η := by
    have hm := pD.pw.hom i
    change (_ ≫ _) ≫ _ = _ ≫ _
    rw [Category.assoc, ← Functor.map_comp, hm.one_hom]
  have hc : ((U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i)) ≫ (U.gt e).q =
      toUnit _ ≫ η := by
    rw [Category.assoc, ← P.q_pr e i, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc, hη]
  exact ⟨hk.lift _ _ hc, hk.lift_fst _ _ hc⟩



theorem char_prod (P : UnifPowOf3 pD pA pG U' U) (e : ℕ)
    (h : Fin j → (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X))
    (hh : ∀ i, h i ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i))
    (x : D'.toPre.X) (z : (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X).left) :
    gm (𝟙 _) z ⊤ (charUnit _ D'.toPre.X x) = ∏ i, gm (h i).left z ⊤ (charUnit _ D.toPre.X (pD.xe x i)) := by
  obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨J', hJ', -⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨hψ, H⟩ := P.t_pr e x
  have B := box_gen_val_along pD.w hψ ((U'.gt e).t x) (fun i => (U.gt e).t (pD.xe x i)) H
    (U'.gt e).i.left z hJ hJ'
  have hP := prod_on_torus (U'.gt e) x (fun ψ => bw pD.w ψ z (fun i => J (ψ ≫ (pD.pw.pr i).left)) (J' ψ))
  rw [hP, _root_.one_mul] at B
  have L1 := val_on_torus (U'.gt e) x hJ' (𝟙 _)
  rw [Category.id_comp] at L1
  rw [L1] at B
  refine B.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← val_on_torus (U.gt e) (pD.xe x i) hJ (h i), hh i]
  rfl

end Pow

theorem torus_isPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (e : ℕ), ∃ pT : IsPowGrp (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X) (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X) j, (∀ i, (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) = pT.pr i ≫ (U.gt e).i) ∧ ∀ (i : Fin j) (χ : D.toPre.X), res (fun x _ => show (pT.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (pT.pr i).left ⊤ (charUnit _ D.toPre.X χ)) = charUnit _ D'.toPre.X (pD.xe.symm (Pi.single i χ)) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P e
  obtain ⟨p, hp⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X
    D'.toPre.X j pD.xe
  choose h hh using fun i => exists_factor P e i
  refine ⟨p, fun i => ?_, hp⟩
  have key : h i = p.pr i := by
    apply torus_ext
    intro χ z
    have c := char_prod P e h hh (pD.xe.symm (Pi.single i χ)) z
    rw [Finset.prod_eq_single i] at c
    · rw [AddEquiv.apply_symm_apply, Pi.single_eq_same] at c
      rw [← c]
      have hz := (gm_rp₁ (p.pr i).left z ⊤ ⊤ _ trivial (charUnit _ D.toPre.X χ)).symm.trans
        (congrArg (gm (𝟙 _) z ⊤) (hp i χ))
      exact hz.symm
    · intro b _ hb
      rw [AddEquiv.apply_symm_apply, Pi.single_eq_of_ne hb, gm_char_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hh i, key]

end GlobalTheory.PowTorus
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.TauBalBox

private theorem hom_ext_of_isPowGrp_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) {T : Over S} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b := by
  apply p.lim.hom_ext
  rintro ⟨i⟩
  first
  | exact h i
  | simpa using h i

theorem exists_pow_oAct : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ oa : D.OAct O, ∃ oa' : D'.OAct O, ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a := by
  intro hG R _ _ j D D' pD O _ _ _ _ hxe oa
  obtain ⟨⟨oB, hros⟩, hc, htau⟩ := oa
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  obtain ⟨r', hr'⟩ := (GlobalTheory.exists_powAct _ D'.P.A D.P.A j pD.pw).1 O oB
  have hros' : ∀ a : O, RosatiAdj D'.P.A D'.P.L (r'.act a) (r'.act (star a)) := fun a =>
    GlobalTheory.rosatiAdj_pow _ D'.P.A D.P.A j pD.pw D.P.L D'.P.L D.P.isLB D'.P.isLB ⟨pD.w, pD.w_gen⟩
      (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a)) (hr' a) (hr' (star a)) (hros a)
  have hc' : ∀ (a : O) (y : D'.X), D'.c (a • y) = D'.c y ≫ r'.act a := by
    intro a y
    apply hom_ext_of_isPowGrp_pr pD.pw
    intro i
    rw [pD.c_pr, Category.assoc, hr' a i, ← Category.assoc, pD.c_pr, hxe, Pi.smul_apply, hc]
  have htau' : ∀ a : O, D'.TauBal (r'.act a) (r'.act (star a)) (fun y => a • y) fun y => star a • y := by
    intro a
    haveI := oB.hom a
    haveI := oB.hom (star a)
    haveI := r'.hom a
    haveI := r'.hom (star a)
    exact tauBal_pow hG R j D D' pD (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a))
      inferInstance inferInstance inferInstance inferInstance (hr' a) (hr' (star a)) (hros a)
      (fun y => a • y) (fun y => star a • y) (fun y => a • y) (fun y => star a • y)
      (fun x i => by simp only [hxe, Pi.smul_apply]) (fun x i => by simp only [hxe, Pi.smul_apply])
      (hc a) (hc (star a)) (htau a)
  exact ⟨⟨⟨r', hros'⟩, hc', htau'⟩, hr'⟩

end GlobalTheory.TauBalBox
end
