module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CompAutEqOfSerreBaseChange
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem exists_chart_lbPow (u : HolUnif A L g) (hL : L.IsLB) (n : ℕ) (z : Fin g → ℂ) :
    ∃ k : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k := by
  obtain ⟨i, hi⟩ := SymmetricSemicharacter.exists_chart u SymmetricSemicharacter.valueRules hL z
  refine ⟨fun _ => i, ?_⟩
  rwa [Cartier.lbPow_U]

theorem fr_pow_ne_zero (u : HolUnif A L g) (n : ℕ) {z : Fin g → ℂ} {k : (lbPow L n).ι}
    (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k) : u.fr (k PUnit.unit) z ^ n ≠ 0 :=
  pow_ne_zero n (u.fr_ne _ z (Cartier.lbPow_U L n k ▸ hk))

theorem le_preimage_nonzeroLocus_iff (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s : (lbPow L n).Sec}
    {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (z : Fin g → ℂ) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus s ↔ θ z ≠ 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem _ _).1 h)
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hs k z (top_le_preimage_of_valAt'_ne_zero _ h1)] at h1
    exact left_ne_zero_of_mul h1
  · intro h
    obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
    refine top_le_preimage_mono _ (le_iSup (fun k => A.left.basicOpen (s.f k)) k) ?_
    rw [top_le_preimage_basicOpen_iff, hs k z hk]
    exact mul_ne_zero h (fr_pow_ne_zero u n hk)

theorem valAt'_eq_div_of_mul (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s s' : (lbPow L n).Sec}
    {θ θ' : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ') (r : Γ(A.left, Out.nonzeroLocus s))
    (hr : ∀ k, resG _ (inf_le_right : Out.nonzeroLocus s ⊓ (lbPow L n).U k ≤ _) (s'.f k) =
      resG _ inf_le_left r * resG _ inf_le_right (s.f k)) {z : Fin g → ℂ} (hz : θ z ≠ 0) :
    valAt' (u.ex z).left _ r = θ' z / θ z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
  have hW := (top_le_preimage_inf _ _ _).2 ⟨(le_preimage_nonzeroLocus_iff u hL hs z).2 hz, hk⟩
  have h := congrArg (valAt' (u.ex z).left _) (hr k)
  rw [valAt'_mul, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, hs k z hk, hs' k z hk,
    ← _root_.mul_assoc] at h
  rw [mul_right_cancel₀ (fr_pow_ne_zero u n hk) h, mul_div_cancel_right₀ _ hz]

theorem exists_regular_quotients (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {κ : Type*} {s : κ → (lbPow L n).Sec}
    {θ : κ → (Fin g → ℂ) → ℂ} (hs : ∀ j, u.IsFnPow n (s j) (θ j)) (i : κ) {z₀ : Fin g → ℂ} (h0 : θ i z₀ ≠ 0) :
    ∃ (U : A.left.Opens) (ρ : κ → Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → θ i z ≠ 0 ∧ ∀ j, valAt' (u.ex z).left U (ρ j) = θ j z / θ i z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z₀
  have hle := A.left.basicOpen_le ((s i).f k)
  obtain ⟨v, hv⟩ : IsUnit (resG A.left hle ((s i).f k)) := RingedSpace.isUnit_res_basicOpen _ _
  refine ⟨A.left.basicOpen ((s i).f k), fun j => resG A.left hle ((s j).f k) * (v⁻¹).val, ?_, fun z hz => ?_⟩
  · rw [top_le_preimage_basicOpen_iff, hs i k z₀ hk]
    exact mul_ne_zero h0 (fr_pow_ne_zero u n hk)
  · have hk' := top_le_preimage_mono _ hle hz
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 hz
    rw [hs i k z hk'] at h1
    refine ⟨left_ne_zero_of_mul h1, fun j => ?_⟩
    rw [valAt'_mul, valAt'_units_inv _ hz, hv, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, hs i k z hk', hs j k z hk',
      ← div_eq_mul_inv, mul_div_mul_right _ _ (right_ne_zero_of_mul h1)]

theorem isMonHom_of_lift {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') [Smooth A.hom] (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (f : A ⟶ A')
    (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f) : IsMonHom f := by
  have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom inferInstance
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  have h0' : u'.ex 0 = η[A'] := by
    rw [(u'.ker 0).2 u'.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨?_, ?_⟩
  · rw [← h0, ← hf, map_zero, h0']
  · have hft : LocallyOfFiniteType (A ⊗ A).hom := by
      change LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    refine TorusEnd.hom_ext_of_points (existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) A' (A ⊗ A)
      (isReduced_tensorObj_complex A A hr hr inferInstance inferInstance) hft) fun y => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (y ≫ fst A A)
    obtain ⟨w, hw⟩ := u.ex_onto (y ≫ snd A A)
    have hy : y = lift (u.ex z) (u.ex w) := by
      ext1 <;> simp [hz, hw]
    rw [hy, ← Category.assoc, ← Hom.mul_def, ← u.ex_add, ← hf, map_add (f := _), u'.ex_add, Hom.mul_def, ← Category.assoc,
      lift_map, ← hf, ← hf]

theorem exists_isMonHom_of_complementary (hamp : Out.AmpleSt) (P P' : Out.PolAV (Sp ℂ)) {g g' : ℕ}
    (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g') {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (hsec : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ)
    (hfn : ∀ (k : ℕ) s, ∃ θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (d : ℕ)
    (hd : ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' 4 θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  have hsm := P.isAb.smooth
  have hr : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom hsm
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ P.A) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A) := fun y => u'.ex (F (Function.surjInv u.ex_onto y))
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (F z) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (F z) ⟨_, hF _ h1⟩
    rwa [← map_add, add_sub_cancel] at this
  obtain ⟨m, s, hcov, hD⟩ := veryAmple_lbPow hamp ℂ P' 4 le_rfl
  choose θ hθ hθs using fun j => hfn 4 (s j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P'.A P.A hr inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (F z₀)).left _ hcov
    obtain ⟨haff, r, hr, hgen⟩ := hD i
    have hmem := le_preimage_nonzeroLocus_iff u' P'.isLB (hθs i)
    obtain ⟨G, hG0, hG⟩ := hd z₀
    choose t ht using fun j => hsec d _ (hG _ (hθ j))
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u P.isLB ht i (mul_ne_zero ((hmem _).1 hi) hG0)
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun ψ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen ψ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P'.isLB (hθs i) (hθs j) (r j) (hr j) h1, mul_div_mul_right _ _ h2]
  have hfe : ∀ z, u'.ex (F z) = u.ex z ≫ f := fun z => by rw [hf, hΦ]
  exact ⟨f, isMonHom_of_lift u u' F f hfe, hfe⟩

end GlobalTheory.LatticeHom
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TripleDescent

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lift_left_fst {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (fst X Y).left = a.left :=
  congrArg (fun q => q.left) (lift_fst a b)

theorem lift_left_snd {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (snd X Y).left = b.left :=
  congrArg (fun q => q.left) (lift_snd a b)

theorem isPullback_tensor {X Y : Over S} {X' Y' : Over S'} {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left}
    (ha : IsPullback a X'.hom X.hom f) (hb : IsPullback b Y'.hom Y.hom f) (c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left)
    (c₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (c₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have p : IsPullback (snd X Y).left (fst X Y).left Y.hom X.hom := (IsPullback.of_hasPullback X.hom Y.hom).flip
  have p' : IsPullback (snd X' Y').left (fst X' Y').left Y'.hom X'.hom :=
    (IsPullback.of_hasPullback X'.hom Y'.hom).flip
  have q := p'.paste_horiz hb
  rw [← c₂, ← ha.w] at q
  have r := (IsPullback.of_right q c₁ p).paste_vert ha
  rwa [Over.w, Over.w] at r

variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem lbIso_cubeLB_pull (h : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso (cubeLB G' x' L') ((cubeLB G x L).pull U.left) := by
  obtain ⟨w, hw⟩ := hw
  exact (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down)

theorem exists_gen_cubeLB_pull (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (t : (cubeLB G' x' L').Gen)
    (ht : t.IsGen) : ∃ t : ((cubeLB G x L).pull U.left).Gen, t.IsGen := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' t ht
  exact gen_chartPull (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down) c hc

end GlobalTheory.TripleDescent


open GlobalTheory.TripleDescent in
theorem GlobalTheory.exists_triple_of_fieldExtension : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (τ : SAB H (Sp K)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : τ.G.left ⟶ A₀.left) (L₀ : LB A₀.left) (r : OAct (𝓞 E) A₀), IsAbelianScheme A₀ → IsGrpPullback τ.G A₀ (spMap i) φ → L₀.IsLB → LBIso τ.PP.L (L₀.pull φ) → (∀ c, (τ.act.act c).left ≫ φ = φ ≫ (r.act c).left) → ∃ (τ₀ : SAB H (Sp K₀)) (e : τ₀.G ≅ A₀), IsMonHom e.hom ∧ LBIso τ₀.PP.L (L₀.pull e.hom.left) ∧ ∀ c, τ₀.act.act c ≫ e.hom = e.hom ≫ r.act c := by
  intro hLaws E _ _ _ H K₀ K _ _ i τ A₀ _ φ L₀ r hA h hL₀ hw hact
  have := hA.comm
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  have A₃ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ _ hA A₂
  have lb : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ τ.G) a,
      pushPt h.1.w (x ≫ τ.act.act a) = pushPt h.1.w x ≫ r.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have hP := τ.PP.isLB
  let U₁ := pushPt h.1.w (𝟙 τ.G)
  have e₁ : U₁.left = φ := Category.id_comp _
  let U₂ := lift (pushPt h.1.w (fst τ.G τ.G)) (pushPt h.1.w (snd τ.G τ.G))
  let U₃ := lift (pushPt h.1.w (x3 τ.G 0)) (lift (pushPt h.1.w (x3 τ.G 1)) (pushPt h.1.w (x3 τ.G 2)))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst τ.G τ.G).left ≫ φ := lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd τ.G τ.G).left ≫ φ := lift_left_snd _ _
  have P₂ : IsPullback U₂.left (τ.G ⊗ τ.G).hom (A₀ ⊗ A₀).hom (spMap i) := isPullback_tensor h.1 h.1 _ u₁ u₂
  have P₃ : IsPullback U₃.left (τ.G ⊗ τ.G ⊗ τ.G).hom (A₀ ⊗ A₀ ⊗ A₀).hom (spMap i) := by
    refine isPullback_tensor h.1 P₂ _ (lift_left_fst _ _) ?_
    refine (lift_left_snd _ _).trans ?_
    apply pullback.hom_ext
    · refine (lift_left_fst _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₁).trans (Category.assoc _ _ _).symm)
    · refine (lift_left_snd _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₂).trans (Category.assoc _ _ _).symm)
  have D₁ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom _ _ hA.smooth hA.proper hA.geomConnected h.1
  have D₂ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂
  have D₃ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀ ⊗ A₀).hom _ _ A₃.smooth A₃.proper A₃.geomConnected P₃
  have hT : ∃ t : LB.Gen (Theta A₀ L₀), t.IsGen := D₃.1 _ (lb _ hL₀)
    (exists_gen_cubeLB_pull h hL₀ hP hw (x3 τ.G) (x3 A₀) U₃ (fun j => by fin_cases j <;> simp [x3, U₃])
      τ.cub.t τ.cub.isGen)
  have ha : ∀ a, LBIso (cubeLB A₀ ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] L₀)
      (cubeLB A₀ ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] L₀) := fun a => by
    have k₁ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G ≫ τ.act.act a, snd τ.G τ.G]
      ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] U₂ (fun j => by
        fin_cases j
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂])
    have k₂ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G, snd τ.G τ.G ≫ τ.act.act (H.bar a)]
      ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] U₂ (fun j => by
        fin_cases j
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂]))
    exact D₂.2 _ _ (lb _ hL₀) (lb _ hL₀) (LBIso.trans (pull_isLB (lb _ hL₀) _) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _)
      k₁.symm (LBIso.trans (by exact lb _ hP) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) (τ.adj a) k₂))
  have hp : LBIso L₀ (cubeLB A₀ ![𝟙 A₀, r.act H.w0] L₀) := by
    have k := lbIso_cubeLB_pull h hw ![𝟙 τ.G, τ.act.act H.w0] ![𝟙 A₀, r.act H.w0] U₁ (fun j => by
      fin_cases j
      · simp [U₁]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _))
    rw [e₁] at k
    exact D₁.2 _ _ hL₀ (lb _ hL₀) (LBIso.trans (pull_isLB hL₀ _) hP (pull_isLB (lb _ hL₀) _)
      hw.symm (LBIso.trans hP (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) τ.prim k))
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation hLaws.globalFns E H _ A₀ r L₀ hA hL₀ hT ha
  refine ⟨⟨A₀, GlobalTheory.isSemiAbelian_of_isAbelianScheme A₀ hA, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 A₀)), ?_, fun c => (Category.comp_id _).trans (Category.id_comp _).symm⟩
  exact (LBIso.trans PP.isLB (lb _ hL₀) hL₀ iso hp.symm).chartPull (chartPullId _) (chartPullPull L₀ _ (𝟙 _) rfl)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem eq_id_of_forall_geometric_fibre (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (σ : A ⟶ A) (h0 : η[A] ≫ σ = η[A])
    (hσ : ∀ t : S, ∃ (S' X : Scheme.{0}) (f : S' ⟶ S) (g : X ⟶ A.left) (q : X ⟶ S') (y : S'),
      f y = t ∧ IsPullback g q A.hom f ∧ g ≫ σ.left = g) : σ = 𝟙 A := by
  have := hA.proper
  let u : A ⟶ A := σ * (𝟙 A)⁻¹
  have hu : ∀ {T : Over S} (x : T ⟶ A), x ≫ σ = x → x ≫ u = 1 := fun x hx => by
    simp only [u, MonObj.comp_mul, GrpObj.comp_inv, hx, Category.comp_id, mul_inv_cancel]
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hfib : ∀ (t : S) (x : A.left), A.hom x = t →
      u.left x = (η[A] : 𝟙_ (Over S) ⟶ A).left t := by
    intro t x hx
    obtain ⟨S', X, f, g, q, y, hy, hg, e⟩ := hσ t
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hg x y (hx.trans hy.symm)
    let x₀ : Over.mk (g ≫ A.hom) ⟶ A := Over.homMk g rfl
    have h₀ : g ≫ u.left = (g ≫ A.hom) ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left :=
      congrArg (fun q => q.left) (hu x₀ (Over.OverMorphism.ext e))
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
  have key : u.left = A.hom ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ u.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨V, hV, e⟩ := local_rigidity _ _ _ A.hom _ u.left hη inferInstance
      (surjective_app_of_isAbelianScheme hG A hA) (A.hom x) _ (hfib _)
    exact ⟨A.hom ⁻¹ᵁ V, hV, e⟩
  have h₁ : u = toUnit A ≫ η[A] ≫ u := Over.OverMorphism.ext key
  rw [hu η[A] h0, MonObj.comp_one] at h₁
  exact mul_inv_eq_one.1 h₁

theorem serre_any_base (hL : Out.Laws) {S : Scheme.{0}} (P : Out.PolAV S) (M : ℕ) (hM : 3 ≤ M)
    (σ : P.A ≅ P.A) (hσ : IsMonHom σ.hom)
    (hloc : ∀ p : S, ∃ V : S.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]).pull
        (P.A.hom ⁻¹ᵁ V).ι), c.IsGen)
    (hfix : ∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) : σ.hom = 𝟙 P.A := by
  refine eq_id_of_forall_geometric_fibre hL.globalFns P.A P.isAb σ.hom (IsMonHom.one_hom σ.hom)
    fun t => ?_
  obtain ⟨V, hV, c, hc⟩ := hloc t
  have hf : ∀ y, S.fromSpecResidueField t y = t := Scheme.fromSpecResidueField_apply t
  obtain ⟨X, g, q, hg, e⟩ := comp_aut_eq_of_serre_baseChange hL.polBaseChange
    (S.fromSpecResidueField t) P M
    (fun P' σ' h' ⟨c', hc'⟩ hx => hL.serre _ P' M hM σ' h' (fun _ => ⟨⊤, trivial,
      gen_chartPull (chartPullPull _ _ _ rfl) c' hc'⟩) hx)
    σ hσ V (fun y => by rw [hf]; exact hV) c hc hfix
  exact ⟨_, X, _, g, q, (default : PrimeSpectrum (S.residueField t)), hf _, hg, e⟩

theorem fix_torsion_of_forall_geometric {S : Scheme.{0}} (A : Over S) [GrpObj A] (n : ℕ)
    [Etale (Out.mulA A n).left] (σ : A ⟶ A) [IsMonHom σ]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A),
      x ^ n = 1 → x ≫ σ = x) (T : Over S) (x : T ⟶ A) (hx : x ^ n = 1) : x ≫ σ = x := by
  have e : ∀ y : T ⟶ A, y ≫ Out.mulA A n = y ^ n := fun y => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  have hx' : (x ≫ σ) ^ n = 1 := by
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA A n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, hx, hx']) (Set.eq_univ_of_forall fun z => ?_)
  let K : Type := AlgebraicClosure (T.left.residueField z)
  let j : Sp K ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField z) K)) ≫
      T.left.fromSpecResidueField z
  have hj : ∀ p, j p = z := fun p =>
    (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply z _)
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j rfl
  have h₁ := h K (j ≫ T.hom) (j' ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  replace h₁ := (Category.assoc _ _ _).symm.trans h₁
  exact range_subset_range_equalizer_ι j (congrArg (fun q => q.left) h₁)
    ⟨(default : PrimeSpectrum K), hj _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem obj_aut_fix_geometric_torsion {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o : Obj D l b s) (θ : o.t.G ≅ o.t.G) [IsMonHom θ.hom]
    (hact : ∀ a, o.t.act.act a ≫ θ.hom = θ.hom ≫ o.t.act.act a)
    (hL : LBIso o.t.PP.L (o.t.PP.L.pull θ.hom.left)) (heta : ∀ a, o.eta a ≫ θ.hom = o.eta a)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ o.t.G)
    (hy : y ^ l.M = 1) : y ≫ θ.hom = y := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  refine ObjRigid.fix_torsion l I (IsMonHom.monoidHom θ.hom (Over.mk x)) (fun a z => ?_)
    (fun z z' c c' h h' => ?_) (fun a ha => ?_) y hy
  · show (z ≫ _) ≫ θ.hom = (z ≫ θ.hom) ≫ _
    rw [Category.assoc, hact, Category.assoc]
  · have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (Sp k))
    exact H1.unitOn_injective
      (ObjRigid.weil_eq_of_iso (T := Over.mk x) o.t.PP.isLB θ w hw _ z z' _ _ h h')
  · show _ ≫ θ.hom = _
    rw [← hI a ha, Category.assoc, heta]

theorem obj_rigid_of_pol : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f m m' heta
  obtain ⟨hA, hd, hr, hs⟩ := hpol E H D l B' b' S' s' o'
  obtain ⟨θ, hθ, hφ, hact, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have hη : ∀ a, o'.eta a ≫ θ.hom = o'.eta a := fun a => by
    obtain ⟨σ, h₁, h₂⟩ := heta a
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ).trans (h₁.trans h₂.symm)
    · rw [Over.w, Over.w]
  let P : Out.PolAV S' :=
    { A := o'.t.G, g := _, smoothDim := hd, L := o'.t.PP.L, isLB := o'.t.PP.isLB,
      ample := o'.ample, ktriv := o'.ktriv, isAb := hA, rigid := hr, sym := hs }
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMu : IsUnit (l.M : Γ(S', ⊤)) := by
    simpa using (b'.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ s'.appTop).hom
  have := hA.smooth
  have : Etale (Out.mulA o'.t.G l.M).left := GrpTangent.etale_id_pow o'.t.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL P l.M l.three_le θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric o'.t.G l.M θ.hom
        (obj_aut_fix_geometric_torsion o' θ hact ⟨w, hw⟩ hη))
    obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (o'.t.G.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut o'.t.PP.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← hφ, h, Over.id_left, Category.id_comp]

end GlobalTheory
end
