module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Mathlib.RingTheory.Henselian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfSmallTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3346
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTFirstOrderIso

theorem isGrpPullback_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := by change IsIso ((Over.forget S).map e.hom); infer_instance
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x ≫ e.hom := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y ≫ e.hom := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [j]

theorem gd : GlobalTheory.Published.GrothendieckDeformation :=
  GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting

theorem liftHom_eps (k : Type) [Field k] :
    GlobalTheory.Published.GrothendieckMessing.LiftHom (epsDP k) (TrivSqZeroExt.fstHom k k k).toRingHom :=
  (gd.at_dualNumber k).2.2

theorem henselian_of_artinian (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
    HenselianLocalRing C := by
  obtain ⟨n, hn⟩ : IsNilpotent (IsLocalRing.maximalIdeal C) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  have hz : ∀ k, n ≤ k → (IsLocalRing.maximalIdeal C) ^ k = ⊥ := fun k hk => by
    rw [← Nat.add_sub_cancel' hk, pow_add, hn, zero_mul]; rfl
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal C) C := by
    refine { haus' := fun x hx => ?_, prec' := fun f hf => ⟨f n, fun k => ?_⟩ }
    · have := SModEq.zero.1 (hx n)
      rw [hz n le_rfl, Submodule.bot_smul] at this
      simpa using this
    · rcases le_total k n with h | h
      · exact hf h
      · have e := SModEq.sub_mem.1 (hf h)
        rw [hz n le_rfl, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at e
        rw [e]
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

instance isArtinianRing_dualNumber (k : Type) [Field k] : IsArtinianRing (DualNumber k) := by
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  exact IsArtinianRing.of_finite k (DualNumber k)

end GlobalTheory.HTFirstOrderIso

namespace GlobalTheory.HTFirstOrderIso

theorem eta_pow {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
    {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GlobalTheory.UPel.HT.Obj b N s) (a : D.La) (n : ℕ) :
    o.eta (n • a) = o.eta a ^ n := by
  have h0 : o.eta 0 = 1 := by
    have := o.eta_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem comp_pow {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (ρ : T' ⟶ T) (x : T ⟶ G) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem objMap_of_filLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (g : HdR o₀.A → HdR o₀.A), (∀ x ∈ Fil o₀.A, IsFilLift m₁.cart x (g x)) → (∀ x ∈ Fil o₀.A, IsFilLift m₂.cart x (g x)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ (𝟙 _)) := by
  intro p _ D R _ b N hN3 hNp k _ _ t o₀ s₁ s₂ o₁ o₂ m₁ m₂ g hg₁ hg₂
  have hF := GlobalTheory.T.liftedHodgeFiltration_eq_of_same_lifts k o₀.A o₁.A o₂.A m₁.φ m₂.φ m₁.cart m₂.cart o₁.ab o₂.ab g hg₁ hg₂
  obtain ⟨d₁, hd₁⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₁.A o₁.ab
  obtain ⟨d₂, hd₂⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₂.A o₂.ab
  obtain ⟨e, he, em⟩ := ((liftHom_eps k).exists_iso_iff m₁.cart o₁.ab hd₁ m₂.cart o₂.ab hd₂).2 hF
  have hact : ∀ c : D.O, (o₁.act.act c).left ≫ e.hom.left = e.hom.left ≫ (o₂.act.act c).left := by
    intro c
    haveI := o₁.act.hom c
    haveI := o₂.act.hom c
    haveI := o₀.act.hom c
    have := (liftHom_eps k).unique m₁.cart o₁.ab hd₁ m₂.cart o₂.ab hd₂ (o₀.act.act c)
      (f := o₁.act.act c ≫ e.hom) (f' := e.hom ≫ o₂.act.act c)
      (by rw [Over.comp_left, ← Category.assoc, ← m₁.act c, Category.assoc, em])
      (by rw [Over.comp_left, ← Category.assoc, em, m₂.act c])
    rw [← Over.comp_left, this, Over.comp_left]

  have hNu : IsUnit (N : DualNumber k) := by simpa using (b.unit N hNp).map (Spec.preimage s₂).hom
  have heta : ∀ y : D.La, (o₁.eta y).left ≫ e.hom.left = 𝟙 _ ≫ (o₂.eta y).left := by
    intro a
    haveI := henselian_of_artinian (DualNumber k)
    let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
    have hπ : Function.Surjective π := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
    have h2 : RingHom.ker π ^ 2 = 0 := GlobalTheory.FODef.sqZero k k
    have hk : RingHom.ker π ≤ IsLocalRing.maximalIdeal (DualNumber k) := by
      intro x hx
      by_contra hc
      have hu : IsUnit x := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
      have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
      rw [h2] at this
      exact (hu.mul hu).ne_zero (by simpa using this)
    obtain ⟨ρ, hρ⟩ : ∃ ρ : k →+* IsLocalRing.ResidueField (DualNumber k),
        ρ.comp π = IsLocalRing.residue (DualNumber k) :=
      ⟨π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨IsLocalRing.residue (DualNumber k), fun x hx => by
          rw [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff]; exact hk hx⟩,
        RingHom.liftOfRightInverse_comp _ _ _ _⟩
    have hs : IsSemiAbelian o₂.A := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ o₂.ab
    let y₁ : Over.mk (𝟙 (Sp (DualNumber k))) ⟶ o₂.A := o₁.eta a ≫ e.hom
    let y₂ : Over.mk (𝟙 (Sp (DualNumber k))) ⟶ o₂.A := o₂.eta a
    have t₁ : y₁ ^ N = 1 := by
      simp only [y₁]
      rw [← pow_comp, ← eta_pow, o₁.eta_ker, MonObj.one_comp]
    have t₂ : y₂ ^ N = 1 := by
      simp only [y₂]
      rw [← eta_pow, o₂.eta_ker]
    have r : spMap π ≫ y₁.left = spMap π ≫ y₂.left := by
      simp only [y₁, y₂, Over.comp_left]
      rw [← Category.assoc, ← m₁.eta a, Category.assoc, em, m₂.eta a]
    have r' : spMap (IsLocalRing.residue (DualNumber k)) ≫ y₁.left =
        spMap (IsLocalRing.residue (DualNumber k)) ≫ y₂.left := by
      rw [← hρ, Cris.spMap_comp, Category.assoc, r, ← Category.assoc]
    let x₀ : Over.mk (spMap (IsLocalRing.residue (DualNumber k)) ≫ 𝟙 (Sp (DualNumber k))) ⟶ o₂.A :=
      toUnit _ ≫ y₂
    have hx₀ : x₀ ^ N = 1 := by
      simp only [x₀]
      rw [← comp_pow, t₂, MonObj.comp_one]
    have hl : x₀.left = spMap (IsLocalRing.residue (DualNumber k)) ≫ y₂.left := by
      simp only [x₀, Over.comp_left]
      congr 1
    obtain ⟨x, -, hu⟩ := GlobalTheory.existsUnique_torsion_lift_of_henselian (DualNumber k) (Sp (DualNumber k)) o₂.A hs
      (𝟙 _) N hNu x₀ hx₀
    have := (hu y₁ ⟨t₁, r'.trans hl.symm⟩).trans (hu y₂ ⟨t₂, hl.symm⟩).symm
    rw [Category.id_comp, ← Over.comp_left]
    exact congrArg Over.Hom.left this
  let φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left :=
    (lift (fst o₁.A o₁.A ≫ e.hom) (snd o₁.A o₁.A ≫ e.hom)).left
  have hsq : IsSquare e.hom.left φ₂ := by
    constructor
    · simp only [φ₂]; rw [← Over.comp_left, lift_fst, Over.comp_left]
    · simp only [φ₂]; rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hpol := GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations p D R b N k t o₀ s₁ s₂ o₁ o₂ m₁ m₂ e he em φ₂ hsq
  exact ⟨{ φ := e.hom.left
           φ₂ := φ₂
           cart := isGrpPullback_of_iso e
           sq := hsq
           act := hact
           pol := hpol
           eta := heta }⟩

end GlobalTheory.HTFirstOrderIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

section Moves

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}

theorem hasTh_of_sabMap (mm : SABMap t' t f) (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S') {N : ℕ}
    (c : Fin N → K) :
    HasTh t'.G t'.PP.L t'.PP.rig m x c ↔ HasTh t.G t.PP.L t.PP.rig m (x ≫ f) c := by
  rw [hasTh_iff, hasTh_iff]
  exact GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen S' t'.G t'.PP.L t'.PP.rig f mm.φ t'.PP.isLB
    t'.PP.rigGen mm.cart (GlobalTheory.ModelSum.lbIso_of_map mm) m m N N K x c c

theorem polFib_of_sabMap (mm : SABMap t' t f) (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S') :
    PolFib t'.G t'.PP.L g x ↔ PolFib t.G t.PP.L g (x ≫ f) :=
  (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S' t.G t.PP.L t'.G t'.PP.L f mm.φ t.PP.isLB t'.PP.isLB mm.cart
    (GlobalTheory.ModelSum.lbIso_of_map mm) g R x).1

end Moves

end GlobalTheory.UMin

namespace GlobalTheory.UMin


open GlobalTheory.CechPic in
theorem key_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (π : M.Z ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (d : Fin (n + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ π = y ≫ Y.j → HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (y ≫ pullback.fst _ _) d → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) 8).pull π) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial)).pull π) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hYg Ω _ _ _ M π y d hZ hpt hth
  obtain ⟨t, ⟨mt⟩⟩ := GlobalTheory.ModelSum.exists_pull π Y.t
  have hP : PCrd (M.pt ≫ (π ≫ g)) (symTup d) := by
    have h1 : M.pt ≫ (π ≫ g) = y ≫ f := by rw [← Category.assoc, hpt, Category.assoc, hYg]
    rw [h1]; exact hf Ω y d hth
  have hD : M.HasDiv d :=
    GlobalTheory.T.hasDiv_of_hasDiv_thetaSymmetricFunctionsDegreeFactorial c.F Ω M (n + 1) d hZ (GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords c.F Ω o M n (π ≫ g) (symTup d) hP)
  obtain ⟨h, -, hhP⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv c.F Ω M n d hD
  have hsym := GlobalTheory.T.symmetric_coordinates_O1_factorial_power c.F Ω o M n h (π ≫ g) d hhP hP
  have hThO : HasTh Y.oF.t.G Y.oF.t.PP.L Y.oF.t.PP.rig m y d := (hasTh_of_sabMap Y.m0.toSABMap m y d).2 hth
  have hThY : HasTh Y.t.G Y.t.PP.L Y.t.PP.rig m (M.pt ≫ π) d := by
    rw [hpt]; exact (hasTh_of_sabMap Y.m m y d).1 hThO
  have hTh : HasTh t.G t.PP.L t.PP.rig m M.pt d := (hasTh_of_sabMap mt m M.pt d).2 hThY
  have hPolO : PolFib Y.oF.t.G Y.oF.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) y :=
    (polFib_of_sabMap Y.m0.toSABMap _ y).2 (GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c Ω _)
  have hPolY : PolFib Y.t.G Y.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (M.pt ≫ π) := by
    rw [hpt]; exact (polFib_of_sabMap Y.m _ y).1 hPolO
  have hPol : PolFib t.G t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) M.pt := (polFib_of_sabMap mt _ M.pt).2 hPolY
  have hmk : IsUnit (m : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by omega))
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.theta_coordinates_section_exists E H c.F Ω M t _ m n d h hZ hm hm3 hmk hPol hTh hhP
  obtain ⟨hab, hop, hamp⟩ := GlobalTheory.T.abelianLocus_eq_preimage_moduli_and_principal E H Dw l Xo c Y M.Z π t ⟨mt⟩
  obtain ⟨hsmY, hvY⟩ := GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y
  have hsm : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback mt.cart.1 hsmY
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨M.pt (IsLocalRing.closedPoint Ω), trivial⟩
  haveI : CharZero Γ(M.Z, ⊤) := (M.res ⊤ hne).charZero
  have hne2 : (abLocus t.G).Nonempty := by
    refine ⟨M.pt (IsLocalRing.closedPoint Ω), ?_⟩
    rw [hab]
    show π (M.pt (IsLocalRing.closedPoint Ω)) ∈ Set.range Y.j
    have hq := congrArg (fun φ : Sp Ω ⟶ Y.X => φ (IsLocalRing.closedPoint Ω)) hpt
    exact ⟨y (IsLocalRing.closedPoint Ω), hq.symm⟩
  have hδ : ((ProjSpace.O1 c.F n).pull h).IsLB := pull_isLB (ProjSpace.O1_isLB c.F n) h
  have := Y.t.semi.separated
  have hHY := hvY.isLB_det
  have hHt := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback mt.cart hvY).isLB_det
  have hkey : LBIso (lbPow ((ProjSpace.O1 c.F n).pull h) 8)
      (lbPow (GlobalTheory.SiegelTor.hodge t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) 4) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) with h0 | h0
    · have hn0 : n = 0 := by
        rw [h0] at hn
        simpa using hn
      subst hn0
      refine (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).1 ?_
      have hz : cls _ hHt = 0 := by
        revert hHt
        rw [h0]
        exact fun hHt => KeySmall.cls_det_zero _ hHt
      have ho : cls _ (ProjSpace.O1_isLB c.F 0) = 0 := by
        let L := ProjSpace.O1 c.F 0
        have hL := ProjSpace.O1_isLB c.F 0
        have h : L.U (0 : Fin 1) = ⊤ := top_le_iff.1 fun x _ => by
          obtain ⟨i, hi⟩ := Semi.LB.mem_of_cover hL x
          obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
          exact hi
        have le : ∀ j, L.U j ≤ L.U j ⊓ L.U (0 : Fin 1) := fun j => le_inf le_rfl (h ▸ le_top)
        have hm : ∀ y : PSpace c.F 0, y ∈ L.U (0 : Fin 1) := fun y => h ▸ TopologicalSpace.Opens.mem_top y
        exact (cls_eq_zero_iff hL).2 ⟨⟨fun j => res (le j) (L.g j (0 : Fin 1))⟩, fun i j => unit_ext fun y hy => by
          rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy.1, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy.2]
          exact (gm_cocycle hL (𝟙 _) y hy.1 hy.2 (hm y)).symm⟩
      rw [cls_lbPow hδ, cls_lbPow hHt, hz, cls_pull (ProjSpace.O1_isLB c.F 0), ho, map_zero,
        nsmul_zero, nsmul_zero]
    · refine KeySmall.key_sab M.Z t _ _ σ h0 hZ inferInstance inferInstance (fun A _ ξ hξ => ?_) hsm hne2 hop hδ hamp
        (KeySmall.nzFib_of_geom σ hσ)
      exact KeySmall.mk_le_of_lft ((Cardinal.mk_le_of_injective (f := fun a : c.F => (a : ℂ)) Subtype.val_injective).trans_eq
        Cardinal.mk_complex) (ξ ≫ M.s)
  have hO := ProjSpace.O1_isLB o n
  have e1 := (cls_eq_iff (pull_isLB hO (π ≫ g)) (isLB_lbPow hδ _)).2 hsym
  have e2 := (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).2 hkey
  have hHiso : LBIso ((GlobalTheory.SiegelTor.hodge Y.t.G _).pull π) (GlobalTheory.SiegelTor.hodge t.G _) :=
    (hvY.lbIso_det_pullback π).trans (pull_isLB hvY.isLB_det π) (hvY.pullback π).isLB_det
      (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback mt.cart hvY).isLB_det
      ((hvY.pullback π).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase mt.cart)))
  have e3 := (cls_eq_iff (pull_isLB hHY π) hHt).2 hHiso
  rw [cls_pull hO, pull_comp, cls_lbPow hδ] at e1
  rw [cls_lbPow hδ, cls_lbPow hHt] at e2
  rw [cls_pull hHY] at e3
  refine (cls_eq_iff (pull_isLB (isLB_lbPow (pull_isLB hO g) 8) π) (pull_isLB (isLB_lbPow hHY _) π)).1 ?_
  rw [cls_pull (isLB_lbPow (pull_isLB hO g) 8), cls_pull (isLB_lbPow hHY _), cls_lbPow (pull_isLB hO g),
    cls_lbPow hHY, map_nsmul, map_nsmul, cls_pull hO, e1, e3, smul_smul, mul_comm 8, ← smul_smul, e2, smul_smul,
    mul_comm]

end GlobalTheory.UMin

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalLab

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem three_le_level (X₁ : Setup F W i) : 3 ≤ X₁.S.r * X₁.S.N := by
  have hN := X₁.ρ.N_eq
  have hn := X₁.ρ.n_prime.two_le
  have hk := X₁.ρ.two_le
  have hr := X₁.S.r_pos
  have h4 : 4 ≤ X₁.S.N := by
    rw [hN]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (X₁.ρ.n ^ X₁.ρ.k) ^ 2 :=
        Nat.pow_le_pow_left (le_trans hn (Nat.le_self_pow (by omega) _)) 2
  nlinarith

theorem isLab_onto (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X))
    (h : IsLab X ε c yy) (μ : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk μ := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm μ))
  exact ⟨a, by rw [hyy a _ ha, AddEquiv.apply_symm_apply]⟩

theorem congMod_of_mk_eq {X : Type} [AddCommGroup X] [Module.Free ℤ X] (κ : X ≃+ X) (m d L₁ : ℕ) (hm : m = d * L₁)
    (hd : d ≠ 0) (x : X)
    (h : (QuotientAddGroup.mk (d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) : ModN m (Fin 8 → X)) =
      QuotientAddGroup.mk (fun b => κ ((d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) b))) : CongMod L₁ (κ x) x := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.1 h
  have hw0 := congrFun hw 0
  simp only [nsmulAddMonoidHom_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.single_eq_same,
    map_nsmul] at hw0
  refine ⟨w 0, ?_⟩
  have key : (d : ℤ) • ((L₁ : ℤ) • w 0) = (d : ℤ) • (κ x - x) := by
    rw [← mul_smul, ← Nat.cast_mul, ← hm, natCast_zsmul, hw0, smul_sub, natCast_zsmul, natCast_zsmul]; abel
  have := smul_right_injective X (show (d : ℤ) ≠ 0 by exact_mod_cast hd) key
  rw [← natCast_zsmul, this]; abel

theorem rigid {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (D : Deep X₁ ε₁)
    {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁)
    (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (h₁ : IsLab X₁ ε₁ c yy₁)
    (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
    (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))
    (hl : IsLab D.X D.ε (D.lift c y h) yy) (hc : D.Compat yy₁ yy)
    (hl' : IsLab D.X D.ε (D.lift c y h) yy') (hc' : D.Compat yy₁ yy') : yy' = yy := by
  obtain ⟨κ, hκβ, hκ⟩ := LabUniq.main g n F W Z i D.X D.ε D.diag p (y (cPt p)) (D.lift c y h) yy yy' hl hl'
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    rw [D.sq]
    exact D.dvd.trans ((dvd_pow_self D.m two_ne_zero).mul_left _)
  have hdL : D.X.S.r * D.X.S.N = D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) :=
    (Nat.div_mul_cancel hdvd).symm
  have hd0 : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) ≠ 0 := by
    intro h0
    have h3 := three_le_level D.X
    rw [hdL, h0, zero_mul] at h3
    omega
  have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (κ x) x := by
    intro x
    obtain ⟨a, ha⟩ := isLab_onto X₁ ε₁ c yy₁ h₁ (Pi.single 0 x)
    have e1 := hc a _ ha
    have e2 := hc' a _ ha
    have e3 := hκ (D.lab a) _ e1
    rw [e2] at e3
    exact congMod_of_mk_eq κ _ _ _ hdL hd0 x e3
  let e : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X := κ.toIntLinearEquiv
  have he : e = LinearEquiv.refl ℤ _ :=
    eq_refl_of_isometry_congMod _ c.T.β (fun x hx => Trait.beta_pos g n _ _ F c.T x hx) e hκβ _
      (three_le_level X₁) hcong
  have hκ1 : ∀ x, κ x = x := fun x => by
    have := congrArg (fun f : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X => f x) he
    simpa [e] using this
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy x)
  rw [hκ x μ hμ.symm, ← hμ]
  simp [hκ1]

end GlobalTheory.Poinc.GalLab

theorem GlobalTheory.Poinc.GalLab.main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (a x) := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  obtain ⟨a, hfix, htr⟩ := GlobalTheory.T.galois_transport_torsion_labels_thetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  refine ⟨a, hfix, ?_⟩
  intro p _ z₁ c yy₁ h₁ y h h' yy yy' hl hc hl' hc' x
  have hl2 := htr p z₁ c y h h' yy hl
  have hc2 : D.Compat yy₁ (yy.comp a.toAddMonoidHom) := fun b μ hb => by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hfix]
    exact hc b μ hb
  have := GalLab.rigid D c yy₁ h₁ (y ≫ s) h' (yy.comp a.toAddMonoidHom) yy' hl2 hc2 hl' hc'
  exact (DFunLike.congr_fun this x)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory

theorem unitaryStepA_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∃ (m₁ m₂ : ℕ), 1 ≤ m₁ ∧ 1 ≤ m₂ ∧ ∀ (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ m₁) ((m₂ : ℤ) * T.be (π (μ cl)) (π (μ cl))).toNat := by
  intro E _ _ _ H Dw _ l Xo c C X₁
  refine ⟨2 * X₁.S.N, 1, by have := X₁.S.N_ge; omega, le_rfl, ?_⟩
  intro M U₀ EE out hA hE x
  haveI := M.qc
  haveI : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  obtain ⟨x', hx', hcl⟩ := (isClosed_closure (s := ({x} : Set M.Z))).exists_closed_singleton ⟨x, subset_closure rfl⟩
  have hxx' : x ⤳ x' := specializes_iff_mem_closure.2 hx'
  obtain ⟨X, i1, i2, i3, i4, n, eb, b₀, μ, e, h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.T.exists_balanced_lattice_data_closedPoint E H Dw l Xo c C X₁ M U₀ EE out hA hE x' hcl
  refine ⟨X, i1, i2, i3, i4, n, eb, b₀, μ, e, h1, h2, h3, h4, h5, h6, ?_⟩
  intro T ξ hξ hsp
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := h7 T ξ hξ (hsp.trans hxx')
  refine ⟨π, hπ1, hπ2, fun cl => ?_⟩
  simpa using hπ3 cl

end GlobalTheory
end
