module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle052
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle096
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle086
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
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
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem isDer_snd_of_ringHom {R : Type} [CommRing R] (xD : R →+* DualNumber ℂ) :
    IsDer ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) (fun r => (xD r).snd) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [map_add (f := _), TrivSqZeroExt.snd_add]
  · simp only [map_mul, TrivSqZeroExt.snd_mul, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring

theorem spMap_fst_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 (Sp ℂ) := by
  unfold spMap Sp
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem exists_isConst_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  intro hL P₀ u Hm χ hU R _ xD A _ A' _ φ j s hA hA' hφ hj hKS

  have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD =
      spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hsq : IsPullback (j ≫ φ) P₀.A.hom A.hom
      (spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD)) := by
    rw [← hcomp]
    exact hj.1.paste_horiz hφ.1

  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_global_derivation_of_kodairaSpencer_zero hL P₀ u Hm χ hU R _ A.left A.hom (j ≫ φ) hA.smooth hsq
    (fun r => (xD r).snd) s (isDer_snd_of_ringHom xD) hKS

  obtain ⟨Y', ρ, π, hpb⟩ : ∃ (Y' : Scheme.{0}) (ρ : Y' ⟶ P₀.A.left) (π : Y' ⟶ Sp (DualNumber ℂ)),
      IsPullback ρ π P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hw : 𝟙 P₀.A.left ≫ P₀.A.hom =
      (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, spMap_fst_comp_algebraMap, Category.comp_id, Category.id_comp]
  obtain ⟨i, hiρ, hiπ⟩ := hpb.exists_lift (𝟙 _) (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) hw

  have hm : (j ≫ φ) ≫ A.hom =
      P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hiΦ, hΦ⟩ :=
    GlobalTheory.T.exists_hom_from_const_thickening_of_derivation P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ R xD A.left A.hom (j ≫ φ) d hm hd

  obtain ⟨e, heφ, heπ⟩ := hφ.1.exists_lift Φ π hΦ
  have hie : i ≫ e = j := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, heφ, hiΦ]
    · rw [Category.assoc, heπ, hiπ, hj.1.w]

  have hpb' := (GlobalTheory.T.const_thickening_complex_functions_structure P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ).2.1
  have := P₀.isAb.smooth
  have hfl : Flat π := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have he : IsIso e := GlobalTheory.T.isIso_thickening_map_of_mod_eps P₀.A.left Y' A'.left P₀.A.hom π A'.hom i j e hpb' hj.1 hfl heπ hie

  have hsq2 : IsPullback (inv e) A'.hom π (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heπ]⟩
  have hρ₀ : IsPullback (inv e ≫ ρ) A'.hom P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) := by
    have h := hsq2.paste_horiz hpb
    rwa [Category.id_comp] at h
  have hjρ : j ≫ inv e ≫ ρ = 𝟙 _ := by
    rw [← hie, Category.assoc, IsIso.hom_inv_id_assoc, hiρ]
  exact exists_isConst_of_isPullback hL P₀.A A' (inv e ≫ ρ) j P₀.isAb hA' hj hρ₀ hjρ

end GlobalTheory.KS
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelTower

theorem zeta_eq_pow {n m : ℕ} (hm : 0 < m) (h : n ∣ m) : zeta n = zeta m ^ (m / n) := by
  obtain ⟨c, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  have hc : 0 < c := Nat.pos_of_mul_pos_left hm
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c hn, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact (baseKA l₂).ρ.2
  · rw [zeta_eq_pow l₂.A_pos h]
    exact pow_mem (baseKA l₂).ζ.2 _

theorem base_rho (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem base_zeta (l : Level H) : (((baseKA l).ζ : KA l) : ℂ) = zeta l.A := rfl

theorem exists_inclusion' {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') :
    ∃ j : F →+* F', ∀ x, ((j x : F') : ℂ) = ((x : F) : ℂ) :=
  ⟨(IntermediateField.inclusion h).toRingHom, fun x => IntermediateField.coe_inclusion h x⟩

theorem exists_inclusion {l l₂ : Level H} (h : l.A ∣ l₂.A) :
    ∃ j : KA l →+* KA l₂, (∀ x, ((j x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ j (baseKA l).ρ = (baseKA l₂).ρ ∧
      j (baseKA l).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  obtain ⟨j, hj⟩ := exists_inclusion' (KA_le h)
  refine ⟨j, hj, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [hj, base_rho, base_rho]
  · rw [hj, IntermediateField.coe_pow, base_zeta, base_zeta]
    exact zeta_eq_pow l₂.A_pos h

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x (rfl | rfl)
  · refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_natCast H.d).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem finite_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : j.Finite := by
  letI := j.toAlgebra
  exact Module.Finite.of_restrictScalars_finite ℚ K K'

theorem etale_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : Etale (spMap j) := by
  letI := j.toAlgebra
  haveI : Module.Finite K K' := finite_of_numberField j
  haveI : Algebra.FormallyEtale K K' := Algebra.FormallyEtale.of_isSeparable K K'
  haveI : Algebra.FinitePresentation K K' := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K K' := ⟨inferInstance, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr this

end GlobalTheory.LevelTower

namespace GlobalTheory

open LevelTower

theorem nonempty_levelQuot : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  intro hL hL2 hTh E _ _ _ H D l l₂ Xo₂ hpq hdvd
  have hA : l.A ∣ l₂.A := hdvd.2.2
  obtain ⟨jK, hj, hjρ, hjζ⟩ := exists_inclusion hA
  haveI := finiteDimensional_KA l₂
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ :=
    GlobalTheory.LevelGroup.exists_group_action hL hL2 E H D l l₂ Xo₂ jK hpq hdvd hj
  have hq : IsQProjOver (Xo₂.s ≫ spMap jK) :=
    (isQProjOver_baseChange_and_finite_restrict _ _ jK Xo₂.X (Xo₂.s ≫ spMap jK)).2 Xo₂.s
      (finite_of_numberField jK) Xo₂.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    exists_isGaloisCover_of_isQProjOver (KA l) Xo₂.X (Xo₂.s ≫ spMap jK) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := GlobalTheory.T.isQProjOver_target_of_isGaloisCover (KA l) _ Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension D.dim (π ≫ sY) := by
    rw [hπ]
    haveI := Xo₂.smooth
    haveI : Etale (spMap jK) := etale_of_numberField jK
    haveI : SmoothOfRelativeDimension 0 (spMap jK) := inferInstance
    have := smoothOfRelativeDimension_comp D.dim 0 Xo₂.s (spMap jK)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension D.dim sY := GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover (KA l) _ Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨t', m, hνm, hp, ha, hk⟩ := GlobalTheory.T.exists_abelianTriple_descent_galoisCover hL hL2 hTh E H (KA l) _ Y π sY Ga ρ Xo₂.univ.t _ ν hG hqY
    Xo₂.univ.proper (obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ _ _ _ Xo₂.univ).2.1
    Xo₂.univ.ample Xo₂.univ.ktriv hν1 hνmul
  obtain ⟨ob, m', hη, hηA⟩ := obj_descend_lower_level hL hL2 E H D l l₂ _ _ (baseKA l) (baseKA l₂) jK _ Y π sY
    Xo₂.s Ga ρ Xo₂.univ (fun a => (ν a).φ) t' m hdvd hjρ hjζ
    hπ hG hνm hlow hp ha hk
  refine ⟨⟨Y, sY, hqY, hsY, ob, π, jK, hj, hπ, hG.fin, hG.etale, hG.onto, m', hη, hηA, ?_⟩⟩
  intro K _ _ y y' t mu mu' eM eA h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans K y y' t mu mu' eM eA h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

end GlobalTheory

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullRigid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_field (hS : Out.SerreSt) {S : Scheme.{0}} {t : SAB H S} (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) {K : Type} [Field K] [CharZero K] {z : Sp K ⟶ S}
    {t' : SAB H (Sp K)} (m m' : SABMap t' t z) {N : ℕ} (hN : 3 ≤ N)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Sp K) (y : Over.mk x ⟶ t'.G),
      y ^ N = 1 → y.left ≫ m.φ = y.left ≫ m'.φ) : m.φ = m'.φ := by
  obtain ⟨θ, hθ, hφ, -, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w₁, g₁, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have : ConnectedSpace t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp K) :=
    { A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB
      ample := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) U hU hy hA
      ktriv := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) hK
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have hNK : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
  have hMu : IsUnit (N : Γ(Sp K, ⊤)) := by
    simpa using hNK.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : Etale (Out.mulA t'.G N).left := GrpTangent.etale_id_pow t'.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine hS (Sp K) P N hN θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t'.G N θ.hom fun k _ _ x y hy => ?_)
    · obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (t'.G.hom ⁻¹ᵁ ⊤).ι
      refine gen_chartPull (chartPullOut t'.PP.L _ _ _ _ fun n => ?_) t ht
      fin_cases n
      exacts [rfl, (Category.comp_id _).symm]
    · let β : K →+* k := (Spec.preimage x).hom
      have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
      apply Over.OverMorphism.ext
      apply m'.cart.1.hom_ext
      · rw [Over.comp_left, Category.assoc]
        exact (congrArg _ hφ).trans (hfix k x y hy)
      · rw [Over.w, Over.w]
  rw [← hφ, h, Over.id_left, Category.id_comp]

theorem eq_on_torsion {D : Datum H} {n N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S}
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {t' : SAB H S'} {f : S' ⟶ S} (ν ν' : SABMap t' t f)
    (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)) (hN : 0 < N) (o : FullObj D s t lev)
    (h : ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) (h' : ∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ t'.G) (hy : y ^ N = 1) :
    y.left ≫ ν.φ = y.left ≫ ν'.φ := by
  obtain ⟨-, I, -, hI⟩ := o.geom k (x ≫ f) (Spec.preimage ((x ≫ f) ≫ s)).hom (Spec.map_preimage _).symm
  have hy₁ : pushHom ν.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN _).1 hy₁
  have e : (x ≫ f) ≫ (lev a).left = y.left ≫ ν.φ := congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply ν.cart.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h a).trans (h' a).symm)

end GlobalTheory.FullRigid

theorem GlobalTheory.fullObj_rigid : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (t' : SAB H S') (f : S' ⟶ S) (ν ν' : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), 3 ≤ N → Odd N → FullObj D s t lev → IsReduced S' → (∀ x : S', CharZero (S'.residueField x)) → (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → (∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left) → ν.φ = ν'.φ := by
  intro hL E _ _ _ H D n N S S' s t lev t' f ν ν' lv hN _ o _ hc h h'
  obtain ⟨θ, hθ, hφ, -⟩ := sabMap_iso ν ν' rfl rfl
  have hA : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 o.proper, t'.semi.geomConnected⟩
  have key : θ.hom = 𝟙 _ := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre hL.globalFns t'.G hA θ.hom (IsMonHom.one_hom θ.hom) fun p => ?_
    have := hc p
    let j : Sp (S'.residueField p) ⟶ S' := S'.fromSpecResidueField p
    have hsemi : IsSemiAbelian ((Over.pullback j).obj t'.G) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := t'.semi.comm; infer_instance
      · have := t'.semi.smooth; change Smooth (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.separated; change IsSeparated (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.quasiCompact; change QuasiCompact (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.geomConnected; change GeometricallyConnected (pullback.snd t'.G.hom j); infer_instance
      · intro Ω _ _ q
        obtain ⟨E⟩ := t'.semi.fibres Ω (q ≫ j)
        exact ⟨torusExtOfIso (pullCompIso q j t'.G) E⟩
    have hPull : ∃ (PP' : RigLB ((Over.pullback j).obj t'.G))
        (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback j).obj t'.G, hsemi,
          OAct.pullback j t'.G t'.act, PP', cub, sym, adj, prim⟩ t' j),
        m.φ = pullback.fst t'.G.hom j := by
      have h := isGrpPullback_pullback t'.G j
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull _ _ t'.G _ (cubeMapOf h) t'.PP t'.cub
      have hact : ∀ a, ((OAct.pullback j t'.G t'.act).act a).left ≫ pullback.fst t'.G.hom j =
          pullback.fst t'.G.hom j ≫ (t'.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over (Sp (S'.residueField p))} (x : T ⟶ (Over.pullback j).obj t'.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback j t'.G t'.act).act a) = pushPt h.1.w x ≫ t'.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB t'.PP hL hr, c', hs t'.sym, fun a => ?_, ?_,
        ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback j).obj t'.G) ((Over.pullback j).obj t'.G)))
          (pushPt h.1.w (snd ((Over.pullback j).obj t'.G) ((Over.pullback j).obj t'.G)))
        refine LBIso.chartPull (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t'.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback j).obj t'.G))
        refine LBIso.chartPull (chartPullPull t'.PP.L _)
          (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t'.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := hPull
    generalize (⟨(Over.pullback j).obj t'.G, hsemi,
      OAct.pullback _ t'.G t'.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t'' at m
    obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m
    obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' m
    have e : a.φ = b.φ := GlobalTheory.FullRigid.eq_of_field hL.serre o.proper o.ample o.ktriv a b hN fun k _ _ _ x y hy => by
      have hy₁ : pushHom m.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
      have e₁ := GlobalTheory.FullRigid.eq_on_torsion ν ν' lv (by omega) o h h' k (x ≫ j) _ hy₁
      rw [ha, hb, ← Category.assoc, ← Category.assoc]
      exact e₁
    refine ⟨_, _, j, m.φ, _, (default : PrimeSpectrum (S'.residueField p)),
      Scheme.fromSpecResidueField_apply p _, m.cart.1, ?_⟩
    apply ν'.cart.1.hom_ext
    · rw [Category.assoc]
      exact (congrArg (m.φ ≫ ·) hφ).trans (ha.symm.trans (e.trans hb))
    · rw [Category.assoc, Over.w]
  rw [← hφ, key, Over.id_left, Category.id_comp]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.Coisotropic

theorem eq_one_of_unitOn_eq_one {R : Type} [CommRing R] {u : Rˣ} (h : unitOn u = 1) : u = 1 := by
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact congrArg Units.val h

theorem level_dvd_form_of_cubWeil_one : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ∀ (K : Type) [Field K] [IsAlgClosed K] (u : Sp K ⟶ U) (a a' : D.La) (p p' : Over.mk (u ≫ j) ⟶ t.G), p.left = u ≫ (o.etaA a).left ≫ μ₀.φ → p'.left = u ≫ (o.etaA a').left ≫ μ₀.φ → CubWeil t.cub l.A p p' 1 → (l.A : ℤ) ∣ D.EF a a' := by
  intro hL E _ _ _ H D l B _ b X U j s o t μ₀ K _ _ u a a' p p' hp hp' h
  have hβ : u ≫ s = spMap (Spec.preimage (u ≫ s)).hom := (Spec.map_preimage (u ≫ s)).symm
  obtain ⟨-, I, -, hI, -⟩ := o.geom K u _ hβ
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have kill : ∀ c, I.ev l.A c ^ l.A = 1 := fun c => (I.onto l.A l.A_pos _).2 ⟨c, rfl⟩
  have h₁ : CubWeil o.t.cub l.A (I.ev l.A a) (I.ev l.A a') (unitOn (I.ζ l.A ^ D.EF a a')) :=
    (cubWeil_iff_weilIs hL.globalFns hA (kill a) (kill a') _).2 (I.isom l.A l.A_pos a a')
  have h₂ := GlobalTheory.T.cubicalBundlePairing_compatible_pullback X U j t.G o.t.G μ₀.cm μ₀.cart.1.w
    (fun T x y => Over.OverMorphism.ext (μ₀.cart.2 T x y _ _ rfl rfl).symm) _ _ _ _ μ₀.lin l.A _ _ _ _ h₁
  have e : ∀ (c : D.La) (q : Over.mk (u ≫ j) ⟶ t.G), q.left = u ≫ (o.etaA c).left ≫ μ₀.φ →
      Out.toBase μ₀.cart.1.w (I.ev l.A c) = q := fun c q hq => Over.OverMorphism.ext (by
    rw [hq, ← hI c]
    show ((toUnit (Over.mk u)).left ≫ (o.etaA c).left) ≫ μ₀.φ = _
    rw [Category.assoc]
    rfl)
  rw [e a p hp, e a' p' hp'] at h₂
  exact ((I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd _).1 (eq_one_of_unitOn_eq_one (h₂.unique h))

end GlobalTheory.Coisotropic
end
