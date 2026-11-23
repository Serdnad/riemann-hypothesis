module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.GSep.TermsUniq

section Reformulated
variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V] [IsDomain V]
  [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y}

theorem hom_eq_of_comp (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {u v : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    (h : u.left ≫ 𝔪.φ = v.left ≫ 𝔪.φ) : u = v :=
  Over.OverMorphism.ext (𝔪.cart.1.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem frame_val_eq (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {a : X₁.S.Gam} (fr fr₂ : FrAt x)
    (h : ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J)
    (h₂ : ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr₂ (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∀ z J', Good 𝔪.A.L z J' → val fr₂ (𝟙 _) z J' = val fr (𝟙 _) z J' := by
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good' X₁.ρ.P.isLB z
  exact mul_left_cancel ((h₂ z J J' hJ hJ').trans (h z J J' hJ hJ').symm)
end Reformulated

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem valAt_congr {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {k : ℕ} {th : SecA A F k}
    {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} {c : F} (h : ValAt th x e c)
    (he : ∀ z J, Good A.L z J → val e' (𝟙 _) z J = val e (𝟙 _) z J) : ValAt th x e' c := by
  intro z J hJ
  rw [h z J hJ]
  congr 2
  have := he z J hJ
  simp only [Geo.Tor.val, powFrame] at this ⊢
  exact (map_zpow _ _ _).trans ((congrArg (· ^ (k : ℤ)) this.symm).trans (map_zpow _ _ _).symm)

variable {D : DegPre R}

theorem coef_congr {k : ℕ} {g g₂ : GtPtF D F} {w : Frm D F k g.b} {w₂ : Frm D F k g₂.b} (hw : w.IsGen)
    (hb : g₂.b = g.b) (hs : ∀ χ z J, Good D.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J)
    (hv : ∀ z J, Good D.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g₂ w₂ χ = coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e : lift (𝟙 (TF (R := R) F)) g₂.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hs χ z J hJ, hv z J hJ, e]
  exact a

theorem coef_smul {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} (hw : w.IsGen) (u : F) (s : Fam D F k) (χ : D.X) :
    coef (u • s) g w χ = u * coef s g w χ := by
  have hlin := ((coef_basic R D F k g).2.2 w hw).2.1
  have e0 := hlin 0 0 1 χ
  simp only [_root_.one_smul, _root_.add_zero, _root_.one_mul] at e0
  have h0 : coef (0 : Fam D F k) g w χ = 0 := by linear_combination (-1 : F) * e0
  have e := hlin s 0 u χ
  rw [_root_.add_zero, h0, _root_.add_zero] at e
  exact e
end Gen

section Transport
variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V] [IsDomain V]
  [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y}

theorem over_transport (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {w₀ w₀₂ : W0 𝔪.U.toUnifPre}
    {g : GtPtF 𝔪.D.toPre (FractionRing V)} {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b}
    {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A} {fr fr₂ : FrAt x} {u : FractionRing V}
    (hO : 𝔪.Over' w₀₂ g w x fr₂) (hw : w.IsGen)
    (hD : ∀ (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s : Fam 𝔪.D.toPre (FractionRing V) k),
      𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀₂ th (u ^ k • s))
    (hfr : ∀ z J, Good 𝔪.A.L z J → val fr₂ (𝟙 _) z J = val fr (𝟙 _) z J)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J →
      (val w' (𝟙 _) z J).val = cst (FractionRing V) z u * (val w (𝟙 _) z J).val) :
    𝔪.Over' w₀ g w' x fr := by
  intro k hk wk' hwk' hwk'g th s' v hexp hval
  obtain ⟨wk, hwkg, hwk⟩ := TorsionValue.exists_frm_pow w hw k
  have H := hO k hk wk hwk hwkg th (u ^ k • s') v (hD k th s' hexp) (valAt_congr hval fun z J hJ => hfr z J hJ)
  have hcv : ∀ z J, Good 𝔪.D.toPre.P.L z J →
      (val wk' (𝟙 _) z J).val = cst (FractionRing V) z (u ^ k) * (val wk (𝟙 _) z J).val := by
    intro z J hJ
    rw [hwk' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow, cst_eq, cst_eq,
      map_pow]
  have e : coef (u ^ k • s') g wk = coef s' g wk' := funext fun χ => by
    rw [coef_smul hwkg, TorsionValue.coef_scale hwkg hcv s' χ]
  rw [e] at H
  exact H
end Transport

theorem coef_eq : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (b : X₁.S.Gam)
  (x x₂ : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (fr₂ : ∀ a, FrAt (x₂ a))
  (th th₂ : SecA 𝔪.A (FractionRing V) 1) (w₀ w₀₂ : W0 𝔪.U.toUnifPre) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) 1)
  (g' g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x b) (fr b) →
  (∀ a, (x₂ a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀₂.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀₂ th₂ s₂ →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀₂ g₂ w₂ (x₂ b) (fr₂ b) →
  ∀ χ, coef s g' w χ = coef s₂ g₂ w₂ χ := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 b x x₂ fr fr₂ th th₂ w₀ w₀₂ s s₂ g' g₂ w w₂ hx hfr hth hw₀ hs hg hw hO hx₂ hfr₂
    hth₂ hw₀₂ hs₂ hg₂ hw₂ hO₂ χ
  obtain rfl : x = x₂ := (funext fun a => hom_eq_of_comp 𝔪 ((hx₂ a).trans (hx a).symm)).symm
  have efr : ∀ a z J', Good 𝔪.A.L z J' → val (fr₂ a) (𝟙 _) z J' = val (fr a) (𝟙 _) z J' :=
    fun a => frame_val_eq 𝔪 (a := a) (fr a) (fr₂ a) (hfr a).2 (hfr₂ a).2
  have hth₂' : ∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) :=
    fun a => valAt_congr (hth₂ a) fun z J hJ => (efr a z J hJ).symm
  obtain rfl : th = th₂ := Eq.symm <| GlobalTheory.T.section_eq_of_values_at_label_torsion I X₁ z₁ act V ev Y t δ 𝔪 x fr th th₂ (fun a => (hfr a).1) hth hth₂'
  obtain ⟨u, hu, hD⟩ := GlobalTheory.T.uniformisation_generic_frames_scale_by_constant I X₁ z₁ act V ev Y t δ 𝔪 w₀ w₀₂ hw₀ hw₀₂
  obtain ⟨w₂', hw₂'g, hv₂'⟩ := TorsionValue.exists_frm_scale w₂ hw₂ hu
  have hO₂' : 𝔪.Over' w₀ g₂ w₂' (x b) (fr b) := over_transport 𝔪 hO₂ hw₂ hD (efr b) hv₂'
  obtain ⟨hb, hsv⟩ := GlobalTheory.T.thetaMember_torsion_points_eq_same_values I X₁ z₁ act V ev Y t δ 𝔪 w₀ (x b) (fr b) g' g₂ w w₂' hw₀ (hfr b).1 hg hw hO hg₂ hw₂'g hO₂'
  have hwv := GlobalTheory.T.thetaMember_torsion_frame_unique I X₁ z₁ act V ev Y t δ 𝔪 w₀ (x b) (fr b) g' g₂ w w₂' hw₀ (hfr b).1 hg hw hO hg₂ hw₂'g hO₂' hb hsv
  have e1 : coef s g₂ w₂' χ = coef s g' w χ := coef_congr hw hb hsv hwv s χ
  have e2 : coef s₂ g₂ w₂ χ = coef (u ^ 1 • s) g₂ w₂ χ :=
    GlobalTheory.T.thetaMember_expansion_terms_eq I X₁ z₁ act V ev Y t δ 𝔪 w₀₂ 1 th (u ^ 1 • s) s₂ hw₀₂ le_rfl (hD 1 th s hs) hs₂ g₂ w₂ hw₂ χ
  rw [e2, pow_one, coef_smul hw₂, ← TorsionValue.coef_scale hw₂ hv₂' s χ, e1]

end GlobalTheory.GSep.TermsUniq
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdEquation
open GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.FlagBundle

theorem dvd_pow_of_vanishing {Y : Scheme.{0}} (O V : Y.Opens) (t : Γ(Y, V))
    (ht : ∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ O) (W : Y.Opens) (hW : W ≤ V) (f : Γ(Y, W))
    (hf : ∀ z (hz : z ∈ W), z ∉ O → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z))
    (z : Y) (hz : z ∈ W) : ∃ n : ℕ, ger z (hW hz) t ∣ ger z hz f ^ n := by
  obtain ⟨A, hA, hzA, e⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hz
  have hA' : IsAffineOpen A := hA
  let f' : Γ(Y, A) := Y.presheaf.map (homOfLE e).op f
  let t' : Γ(Y, A) := Y.presheaf.map (homOfLE (e.trans hW)).op t
  have hle : Y.basicOpen f' ≤ Y.basicOpen t' := by
    intro x hx
    have hxA : x ∈ A := Y.basicOpen_le _ hx
    rw [Y.mem_basicOpen _ x hxA] at hx ⊢
    rw [Y.presheaf.germ_res_apply] at hx ⊢
    refine (ht x _).2 ?_
    by_contra hO
    exact hf x (e hxA) hO hx
  have h2 : PrimeSpectrum.basicOpen f' ≤ PrimeSpectrum.basicOpen t' := by
    rw [← hA'.fromSpec_preimage_basicOpen, ← hA'.fromSpec_preimage_basicOpen]
    exact fun x hx => hle hx
  obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 h2
  have h3 := map_dvd (Y.presheaf.germ A z hzA).hom (Ideal.mem_span_singleton.1 hn)
  rw [map_pow] at h3
  refine ⟨n, ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (e.trans hW)) z hzA t, ← Y.presheaf.germ_res_apply (homOfLE e) z hzA f]
  exact h3

theorem exists_section {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (hD : D.Eff)
    (hr : ∀ (y : X) (g : X.functionFieldˣ), D.IsEqn y g → ∀ (f : X.functionField) (n : ℕ), RegAt y f →
      RegAt y (f ^ n / g) → RegAt y (f / g)) (y : X) :
    ∃ (V : X.Opens) (_ : y ∈ V) (t : Γ(X, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∉ D.supp) ∧
      ∀ z (hz : z ∈ V) (b : X.presheaf.stalk z) (n : ℕ), ger z hz t ∣ b ^ n → ger z hz t ∣ b := by
  obtain ⟨U, hyU, g, hg⟩ := D.exists_isEqn_nhds y
  obtain ⟨a, ha⟩ := (hg y hyU).regularAt_iff.1 (hD y)
  rw [one_mul] at ha
  obtain ⟨W, hyW, s, rfl⟩ := X.presheaf.germ_exist a
  have inj := fun z : X => IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  have key : ∀ z (hz : z ∈ W ⊓ U), algebraMap _ X.functionField
      (ger z hz (X.presheaf.map (homOfLE inf_le_left).op s)) = g := fun z hz => by
    refine Eq.trans ?_ ((algebraMap_germ hz.1 s).trans ((algebraMap_germ hyW s).symm.trans ha))
    exact congrArg _ (X.presheaf.germ_res_apply (homOfLE inf_le_left) z hz s)
  refine ⟨W ⊓ U, ⟨hyW, hyU⟩, X.presheaf.map (homOfLE inf_le_left).op s, fun z hz => ?_, fun z hz b n hb => ?_⟩
  · rw [(hg z hz.2).mem_supp_iff, not_not]
    refine ⟨fun h => ⟨_, h, key z hz⟩, fun ⟨u, hu, e⟩ => ?_⟩
    rwa [inj z (e.trans (key z hz).symm)] at hu
  · obtain ⟨c, hc⟩ := hb
    obtain ⟨d, hd⟩ := hr z g (hg z hz.2) (algebraMap _ X.functionField b) n ⟨b, rfl⟩ ⟨c, by
      rw [eq_div_iff g.ne_zero, ← map_pow, hc, map_mul, key z hz, mul_comm]⟩
    refine ⟨d, inj z ?_⟩
    rw [map_mul, key z hz, hd, mul_div_cancel₀ _ g.ne_zero]

theorem exists_reduced_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  intro _ E _ _ _ H Dw l Xo c T Z hF _ y _
  have hsm := GlobalTheory.VarFlag.smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, -, hl⟩ :=
    GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  obtain ⟨h, hiso, hh, -, -⟩ := GlobalTheory.CompProport.exists_iso T Z B j hB hcov C f hπ hl
  have hmem : ∀ z : Y₀ T.X Z, h z ∉ CartierDiv.supp C.bd ↔ z ∈ U₀ T.X Z := fun z => by
    have e : GlobalTheory.Toroidal.genι T.Y (C.π (h z)) = T.X.π (inc₀ T.X Z z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    refine (not_congr (C.bd_supp (h z))).trans (not_not.trans ?_)
    change C.π (h z) ∈ Set.range T.Y.jQ ↔ T.X.π (inc₀ T.X Z z) ∈ Set.range T.Y.j
    refine exists_congr fun x => ?_
    rw [← e, Model.j, Scheme.Hom.comp_apply]
    exact (GlobalTheory.Toroidal.genι T.Y).isOpenEmbedding.injective.eq_iff.symm
  obtain ⟨V, hyV, t, ht, hrad⟩ := exists_section C.bd C.bd_eff C.bd_red (h y)
  have hg : ∀ z (hz : z ∈ h ⁻¹ᵁ V), ger z hz (h.app V t) = (h.stalkMap z).hom (ger (h z) hz t) :=
    fun z hz => (Scheme.Hom.germ_stalkMap_apply h V z hz t).symm
  have hu : ∀ z (hz : z ∈ h ⁻¹ᵁ V), IsUnit (ger z hz (h.app V t)) ↔ z ∈ U₀ T.X Z := fun z hz => by
    rw [hg, isUnit_map_iff]
    exact (ht (h z) hz).trans (hmem z)
  refine ⟨h ⁻¹ᵁ V, hyV, h.app V t, hu, fun W hW s hs z hz => ?_⟩
  obtain ⟨n, c', hc⟩ := dvd_pow_of_vanishing _ _ _ hu W hW s hs z hz
  have hb := GlobalTheory.BoundaryDivisor.stalkMap_bijective h z
  obtain ⟨b, hb'⟩ := hb.2 (ger z hz s)
  obtain ⟨c'', rfl⟩ := hb.2 c'
  rw [hg, ← hb', ← map_pow, ← map_mul] at hc
  rw [hg, ← hb']
  exact map_dvd _ (hrad _ _ b n ⟨c'', hb.1 hc⟩)

end GlobalTheory.BdEquation
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.GaussBC

theorem gp_comp_eq_spMap_cst : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R),
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  intro X _ R _ p
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_regAt_zeroAt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X), p x = closedPoint R → ∀ r : R, GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  intro R _ _ X _ p x hx r
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.GaussBC

namespace GlobalTheory.Desc.GaussBC

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

theorem zero_mem_spanBy (T : Set F₁) : (0 : F₁) ∈ spanBy c T := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy {T : Set F₁} {v w : F₁} (hv : v ∈ spanBy c T) (hw : w ∈ spanBy c T) :
    v + w ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem mul_mem_spanBy {T : Set F₁} {v : F₁} (hv : v ∈ spanBy c T) (d : R₁) : c d * v ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  exact ⟨n, fun i => d * r i, t, ht, by rw [Finset.mul_sum]; simp only [map_mul, _root_.mul_assoc]⟩

theorem spanBy_induction {T : Set F₁} (p : F₁ → Prop) (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hmul : ∀ r, ∀ t ∈ T, p (c r * t)) : ∀ v ∈ spanBy c T, p v := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact Finset.sum_induction _ p hadd h0 fun i _ => hmul (r i) (t i) (ht i)

end Span

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem gauss_baseChange : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → GaussAt (GlobalTheory.Desc.cst H'.hom) (maximalIdeal D) θ (regSet y) (regSet y') ∧ θ ⁻¹' (regSet y') = regSet y ∧ LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hmT := hϖ.maximalIdeal_eq
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]

  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_eq_spMap_cst H.left T H.hom
    have e2 := gp_comp_eq_spMap_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  set c := cst H'.hom with hc
  set P := c (a ϖ) with hPdef
  have hP : P = θ (cst H.hom ϖ) := by rw [hPdef, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply]
  obtain ⟨hϖ0, hfac⟩ := GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT
  have hP0 : P ≠ 0 := by rw [hP]; exact (map_ne_zero θ).2 hϖ0
  have hPz : GlobalTheory.Cartier.ZeroAt y' P :=
    (cst_regAt_zeroAt D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_regAt_zeroAt D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_regAt_zeroAt T H.left H.hom y hy t).1
  have hmod := GlobalTheory.T.thetaSpan_vanishing_eq_uniformiser_mul T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy' ϖ hmT
  set S := spanBy c (θ '' regSet y) with hS
  have hSreg : ∀ v ∈ S, GlobalTheory.Cartier.RegAt y' v :=
    spanBy_induction c _ (regAt_zero y') (fun _ _ h h' => h.add h') (by
      rintro r _ ⟨t, ht, rfl⟩; exact (hcreg r).mul (hreg t ht))
  have hSP : ∀ v ∈ S, ∀ N : ℕ, P ^ N * v ∈ S := by
    intro v hv N
    induction N with
    | zero => simpa using hv
    | succ N ih => rw [pow_succ', _root_.mul_assoc]; exact mul_mem_spanBy c ih _

  have hQ : ∀ v ∈ spanBy c (Set.range θ), ∃ N : ℕ, P ^ N * v ∈ S := by
    refine spanBy_induction c _ ⟨0, by simpa using zero_mem_spanBy c _⟩ ?_ ?_
    · rintro v w ⟨N, hN⟩ ⟨M, hM⟩
      refine ⟨N + M, ?_⟩
      have := add_mem_spanBy c (hSP _ hN M) (hSP _ hM N)
      convert this using 1; ring
    · rintro r _ ⟨u, rfl⟩
      by_cases hu : u = 0
      · exact ⟨0, by simpa [hu] using zero_mem_spanBy c _⟩
      obtain ⟨k, w, hw, rfl⟩ := hfac u hu
      refine ⟨(-k).toNat, ?_⟩
      have hk : ((-k).toNat : ℤ) + k = ((((-k).toNat : ℤ) + k).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by omega)).symm
      have e : P ^ (-k).toNat * (c r * θ (cst H.hom ϖ ^ k * w)) =
          c r * θ (cst H.hom ϖ ^ (((-k).toNat : ℤ) + k).toNat * w) := by
        rw [hP, map_mul, map_mul, map_zpow₀, map_pow]
        have hq : θ (cst H.hom ϖ) ^ (-k).toNat * θ (cst H.hom ϖ) ^ k =
            θ (cst H.hom ϖ) ^ (((-k).toNat : ℤ) + k).toNat := by
          rw [← zpow_natCast, ← zpow_natCast _ (((-k).toNat : ℤ) + k).toNat, ← hk,
            zpow_add₀ ((map_ne_zero θ).2 hϖ0)]
        linear_combination (c r * θ w) * hq
      rw [e]
      exact mul_mem_spanBy c (subset_spanBy c (θ '' regSet y) (Set.mem_image_of_mem θ
        (show _ ∈ regSet y from (regAt_pow (hc0reg ϖ) _).mul hw.regAt))) r

  have hB : ∀ (N : ℕ) (t : H'.left.functionField), GlobalTheory.Cartier.RegAt y' t → P ^ N * t ∈ S → t ∈ S := by
    intro N
    induction N with
    | zero => intro t _ h; simpa using h
    | succ N ih =>
      intro t ht h
      rw [pow_succ', _root_.mul_assoc] at h
      obtain ⟨z₁, hz₁, e⟩ := hmod _ h (hPz.mul ((regAt_pow hPz.regAt N).mul ht))
      have : P ^ N * t = z₁ := mul_left_cancel₀ hP0 e
      exact ih t ht (this ▸ hz₁)
  refine ⟨fun v ⟨d, hd0, hdv⟩ => ⟨fun hv => ?_, fun ⟨s, hs, hsv⟩ => ?_⟩, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hQ _ hdv
    have hirr : Irreducible (a ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmD
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
    have e : P ^ (N + n) * v = c (↑u⁻¹ : D) * (P ^ N * (c (↑u * a ϖ ^ n) * v)) := by
      rw [hPdef, map_mul, map_pow]
      have : c (↑u⁻¹ : D) * c ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(c (a ϖ) ^ (N + n) * v)) * this
    refine ⟨1, fun h => (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [map_one, _root_.one_mul]
    exact hB (N + n) v hv (e ▸ mul_mem_spanBy c hN _)
  · obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hs
    have e : v = c (↑u⁻¹ : D) * (c ↑u * v) := by rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e]; exact (hcreg _).mul (hSreg _ hsv)
  · ext u
    refine ⟨fun h => ?_, fun h => hreg u h⟩
    change GlobalTheory.Cartier.RegAt y' (θ u) at h
    change GlobalTheory.Cartier.RegAt y u
    by_cases hu : u = 0
    · rw [hu]; exact regAt_zero y
    obtain ⟨k, w, hw, rfl⟩ := hfac u hu
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [zpow_natCast]; exact (regAt_pow (hc0reg ϖ) k).mul hw.regAt
    · exfalso
      have hw0 := hw.ne_zero
      obtain ⟨hw1, hw2⟩ := (unitAt_iff hw0).1 hw
      have hθw : GlobalTheory.Cartier.UnitAt y' (θ w) :=
        (unitAt_iff ((map_ne_zero θ).2 hw0)).2 ⟨hreg w hw1, by rw [← map_inv₀]; exact hreg _ hw2⟩
      have hm1 : ((-(k + 1)).toNat : ℤ) = -(k + 1) := Int.toNat_of_nonneg (by omega)
      have e : P⁻¹ = θ (cst H.hom ϖ ^ k * w) * (θ w)⁻¹ * P ^ (-(k + 1)).toNat := by
        rw [map_mul, map_zpow₀, ← hP, _root_.mul_assoc (P ^ k), mul_inv_cancel₀ ((map_ne_zero θ).2 hw0),
          _root_.mul_one, ← zpow_natCast, hm1, ← zpow_add₀ hP0, show k + -(k + 1) = -1 by ring, zpow_neg_one]
      have hPi : GlobalTheory.Cartier.RegAt y' P⁻¹ := by
        rw [e]; exact (h.mul hθw.inv.regAt).mul (regAt_pow hPz.regAt _)
      exact (zeroAt_iff.1 hPz).2 ((unitAt_iff hP0).2 ⟨hPz.regAt, hPi⟩)
  · exact GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange T D a ha H H' π θ hpb ⟨_, hff.choose_spec⟩

end GlobalTheory.Desc.GaussBC
end
