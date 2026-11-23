module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobi
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
import Mathlib.RingTheory.Henselian
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
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle001
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
  first | exact @GlobalTheory.ArcQ.arcBasis_baseChange | exact GlobalTheory.ArcQ.arcBasis_baseChange | (intros; apply GlobalTheory.ArcQ.arcBasis_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_constant_eigenbasis_tangent_arc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] [CharZero A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (f : c.F →+* FractionRing A), f.comp β = (algebraMap A (FractionRing A)).comp b → (∀ τ x, algebraMap A (FractionRing A) (ρ τ x) = f (embK c τ x)) → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → ∃ e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A), (∀ τ k, GtTanR (e τ k)) ∧ ArcBasis W ρ e := by
  first | exact @GlobalTheory.ConstBasis.exists_arcBasis | exact GlobalTheory.ConstBasis.exists_arcBasis | (intros; apply GlobalTheory.ConstBasis.exists_arcBasis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.TransvPrinc

theorem transvIn_of_princ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {M N : ℕ}
    (hMN : M ∣ N) (la : Wt X.Ψ r)
    (hP : ∀ gm : GL (Fin r) E, IsUStab X.Gm X.Λ gm →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (gm : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → gm ∈ X.Γ)
    (hχ : ∀ gm ∈ X.Γ, X.χ la gm = 1) : TransvIn X N la := by
  intro ξ hξ s hs hc
  have hκ : cc (s * X.κ0) = -(s * X.κ0) := by
    have h0 := X.ξ0_im
    simp only [cc] at hs h0 ⊢
    rcases X.κ0_xi with h | h <;> simp [h, hs, h0, map_ofNat]
  have hn : ∀ (n : ℕ) u, u ∈ X.Λ → (n : E) • u ∈ X.Λ := fun n u hu => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hu n
  have hmem : GlobalTheory.FlagData.transv X.Gm hξ.2.1 (s * X.κ0) ∈ X.Γ := by
    refine hP _ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ (fun x hx => ?_)
    · exact GlobalTheory.FlagData.herm_transvMat X.Gm_herm hξ.2.1 hκ x y
    · obtain ⟨u, hu, e⟩ := hc x hx
      rw [sub_eq_iff_eq_add] at e
      change (transvMat _ _ _).mulVec x ∈ _
      rw [e]; exact add_mem (hn _ u hu) hx
    · change (transvMat _ _ _).mulVec x ∈ _ at hx
      obtain ⟨u, hu, e⟩ := hc _ hx
      have : x = (transvMat X.Gm ξ (s * X.κ0)).mulVec x - (N : E) • u := by
        rw [← e, GlobalTheory.FlagData.transvMat_mulVec _ _ (Matrix.mulVec _ _), GlobalTheory.FlagData.transvMat_mulVec,
          GlobalTheory.FlagData.herm_add_smul_left, hξ.2.1]
        simp
      rw [this]; exact sub_mem hx (hn _ u hu)
    · obtain ⟨m, hm⟩ := hMN
      obtain ⟨u, hu, e⟩ := hc x hx
      refine ⟨(m : E) • u, hn m u hu, ?_⟩
      change (transvMat _ _ _).mulVec x - x = _
      rw [e, hm, smul_smul]
      push_cast; rfl
  exact ⟨_, hmem, rfl, hχ _ hmem⟩

theorem transvIn_of_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.FrameNorm.HasPrinc U l.M → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → ∀ k, TransvIn (U.X k) l.M' (laU U a' n k) := by
  intro E _ _ _ H Dw l Xo c σ r U a' n hP hχ k
  exact transvIn_of_princ (U.X k) (Nat.dvd_lcm_left _ _) _ (hP k) (hχ k)

end GlobalTheory.TransvPrinc
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), InR D j → j < D.R.m → ∀ F : (recB h).Cusp j ka, (∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA ka) ka.n k)) ∧ (F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka ↔ ∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) := by
  first | exact @GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish | exact GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish | (intros; apply GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamFree

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FamSec (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

abbrev multiples (D : DegPre R) (k : ℕ) : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range

theorem zero_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s (α + k • mu)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hG k mu α
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

theorem zero_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s β).f j = 0 := by
  obtain ⟨mu, rfl⟩ := hβ
  exact zero_add_nsmul hG s α mu h

theorem zero_add_nsmul_iff (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X) :
    (∀ j, (s.s (α + k • mu)).f j = 0) ↔ ∀ j, (s.s α).f j = 0 :=
  ⟨zero_of_eq_add_nsmul hG s ⟨-mu, by rw [smul_neg, add_neg_cancel_right]⟩, zero_add_nsmul hG s α mu⟩

theorem eq_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s t : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : s.s α = t.s α) : s.s β = t.s β := by
  have h0 := zero_of_eq_add_nsmul hG (s + -t) hβ (fun j => by rw [add_f, neg_f, h, add_neg_cancel])
  refine SecOps.sec_ext fun j => ?_
  have := h0 j
  rw [add_f, neg_f, add_neg_eq_zero] at this
  exact this

theorem add_nsmul_inj {k : ℕ} (hk : 1 ≤ k) (ρ a b : D.X) (h : ρ + k • a = ρ + k • b) : a = b := by
  have h' : (k : ℤ) • a = (k : ℤ) • b := by
    rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
  exact smul_right_injective D.X (by omega : (k : ℤ) ≠ 0) h'

theorem exists_fam_single (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (ρ : D.X)
    (σ : FamSec D F k ρ) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 :=
  UUA.exists_fam_rep hG hB k ρ (add_nsmul_inj hk ρ) σ

theorem existsUnique_fam_of_reps (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) {C : Type*}
    (rep : C → D.X) (hrep : ∀ α : D.X, ∃! c, ∃ mu, rep c + k • mu = α) (σ : ∀ c, FamSec D F k (rep c)) :
    ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c := by
  choose cl hcl hcl' using hrep
  choose f hf _ using fun c => exists_fam_single hG hB hk (rep c) (σ c)
  have key : ∀ (α β : D.X) (c : C), cl β = c → (f (cl β)).s β = (f c).s β := by
    rintro α β c rfl; rfl
  refine ⟨⟨fun β => (f (cl β)).s β, fun mu α u hu hc => ?_⟩, fun c => ?_, fun s hs => ?_⟩
  · have e : cl (α + k • mu) = cl α := by
      obtain ⟨nu, hnu⟩ := hcl α
      exact (hcl' (α + k • mu) (cl α) ⟨nu + mu, by rw [smul_add, ← add_assoc, hnu]⟩).symm
    have := (f (cl α)).fe mu α u hu hc
    rw [← key α _ _ e] at this
    exact this
  · have e : cl (rep c) = c := (hcl' (rep c) c ⟨0, by rw [smul_zero, add_zero]⟩).symm
    exact (key (rep c) _ _ e).trans (hf c)
  · refine fam_ext fun α j => ?_
    have := eq_of_eq_add_nsmul hG s (f (cl α)) (hcl α) ((hs (cl α)).trans (hf (cl α)).symm)
    rw [this]

theorem mk_eq_mk_iff {k : ℕ} (α β : D.X) :
    (QuotientAddGroup.mk α : D.X ⧸ multiples D k) = QuotientAddGroup.mk β ↔ ∃ mu, α + k • mu = β := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨mu, h⟩
    exact ⟨mu, by rw [show k • mu = -α + β from h, add_neg_cancel_left]⟩
  · rintro ⟨mu, rfl⟩
    exact ⟨mu, by rw [neg_add_cancel_left]; rfl⟩

theorem existsUnique_fam (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k)
    (rep : D.X ⧸ multiples D k → D.X) (hrep : ∀ c, QuotientAddGroup.mk (rep c) = c)
    (σ : ∀ c, FamSec D F k (rep c)) : ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c :=
  existsUnique_fam_of_reps hG hB hk rep (fun α => ⟨QuotientAddGroup.mk α, (mk_eq_mk_iff _ _).1 (hrep _),
    fun c hc => (hrep c).symm.trans ((mk_eq_mk_iff _ _).2 hc)⟩) σ

theorem IsSecBasis.ne_zero {S : Scheme.{0}} {A T : Over S} [Nontrivial Γ(T.left, ⊤)] {N : LB (T ⊗ A).left} {m : ℕ}
    {b : Fin m → LB.Sec N} (hb : IsSecBasis N b) (i : Fin m) : ¬ ∀ j, (b i).f j = 0 := by
  classical
  intro h
  obtain ⟨r, -, hr⟩ := hb SecOps.secZero
  have h0 := hr 0 (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    simp only [Pi.zero_apply, map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero])
  have h1 := hr (Pi.single i 1) (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    refine (Finset.sum_eq_zero fun i' _ => ?_).symm
    by_cases e : i' = i
    · rw [e, h j, mul_zero]
    · rw [Pi.single_eq_of_ne e, map_zero, map_zero, MulZeroClass.zero_mul])
  have := congrFun (h1.trans h0.symm) i
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

theorem exists_sec_ne_zero (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ σ : FamSec D F k α, ¬ ∀ j, σ.f j = 0 := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  have : Nontrivial Γ((TF (R := R) F).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := IsSecBasis.ne_zero hb ⟨0, pow_pos (by omega) _⟩
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc])
    (pullMulSec (b ⟨0, pow_pos (by omega) _⟩) (𝟙 _) u hu)
  refine ⟨σ, fun h => hne fun j => ?_⟩
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e := (hσ _ (𝟙 _) y J hJ).trans (sval_pullMulSec _ _ _ hu _ y hJ)
  rw [UUA.sval_zero_of h _ y J (hJ.mem _ _), Category.id_comp] at e
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e.symm

theorem exists_fam_support (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ s : Fam D F k, ∀ β : D.X, (¬ ∀ j, (s.s β).f j = 0) ↔ ∃ mu, α + k • mu = β := by
  obtain ⟨σ, hσ⟩ := exists_sec_ne_zero (D := D) (F := F) hT hk α
  obtain ⟨s, rfl, hs⟩ := exists_fam_single hG hB hk α σ
  refine ⟨s, fun β => ⟨fun h => by_contra fun hn => h (hs β fun mu e => hn ⟨mu, e⟩), ?_⟩⟩
  rintro ⟨mu, rfl⟩ h
  exact hσ ((zero_add_nsmul_iff hG s α mu).1 h)

end GlobalTheory.FamFree

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

end GlobalTheory
end
end
