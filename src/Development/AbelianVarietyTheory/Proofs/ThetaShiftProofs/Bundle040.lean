module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle039
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.XiIntegral

section Tangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  obtain ⟨h₁', h₂'⟩ := (gtTanR_iff ν').1 ht'
  have hb : ν''.b = ν.b * ν'.b := h.1
  refine (gtTanR_iff ν'').2 ⟨by rw [hb, MonObj.comp_mul, h₁, h₁', _root_.mul_one], fun χ y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) (origin R).left).trans (val_mul hJ _ _ _))
  have c := val_cub D.cub (origin R) hJ (DegPre.cT D (epsR R) χ) ν.b ν'.b
  have c' := congrArg (fun z => cubV D.cub y J ((origin R) ≫ DegPre.cT D (epsR R) χ)
    ((origin R) ≫ ν.b) z) h₁'
  have cz (x x' : Over.mk (𝟙 (Sp R)) ⟶ D.P.A) : cubV D.cub y J x x' 1 = 1 := by
    have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
      simp [faceMap, x2, pzero, Hom.one_def]
    refine Eq.trans ?_ ((val_corr (hJ := hJ) (D.cub.face 2) (lift x x').left).trans (val_one _))
    refine Eq.trans ?_ (val_pull (hJ := hJ) ..).symm
    show val D.cub.t (lift x (lift x' 1)).left y J = _
    rw [hm, Over.comp_left]
    all_goals rfl
  have c := c.trans (c'.trans (cz _ _))
  have e' := (congrArg₂ (· * ·) rfl c).symm.trans (e.trans (congrArg₂ (· * ·) (h₂ χ y J hJ) (h₂' χ y J hJ)))
  simpa using e'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

end Tangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem exists_intHom {E : Type} [Field E] [NumberField E] [IsCMField E] {K₁ : Type} [Field K₁] [NumberField K₁]
    (τK : E →+* K₁) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X) :
    ∃ φ : X →+ 𝓞 K₁, ∀ x, (φ x : K₁) = ((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x)) := by
  obtain ⟨-, hadd, -, hint, -⟩ := GlobalTheory.ArcQ.pairE_properties E X ξ
  have hi : ∀ x, IsIntegral ℤ (((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x))) := fun x => by
    have h := (hint x).map (τK.comp (IsCMField.complexConj E).toRingEquiv.toRingHom).toIntAlgHom
    simpa [cc] using h
  refine ⟨AddMonoidHom.mk' (fun x => ⟨_, hi x⟩) fun x y => ?_, fun x => rfl⟩
  apply RingOfIntegers.ext
  show _ * τK (cc (pairE ξ (x + y))) = _ * τK (cc (pairE ξ x)) + _ * τK (cc (pairE ξ y))
  rw [hadd]
  simp [cc, mul_add]

theorem discr_mul_xi_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), s.kind τ k = none → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ _ hρ _ _ _ τ k hk
  have hG : Out.GlobalFnsSt := hK.laws.globalFns
  obtain ⟨φ, hφ⟩ := exists_intHom (labK c K₁ τ) s.ξ
  obtain ⟨hb, hd⟩ := s.xi τ k hk
  obtain ⟨hw1, -, hw3⟩ := GlobalTheory.TorusTangent.main hG Tv.V M.aw.D₀
  obtain ⟨-, -, hK3⟩ := GlobalTheory.TorusTangent.main hG K₁ d.a.D₀
  obtain ⟨hF1, hF2, -⟩ := GlobalTheory.TorusTangent.main hG Tv.Fr M.aK.D₀
  obtain ⟨-, hadd, -⟩ := GlobalTheory.ArcQ.pairE_properties E d.a.D₀.X s.ξ
  let φw : M.aw.D₀.X →+ Tv.V :=
    ρ.toAddMonoidHom.comp (φ.comp (M.pK.xe.toAddMonoidHom.comp M.pw.xe.symm.toAddMonoidHom))
  let φ₀ : d.a.D₀.X →+ K₁ := AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE s.ξ x))) fun x y => by
    rw [hadd]; simp [cc]
  let φ₂ : M.aK.D₀.X →+ Tv.Fr := io.toAddMonoidHom.comp (φ₀.comp M.pK.xe.toAddMonoidHom)
  obtain ⟨ν, ⟨hν, hνb, hνd⟩, -⟩ := hw1 φw
  obtain ⟨ν₁, h₁, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pw hG ν
  obtain ⟨e₂, h₂, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pK hG (d.e τ k)
  have t₁ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pw hG h₁ hν
  have t₂ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pK hG h₂ (s.tan τ k)
  obtain ⟨b₁, d₁⟩ := hw3 Tv.Fr M.aK.D₀ _ M.pw φw ν ν₁ hνb hνd h₁
  obtain ⟨b₂, d₂⟩ := hK3 Tv.Fr M.aK.D₀ _ M.pK φ₀ (d.e τ k) e₂ hb hd h₂
  obtain ⟨ν', hν'⟩ := GlobalTheory.ConstLie.exists_gtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂]
  have t₃ : GtTanR ν' := gtTanR_of_gtComb hν' fun i => by fin_cases i; exact t₂
  obtain ⟨b₃, d₃⟩ := hF2 φ₂ _ e₂ ν' t₂ b₂ d₂ hν'
  have key : ∀ x, algebraMap Tv.V Tv.Fr (φw (M.pw.xe x)) = (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂) x := fun x => by
    show algebraMap Tv.V Tv.Fr (ρ (φ (M.pK.xe (M.pw.xe.symm (M.pw.xe x))))) =
      ((NumberField.discr E : ℤ) : Tv.Fr) * io (labK c K₁ τ (cc (pairE s.ξ (M.pK.xe x))))
    rw [AddEquiv.symm_apply_apply, hρ, hφ, map_mul, map_intCast]
  have e : ν₁ = ν' := (hF1 (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂)).unique
    ⟨t₁, b₁, fun x j hj => (d₁ x j hj).trans (congrArg _ (key x))⟩ ⟨t₃, b₃, d₃⟩
  exact ⟨ν, ν₁, e₂, hν, h₁, h₂, e ▸ hν'⟩

end GlobalTheory.XiIntegral
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_constantLieBasis_arcGroup : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ (g : ℕ) (e : Fin g → Out.GtPt a.D₀ (epsR A)) (v : Fin g → (epsR (PowerSeries A) ⟶ W.t.G)) (M : 𝓞 E → Matrix (Fin g) (Fin g) A), (∀ i, GtTanR (e i) ∧ LieImg W (e i) (v i)) ∧ IsLieBasis v ∧ (∀ ν, GtTanR ν → ∃! cf : Fin g → A, GtComb cf e ν) ∧ ∀ (x : 𝓞 E) i, IsLieComb (fun k => PowerSeries.C (R := A) (M x i k)) v (v i ≫ W.t.act.act x) := by
  first | exact @GlobalTheory.ConstLie.exists_const_basis | exact GlobalTheory.ConstLie.exists_const_basis | (intros; apply GlobalTheory.ConstLie.exists_const_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstRational

section Sums
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem fsum_mem (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (hth : th ∈ A.Theta j α) (v : A.V) :
    A.FSum j α th v ∈ Conv.convLaurent := by
  obtain ⟨T, hT⟩ := exists_formal_convergence O A
  obtain ⟨h, -⟩ := ((hT T le_rfl j).1 α th hth).1 v
  exact Conv.halfRing_le_convLaurent T h

theorem exists_shift_mem (k : ℕ) [NeZero k] (la : A.La) (hla : ∀ α, (k : ℤ) ∣ A.be la.y α) :
    ∃ ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩,
      ∀ i z, IsFShift A k i.1 i.2 la z (ψ i z) ∧ ψ i z ∈ Conv.convLaurent := by
  obtain ⟨cz, -, h⟩ := GlobalTheory.T.theta_sum_shift_eq_single_mul_fSum O A k la hla
  choose th' hth' _ h' using h
  refine ⟨fun i z => HahnSeries.single (A.be la.y i.1 / k) (cz z) *
    A.FSum k (i.1 + la.y) (th' i.1 i.2 i.2.2) z, fun i z => ⟨((h' i.1 i.2 i.2.2 z).1 _).2 rfl, ?_⟩⟩
  exact mul_mem (Conv.halfRing_le_convLaurent 0 (Conv.single_mem_halfRing 0 _ _))
    (fsum_mem A k _ _ (hth' _ _ _) z)

end Sums

theorem points_frames_eq (L₁ : Out.Laws) (L₂ : Out.Laws2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} [StarRing (𝓞 E)] {D : Datum H} {l : Level H} {Xo : Moduli D l} {A : AnArc (𝓞 E)}
    (σ : KA l →+* ℂ) {y : Sp ℂ⸨X⸩ ⟶ Xo.X} (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La) (hA : AnFin A)
    (hy : y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ))
    (levA : ∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v))
    (levM : ∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v))
    {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (f g : ℂ⸨X⸩ →+* F)
    (hfg : ∀ a ∈ Conv.convLaurent, f a = g a) (v : A.V) :
    spMap f ≫ (Φ.x v).left = spMap g ≫ (Φ.x v).left ∧
      ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → f (Φ.τ v j) = g (Φ.τ v j) := by
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  let φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F := fun j i v =>
    if h : j = 0 then 0 else haveI : NeZero j := ⟨h⟩; f (A.FSum j i.1 i.2 v)
  have hf : ∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v) := fun j _ i v =>
    dif_neg (NeZero.ne j)
  have hg : ∀ (j : ℕ) [NeZero j] i v, φ j i v = g (A.FSum j i.1 i.2 v) := fun j _ i v =>
    (hf j i v).trans (hfg _ (fsum_mem A j _ _ i.2.2 v))
  obtain ⟨Θ₁, x₁, l₁⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F f φ hA hf
  obtain ⟨Θ₂, x₂, l₂⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F g φ hA hg
  have lev : ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : A.La),
      Φ.LevelPt k (toUnit _ ≫ ξ) la → ∃ ψ, Θ₁.Lev k (toUnit _ ≫ ξ) ψ ∧ Θ₂.Lev k (toUnit _ ≫ ξ) ψ := by
    intro k _ ξ la h
    obtain ⟨ψ, hψ⟩ := exists_shift_mem A k la h.2.1.2
    refine ⟨fun i z => f (ψ i z), l₁ k ξ la ψ h fun i z => (hψ i z).1, ?_⟩
    have e : (fun i z => f (ψ i z)) = fun i z => g (ψ i z) :=
      funext fun i => funext fun z => hfg _ (hψ i z).2
    rw [e]
    exact l₂ k ξ la ψ h fun i z => (hψ i z).1
  have hs : (spMap f ≫ y) ≫ Xo.s = (spMap g ≫ y) ≫ Xo.s := by
    have e : f.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) = g.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) :=
      RingHom.ext fun a => hfg _ (Conv.convLaurent.algebraMap_mem (σ a))
    rw [Category.assoc, Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.pointFamilies_eq_of_values_levels_universalFamily L₁ L₂ E H D l Xo F A.V _ _ φ _ _ Θ₁ Θ₂ hs
    (fun v => lev _ _ _ (levA v)) (fun v hv => lev _ _ _ (levM v hv)) v
  refine ⟨(x₁ v).1.symm.trans (e₁.trans (x₂ v).1), fun j hj => ?_⟩
  rw [← (x₁ v).2 j hj, ← (x₂ v).2 j hj]
  refine e₂ j ?_
  rw [(x₁ v).1]
  exact fun p _ => hj (Set.mem_univ (spMap f p))

theorem rational : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) (σ : KA l →+* ℂ) (y : Sp ℂ⸨X⸩ ⟶ Xo.X) (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La), AnFin A → y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ) → (∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) → (∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v)) → Φ.Rational := by
  intro L₁ L₂ E _ _ _ H _ D l Xo A σ y Φ laA laM hA hy levA levM
  haveI : CharZero ℂ⸨X⸩ := algebraRat.charZero _
  haveI : CharZero Conv.convLaurent := algebraRat.charZero _
  have key := fun s : AlgebraicClosure ℂ⸨X⸩ ≃ₐ[Conv.convLaurent] AlgebraicClosure ℂ⸨X⸩ =>
    points_frames_eq L₁ L₂ σ Φ laA laM hA hy levA levM
      ((s : AlgebraicClosure ℂ⸨X⸩ →+* AlgebraicClosure ℂ⸨X⸩).comp (algebraMap ℂ⸨X⸩ _))
      (algebraMap ℂ⸨X⸩ (AlgebraicClosure ℂ⸨X⸩)) (fun a ha => s.commutes (⟨a, ha⟩ : Conv.convLaurent))
  refine ⟨fun v => ?_, fun v j hj => ?_⟩
  · refine (FixedPoint.existsUnique_factor (K₀ := Conv.convLaurent) (L := AlgebraicClosure ℂ⸨X⸩)
      (Φ.x v).left fun s => ?_).exists
    have h := (key s v).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h
  · obtain ⟨a, ha⟩ := FixedPoint.mem_range_of_algebraMap_fixed (K₀ := Conv.convLaurent)
      (L := AlgebraicClosure ℂ⸨X⸩) (Φ.τ v j) fun s => (key s v).2 j hj
    exact ha ▸ a.2

end GlobalTheory.ConstRational
end
