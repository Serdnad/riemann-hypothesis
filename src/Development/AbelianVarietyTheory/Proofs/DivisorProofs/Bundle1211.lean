module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeThetaJets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Mathlib.Analysis.Normed.Group.Ultra
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumberSectionValue_linearCombination : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  first | exact @GlobalTheory.DualLin.sE_comb | exact GlobalTheory.DualLin.sE_comb | (intros; apply GlobalTheory.DualLin.sE_comb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusExtDualNumberTermValue_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := by
  first | exact @GlobalTheory.JcSmul.jc_smul | exact GlobalTheory.JcSmul.jc_smul | (intros; apply GlobalTheory.JcSmul.jc_smul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaKeyRule_scale_section_pow_eight : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 → ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧ ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C), ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i) (fun i j => a * J i j) := by
  first | exact @GlobalTheory.MBLow.ScaleJet.scale_key | exact GlobalTheory.MBLow.ScaleJet.scale_key | (intros; apply GlobalTheory.MBLow.ScaleJet.scale_key <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  first | exact @GlobalTheory.MBLow.TrNum.transport | exact GlobalTheory.MBLow.TrNum.transport | (intros; apply GlobalTheory.MBLow.TrNum.transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem deform_of_lattice_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  intro κ C _ _ _ _ e x g hg m ζ lev k X n π B a b hπ0 hπ1 hfin ha hb hJ hE
  have hA := fun i => lattice_series_regroup C X n π (a i) B hπ0 hπ1 hfin (ha i)
  have hB := fun i j => lattice_series_regroup C X n π (b i j) B hπ0 hπ1 hfin (hb i j)
  choose Θ hΘb hΘs hΘc using hA
  choose Γ hΓb hΓs hΓc using hB
  obtain ⟨ε, hε, hu⟩ := hE
  have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
  have hnπ : 0 < ‖e π‖ := norm_pos_iff.2 heπ
  refine ⟨Θ, Γ, π, max B 0, hπ1, fun i l => ⟨hΘb i l, fun j => hΓb i j l⟩, ?_, ε * ‖e π‖, mul_pos hε hnπ, ?_⟩
  · have h1 : (fun i => ∑' l, PowerSeries.coeff l (Θ i) * π ^ l) = fun i => ∑' α, a i α := funext hΘs
    have h2 : (fun i j => ∑' l, PowerSeries.coeff l (Γ i j) * π ^ l) = fun i j => ∑' α, b i j α :=
      funext fun i => funext (hΓs i)
    rw [h1, h2]; exact hJ
  · intro u hu0 hul
    have hv0 : u / e π ≠ 0 := div_ne_zero hu0 heπ
    have hvl : ‖u / e π‖ < ε := by rw [norm_div, div_lt_iff₀ hnπ]; exact hul
    obtain ⟨⟨hsa, hsb⟩, x₀, hg₀, lev₀, hJ₀, hk⟩ := hu (u / e π) hv0 hvl
    refine ⟨fun i => ⟨(hΘc i e u (hsa i)).1, fun j => (hΓc i j e u (hsb i j)).1⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have h1 : (fun i => ∑' l, e (PowerSeries.coeff l (Θ i)) * u ^ l) = fun i => ∑' α, e (a i α) * (u / e π) ^ n α :=
      funext fun i => (hΘc i e u (hsa i)).2
    have h2 : (fun i j => ∑' l, e (PowerSeries.coeff l (Γ i j)) * u ^ l) =
        fun i j => ∑' α, e (b i j α) * (u / e π) ^ n α :=
      funext fun i => funext fun j => (hΓc i j e u (hsb i j)).2
    rw [h1, h2]; exact hJ₀

end GlobalTheory.MBLow
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationValues_transport_fieldIso : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N), ∃ (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ ∧ (∀ x, I.h x = 1) ∧ I.lam = 1 ∧ (∀ χ, ν'.eX (I.e χ) = ν.eX χ) ∧ ν'.th = ν.th ∧ ν'.rg = e ν.rg ∧ (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) ∧ ∀ (k : ℕ) (s : Fam D F k), ∃ s' : Fam D F' k, (∀ f, ν.FamV s f → ∃ f', ν'.FamV s' f' ∧ ∀ α x, f' (I.e α) (I.φ x) = e (f α x)) ∧ ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ α, jc ν' s' gm' (I.e α) = dualMap (e : F →+* F') (jc ν s gm α) := by
  exact @GlobalTheory.MBLow.FieldIso.transport_iso
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_keyDatumBaseChange_thetaJets : ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (x : KeyIn K), ∃ (xC : KeyIn C) (hg : xC.P.g = x.P.g) (io : (Over.mk (spMap f) ⟶ x.P.A) ≃* (baseOver (Sp C) ⟶ xC.P.A)), KeyPB xC x f ∧ (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs xC.P.A xC.P.L k (io a) (io b) z → WeilIs x.P.A x.P.L k a b z) ∧ ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap f)))) (I : Type) (pt : I → (Over.mk (spMap f) ⟶ x.P.A)) (y : Fin x.P.g → (Sp (DualNumber C) ⟶ (Over.mk (spMap f) ⊗ x.P.A).left)) (ϑ : I → C) (J : I → Fin x.P.g → C), IsPolAVSectionInverseImage x.P (Over.mk (spMap f)) x.th th → (∀ j, y j ≫ (fst (Over.mk (spMap f)) x.P.A).left = spMap (algebraMap C (DualNumber C)) ∧ y j ≫ (snd (Over.mk (spMap f)) x.P.A).left = spMap (dualMap f) ≫ (x.v j).left) → ThJetT x.P x.rig m (spMap f) th pt y ϑ J → ThJet xC hg m (fun i => io (pt i)) ϑ J := by
  first | exact @GlobalTheory.MBLow.exists_keyPB_thJet | exact GlobalTheory.MBLow.exists_keyPB_thJet | (intros; apply GlobalTheory.MBLow.exists_keyPB_thJet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TangentFirstOrder

theorem fst_eq_of_tangent : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  intro K C _ _ _ P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
  have key : ∀ {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens) (s : Γ(X, U)),
      (valR y U s).fst = valR (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) U s := by
    intro X y U s
    by_cases h : ⊤ ≤ y ⁻¹ᵁ U
    · exact (GlobalTheory.MBLow.BaseChRig.valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom y h s).symm
    · have h' : ¬ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) ⁻¹ᵁ U :=
        fun h' => h ((GlobalTheory.ArcLie.le_iff_fst y U).2 h')
      unfold valR
      rw [dite_eq_right h, dite_eq_right h']
      rfl
  have sq : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap (algebraMap K C)) =
      spMap (algebraMap K C) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    simp [dualMap]
  have e0 : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yv = spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yw := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hv1, Category.assoc, hw1]
    · rw [Category.assoc, hv2, Category.assoc, hw2, ← Category.assoc, ← Category.assoc, sq, Category.assoc,
        Category.assoc, hv, hw]
  have hU : ⊤ ≤ (spMap (algebraMap K C)) ⁻¹ᵁ (P.L.pull (eSec P.A)).U (fun _ => i₀) :=
    fun q hq => Set.mem_iInter.2 fun _ => hi hq
  have hr : valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ≠ 0 := by
    unfold valR
    rw [dite_eq_left hU]
    exact (((ρ.s fun _ => i₀).isUnit.map _).map _).ne_zero
  have h1 := congrArg TrivSqZeroExt.fst ev
  have h2 := congrArg TrivSqZeroExt.fst ew
  rw [key] at h1 h2
  rw [e0, h2] at h1
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero] at h1
  exact (mul_left_cancel₀ (pow_ne_zero k hr) h1).symm

end GlobalTheory.TangentFirstOrder
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.Mix.SecNorm

theorem logSec_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec), Measurable (M.logSec s) ∧ (∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s)) ∧ (∀ y, CInfAt (M.φ.nsq (secVal p σ s)) y) ∧ ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ∀ y ∈ ptsIn p σ (nonzeroLocus s), (M.addFn u hu).logSec s y = M.logSec s y - u y / 2 := by
  intro k _ X p σ M s
  have hpos : ∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s) := fun y => by
    rw [← secVal_ne_zero_iff s (mem_pick M.φ.isLB y), Weight.nsq, mul_pos_iff_of_pos_right (Real.exp_pos _),
      sq_pos_iff, norm_ne_zero_iff]
  refine ⟨?_, hpos, fun y => ?_, fun u hu y hy => ?_⟩
  · exact (Real.measurable_log.comp (M.cInf.continuous_nsq s).measurable).div_const 2
  · have hi := mem_pick M.φ.isLB y
    have ho := (isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi
    have h1 : CInfAt (fun z => ‖ev p σ (M.B.U (pick M.φ.isLB y)) (s.f _) z‖ ^ 2) y :=
      ⟨_, Unit, inferInstance, fun _ => s.f _, fun v => ‖v ()‖ ^ 2, univ, hi, isOpen_univ, trivial,
        ((contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
    refine (h1.comp₂ (M.cInf _ y hi) (G := fun x => x.1 * Real.exp (-x.2))
      (contDiff_fst.mul contDiff_snd.neg.exp)).congr ?_
    exact eventually_of_mem ho fun z hz => M.φ.nsq_eq (secVal_mem s) hz
  · have h := (hpos y).2 hy
    change Real.log ((M.φ.addFn u).nsq (secVal p σ s) y) / 2 = Real.log (M.φ.nsq (secVal p σ s) y) / 2 - u y / 2
    rw [Weight.nsq_addFn, Real.log_mul h.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

end GlobalTheory.Mix.SecNorm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AdicDual

theorem hasSum_of_sumI {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} {C : Type} [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (h1 : ∀ a, ‖φ a‖ ≤ 1) (h2 : ∀ a ∈ I, ‖φ a‖ < 1)
    {M : Type} [AddCommGroup M] [Module R M] (g : M →+ C) (hg : ∀ (a : R) y, g (a • y) = φ a * g y)
    {Ix : Type} {x : Ix → M} {s : M} (h : GlobalTheory.UT.SumI I x s) : HasSum (fun i => g (x i)) (g s) := by
  have bd : ∀ {E : Type} [AddCommGroup E] [Module R E] (f : E →+ C), (∀ (a : R) y, f (a • y) = φ a * f y) →
      ∀ (t : Set E) (c : ℝ), 0 ≤ c → (∀ y ∈ t, ‖f y‖ ≤ c) → ∀ y ∈ Submodule.span R t, ‖f y‖ ≤ c := by
    intro E _ _ f hf t c h0 hc y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using h0
    | add y z _ _ k1 k2 => rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2)
    | smul a y _ k1 => rw [hf, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h1 a)).trans k1
  obtain ⟨N, ⟨t, rfl⟩, -, -, h⟩ := h
  obtain ⟨u, rfl⟩ := IsNoetherian.noetherian I
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ t, ‖g y‖ ≤ c :=
    ⟨∑ y ∈ t, ‖g y‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
      fun y hy => Finset.single_le_sum (f := fun y : M => ‖g y‖) (fun _ _ => norm_nonneg _) hy⟩
  obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ a ∈ u, ‖φ a‖ ≤ r :=
    ⟨(u.sup fun a => ‖φ a‖₊ : NNReal), NNReal.coe_nonneg _,
      by exact_mod_cast (Finset.sup_lt_iff (f := fun a => ‖φ a‖₊) (zero_lt_one' NNReal)).2 fun a ha =>
        show ‖φ a‖₊ < 1 from h2 a (Submodule.subset_span ha),
      fun a ha => by exact_mod_cast Finset.le_sup (f := fun a => ‖φ a‖₊) ha⟩
  have hI := bd φ.toAddMonoidHom (fun a y => map_mul φ a y) u r hr0 hr
  have hP : ∀ n : ℕ, ∀ y ∈ (Submodule.span R (u : Set R)) ^ n • Submodule.span R (t : Set M), ‖g y‖ ≤ r ^ n * c := by
    intro n
    induction n with
    | zero => simpa using bd g hg t c hc0 hc
    | succ n ih =>
      intro y hy
      rw [pow_succ', Submodule.mul_smul] at hy
      refine Submodule.smul_induction_on hy (fun a ha z hz => ?_)
        (fun y z k1 k2 => by rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2))
      rw [hg, norm_mul, pow_succ', _root_.mul_assoc]
      exact mul_le_mul (hI a ha) (ih z hz) (norm_nonneg _) hr0
  refine Metric.tendsto_nhds.2 fun e he => ?_
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const c
  rw [zero_mul] at lim
  obtain ⟨n, hn⟩ := (lim.eventually (gt_mem_nhds he)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.mem_of_superset (Filter.mem_atTop S) fun T hT => ?_
  show dist _ _ < e

  rw [dist_comm, dist_eq_norm, ← map_sum, ← map_sub]
  exact (hP n _ (hS T hT)).trans_lt hn

theorem hasSum_fst_snd : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (I : Ideal V) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V I C → ∀ {Ix : Type} (x : Ix → DualNumber V) (s : DualNumber V), GlobalTheory.UT.SumI I x s → HasSum (fun i => toF V C (x i).fst) (toF V C s.fst) ∧ HasSum (fun i => toF V C (x i).snd) (toF V C s.snd) := by
  intro V _ _ _ I C _ _ _ hC Ix x s h
  let φ : V →+* C := (algebraMap (FractionRing V) C).comp (algebraMap V _)
  constructor
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.fstHom V V V).toLinearMap.toAddMonoidHom)
      (fun a y => by simp) h
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.sndHom V V).toAddMonoidHom)
      (fun a y => by simp) h

end GlobalTheory.AdicDual

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.DZero

theorem valR_push {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valR, valR, dite_eq_left h, dite_eq_left h']
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  rw [e1]
  exact congrArg (fun k => k.hom ((x.appLE U ⊤ h).hom f)) e2

theorem isD_zero : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), IsD ν d 0 (DegPre.zeroT D (TE R ℂ)) := by
  intro R _ _ _ _ D _ _ _ N ν g d U f hU
  have h0 : d.ex 0 = 1 := by
    have := d.ex_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have e : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
      (DegPre.zeroT D (TE R ℂ))).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    have : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        (DegPre.zeroT D (TE R ℂ)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id, h0, map_one, Hom.one_def, ← Category.assoc, comp_toUnit]
    rw [this, Over.comp_left]
    rfl
  rw [e, valR_push _ _ _ hU, map_zero, TrivSqZeroExt.inr_zero, add_zero]
  rfl

end GlobalTheory.MBLow.Cl.DZero

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.MBLow.Cl.HolB

variable {X Y : Scheme.{0}}

theorem valF_comp_app (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valF x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valF (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dite_eq_left h', dite_eq_left h]
    simp only [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dite_eq_right h', dite_eq_right h]

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := rfl

def psiB (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left)
    (hw : φ ≫ D.P.A.hom = x.P.A.hom ≫ spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) :
    x.P.A.left ⟶ (DegPre.BF D ℂ).left :=
  (lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
    (Over.homMk φ (by
      rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
      Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A)).left

theorem hol_ptB : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := by
  intro R _ _ _ D N ν g d x u φ hφ hE U f
  have hw := hφ.1.w
  have key : ∀ z, ptB ν d z = (u.ex z).left ≫ psiB R D x φ hw := by
    intro z
    have h0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := Over.w (u.ex z)
    let e : TF (R := R) ℂ ⟶ Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) :=
      Over.homMk (u.ex z).left (by simp only [Over.mk_hom]; rw [← Category.assoc, h0]; exact Category.id_comp _)
    have he : e ≫ lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
        (Over.homMk φ (by
          rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
          Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A) = lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) := by
      rw [comp_lift]
      congr 1
      · ext; simp [e, h0]
      · ext; simp [e, hE z]
    rw [ptB, ← he]
    rfl
  have hs : {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (psiB R D x φ hw ⁻¹ᵁ U)} := by
    ext z
    simp only [Set.mem_setOf_eq, key z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := u.hol (psiB R D x φ hw ⁻¹ᵁ U) ((psiB R D x φ hw).app U |>.hom f)
  rw [hs]
  refine ⟨ho, hd.congr fun z _ => ?_⟩
  rw [← valF_eq_valAt', valF_comp_app, key z]

end GlobalTheory.MBLow.Cl.HolB

end
end
