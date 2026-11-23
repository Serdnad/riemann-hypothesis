module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFptsPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle014
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  first | exact @GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | exact GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | (intros; apply GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), (∀ ν, GtTanR ν → ∃! z₀, AnVec Ha ν z₀) ∧ (∀ z₀, ∃! ν, AnVec Ha ν z₀) ∧ (∀ ν z₀, AnVec Ha ν z₀ → GtTanR ν) ∧ ∀ (m : ℕ) (cf : Fin m → ℂ) (e : Fin m → Out.GtPt a.D₀ (epsR ℂ)) (z : Fin m → (Fin g → ℂ)) ν, (∀ i, AnVec Ha (e i) (z i)) → (GtComb cf e ν ↔ AnVec Ha ν (∑ i, cf i • z i)) := by
  first | exact @GlobalTheory.ExpTan.anVec_bijective | exact GlobalTheory.ExpTan.anVec_bijective | (intros; apply GlobalTheory.ExpTan.anVec_bijective <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FamilyUnique

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F)) (hw : IsRigIso m L' L w) (hw' : IsRigIso m' L'' L' w') :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F), IsRigIso n L'' L w'' ∧
      ∀ (F : Type) [Field F] (x : Sp F ⟶ G''.left) (x' : Sp F ⟶ G'.left) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        x ≫ m'.F = x' →
        ⊤ ≤ x' ⁻¹ᵁ (LB.div (L.L.pull m.F) L'.L).U (fun _ => j, i) →
        ⊤ ≤ x ⁻¹ᵁ (LB.div (L'.L.pull m'.F) L''.L).U (fun _ => i, k) →
        valR x _ (w''.s (fun _ => j, k)).val =
          valR x' _ (w.s (fun _ => j, i)).val * valR x _ (w'.s (fun _ => i, k)).val := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw'
  obtain ⟨g, r⟩ := hw
  obtain ⟨g', r'⟩ := hw'
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  refine ⟨w'', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_comp L'.isLB g g', T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r'⟩, ?_⟩
  rintro F _ x x' j i k rfl h₁ h₂
  have a₁ := h₁ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have a₂ := h₂ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have hj : m.F (m'.F (x (cpt F))) ∈ L.L.U j := mem_pull.1 a₁.1
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (LB.div (L.L.pull (m'.F ≫ m.F)) L''.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull₂.2 hj, a₂.2⟩
  apply toStkA_injective
  rw [map_mul]
  exact (toStkA_valR x _ _ h₃ _).trans ((congrArg Units.val (T _ x (cpt F) j i k hj a₁.2 a₂.2)).trans
    (congrArg₂ (· * ·) (toStkA_valR _ _ _ h₁ _).symm (toStkA_valR _ _ _ h₂ _).symm))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_objMap_eq {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) : ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap = m := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩, rfl⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

theorem points_frames_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  intro hL hL2 E _ _ _ H _ D l Xo F _ _ _ V _ act I φ y₁ y₂ Θ₁ Θ₂ hy hA hM
  obtain ⟨o₁, m₁, w₁, Θ₁', rw₁, p₁, lev₁⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₁ _ Θ₁ hy
  obtain ⟨o₂, m₂, w₂, Θ₂', rw₂, p₂, lev₂⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₂ _ Θ₂ rfl
  obtain ⟨m, w, rw₀, p⟩ := GlobalTheory.T.exists_abelianTriple_iso_of_same_point_values hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂'
  have key : ∀ (k : ℕ) (x₁ : 𝟙_ (Over (Sp F)) ⟶ o₁.t.G) (x₂ : 𝟙_ (Over (Sp F)) ⟶ o₂.t.G)
      (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G), 1 ≤ k → x₁.left ≫ m₁.φ = y₁ ≫ x.left → x₂.left ≫ m₂.φ = y₂ ≫ x.left →
      (∃ ψ, Θ₁.Lev k (toUnit _ ≫ x) ψ ∧ Θ₂.Lev k (toUnit _ ≫ x) ψ) → x₁.left ≫ m.φ = x₂.left := by
    rintro k x₁ x₂ x hk k₁ k₂ ⟨ψ, a₁, a₂⟩
    exact GlobalTheory.T.triple_iso_respects_level_ratio_points hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂' m w k ψ x₁ x₂ hk rw₀.1 p
      (lev₁ k ψ _ x₁ hk k₁ a₁) (lev₂ k ψ _ x₂ hk k₂ a₂)
  obtain ⟨n, rfl⟩ := exists_objMap_eq o₁ o₂ m
    (fun a ha => key l.M _ _ _ (le_trans (by norm_num) l.three_le) (m₁.eta a) (m₂.eta a) (hM a ha))
    (fun a => key l.A _ _ _ l.A_pos (m₁.etaA a) (m₂.etaA a) (hA a))
  obtain ⟨n', hn'⟩ := ObjComp.objMap_comp m₂ n
  have e : y₁ = 𝟙 _ ≫ y₂ := (Xo.rep _ _ inferInstance o₁).unique ⟨hy, ⟨m₁⟩⟩ ⟨by rw [Category.id_comp], ⟨n'⟩⟩
  subst e
  have hφ : m₁.toSABMap.φ = n.toSABMap.φ ≫ m₂.toSABMap.φ := (objMap_unique_of_field hL.serre m₁ n').trans hn'
  obtain ⟨w', rw', hval⟩ := exists_rigIso_comp m₂.cm n.cm m₁.cm hφ
    (m₁.base.trans (congrArg₂ (· ≫ ·) n.base m₂.base).symm) _ _ _ w₂ w rw₂ rw₀
  intro v
  have hx : (Θ₁.x v).left = (Θ₂.x v).left := by
    rw [← (p₁ v).1, ← (p₂ v).1, ← (p v).1, hφ, Category.assoc]
  refine ⟨hx, fun j hj => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart o₁.t.PP.isLB ((Θ₁'.x v).left (cpt F))
  obtain ⟨i, hi⟩ := exists_chart o₂.t.PP.isLB ((Θ₂'.x v).left (cpt F))
  have hj₀ := (top_le_iff_cpt _ _).1 hj
  have c₁ : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₁.toSABMap.φ) o₁.t.PP.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p₁ v).1] at hj₀; exact hj₀), hk⟩
  have c₂ : ⊤ ≤ (Θ₂'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₂.toSABMap.φ) o₂.t.PP.L).U (fun _ => j, i) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [hx, ← (p₂ v).1] at hj₀; exact hj₀), hi⟩
  have c : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull n.toSABMap.φ) o₁.t.PP.L).U (fun _ => i, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p v).1] at hi; exact hi), hk⟩
  have := o₁.proper
  have u := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Xo.univ.t o₁.t _ m₁.toSABMap).2 w₁ w' rw₁ rw' F (𝟙 _) (Θ₁'.x v)
    inferInstance j k c₁
  rw [(p₁ v).2 j k c₁, (p₂ v).2 j i c₂, (p v).2 i k c, ← _root_.mul_assoc]
  exact congrArg (· * _) (u.trans (hval F _ _ j i k (p v).1 c₂ c))

end GlobalTheory.FamilyUnique
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.constantPointFrame_isFrame_with_rigidification : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  first | exact @GlobalTheory.ConstFrame.main | exact GlobalTheory.ConstFrame.main | (intros; apply GlobalTheory.ConstFrame.main <;> assumption)
end
